/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepBCore
public import Hironaka.Manifold.FiniteSuccession.Functor.PushforwardPullback
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Resolution.Analytic.OrderReduction.BDOf
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The modified first step: the modified core commutes with local analytic isomorphisms

The functoriality argument in the proof of [Kol07, Lemma 102] (the restriction of a smooth
surjection to the member is again a smooth surjection, and pull-back and restriction commute) for
the modified first step of [Wlo09, Theorem 7.4.1]: for a local analytic isomorphism `g : N → M` and
the pulled-back triple `g^*T`, the modified core of `g^*T` on a relatively compact open `U'` is the
modified core of `T` on `g(U')` pulled back along `g|_{U'}`, up to empty blow-ups. This is the
counterpart of `BDan.coreFamOn_commutesWithLocalIsos` **without** the first blow-up.

The argument, step by step:
* the stopped locus and `H⁺` pull back (`hplus_pullback`: `H⁺(g^*T) = g⁻¹(H⁺(T))`, by
  `BD.Zminus1_comap`: a component of `g⁻¹(E^j)` lies in `cosupp(g^*𝓘, 1)` iff the component of
  `E^j` it maps into lies in `cosupp(𝓘, 1)`);
* the restricted triple of `g^*T` on `g⁻¹(H⁺)` is the pull-back of the restricted triple of `T`
  along the restriction `g|_{H⁺} : g⁻¹(H⁺) → H⁺` (`restrictedTripleModOf_isPullbackOf`:
  `pullback_inclusionMap_pullback` for the ideal, `emptyMember_comap` for the boundary), itself a
  local analytic isomorphism (`IsClosedSubmanifold.isLocalDiffeomorph_restrictMap`);
* the functor `R` one dimension down commutes with it (its commutation with local isomorphisms, a
  hypothesis here) at the trace `U' ∩ g⁻¹(H⁺)`, whose image is the trace `g(U') ∩ H⁺`
  (`imageOpens_hplusRestrictMap_preimageOpens`);
* the push-forward on each open commutes with the pull-back along `g|_{U'}`
  ([Kol07, Definition 30, 30.3]; `PushforwardStage.pushforwardAux_pullback` at the two restriction
  stages, the general form of `pushforwardRestrict_pullback_restrictLE`:
  `pushforwardRestrict_pullback_restrictMap`), and the deletions of empty blow-ups commute with
  both.

The transport from `H⁺(g^*T)` to the propositionally equal `g⁻¹(H⁺(T))` reads the constructions
on an arbitrary closed hypersurface `S` with `S = H⁺` (`restrictedTripleModOf`,
`coreModOn_eq_of_eq`, as `coreFamOn_eq_of_eq` does).
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Manifold

open Hironaka.Manifold

/-! ### Generic tools: the per-open push-forward under a local analytic isomorphism -/

section Generic

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n s : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E} {S : Set M}

/-- The restriction `g|_{g⁻¹(S)} : g⁻¹(S) → S` maps the trace `U' ∩ g⁻¹(S)` into the trace `W ∩ S`
when `g(U') ⊆ W`. -/
theorem IsClosedSubmanifold.image_restrictMap_preimageOpens_subset (hS : IsClosedSubmanifold ψ S s)
    (g : AnalyticMap N M) (hS' : IsClosedSubmanifold ψ (⇑g ⁻¹' S) s) {U' : Opens N} {W : Opens M}
    (hUW : ⇑g '' (U' : Set N) ⊆ W) :
    ⇑(hS'.restrictMap hS g g.contMDiff fun _ hx => hx) ''
        (hS'.preimageOpens U' : Set hS'.toAnalyticManifold) ⊆
      hS.preimageOpens W := by
  rintro _ ⟨p, hp, rfl⟩
  exact hUW ⟨(p : ⇑g ⁻¹' S).1, hp, rfl⟩

/-- The push-forward on each open commutes with the pull-back along a local analytic isomorphism
`g|_{U'} : U' → W` (`g(U') ⊆ W`), as in the proof of [Kol07, Lemma 102] with the push-forward of
[Kol07, Definition 30, 30.3]: `pushforwardAux_pullback` at the two restriction stages, the square
being `g|_{U'} ∘ (U' ∩ g⁻¹(S) ⊆ U') = (W ∩ S ⊆ W) ∘ g|_{g⁻¹(S)}`. The general form of
`pushforwardRestrict_pullback_restrictLE`. -/
theorem _root_.AnalyticManifold.BlowUpSequence.pushforwardRestrict_pullback_restrictMap
    (hS : IsClosedSubmanifold ψ S s) (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g)
    (hS' : IsClosedSubmanifold ψ (⇑g ⁻¹' S) s) (U' : Opens N) (W : Opens M)
    (hUW : ⇑g '' (U' : Set N) ⊆ W)
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      ((hS.toAnalyticManifold).restrict (hS.preimageOpens W))) :
    (AnalyticManifold.BlowUpSequence.pushforwardRestrict hS W L).pullback
        (AnalyticMap.restrictMap g U' W hUW)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' W hUW) =
      AnalyticManifold.BlowUpSequence.pushforwardRestrict hS' U'
        (L.pullback
          (AnalyticMap.restrictMap (hS'.restrictMap hS g g.contMDiff fun _ hx => hx)
            (hS'.preimageOpens U') (hS.preimageOpens W)
            (hS.image_restrictMap_preimageOpens_subset g hS' hUW))
          (AnalyticMap.isLocalDiffeomorph_restrictMap
            (IsClosedSubmanifold.isLocalDiffeomorph_restrictMap g hg _) _ _ _)) :=
  PushforwardStage.pushforwardAux_pullback (hS.restrictStageOf W _ rfl)
    (hS'.restrictStageOf U' _ rfl) (AnalyticMap.restrictMap g U' W hUW) _ _
    ⟨AnalyticMap.isLocalDiffeomorph_restrictMap hg U' W hUW, rfl, fun _ => rfl⟩ L

/-- Pull-backs of the values of a compatible family on two equal opens, along the restrictions of
the same map, are equal (a substitution). -/
theorem _root_.Hironaka.Manifold.CompatibleFamily.pullback_restrictMap_congr
    {A B : AnalyticManifold.{u} 𝕜 E}
    {X : AnalyticTriple ψ A} (C : CompatibleFamily X) (f : AnalyticMap B A)
    (hf : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f) (V : Opens B) {W W' : Opens A} (e : W = W')
    (hW : IsCompact (closure (W : Set A))) (hW' : IsCompact (closure (W' : Set A)))
    (h1 : ⇑f '' (V : Set B) ⊆ W) (h2 : ⇑f '' (V : Set B) ⊆ W') :
    (C.seqOn W hW).pullback (AnalyticMap.restrictMap f V W h1)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hf V W h1) =
      (C.seqOn W' hW').pullback (AnalyticMap.restrictMap f V W' h2)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hf V W' h2) := by
  subst e
  rfl

end Generic

end Manifold

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
  (R : AnalyticFamilyFunctor.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
    (AnalyticTriple.BMOClass 1))
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (j : T.F.ι)
  (hT : AnalyticTriple.BMOClass 1 T)

/-! ### Commutation with a local analytic isomorphism -/

section Comm

variable {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (g : AnalyticMap N M)
  (hg : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g)

/-- **The stopped locus and `H⁺` pull back** (`Zminus1_comap`; the functoriality argument in the
proof of [Kol07, Lemma 102]): `H⁺(g^*T) = g⁻¹(H⁺(T))`. -/
theorem hplus_pullback : hplus (T.pullback g hg) j = ⇑g ⁻¹' hplus T j := by
  change (⇑g ⁻¹' T.F.hyp j) \ BD.Zminus1 (T.I.pullback g g.contMDiff) 1 (⇑g ⁻¹' T.F.hyp j) =
    ⇑g ⁻¹' (T.F.hyp j \ BD.Zminus1 T.I 1 (T.F.hyp j))
  rw [BD.Zminus1_comap g hg T.I 1 (T.isSnc.1 j)]
  rfl

include hg in
/-- `g⁻¹(H⁺)` is a closed hypersurface of `N` (the preimage of a closed hypersurface under a local
analytic isomorphism, `preimage_of_isLocalDiffeomorph`). -/
theorem isClosedSubmanifold_preimage_hplus :
    IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (⇑g ⁻¹' hplus T j) 1 :=
  (isClosedSubmanifold_hplus T j).preimage_of_isLocalDiffeomorph hg

/-- **The restriction `g|_{H⁺} : g⁻¹(H⁺) → H⁺`** (Kollár's `h|_{E^j_Y}` in the proof of
[Kol07, Lemma 102]) between the bundled hypersurfaces. -/
abbrev hplusRestrictMap :
    AnalyticMap (isClosedSubmanifold_preimage_hplus T j g hg).toAnalyticManifold
      (isClosedSubmanifold_hplus T j).toAnalyticManifold :=
  (isClosedSubmanifold_preimage_hplus T j g hg).restrictMap (isClosedSubmanifold_hplus T j) g
    g.contMDiff fun _ hx => hx

theorem isLocalDiffeomorph_hplusRestrictMap :
    IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      (hplusRestrictMap T j g hg) :=
  IsClosedSubmanifold.isLocalDiffeomorph_restrictMap g hg _

/-- The restricted triple of `g^*T` on `g⁻¹(H⁺)` is the pull-back of the restricted triple of `T`
along `g|_{H⁺}` (pull-back and restriction commute, the proof of [Kol07, Lemma 102]): the ideal by
`pullback_inclusionMap_pullback`, the boundary by `emptyMember_comap` (the trace of the pulled-back
boundary is the pull-back of the trace, member by member). -/
theorem restrictedTripleModOf_isPullbackOf :
    (restrictedTripleModOf (T.pullback g hg) j (isClosedSubmanifold_preimage_hplus T j g hg)
        (hplus_pullback T j g hg).symm).IsPullbackOf (restrictedTripleMod T j)
      (hplusRestrictMap T j g hg) := by
  refine ⟨?_, ?_⟩
  · exact BD.pullback_inclusionMap_pullback g T.I (isClosedSubmanifold_hplus T j)
      (isClosedSubmanifold_preimage_hplus T j g hg)
  · change (isClosedSubmanifold_preimage_hplus T j g hg).traceFamily
        ((T.F.comap ⇑g).emptyMember j) =
      ((isClosedSubmanifold_hplus T j).traceFamily (T.F.emptyMember j)).comap
        ⇑(hplusRestrictMap T j g hg)
    rw [HypersurfaceFamily.emptyMember_comap]
    rfl

/-- The image under `g|_{H⁺}` of the trace `U' ∩ g⁻¹(H⁺)` is the trace `g(U') ∩ H⁺`. -/
theorem imageOpens_hplusRestrictMap_preimageOpens (U' : Opens N) :
    AnalyticMap.imageOpens (hplusRestrictMap T j g hg)
        (isLocalDiffeomorph_hplusRestrictMap T j g hg)
        ((isClosedSubmanifold_preimage_hplus T j g hg).preimageOpens U') =
      (isClosedSubmanifold_hplus T j).preimageOpens (AnalyticMap.imageOpens g hg U') := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(p : ⇑g ⁻¹' hplus T j).1, hp, rfl⟩
  · rintro ⟨x, hx, hgx⟩
    refine ⟨⟨x, ?_⟩, hx, Subtype.ext hgx⟩
    change g x ∈ hplus T j
    rw [hgx]
    exact (q : hplus T j).2

variable (hT' : AnalyticTriple.BMOClass 1 (T.pullback g hg)) (hRc : R.CommutesWithLocalIsos)

include hRc in
/-- **The modified core commutes with local analytic isomorphisms** (the functoriality argument in
the proof of [Kol07, Lemma 102]; [Wlo09, Theorem 7.4.1]; the counterpart of
`coreFamOn_commutesWithLocalIsos` without the first blow-up): the modified core of `g^*T` on `U'` is
the modified core of `T` on `g(U')` pulled back along `g|_{U'}`, with empty blow-ups deleted, given
that the functor `R` one dimension down commutes with local analytic isomorphisms. -/
theorem coreModOn_commutesWithLocalIsos (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))) :
    coreModOn R (T.pullback g hg) j hT' U' hU' =
      ((coreModOn R T j hT (AnalyticMap.imageOpens g hg U')
          (AnalyticMap.isCompact_closure_image g hU')).pullback
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
          Set.Subset.rfl)).eraseEmpty := by
  -- the left side, read on the closed hypersurface `g⁻¹(H⁺)`
  rw [coreModOn_eq_of_eq R (T.pullback g hg) j hT' (isClosedSubmanifold_preimage_hplus T j g hg)
    (hplus_pullback T j g hg).symm U' hU']
  -- the functor one dimension down commutes with `g|_{H⁺}` at the trace of `U'`, whose image is the
  -- trace of `g(U')`
  have htr := hRc (restrictedTripleMod T j)
    (restrictedTripleModOf (T.pullback g hg) j (isClosedSubmanifold_preimage_hplus T j g hg)
      (hplus_pullback T j g hg).symm)
    (hplusRestrictMap T j g hg) (isLocalDiffeomorph_hplusRestrictMap T j g hg)
    (restrictedTripleModOf_isPullbackOf T j g hg) (bmoClass_restrictedTripleMod T j hT)
    (bmoClass_restrictedTripleModOf (T.pullback g hg) j hT' _ _)
    ((isClosedSubmanifold_preimage_hplus T j g hg).preimageOpens U')
    ((isClosedSubmanifold_preimage_hplus T j g hg).isCompact_closure_preimageOpens U' hU')
  have htr' := htr.trans (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
    (CompatibleFamily.pullback_restrictMap_congr
      (R.fam (restrictedTripleMod T j) (bmoClass_restrictedTripleMod T j hT))
      (hplusRestrictMap T j g hg) (isLocalDiffeomorph_hplusRestrictMap T j g hg)
      ((isClosedSubmanifold_preimage_hplus T j g hg).preimageOpens U')
      (imageOpens_hplusRestrictMap_preimageOpens T j g hg U')
      (AnalyticMap.isCompact_closure_image _
        ((isClosedSubmanifold_preimage_hplus T j g hg).isCompact_closure_preimageOpens U' hU'))
      ((isClosedSubmanifold_hplus T j).isCompact_closure_preimageOpens _
        (AnalyticMap.isCompact_closure_image g hU'))
      Set.Subset.rfl
      ((isClosedSubmanifold_hplus T j).image_restrictMap_preimageOpens_subset g
        (isClosedSubmanifold_preimage_hplus T j g hg) Set.Subset.rfl)))
  -- the push-forward commutes with the pull-back along `g|_{U'}`; the erasures move through both
  unfold coreModOn coreModTrace
  rw [AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
    AnalyticManifold.BlowUpSequence.pushforwardRestrict_pullback_restrictMap
        (isClosedSubmanifold_hplus T j) g hg
      (isClosedSubmanifold_preimage_hplus T j g hg) U' (AnalyticMap.imageOpens g hg U')
      Set.Subset.rfl, htr',
          AnalyticManifold.BlowUpSequence.eraseEmpty_pushforwardRestrict_eraseEmpty]

include hRc in
/-- `coreModOn_commutesWithLocalIsos` for the compatible family `coreModFam` (the shape the
alignment of the links of the maximal-contact step takes). -/
theorem coreModFam_commutesWithLocalIsos (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))) :
    (coreModFam R (T.pullback g hg) j hT').seqOn U' hU' =
      (((coreModFam R T j hT).seqOn (AnalyticMap.imageOpens g hg U')
          (AnalyticMap.isCompact_closure_image g hU')).pullback
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
          Set.Subset.rfl)).eraseEmpty :=
  coreModOn_commutesWithLocalIsos R T j hT g hg hT' hRc U' hU'

end Comm

end Hironaka.Manifold.BMOmod

end
