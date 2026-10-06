/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.LocalIsoTools
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceResolution
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.FiniteSuccession.Functor.SigmaTriple
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionShear
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The fixed-run device: two local isomorphisms with the same pulled-back triple

Kollár descends the blow-up sequence of the disjoint union `X' = ⊔ Uᵢ` of an affine cover to `X`
through the two surjective open immersions `τ₁, τ₂ : X'' → X'` from `X'' = ⊔ Uᵢ ∩ Uⱼ`: since the
functor commutes with `τ₁` and `τ₂`, the pulled-back centres agree, `τ₁^* Z₀' = Z₀'' = τ₂^* Z₀'`
((37.1) in [Kol07, Proposition 37, proof]), because the functor commutes with smooth surjections
[Kol07, 34.1]. Here the synchronisation of two runs is obtained by running the functor on ONE
input `P` with two SURJECTIVE local analytic isomorphisms `a b : P → M` onto the same fixed
reading open — the device of `seq_pullback_eq_eraseEmpty` (`Functor/LocalIsoTools.lean`, the
sequence level) at the FAMILY level, where `bed.seqOn` is what the runs are. The clause of the
family functor is `CommutesWithLocalIsos` (`Functor/Family.lean`): the value on the pulled-back
triple over `U'` is the pull-back along `g|U'` of the value over the image open with the empty
blow-ups ERASED; for a SURJECTION onto the fixed reading open the erasure is a no-op
(`eraseEmpty_pullback_of_surjective`, `Functor/PullbackInj.lean`; the first bullet of
[Kol07, 34.1]), so the identity holds as an equality of WHOLE `CenterList`s, stage by stage — the
same fact `CommutesWithSurjectiveLocalIsos` (`Functor/Basic.lean`; its consequence `commutesWith`
in `Functor/SigmaTriple.lean`) states at the sequence level.

* `seqOn_pullback_eq_of_isLocalDiffeomorph` — `seqOn_eq_of_isAnalyticOpenEmbedding`
  (`LocalResolutionOn.lean`) for an arbitrary local analytic isomorphism `a` in place of an open
  embedding: the value on `T.pullback a` over `U'` is the erased pull-back along `a|U' : U' → V` of
  the value over any relatively compact `V ⊇ a(U')` (the clause at `a` and `U'`, the family's
  restriction compatibility from `a(U')` up to `V`, `eraseEmpty_pullback_eraseEmpty`,
  `pullback_comp` — the same proof);
* `seqOn_pullback_eq_of_pullback_eq` — the device: two local isomorphisms `a b : P → M` with the
  SAME pulled-back triple (`T.pullback a = T.pullback b`) whose images of the reading open `U'` are
  BOTH the fixed open `V` (the reading-open hypothesis, in the binders) pull the run over `V` back
  to the SAME list. Nothing here is specific to a particular functor: the lemma holds for every
  `bed` under `hbed : bed.IsEmbeddedDesing`.
* the coproduct maps: `AnalyticTriple.pullback_sigmaDescMap_sumDesc_eq` — two local isomorphisms
  `u v : N → M` with the same pulled-back triple give the same pulled-back triple along
  `sigmaDescMap (sumDesc u)`, `sigmaDescMap (sumDesc v) : M ⊔ N → M` (`id` on the `M` summand; an
  ideal sheaf on a disjoint union is determined by its restrictions to the summands,
  `IdealSheaf.ext_of_comap_sigmaMk`, stalkwise along the bijective germ maps of the inclusions),
  `domBEDan_pullback_sigmaDescMap_sumDesc` (the coproduct input is admissible), and
  `BlowUpSequence.pullback_eq_of_pullback_sigmaDescMap_sumDesc_eq` (the whole-list equality read on
  the `N` summand through `sumInl`, `pullback_comp`, `sigmaDescMap_comp_sigmaMk`).

The generic reading on a summand of `N ⊔ M` and the form with synchronised members — Kollár's
(37.2) for the FIXED member of a stage — are in `FixedRunDevice.lean`; the instance with the shear
`g` of `exists_padded_equivalence_hom_point` (`u`, `v` the two embeddings of the shear's domain
into the common datum's coproduct ambient) is `exists_mixedTransition_sumPadData` in
`CoproductMixedTransition.lean`. `IsEmbeddedDesing` enters only through `hbed`. Not in the sources
beyond Kollár's descent; bookkeeping.
-/

public section

noncomputable section

open TopologicalSpace Set AnalyticManifold.BlowUpSequence
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BEDanFamStar

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] (bed : BEDanFamStar.{u} 𝕜) {n : ℕ}
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-- The value of the functor depends only on the triple — the transport along an equality of
triples, `DomBEDan` being a proposition. -/
theorem seqOn_congr_triple {T₁ T₂ : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M}
    (e : T₁ = T₂) (h₁ : DomBEDan 𝕜 T₁) (h₂ : DomBEDan 𝕜 T₂) (W : Opens M)
    (hW : IsCompact (closure (W : Set M))) :
    bed.seqOn T₁ h₁ W hW = bed.seqOn T₂ h₂ W hW := by
  subst e
  rfl

variable {P : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-- `seqOn_eq_of_isAnalyticOpenEmbedding` for a local isomorphism ([Kol07, 34.1]): for an
arbitrary local analytic isomorphism `a : P → M` (not only an open embedding) the value on the
pulled-back triple over `U'` is the pull-back along `a|U' : U' → V` of the value over `V ⊇ a(U')`,
empty blow-ups erased — `hbed`'s `CommutesWithLocalIsos` at `a` and `U'` (onto the image open
`a(U')`), the family's restriction compatibility from `a(U')` up to `V`,
`eraseEmpty_pullback_eraseEmpty` and `pullback_comp` (the proof of
`seqOn_eq_of_isAnalyticOpenEmbedding` verbatim, `hg.1` read as `ha`). -/
theorem seqOn_pullback_eq_of_isLocalDiffeomorph (hbed : bed.IsEmbeddedDesing)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
    (a : AnalyticMap P M)
        (ha : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω a)
    (hTa : DomBEDan 𝕜 (T.pullback a ha)) (U' : Opens P) (hU' : IsCompact (closure (U' : Set P)))
    (V : Opens M) (hV : IsCompact (closure (V : Set M))) (hle : a '' (U' : Set P) ⊆ (V : Set M)) :
    bed.seqOn (T.pullback a ha) hTa U' hU' =
      ((bed.seqOn T hT V hV).pullback (AnalyticMap.restrictMap a U' V hle)
        (AnalyticMap.isLocalDiffeomorph_restrictMap ha U' V hle)).eraseEmpty := by
  have h1 := hbed.2 n T (T.pullback a ha) a ha ⟨rfl, rfl⟩ hT hTa U' hU'
  have himg : AnalyticMap.imageOpens a ha U' ≤ V := fun _ hx => hle hx
  have h2 := ((bed.fam n).fam T hT).compat (AnalyticMap.imageOpens a ha U') V
    (AnalyticMap.isCompact_closure_image a hU') hV himg
  have hcomp : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      ((M.restrictLE himg).comp (AnalyticMap.restrictMap a U' (AnalyticMap.imageOpens a ha U')
        Set.Subset.rfl)) :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_restrictLE himg)
      (AnalyticMap.isLocalDiffeomorph_restrictMap ha U' _ Set.Subset.rfl)
  have key : ∀ (k : AnalyticMap (P.restrict U') (M.restrict V))
      (hk : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω k),
      (M.restrictLE himg).comp (AnalyticMap.restrictMap a U' (AnalyticMap.imageOpens a ha U')
        Set.Subset.rfl) = k →
      (((bed.fam n).fam T hT).seqOn V hV).pullback ((M.restrictLE himg).comp
        (AnalyticMap.restrictMap a U' (AnalyticMap.imageOpens a ha U') Set.Subset.rfl))
          hcomp = (((bed.fam n).fam T hT).seqOn V hV).pullback k hk := by
    rintro k hk rfl
    rfl
  change ((bed.fam n).fam (T.pullback a ha) hTa).seqOn U' hU' = _
  rw [h1, h2, eraseEmpty_pullback_eraseEmpty, pullback_comp _ _ _ _ _,
    key (AnalyticMap.restrictMap a U' V hle)
      (AnalyticMap.isLocalDiffeomorph_restrictMap ha U' V hle)
      (Subtype.ext (funext fun _ => rfl))]
  rfl

/-- The restriction of `a` to `U'` is ONTO `V` when `V ⊆ a(U')`. -/
theorem surjective_restrictMap_of_subset_image (a : AnalyticMap P M)
    (U' : Opens P)
    (V : Opens M) (hle : a '' (U' : Set P) ⊆ (V : Set M)) (hge : (V : Set M) ⊆ a '' (U' : Set P)) :
    Function.Surjective (AnalyticMap.restrictMap a U' V hle) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := hge hy
  exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩

/-- **The fixed-run device** ((37.1) in [Kol07, Proposition 37, proof]; the commutation with smooth
surjections, [Kol07, 34.1]) — two SURJECTIVE local isomorphisms `a b : P → M` whose pulled-back
triples COINCIDE and whose images of the reading open `U'` are the SAME relatively compact open `V`
pull the run over `V` back to the SAME list — the family clause at `a` and at `b` has the same left
side, and both erasures are no-ops. -/
theorem seqOn_pullback_eq_of_pullback_eq (hbed : bed.IsEmbeddedDesing)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
    (a b : AnalyticMap P M)
    (ha : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω a)
    (hb : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω b)
    (hab : T.pullback a ha = T.pullback b hb) (hTP : DomBEDan 𝕜 (T.pullback a ha))
    (U' : Opens P) (hU' : IsCompact (closure (U' : Set P)))
    (V : Opens M) (hV : IsCompact (closure (V : Set M)))
    (haV : a '' (U' : Set P) ⊆ (V : Set M)) (haV' : (V : Set M) ⊆ a '' (U' : Set P))
    (hbV : b '' (U' : Set P) ⊆ (V : Set M)) (hbV' : (V : Set M) ⊆ b '' (U' : Set P)) :
    (bed.seqOn T hT V hV).pullback (AnalyticMap.restrictMap a U' V haV)
        (AnalyticMap.isLocalDiffeomorph_restrictMap ha U' V haV) =
      (bed.seqOn T hT V hV).pullback (AnalyticMap.restrictMap b U' V hbV)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hb U' V hbV) := by
  have hTb : DomBEDan 𝕜 (T.pullback b hb) := hab ▸ hTP
  have hne : (bed.seqOn T hT V hV).NoEmptyCenters := ((bed.fam n).fam T hT).noEmptyCenters V hV
  have ea := bed.seqOn_pullback_eq_of_isLocalDiffeomorph hbed T hT a ha hTP U' hU' V hV haV
  have eb := bed.seqOn_pullback_eq_of_isLocalDiffeomorph hbed T hT b hb hTb U' hU' V hV hbV
  rw [eraseEmpty_pullback_of_surjective _ hne _ _
    (surjective_restrictMap_of_subset_image a U' V haV haV')] at ea
  rw [eraseEmpty_pullback_of_surjective _ hne _ _
    (surjective_restrictMap_of_subset_image b U' V hbV hbV')] at eb
  rw [← ea, ← eb]
  exact bed.seqOn_congr_triple hab hTP hTb U' hU'

end Hironaka.Manifold.BEDanFamStar

namespace Manifold

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

section SigmaExt

variable {σ : Type u} [Countable σ] (N : σ → AnalyticManifold.{u} 𝕜 E)

/-- An ideal sheaf on a disjoint union is determined by its restrictions to the summands —
stalkwise, the germ map along the summand inclusion is bijective
(`germMap_bijective_of_isLocalDiffeomorphAt`). -/
theorem IdealSheaf.ext_of_comap_sigmaMk (J₁ J₂ : AnalyticManifold.IdealSheaf (sigmaManifold N))
    (h : ∀ i, J₁.pullback _ (sigmaMk N i).contMDiff =
      J₂.pullback _ (sigmaMk N i).contMDiff) : J₁ = J₂ := by
  refine IdealSheaf.ext fun p => ?_
  obtain ⟨i, y⟩ := p
  have hb : Function.Bijective (germMap ⇑(sigmaMk N i) (sigmaMk N i).contMDiff y) :=
    germMap_bijective_of_isLocalDiffeomorphAt ⇑(sigmaMk N i) (sigmaMk N i).contMDiff
      (isLocalDiffeomorph_sigmaMk N i y)
  have e := congrArg (fun J : AnalyticManifold.IdealSheaf (N i) => J.stalkIdeal y) (h i)
  change ((J₁.pullback ⇑(sigmaMk N i) (sigmaMk N i).contMDiff).stalkIdeal y) =
    ((J₂.pullback ⇑(sigmaMk N i) (sigmaMk N i).contMDiff).stalkIdeal y) at e
  rw [IdealSheaf.stalkIdeal_pullback, IdealSheaf.stalkIdeal_pullback] at e
  have e' := congrArg (Ideal.comap (germMap ⇑(sigmaMk N i) (sigmaMk N i).contMDiff y)) e
  rwa [Ideal.comap_map_of_bijective _ hb, Ideal.comap_map_of_bijective _ hb] at e'

end SigmaExt

section Sum

variable {n : ℕ} {M N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-- Equal inverse images of a hypersurface family along `u` and `v` have equal preimages of every
member. -/
theorem HypersurfaceFamily.preimage_eq_of_comap_eq (F : HypersurfaceFamily M) {u v : N → M}
    (h : F.comap u = F.comap v) (j : F.ι) : u ⁻¹' F.hyp j = v ⁻¹' F.hyp j := by
  have h' : HypersurfaceFamily.mk F.ι (fun j => u ⁻¹' F.hyp j) =
      HypersurfaceFamily.mk F.ι (fun j => v ⁻¹' F.hyp j) := h
  rw [HypersurfaceFamily.mk.injEq] at h'
  obtain ⟨-, -, hh⟩ := h'
  exact congrFun (eq_of_heq hh) j

/-- **The device's INPUT** — two local isomorphisms `u v : N → M` with the same pulled-back triple
give the same pulled-back triple along the two coproduct maps `sigmaDescMap (sumDesc u)`,
`sigmaDescMap (sumDesc v) : M ⊔ N → M` (`id` on the `M` summand). -/
theorem AnalyticTriple.pullback_sigmaDescMap_sumDesc_eq
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (u v : AnalyticMap N M)
    (hu : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω u)
    (hv : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω v)
    (huv : T.pullback u hu = T.pullback v hv) :
    T.pullback (sigmaDescMap (sumDesc u))
        (isLocalDiffeomorph_sigmaDescMap _ (isLocalDiffeomorph_sumDesc hu)) =
      T.pullback (sigmaDescMap (sumDesc v))
        (isLocalDiffeomorph_sigmaDescMap _ (isLocalDiffeomorph_sumDesc hv)) := by
  have hI : T.I.pullback u u.contMDiff = T.I.pullback v v.contMDiff := congrArg AnalyticTriple.I huv
  have hF : T.F.comap u = T.F.comap v := congrArg AnalyticTriple.F huv
  have hI' : T.I.pullback _ (sigmaDescMap (sumDesc u)).contMDiff = T.I.pullback _ (sigmaDescMap
      (sumDesc v)).contMDiff := by
    refine IdealSheaf.ext_of_comap_sigmaMk (sumFamily N M) _ _ fun b => ?_
    rw [AnalyticManifold.IdealSheaf.pullback_comp, AnalyticManifold.IdealSheaf.pullback_comp,
      sigmaDescMap_comp_sigmaMk, sigmaDescMap_comp_sigmaMk]
    rcases b with ⟨_ | _⟩
    · rfl
    · exact hI
  have hF' : T.F.comap (sigmaDescMap (sumDesc u)) = T.F.comap (sigmaDescMap (sumDesc v)) := by
    refine congrArg (HypersurfaceFamily.mk T.F.ι) (funext fun j => Set.ext fun p => ?_)
    obtain ⟨⟨_ | _⟩, x⟩ := p
    · exact Iff.rfl
    · exact Set.ext_iff.mp (T.F.preimage_eq_of_comap_eq hF j) x
  exact AnalyticTriple.ext' hI' hF'

/-- The pulled-back triple along the coproduct map is in `DomBEDan` when `T` is — the divisor
stays empty and the ideal reduced (`isReduced_pullback_of_isLocalDiffeomorph`). -/
theorem _root_.Hironaka.Manifold.domBEDan_pullback_sigmaDescMap_sumDesc
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
    (u : AnalyticMap N M)
    (hu : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω u) :
    DomBEDan 𝕜 (T.pullback (sigmaDescMap (sumDesc u))
      (isLocalDiffeomorph_sigmaDescMap _ (isLocalDiffeomorph_sumDesc hu))) :=
  ⟨hT.1, IdealSheaf.isReduced_pullback_of_isLocalDiffeomorph _
    (isLocalDiffeomorph_sigmaDescMap _ (isLocalDiffeomorph_sumDesc hu)) hT.2⟩

/-- A whole-list equality of pull-backs along the two coproduct maps, read on the `N` summand
(`sumInl`; `pullback_comp`, `sigmaDescMap_comp_sigmaMk`), is the equality of the pull-backs along
`u` and `v`. -/
theorem _root_.AnalyticManifold.BlowUpSequence.pullback_eq_of_pullback_sigmaDescMap_sumDesc_eq
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
        (u v : AnalyticMap N M)
    (hu : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω u)
    (hv : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω v)
    (h : L.pullback (sigmaDescMap (sumDesc u))
        (isLocalDiffeomorph_sigmaDescMap _ (isLocalDiffeomorph_sumDesc hu)) =
      L.pullback (sigmaDescMap (sumDesc v))
        (isLocalDiffeomorph_sigmaDescMap _ (isLocalDiffeomorph_sumDesc hv))) :
    L.pullback u hu = L.pullback v hv := by
  have hinl : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (sumInl (N := N) (M := M)) :=
    isLocalDiffeomorph_sigmaMk _ _
  have key : ∀ (w : AnalyticMap N M)
      (hw : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω w)
      (hcomp : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
        ((sigmaDescMap (sumDesc w)).comp sumInl)),
      (L.pullback (sigmaDescMap (sumDesc w))
        (isLocalDiffeomorph_sigmaDescMap _ (isLocalDiffeomorph_sumDesc hw))).pullback sumInl hinl =
        L.pullback w hw := by
    intro w hw hcomp
    rw [pullback_comp _ _ _ _ _]
    have e : (sigmaDescMap (sumDesc w)).comp sumInl = w := sigmaDescMap_comp_sigmaMk _ _
    exact (fun (k : AnalyticMap N M) (hk)
      (e : (sigmaDescMap (sumDesc w)).comp sumInl = k) => by subst e; rfl) w hw e
  have hcu : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      ((sigmaDescMap (sumDesc u)).comp sumInl) :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_sigmaDescMap _ (isLocalDiffeomorph_sumDesc hu)) hinl
  have hcv : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      ((sigmaDescMap (sumDesc v)).comp sumInl) :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_sigmaDescMap _ (isLocalDiffeomorph_sumDesc hv)) hinl
  rw [← key u hu hcu, ← key v hv hcv, h]

end Sum

end Manifold

end
