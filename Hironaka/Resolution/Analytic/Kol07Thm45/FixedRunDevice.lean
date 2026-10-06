/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.LocalIsoTools
public import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductExceptionalFamily
public import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionOn
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Resolution.Analytic.Kol07Thm45.ExceptionalFamilyGlue
import Hironaka.Resolution.Analytic.Kol07Thm45.RunFamilyRestrict
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The fixed-run device with synchronised members

Kollár's descent of the centres from the disjoint union of a cover: the centre of the disjoint
union agrees on the overlaps, (37.2) in [Kol07, Proposition 37, proof], because the functor
commutes with smooth surjections [Kol07, 34.1]. Two local analytic isomorphisms `u v : N → M` with
the SAME pulled-back triple (`T.pullback u = T.pullback v` — the shear's ideal identity `hI` in the
application) pull the functor's run over a reading open `V ⊆ M` back to the SAME list over any
relatively compact open `W' ⊆ N` whose two images lie in `V`: this is
`seqOn_pullback_eq_of_pullback_eq` (`ExceptionalFamilyGlue.lean`) on the coproduct `P := N ⊔ M`
with the maps `id ⊔ u`, `id ⊔ v` (surjective, so both erasures are no-ops) at the reading open
`U' := W' ⊔ V` of `P`, READ ON THE `N`-SUMMAND (the restricted summand inclusion `N|W' → P|U'`,
`pullback_comp`). With the synchronisation of `RunFamilyRestrict.lean` it follows that, when `u`,
`v` are moreover open embeddings of one admissible input `T'`, the two open immersions
`localResolutionHomOn` of local resolutions pull every member of the run's boundary family back to
the SAME closed subspace — the stage-`σ` member on one side IS the stage-`σ` member on the other,
no label chosen (the label is a stage of the one run).

The user is the transition between a padded piece and a piece of the other embedding in the common
datum `sumPadData D₁ D₂` (`CoproductSumData.lean`, `CoproductMixedTransition.lean`):
`u := sigmaMk (inl i) ∘ …`, `v := sigmaMk (inr j) ∘ … ∘ g` with the shear `g` of
`exists_padded_equivalence_hom_point`. `hbed` is the only hypothesis. Not in the sources beyond
Kollár's descent; bookkeeping.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set AnalyticManifold.BlowUpSequence
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜]

section SumOpens

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {N M : AnalyticManifold.{u} 𝕜 E} (W' : Opens N) (V : Opens M)

/-- **The reading open `W' ⊔ V` of the coproduct `N ⊔ M`** — the union of the two summand
images. -/
def sumOpens : Opens (sigmaManifold (sumFamily N M)) :=
  ⟨(⇑(sumInl (N := N) (M := M)) '' (W' : Set N)) ∪
    (⇑(sigmaMk (sumFamily N M) (ULift.up false)) '' (V : Set M)),
    (isOpenMap_sigmaMk (σ := fun b => (sumFamily N M b : Type u)) _ W'.isOpen).union
      (isOpenMap_sigmaMk (σ := fun b => (sumFamily N M b : Type u)) _ V.isOpen)⟩

/-- The first summand's image lies in the coproduct's reading open `sumOpens`. -/
theorem image_sumInl_subset_sumOpens :
    ⇑(sumInl (N := N) (M := M)) '' (W' : Set N) ⊆
      (sumOpens W' V : Set (sigmaManifold (sumFamily N M))) :=
  Set.subset_union_left

/-- Relatively compact summands give a relatively compact reading open of the coproduct. -/
theorem isCompact_closure_sumOpens (hW' : IsCompact (closure (W' : Set N)))
    (hV : IsCompact (closure (V : Set M))) :
    IsCompact (closure (sumOpens W' V : Set (sigmaManifold (sumFamily N M)))) := by
  change IsCompact (closure (_ ∪ _))
  rw [closure_union]
  exact (AnalyticMap.isCompact_closure_image (sumInl (N := N) (M := M)) hW').union
    (AnalyticMap.isCompact_closure_image (sigmaMk (sumFamily N M) (ULift.up false)) hV)

/-- `id ⊔ w` maps `W' ⊔ V` into `V` when `w(W') ⊆ V`. -/
theorem image_sigmaDescMap_sumDesc_sumOpens_subset (w : AnalyticMap N M)
    (hwV : ⇑w '' (W' : Set N) ⊆ (V : Set M)) :
    ⇑(sigmaDescMap (sumDesc w)) '' (sumOpens W' V : Set (sigmaManifold (sumFamily N M))) ⊆
      (V : Set M) := by
  rintro _ ⟨p, hp | hp, rfl⟩
  · obtain ⟨x, hx, rfl⟩ := hp
    exact hwV ⟨x, hx, rfl⟩
  · obtain ⟨y, hy, rfl⟩ := hp
    exact hy

/-- `id ⊔ w` maps `W' ⊔ V` ONTO `V` (the `M`-summand). -/
theorem subset_image_sigmaDescMap_sumDesc_sumOpens (w : AnalyticMap N M) :
    (V : Set M) ⊆
      ⇑(sigmaDescMap (sumDesc w)) '' (sumOpens W' V : Set (sigmaManifold (sumFamily N M))) :=
  fun y hy => ⟨sigmaMk (sumFamily N M) (ULift.up false) y, Or.inr ⟨y, hy, rfl⟩, rfl⟩

end SumOpens

namespace BEDanFamStar

open _root_.Manifold

variable (bed : BEDanFamStar.{u} 𝕜) {n : ℕ}
  {M N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
  (hbed : bed.IsEmbeddedDesing)

include hbed in
/-- **The fixed-run device read on a summand** ((37.1)–(37.2) in [Kol07, Proposition 37, proof];
[Kol07, 34.1]) — two local analytic isomorphisms `u v : N → M` with the SAME pulled-back triple
pull the run over `V` back to the SAME list over any relatively compact `W' ⊆ N` with `u(W') ⊆ V`,
`v(W') ⊆ V`: `seqOn_pullback_eq_of_pullback_eq` on `N ⊔ M` with the surjective maps `id ⊔ u`,
`id ⊔ v` at the reading open `W' ⊔ V`, then the restricted summand inclusion
`N|W' → (N ⊔ M)|W' ⊔ V` (`pullback_comp`). -/
theorem seqOn_pullback_restrictMap_eq_of_pullback_eq (u v : AnalyticMap N M)
    (hu : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω u)
    (hv : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω v)
    (huv : T.pullback u hu = T.pullback v hv) (V : Opens M) (hV : IsCompact (closure (V : Set M)))
    (W' : Opens N) (hW' : IsCompact (closure (W' : Set N)))
    (huV : ⇑u '' (W' : Set N) ⊆ (V : Set M)) (hvV : ⇑v '' (W' : Set N) ⊆ (V : Set M)) :
    (bed.seqOn T hT V hV).pullback (AnalyticMap.restrictMap u W' V huV)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hu W' V huV) =
      (bed.seqOn T hT V hV).pullback (AnalyticMap.restrictMap v W' V hvV)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hv W' V hvV) := by
  have ha : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (sigmaDescMap (sumDesc u)) :=
    isLocalDiffeomorph_sigmaDescMap _ (isLocalDiffeomorph_sumDesc hu)
  have hb : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (sigmaDescMap (sumDesc v)) :=
    isLocalDiffeomorph_sigmaDescMap _ (isLocalDiffeomorph_sumDesc hv)
  have hab : T.pullback (sigmaDescMap (sumDesc u)) ha = T.pullback (sigmaDescMap (sumDesc v)) hb :=
    AnalyticTriple.pullback_sigmaDescMap_sumDesc_eq T u v hu hv huv
  have hTP : DomBEDan 𝕜 (T.pullback (sigmaDescMap (sumDesc u)) ha) :=
    domBEDan_pullback_sigmaDescMap_sumDesc T hT u hu
  have hc3 := bed.seqOn_pullback_eq_of_pullback_eq hbed T hT _ _ ha hb hab hTP (sumOpens W' V)
    (isCompact_closure_sumOpens W' V hW' hV) V hV
    (image_sigmaDescMap_sumDesc_sumOpens_subset W' V u huV)
    (subset_image_sigmaDescMap_sumDesc_sumOpens W' V u)
    (image_sigmaDescMap_sumDesc_sumOpens_subset W' V v hvV)
    (subset_image_sigmaDescMap_sumDesc_sumOpens W' V v)
  -- the restricted summand inclusion `N|W' → (N ⊔ M)|W' ⊔ V`
  have hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      (AnalyticMap.restrictMap (sumInl (N := N) (M := M)) W' (sumOpens W' V)
        (image_sumInl_subset_sumOpens W' V)) :=
    AnalyticMap.isLocalDiffeomorph_restrictMap (isLocalDiffeomorph_sigmaMk (sumFamily N M)
      (ULift.up true)) W' _ _
  have key : ∀ (w : AnalyticMap N M)
      (hw : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω w)
      (hwV : ⇑w '' (W' : Set N) ⊆ (V : Set M))
      (hwU : ⇑(sigmaDescMap (sumDesc w)) '' (sumOpens W' V : Set _) ⊆ (V : Set M))
      (hw' : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (sigmaDescMap (sumDesc w)))
      (hcomp : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
        ((AnalyticMap.restrictMap (sigmaDescMap (sumDesc w)) (sumOpens W' V) V hwU).comp
          (AnalyticMap.restrictMap (sumInl (N := N) (M := M)) W' (sumOpens W' V)
            (image_sumInl_subset_sumOpens W' V)))),
      ((bed.seqOn T hT V hV).pullback
          (AnalyticMap.restrictMap (sigmaDescMap (sumDesc w)) (sumOpens W' V) V hwU)
          (AnalyticMap.isLocalDiffeomorph_restrictMap hw' _ _ hwU)).pullback
        (AnalyticMap.restrictMap (sumInl (N := N) (M := M)) W' (sumOpens W' V)
          (image_sumInl_subset_sumOpens W' V)) hι =
      (bed.seqOn T hT V hV).pullback (AnalyticMap.restrictMap w W' V hwV)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hw W' V hwV) := by
    intro w hw hwV hwU hw' hcomp
    rw [pullback_comp _ _ _ _ _]
    have e : (AnalyticMap.restrictMap (sigmaDescMap (sumDesc w)) (sumOpens W' V) V hwU).comp
        (AnalyticMap.restrictMap (sumInl (N := N) (M := M)) W' (sumOpens W' V)
          (image_sumInl_subset_sumOpens W' V)) = AnalyticMap.restrictMap w W' V hwV :=
      Subtype.ext (funext fun _ => rfl)
    exact (fun (k : AnalyticMap (N.restrict W') (M.restrict V))
      (hk : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω k) (e : _ = k) => by
        subst e; rfl) (AnalyticMap.restrictMap w W' V hwV)
      (AnalyticMap.isLocalDiffeomorph_restrictMap hw W' V hwV) e
  rw [← key u hu huV (image_sigmaDescMap_sumDesc_sumOpens_subset W' V u huV) ha
      (isLocalDiffeomorph_comp (AnalyticMap.isLocalDiffeomorph_restrictMap ha _ _ _) hι),
    ← key v hv hvV (image_sigmaDescMap_sumDesc_sumOpens_subset W' V v hvV) hb
      (isLocalDiffeomorph_comp (AnalyticMap.isLocalDiffeomorph_restrictMap hb _ _ _) hι),
    hc3]

variable (V : Opens M) (hV : IsCompact (closure (V : Set M)))
  (T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) N) (hT' : DomBEDan 𝕜 T')
  (u v : AnalyticMap N M) (hu : IsAnalyticOpenEmbedding u)
  (hv : IsAnalyticOpenEmbedding v) (hpu : T'.IsPullbackOf T u) (hpv : T'.IsPullbackOf T v)
  (W' : Opens N) (hW' : IsCompact (closure (W' : Set N)))
  (huV : ⇑u '' (W' : Set N) ⊆ (V : Set M)) (hvV : ⇑v '' (W' : Set N) ⊆ (V : Set M))

/-- **The fixed-run device with synchronised members** ((37.2) in [Kol07, Proposition 37, proof])
— two open embeddings `u`, `v` of ONE admissible input `(T', W')` into `(T, V)` pull every member of
the run on `T` back along the two open immersions of local resolutions to the SAME closed subspace:
the two pulled-back triples coincide (`ext'`), hence the two pulled-back runs (the device above),
hence the members (`comap_localResolutionHomOn_runMembers_eq_of_pullback_eq`,
`RunFamilyRestrict.lean`). -/
theorem comap_localResolutionHomOn_runMembers_eq_of_isPullbackOf
    (σ : (bed.runFamily T hT V hV).ι) :
    AnalyticSpace.QuotientSpace.comap
        (bed.localResolutionHomOn T hT V hV T' hT' u hu hpu W' hW' huV hbed).1
        (bed.runMembers T hT V hV hbed σ) =
      AnalyticSpace.QuotientSpace.comap
        (bed.localResolutionHomOn T hT V hV T' hT' v hv hpv W' hW' hvV hbed).1
        (bed.runMembers T hT V hV hbed σ) := by
  have huv : T.pullback u hu.1 = T.pullback v hv.1 :=
    (AnalyticTriple.ext' hpu.1.symm hpu.2.symm).trans
      (AnalyticTriple.ext' hpv.1.symm hpv.2.symm).symm
  exact bed.comap_localResolutionHomOn_runMembers_eq_of_pullback_eq T hT V hV hbed T' hT' W' hW'
    u v hu hv hpu hpv huV hvV
    (bed.seqOn_pullback_restrictMap_eq_of_pullback_eq T hT hbed u v hu.1 hv.1 huv V hV W' hW'
      huV hvV) σ

end BEDanFamStar

end Hironaka.Manifold

end
