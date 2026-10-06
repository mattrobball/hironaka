/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Principalization.IsoOff
public import Hironaka.Resolution.Analytic.OrderReduction.Step21Fam
public import Hironaka.Resolution.Analytic.Principalization.Assembly
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.EraseEmptyConcat
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.Principalization.BoundaryConcat
import Hironaka.Resolution.Analytic.Principalization.ClauseOne
import Hironaka.Resolution.Analytic.Principalization.DisjoinLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Clause (3) of the principalization family: an isomorphism off `cosupp 𝓘 ∪ Sing E`

Clause (3) of [Kol07, Theorem 35] in the form that holds with the disjoining blow-ups included,
per open: the composite blow-down of the value on `U` is an analytic isomorphism over
`U ∖ (cosupp 𝓘|U ∪ Sing E|U)` (Kollár's "over `X ∖ cosupp I`" fails for the disjoining blow-ups,
whose centres lie in the multiple locus `Sing E`). By `isAnalyticIsoOver_stageMap` (condition (1)
of Bierstone–Milman's blowing-up [BM88, Definition 4.1], iterated) it suffices that every centre
lies over `cosupp 𝓘|U ∪ Sing E|U`:

* the disjoining centres lie over `Sing E|U` (`centersOver_disjoinList`; [Kol07, 72]);
* the order-reduction centres lie over `cosupp 𝓘|U`: a centre of a sequence of order `≥ 1` for
  `(𝓘, 1)` lies in the cosupport of the marked transform there (clause (4′) of
  [Kol07, Definition 66], `1 ≤ ord_Z I_i` at every point of `Z`, read by `le_ordAlongIdeal_iff` at
  `p = 1`), and the cosupport of the marked transform lies over the cosupport of `𝓘`
  (`cosupport_markedTransformSeqAux_subset`: the birational transform contains the total
  transform, `cosupport_birationalTransform_I_subset`, whose cosupport is the preimage,
  `cosupport_pullback`) — `CentersOver.of_isOfOrderGe`;
* the concatenation (`centersOver_concat`) and the deletion of the empty rounds — the composite
  blow-downs of a list and of its cleaned list agree through `eraseEmptyLast`
  (`stageMap_last_eraseEmptyLast`), so the analytic-isomorphism-over predicate transports
  (`IsIsoOver.of_comp_diffeomorph`).

Włodarczyk's corresponding statement is that the canonical principalization is an isomorphism over
`M_Z ∖ V(I)` [Wlo09, Lemma 4.0.3].
-/

public section

universe u

open Set TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-! ### The cosupport of the marked transforms -/

/-- The birational transform of a marked ideal sheaf contains the total transform, so its
cosupport lies in the preimage of the cosupport (the unit ideal when no exceptional divisor
exists). -/
theorem _root_.Hironaka.Manifold.cosupport_birationalTransform_I_subset
    {M' : AnalyticManifold.{u} 𝕜 E} {π : M' → M} {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
    (J : MarkedIdealSheaf (structureSheaf 𝕜 E M)) :
    (MarkedIdealSheaf.birationalTransform hY h J).I.support ⊆ π ⁻¹' J.I.support := by
  intro a ha
  rw [Set.mem_preimage, IdealSheaf.mem_support]
  rw [IdealSheaf.mem_support] at ha
  intro htop
  apply ha
  unfold MarkedIdealSheaf.birationalTransform
  dsimp only
  split_ifs with hex
  · rw [Classical.choose_spec hex a]
    have htot : (J.I.pullback π h.contMDiff).stalkIdeal a = ⊤ := by
      rw [IdealSheaf.stalkIdeal_pullback, htop, Ideal.map_top]
    rw [htot]
    exact (Ideal.eq_top_iff_one _).mpr (Submodule.mem_colon.mpr fun _ _ => Submodule.mem_top)
  · exact IdealSheaf.stalkIdeal_top a

/-- The cosupport of the marked transform at stage `i` lies over the cosupport of `𝓘`. -/
theorem cosupport_markedTransformSeqAux_subset (J : IdealSheaf M) (m : ℕ) :
    ∀ (i : ℕ) (h : i < S.length + 1),
      (S.markedTransformSeqAux J m i h).support ⊆ S.stageMapAux i h ⁻¹' J.support
  | 0, _ => fun _ ha => ha
  | i + 1, h => fun _ ha =>
    cosupport_markedTransformSeqAux_subset J m i (Nat.lt_of_succ_lt h)
      (Hironaka.Manifold.cosupport_birationalTransform_I_subset
        (S.isClosedSubmanifold_center ⟨i, Nat.lt_of_succ_lt_succ h⟩)
        (S.isBlowUp_map ⟨i, Nat.lt_of_succ_lt_succ h⟩) _ ha)

/-- Clause (4′) of [Kol07, Definition 66] read on the cosupports: **the centres of a sequence of
order `≥ m ≥ 1` lie over the cosupport of `𝓘`** — a centre lies in the cosupport of the marked
transform at its stage (`ord_Z I_i ≥ 1` at every point of `Z`), which lies over the cosupport of
`𝓘`. -/
theorem CentersOver.of_isOfOrderGe {I E₀ : IdealSheaf M} {m : ℕ} (h : S.IsOfOrderGe I m E₀)
    (hm : 1 ≤ m) : S.CentersOver I.support := by
  intro i a ha
  have h1 : ((1 : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (S.center i)
      (S.markedTransformSeq I m i.castSucc) a :=
    le_trans (Nat.cast_le.mpr hm) ((h i).2 a ha)
  have h2 := (IdealSheaf.le_ordAlongIdeal_iff (S.center i)
    (S.markedTransformSeq I m i.castSucc) a 1).mp h1
  rw [pow_one] at h2
  have hne : (S.markedTransformSeq I m i.castSucc).stalkIdeal a ≠ ⊤ := fun htop => by
    rw [htop, top_le_iff] at h2
    exact (IdealSheaf.mem_support (S.center i)).mp ha h2
  exact S.cosupport_markedTransformSeqAux_subset I m i.castSucc.1 i.castSucc.2 hne

end AnalyticManifold.FiniteSuccession

namespace Hironaka.Manifold

open _root_.Manifold

section General

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### Transport of `IsAnalyticIsoOver` along an analytic isomorphism of the source -/

/-- If `f ∘ φ = g` for an analytic isomorphism `φ` of the sources, then `f` is an analytic
isomorphism over `U` when `g` is. -/
theorem _root_.AnalyticMap.IsIsoOver.of_comp_diffeomorph
    {A B M : AnalyticManifold.{u} 𝕜 E} (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) A B ω)
    (f : AnalyticMap B M) (g : AnalyticMap A M) (hfg : ∀ a, f (φ a) = g a) {U : Set M}
    (hg : g.IsIsoOver U) : f.IsIsoOver U := by
  have hf : ⇑f = ⇑g ∘ ⇑φ.symm := funext fun b => by
    rw [Function.comp_apply, ← hfg, Diffeomorph.apply_symm_apply]
  have hpre : ⇑φ.symm '' (⇑f ⁻¹' U) = ⇑g ⁻¹' U := by
    rw [hf]
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hb
    · intro ha
      exact ⟨φ a, by simpa [Function.comp_apply, Diffeomorph.symm_apply_apply] using ha,
        Diffeomorph.symm_apply_apply φ a⟩
  refine ⟨fun b => ?_, ?_⟩
  · have hb : φ.symm b.1 ∈ ⇑g ⁻¹' U := by
      rw [← hpre]
      exact ⟨b.1, b.2, rfl⟩
    have h := (φ.symm.isLocalDiffeomorph b.1).comp 𝓘(𝕜, E) _ (hg.1 ⟨φ.symm b.1, hb⟩)
    rw [← hf] at h
    exact h
  · rw [hf]
    refine hg.2.comp ?_
    exact ⟨fun _ hb => hb, fun _ _ _ _ h => φ.symm.toEquiv.injective h, fun a ha =>
      ⟨φ a, by simpa [Function.comp_apply, Diffeomorph.symm_apply_apply] using ha,
        Diffeomorph.symm_apply_apply φ a⟩⟩

end General

end Hironaka.Manifold

namespace AnalyticManifold.BlowUpSequence

open _root_.Manifold
open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- The composite blow-down of the cleaned list is an analytic isomorphism over `Zᶜ` when the
composite blow-down of the list is (`stageMap_last_eraseEmptyLast`). -/
theorem isAnalyticIsoOver_stageMap_last_eraseEmpty (L : BlowUpSequence ψ₀ M) {Z : Set M}
    (h : (L.toSuccession.stageMap (Fin.last _)).IsIsoOver Zᶜ) :
    (L.eraseEmpty.toSuccession.stageMap (Fin.last _)).IsIsoOver Zᶜ :=
  AnalyticMap.IsIsoOver.of_comp_diffeomorph L.eraseEmptyLast _ _
    (fun p => stageMap_last_eraseEmptyLast L p) h

/-- Transport of `CentersOver` along an equality of lists. -/
theorem centersOver_of_eq {L₁ L₂ : BlowUpSequence ψ₀ M} (e : L₁ = L₂) {Z : Set M}
    (h : L₁.toSuccession.CentersOver Z) : L₂.toSuccession.CentersOver Z := by
  subst e
  exact h

end AnalyticManifold.BlowUpSequence

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-! ### Clause (3) for the value -/

/-- The centres of the value on `U`, before the deletion of the empty rounds, lie over
`cosupp 𝓘|U ∪ Sing E|U`. -/
theorem principalizationValue_centersOver_concat (bmo : BMOanFam.{u} 𝕜 n 1)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    ((disjoinListOn T (shrinkOpen U hU) (isCompact_closure_shrinkOpen U hU)).shrinkAppend
      (M.restrictLE (subset_closure.trans (closure_subset_shrinkOpen U hU)))
      (isLocalDiffeomorph_restrictLE _)
      ((bmo.functor.fam
        (disjoinedTriple (restrictTriple T (shrinkOpen U hU))
          (meetLocus_disjoinBound_eq_empty T _ (isCompact_closure_shrinkOpen U hU)))
        (disjoinedTriple_bmoClass _ _)).seqOn
          ((disjoinListOn T (shrinkOpen U hU) (isCompact_closure_shrinkOpen U hU)).liftRange
            (M.restrictLE (subset_closure.trans (closure_subset_shrinkOpen U hU)))
            (isLocalDiffeomorph_restrictLE _))
          ((disjoinListOn T (shrinkOpen U hU)
            (isCompact_closure_shrinkOpen U hU)).isCompact_closure_liftRange _ _
            (isCompact_closure_range_restrictLE _ hU
              (closure_subset_shrinkOpen U hU))))).toSuccession.CentersOver
      ((restrictTriple T U).I.support ∪ (restrictTriple T U).F.singularLocus) := by
  have hUW : U ≤ shrinkOpen U hU := subset_closure.trans (closure_subset_shrinkOpen U hU)
  refine BlowUpSequence.centersOver_concat _ _ _ ?_ ?_
  · exact (BlowUpSequence.centersOver_of_eq (disjoinListOn_pullback_restrictLE T _ hUW).symm
      (centersOver_disjoinList _ _ _ _)).mono Set.subset_union_right
  · have h := bmo.isOfOrderGe
      (disjoinedTriple (restrictTriple T (shrinkOpen U hU))
        (meetLocus_disjoinBound_eq_empty T (shrinkOpen U hU) (isCompact_closure_shrinkOpen U hU)))
      (disjoinedTriple_bmoClass _ _) _
      ((disjoinListOn T (shrinkOpen U hU)
        (isCompact_closure_shrinkOpen U hU)).isCompact_closure_liftRange
        (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE hUW)
        (isCompact_closure_range_restrictLE hUW hU (closure_subset_shrinkOpen U hU)))
    have h2 := BlowUpSequence.isOfOrderGe_pullback _
      ((disjoinListOn T (shrinkOpen U hU) (isCompact_closure_shrinkOpen U hU)).liftCorestrict
        (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE hUW))
      (BlowUpSequence.isLocalDiffeomorph_liftCorestrict _ _ _) _ 1 (AnalyticTriple.isSnc _) h
    refine (FiniteSuccession.CentersOver.of_isOfOrderGe _ h2 le_rfl).mono fun q hq => ?_
    rw [Set.mem_preimage]
    left
    rw [IdealSheaf.support_pullback, Set.mem_preimage] at hq
    change _ ∈ ((disjoinedTriple (restrictTriple T (shrinkOpen U hU))
      (meetLocus_disjoinBound_eq_empty T (shrinkOpen U hU)
        (isCompact_closure_shrinkOpen U hU))).I.pullback _
      (((disjoinListOn T (shrinkOpen U hU) (isCompact_closure_shrinkOpen U hU)).stage
        (Fin.last _)).inclusion
        ((disjoinListOn T (shrinkOpen U hU) (isCompact_closure_shrinkOpen U hU)).liftRange
          (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE hUW))).contMDiff).support at hq
    rw [IdealSheaf.support_pullback, Set.mem_preimage] at hq
    change _ ∈ ((restrictTriple T (shrinkOpen U hU)).I.pullback _ ((disjoinListOn T (shrinkOpen U
        hU)
        (isCompact_closure_shrinkOpen U hU)).toSuccession.stageMap (Fin.last _)).contMDiff).support
            at hq
    rw [IdealSheaf.support_pullback, Set.mem_preimage] at hq
    have hT : (restrictTriple T (shrinkOpen U hU)).pullback (M.restrictLE hUW)
        (isLocalDiffeomorph_restrictLE hUW) = restrictTriple T U :=
      T.pullback_inclusion_restrictLE hUW
    rw [← hT]
    change _ ∈ ((restrictTriple T (shrinkOpen U hU)).I.pullback _ (M.restrictLE
        hUW).contMDiff).support
    rw [IdealSheaf.support_pullback, Set.mem_preimage,
      ← BlowUpSequence.stageMap_last_pullbackLiftLast]
    exact hq

/-- Clause (3) of [Kol07, Theorem 35] with the disjoining blow-ups included: **the composite
blow-down of the value on `U` is an analytic isomorphism over `U ∖ (cosupp 𝓘|U ∪ Sing E|U)`**. -/
theorem principalizationValue_isAnalyticIsoOver (bmo : BMOanFam.{u} 𝕜 n 1)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    ((principalizationValue bmo T U hU).toSuccession.stageMap (Fin.last _)).IsIsoOver
      ((restrictTriple T U).I.support ∪ (restrictTriple T U).F.singularLocus)ᶜ := by
  unfold principalizationValue principalizationValueOn valueOf
  exact BlowUpSequence.isAnalyticIsoOver_stageMap_last_eraseEmpty _
    (FiniteSuccession.isAnalyticIsoOver_stageMap
      (principalizationValue_centersOver_concat bmo T U hU) (Fin.last _))

end Hironaka.Manifold
