/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Principalization.Assembly
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.Snc.NormalCrossings
import Hironaka.Resolution.Analytic.Functor.EraseEmptyOrder
import Hironaka.Resolution.Analytic.OrderReduction.BDLift
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.OrderReduction.Step21Fam
import Hironaka.Resolution.Analytic.Principalization.DisjoinBoundary
import Hironaka.Resolution.Analytic.Principalization.DisjoinNatural
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Clause (1) of the principalization family: the centres have snc with the boundary

Clause (1) of [Kol07, Theorem 35], per open, for the value on `U`: every centre of
`principalizationValue bmo T U hU` has simple normal crossings with the total transform of the
restricted boundary `F|U` at its stage ([Kol07, Definition 25] from `F|U`), in the given
codimension.

The route: clause (1) at stage `i` follows from clause (3′) of [Kol07, Definition 66] at the
stages `≤ i` — "`E_i` has only normal crossings with `Z_i`" for the boundary ideal sheaf
`E_i = boundarySeq (red F|U) i` — by `hasSncWith_totalTransformSeqFrom_center_of_forall_lt`.
Clause (3′) at every stage is the `m = 0` instance of `IsOfOrderGe` (its order half `0 ≤ ord` is
vacuous), and `IsOfOrderGe` is available along every piece of the value:

* the disjoining list (its centres have snc with the running total transform in the given
  codimension, `disjoinList_center_hasSncWith`; converted to (3′) at each stage by
  `hasOnlyNormalCrossingsWith_boundarySeq_of_forall_hasSncWith`);
* the appended order-reduction value: the input family's `isOfOrderGe` at mark `1` on the
  disjoined triple, pulled back along the corestricted lift (`isOfOrderGe_pullback`) and weakened
  to mark `0`; its boundary is the boundary of the disjoining list at its last stage (the junction
  identity `support_comap_liftCorestrict_collapsed`: the collapse does not change the support,
  `support_collapse`);
* the concatenation (`isOfOrderGe_concat`) and the deletion of the empty rounds
  (`isOfOrderGe_eraseEmpty`; [Kol07, 34.1]).
-/

public section

universe u

open Set TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-! ### Clause (3′) alone is `IsOfOrderGe` at mark `0` -/

/-- `IsOfOrderGe` at mark `0` is clause (3′) at every stage: the order half is vacuous. -/
theorem isOfOrderGe_zero_iff (I E₀ : IdealSheaf M) :
    S.IsOfOrderGe I 0 E₀ ↔
      ∀ i : Fin S.length, (S.boundarySeq E₀ i.castSucc).HasOnlyNormalCrossingsWith (S.center i) :=
  ⟨fun h i => (h i).1, fun h i => ⟨h i, fun _ _ => by simp⟩⟩

/-- A sequence of order `≥ m` is of order `≥ 0` for any marked ideal sheaf (clause (3′) alone). -/
theorem IsOfOrderGe.zero {I E₀ : IdealSheaf M} {m : ℕ} (h : S.IsOfOrderGe I m E₀)
    (J : IdealSheaf M) : S.IsOfOrderGe J 0 E₀ :=
  fun i => ⟨(h i).1, fun _ _ => by simp⟩

/-- If every centre has snc with the running total transform of an snc start `F` (Kollár's form of
clause (1)), then the boundary ideal sheaf starting with `red F` has only normal crossings with
every centre (clause (3′) of [Kol07, Definition 66]) — by induction on the stage, the boundary
ideal sheaf at stage `i` being the reduced ideal sheaf of the total transform there
(`isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt`). -/
theorem hasOnlyNormalCrossingsWith_boundarySeq_of_forall_hasSncWith {F : HypersurfaceFamily M}
    (hF : F.IsSnc ψ)
    (h1 : ∀ i : Fin S.length,
      (S.totalTransformSeqFrom F i.castSucc).HasSncWith ψ (S.center i).support (S.codim i)) :
    ∀ (k : ℕ) (i : Fin S.length), i.1 < k →
      (S.boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E)) i.castSucc).HasOnlyNormalCrossingsWith
        (S.center i)
  | 0, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, i, hi => by
    obtain ⟨hsnc, heq⟩ := S.isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt hF
      i.castSucc fun i' hi' =>
        hasOnlyNormalCrossingsWith_boundarySeq_of_forall_hasSncWith hF h1 k i'
          (lt_of_lt_of_le hi' (Nat.lt_succ_iff.mp hi))
    have hZ : IsClosedSubmanifold ψ (S.center i).support (S.codim i) :=
      (S.isClosedSubmanifold_center i).congr_chart ψ
    have hZI : hZ.idealSheaf = S.center i :=
      (IsClosedSubmanifold.idealSheaf_congr hZ (S.isClosedSubmanifold_center i) rfl).trans
        (S.idealSheaf_center i)
    rw [heq, ← hZI]
    exact (hasOnlyNormalCrossingsWith_idealSheaf_iff hsnc hZ).mpr (h1 i)

/-- Kollár's clause (1) at every stage gives `IsOfOrderGe` at mark `0` for the boundary starting
with `red F`. -/
theorem isOfOrderGe_zero_of_forall_hasSncWith {F : HypersurfaceFamily M} (hF : F.IsSnc ψ)
    (h1 : ∀ i : Fin S.length,
      (S.totalTransformSeqFrom F i.castSucc).HasSncWith ψ (S.center i).support (S.codim i))
    (J : IdealSheaf M) : S.IsOfOrderGe J 0 (F.idealSheaf (𝕜 := 𝕜) (E := E)) :=
  (S.isOfOrderGe_zero_iff J _).mpr fun i =>
    S.hasOnlyNormalCrossingsWith_boundarySeq_of_forall_hasSncWith hF h1 (i.1 + 1) i
      (Nat.lt_succ_self _)

end AnalyticManifold.FiniteSuccession

namespace Hironaka.Manifold

open _root_.Manifold

/-- Transport of the order clause along an equality of lists. -/
theorem _root_.AnalyticManifold.BlowUpSequence.isOfOrderGe_of_eq {𝕜 : Type} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
    {L₁ L₂ : BlowUpSequence ψ₀ M} (e : L₁ = L₂) {I E₀ : AnalyticManifold.IdealSheaf M} {m : ℕ}
    (h : L₁.toSuccession.IsOfOrderGe I m E₀) : L₂.toSuccession.IsOfOrderGe I m E₀ := by
  subst e
  exact h

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-! ### The disjoining list restricted to `U` -/

/-- Over the smaller open `U ⋐ W` the restricted boundary has no `(k+1)`-fold points for the bound
`k` of `W`. -/
theorem meetLocus_restrictTriple_disjoinBound_eq_empty_of_le
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) {U W : Opens M}
    (hW : IsCompact (closure (W : Set M))) (hUW : U ≤ W) :
    (restrictTriple T U).F.meetLocus (disjoinBound T W + 1) = ∅ := by
  have h := meetLocus_disjoinBound_eq_empty T W hW
  have hT : (restrictTriple T W).pullback (M.restrictLE hUW)
      (isLocalDiffeomorph_restrictLE hUW) = restrictTriple T U :=
    T.pullback_inclusion_restrictLE hUW
  rw [← hT]
  change ((restrictTriple T W).F.comap (M.restrictLE hUW)).meetLocus _ = ∅
  rw [HypersurfaceFamily.meetLocus_comap, h, Set.preimage_empty]

/-- The disjoining list over `W`, restricted to `U ⋐ W`, is the disjoining list of the boundary
restricted to `U`, at `W`'s bound (functoriality of the disjoining for open embeddings,
[Kol07, 34.1]). -/
theorem disjoinListOn_pullback_restrictLE
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) {U W : Opens M}
    (hW : IsCompact (closure (W : Set M))) (hUW : U ≤ W) :
    (disjoinListOn T W hW).pullback (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE hUW) =
      disjoinList (disjoinBound T W) (restrictTriple T U).F (restrictTriple T U).isSnc
        (meetLocus_restrictTriple_disjoinBound_eq_empty_of_le T hW hUW) := by
  rw [disjoinList_pullback]
  exact disjoinList_congr (congrArg AnalyticTriple.F (T.pullback_inclusion_restrictLE hUW)) _ _ _
    _ _

/-! ### The junction: the appended value's boundary is the disjoining list's boundary -/

/-- The boundary of the disjoined triple, restricted to the reading open and pulled back along the
corestricted lift, has the support of the total transform of `F|U` at the last stage of the
restricted disjoining list (the collapse keeps the support, `support_collapse`; the pull-back of a
total transform along the lift, `totalTransformSeqFrom_last_pullbackLiftLast`, as in
[Kol07, 30.1]). -/
theorem support_comap_liftCorestrict_collapsed
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) {U W : Opens M}
    (hW : IsCompact (closure (W : Set M))) (hUW : U ≤ W) :
    (((disjoinedTriple (restrictTriple T W) (meetLocus_disjoinBound_eq_empty T W hW)).pullback
        (((disjoinListOn T W hW).stage (Fin.last _)).inclusion
          ((disjoinListOn T W hW).liftRange (M.restrictLE hUW)
            (isLocalDiffeomorph_restrictLE hUW)))
        (isLocalDiffeomorph_inclusion _ _)).F.comap
      ((disjoinListOn T W hW).liftCorestrict (M.restrictLE hUW)
        (isLocalDiffeomorph_restrictLE hUW))).support =
    (((disjoinListOn T W hW).pullback (M.restrictLE hUW)
      (isLocalDiffeomorph_restrictLE hUW)).toSuccession.totalTransformSeqFrom
        (restrictTriple T U).F (Fin.last _)).support := by
  rw [HypersurfaceFamily.support_comap]
  change ⇑((disjoinListOn T W hW).liftCorestrict (M.restrictLE hUW) _) ⁻¹'
    ((collapsedFamilyOf (disjoinListOn T W hW) (restrictTriple T W).F).comap
      ⇑(((disjoinListOn T W hW).stage (Fin.last _)).inclusion _)).support = _
  unfold collapsedFamilyOf
  rw [HypersurfaceFamily.support_comap, ← Set.preimage_comp, HypersurfaceFamily.support_collapse,
    ← congrArg AnalyticTriple.F (T.pullback_inclusion_restrictLE hUW)]
  change _ = (((disjoinListOn T W hW).pullback (M.restrictLE hUW)
    (isLocalDiffeomorph_restrictLE hUW)).toSuccession.totalTransformSeqFrom
      ((restrictTriple T W).F.comap (M.restrictLE hUW)) (Fin.last _)).support
  rw [BlowUpSequence.totalTransformSeqFrom_last_pullbackLiftLast, HypersurfaceFamily.support_comap]
  rfl

/-! ### Clause (1) for the value -/

/-- The value on `U` is of order `≥ 0` for the boundary `red (F|U)` — clause (3′) of
[Kol07, Definition 66] at every stage — along the disjoining part (clause (1) of the disjoining in
the given codimension), the appended order-reduction value (the input family's `isOfOrderGe`,
weakened), the concatenation and the deletion of the empty rounds. -/
theorem principalizationValue_isOfOrderGe_zero (bmo : BMOanFam.{u} 𝕜 n 1)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    (principalizationValue bmo T U hU).toSuccession.IsOfOrderGe (restrictTriple T U).I 0
      (restrictTriple T U).F.idealSheaf := by
  have hUW : U ≤ shrinkOpen U hU := subset_closure.trans (closure_subset_shrinkOpen U hU)
  have hL : ((disjoinListOn T (shrinkOpen U hU) (isCompact_closure_shrinkOpen U hU)).pullback
      (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE hUW)).toSuccession.IsOfOrderGe
      (restrictTriple T U).I 0 (restrictTriple T U).F.idealSheaf :=
    BlowUpSequence.isOfOrderGe_of_eq (disjoinListOn_pullback_restrictLE T _ hUW).symm
      (FiniteSuccession.isOfOrderGe_zero_of_forall_hasSncWith _ (restrictTriple T U).isSnc
        (disjoinList_center_hasSncWith _ _ _ _) _)
  unfold principalizationValue principalizationValueOn valueOf
  refine BlowUpSequence.isOfOrderGe_eraseEmpty _ _ 0 (restrictTriple T U).isSnc ?_
  refine BlowUpSequence.isOfOrderGe_concat _ _ hL ?_
  have h := bmo.isOfOrderGe
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
  have hE := HypersurfaceFamily.idealSheaf_eq_of_support_eq (𝕜 := 𝕜) (E := Fin n → 𝕜)
    (support_comap_liftCorestrict_collapsed T (isCompact_closure_shrinkOpen U hU) hUW)
  have hB := (FiniteSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt
    (S := ((disjoinListOn T (shrinkOpen U hU) (isCompact_closure_shrinkOpen U hU)).pullback
      (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE hUW)).toSuccession)
    (restrictTriple T U).isSnc (Fin.last _) (fun i' _ => (hL i').1)).2
  rw [hE, ← hB] at h2
  exact h2.zero _ _

/-- Clause (1) of [Kol07, Theorem 35], per open: **every centre of the value on `U` has snc with
the total transform of `F|U` at its stage**, in the given codimension
(`hasSncWith_totalTransformSeqFrom_center_of_forall_lt` from clause (3′) at every stage). -/
theorem principalizationValue_center_hasSncWith (bmo : BMOanFam.{u} 𝕜 n 1)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (U : Opens M)
    (hU : IsCompact (closure (U : Set M)))
    (i : Fin (principalizationValue bmo T U hU).toSuccession.length) :
    ((principalizationValue bmo T U hU).toSuccession.totalTransformSeqFrom (restrictTriple T U).F
        i.castSucc).HasSncWith (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      ((principalizationValue bmo T U hU).toSuccession.center i).support
      ((principalizationValue bmo T U hU).toSuccession.codim i) :=
  FiniteSuccession.hasSncWith_totalTransformSeqFrom_center_of_forall_lt (restrictTriple T U).isSnc i
    fun i' _ => (principalizationValue_isOfOrderGe_zero bmo T U hU i').1

end Hironaka.Manifold
