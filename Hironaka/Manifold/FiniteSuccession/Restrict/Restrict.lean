/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.StrictSubmanifold
public import Hironaka.Manifold.FiniteSuccession.Restrict.Bundle
public import Hironaka.Manifold.Submanifold.Restrict
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Restrict.CongrChart
import Hironaka.Manifold.FiniteSuccession.Restrict.Lift
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The restriction of a blow-up sequence to a closed submanifold

For a blow-up sequence `Π` of `X` (a finite succession, `FiniteSuccession`) and a closed
submanifold `S ⊆ X` with `Z_i ⊆ S_i` for all `i` (`FiniteSuccession.CentersIn`), the restriction
`Π|_S` of [Kol07, Definition 30.2] is the blow-up sequence of the bundled `S` whose stages are the
strict transforms `S_i` (`strictTransformSeq`, closed submanifolds of `X_i` by
`isClosedSubmanifold_strictTransformSeq`), whose centres are the `Z_i = Z_i ∩ S_i` regarded inside
`S_i` (`IsClosedSubmanifold.preimage_val_of_subset`, with the ideal sheaf
`IsClosedSubmanifold.idealSheaf`), and whose blow-downs are the restrictions
`π_i|_{S_{i+1}} : S_{i+1} → S_i` — blowings-up of `S_i` along `Z_i` by `isBlowUp_restrictMap`
(`Lift.lean`), so that `Π|_S` is a succession of monoidal transformations (`restrictSubmanifold`).
Kollár's natural embeddings `S_i ↪ X_i` are the inclusions `restrictIncl`, closed embeddings with
image `S_i`, commuting with the blow-downs.

A succession carries one chosen chart `chartAt i` per step; the restriction is stated for one
chart `ψ` of `E`, exchanged for `chartAt i` through `IsClosedSubmanifold.congr_chart` and
`IsBlowUp.congr_chart`. The stages are typed on the stages `finStages` of a succession by a case
split on the index.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set Manifold
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  [SecondCountableTopology M] {S : Set M} {s : ℕ}

/-- The inclusion of a closed submanifold as a bundled analytic map (between the model `𝕜^{n-s}`
of the submanifold and the model `E` of `M`); the natural embeddings `S_i ↪ X_i` of
[Kol07, Definition 30.2] are of this form. -/
def IsClosedSubmanifold.inclusionMap (hS : IsClosedSubmanifold ψ S s) :
    C^ω⟮𝓘(𝕜, Fin (n - s) → 𝕜), hS.toAnalyticManifold; 𝓘(𝕜, E), M⟯ :=
  letI := hS.chartedSpace
  ⟨Subtype.val, hS.contMDiff_val⟩

theorem IsClosedSubmanifold.inclusionMap_apply (hS : IsClosedSubmanifold ψ S s)
    (p : hS.toAnalyticManifold) : hS.inclusionMap p = (p : S).1 :=
  rfl

end Manifold

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M) {H : Set M}
  {s : ℕ} (hH : IsClosedSubmanifold ψ H s) (hc : S.CentersIn H)

/-! ### The pieces at the level of the recursion -/

/-- The centre `Z_i` as a closed submanifold of `X_i` for the chart `ψ`. -/
theorem restrictCenterSub (i : ℕ) (hi : i < S.length) :
    IsClosedSubmanifold ψ (S.center ⟨i, hi⟩).support (S.codim ⟨i, hi⟩) :=
  (S.isClosedSubmanifold_center ⟨i, hi⟩).congr_chart ψ

/-- Kollár's `Z_i ∩ S_i`: the centre as a closed submanifold of the bundled `S_i`, of codimension
`c_i − s`. -/
theorem restrictCenterSub' (i : ℕ) (hi : i < S.length) :
    IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      ((S.isClosedSubmanifold_strictTransformSeqAux _ hH hc i (Nat.lt_succ_of_lt hi)).preimageVal
          (S.center ⟨i, hi⟩).support)
      (S.codim ⟨i, hi⟩ - s) :=
  (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc i
      (Nat.lt_succ_of_lt hi)).preimage_val_of_subset
    (S.restrictCenterSub i hi) (hc ⟨i, hi⟩)

include hH in
/-- The blow-down carries `S_{i+1}` into `S_i`. -/
theorem restrictMapsTo (i : ℕ) (hi : i < S.length) :
    ∀ x ∈ S.strictTransformSeqAux H (i + 1) (Nat.succ_lt_succ hi),
      S.map ⟨i, hi⟩ x ∈ S.strictTransformSeqAux H i (Nat.lt_succ_of_lt hi) :=
  S.strictTransformSeq_succ_subset_preimage H hH.isClosed ⟨i, hi⟩

/-- The later stages `S_1, …, S_r` of the restriction. -/
def restrictLater (i : Fin S.length) : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜) :=
  (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc (i.1 + 1)
      (Nat.succ_lt_succ i.2)).toAnalyticManifold

/-- The centre of the restriction at step `i`: the ideal sheaf of `Z_i ∩ S_i` in `S_i`. -/
def restrictCenterOf (i : ℕ) (hi : i < S.length) :
    IdealSheaf (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc i
        (Nat.lt_succ_of_lt hi)).toAnalyticManifold :=
  (S.restrictCenterSub' hH hc i hi).idealSheaf

/-- The blow-down of the restriction at step `i`: `π_i|_{S_{i+1}} : S_{i+1} → S_i`. -/
def restrictMapOf (i : ℕ) (hi : i < S.length) :
    AnalyticMap (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc (i + 1)
        (Nat.succ_lt_succ hi)).toAnalyticManifold
      (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc i
          (Nat.lt_succ_of_lt hi)).toAnalyticManifold :=
  (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc (i + 1) (Nat.succ_lt_succ hi)).restrictMap
    (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc i (Nat.lt_succ_of_lt hi)) (S.map ⟨i, hi⟩)
        (S.map ⟨i, hi⟩).contMDiff
    (S.restrictMapsTo hH i hi)

/-- Each blow-down of the restriction is a blowing-up of `S_i` along `Z_i ∩ S_i`
(`isBlowUp_restrictMap`, with the succession's chart exchanged for `ψ`). -/
theorem isBlowUp_restrictMapOf (i : ℕ) (hi : i < S.length) :
    IsBlowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      ((S.isClosedSubmanifold_strictTransformSeqAux _ hH hc i (Nat.lt_succ_of_lt hi)).preimageVal
          (S.center ⟨i, hi⟩).support)
      (S.codim ⟨i, hi⟩ - s) (S.restrictMapOf hH hc i hi) :=
  isBlowUp_restrictMap (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc i
      (Nat.lt_succ_of_lt hi))
    (S.restrictCenterSub i hi) ((S.isBlowUp_map ⟨i, hi⟩).congr_chart ψ) (hc ⟨i, hi⟩)

/-- Each blow-down of the restriction is a monoidal transformation with centre the ideal sheaf of
`Z_i ∩ S_i` (`IsMonoidalTransformation`). -/
theorem restrictIsMonoidalOf (i : ℕ) (hi : i < S.length) :
    (S.restrictMapOf hH hc i hi).IsMonoidalTransformation (S.restrictCenterOf hH hc i hi) := by
  have hZ := S.restrictCenterSub' hH hc i hi
  have hs : hZ.idealSheaf.support =
      (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc i (Nat.lt_succ_of_lt hi)).preimageVal
          (S.center ⟨i, hi⟩).support :=
    hZ.cosupport_idealSheaf
  refine ⟨n - s, ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜), S.codim ⟨i, hi⟩ - s, ?_, ?_, ?_⟩
  · change IsClosedSubmanifold _ hZ.idealSheaf.support _
    rw [hs]; exact hZ
  · change IsIdealSheafOf _ hZ.idealSheaf.support _ hZ.idealSheaf
    rw [hs]; exact hZ.isIdealSheafOf_idealSheaf
  · change IsBlowUp _ hZ.idealSheaf.support _ (S.restrictMapOf hH hc i hi)
    rw [hs]; exact S.isBlowUp_restrictMapOf hH hc i hi

/-! ### The pieces typed on the stages of a succession -/

/-- The centres of the restriction, typed on the stages `finStages` (a case split on the index
makes the stage reduce to the recursion's). -/
def restrictCenterAux :
    ∀ (i : ℕ) (hi : i < S.length),
      IdealSheaf (finStages hH.toAnalyticManifold (S.restrictLater hH hc) ⟨i, Nat.lt_succ_of_lt hi⟩)
  | 0, hi => S.restrictCenterOf hH hc 0 hi
  | i + 1, hi => S.restrictCenterOf hH hc (i + 1) hi

/-- The blow-downs of the restriction, typed on the stages `finStages`. -/
def restrictMapAux :
    ∀ (i : ℕ) (hi : i < S.length),
      AnalyticMap
        (finStages hH.toAnalyticManifold (S.restrictLater hH hc) ⟨i + 1, Nat.succ_lt_succ hi⟩)
        (finStages hH.toAnalyticManifold (S.restrictLater hH hc) ⟨i, Nat.lt_succ_of_lt hi⟩)
  | 0, hi => S.restrictMapOf hH hc 0 hi
  | i + 1, hi => S.restrictMapOf hH hc (i + 1) hi

/-- Each blow-down of the restriction is a monoidal transformation, typed on the stages. -/
theorem restrictIsMonoidalAux :
    ∀ (i : ℕ) (hi : i < S.length),
      (S.restrictMapAux hH hc i hi).IsMonoidalTransformation (S.restrictCenterAux hH hc i hi)
  | 0, hi => S.restrictIsMonoidalOf hH hc 0 hi
  | i + 1, hi => S.restrictIsMonoidalOf hH hc (i + 1) hi

/-! ### The restriction and the inclusions -/

/-- **The restriction `Π|_S` of a blow-up sequence to a closed submanifold `S` with `Z_i ⊆ S_i`
for all `i`** [Kol07, Definition 30.2]: the blow-up sequence of the bundled `S` of the same length
whose `i`-th stage is the strict transform `S_i`, whose `i`-th centre is (the ideal sheaf of)
`Z_i ∩ S_i = Z_i`, and whose `i`-th blow-down is `π_i|_{S_{i+1}}`. -/
def restrictSubmanifold : FiniteSuccession hH.toAnalyticManifold where
  length := S.length
  later := S.restrictLater hH hc
  center i := S.restrictCenterAux hH hc i.1 i.2
  map i := S.restrictMapAux hH hc i.1 i.2
  isMonoidal i := S.restrictIsMonoidalAux hH hc i.1 i.2

/-- The natural embeddings `S_i ↪ X_i` of [Kol07, Definition 30.2]: the inclusions of the stages
of the restriction into those of `Π`. -/
def restrictIncl : ∀ i : Fin (S.length + 1),
    C^ω⟮𝓘(𝕜, Fin (n - s) → 𝕜), (S.restrictSubmanifold hH hc).stage i; 𝓘(𝕜, E), S.stage i⟯
  | ⟨0, hi⟩ => (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc 0 hi).inclusionMap
  | ⟨i + 1, hi⟩ => (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc (i + 1) hi).inclusionMap

/-! ### The properties of the restriction -/

theorem length_restrictSubmanifold : (S.restrictSubmanifold hH hc).length = S.length := rfl

/-- The stages of `Π|_S` are the strict transforms `S_i`, as bundled closed submanifolds. -/
theorem stage_restrictSubmanifold (i : Fin (S.length + 1)) :
    (S.restrictSubmanifold hH hc).stage i =
      (S.isClosedSubmanifold_strictTransformSeq H hH hc i).toAnalyticManifold := by
  obtain ⟨i, hi⟩ := i
  cases i <;> rfl

/-- The inclusions `S_i ↪ X_i` are closed embeddings. -/
theorem isClosedEmbedding_restrictIncl (i : Fin (S.length + 1)) :
    Topology.IsClosedEmbedding (S.restrictIncl hH hc i) := by
  obtain ⟨i, hi⟩ := i
  cases i
  · exact (S.isClosed_strictTransformSeq H hH.isClosed ⟨0, hi⟩).isClosedEmbedding_subtypeVal
  · exact (S.isClosed_strictTransformSeq H hH.isClosed ⟨_ + 1, hi⟩).isClosedEmbedding_subtypeVal

/-- The image of the inclusion `S_i ↪ X_i` is the strict transform `S_i`. -/
theorem range_restrictIncl (i : Fin (S.length + 1)) :
    Set.range (S.restrictIncl hH hc i) = S.strictTransformSeq H i := by
  obtain ⟨i, hi⟩ := i
  cases i
  · exact Subtype.range_val
  · exact Subtype.range_val

/-- The centre of `Π|_S` at step `i` is `Z_i ∩ S_i`, read through the inclusion. -/
theorem support_center_restrictSubmanifold (i : Fin S.length) :
    ((S.restrictSubmanifold hH hc).center i).support =
      S.restrictIncl hH hc i.castSucc ⁻¹' (S.center i).support := by
  obtain ⟨i, hi⟩ := i
  cases i
  · exact (S.restrictCenterSub' hH hc 0 hi).cosupport_idealSheaf
  · exact (S.restrictCenterSub' hH hc (_ + 1) hi).cosupport_idealSheaf

/-- The inclusions commute with the blow-downs: `π_i^S` is the restriction of `π_i`. -/
theorem restrictIncl_map (i : Fin S.length) (p : (S.restrictSubmanifold hH hc).stage i.succ) :
    S.restrictIncl hH hc i.castSucc ((S.restrictSubmanifold hH hc).map i p) =
      S.map i (S.restrictIncl hH hc i.succ p) := by
  obtain ⟨i, hi⟩ := i
  cases i <;> rfl

/-- Each blow-down of `Π|_S` is a blowing-up of `S_i` along `Z_i ∩ S_i`, of codimension `c_i − s`,
in the induced charts. -/
theorem isBlowUp_map_restrictSubmanifold (i : Fin S.length) :
    IsBlowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      (S.restrictIncl hH hc i.castSucc ⁻¹' (S.center i).support) (S.codim i - s)
      ((S.restrictSubmanifold hH hc).map i) := by
  obtain ⟨i, hi⟩ := i
  cases i
  · exact S.isBlowUp_restrictMapOf hH hc 0 hi
  · exact S.isBlowUp_restrictMapOf hH hc (_ + 1) hi

end AnalyticManifold.FiniteSuccession

end
