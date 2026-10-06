/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.Basic
import Hironaka.Manifold.Snc.NonSingular
import Hironaka.Resolution.Analytic.MaximalContact.OneStepDescentLemmas
import Hironaka.Resolution.Analytic.Wlo09.BoundaryBridge
import Hironaka.Resolution.Analytic.Wlo09.Clauses
import Hironaka.Resolution.Analytic.Wlo09.Components
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The final strict transform of the value of `bedanFamOfInput`

The four theorems of this module describe the final strict transform of the value of the embedded
desingularization functor `bedanFamOfInput bmod n` over a relatively compact open `U` of a manifold
`M` modelled on `𝕜ⁿ`, for a triple `T` of the class `DomBEDan`. Write `L` for the value on `U`,
`𝓘_r` for the final marked transform of `(T|_U).I` at mark `1` along `L`
(`markedTransformSeq … 1 (Fin.last _)`) and `Ỹ` for the final ideal-theoretic strict transform
(`strictTransformSubspaceSeq … (Fin.last _)`, whose stalks are the saturations of
[BM97, Proposition 3.13] at every stage). Each theorem carries one explicit hypothesis `hsat`: at
every stage the saturation stalks of the strict transform have local generators. The hypothesis
always holds (`saturationStalk_hasLocalGenerators`,
`Hironaka/Manifold/BlowUp/Transform/SaturationFiniteType.lean`).

* `bedanFamOfInput_cosupport_markedTransformSeq_eq_of_hsat`: the cosupport of `𝓘_r` is the
  cosupport of `Ỹ`;
* `bedanFamOfInput_strictTransform_eq_of_hsat`: `𝓘_r = Ỹ` as ideal sheaves;
* `bedanFamOfInput_isNonsingular_strictTransform_of_hsat`: `Ỹ` is non-singular;
* `bedanFamOfInput_exists_adaptedChart_isSncChartAt_of_hsat`: at every point of `Ỹ` there is a
  chart adapted to `Ỹ` which is a simple-normal-crossing chart of the exceptional divisors in which
  no divisor through the point carries a coordinate of `Ỹ`.

The last two are clause (3) of [Wlo09, Theorem 2.0.2] in its proper form, the shape of the output
of Włodarczyk's modified algorithm (the proof of [Wlo09, Theorem 7.4.1]: the final marked
transform is the ideal of a smooth submanifold with coordinates transversal to the exceptional
divisors). The identification `𝓘_r = Ỹ` is what makes that output the strict transform of `Y`.

**Proofs.** The cosupport identity is the general assembly
`cosupport_markedTransformSeq_eq_cosupport_strictTransformSubspaceSeq`
(`Hironaka/Resolution/Analytic/Wlo09/Components.lean`) at the value: the order bound `≥ 1` at every
stage is `bedanFamOfInput_isOfOrderGe`, the simple normal crossings of the exceptional families is
`bedanFamOfInput_isSnc_totalTransformSeq`, and the coordinate shape of `𝓘_r` at its support points
is the field `output_isSmoothSubmanifoldIdeal` of the underlying `BMOmodFam`, read through the
empty-boundary bridge (`isSmoothTransversalIdealAt_totalTransformSeqFrom_iff_of_isEmpty`). For
`𝓘_r = Ỹ`: `𝓘_r ≤ Ỹ` is the chain inequality `markedTransformSeq_le_strictTransformSubspaceSeq`; for
`Ỹ ≤ 𝓘_r` stalkwise, off the support both are the unit ideal, and at a support point `𝓘_r` is a
coordinate ideal on a chart, the stalk of `Ỹ` lies in the vanishing ideal of its cosupport
(`stalkIdeal_le_vanishingStalk_of_subset_cosupport`), which is the cosupport of `𝓘_r` by the first
theorem, and that vanishing ideal is the stalk of `𝓘_r` by the local Hadamard lemma
(`vanishingStalk_cosupport_eq_stalkIdeal_of_eq_span_coord`). Non-singularity is the regularity of
the quotient by a coordinate ideal (`isRegularLocalRing_quotient_span_coord` through
`mem_reg_toAnalyticSpace_iff`), and the chart of the coordinate shape is the adapted
simple-normal-crossing chart, with the proper conjunct `cidx j ≠ σ i`.
-/

public section

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

section

variable (𝕜 : Type) [RCLike 𝕜] (bmod : ∀ n : ℕ, BMOmodFam.{u} 𝕜 n) (n : ℕ)
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
  (U : Opens M) (hU : IsCompact (closure (U : Set M)))

/-- The cosupport of the final marked transform `𝓘_r` of the value over `U` is the cosupport of the
final strict transform `Ỹ`, under the hypothesis `hsat` (always satisfied) that the saturation
stalks of the strict transform have local generators at every stage. -/
theorem bedanFamOfInput_cosupport_markedTransformSeq_eq_of_hsat
    (hsat : ∀ i : Fin (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.length,
      IdealSheaf.HasLocalGenerators
        (𝒪 := structureSheaf 𝕜 (Fin n → 𝕜)
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.stage i.succ))
        (saturationStalk
          (π := ⇑((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.map i))
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
            U hU).toSuccession.isClosedSubmanifold_center i)
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.isBlowUp_map i)
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
            U hU).toSuccession.strictTransformSubspaceSeq
            (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I i.castSucc))) :
    ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.markedTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
        (Fin.last _)).support =
      ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.strictTransformSubspaceSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
        (Fin.last _)).support := by
  have hT' : IsEmpty (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.ι := hT.1
  refine cosupport_markedTransformSeq_eq_cosupport_strictTransformSubspaceSeq
    (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) _ _ ⊤
    (bedanFamOfInput_isOfOrderGe 𝕜 bmod n T hT U hU)
    (bedanFamOfInput_isSnc_totalTransformSeq 𝕜 bmod n T hT U hU) hsat fun x hx => ?_
  have hord : (1 : ℕ∞) ≤ ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
      U hU).toSuccession.markedTransformSeq
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1 (Fin.last _)).ord x :=
    Order.one_le_iff_ne_zero.mpr fun h0 => (((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
      U hU).toSuccession.markedTransformSeq
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      (Fin.last _)).ord_eq_zero_iff.mp h0) hx
  exact (isSmoothTransversalIdealAt_totalTransformSeqFrom_iff_of_isEmpty _ _ _ _ _ _).mp
    ((bmod n).output_isSmoothSubmanifoldIdeal T (DomBEDan.bmoClass_one 𝕜 hT) U hU x hord)

/-- The final marked transform `𝓘_r` of the value over `U` is the final strict transform `Ỹ`, as
ideal sheaves, under `hsat`: Kollár's marked transform at mark `1` along the sequence produces the
strict transform of `Y` once its output is the ideal of a smooth submanifold. -/
theorem bedanFamOfInput_strictTransform_eq_of_hsat
    (hsat : ∀ i : Fin (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.length,
      IdealSheaf.HasLocalGenerators
        (𝒪 := structureSheaf 𝕜 (Fin n → 𝕜)
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.stage i.succ))
        (saturationStalk
          (π := ⇑((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.map i))
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
            U hU).toSuccession.isClosedSubmanifold_center i)
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.isBlowUp_map i)
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
            U hU).toSuccession.strictTransformSubspaceSeq
            (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I i.castSucc))) :
    (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.markedTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1 (Fin.last _) =
      (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.strictTransformSubspaceSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I (Fin.last _) := by
  have hcos := bedanFamOfInput_cosupport_markedTransformSeq_eq_of_hsat 𝕜 bmod n T hT U hU hsat
  refine le_antisymm (markedTransformSeq_le_strictTransformSubspaceSeq _ _ ⊤
    (bedanFamOfInput_isOfOrderGe 𝕜 bmod n T hT U hU) _) ?_
  rw [IdealSheaf.le_def]
  intro x
  by_cases hx : x ∈ ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
      U hU).toSuccession.markedTransformSeq
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1 (Fin.last _)).support
  · have hord : (1 : ℕ∞) ≤ ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
        U hU).toSuccession.markedTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1 (Fin.last _)).ord x :=
      Order.one_le_iff_ne_zero.mpr fun h0 => (((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
        U hU).toSuccession.markedTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
        (Fin.last _)).ord_eq_zero_iff.mp h0) hx
    obtain ⟨c, φ, σ, cidx, hφ, hJx, -⟩ :=
      (bmod n).output_isSmoothSubmanifoldIdeal T (DomBEDan.bmoClass_one 𝕜 hT) U hU x hord
    calc ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
          U hU).toSuccession.strictTransformSubspaceSeq
          (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
          (Fin.last _)).stalkIdeal x
        ≤ vanishingStalk (𝕜 := 𝕜) (E := Fin n → 𝕜) ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
            U hU).toSuccession.strictTransformSubspaceSeq
            (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
            (Fin.last _)).support x :=
          stalkIdeal_le_vanishingStalk_of_subset_cosupport _ subset_rfl x
      _ = vanishingStalk (𝕜 := 𝕜) (E := Fin n → 𝕜) ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
            U hU).toSuccession.markedTransformSeq
            (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
            (Fin.last _)).support x := by rw [hcos]
      _ = ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.markedTransformSeq
            (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
            (Fin.last _)).stalkIdeal x :=
          vanishingStalk_cosupport_eq_stalkIdeal_of_eq_span_coord _ _ hφ.1 σ hJx hφ.2.1
  · have htop : ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.markedTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
        (Fin.last _)).stalkIdeal x = ⊤ := not_not.mp hx
    rw [htop]
    exact le_top

/-- The final strict transform of the value over `U` is non-singular (`IsNonsingular` of the closed
subspace), under `hsat`: the first conjunct of clause (3) of [Wlo09, Theorem 2.0.2]. -/
theorem bedanFamOfInput_isNonsingular_strictTransform_of_hsat
    (hsat : ∀ i : Fin (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.length,
      IdealSheaf.HasLocalGenerators
        (𝒪 := structureSheaf 𝕜 (Fin n → 𝕜)
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.stage i.succ))
        (saturationStalk
          (π := ⇑((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.map i))
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
            U hU).toSuccession.isClosedSubmanifold_center i)
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.isBlowUp_map i)
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
            U hU).toSuccession.strictTransformSubspaceSeq
            (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I i.castSucc))) :
    AnalyticSpace.IsNonsingular
      (IdealSheaf.toAnalyticSpace
        ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.strictTransformSubspaceSeq
          (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I (Fin.last _))) := by
  have heq := bedanFamOfInput_strictTransform_eq_of_hsat 𝕜 bmod n T hT U hU hsat
  rw [← heq]
  change AnalyticSpace.regularLocus _ = Set.univ
  rw [Set.eq_univ_iff_forall]
  intro y
  rw [mem_reg_toAnalyticSpace_iff]
  have hy : y.1 ∈ ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
      U hU).toSuccession.markedTransformSeq
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1 (Fin.last _)).support :=
    y.2
  have hord : (1 : ℕ∞) ≤ ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
      U hU).toSuccession.markedTransformSeq
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1 (Fin.last _)).ord y.1 :=
    Order.one_le_iff_ne_zero.mpr fun h0 => (((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
      U hU).toSuccession.markedTransformSeq
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      (Fin.last _)).ord_eq_zero_iff.mp h0) hy
  obtain ⟨c, φ, σ, cidx, hφ, hJx, -⟩ :=
    (bmod n).output_isSmoothSubmanifoldIdeal T (DomBEDan.bmoClass_one 𝕜 hT) U hU y.1 hord
  have hne : ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.markedTransformSeq
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      (Fin.last _)).stalkIdeal y.1 ≠ ⊤ := hy
  have hJx' : ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.markedTransformSeq
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      (Fin.last _)).stalkIdeal y.1 = Ideal.span (Set.range fun i =>
        coord (Fin n → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ hφ.1 hφ.2.1 (σ i)) :=
    hJx y.1 hφ.2.1
  rw [hJx'] at hne ⊢
  exact isRegularLocalRing_quotient_span_coord φ hφ.1 hφ.2.1 σ
    ((span_coord_ne_top_iff (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ hφ.1 hφ.2.1 σ).mp hne)

/-- At every point of the final strict transform of the value over `U` there is a chart adapted to
it which is a simple-normal-crossing chart of the exceptional divisors, no divisor through the point
carrying a coordinate of the strict transform (the proper form of clause (3) of
[Wlo09, Theorem 2.0.2]), under `hsat`. -/
theorem bedanFamOfInput_exists_adaptedChart_isSncChartAt_of_hsat
    (hsat : ∀ i : Fin (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.length,
      IdealSheaf.HasLocalGenerators
        (𝒪 := structureSheaf 𝕜 (Fin n → 𝕜)
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.stage i.succ))
        (saturationStalk
          (π := ⇑((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.map i))
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
            U hU).toSuccession.isClosedSubmanifold_center i)
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.isBlowUp_map i)
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
            U hU).toSuccession.strictTransformSubspaceSeq
            (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I i.castSucc))) :
    ∀ x ∈ ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
        U hU).toSuccession.strictTransformSubspaceSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
        (Fin.last _)).support,
      ∃ (c : ℕ)
        (φ : OpenPartialHomeomorph
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.stage (Fin.last _))
          (Fin n → 𝕜))
        (σ : Fin c ↪ Fin n)
        (cidx : {j // x ∈ ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
          U hU).toSuccession.totalTransformSeq (Fin.last _)).hyp j} → Fin n),
        IsAdaptedChart (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
            U hU).toSuccession.strictTransformSubspaceSeq
            (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
            (Fin.last _)).support φ σ ∧
        ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.totalTransformSeq
          (Fin.last _)).IsSncChartAt (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ x cidx ∧
        ∀ j, cidx j ∉ Set.range σ := by
  intro x hx
  have heq := bedanFamOfInput_strictTransform_eq_of_hsat 𝕜 bmod n T hT U hU hsat
  have hx' : x ∈ ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
      U hU).toSuccession.markedTransformSeq
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      (Fin.last _)).support := by
    rw [heq]
    exact hx
  have hord : (1 : ℕ∞) ≤ ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
      U hU).toSuccession.markedTransformSeq
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1 (Fin.last _)).ord x :=
    Order.one_le_iff_ne_zero.mpr fun h0 => (((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
      U hU).toSuccession.markedTransformSeq
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      (Fin.last _)).ord_eq_zero_iff.mp h0) hx'
  obtain ⟨c, φ, σ, cidx, hφ, hJx, hne⟩ :=
    (bmod n).output_isSmoothSubmanifoldIdeal T (DomBEDan.bmoClass_one 𝕜 hT) U hU x hord
  have hT' : IsEmpty (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.ι := hT.1
  obtain ⟨e, he⟩ := exists_equiv_totalTransformSeqFrom_of_isEmpty
    (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F (Fin.last _)
  refine ⟨c, φ, σ, _, ⟨hφ.1, fun a ha => ?_⟩,
    hφ.of_equiv (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) e he, fun j => ?_⟩
  · rw [← heq]
    change ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.markedTransformSeq
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      (Fin.last _)).stalkIdeal a ≠ ⊤ ↔ _
    have hJx' : ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.markedTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
        (Fin.last _)).stalkIdeal a = Ideal.span (Set.range fun i =>
          coord (Fin n → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ hφ.1 ha (σ i)) := hJx a ha
    rw [hJx']
    exact span_coord_ne_top_iff (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ hφ.1 ha σ
  · rintro ⟨i, hi⟩
    exact hne _ i hi.symm

end

end Hironaka.Manifold
