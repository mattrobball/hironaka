/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Step21BoundaryClearing
import Hironaka.Resolution.Algebraic.MaximalContact.Sequence
import Hironaka.Resolution.Algebraic.OrderReduction.Step21Disjoint
import Hironaka.Scheme.BlowUpSequence.Remark67
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The end of Step 2.1 for a round of order `1`

Step 2.1 of the proof of [Kol07, Theorem 103] (item 104, Step 2.1) passes over the members of the
boundary; at its end the birational transform of every original member misses the cosupport of the
weak transform (`disjoint_cosupp_step21_final`,
`Hironaka.Resolution.Algebraic.OrderReduction.Step21Disjoint`). For a round of order `1` the marked
transform with mark `1` is the weak transform ([Kol07, Remark 67],
`IsOrderGeSeq.markedTransformSeq_eq_weakTransformSeq`) and the cosupport `{x | 1 ≤ ord x}` is the
support (`one_le_ord_iff`), so the transforms of the members miss the SUPPORT of the marked
transform. This is the input at the end of Step 2.1 for the passage of the statements CP1 and CP3 of
the embedded desingularization (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) from
the exceptional sub-family to the full boundary along Step 2.2
(`disjoint_support_markedTransformSeq_strictTransformSeq`). Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step22` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step22`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-- At the end of Step 2.1 of a round of order `1` (`T.I.maxOrd = 1`), the birational transform of
every original member misses the support of the marked transform of `(T.I, 1)`
([Kol07, 104, Step 2.1] with [Kol07, Remark 67]): `disjoint_cosupp_step21_final` on the weak
transform, `markedTransformSeq_eq_weakTransformSeq` and `one_le_ord_iff`. -/
theorem disjoint_support_markedTransformSeq_step21_final {n : ℕ} (T : Triple k)
    (hn : T.HasDimLE n) (hmax : T.I.maxOrd ≤ 1) (bd : ∀ j : ℕ, BDData.{u} n 1 j)
    (hm : T.I.maxOrd = 1) {i : ℕ} (hi : i < Fintype.card T.E.ι) :
    Disjoint
      (SetLike.coe ((Hironaka.BO.step21Seq T hn hmax bd (Fintype.card T.E.ι)).1.markedTransformSeq
        T.I 1 (Fin.last _)).support)
      (SetLike.coe ((Hironaka.BO.step21Seq T hn hmax bd (Fintype.card T.E.ι)).1.strictTransformSeq
        (T.E.nth ⟨i, hi⟩) (Fin.last _)).support) := by
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  have hsmn : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hord := Hironaka.BO.isOrderSeq_step21Seq T hn hmax bd (Fintype.card T.E.ι)
  have hge : (Hironaka.BO.step21Seq T hn hmax bd (Fintype.card T.E.ι)).1.IsOrderGeSeq
      (T.X.left ↘ Spec (.of k)) T.I 1 T.E :=
    IsOrderSeq.isOrderGeSeq (T.X.left ↘ Spec (.of k)) n' hord
  have hm' : T.I.maxOrd = ((1 : ℕ) : ℕ∞) := by
    rw [Nat.cast_one]
    exact hm
  have hmw := IsOrderGeSeq.markedTransformSeq_eq_weakTransformSeq (T.X.left ↘ Spec (.of k)) n' hm'
    hge (Fin.last _)
  have hdisj := Hironaka.BO.disjoint_cosupp_step21_final T hn hmax bd hi
  have hset : SetLike.coe ((Hironaka.BO.step21Seq T hn hmax bd
      (Fintype.card T.E.ι)).1.weakTransformSeq T.I (Fin.last _)).support =
      {x | ((1 : ℕ) : ℕ∞) ≤ ((Hironaka.BO.step21Seq T hn hmax bd
        (Fintype.card T.E.ι)).1.weakTransformSeq T.I (Fin.last _)).ord x} := by
    ext x
    change x ∈ ((Hironaka.BO.step21Seq T hn hmax bd (Fintype.card T.E.ι)).1.weakTransformSeq T.I
      (Fin.last _)).support ↔ ((1 : ℕ) : ℕ∞) ≤ _
    rw [Nat.cast_one]
    exact (Scheme.IdealSheafData.one_le_ord_iff _ _).symm
  rw [hmw, hset]
  exact hdisj

end Hironaka.Resolution
