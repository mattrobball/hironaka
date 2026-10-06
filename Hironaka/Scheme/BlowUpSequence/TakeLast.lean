/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Truncate
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The last stage of a prefix is a stage of the sequence

The truncation `S.take n` (`Hironaka/Scheme/BlowUpSequence/Truncate.lean`) has the stages and the
induced data of `S` up to `n`, stated there index by index as heterogeneous equalities
(`stage_take_mk`, `markedTransformSeq_take_heq_mk`, …). The embedded resolution reads a prefix
`run.take n₀` of a run of the order reduction functor (the blow-up sequence the functor assigns to a
triple) at its last stage (`Fin.last`), while the clauses about the run (the order condition of
[Kol07, Definition 66], the stop rule `CenterContains`, the behaviour off the centers) are stated
at the run's stage `⟨n₀, _⟩`. This module restates the truncation lemmas
at the last stage of the prefix, for `n ≤ S.length`: `(S.take n).last = S.stage ⟨n, _⟩`, and the
heterogeneous equalities of the marked, strict and total transforms and of the stage map there.
A proposition is transported across them by generalizing the scheme, as in `ord_cast_of_heq` of
`Truncate.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The length of the prefix `S.take n`, `n ≤ S.length`, is `n`; hence
`n < (S.take n).length + 1`. -/
theorem lt_length_take_succ (S : BlowUpSequence X) {n : ℕ} (hn : n ≤ S.length) :
    n < (S.take n).length + 1 := by
  rw [length_take_of_le S hn]
  exact Nat.lt_succ_self n

/-- The last index of the prefix, as the index `⟨n, _⟩`. -/
theorem fin_last_take_eq (S : BlowUpSequence X) {n : ℕ} (hn : n ≤ S.length) :
    (Fin.last (S.take n).length : Fin ((S.take n).length + 1)) = ⟨n, lt_length_take_succ S hn⟩ :=
  Fin.ext (length_take_of_le S hn)

/-- The last stage of the prefix `S.take n` is the stage `n` of `S`. -/
theorem stage_take_last (S : BlowUpSequence X) {n : ℕ} (hn : n ≤ S.length) :
    (S.take n).last = S.stage ⟨n, Nat.lt_succ_of_le hn⟩ := by
  change (S.take n).stage (Fin.last _) = _
  rw [fin_last_take_eq S hn]
  exact stage_take_mk S n n (lt_length_take_succ S hn) (Nat.lt_succ_of_le hn)

/-- The marked transform at the last stage of the prefix is the marked transform at stage `n`. -/
theorem markedTransformSeq_take_last_heq (S : BlowUpSequence X) (J : X.IdealSheafData) (c : ℕ)
    {n : ℕ} (hn : n ≤ S.length) :
    HEq ((S.take n).markedTransformSeq J c (Fin.last _))
      (S.markedTransformSeq J c ⟨n, Nat.lt_succ_of_le hn⟩) := by
  rw [fin_last_take_eq S hn]
  exact markedTransformSeq_take_heq_mk S J c n n (lt_length_take_succ S hn) (Nat.lt_succ_of_le hn)

/-- The strict transform at the last stage of the prefix is the strict transform at stage `n`. -/
theorem strictTransformSeq_take_last_heq (S : BlowUpSequence X) (J : X.IdealSheafData) {n : ℕ}
    (hn : n ≤ S.length) :
    HEq ((S.take n).strictTransformSeq J (Fin.last _))
      (S.strictTransformSeq J ⟨n, Nat.lt_succ_of_le hn⟩) := by
  rw [fin_last_take_eq S hn]
  exact strictTransformSeq_take_heq_mk S J n n (lt_length_take_succ S hn) (Nat.lt_succ_of_le hn)

/-- The total transform of a family at the last stage of the prefix is the one at stage `n`. -/
theorem totalTransformSeq_take_last_heq (S : BlowUpSequence X) (E : DivisorFamily X) {n : ℕ}
    (hn : n ≤ S.length) :
    HEq ((S.take n).totalTransformSeq E (Fin.last _))
      (S.totalTransformSeq E ⟨n, Nat.lt_succ_of_le hn⟩) := by
  rw [fin_last_take_eq S hn]
  exact totalTransformSeq_take_heq_mk S E n n (lt_length_take_succ S hn) (Nat.lt_succ_of_le hn)

/-- The composite of the prefix is the stage map at stage `n`. -/
theorem composite_take_heq (S : BlowUpSequence X) {n : ℕ} (hn : n ≤ S.length) :
    HEq (S.take n).composite (S.stageMap ⟨n, Nat.lt_succ_of_le hn⟩) := by
  change HEq ((S.take n).stageMap (Fin.last _)) _
  rw [fin_last_take_eq S hn]
  exact stageMap_take_heq_mk S n n (lt_length_take_succ S hn) (Nat.lt_succ_of_le hn)

end AlgebraicGeometry
