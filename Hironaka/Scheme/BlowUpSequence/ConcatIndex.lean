/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Basic
public import Hironaka.Scheme.BlowUpSequence.Concat
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Concatenation of blow-up sequences: the stages and transforms at a shifted index

The stage of `S.concat T` at an index `S.length + i` is the stage `i` of `T`, and the center and
the transforms of an ideal sheaf or a boundary there are those of `T` at `i` for the transforms
along `S`; below `S.length` they are those of `S`. These are the analogues, for the suffix, of the
truncation lemmas `stage_take_mk` and `markedTransformSeq_take_heq_mk` of
`Hironaka/Scheme/BlowUpSequence/Truncate.lean` for the prefix (Kollár's `Π_{ij}` bookkeeping,
[Kol07, Definition 29]). The embedded resolution reads a run of the marked order reduction
functor (the blow-up sequence the functor assigns to a triple), which is a concatenation of
rounds, round by round with these lemmas.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData BlowUpSequence

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The stage of a concatenation at an index `j = S.length + i` is the stage `i` of the second
sequence. -/
theorem stage_concat_mk : ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (T : BlowUpSequence S.last)
    (j i : ℕ) (hj : j < (S.concat T).length + 1) (hi : i < T.length + 1),
    j = S.length + i → (S.concat T).stage ⟨j, hj⟩ = T.stage ⟨i, hi⟩
  | _, nil _, T, j, i, hj, hi, e => by
    simp only [length] at e
    obtain rfl : j = i := by omega
    rfl
  | _, cons X D rest, T, j, i, hj, hi, e => by
    cases j with
    | zero =>
      simp only [length] at e
      omega
    | succ j =>
      exact stage_concat_mk rest T j i (Nat.lt_of_succ_lt_succ hj) hi
        (by simp only [length] at e; omega)

/-- The centre of a concatenation at an index `j = S.length + i` is the centre `i` of the second
sequence, heterogeneously. -/
theorem center_concat_heq_mk : ∀ {X : Scheme.{u}} (S : BlowUpSequence X)
    (T : BlowUpSequence S.last) (j i : ℕ) (hj : j < (S.concat T).length) (hi : i < T.length),
    j = S.length + i → HEq ((S.concat T).center ⟨j, hj⟩) (T.center ⟨i, hi⟩)
  | _, nil _, T, j, i, hj, hi, e => by
    simp only [length] at e
    obtain rfl : j = i := by omega
    rfl
  | _, cons X D rest, T, j, i, hj, hi, e => by
    cases j with
    | zero =>
      simp only [length] at e
      omega
    | succ j =>
      exact center_concat_heq_mk rest T j i (Nat.lt_of_succ_lt_succ hj) hi
        (by simp only [length] at e; omega)

/-- The marked transform along a concatenation at an index `j = S.length + i` is the marked
transform along the second sequence at `i` of the marked transform along the first,
heterogeneously. -/
theorem markedTransformSeq_concat_heq_mk : ∀ {X : Scheme.{u}} (S : BlowUpSequence X)
    (T : BlowUpSequence S.last) (I : X.IdealSheafData) (m j i : ℕ)
    (hj : j < (S.concat T).length + 1) (hi : i < T.length + 1), j = S.length + i →
    HEq ((S.concat T).markedTransformSeq I m ⟨j, hj⟩)
      (T.markedTransformSeq (S.markedTransformSeq I m (Fin.last _)) m ⟨i, hi⟩)
  | _, nil _, T, I, m, j, i, hj, hi, e => by
    simp only [length] at e
    obtain rfl : j = i := by omega
    rfl
  | _, cons X D rest, T, I, m, j, i, hj, hi, e => by
    cases j with
    | zero =>
      simp only [length] at e
      omega
    | succ j =>
      exact markedTransformSeq_concat_heq_mk rest T (I.markedTransform D m) m j i
        (Nat.lt_of_succ_lt_succ hj) hi (by simp only [length] at e; omega)

/-- The strict transform along a concatenation at an index `j = S.length + i`, heterogeneously. -/
theorem strictTransformSeq_concat_heq_mk : ∀ {X : Scheme.{u}} (S : BlowUpSequence X)
    (T : BlowUpSequence S.last) (I : X.IdealSheafData) (j i : ℕ)
    (hj : j < (S.concat T).length + 1) (hi : i < T.length + 1), j = S.length + i →
    HEq ((S.concat T).strictTransformSeq I ⟨j, hj⟩)
      (T.strictTransformSeq (S.strictTransformSeq I (Fin.last _)) ⟨i, hi⟩)
  | _, nil _, T, I, j, i, hj, hi, e => by
    simp only [length] at e
    obtain rfl : j = i := by omega
    rfl
  | _, cons X D rest, T, I, j, i, hj, hi, e => by
    cases j with
    | zero =>
      simp only [length] at e
      omega
    | succ j =>
      exact strictTransformSeq_concat_heq_mk rest T (I.strictTransform D) j i
        (Nat.lt_of_succ_lt_succ hj) hi (by simp only [length] at e; omega)

/-- The total transform along a concatenation at an index `j = S.length + i`, heterogeneously. -/
theorem totalTransformSeq_concat_heq_mk : ∀ {X : Scheme.{u}} (S : BlowUpSequence X)
    (T : BlowUpSequence S.last) (E : DivisorFamily X) (j i : ℕ)
    (hj : j < (S.concat T).length + 1) (hi : i < T.length + 1), j = S.length + i →
    HEq ((S.concat T).totalTransformSeq E ⟨j, hj⟩)
      (T.totalTransformSeq (S.totalTransformSeq E (Fin.last _)) ⟨i, hi⟩)
  | _, nil _, T, E, j, i, hj, hi, e => by
    simp only [length] at e
    obtain rfl : j = i := by omega
    rfl
  | _, cons X D rest, T, E, j, i, hj, hi, e => by
    cases j with
    | zero =>
      simp only [length] at e
      omega
    | succ j =>
      exact totalTransformSeq_concat_heq_mk rest T (E.totalTransform D) j i
        (Nat.lt_of_succ_lt_succ hj) hi (by simp only [length] at e; omega)

/-! ### Below the first sequence's length -/

/-- The stage of a concatenation at an index `j ≤ S.length` is the stage `j` of the first
sequence. -/
theorem stage_concat_mk_of_le : ∀ {X : Scheme.{u}} (S : BlowUpSequence X)
    (T : BlowUpSequence S.last) (j : ℕ) (hj : j < (S.concat T).length + 1) (hj' : j < S.length + 1),
    (S.concat T).stage ⟨j, hj⟩ = S.stage ⟨j, hj'⟩
  | _, nil _, T, j, hj, hj' => by
    simp only [length] at hj'
    obtain rfl : j = 0 := by omega
    cases T <;> rfl
  | _, cons X D rest, T, j, hj, hj' => by
    cases j with
    | zero => rfl
    | succ j =>
      exact stage_concat_mk_of_le rest T j (Nat.lt_of_succ_lt_succ hj) (Nat.lt_of_succ_lt_succ hj')

/-- The centre of a concatenation at an index `j < S.length` is the centre `j` of the first
sequence, heterogeneously. -/
theorem center_concat_heq_mk_of_lt : ∀ {X : Scheme.{u}} (S : BlowUpSequence X)
    (T : BlowUpSequence S.last) (j : ℕ) (hj : j < (S.concat T).length) (hj' : j < S.length),
    HEq ((S.concat T).center ⟨j, hj⟩) (S.center ⟨j, hj'⟩)
  | _, nil _, T, j, hj, hj' => by
    simp only [length] at hj'
    omega
  | _, cons X D rest, T, j, hj, hj' => by
    cases j with
    | zero => rfl
    | succ j =>
      exact center_concat_heq_mk_of_lt rest T j (Nat.lt_of_succ_lt_succ hj)
        (Nat.lt_of_succ_lt_succ hj')

/-- The marked transform along a concatenation at an index `j ≤ S.length` is the marked transform
along the first sequence, heterogeneously. -/
theorem markedTransformSeq_concat_heq_mk_of_le : ∀ {X : Scheme.{u}} (S : BlowUpSequence X)
    (T : BlowUpSequence S.last) (I : X.IdealSheafData) (m j : ℕ) (hj : j < (S.concat T).length + 1)
    (hj' : j < S.length + 1),
    HEq ((S.concat T).markedTransformSeq I m ⟨j, hj⟩) (S.markedTransformSeq I m ⟨j, hj'⟩)
  | _, nil _, T, I, m, j, hj, hj' => by
    simp only [length] at hj'
    obtain rfl : j = 0 := by omega
    cases T <;> rfl
  | _, cons X D rest, T, I, m, j, hj, hj' => by
    cases j with
    | zero => rfl
    | succ j =>
      exact markedTransformSeq_concat_heq_mk_of_le rest T (I.markedTransform D m) m j
        (Nat.lt_of_succ_lt_succ hj) (Nat.lt_of_succ_lt_succ hj')

/-- The strict transform along a concatenation at an index `j ≤ S.length`, heterogeneously. -/
theorem strictTransformSeq_concat_heq_mk_of_le : ∀ {X : Scheme.{u}} (S : BlowUpSequence X)
    (T : BlowUpSequence S.last) (I : X.IdealSheafData) (j : ℕ) (hj : j < (S.concat T).length + 1)
    (hj' : j < S.length + 1),
    HEq ((S.concat T).strictTransformSeq I ⟨j, hj⟩) (S.strictTransformSeq I ⟨j, hj'⟩)
  | _, nil _, T, I, j, hj, hj' => by
    simp only [length] at hj'
    obtain rfl : j = 0 := by omega
    cases T <;> rfl
  | _, cons X D rest, T, I, j, hj, hj' => by
    cases j with
    | zero => rfl
    | succ j =>
      exact strictTransformSeq_concat_heq_mk_of_le rest T (I.strictTransform D) j
        (Nat.lt_of_succ_lt_succ hj) (Nat.lt_of_succ_lt_succ hj')

/-- The total transform along a concatenation at an index `j ≤ S.length`, heterogeneously. -/
theorem totalTransformSeq_concat_heq_mk_of_le : ∀ {X : Scheme.{u}} (S : BlowUpSequence X)
    (T : BlowUpSequence S.last) (E : DivisorFamily X) (j : ℕ) (hj : j < (S.concat T).length + 1)
    (hj' : j < S.length + 1),
    HEq ((S.concat T).totalTransformSeq E ⟨j, hj⟩) (S.totalTransformSeq E ⟨j, hj'⟩)
  | _, nil _, T, E, j, hj, hj' => by
    simp only [length] at hj'
    obtain rfl : j = 0 := by omega
    cases T <;> rfl
  | _, cons X D rest, T, E, j, hj, hj' => by
    cases j with
    | zero => rfl
    | succ j =>
      exact totalTransformSeq_concat_heq_mk_of_le rest T (E.totalTransform D) j
        (Nat.lt_of_succ_lt_succ hj) (Nat.lt_of_succ_lt_succ hj')

end AlgebraicGeometry
