/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Balanced.Basic
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The tuned ideal `I + D(I)²` at `m = 2`: the general facts

[Kol07, Proposition 99] for the maximal coefficient ideal `W_s(I)` at `m = 2`,
`s = m! = 2 = 1·lcm(2)`: `W_2(I) = I + D(I)²` (`W_two_eq` of
`Hironaka.Resolution.Algebraic.Tuning.Assemble`, in the sheaf vocabulary) is MC-invariant (99.5) and
D-balanced (99.8). Here these facts are proved for the intrinsic derivative ideal `Ideal.derivative
k` of `Hironaka.Derivative` on any `k`-algebra, with no hypothesis on `I`, the form the
polynomial-ring examples `HironakaExamples.Balanced.Example11` and `Example106` (Kollár's Examples
11 and 106) instantiate:

* `D(I + D(I)²) = D(I)` — `⊇` by monotonicity; `⊆` since
  `D(D(I)²) ⊆ D(D(I))·D(I) + D(I)·D(D(I)) ⊆ D(I)` by the Leibniz rule (`derivative_mul_le`)
  (`derivative_sup_derivative_sq`);
* hence `D(I + D(I)²)² = D(I)² ⊆ I + D(I)²`: `I + D(I)²` is D-balanced with respect to `2`
  ([Kol07, Definition 83]; the clause `i = 0` is trivial) (`isDBalanced_sup_derivative_sq`) and
  MC-invariant with respect to `2`, `MC(W)·D(W) = D(W)·D(W) ⊆ W` ([Kol07, Definition 79]:
  `MC(W) = D^{2−1}(W) = D(W)`) (`mcInvariant_sup_derivative_sq`).

The same facts in coordinates on a regular local ring are `RegularCoords.isMCInvariant_W` and
`RegularCoords.isDBalanced_W` of `Hironaka.Local`; nothing here redefines `W`.
-/

public section

namespace Ideal

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] (I : Ideal A)

/-- `D(I + D(I)²) = D(I)` (the computation behind [Kol07, Proposition 99] at `m = 2`). -/
theorem derivative_sup_derivative_sq :
    derivative k (I ⊔ derivative k I ^ 2) = derivative k I := by
  refine le_antisymm ?_ (derivative_mono le_sup_left)
  rw [derivative_sup, pow_two]
  refine sup_le le_rfl ((derivative_mul_le _ _).trans (sup_le ?_ ?_))
  · exact Ideal.mul_le_right
  · exact Ideal.mul_le_left

/-- [Kol07, Proposition 99 (8)] at `m = 2`, `s = 2`, for the intrinsic derivative ideal: `I + D(I)²`
is D-balanced with respect to `2`, since `D(I + D(I)²)² = D(I)² ⊆ I + D(I)²`. -/
theorem isDBalanced_sup_derivative_sq : IsDBalanced k (I ⊔ derivative k I ^ 2) 2 := by
  intro i hi
  interval_cases i
  · exact le_rfl
  · rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, derivativeIter_succ, derivativeIter_zero,
      derivative_sup_derivative_sq]
    exact le_sup_right

/-- [Kol07, Proposition 99 (5)] at `m = 2`, for the intrinsic derivative ideal: `I + D(I)²` is
MC-invariant with respect to `2`, `MC(W)·D(W) = D(W)·D(W) ⊆ W` (`MC(W) = D^{2−1}(W) = D(W)`). -/
theorem mcInvariant_sup_derivative_sq :
    derivative k (I ⊔ derivative k I ^ 2) * derivative k (I ⊔ derivative k I ^ 2) ≤
      I ⊔ derivative k I ^ 2 := by
  rw [derivative_sup_derivative_sq, ← pow_two]
  exact le_sup_right

end Ideal
