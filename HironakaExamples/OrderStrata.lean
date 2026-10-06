/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Sheaves.Init
import Hironaka.Scheme.IdealSheaf.Order.AffineSpace  -- shake: keep (used only by `example`s)

/-!
# Hauser's Exercises 3 and 4 on the order: the strata of constant order

Appendix B of [Hau03] asks for the strata of constant order of two subschemes. Exercise 3:
`f = x³ + yᵏzᵐ` on `𝔸³`; the `example`s instantiate the loci `{ord ≥ 2}` and `{ord = 3}` computed
in `Hironaka/Scheme/IdealSheaf/Order/AffineSpace.lean` at `k = m = 3` (the top locus is the union of
the two axes `{x = y = 0} ∪ {x = z = 0}`) and at `k = m = 1` (`f = x³ + yz`: order `≥ 2` only at the
origin, which has order `2`; order `3` nowhere). Exercise 4: the union of the four coordinate
hyperplanes of `𝔸⁴`, whose strata of constant order `j` are the points with exactly `j` vanishing
coordinates: the origin has order `4`, `(0, 0, 1, 1)` order `2`, `(1, 1, 1, 1)` order `0`; and
Hauser's `Y = V(xᵏyˡzᵐwⁿ)` at the origin has order `k + l + m + n`. The points are the
`K`-rational points `ratPoint a`, `K` a field of characteristic zero.
-/

-- The module consists of `example`s only, so it declares nothing public.
set_option linter.privateModule false

namespace Hironaka.Order.Examples

open AlgebraicGeometry

open AlgebraicGeometry MvPolynomial

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ### Exercise 3, `k = m = 3`: the top locus is the union of the two axes -/

/-- Hauser's Exercise 3: for `f = x³ + y³z³`, order `3` exactly on the two axes
`{x = y = 0} ∪ {x = z = 0}`. -/
example (a : Fin 3 → K) :
    (specIdealSheaf (Ideal.span
        {(X 0 ^ 3 + X 1 ^ 3 * X 2 ^ 3 : MvPolynomial (Fin 3) K)})).ord (ratPoint a) = 3 ↔
      a 0 = 0 ∧ (a 1 = 0 ∨ a 2 = 0) := by
  rw [ord_hauserEx3_eq_three_iff 3 3 (by norm_num) (by norm_num) a]
  constructor
  · rintro ⟨h0, ⟨h1, -⟩ | ⟨h2, -⟩ | ⟨h1, -, -⟩⟩
    · exact ⟨h0, Or.inl h1⟩
    · exact ⟨h0, Or.inr h2⟩
    · exact ⟨h0, Or.inl h1⟩
  · rintro ⟨h0, h1 | h2⟩
    · exact ⟨h0, Or.inl ⟨h1, le_rfl⟩⟩
    · exact ⟨h0, Or.inr (Or.inl ⟨h2, le_rfl⟩)⟩

/-- Hauser's Exercise 3: for `f = x³ + y³z³`, order `≥ 2` exactly on the two axes as well; the
strata are `{ord = 3}` = the axes, `{ord = 1}` = the rest of `V(f)`, `{ord = 0}` = the complement
of `V(f)`. -/
example (a : Fin 3 → K) :
    (2 : ℕ∞) ≤ (specIdealSheaf (Ideal.span
        {(X 0 ^ 3 + X 1 ^ 3 * X 2 ^ 3 : MvPolynomial (Fin 3) K)})).ord (ratPoint a) ↔
      a 0 = 0 ∧ (a 1 = 0 ∨ a 2 = 0) := by
  rw [two_le_ord_hauserEx3_iff 3 3 (by norm_num) (by norm_num) a]
  constructor
  · rintro ⟨h0, ⟨h1, -⟩ | ⟨h2, -⟩⟩
    · exact ⟨h0, Or.inl h1⟩
    · exact ⟨h0, Or.inr h2⟩
  · rintro ⟨h0, h1 | h2⟩
    · exact ⟨h0, Or.inl ⟨h1, Or.inl (by norm_num)⟩⟩
    · exact ⟨h0, Or.inr ⟨h2, Or.inl (by norm_num)⟩⟩

/-! ### Exercise 3, `k = m = 1`: `f = x³ + yz` -/

/-- Hauser's Exercise 3: for `f = x³ + yz`, order `≥ 2` only at the origin. -/
example (a : Fin 3 → K) :
    (2 : ℕ∞) ≤ (specIdealSheaf (Ideal.span
        {(X 0 ^ 3 + X 1 ^ 1 * X 2 ^ 1 : MvPolynomial (Fin 3) K)})).ord (ratPoint a) ↔
      a = 0 := by
  rw [two_le_ord_hauserEx3_iff 1 1 le_rfl le_rfl a]
  constructor
  · rintro ⟨h0, ⟨h1, h | h2⟩ | ⟨h2, h | h1⟩⟩
    · exact absurd h (by norm_num)
    · exact funext fun i => by fin_cases i <;> assumption
    · exact absurd h (by norm_num)
    · exact funext fun i => by fin_cases i <;> assumption
  · rintro rfl
    exact ⟨rfl, Or.inl ⟨rfl, Or.inr rfl⟩⟩

/-- Hauser's Exercise 3: for `f = x³ + yz`, no point has order `3` (the origin has order `2`). -/
example (a : Fin 3 → K) :
    (specIdealSheaf (Ideal.span
        {(X 0 ^ 3 + X 1 ^ 1 * X 2 ^ 1 : MvPolynomial (Fin 3) K)})).ord (ratPoint a) ≠ 3 := by
  rw [Ne, ord_hauserEx3_eq_three_iff 1 1 le_rfl le_rfl a]
  rintro ⟨-, ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, -, h⟩⟩ <;> norm_num at h

/-! ### Exercise 4: the four coordinate hyperplanes of `𝔸⁴` -/

/-- Hauser's Exercise 4: the origin of `𝔸⁴` lies in the stratum of order `4` of `V(xyzw)`. -/
example :
    (specIdealSheaf (Ideal.span {(X 0 * X 1 * X 2 * X 3 : MvPolynomial (Fin 4) K)})).ord
      (ratPoint (fun _ : Fin 4 => (0 : K))) = 4 := by
  rw [show (X 0 * X 1 * X 2 * X 3 : MvPolynomial (Fin 4) K) = ∏ i, X i from
    (Fin.prod_univ_four fun i => (X i : MvPolynomial (Fin 4) K)).symm,
    ord_specIdealSheaf_span_singleton_prod_X]
  simp

/-- Hauser's Exercise 4: the point `(0, 0, 1, 1)` lies in the stratum of order `2`. -/
example :
    (specIdealSheaf (Ideal.span {(X 0 * X 1 * X 2 * X 3 : MvPolynomial (Fin 4) K)})).ord
      (ratPoint ![(0 : K), 0, 1, 1]) = 2 := by
  rw [show (X 0 * X 1 * X 2 * X 3 : MvPolynomial (Fin 4) K) = ∏ i, X i ^ 1 by
    simp [Fin.prod_univ_four], ord_specIdealSheaf_span_singleton_prod_pow_X, Fin.sum_univ_four,
    show (![(0 : K), 0, 1, 1] : Fin 4 → K) 2 = 1 from rfl,
    show (![(0 : K), 0, 1, 1] : Fin 4 → K) 3 = 1 from rfl]
  norm_num

/-- Hauser's Exercise 4: the point `(1, 1, 1, 1)` lies in the stratum of order `0` (off
`V(xyzw)`). -/
example :
    (specIdealSheaf (Ideal.span {(X 0 * X 1 * X 2 * X 3 : MvPolynomial (Fin 4) K)})).ord
      (ratPoint (fun _ : Fin 4 => (1 : K))) = 0 := by
  rw [show (X 0 * X 1 * X 2 * X 3 : MvPolynomial (Fin 4) K) = ∏ i, X i from
    (Fin.prod_univ_four fun i => (X i : MvPolynomial (Fin 4) K)).symm,
    ord_specIdealSheaf_span_singleton_prod_X]
  simp

open scoped Classical in
/-- Hauser's Exercise 4, `Y = V(xᵏyˡzᵐwⁿ)`: the origin has order `k + l + m + n`. -/
example (e : Fin 4 → ℕ) :
    (specIdealSheaf (Ideal.span {(∏ i, X i ^ e i : MvPolynomial (Fin 4) K)})).ord
      (ratPoint (fun _ : Fin 4 => (0 : K))) = ∑ i, (e i : ℕ∞) := by
  rw [ord_specIdealSheaf_span_singleton_prod_pow_X]
  simp

end Hironaka.Order.Examples
