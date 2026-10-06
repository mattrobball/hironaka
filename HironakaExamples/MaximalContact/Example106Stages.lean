/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Derivative.Basic
import Hironaka.Scheme.IdealSheaf.Order.AffineSpace
import HironakaExamples.Balanced.PDeriv
import HironakaExamples.MaximalContact.Example106Charts
import HironakaExamples.MaximalContact.Example82
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's Example 106, the order-2 run continues: the blow-ups of `q` and of `q'`

In [Kol07, Example 106], after the blow-up of the origin the transform `I₁` on the `z`-chart,
`I₁ = (x₁³z₁ − y₁², z₁(x₁⁴z₁ + x₁ − w₁³))`, has order `2` at the origin `q ∈ E₁` of that chart
(`HironakaExamples/MaximalContact/Example106Charts.lean`), against Kollár's sentence "the order has
dropped to 1", which holds on his `x`-chart only. This file follows the order-`2` run two stages
further, computed exactly in `ℚ`:

* blowing up `q`, the `x₂`-, `y₂`- and `z₂`-charts have no point of order `2`, while on the
  `w₂`-chart `I₂ = (x₂³z₂w₂² − y₂², z₂(x₂⁴z₂w₂⁴ + x₂ − w₂²))` has order exactly `2` at its origin
  `q'`, its only `ℚ`-point of order `2`, which lies on the strict transforms `H₂ = (y₂)` and
  `H₂' = (y₂ − x₂²z₂w₂²)` (`y₂`, `y₂ − x₂²z₂w₂² ∈ MC(I₂)`);
* blowing up `q'`, again only the `w₃`-chart has a point of order `2`, its origin, for
  `I₃ = (x₃³z₃w₃⁴ − y₃², z₃(x₃⁴z₃w₃⁸ + x₃ − w₃))`, inside `H₃ = (y₃)` and `H₃' = (y₃ − x₃²z₃w₃⁴)`.

So the order-`2` run of Example 106 continues for at least three stages; its length is not
computed here. The `ℚ`-point arguments read the value and the first partials of the generators at
the point (`vanish_of_mem_m4_sq`).
-/

public section

open MvPolynomial Hironaka.Examples

namespace Hironaka.Examples.Example106Stages

/-- `x = X 0` in `ℚ[x, y, z, w]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 4) ℚ)
/-- `y = X 1`. -/
local notation "y" => (X 1 : MvPolynomial (Fin 4) ℚ)
/-- `z = X 2`. -/
local notation "z" => (X 2 : MvPolynomial (Fin 4) ℚ)
/-- `w = X 3`. -/
local notation "w" => (X 3 : MvPolynomial (Fin 4) ℚ)
/-- The `x`-chart. -/
local notation "σx" => (aeval ![X 0, X 1 * X 0, X 2 * X 0, X 3 * X 0] :
  MvPolynomial (Fin 4) ℚ →ₐ[ℚ] MvPolynomial (Fin 4) ℚ)
/-- The `y`-chart. -/
local notation "σy" => (aeval ![X 0 * X 1, X 1, X 2 * X 1, X 3 * X 1] :
  MvPolynomial (Fin 4) ℚ →ₐ[ℚ] MvPolynomial (Fin 4) ℚ)
/-- The `z`-chart. -/
local notation "σz" => (aeval ![X 0 * X 2, X 1 * X 2, X 2, X 3 * X 2] :
  MvPolynomial (Fin 4) ℚ →ₐ[ℚ] MvPolynomial (Fin 4) ℚ)
/-- The `w`-chart. -/
local notation "σw" => (aeval ![X 0 * X 3, X 1 * X 3, X 2 * X 3, X 3] :
  MvPolynomial (Fin 4) ℚ →ₐ[ℚ] MvPolynomial (Fin 4) ℚ)
/-- The maximal ideal of the `ℚ`-point `(a, b, c, d)`. -/
local notation "𝔪(" a ", " b ", " c ", " d ")" =>
  Ideal.span {x - C a, y - C b, z - C c, w - C d}


/-! ### The blow-up of `q`: the `x₂`-, `y₂`-, `z₂`-charts are empty -/

/-- The marked transforms of the generators of `I₁` on the `x₂`-chart. -/
theorem transform_example106_zx :
    σx (x ^ 3 * z - y ^ 2) = x ^ 2 * (x ^ 2 * z - y ^ 2) ∧
      σx (z * (x ^ 4 * z + x - w ^ 3)) = x ^ 2 * (z * (x ^ 4 * z + 1 - w ^ 3 * x ^ 2)) := by
  refine ⟨?_, ?_⟩ <;>
  · simp only [map_sub, map_add, map_mul, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three]
    ring

/-- No point of order `2` on the `x₂`-chart: `∂(x₂²z₂ − y₂²)/∂y₂ = −2y₂` and `∂/∂z₂ = x₂²` force
`x₂ = y₂ = 0`, and then `∂(z₂(x₂⁴z₂ + 1 − w₂³x₂²))/∂z₂ = 1`. -/
theorem empty_example106_zx (a b c d : ℚ) :
    ¬ Ideal.span {x ^ 2 * z - y ^ 2, z * (x ^ 4 * z + 1 - w ^ 3 * x ^ 2)} ≤ 𝔪(a, b, c, d) ^ 2 := by
  intro h
  obtain ⟨-, hd1⟩ := vanish_of_mem_m4_sq a b c d (h (Ideal.subset_span (by simp)) :
    x ^ 2 * z - y ^ 2 ∈ _)
  obtain ⟨-, hd2⟩ := vanish_of_mem_m4_sq a b c d (h (Ideal.subset_span (by simp)) :
    z * (x ^ 4 * z + 1 - w ^ 3 * x ^ 2) ∈ _)
  have ha : a = 0 := by simpa using hd1 2
  subst ha
  have h2 := hd2 2
  simp at h2

/-- The marked transforms on the `y₂`-chart. -/
theorem transform_example106_zy :
    σy (x ^ 3 * z - y ^ 2) = y ^ 2 * (x ^ 3 * y ^ 2 * z - 1) ∧
      σy (z * (x ^ 4 * z + x - w ^ 3)) = y ^ 2 * (z * (x ^ 4 * y ^ 4 * z + x - w ^ 3 * y ^ 2)) := by
  refine ⟨?_, ?_⟩ <;>
  · simp only [map_sub, map_add, map_mul, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three]
    ring

/-- No point of order `2` on the `y₂`-chart: `x₂³y₂²z₂ = 1` and `∂/∂y₂ = 2x₂³y₂z₂ = 0` are
incompatible. -/
theorem empty_example106_zy (a b c d : ℚ) :
    ¬ Ideal.span {x ^ 3 * y ^ 2 * z - 1, z * (x ^ 4 * y ^ 4 * z + x - w ^ 3 * y ^ 2)} ≤
      𝔪(a, b, c, d) ^ 2 := by
  intro h
  obtain ⟨hv, hd1⟩ := vanish_of_mem_m4_sq a b c d (h (Ideal.subset_span (by simp)) :
    x ^ 3 * y ^ 2 * z - 1 ∈ _)
  have hv' : a ^ 3 * b ^ 2 * c - 1 = 0 := by simpa using hv
  have h1 : a ^ 3 * b * c = 0 := by
    have h2 : c = 0 ∨ a = 0 ∨ b = 0 := by simpa using hd1 1
    rcases h2 with h | h | h <;> rw [h] <;> ring
  have : a ^ 3 * b ^ 2 * c = b * (a ^ 3 * b * c) := by ring
  rw [this, h1, mul_zero] at hv'
  norm_num at hv'

/-- The marked transforms on the `z₂`-chart. -/
theorem transform_example106_zz :
    σz (x ^ 3 * z - y ^ 2) = z ^ 2 * (x ^ 3 * z ^ 2 - y ^ 2) ∧
      σz (z * (x ^ 4 * z + x - w ^ 3)) = z ^ 2 * (x ^ 4 * z ^ 4 + x - w ^ 3 * z ^ 2) := by
  refine ⟨?_, ?_⟩ <;>
  · simp only [map_sub, map_add, map_mul, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three]
    ring

/-- No point of order `2` on the `z₂`-chart: `∂(x₂⁴z₂⁴ + x₂ − w₂³z₂²)/∂x₂ = 4x₂³z₂⁴ + 1` and
`∂(x₂³z₂² − y₂²)/∂z₂ = 2x₂³z₂` are incompatible. -/
theorem empty_example106_zz (a b c d : ℚ) :
    ¬ Ideal.span {x ^ 3 * z ^ 2 - y ^ 2, x ^ 4 * z ^ 4 + x - w ^ 3 * z ^ 2} ≤ 𝔪(a, b, c, d) ^ 2 :=
    by
  intro h
  obtain ⟨-, hd1⟩ := vanish_of_mem_m4_sq a b c d (h (Ideal.subset_span (by simp)) :
    x ^ 3 * z ^ 2 - y ^ 2 ∈ _)
  obtain ⟨-, hd2⟩ := vanish_of_mem_m4_sq a b c d (h (Ideal.subset_span (by simp)) :
    x ^ 4 * z ^ 4 + x - w ^ 3 * z ^ 2 ∈ _)
  have h1 : a ^ 3 * c = 0 := by
    have h2 : 2 * a ^ 3 * c = 0 := by simpa using hd1 2
    linarith
  have h2 : c ^ 4 * (4 * a ^ 3) + 1 = 0 := by simpa using hd2 0
  have : c ^ 4 * (4 * a ^ 3) + 1 = 4 * c ^ 3 * (a ^ 3 * c) + 1 := by ring
  rw [this, h1] at h2
  norm_num at h2

/-! ### The blow-up of `q`: the `w₂`-chart carries the point `q'` of order `2` -/

/-- The marked transforms on the `w₂`-chart and the strict transforms of `H₁, H₁'`. -/
theorem transform_example106_zw :
    σw (x ^ 3 * z - y ^ 2) = w ^ 2 * (x ^ 3 * z * w ^ 2 - y ^ 2) ∧
      σw (z * (x ^ 4 * z + x - w ^ 3)) = w ^ 2 * (z * (x ^ 4 * z * w ^ 4 + x - w ^ 2)) ∧
      σw y = w * y ∧ σw (y - x ^ 2 * z) = w * (y - x ^ 2 * z * w ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [map_sub, map_add, map_mul, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three]
    ring

/-- `I₂` has order exactly `2` at its origin `q'`. -/
theorem ord_zero_example106_zw :
    Ideal.span {x ^ 3 * z * w ^ 2 - y ^ 2, z * (x ^ 4 * z * w ^ 4 + x - w ^ 2)} ≤
        Ideal.span {x, y, z, w} ^ 2 ∧
      ¬ Ideal.span {x ^ 3 * z * w ^ 2 - y ^ 2, z * (x ^ 4 * z * w ^ 4 + x - w ^ 2)} ≤
        Ideal.span {x, y, z, w} ^ 3 := by
  refine ⟨?_, fun h => ?_⟩
  · rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · refine Ideal.sub_mem _ ?_ (Ideal.pow_mem_pow y_mem_m0_fin4 2)
      have : x ^ 3 * z * w ^ 2 = x ^ 3 * (z * w ^ 2) := by ring
      rw [this]
      refine mem_pow_of_mem_pow_of_le (k := 3 + 3) (by norm_num) (mul_mem_pow_add ?_ ?_)
      · exact Ideal.pow_mem_pow x_mem_m0_fin4 3
      · refine mem_pow_of_mem_pow_of_le (k := 1 + 2) le_rfl (mul_mem_pow_add ?_ ?_)
        · rw [pow_one]; exact z_mem_m0_fin4
        · exact Ideal.pow_mem_pow w_mem_m0_fin4 2
    · have : z * (x ^ 4 * z * w ^ 4 + x - w ^ 2) =
          x ^ 4 * (z ^ 2 * w ^ 4) + x * z - w ^ 2 * z := by ring
      rw [this]
      refine Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_
      · refine mem_pow_of_mem_pow_of_le (k := 4 + 6) (by norm_num) (mul_mem_pow_add ?_ ?_)
        · exact Ideal.pow_mem_pow x_mem_m0_fin4 4
        · exact mul_mem_pow_add (Ideal.pow_mem_pow z_mem_m0_fin4 2)
            (Ideal.pow_mem_pow w_mem_m0_fin4 4)
      · refine mem_pow_of_mem_pow_of_le (k := 1 + 1) le_rfl (mul_mem_pow_add ?_ ?_) <;>
          rw [pow_one]
        · exact x_mem_m0_fin4
        · exact z_mem_m0_fin4
      · refine mem_pow_of_mem_pow_of_le (k := 2 + 1) (by norm_num) (mul_mem_pow_add ?_ ?_)
        · exact Ideal.pow_mem_pow w_mem_m0_fin4 2
        · rw [pow_one]; exact z_mem_m0_fin4
  · have := eval_pderiv_pderiv_eq_zero_of_mem_m0_cube (h (Ideal.subset_span (by simp)) :
      x ^ 3 * z * w ^ 2 - y ^ 2 ∈ _) 1 1
    simp at this

/-- Every `ℚ`-point of order `≥ 2` on the `w₂`-chart is its origin: `∂/∂y₂ = −2y₂`,
`∂(x₂³z₂w₂² − y₂²)/∂z₂ = x₂³w₂²`, and the partials of the second generator finish the two cases
`x₂ = 0`, `w₂ = 0`. -/
theorem cosupport_example106_zw (a b c d : ℚ)
    (h : Ideal.span {x ^ 3 * z * w ^ 2 - y ^ 2, z * (x ^ 4 * z * w ^ 4 + x - w ^ 2)} ≤
      𝔪(a, b, c, d) ^ 2) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  obtain ⟨-, hd1⟩ := vanish_of_mem_m4_sq a b c d (h (Ideal.subset_span (by simp)) :
    x ^ 3 * z * w ^ 2 - y ^ 2 ∈ _)
  obtain ⟨-, hd2⟩ := vanish_of_mem_m4_sq a b c d (h (Ideal.subset_span (by simp)) :
    z * (x ^ 4 * z * w ^ 4 + x - w ^ 2) ∈ _)
  have hb : b = 0 := by simpa using hd1 1
  subst hb
  have hz1 : d = 0 ∨ a = 0 := by simpa using hd1 2
  rcases hz1 with hd | ha
  · subst hd
    have ha : a = 0 := by simpa using hd2 2
    subst ha
    have hc : c = 0 := by simpa using hd2 0
    exact ⟨rfl, rfl, hc, rfl⟩
  · subst ha
    have hc : c = 0 := by simpa using hd2 0
    subst hc
    have hd : d = 0 := by simpa using hd2 2
    exact ⟨rfl, rfl, rfl, hd⟩

/-- `q' ∈ H₂`: `y₂ ∈ MC(I₂)`. -/
theorem mem_derivative_example106_zw_H :
    y ∈ Ideal.derivative ℚ
      (Ideal.span {x ^ 3 * z * w ^ 2 - y ^ 2, z * (x ^ 4 * z * w ^ 4 + x - w ^ 2)}) := by
  have h := pderiv_mem_derivative (σ := Fin 4) 1
    (Ideal.subset_span (by simp) : x ^ 3 * z * w ^ 2 - y ^ 2 ∈ Ideal.span
      {x ^ 3 * z * w ^ 2 - y ^ 2, z * (x ^ 4 * z * w ^ 4 + x - w ^ 2)})
  have e : pderiv 1 (x ^ 3 * z * w ^ 2 - y ^ 2) = -(C 2 * y) := by simp [map_ofNat]
  rw [e, neg_mem_iff] at h
  exact mem_of_C_mul_mem (q := (2 : ℚ)) two_ne_zero h

/-- `q' ∈ H₂'`: `y₂ − x₂²z₂w₂² ∈ MC(I₂)`, with `∂(x₂³z₂w₂² − y₂²)/∂x₂ = 3x₂²z₂w₂²`. -/
theorem mem_derivative_example106_zw_H' :
    y - x ^ 2 * z * w ^ 2 ∈ Ideal.derivative ℚ
      (Ideal.span {x ^ 3 * z * w ^ 2 - y ^ 2, z * (x ^ 4 * z * w ^ 4 + x - w ^ 2)}) := by
  refine Ideal.sub_mem _ mem_derivative_example106_zw_H ?_
  have h := pderiv_mem_derivative (σ := Fin 4) 0
    (Ideal.subset_span (by simp) : x ^ 3 * z * w ^ 2 - y ^ 2 ∈ Ideal.span
      {x ^ 3 * z * w ^ 2 - y ^ 2, z * (x ^ 4 * z * w ^ 4 + x - w ^ 2)})
  have e : pderiv 0 (x ^ 3 * z * w ^ 2 - y ^ 2) = C 3 * (x ^ 2 * z * w ^ 2) := by
    simp [map_ofNat]; ring
  rw [e] at h
  exact mem_of_C_mul_mem (q := (3 : ℚ)) three_ne_zero h

/-! ### The blow-up of `q'`: three empty charts and the `w₃`-chart -/

/-- The marked transforms of the generators of `I₂` on the `x₃`-chart. -/
theorem transform_example106_zwx :
    σx (x ^ 3 * z * w ^ 2 - y ^ 2) = x ^ 2 * (x ^ 4 * z * w ^ 2 - y ^ 2) ∧
      σx (z * (x ^ 4 * z * w ^ 4 + x - w ^ 2)) =
        x ^ 2 * (z * (x ^ 8 * z * w ^ 4 + 1 - w ^ 2 * x)) := by
  refine ⟨?_, ?_⟩ <;>
  · simp only [map_sub, map_add, map_mul, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three]
    ring

/-- No point of order `2` on the `x₃`-chart: `∂(x₃⁴z₃w₃² − y₃²)/∂z₃ = x₃⁴w₃²` forces `x₃ = 0` or
`w₃ = 0`, and then `∂(z₃(x₃⁸z₃w₃⁴ + 1 − w₃²x₃))/∂z₃ = 1`. -/
theorem empty_example106_zwx (a b c d : ℚ) :
    ¬ Ideal.span {x ^ 4 * z * w ^ 2 - y ^ 2, z * (x ^ 8 * z * w ^ 4 + 1 - w ^ 2 * x)} ≤
      𝔪(a, b, c, d) ^ 2 := by
  intro h
  obtain ⟨-, hd1⟩ := vanish_of_mem_m4_sq a b c d (h (Ideal.subset_span (by simp)) :
    x ^ 4 * z * w ^ 2 - y ^ 2 ∈ _)
  obtain ⟨-, hd2⟩ := vanish_of_mem_m4_sq a b c d (h (Ideal.subset_span (by simp)) :
    z * (x ^ 8 * z * w ^ 4 + 1 - w ^ 2 * x) ∈ _)
  have hz1 : d = 0 ∨ a = 0 := by simpa using hd1 2
  rcases hz1 with hd | ha
  · subst hd
    have h2 := hd2 2
    simp at h2
  · subst ha
    have h2 := hd2 2
    simp at h2

/-- The marked transforms on the `y₃`-chart. -/
theorem transform_example106_zwy :
    σy (x ^ 3 * z * w ^ 2 - y ^ 2) = y ^ 2 * (x ^ 3 * y ^ 4 * z * w ^ 2 - 1) ∧
      σy (z * (x ^ 4 * z * w ^ 4 + x - w ^ 2)) =
        y ^ 2 * (z * (x ^ 4 * y ^ 8 * z * w ^ 4 + x - w ^ 2 * y)) := by
  refine ⟨?_, ?_⟩ <;>
  · simp only [map_sub, map_add, map_mul, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three]
    ring

/-- No point of order `2` on the `y₃`-chart: `x₃³y₃⁴z₃w₃² = 1` and `∂/∂y₃ = 4x₃³y₃³z₃w₃² = 0` are
incompatible. -/
theorem empty_example106_zwy (a b c d : ℚ) :
    ¬ Ideal.span {x ^ 3 * y ^ 4 * z * w ^ 2 - 1, z * (x ^ 4 * y ^ 8 * z * w ^ 4 + x - w ^ 2 * y)} ≤
      𝔪(a, b, c, d) ^ 2 := by
  intro h
  obtain ⟨hv, hd1⟩ := vanish_of_mem_m4_sq a b c d (h (Ideal.subset_span (by simp)) :
    x ^ 3 * y ^ 4 * z * w ^ 2 - 1 ∈ _)
  have hv' : a ^ 3 * b ^ 4 * c * d ^ 2 - 1 = 0 := by simpa using hv
  have h1 : a ^ 3 * b ^ 3 * c * d ^ 2 = 0 := by
    have h2 : d = 0 ∨ c = 0 ∨ a = 0 ∨ b = 0 := by simpa using hd1 1
    rcases h2 with h | h | h | h <;> rw [h] <;> ring
  have : a ^ 3 * b ^ 4 * c * d ^ 2 = b * (a ^ 3 * b ^ 3 * c * d ^ 2) := by ring
  rw [this, h1, mul_zero] at hv'
  norm_num at hv'

/-- The marked transforms on the `z₃`-chart. -/
theorem transform_example106_zwz :
    σz (x ^ 3 * z * w ^ 2 - y ^ 2) = z ^ 2 * (x ^ 3 * z ^ 4 * w ^ 2 - y ^ 2) ∧
      σz (z * (x ^ 4 * z * w ^ 4 + x - w ^ 2)) =
        z ^ 2 * (x ^ 4 * z ^ 8 * w ^ 4 + x - w ^ 2 * z) := by
  refine ⟨?_, ?_⟩ <;>
  · simp only [map_sub, map_add, map_mul, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three]
    ring

/-- No point of order `2` on the `z₃`-chart: `∂(x₃⁴z₃⁸w₃⁴ + x₃ − w₃²z₃)/∂x₃ = 4x₃³z₃⁸w₃⁴ + 1` and
`∂(x₃³z₃⁴w₃² − y₃²)/∂z₃ = 4x₃³z₃³w₃²` are incompatible. -/
theorem empty_example106_zwz (a b c d : ℚ) :
    ¬ Ideal.span {x ^ 3 * z ^ 4 * w ^ 2 - y ^ 2, x ^ 4 * z ^ 8 * w ^ 4 + x - w ^ 2 * z} ≤
      𝔪(a, b, c, d) ^ 2 := by
  intro h
  obtain ⟨-, hd1⟩ := vanish_of_mem_m4_sq a b c d (h (Ideal.subset_span (by simp)) :
    x ^ 3 * z ^ 4 * w ^ 2 - y ^ 2 ∈ _)
  obtain ⟨-, hd2⟩ := vanish_of_mem_m4_sq a b c d (h (Ideal.subset_span (by simp)) :
    x ^ 4 * z ^ 8 * w ^ 4 + x - w ^ 2 * z ∈ _)
  have h1 : a ^ 3 * c ^ 3 * d ^ 2 = 0 := by
    have h2 : d = 0 ∨ a = 0 ∨ c = 0 := by simpa using hd1 2
    rcases h2 with h | h | h <;> rw [h] <;> ring
  have h2 : d ^ 4 * (c ^ 8 * (4 * a ^ 3)) + 1 = 0 := by simpa using hd2 0
  have : d ^ 4 * (c ^ 8 * (4 * a ^ 3)) + 1 = 4 * c ^ 5 * d ^ 2 * (a ^ 3 * c ^ 3 * d ^ 2) + 1 := by
    ring
  rw [this, h1] at h2
  norm_num at h2

/-- The marked transforms on the `w₃`-chart and the strict transforms of `H₂, H₂'`. -/
theorem transform_example106_zww :
    σw (x ^ 3 * z * w ^ 2 - y ^ 2) = w ^ 2 * (x ^ 3 * z * w ^ 4 - y ^ 2) ∧
      σw (z * (x ^ 4 * z * w ^ 4 + x - w ^ 2)) = w ^ 2 * (z * (x ^ 4 * z * w ^ 8 + x - w)) ∧
      σw y = w * y ∧ σw (y - x ^ 2 * z * w ^ 2) = w * (y - x ^ 2 * z * w ^ 4) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [map_sub, map_add, map_mul, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three]
    ring

/-- `I₃` has order exactly `2` at its origin. -/
theorem ord_zero_example106_zww :
    Ideal.span {x ^ 3 * z * w ^ 4 - y ^ 2, z * (x ^ 4 * z * w ^ 8 + x - w)} ≤
        Ideal.span {x, y, z, w} ^ 2 ∧
      ¬ Ideal.span {x ^ 3 * z * w ^ 4 - y ^ 2, z * (x ^ 4 * z * w ^ 8 + x - w)} ≤
        Ideal.span {x, y, z, w} ^ 3 := by
  refine ⟨?_, fun h => ?_⟩
  · rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · refine Ideal.sub_mem _ ?_ (Ideal.pow_mem_pow y_mem_m0_fin4 2)
      have : x ^ 3 * z * w ^ 4 = x ^ 3 * (z * w ^ 4) := by ring
      rw [this]
      refine mem_pow_of_mem_pow_of_le (k := 3 + 5) (by norm_num) (mul_mem_pow_add ?_ ?_)
      · exact Ideal.pow_mem_pow x_mem_m0_fin4 3
      · refine mem_pow_of_mem_pow_of_le (k := 1 + 4) le_rfl (mul_mem_pow_add ?_ ?_)
        · rw [pow_one]; exact z_mem_m0_fin4
        · exact Ideal.pow_mem_pow w_mem_m0_fin4 4
    · have : z * (x ^ 4 * z * w ^ 8 + x - w) = x ^ 4 * (z ^ 2 * w ^ 8) + x * z - w * z := by ring
      rw [this]
      refine Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_
      · refine mem_pow_of_mem_pow_of_le (k := 4 + 10) (by norm_num) (mul_mem_pow_add ?_ ?_)
        · exact Ideal.pow_mem_pow x_mem_m0_fin4 4
        · exact mul_mem_pow_add (Ideal.pow_mem_pow z_mem_m0_fin4 2)
            (Ideal.pow_mem_pow w_mem_m0_fin4 8)
      · refine mem_pow_of_mem_pow_of_le (k := 1 + 1) le_rfl (mul_mem_pow_add ?_ ?_) <;>
          rw [pow_one]
        · exact x_mem_m0_fin4
        · exact z_mem_m0_fin4
      · refine mem_pow_of_mem_pow_of_le (k := 1 + 1) le_rfl (mul_mem_pow_add ?_ ?_) <;>
          rw [pow_one]
        · exact w_mem_m0_fin4
        · exact z_mem_m0_fin4
  · have := eval_pderiv_pderiv_eq_zero_of_mem_m0_cube (h (Ideal.subset_span (by simp)) :
      x ^ 3 * z * w ^ 4 - y ^ 2 ∈ _) 1 1
    simp at this

/-- Every `ℚ`-point of order `≥ 2` on the `w₃`-chart is its origin:
`∂(x₃³z₃w₃⁴ − y₃²)/∂z₃ = x₃³w₃⁴` splits the cases `x₃ = 0` and `w₃ = 0`, which
`∂(z₃(x₃⁴z₃w₃⁸ + x₃ − w₃))/∂x₃ = 4x₃³z₃²w₃⁸ + z₃` and `∂/∂z₃ = 2x₃⁴z₃w₃⁸ + x₃ − w₃` finish. -/
theorem cosupport_example106_zww (a b c d : ℚ)
    (h : Ideal.span {x ^ 3 * z * w ^ 4 - y ^ 2, z * (x ^ 4 * z * w ^ 8 + x - w)} ≤
      𝔪(a, b, c, d) ^ 2) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  obtain ⟨-, hd1⟩ := vanish_of_mem_m4_sq a b c d (h (Ideal.subset_span (by simp)) :
    x ^ 3 * z * w ^ 4 - y ^ 2 ∈ _)
  obtain ⟨-, hd2⟩ := vanish_of_mem_m4_sq a b c d (h (Ideal.subset_span (by simp)) :
    z * (x ^ 4 * z * w ^ 8 + x - w) ∈ _)
  have hb : b = 0 := by simpa using hd1 1
  subst hb
  have hz1 : d = 0 ∨ a = 0 := by simpa using hd1 2
  rcases hz1 with hd | ha
  · subst hd
    have ha : a = 0 := by simpa using hd2 2
    subst ha
    have hc : c = 0 := by simpa using hd2 0
    exact ⟨rfl, rfl, hc, rfl⟩
  · subst ha
    have hc : c = 0 := by simpa using hd2 0
    subst hc
    have hd : d = 0 := by simpa using hd2 2
    exact ⟨rfl, rfl, rfl, hd⟩

/-- The origin of the `w₃`-chart lies on `H₃`: `y₃ ∈ MC(I₃)`. -/
theorem mem_derivative_example106_zww_H :
    y ∈ Ideal.derivative ℚ
      (Ideal.span {x ^ 3 * z * w ^ 4 - y ^ 2, z * (x ^ 4 * z * w ^ 8 + x - w)}) := by
  have h := pderiv_mem_derivative (σ := Fin 4) 1
    (Ideal.subset_span (by simp) : x ^ 3 * z * w ^ 4 - y ^ 2 ∈ Ideal.span
      {x ^ 3 * z * w ^ 4 - y ^ 2, z * (x ^ 4 * z * w ^ 8 + x - w)})
  have e : pderiv 1 (x ^ 3 * z * w ^ 4 - y ^ 2) = -(C 2 * y) := by simp [map_ofNat]
  rw [e, neg_mem_iff] at h
  exact mem_of_C_mul_mem (q := (2 : ℚ)) two_ne_zero h

/-- The origin of the `w₃`-chart lies on `H₃'`: `y₃ − x₃²z₃w₃⁴ ∈ MC(I₃)`. -/
theorem mem_derivative_example106_zww_H' :
    y - x ^ 2 * z * w ^ 4 ∈ Ideal.derivative ℚ
      (Ideal.span {x ^ 3 * z * w ^ 4 - y ^ 2, z * (x ^ 4 * z * w ^ 8 + x - w)}) := by
  refine Ideal.sub_mem _ mem_derivative_example106_zww_H ?_
  have h := pderiv_mem_derivative (σ := Fin 4) 0
    (Ideal.subset_span (by simp) : x ^ 3 * z * w ^ 4 - y ^ 2 ∈ Ideal.span
      {x ^ 3 * z * w ^ 4 - y ^ 2, z * (x ^ 4 * z * w ^ 8 + x - w)})
  have e : pderiv 0 (x ^ 3 * z * w ^ 4 - y ^ 2) = C 3 * (x ^ 2 * z * w ^ 4) := by
    simp [map_ofNat]; ring
  rw [e] at h
  exact mem_of_C_mul_mem (q := (3 : ℚ)) three_ne_zero h

end Hironaka.Examples.Example106Stages
