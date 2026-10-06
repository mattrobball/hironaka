/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Derivative.Basic
import Hironaka.Scheme.IdealSheaf.Order.AffineSpace
import HironakaExamples.Balanced.PDeriv
import HironakaExamples.MaximalContact.Example11Charts
import HironakaExamples.MaximalContact.Example12Charts
import HironakaExamples.MaximalContact.Example82
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's Example 12: the three point blow-ups on the `z`-chart

[Kol07, Example 12], `m = 3`: after the blow-up of the origin, on the `z`-chart,
`f₁ = x₁³ + z₁(y₁² − z₁⁴)² + z₁¹⁸`; two more point blow-ups (the origin of the `z`-chart each time)
give `f₂ = x₂³ + z₂²(y₂² − z₂²)² + z₂¹⁵` and `f₃ = x₃³ + z₃³((y₃² − 1)² + z₃⁹)`, Kollár's three
displays, the third regrouped (printed `x₃³ + z₃³(y₃² − 1)² + z₃¹²`). Computed exactly: `I₁ = (f₁)`
and `I₂ = (f₂)` have order exactly `3` at the origin,
their only `ℚ`-point of order `≥ 3`; the locus of order `3` of `I₃ = (f₃)` is the line
`x₃ = z₃ = 0`; at every stage `Hᵢ = (xᵢ)` and `Hᵢ' = (xᵢ + …)` lie in `MC(Iᵢ) = D²(Iᵢ)`
(`∂²fᵢ/∂xᵢ² = 6xᵢ`, and `∂²fᵢ/∂yᵢ²` is `4` times the second generator); the restriction
`I₃|_{H₃} = (z₃³·g)` with `g = (y₃² − 1)² + z₃⁹` Kollár's equation of the birational transform of
`S ∩ H`, the factor `z₃³` being the exceptional part that the marked transform carries.
-/

@[expose] public section

open MvPolynomial Hironaka.Examples

namespace Hironaka.Examples.Example12Stages

/-- `x = X 0` in `ℚ[x, y, z]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 3) ℚ)
/-- `y = X 1`. -/
local notation "y" => (X 1 : MvPolynomial (Fin 3) ℚ)
/-- `z = X 2`. -/
local notation "z" => (X 2 : MvPolynomial (Fin 3) ℚ)
/-- `y = X 0` in `ℚ[y, z]`. -/
local notation "yR" => (X 0 : MvPolynomial (Fin 2) ℚ)
/-- `z = X 1` in `ℚ[y, z]`. -/
local notation "zR" => (X 1 : MvPolynomial (Fin 2) ℚ)
/-- The `z`-chart. -/
local notation "σz" => (aeval ![X 0 * X 2, X 1 * X 2, X 2] :
  MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 3) ℚ)
/-- Restriction to `(x = 0)` into `ℚ[y, z]`. -/
local notation "ρH" => (aeval ![0, X 0, X 1] :
  MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ)


/-- The three stage polynomials. -/
noncomputable abbrev f1 : MvPolynomial (Fin 3) ℚ := x ^ 3 + z * (y ^ 2 - z ^ 4) ^ 2 + z ^ 18
noncomputable abbrev f2 : MvPolynomial (Fin 3) ℚ := x ^ 3 + z ^ 2 * (y ^ 2 - z ^ 2) ^ 2 + z ^ 15
noncomputable abbrev f3 : MvPolynomial (Fin 3) ℚ := x ^ 3 + z ^ 3 * ((y ^ 2 - 1) ^ 2 + z ^ 9)

/-- `x ∈ D²(⟨g⟩)` whenever `∂²g/∂x² = 6x`. -/
theorem x_mem_derivativeIter_two_of_pderiv00 (g : MvPolynomial (Fin 3) ℚ)
    (hg : pderiv 0 (pderiv 0 g) = C 6 * x) : x ∈ Ideal.derivativeIter ℚ 2 (Ideal.span {g}) := by
  change x ∈ Ideal.derivativeIter ℚ (1 + 1) _
  rw [Ideal.derivativeIter_succ, Ideal.derivativeIter_succ, Ideal.derivativeIter_zero]
  have h := Example12Charts.hD 0 (Example12Charts.hD 0 (Ideal.mem_span_singleton_self g))
  rw [hg] at h
  exact mem_of_C_mul_mem (q := (6 : ℚ)) (by norm_num) h

/-- `q ∈ D²(⟨g⟩)` whenever `∂²g/∂y² = 4q`. -/
theorem mem_derivativeIter_two_of_pderiv11 (g q : MvPolynomial (Fin 3) ℚ)
    (hg : pderiv 1 (pderiv 1 g) = C 4 * q) : q ∈ Ideal.derivativeIter ℚ 2 (Ideal.span {g}) := by
  change q ∈ Ideal.derivativeIter ℚ (1 + 1) _
  rw [Ideal.derivativeIter_succ, Ideal.derivativeIter_succ, Ideal.derivativeIter_zero]
  have h := Example12Charts.hD 1 (Example12Charts.hD 1 (Ideal.mem_span_singleton_self g))
  rw [hg] at h
  exact mem_of_C_mul_mem (q := (4 : ℚ)) (by norm_num) h

/-! ### Stage 1 -/

/-- The first blow-up on the `z`-chart: `σ f = z₁³ f₁` with `f₁ = x₁³ + z₁(y₁² − z₁⁴)² + z₁¹⁸`,
Kollár's display, and the transforms of the equations of `H` and `H'`. -/
theorem transform_example12_z :
    σz (x ^ 3 + (y ^ 2 - z ^ 6) ^ 2 + z ^ 21) =
        z ^ 3 * (x ^ 3 + z * (y ^ 2 - z ^ 4) ^ 2 + z ^ 18) ∧
      σz x = z * x ∧ σz (x + 3 * y ^ 2 - z ^ 6) = z * (x + 3 * y ^ 2 * z - z ^ 5) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring

/-- `I₁ = (f₁)` has order exactly `3` at the origin. -/
theorem ord_zero_example12_z :
    Ideal.span {f1} ≤ Ideal.span {x, y, z} ^ 3 ∧ ¬ Ideal.span {f1} ≤ Ideal.span {x, y, z} ^ 4 := by
  refine ⟨(Ideal.span_singleton_le_iff_mem _).mpr ?_, fun h => ?_⟩
  · have hv : y ^ 2 - z ^ 4 ∈ Ideal.span {x, y, z} ^ 2 := by
      refine Ideal.sub_mem _ (Ideal.pow_mem_pow y_mem_m0 2) ?_
      exact mem_pow_of_mem_pow_of_le (by norm_num) (Ideal.pow_mem_pow z_mem_m0 4)
    refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.pow_mem_pow x_mem_m0 3) ?_) ?_
    · rw [sq]
      refine mem_pow_of_mem_pow_of_le (k := 1 + (2 + 2)) (by norm_num)
        (mul_mem_pow_add ?_ (mul_mem_pow_add hv hv))
      rw [pow_one]; exact z_mem_m0
    · exact mem_pow_of_mem_pow_of_le (by norm_num) (Ideal.pow_mem_pow z_mem_m0 18)
  · have := eval_pderiv3_eq_zero_of_mem_m3_zero_pow4 ((Ideal.span_singleton_le_iff_mem _).mp h)
      0 0 0
    simp at this

/-- Stage 1: the origin is the only `ℚ`-point of order `≥ 3`, from `∂²f₁/∂x² = 6x`,
`∂²f₁/∂y² = 4z(3y² − z⁴)`, `∂f₁/∂z|_{z=0} = y⁴`, `∂²f₁/∂y∂z = 4y(y² − 5z⁴)`. -/
theorem cosupport_example12_z (a b c : ℚ)
    (h : Ideal.span {f1} ≤ Ideal.span {x - C a, y - C b, z - C c} ^ 3) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨-, hd, hdd⟩ := vanish_of_mem_m3_cube a b c ((Ideal.span_singleton_le_iff_mem _).mp h)
  have ha : a = 0 := by simpa using hdd 0 0
  have Eyy : c * (3 * b ^ 2 - c ^ 4) = 0 := by
    have h : c = 0 ∨ (b ^ 2 - c ^ 4) * 2 + 2 * b * (2 * b) = 0 := by simpa using hdd 1 1
    rcases h with h | h
    · rw [h]; ring
    · linear_combination c * h / 2
  have Ez : (b ^ 2 - c ^ 4) ^ 2 - 8 * c ^ 4 * (b ^ 2 - c ^ 4) + 18 * c ^ 17 = 0 := by
    have := hd 2
    simp at this
    linear_combination this
  have Eyz : b * (b ^ 2 - 5 * c ^ 4) = 0 := by
    have := hdd 1 2
    simp at this
    linear_combination this / 4
  refine ⟨ha, ?_⟩
  by_cases hc : c = 0
  · subst hc
    have : b ^ 4 = 0 := by linear_combination Ez
    exact ⟨pow_eq_zero_iff (by norm_num) |>.mp this, rfl⟩
  · exfalso
    have h3 : 3 * b ^ 2 - c ^ 4 = 0 := by
      rcases mul_eq_zero.mp Eyy with h | h
      · exact absurd h hc
      · exact h
    rcases mul_eq_zero.mp Eyz with hb | hb
    · subst hb
      have : c ^ 4 = 0 := by linarith
      exact hc (pow_eq_zero_iff (by norm_num) |>.mp this)
    · have hb2 : b ^ 2 = 0 := by nlinarith
      have hb0 : b = 0 := pow_eq_zero_iff two_ne_zero |>.mp hb2
      subst hb0
      have : c ^ 4 = 0 := by linarith
      exact hc (pow_eq_zero_iff (by norm_num) |>.mp this)

/-- Stage 1: `x₁ ∈ MC(I₁)`, so `H₁ = (x₁)` is of maximal contact. -/
theorem mem_derivativeIter_example12_z_H : x ∈ Ideal.derivativeIter ℚ 2 (Ideal.span {f1}) :=
  x_mem_derivativeIter_two_of_pderiv00 f1 (by simp [map_ofNat]; ring)

/-- Stage 1: `x₁ + 3y₁²z₁ − z₁⁵ ∈ MC(I₁)`, so `H₁'` is of maximal contact
(`∂²f₁/∂y² = 4(3y²z − z⁵)`). -/
theorem mem_derivativeIter_example12_z_H' :
    x + 3 * y ^ 2 * z - z ^ 5 ∈ Ideal.derivativeIter ℚ 2 (Ideal.span {f1}) := by
  have : x + 3 * y ^ 2 * z - z ^ 5 = x + (3 * y ^ 2 * z - z ^ 5) := by ring
  rw [this]
  exact Ideal.add_mem _ mem_derivativeIter_example12_z_H
    (mem_derivativeIter_two_of_pderiv11 f1 _ (by simp [map_ofNat]; ring))

/-! ### Stage 2 -/

/-- The second blow-up: `σ f₁ = z₂³ f₂` with `f₂ = x₂³ + z₂²(y₂² − z₂²)² + z₂¹⁵`, Kollár's display,
and the transforms of the equations of `H₁` and `H₁'`. -/
theorem transform_example12_zz :
    σz f1 = z ^ 3 * (x ^ 3 + z ^ 2 * (y ^ 2 - z ^ 2) ^ 2 + z ^ 15) ∧
      σz x = z * x ∧
      σz (x + 3 * y ^ 2 * z - z ^ 5) = z * (x + 3 * y ^ 2 * z ^ 2 - z ^ 4) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring

/-- `I₂ = (f₂)` has order exactly `3` at the origin. -/
theorem ord_zero_example12_zz :
    Ideal.span {f2} ≤ Ideal.span {x, y, z} ^ 3 ∧ ¬ Ideal.span {f2} ≤ Ideal.span {x, y, z} ^ 4 := by
  refine ⟨(Ideal.span_singleton_le_iff_mem _).mpr ?_, fun h => ?_⟩
  · have hv : y ^ 2 - z ^ 2 ∈ Ideal.span {x, y, z} ^ 2 :=
      Ideal.sub_mem _ (Ideal.pow_mem_pow y_mem_m0 2) (Ideal.pow_mem_pow z_mem_m0 2)
    refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.pow_mem_pow x_mem_m0 3) ?_) ?_
    · rw [sq (y ^ 2 - z ^ 2)]
      exact mem_pow_of_mem_pow_of_le (k := 2 + (2 + 2)) (by norm_num)
        (mul_mem_pow_add (Ideal.pow_mem_pow z_mem_m0 2) (mul_mem_pow_add hv hv))
    · exact mem_pow_of_mem_pow_of_le (by norm_num) (Ideal.pow_mem_pow z_mem_m0 15)
  · have := eval_pderiv3_eq_zero_of_mem_m3_zero_pow4 ((Ideal.span_singleton_le_iff_mem _).mp h)
      0 0 0
    simp at this

/-- Stage 2: the origin is the only `ℚ`-point of order `≥ 3`, from `∂²f₂/∂y² = 4z²(3y² − z²)`,
`∂²f₂/∂z²|_{z=0} = 2y⁴`, `∂²f₂/∂y∂z = 8yz(y² − 2z²)`. -/
theorem cosupport_example12_zz (a b c : ℚ)
    (h : Ideal.span {f2} ≤ Ideal.span {x - C a, y - C b, z - C c} ^ 3) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨-, -, hdd⟩ := vanish_of_mem_m3_cube a b c ((Ideal.span_singleton_le_iff_mem _).mp h)
  have ha : a = 0 := by simpa using hdd 0 0
  have Eyy : c ^ 2 * (3 * b ^ 2 - c ^ 2) = 0 := by
    have h : c = 0 ∨ (b ^ 2 - c ^ 2) * 2 + 2 * b * (2 * b) = 0 := by simpa using hdd 1 1
    rcases h with h | h
    · rw [h]; ring
    · linear_combination c ^ 2 * h / 2
  have Ezz : 2 * (b ^ 2 - c ^ 2) ^ 2 - 20 * c ^ 2 * (b ^ 2 - c ^ 2) + 8 * c ^ 4 +
      210 * c ^ 13 = 0 := by
    have := hdd 2 2
    simp at this
    linear_combination this
  have Eyz : b * c * (b ^ 2 - 2 * c ^ 2) = 0 := by
    have := hdd 1 2
    simp at this
    linear_combination this / 8
  refine ⟨ha, ?_⟩
  by_cases hc : c = 0
  · subst hc
    have : b ^ 4 = 0 := by linear_combination Ezz / 2
    exact ⟨pow_eq_zero_iff (by norm_num) |>.mp this, rfl⟩
  · exfalso
    have h3 : 3 * b ^ 2 - c ^ 2 = 0 := by
      rcases mul_eq_zero.mp Eyy with h | h
      · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hc
      · exact h
    rcases mul_eq_zero.mp Eyz with hb | hb
    · rcases mul_eq_zero.mp hb with hb | hb
      · subst hb
        have : c ^ 2 = 0 := by linarith
        exact hc (pow_eq_zero_iff two_ne_zero |>.mp this)
      · exact hc hb
    · have hb2 : b ^ 2 = 0 := by nlinarith
      have hb0 : b = 0 := pow_eq_zero_iff two_ne_zero |>.mp hb2
      subst hb0
      have : c ^ 2 = 0 := by linarith
      exact hc (pow_eq_zero_iff two_ne_zero |>.mp this)

/-- Stage 2: `x₂ ∈ MC(I₂)`, so `H₂ = (x₂)` is of maximal contact. -/
theorem mem_derivativeIter_example12_zz_H : x ∈ Ideal.derivativeIter ℚ 2 (Ideal.span {f2}) :=
  x_mem_derivativeIter_two_of_pderiv00 f2 (by simp [map_ofNat]; ring)

/-- Stage 2: `x₂ + 3y₂²z₂² − z₂⁴ ∈ MC(I₂)`, so `H₂'` is of maximal contact
(`∂²f₂/∂y² = 4(3y²z² − z⁴)`). -/
theorem mem_derivativeIter_example12_zz_H' :
    x + 3 * y ^ 2 * z ^ 2 - z ^ 4 ∈ Ideal.derivativeIter ℚ 2 (Ideal.span {f2}) := by
  have : x + 3 * y ^ 2 * z ^ 2 - z ^ 4 = x + (3 * y ^ 2 * z ^ 2 - z ^ 4) := by ring
  rw [this]
  exact Ideal.add_mem _ mem_derivativeIter_example12_zz_H
    (mem_derivativeIter_two_of_pderiv11 f2 _ (by simp [map_ofNat]; ring))

/-! ### Stage 3 -/

/-- The third blow-up: `σ f₂ = z₃³ f₃` with `f₃ = x₃³ + z₃³((y₃² − 1)² + z₃⁹)`, Kollár's
`x₃³ + z₃³(y₃² − 1)² + z₃¹²`, and the transforms of the equations of `H₂` and `H₂'`. -/
theorem transform_example12_zzz :
    σz f2 = z ^ 3 * (x ^ 3 + z ^ 3 * ((y ^ 2 - 1) ^ 2 + z ^ 9)) ∧
      σz x = z * x ∧
      σz (x + 3 * y ^ 2 * z ^ 2 - z ^ 4) = z * (x + z ^ 3 * (3 * y ^ 2 - 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring

/-- Stage 3: the locus of order `3` contains the line `x₃ = z₃ = 0`, `f₃ ∈ 𝔪_{(0,b,0)}³`. -/
theorem line_example12_zzz (b : ℚ) : Ideal.span {f3} ≤ Ideal.span {x, y - C b, z} ^ 3 := by
  refine (Ideal.span_singleton_le_iff_mem _).mpr ?_
  have hx : x ∈ Ideal.span {x, y - C b, z} := Ideal.subset_span (by simp)
  have hz : z ∈ Ideal.span {x, y - C b, z} := Ideal.subset_span (by simp)
  exact Ideal.add_mem _ (Ideal.pow_mem_pow hx 3) (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hz 3))

/-- Stage 3: the locus of order `3` lies in the line `x₃ = z₃ = 0`, from `∂²f₃/∂x² = 6x`,
`∂²f₃/∂y² = 4z³(3y² − 1)`, `∂f₃/∂y = 4z³y(y² − 1)`; a point with `z ≠ 0` would need `3y² = 1` and
`y(y² − 1) = 0`. -/
theorem line_example12_zzz' (a b c : ℚ)
    (h : Ideal.span {f3} ≤ Ideal.span {x - C a, y - C b, z - C c} ^ 3) : a = 0 ∧ c = 0 := by
  obtain ⟨-, hd, hdd⟩ := vanish_of_mem_m3_cube a b c ((Ideal.span_singleton_le_iff_mem _).mp h)
  have ha : a = 0 := by simpa using hdd 0 0
  have Eyy : c ^ 3 * (3 * b ^ 2 - 1) = 0 := by
    have h : c = 0 ∨ (b ^ 2 - 1) * 2 + 2 * b * (2 * b) = 0 := by simpa using hdd 1 1
    rcases h with h | h
    · rw [h]; ring
    · linear_combination c ^ 3 * h / 2
  have Ey : c ^ 3 * (b * (b ^ 2 - 1)) = 0 := by
    have h : c = 0 ∨ b ^ 2 - 1 = 0 ∨ b = 0 := by simpa using hd 1
    rcases h with h | h | h <;> rw [h] <;> ring
  refine ⟨ha, ?_⟩
  by_contra hc
  have hc3 : c ^ 3 ≠ 0 := pow_ne_zero 3 hc
  have h1 : 3 * b ^ 2 - 1 = 0 := by
    rcases mul_eq_zero.mp Eyy with h | h
    · exact absurd h hc3
    · exact h
  have h2 : b * (b ^ 2 - 1) = 0 := by
    rcases mul_eq_zero.mp Ey with h | h
    · exact absurd h hc3
    · exact h
  rcases mul_eq_zero.mp h2 with hb | hb
  · subst hb; norm_num at h1
  · have : b ^ 2 = 1 := by linarith
    rw [this] at h1; norm_num at h1

/-- Stage 3: `x₃ ∈ MC(I₃)`, so `H₃ = (x₃)` is of maximal contact. -/
theorem mem_derivativeIter_example12_zzz_H : x ∈ Ideal.derivativeIter ℚ 2 (Ideal.span {f3}) :=
  x_mem_derivativeIter_two_of_pderiv00 f3 (by simp [map_ofNat]; ring)

/-- Stage 3: `x₃ + z₃³(3y₃² − 1) ∈ MC(I₃)`, so `H₃'` is of maximal contact
(`∂²f₃/∂y² = 4z³(3y² − 1)`). -/
theorem mem_derivativeIter_example12_zzz_H' :
    x + z ^ 3 * (3 * y ^ 2 - 1) ∈ Ideal.derivativeIter ℚ 2 (Ideal.span {f3}) :=
  Ideal.add_mem _ mem_derivativeIter_example12_zzz_H
    (mem_derivativeIter_two_of_pderiv11 f3 _ (by simp [map_ofNat]; ring))

/-- The restriction at stage 3, `I₃|_{H₃} = (z₃³·g)` with `g = (y₃² − 1)² + z₃⁹` Kollár's equation
of the birational transform of `S ∩ H`; the marked transform carries the exceptional factor
`z₃³`. -/
theorem map_example12_zzz_H :
    (Ideal.span {f3}).map ρH = Ideal.span {zR ^ 3 * ((yR ^ 2 - 1) ^ 2 + zR ^ 9)} := by
  rw [Ideal.map_span, Set.image_singleton]
  simp only [map_sub, map_add, map_mul, map_pow, map_one, aeval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    zero_pow three_ne_zero, zero_add]

end Hironaka.Examples.Example12Stages
