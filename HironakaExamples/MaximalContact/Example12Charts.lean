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
import HironakaExamples.MaximalContact.Example11Charts
import HironakaExamples.MaximalContact.Example82
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's Example 12: `S = (x³ + (y² − z⁶)² + z²¹ = 0)`, `m = 3`

[Kol07, Example 12]: `I = (x³ + (y² − z⁶)² + z²¹) ⊂ ℚ[x, y, z]`, `m = 3`, `H = (x)`, and a second
hypersurface of maximal contact `H' = (x + 3y² − z⁶)`. Computed exactly:

* `MC(I) = D²(I) = (x, y³, y²z⁴, yz⁵, 3y² − z⁶)`; `I` has order exactly `3` at the origin, its
  only `ℚ`-point of order `≥ 3`; `x`, `x + 3y² − z⁶ ∈ MC(I)`;
* `I|_H = ((y² − z⁶)² + z²¹)`, Kollár's trace "of multiplicity 4", and
  `I|_{H'} = ((z⁶ − 3y²)³ + (y² − z⁶)² + z²¹)` have the origin as their only point of order `3`.

The three point blow-ups on the `z`-chart are in
`HironakaExamples/MaximalContact/Example12Stages.lean`. Orders at `ℚ`-points read the value and the
partials up to order two (`vanish_of_mem_m3_cube`); the equations are solved by cases on which
factor vanishes.
-/

@[expose] public section

open MvPolynomial Hironaka.Examples

namespace Hironaka.Examples

section ToolsOrderFour

/-- `g ∈ 𝔪₀⁴` in `𝔸³` kills every third partial derivative of `g` at `0`. -/
theorem eval_pderiv3_eq_zero_of_mem_m3_zero_pow4 {g : MvPolynomial (Fin 3) ℚ}
    (hg : g ∈ Ideal.span {(X 0 : MvPolynomial (Fin 3) ℚ), X 1, X 2} ^ 4) (i j l : Fin 3) :
    eval ![(0 : ℚ), 0, 0] (pderiv l (pderiv j (pderiv i g))) = 0 := by
  have h : g ∈ Ideal.span {X 0 - C (0 : ℚ), X 1 - C (0 : ℚ), X 2 - C (0 : ℚ)} ^ 4 := by
    simpa using hg
  have h1 := pderiv_mem_pow_of_mem_pow_succ i (a := 3) h
  have h2 := pderiv_mem_pow_of_mem_pow_succ j (a := 2) h1
  have h3 := pderiv_mem_pow_of_mem_pow_succ l (a := 1) h2
  rw [pow_one] at h3
  exact eval_eq_zero_of_mem_m3 0 0 0 h3

/-- `g ∈ 𝔪₀⁵` in `𝔸²` kills every fourth partial derivative of `g` at `0`. -/
theorem eval_pderiv4_eq_zero_of_mem_m2_zero_pow5 {g : MvPolynomial (Fin 2) ℚ}
    (hg : g ∈ Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ), X 1} ^ 5) (i j l k : Fin 2) :
    eval ![(0 : ℚ), 0] (pderiv k (pderiv l (pderiv j (pderiv i g)))) = 0 := by
  have h : g ∈ Ideal.span {X 0 - C (0 : ℚ), X 1 - C (0 : ℚ)} ^ 5 := by simpa using hg
  have h1 := pderiv_mem_pow_of_mem_pow_succ i (a := 4) h
  have h2 := pderiv_mem_pow_of_mem_pow_succ j (a := 3) h1
  have h3 := pderiv_mem_pow_of_mem_pow_succ l (a := 2) h2
  have h4 := pderiv_mem_pow_of_mem_pow_succ k (a := 1) h3
  rw [pow_one] at h4
  exact eval_eq_zero_of_mem_m2 0 0 h4

end ToolsOrderFour

namespace Example12Charts

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


/-- A partial derivative of a member of an ideal lies in its derivative ideal (`Fin 3` form). -/
theorem hD {K : Ideal (MvPolynomial (Fin 3) ℚ)} (i : Fin 3) {g : MvPolynomial (Fin 3) ℚ}
    (hg : g ∈ K) : pderiv i g ∈ Ideal.derivative ℚ K :=
  pderiv_mem_derivative i hg

/-! ### `MC(I) = D²(I)` and the cosupport -/

/-- Kollár's `f = x³ + (y² − z⁶)² + z²¹`. -/
noncomputable abbrev f12 : MvPolynomial (Fin 3) ℚ := x ^ 3 + (y ^ 2 - z ^ 6) ^ 2 + z ^ 21
/-- The ideal `M = (x, y³, y²z⁴, yz⁵, 3y² − z⁶)`, to be shown equal to `MC(I) = D²(I)`. -/
noncomputable abbrev M12 : Ideal (MvPolynomial (Fin 3) ℚ) :=
  Ideal.span {x, y ^ 3, y ^ 2 * z ^ 4, y * z ^ 5, 3 * y ^ 2 - z ^ 6}

theorem x_mem_M12 : x ∈ M12 := Ideal.subset_span (by simp)
theorem y3_mem_M12 : y ^ 3 ∈ M12 := Ideal.subset_span (by simp)
theorem y2z4_mem_M12 : y ^ 2 * z ^ 4 ∈ M12 := Ideal.subset_span (by simp)
theorem yz5_mem_M12 : y * z ^ 5 ∈ M12 := Ideal.subset_span (by simp)
theorem A_mem_M12 : 3 * y ^ 2 - z ^ 6 ∈ M12 := Ideal.subset_span (by simp)

theorem pderiv0_f12 : pderiv 0 f12 = C 3 * x ^ 2 := by simp [map_ofNat]
theorem pderiv1_f12 : pderiv 1 f12 = 4 * y ^ 3 - 4 * y * z ^ 6 := by simp; ring
theorem pderiv2_f12 : pderiv 2 f12 = -12 * y ^ 2 * z ^ 5 + 12 * z ^ 11 + 21 * z ^ 20 := by
  simp; ring
theorem pderiv00_f12 : pderiv 0 (pderiv 0 f12) = C 6 * x := by simp [map_ofNat]; ring
theorem pderiv10_f12 : pderiv 1 (pderiv 0 f12) = 0 := by simp
theorem pderiv20_f12 : pderiv 2 (pderiv 0 f12) = 0 := by simp
theorem pderiv01_f12 : pderiv 0 (pderiv 1 f12) = 0 := by simp
theorem pderiv11_f12 : pderiv 1 (pderiv 1 f12) = C 4 * (3 * y ^ 2 - z ^ 6) := by
  simp [map_ofNat]; ring
theorem pderiv21_f12 : pderiv 2 (pderiv 1 f12) = -(C 24 * (y * z ^ 5)) := by simp [map_ofNat]; ring
theorem pderiv02_f12 : pderiv 0 (pderiv 2 f12) = 0 := by simp
theorem pderiv12_f12 : pderiv 1 (pderiv 2 f12) = -(C 24 * (y * z ^ 5)) := by simp [map_ofNat]; ring
theorem pderiv22_f12 : pderiv 2 (pderiv 2 f12) =
    -60 * y ^ 2 * z ^ 4 + 132 * z ^ 10 + 420 * z ^ 19 := by
  simp; ring

/-- The generators of `D²(I)` lie in `M`: `f` and its first and second partials. -/
theorem f12_mem_M12 : f12 ∈ M12 := by
  have : f12 = x ^ 2 * x + y * y ^ 3 + (z ^ 2 + 3 * z ^ 11) * (y ^ 2 * z ^ 4) -
      (z ^ 6 + z ^ 15) * (3 * y ^ 2 - z ^ 6) := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ x_mem_M12)
    (Ideal.mul_mem_left _ _ y3_mem_M12)) (Ideal.mul_mem_left _ _ y2z4_mem_M12))
    (Ideal.mul_mem_left _ _ A_mem_M12)

theorem pderiv1_f12_mem_M12 : pderiv 1 f12 ∈ M12 := by
  rw [pderiv1_f12]
  have : 4 * y ^ 3 - 4 * y * z ^ 6 = 4 * y ^ 3 - (4 * z) * (y * z ^ 5) := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ y3_mem_M12) (Ideal.mul_mem_left _ _ yz5_mem_M12)

theorem pderiv2_f12_mem_M12 : pderiv 2 f12 ∈ M12 := by
  rw [pderiv2_f12]
  have : -12 * y ^ 2 * z ^ 5 + 12 * z ^ 11 + 21 * z ^ 20 =
      (24 * z + 63 * z ^ 10) * (y ^ 2 * z ^ 4) - (12 * z ^ 5 + 21 * z ^ 14) * (3 * y ^ 2 - z ^ 6)
      := by
    ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ y2z4_mem_M12) (Ideal.mul_mem_left _ _ A_mem_M12)

theorem pderiv22_f12_mem_M12 : pderiv 2 (pderiv 2 f12) ∈ M12 := by
  rw [pderiv22_f12]
  have : -60 * y ^ 2 * z ^ 4 + 132 * z ^ 10 + 420 * z ^ 19 =
      (336 + 1260 * z ^ 9) * (y ^ 2 * z ^ 4) - (132 * z ^ 4 + 420 * z ^ 13) * (3 * y ^ 2 - z ^ 6)
      := by
    ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ y2z4_mem_M12) (Ideal.mul_mem_left _ _ A_mem_M12)

/-- `MC(I) = D²(I) = (x, y³, y²z⁴, yz⁵, 3y² − z⁶)`. `⊆`: `f`, its partials and second partials lie
in `M` (`z⁶ ≡ 3y²` modulo `3y² − z⁶` absorbs the pure powers of `z`); `⊇`: `6x = ∂²f/∂x²`,
`4(3y² − z⁶) = ∂²f/∂y²`, `−24yz⁵ = ∂²f/∂y∂z`, then `4y³ = ∂f/∂y + 4z·yz⁵` and
`336·y²z⁴ = ∂²f/∂z² + (132z⁴ + 420z¹³)(3y² − z⁶) − 1260yz⁸·yz⁵`. -/
theorem derivativeIter_example12 : Ideal.derivativeIter ℚ 2 (Ideal.span {f12}) = M12 := by
  change Ideal.derivativeIter ℚ (1 + 1) _ = _
  rw [Ideal.derivativeIter_succ, Ideal.derivativeIter_succ, Ideal.derivativeIter_zero]
  have hf : f12 ∈ Ideal.span {f12} := Ideal.mem_span_singleton_self _
  apply le_antisymm
  · rw [derivative_span_pderiv, derivative_span_pderiv, Ideal.span_le]
    rintro t (ht | ht)
    · rcases ht with ht | ht
      · rw [Set.mem_singleton_iff] at ht
        subst ht
        exact f12_mem_M12
      · simp only [Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff] at ht
        obtain ⟨i, g', rfl, rfl⟩ := ht
        match i with
        | 0 => rw [pderiv0_f12]; exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ x_mem_M12)
        | 1 => exact pderiv1_f12_mem_M12
        | 2 => exact pderiv2_f12_mem_M12
    · simp only [Set.mem_iUnion, Set.mem_image] at ht
      obtain ⟨j, t', ht', rfl⟩ := ht
      rcases ht' with ht' | ht'
      · rw [Set.mem_singleton_iff] at ht'
        subst ht'
        match j with
        | 0 => rw [pderiv0_f12]; exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ x_mem_M12)
        | 1 => exact pderiv1_f12_mem_M12
        | 2 => exact pderiv2_f12_mem_M12
      · simp only [Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff] at ht'
        obtain ⟨i, g', rfl, rfl⟩ := ht'
        match i, j with
        | 0, 0 => rw [pderiv00_f12]; exact Ideal.mul_mem_left _ _ x_mem_M12
        | 0, 1 => rw [pderiv10_f12]; exact Ideal.zero_mem _
        | 0, 2 => rw [pderiv20_f12]; exact Ideal.zero_mem _
        | 1, 0 => rw [pderiv01_f12]; exact Ideal.zero_mem _
        | 1, 1 => rw [pderiv11_f12]; exact Ideal.mul_mem_left _ _ A_mem_M12
        | 1, 2 => rw [pderiv21_f12]; exact neg_mem_iff.mpr (Ideal.mul_mem_left _ _ yz5_mem_M12)
        | 2, 0 => rw [pderiv02_f12]; exact Ideal.zero_mem _
        | 2, 1 => rw [pderiv12_f12]; exact neg_mem_iff.mpr (Ideal.mul_mem_left _ _ yz5_mem_M12)
        | 2, 2 => exact pderiv22_f12_mem_M12
  · set D2 := Ideal.derivative ℚ (Ideal.derivative ℚ (Ideal.span {f12})) with hD2
    have hle : Ideal.derivative ℚ (Ideal.span {f12}) ≤ D2 := Ideal.le_derivative _
    have hx : x ∈ D2 := by
      have h := hD 0 (hD 0 hf)
      rw [pderiv00_f12] at h
      exact mem_of_C_mul_mem (q := (6 : ℚ)) (by norm_num) h
    have hA : 3 * y ^ 2 - z ^ 6 ∈ D2 := by
      have h := hD 1 (hD 1 hf)
      rw [pderiv11_f12] at h
      exact mem_of_C_mul_mem (q := (4 : ℚ)) (by norm_num) h
    have hyz : y * z ^ 5 ∈ D2 := by
      have h := hD 2 (hD 1 hf)
      rw [pderiv21_f12, neg_mem_iff] at h
      exact mem_of_C_mul_mem (q := (24 : ℚ)) (by norm_num) h
    have hy3 : y ^ 3 ∈ D2 := by
      have h := hle (hD 1 hf)
      rw [pderiv1_f12] at h
      have e : C 4 * y ^ 3 = (4 * y ^ 3 - 4 * y * z ^ 6) + (4 * z) * (y * z ^ 5) := by
        simp only [map_ofNat]; ring
      exact mem_of_C_mul_mem (q := (4 : ℚ)) (by norm_num)
        (e ▸ Ideal.add_mem _ h (Ideal.mul_mem_left _ _ hyz))
    have hy2z4 : y ^ 2 * z ^ 4 ∈ D2 := by
      have h := hD 2 (hD 2 hf)
      rw [pderiv22_f12] at h
      have e : C 336 * (y ^ 2 * z ^ 4) = (-60 * y ^ 2 * z ^ 4 + 132 * z ^ 10 + 420 * z ^ 19) +
          (132 * z ^ 4 + 420 * z ^ 13) * (3 * y ^ 2 - z ^ 6) - (1260 * y * z ^ 8) * (y * z ^ 5) :=
          by
        simp only [map_ofNat]; ring
      exact mem_of_C_mul_mem (q := (336 : ℚ)) (by norm_num)
        (e ▸ Ideal.sub_mem _ (Ideal.add_mem _ h (Ideal.mul_mem_left _ _ hA))
          (Ideal.mul_mem_left _ _ hyz))
    rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact hx
    · exact hy3
    · exact hy2z4
    · exact hyz
    · exact hA

/-- `I` has order exactly `3` at the origin (`∂³f/∂x³ = 6`). -/
theorem ord_zero_example12 :
    Ideal.span {f12} ≤ Ideal.span {x, y, z} ^ 3 ∧ ¬ Ideal.span {f12} ≤ Ideal.span {x, y, z} ^ 4 :=
    by
  refine ⟨(Ideal.span_singleton_le_iff_mem _).mpr ?_, fun h => ?_⟩
  · have : f12 = x ^ 3 + (y * y ^ 3 - 2 * (y * y) * z ^ 6 + z ^ 9 * z ^ 3) + z ^ 18 * z ^ 3 := by
      ring
    rw [this]
    refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.pow_mem_pow x_mem_m0 3) ?_) ?_
    · refine Ideal.add_mem _ (Ideal.sub_mem _ ?_ ?_) ?_
      · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow y_mem_m0 3)
      · refine Ideal.mul_mem_left _ _ ?_
        exact mem_pow_of_mem_pow_of_le (by norm_num) (Ideal.pow_mem_pow z_mem_m0 6)
      · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow z_mem_m0 3)
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow z_mem_m0 3)
  · have := eval_pderiv3_eq_zero_of_mem_m3_zero_pow4 ((Ideal.span_singleton_le_iff_mem _).mp h)
      0 0 0
    simp at this

/-- `cosupp(I, 3) = {0}`: at a `ℚ`-point of order `≥ 3`, `∂²f/∂x² = 6x` gives `x = 0`,
`∂²f/∂y² = 12y² − 4z⁶` and `∂f/∂y = 4y(y² − z⁶)` give `y = 0`, then `z = 0`. -/
theorem cosupport_example12 (a b c : ℚ)
    (h : Ideal.span {f12} ≤ Ideal.span {x - C a, y - C b, z - C c} ^ 3) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨-, hd, hdd⟩ := vanish_of_mem_m3_cube a b c ((Ideal.span_singleton_le_iff_mem _).mp h)
  have ha : a = 0 := by
    have := hdd 0 0
    rw [pderiv00_f12] at this
    simpa using this
  have hyy : 3 * b ^ 2 - c ^ 6 = 0 := by
    have := hdd 1 1
    rw [pderiv11_f12] at this
    simpa using this
  have hy : b * (b ^ 2 - c ^ 6) = 0 := by
    have := hd 1
    rw [pderiv1_f12] at this
    simp at this
    linear_combination this / 4
  have hb : b = 0 := by
    rcases mul_eq_zero.mp hy with hb | hb
    · exact hb
    · have : b ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff two_ne_zero |>.mp this
  subst hb
  have hc : c ^ 6 = 0 := by linarith
  exact ⟨ha, rfl, pow_eq_zero_iff (by norm_num) |>.mp hc⟩

/-- `x ∈ MC(I)`: `H = (x)` is a hypersurface of maximal contact. -/
theorem mem_derivativeIter_example12_H : x ∈ Ideal.derivativeIter ℚ 2 (Ideal.span {f12}) := by
  rw [derivativeIter_example12]; exact x_mem_M12

/-- `x + 3y² − z⁶ ∈ MC(I)`: `H' = (x + 3y² − z⁶)` is a hypersurface of maximal contact. -/
theorem mem_derivativeIter_example12_H' :
    x + 3 * y ^ 2 - z ^ 6 ∈ Ideal.derivativeIter ℚ 2 (Ideal.span {f12}) := by
  rw [derivativeIter_example12]
  have : x + 3 * y ^ 2 - z ^ 6 = x + (3 * y ^ 2 - z ^ 6) := by ring
  rw [this]
  exact Ideal.add_mem _ x_mem_M12 A_mem_M12

/-! ### The restrictions -/

/-- `I|_H = ((y² − z⁶)² + z²¹)`. -/
theorem map_example12_H :
    (Ideal.span {f12}).map ρH = Ideal.span {(yR ^ 2 - zR ^ 6) ^ 2 + zR ^ 21} := by
  rw [Ideal.map_span, Set.image_singleton]
  simp only [map_sub, map_add, map_pow, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, zero_pow three_ne_zero, zero_add]

/-- Kollár's trace "has multiplicity 4": order exactly `4` at `0` (`∂⁴/∂y⁴ = 24`). -/
theorem ord_zero_map_example12_H :
    Ideal.span {(yR ^ 2 - zR ^ 6) ^ 2 + zR ^ 21} ≤ Ideal.span {yR, zR} ^ 4 ∧
      ¬ Ideal.span {(yR ^ 2 - zR ^ 6) ^ 2 + zR ^ 21} ≤ Ideal.span {yR, zR} ^ 5 := by
  refine ⟨(Ideal.span_singleton_le_iff_mem _).mpr ?_, fun h => ?_⟩
  · have : (yR ^ 2 - zR ^ 6) ^ 2 + zR ^ 21 =
        yR ^ 4 - (2 * zR ^ 4) * (yR ^ 2 * zR ^ 2) + zR ^ 8 * zR ^ 4 + zR ^ 17 * zR ^ 4 := by ring
    rw [this]
    refine Ideal.add_mem _ (Ideal.add_mem _
      (Ideal.sub_mem _ (Ideal.pow_mem_pow yR_mem_m0_fin2 4) ?_)
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow zR_mem_m0_fin2 4)))
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow zR_mem_m0_fin2 4))
    refine Ideal.mul_mem_left _ _ (mem_pow_of_mem_pow_of_le (k := 2 + 2) le_rfl
      (mul_mem_pow_add (Ideal.pow_mem_pow yR_mem_m0_fin2 2) (Ideal.pow_mem_pow zR_mem_m0_fin2 2)))
  · have := eval_pderiv4_eq_zero_of_mem_m2_zero_pow5 ((Ideal.span_singleton_le_iff_mem _).mp h)
      0 0 0 0
    norm_num at this

/-- `cosupp((I|_H, 3)) = {0}`: the trace lies in `𝔪₀³`, and the origin is its only point of order
`3` (`12y² − 4z⁶` and `4y(y² − z⁶)`). -/
theorem cosupport_map_example12_H :
    Ideal.span {(yR ^ 2 - zR ^ 6) ^ 2 + zR ^ 21} ≤ Ideal.span {yR, zR} ^ 3 ∧
    ∀ b c : ℚ, Ideal.span {(yR ^ 2 - zR ^ 6) ^ 2 + zR ^ 21} ≤ Ideal.span {yR - C b, zR - C c} ^ 3 →
      b = 0 ∧ c = 0 := by
  refine ⟨ord_zero_map_example12_H.1.trans (Ideal.pow_le_pow_right (by norm_num)), fun b c h => ?_⟩
  obtain ⟨-, hd, hdd⟩ := vanish_of_mem_m2_cube b c ((Ideal.span_singleton_le_iff_mem _).mp h)
  have hyy : 3 * b ^ 2 - c ^ 6 = 0 := by
    have := hdd 0 0
    simp at this
    linear_combination this / 2
  have hy : b * (b ^ 2 - c ^ 6) = 0 := by
    have h0 : b ^ 2 - c ^ 6 = 0 ∨ b = 0 := by simpa using hd 0
    rcases h0 with h | h <;> rw [h] <;> ring
  have hb : b = 0 := by
    rcases mul_eq_zero.mp hy with hb | hb
    · exact hb
    · have : b ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff two_ne_zero |>.mp this
  subst hb
  have hc : c ^ 6 = 0 := by linarith
  exact ⟨rfl, pow_eq_zero_iff (by norm_num) |>.mp hc⟩

/-- `I|_{H'} = ((z⁶ − 3y²)³ + (y² − z⁶)² + z²¹)` (`x ↦ z⁶ − 3y²`). -/
theorem map_example12_H' :
    (Ideal.span {f12}).map
        (aeval ![X 1 ^ 6 - 3 * X 0 ^ 2, X 0, X 1] :
          MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ) =
      Ideal.span {(zR ^ 6 - 3 * yR ^ 2) ^ 3 + (yR ^ 2 - zR ^ 6) ^ 2 + zR ^ 21} := by
  rw [Ideal.map_span, Set.image_singleton]
  simp only [map_sub, map_add, map_pow, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- `cosupp((I|_{H'}, 3)) = {0}`: with `u = z⁶ − 3y²`, `v = y² − z⁶`, the partials of
`g = u³ + v² + z²¹` are `∂_y g = y(4v − 18u²)`, `∂²_y g = 4v − 18u² + 8y² + 216uy²`,
`∂_z g = z⁵(18u² − 12v + 21z¹⁵)`, `∂_y∂_z g = −24yz⁵(9u + 1)`; the cases `z = 0`, `z ≠ 0 ∧ y = 0`
and `9u = −1` each force the origin or a contradiction over `ℚ`. -/
theorem cosupport_map_example12_H' :
    Ideal.span {(zR ^ 6 - 3 * yR ^ 2) ^ 3 + (yR ^ 2 - zR ^ 6) ^ 2 + zR ^ 21} ≤
        Ideal.span {yR, zR} ^ 3 ∧
    ∀ b c : ℚ, Ideal.span {(zR ^ 6 - 3 * yR ^ 2) ^ 3 + (yR ^ 2 - zR ^ 6) ^ 2 + zR ^ 21} ≤
      Ideal.span {yR - C b, zR - C c} ^ 3 → b = 0 ∧ c = 0 := by
  refine ⟨(Ideal.span_singleton_le_iff_mem _).mpr ?_, fun b c h => ?_⟩
  · have hu : zR ^ 6 - 3 * yR ^ 2 ∈ Ideal.span {yR, zR} ^ 2 := by
      refine Ideal.sub_mem _ ?_ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow yR_mem_m0_fin2 2))
      exact mem_pow_of_mem_pow_of_le (by norm_num) (Ideal.pow_mem_pow zR_mem_m0_fin2 6)
    have hv : yR ^ 2 - zR ^ 6 ∈ Ideal.span {yR, zR} ^ 2 := by
      refine Ideal.sub_mem _ (Ideal.pow_mem_pow yR_mem_m0_fin2 2) ?_
      exact mem_pow_of_mem_pow_of_le (by norm_num) (Ideal.pow_mem_pow zR_mem_m0_fin2 6)
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · have := Ideal.pow_mem_pow hu 3
      rw [← pow_mul] at this
      exact mem_pow_of_mem_pow_of_le (by norm_num) this
    · rw [sq]
      exact mem_pow_of_mem_pow_of_le (k := 2 + 2) (by norm_num) (mul_mem_pow_add hv hv)
    · exact mem_pow_of_mem_pow_of_le (by norm_num) (Ideal.pow_mem_pow zR_mem_m0_fin2 21)
  · obtain ⟨hv0, hd, hdd⟩ := vanish_of_mem_m2_cube b c ((Ideal.span_singleton_le_iff_mem _).mp h)
    -- the value and the partials at `(b, c)`, with `u = c⁶ − 3b²`, `v = b² − c⁶`
    have Ev : (c ^ 6 - 3 * b ^ 2) ^ 3 + (b ^ 2 - c ^ 6) ^ 2 + c ^ 21 = 0 := by
      have := hv0
      simp at this
      linear_combination this
    have Ey : b * (4 * (b ^ 2 - c ^ 6) - 18 * (c ^ 6 - 3 * b ^ 2) ^ 2) = 0 := by
      have := hd 0
      simp at this
      linear_combination this
    have Ez : c ^ 5 * (18 * (c ^ 6 - 3 * b ^ 2) ^ 2 - 12 * (b ^ 2 - c ^ 6) + 21 * c ^ 15) = 0 := by
      have := hd 1
      simp at this
      linear_combination this
    have Eyy : 4 * (b ^ 2 - c ^ 6) - 18 * (c ^ 6 - 3 * b ^ 2) ^ 2 + 8 * b ^ 2 +
        216 * (c ^ 6 - 3 * b ^ 2) * b ^ 2 = 0 := by
      have := hdd 0 0
      simp at this
      linear_combination this
    have Eyz : -24 * b * c ^ 5 * (9 * (c ^ 6 - 3 * b ^ 2) + 1) = 0 := by
      have := hdd 0 1
      simp at this
      linear_combination this
    have hc6 : 0 ≤ c ^ 6 := by positivity
    by_cases hc : c = 0
    · -- `z = 0`: `b³(4 − 162b²) = 0` and `b²(12 − 810b²) = 0` force `b = 0`
      subst hc
      refine ⟨?_, rfl⟩
      by_contra hb
      have h1 : 4 - 162 * b ^ 2 = 0 := by
        have : b ^ 3 * (4 - 162 * b ^ 2) = 0 := by linear_combination Ey
        rcases mul_eq_zero.mp this with h | h
        · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) hb
        · exact h
      have h2 : 12 - 810 * b ^ 2 = 0 := by
        have : b ^ 2 * (12 - 810 * b ^ 2) = 0 := by linear_combination Eyy
        rcases mul_eq_zero.mp this with h | h
        · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hb
        · exact h
      linarith
    · exfalso
      have hc5 : c ^ 5 ≠ 0 := pow_ne_zero 5 hc
      have h9 : b = 0 ∨ 9 * (c ^ 6 - 3 * b ^ 2) + 1 = 0 := by
        have : (-24 * b * c ^ 5) * (9 * (c ^ 6 - 3 * b ^ 2) + 1) = 0 := by linear_combination Eyz
        rcases mul_eq_zero.mp this with h | h
        · left
          rcases mul_eq_zero.mp h with h' | h'
          · rcases mul_eq_zero.mp h' with h'' | h''
            · norm_num at h''
            · exact h''
          · exact absurd h' hc5
        · exact Or.inr h
      rcases h9 with hb | hu
      · -- `y = 0`: with `t = c³`, `t³ + t² + 1 = 0` and `7t³ + 6t² + 4 = 0`, so `t² = −3`
        subst hb
        set t := c ^ 3 with ht
        have ht0 : t ≠ 0 := pow_ne_zero 3 hc
        have E1 : t ^ 3 + t ^ 2 + 1 = 0 := by
          have : t ^ 4 * (t ^ 3 + t ^ 2 + 1) = 0 := by
            rw [ht]; linear_combination Ev
          rcases mul_eq_zero.mp this with h | h
          · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) ht0
          · exact h
        have E2 : 7 * t ^ 3 + 6 * t ^ 2 + 4 = 0 := by
          have : 3 * c ^ 11 * (7 * t ^ 3 + 6 * t ^ 2 + 4) = 0 := by
            rw [ht]; linear_combination Ez
          rcases mul_eq_zero.mp this with h | h
          · rcases mul_eq_zero.mp h with h' | h'
            · norm_num at h'
            · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h') hc
          · exact h
        have : t ^ 2 + 3 = 0 := by linear_combination 7 * E1 - E2
        nlinarith [sq_nonneg t]
      · -- `9u = −1`: `c⁶ = 3b² − 1/9` and `b(2/9 − 8b²) = 0` leave `c⁶ < 0`
        have hu' : c ^ 6 = 3 * b ^ 2 - 1 / 9 := by linear_combination hu / 9
        have Ey' : b * (2 / 9 - 8 * b ^ 2) = 0 := by
          rw [hu'] at Ey
          linear_combination Ey
        rcases mul_eq_zero.mp Ey' with hb | hb
        · subst hb
          rw [hu'] at hc6
          norm_num at hc6
        · have hb2 : b ^ 2 = 1 / 36 := by linarith
          rw [hu', hb2] at hc6
          norm_num at hc6

end Example12Charts

end Hironaka.Examples
