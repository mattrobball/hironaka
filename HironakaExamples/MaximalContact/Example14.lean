/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Ideal.Span
import Hironaka.Scheme.IdealSheaf.Order.AffineSpace
import HironakaExamples.MaximalContact.Example82
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's Example 14 on the instance `m = 3`, `n = 2`: the mechanism of maximal contact

[Kol07, Example 14] is the motivating computation for hypersurfaces of maximal contact: for a
hypersurface `f = yᵐ + b₂(x)y^{m−2} + ⋯ + b_m(x) = 0` of multiplicity `m` at the origin, blown up
at the origin in the chart `x_i = x_i' x_n'`, `y = y' x_n'`, the transform is
`F = y'ᵐ + c₂ y'^{m−2} + ⋯ + c_m` with `c_i = π⁻¹_*(b_i, i)` the marked transforms (Kollár's (14.2)
and (14.6)); `∂^{m−1}F/∂y'^{m−1} = m!·y'` (14.3), so every point of multiplicity `≥ m` lies on the
transform of `H = (y = 0)` (Claim 14.4); the other `(m−1)`-st partials restricted to `y' = 0` are
`(m − i)!·∂^{i−1} c_i` (14.5); and a point of `y' = 0` has multiplicity `≥ m` iff `mult c_i ≥ i`
for all `i` (Claim 14.7). This file proves these statements on the instance `m = 3`, `n = 2`,
`b₂ = x₁² + x₂³`, `b₃ = x₁⁴ + x₁x₂² + x₂⁵`, in `ℚ[x₁, x₂, y]`, with (14.7) at every `ℚ`-point of
`y' = 0`.

Tools (from `HironakaExamples/MaximalContact/Example82.lean`): orders are `𝔪_p`-adic memberships;
non-memberships come from a partial derivative that does not vanish at the point
(`pderiv_mem_pow_of_mem_pow_succ`, `eval_eq_zero_of_mem_span`); the (14.7) equivalence uses that
the restriction `ρ : y' ↦ 0` maps `𝔪_p^k` into itself and that `∂_{y'}` lowers the `𝔪_p`-adic
order by one. -/

public section

open MvPolynomial

namespace Hironaka.Examples

section ExampleFourteen

/-- Kollár's `x₁ = X 0` in `ℚ[x₁, x₂, y]`. -/
local notation "x₁" => (X 0 : MvPolynomial (Fin 3) ℚ)
/-- Kollár's `x₂ = X 1` in `ℚ[x₁, x₂, y]`. -/
local notation "x₂" => (X 1 : MvPolynomial (Fin 3) ℚ)
/-- Kollár's `y = X 2` in `ℚ[x₁, x₂, y]`. -/
local notation "y" => (X 2 : MvPolynomial (Fin 3) ℚ)
/-- The chart `x₁ = x₁'x₂'`, `x₂ = x₂'`, `y = y'x₂'` (pivot `x₂`), as a substitution. -/
local notation "σ'" => (aeval ![X 0 * X 1, X 1, X 2 * X 1] :
  MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 3) ℚ)
/-- Restriction to `y' = 0`, as a substitution. -/
local notation "ρ" =>
  (aeval ![X 0, X 1, 0] : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 3) ℚ)

/-- Kollár's (14.1) on the instance: `mult₀ f = 3`, `b₂ ∈ 𝔪₀²`, `b₃ ∈ 𝔪₀³`. -/
theorem mult_example14 :
    (y ^ 3 + (x₁ ^ 2 + x₂ ^ 3) * y + (x₁ ^ 4 + x₁ * x₂ ^ 2 + x₂ ^ 5) ∈ Ideal.span {x₁, x₂, y} ^ 3 ∧
        y ^ 3 + (x₁ ^ 2 + x₂ ^ 3) * y + (x₁ ^ 4 + x₁ * x₂ ^ 2 + x₂ ^ 5) ∉
          Ideal.span {x₁, x₂, y} ^ 4) ∧
      x₁ ^ 2 + x₂ ^ 3 ∈ Ideal.span {x₁, x₂, y} ^ 2 ∧
        x₁ ^ 4 + x₁ * x₂ ^ 2 + x₂ ^ 5 ∈ Ideal.span {x₁, x₂, y} ^ 3 := by
  have hb₃ : x₁ ^ 4 + x₁ * x₂ ^ 2 + x₂ ^ 5 ∈ Ideal.span {x₁, x₂, y} ^ 3 := by
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact mem_pow_of_mem_pow_of_le (k := 4) (by norm_num)
        (Ideal.pow_mem_pow Hironaka.Examples.x_mem_m0 4)
    · refine mem_pow_of_mem_pow_of_le (k := 1 + 2) le_rfl (mul_mem_pow_add ?_ ?_)
      · rw [pow_one]; exact Hironaka.Examples.x_mem_m0
      · exact Ideal.pow_mem_pow Hironaka.Examples.y_mem_m0 2
    · exact mem_pow_of_mem_pow_of_le (k := 5) (by norm_num)
        (Ideal.pow_mem_pow Hironaka.Examples.y_mem_m0 5)
  refine ⟨⟨?_, fun h => ?_⟩, ?_, hb₃⟩
  · refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.pow_mem_pow Hironaka.Examples.z_mem_m0 3) ?_) hb₃
    rw [add_mul]
    refine Ideal.add_mem _ ?_ ?_
    · refine mem_pow_of_mem_pow_of_le (k := 2 + 1) le_rfl
        (mul_mem_pow_add (Ideal.pow_mem_pow Hironaka.Examples.x_mem_m0 2) ?_)
      rw [pow_one]; exact Hironaka.Examples.z_mem_m0
    · refine mem_pow_of_mem_pow_of_le (k := 3 + 1) (by norm_num)
        (mul_mem_pow_add (Ideal.pow_mem_pow Hironaka.Examples.y_mem_m0 3) ?_)
      rw [pow_one]; exact Hironaka.Examples.z_mem_m0
  · have h1 := pderiv_mem_pow_of_mem_pow_succ 2 h
    have h2 := pderiv_mem_pow_of_mem_pow_succ 2 h1
    have h3 := pderiv_mem_pow_of_mem_pow_succ 2 (a := 1) h2
    rw [pow_one] at h3
    have := eval_eq_zero_of_mem_span (fun _ : Fin 3 => (0 : ℚ)) (by simp) h3
    simp [map_ofNat] at this
  · refine Ideal.add_mem _ (Ideal.pow_mem_pow Hironaka.Examples.x_mem_m0 2) ?_
    exact mem_pow_of_mem_pow_of_le (k := 3) (by norm_num)
      (Ideal.pow_mem_pow Hironaka.Examples.y_mem_m0 3)

/-- Kollár's (14.2) with (14.6): the chart transforms `σ' f = x₂'³·F`, `σ' b₂ = x₂'²·c₂`,
`σ' b₃ = x₂'³·c₃`. -/
theorem transform_example14 :
    σ' (y ^ 3 + (x₁ ^ 2 + x₂ ^ 3) * y + (x₁ ^ 4 + x₁ * x₂ ^ 2 + x₂ ^ 5)) =
        x₂ ^ 3 * (y ^ 3 + (x₁ ^ 2 + x₂) * y + (x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2)) ∧
      σ' (x₁ ^ 2 + x₂ ^ 3) = x₂ ^ 2 * (x₁ ^ 2 + x₂) ∧
        σ' (x₁ ^ 4 + x₁ * x₂ ^ 2 + x₂ ^ 5) = x₂ ^ 3 * (x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [map_add, map_mul, map_pow, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring

/-- Kollár's (14.3): `∂²F/∂y'² = 3!·y'`. -/
theorem pderiv_y_y_example14 :
    pderiv 2 (pderiv 2 (y ^ 3 + (x₁ ^ 2 + x₂) * y + (x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2))) = 6 * y := by
  simp
  ring

/-- Kollár's Claim 14.4 on the instance: a `ℚ`-point of multiplicity `≥ 3` of `F` lies on
`y' = 0`. -/
theorem eq_zero_of_mem_pow_example14 (a₁ a₂ a₃ : ℚ)
    (h : y ^ 3 + (x₁ ^ 2 + x₂) * y + (x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2) ∈
      Ideal.span {x₁ - C a₁, x₂ - C a₂, y - C a₃} ^ 3) :
    a₃ = 0 := by
  have h1 := pderiv_mem_pow_of_mem_pow_succ 2 h
  have h2 := pderiv_mem_pow_of_mem_pow_succ 2 (a := 1) h1
  rw [pow_one, pderiv_y_y_example14] at h2
  have := eval_eq_zero_of_mem_span (![a₁, a₂, a₃] : Fin 3 → ℚ) (by simp) h2
  simpa using this

/-- Kollár's (14.5): the mixed second partials of `F` restricted to `y' = 0` are `∂c₂/∂x'_j` and
`∂²c₃/∂x'_j∂x'_k`. -/
theorem pderiv_mixed_example14 :
    (ρ (pderiv 0 (pderiv 2 (y ^ 3 + (x₁ ^ 2 + x₂) * y + (x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2)))) =
          pderiv 0 (x₁ ^ 2 + x₂) ∧
        ρ (pderiv 1 (pderiv 2 (y ^ 3 + (x₁ ^ 2 + x₂) * y + (x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2)))) =
          pderiv 1 (x₁ ^ 2 + x₂)) ∧
      (ρ (pderiv 0 (pderiv 0 (y ^ 3 + (x₁ ^ 2 + x₂) * y + (x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2)))) =
          pderiv 0 (pderiv 0 (x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2)) ∧
        ρ (pderiv 0 (pderiv 1 (y ^ 3 + (x₁ ^ 2 + x₂) * y + (x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2)))) =
          pderiv 0 (pderiv 1 (x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2)) ∧
        ρ (pderiv 1 (pderiv 1 (y ^ 3 + (x₁ ^ 2 + x₂) * y + (x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2)))) =
          pderiv 1 (pderiv 1 (x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2))) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> simp [map_ofNat]

/-- Kollár's Claim 14.7 on the instance, at every `ℚ`-point of `y' = 0`:
`mult_p F ≥ 3 ↔ mult_p c₂ ≥ 2 ∧ mult_p c₃ ≥ 3`. -/
theorem mem_pow_iff_example14 (a₁ a₂ : ℚ) :
    y ^ 3 + (x₁ ^ 2 + x₂) * y + (x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2) ∈
        Ideal.span {x₁ - C a₁, x₂ - C a₂, y} ^ 3 ↔
      x₁ ^ 2 + x₂ ∈ Ideal.span {x₁ - C a₁, x₂ - C a₂, y} ^ 2 ∧
        x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2 ∈ Ideal.span {x₁ - C a₁, x₂ - C a₂, y} ^ 3 := by
  set 𝔪 : Ideal (MvPolynomial (Fin 3) ℚ) := Ideal.span {x₁ - C a₁, x₂ - C a₂, y} with h𝔪
  have hy : y ∈ 𝔪 := Ideal.subset_span (by simp)
  -- the restriction `y' ↦ 0` maps `𝔪^k` into itself
  have hle : 𝔪.map ρ ≤ 𝔪 := by
    rw [Ideal.map_le_iff_le_comap, h𝔪, Ideal.span_le]
    rintro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rw [SetLike.mem_coe, Ideal.mem_comap]
    rcases hs with rfl | rfl | rfl
    · have e : ρ (x₁ - C a₁) = x₁ - C a₁ := by simp
      rw [e]; exact Ideal.subset_span (by simp)
    · have e : ρ (x₂ - C a₂) = x₂ - C a₂ := by simp
      rw [e]; exact Ideal.subset_span (by simp)
    · have e : ρ y = 0 := by simp
      rw [e]; exact Ideal.zero_mem _
  have hmap : ∀ (k : ℕ) (q : MvPolynomial (Fin 3) ℚ), q ∈ 𝔪 ^ k → ρ q ∈ 𝔪 ^ k := by
    intro k q hq
    have h1 : ρ q ∈ (𝔪 ^ k).map ρ := Ideal.mem_map_of_mem _ hq
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono hle k h1
  have hρF : ρ (y ^ 3 + (x₁ ^ 2 + x₂) * y + (x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2)) =
      x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2 := by
    simp
  have hρF' : ρ (pderiv 2 (y ^ 3 + (x₁ ^ 2 + x₂) * y + (x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2))) =
      x₁ ^ 2 + x₂ := by
    simp
  constructor
  · intro hF
    refine ⟨?_, ?_⟩
    · have := hmap 2 _ (pderiv_mem_pow_of_mem_pow_succ 2 hF)
      rwa [hρF'] at this
    · have := hmap 3 _ hF
      rwa [hρF] at this
  · rintro ⟨hc₂, hc₃⟩
    refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.pow_mem_pow hy 3) ?_) hc₃
    refine mem_pow_of_mem_pow_of_le (k := 2 + 1) le_rfl (mul_mem_pow_add hc₂ ?_)
    rw [pow_one]; exact hy

/-- At the origin of the chart, `F`, `c₂`, `c₃` have multiplicity `< 2`. -/
theorem mult_example14_origin :
    y ^ 3 + (x₁ ^ 2 + x₂) * y + (x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2) ∉ Ideal.span {x₁, x₂, y} ^ 2 ∧
      x₁ ^ 2 + x₂ ∉ Ideal.span {x₁, x₂, y} ^ 2 ∧
        x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2 ∉ Ideal.span {x₁, x₂, y} ^ 2 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h1 := pderiv_mem_pow_of_mem_pow_succ 0 (a := 1) h
    rw [pow_one] at h1
    have := eval_eq_zero_of_mem_span (fun _ : Fin 3 => (0 : ℚ)) (by simp) h1
    norm_num at this
  · have h1 := pderiv_mem_pow_of_mem_pow_succ 1 (a := 1) h
    rw [pow_one] at h1
    have := eval_eq_zero_of_mem_span (fun _ : Fin 3 => (0 : ℚ)) (by simp) h1
    norm_num at this
  · have h1 := pderiv_mem_pow_of_mem_pow_succ 0 (a := 1) h
    rw [pow_one] at h1
    have := eval_eq_zero_of_mem_span (fun _ : Fin 3 => (0 : ℚ)) (by simp) h1
    norm_num at this

/-- At the point `(0, 1, 0)` of the chart, `F(p) = c₃(p) = 1`. -/
theorem mult_example14_point :
    y ^ 3 + (x₁ ^ 2 + x₂) * y + (x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2) ∉ Ideal.span {x₁, x₂ - 1, y} ∧
      x₁ ^ 4 * x₂ + x₁ + x₂ ^ 2 ∉ Ideal.span {x₁, x₂ - 1, y} := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := eval_eq_zero_of_mem_span (![0, 1, 0] : Fin 3 → ℚ) (by simp) h
    simp at this
  · have := eval_eq_zero_of_mem_span (![0, 1, 0] : Fin 3 → ℚ) (by simp) h
    simp at this

end ExampleFourteen

end Hironaka.Examples
