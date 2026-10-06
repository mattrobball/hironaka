/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.ConvNorm
import Hironaka.Analytic.Weierstrass.Splitting
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.MetricSpace.Contracting

/-!
# The contraction step of Weierstrass division

For the normalized divisor `x_0^d - h` with `‖h‖_ρ ≤ ρ_0^d / 2`, dividing `f ∈ B_ρ` amounts to
solving `f + h q = x_0^d q + r` with `r` of `x_0`-degree `< d`; applying the splitting operators,
`q = Q(f) + Q(h q)` and `r = R(f + h q)`. The map `T q := Q f + Q (h q)` is a contraction of `B_ρ`
with constant `‖Q‖ ‖h‖ ≤ ρ_0^{-d} · ρ_0^d / 2 = 1/2` (the operator bounds of `Splitting.lean`),
so it has a fixed point `q` in the Banach space `B_ρ` (`ContractingWith.fixedPoint`), and
`f = q (x_0^d - h) + R(f + h q)`. This is the Banach-algebra proof of the Weierstrass division
theorem [GR71, Kapitel I]; `Division.lean` removes the normalization and the smallness
hypothesis.

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

public section

open scoped ENNReal NNReal
open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K]

variable {m : ℕ}

/-- The contraction step: for `g = x_0^d - h` with `‖h‖_ρ ≤ ρ_0^d / 2`, every `f ∈ B_ρ` is
`q g + r` with `q, r ∈ B_ρ` and `r` of `x_0`-degree `< d` [GR71, Kapitel I]. -/
theorem exists_division_of_convNorm_le (ρ : Radius (m + 1)) (d : ℕ)
    {f h : MvPowerSeries (Fin (m + 1)) K} (hf : ConvNorm ρ f ≠ ⊤)
    (hh : ConvNorm ρ h ≤ ((ρ 0 ^ d / 2 : ℝ≥0) : ℝ≥0∞)) :
    ∃ q r : MvPowerSeries (Fin (m + 1)) K, ConvNorm ρ q ≠ ⊤ ∧ ConvNorm ρ r ≠ ⊤ ∧
      (∀ ν : Fin (m + 1) →₀ ℕ, d ≤ ν 0 → coeff ν r = 0) ∧ f = q * (X 0 ^ d - h) + r := by
  obtain ⟨Q, R, hQ, hR, hQn, hRn⟩ := exists_splitting_clm K ρ d
  have hhB : h ∈ BanachSeries K ρ := ne_top_of_le_ne_top ENNReal.coe_ne_top hh
  set F : BanachSeries K ρ := ⟨f, hf⟩ with hF
  set H : BanachSeries K ρ := ⟨h, hhB⟩ with hH
  have hHnorm : ‖H‖ ≤ (ρ 0 : ℝ) ^ d / 2 := by
    rw [BanachSeries.norm_def]
    have := ENNReal.toReal_mono ENNReal.coe_ne_top hh
    rwa [ENNReal.coe_toReal, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat] at this
  have hρ : (ρ 0 : ℝ) ≠ 0 := (NNReal.coe_pos.mpr (ρ.pos 0)).ne'
  have hkey : ((ρ 0 : ℝ)⁻¹) ^ d * ((ρ 0 : ℝ) ^ d / 2) = 1 / 2 := by
    rw [mul_div_assoc', ← mul_pow, inv_mul_cancel₀ hρ, one_pow]
  let T : BanachSeries K ρ → BanachSeries K ρ := fun q => Q F + Q (H * q)
  have hT : ContractingWith (1 / 2 : ℝ≥0) T := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : T x - T y = Q (H * (x - y)) := by
      simp only [T]
      rw [mul_sub, map_sub]
      abel
    rw [hsub]
    calc ‖Q (H * (x - y))‖ ≤ ‖Q‖ * ‖H * (x - y)‖ := Q.le_opNorm _
      _ ≤ ((ρ 0 : ℝ)⁻¹) ^ d * (‖H‖ * ‖x - y‖) :=
        mul_le_mul hQn (norm_mul_le H (x - y)) (norm_nonneg _) (by positivity)
      _ ≤ ((ρ 0 : ℝ)⁻¹) ^ d * (((ρ 0 : ℝ) ^ d / 2) * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hHnorm (norm_nonneg _))
          (by positivity)
      _ = ((1 / 2 : ℝ≥0) : ℝ) * ‖x - y‖ := by
        rw [← mul_assoc, hkey]
        push_cast
        ring
  obtain ⟨q, hq⟩ : ∃ q : BanachSeries K ρ, T q = q :=
    ⟨ContractingWith.fixedPoint T hT, hT.fixedPoint_isFixedPt⟩
  set qs : MvPowerSeries (Fin (m + 1)) K := (q : MvPowerSeries (Fin (m + 1)) K) with hqs
  have hq' : qs = wQ d (f + h * qs) := by
    have h1 := congrArg Subtype.val hq
    rw [Subalgebra.coe_add, hQ, hQ, Subalgebra.coe_mul] at h1
    rw [wQ_add]
    exact h1.symm
  have hmem : f + h * qs ∈ BanachSeries K ρ := add_mem hf (mul_mem hhB q.2)
  refine ⟨qs, wR d (f + h * qs), q.2, wR_mem_banachSeries ρ d ⟨_, hmem⟩, fun ν hν =>
    coeff_wR_of_le d _ hν, ?_⟩
  have hsplit := X_pow_mul_wQ_add_wR d (f + h * qs)
  rw [← hq'] at hsplit
  calc f = (f + h * qs) - h * qs := by ring
    _ = X 0 ^ d * qs + wR d (f + h * qs) - h * qs := by rw [hsplit]
    _ = qs * (X 0 ^ d - h) + wR d (f + h * qs) := by ring

end Analytic
