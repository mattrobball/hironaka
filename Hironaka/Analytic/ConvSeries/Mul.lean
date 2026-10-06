/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.Eval
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Positivity.Finset

/-!
# Evaluation is multiplicative on the closed polydisc, over `K = ℝ` or `ℂ`

For two series of finite `ρ`-norm and `‖x_k‖ ≤ ρ_k`, the product of the two absolutely
convergent sums is the sum over all pairs of exponents (`tsum_mul_tsum_of_summable_norm`), which
regrouped by the sum of the two exponents (`hasSum_sum_antidiagonal`) is the sum of the
Cauchy-product coefficients `∑_{μ + μ' = ν} a_μ b_{μ'}` times `x^ν`, the coefficients of `f g`
(`MvPowerSeries.coeff_mul`). Standard [GR71, Kapitel I]; it is what makes evaluation a ring
homomorphism from the convergent series to the functions on a polydisc.


-/

public section

open scoped ENNReal NNReal
open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K] {m : ℕ}

/-- Evaluation is multiplicative on the closed polydisc. -/
theorem evalSeries_mul {ρ : Radius m} {f g : MvPowerSeries (Fin m) K} (hf : ConvNorm ρ f ≠ ⊤)
    (hg : ConvNorm ρ g ≠ ⊤) {x : Fin m → K} (hx : ∀ k, ‖x k‖ ≤ ρ k) :
    evalSeries (f * g) x = evalSeries f x * evalSeries g x := by
  classical
  have hsf := summable_norm_evalTerm hf hx
  have hsg := summable_norm_evalTerm hg hx
  -- the product of the two sums as a sum over pairs
  have hprod : HasSum (fun p : (Fin m →₀ ℕ) × (Fin m →₀ ℕ) =>
      (coeff p.1 f * monomialEval x p.1) * (coeff p.2 g * monomialEval x p.2))
      (evalSeries f x * evalSeries g x) := by
    rw [evalSeries, evalSeries, tsum_mul_tsum_of_summable_norm hsf hsg]
    exact (summable_mul_of_summable_norm hsf hsg).hasSum
  -- regrouped by the sum of the exponents, it is the evaluation of `f * g`
  have hreg := hasSum_sum_antidiagonal hprod
  have hterm : ∀ ν : Fin m →₀ ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
      (coeff p.1 f * monomialEval x p.1) * (coeff p.2 g * monomialEval x p.2)
      = coeff ν (f * g) * monomialEval x ν := by
    intro ν
    rw [MvPowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p.1 + p.2 = ν := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [← hp', monomialEval_add]
    ring
  simp_rw [hterm] at hreg
  exact hreg.tsum_eq

/-- Evaluation at `0` is the constant coefficient. -/
@[simp]
theorem evalSeries_zero_eq (f : MvPowerSeries (Fin m) K) : evalSeries f 0 = constantCoeff f := by
  classical
  unfold evalSeries
  rw [tsum_eq_single 0]
  · simp
  · intro ν hν
    have : monomialEval (0 : Fin m → K) ν = 0 := by
      obtain ⟨k, hk⟩ : ∃ k, ν k ≠ 0 := by
        by_contra h
        push Not at h
        exact hν (Finsupp.ext h)
      rw [monomialEval, Finsupp.prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hk) (by simp [hk])
    rw [this, mul_zero]

/-- The function of the series `1` is the constant `1`. -/
theorem evalSeries_one (x : Fin m → K) : evalSeries (1 : MvPowerSeries (Fin m) K) x = 1 := by
  classical
  unfold evalSeries
  rw [tsum_eq_single 0]
  · simp
  · intro ν hν
    simp [MvPowerSeries.coeff_one, hν]

end Analytic
