/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.Eval
import Hironaka.Analytic.ConvSeries.Banach
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Tactic.Positivity.Finset

/-!
# Analyticity on the open polydisc, by rescaling, over `K = ℝ` or `ℂ`

`HasFPowerSeriesOnBall` lives on a sup-norm ball, while a series of finite `ρ`-norm converges on
the polydisc `{x | ∀ k, ‖x_k‖ < ρ_k}`. The two are reconciled by rescaling the coefficients:
`rescale ρ f = ∑_ν a_ν ρ^ν x^ν` has finite norm at the constant radius `1`, its function is
`evalSeries f (ρ · y)`, and the polydisc is the image of the unit ball under `y ↦ ρ · y`. So
`evalSeries f = evalSeries (rescale ρ f) ∘ (x ↦ x / ρ)` is analytic at every point of the open
polydisc, as the composition of a function analytic on the unit ball with a continuous linear
map. Over `ℝ` the polydisc is the open box `∏_k (-ρ_k, ρ_k)`. Standard [GR71, Kapitel I].


-/

@[expose] public section

open scoped ENNReal NNReal
open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K] {m : ℕ}

/-- The series with coefficients `a_ν ρ^ν`. -/
noncomputable def rescale (ρ : Fin m → ℝ≥0) (f : MvPowerSeries (Fin m) K) :
    MvPowerSeries (Fin m) K :=
  fun ν => coeff ν f * ((monomialEval ρ ν : ℝ) : K)

theorem coeff_rescale (ρ : Fin m → ℝ≥0) (f : MvPowerSeries (Fin m) K) (ν : Fin m →₀ ℕ) :
    coeff ν (rescale ρ f) = coeff ν f * ((monomialEval ρ ν : ℝ) : K) := rfl

/-- The rescaled series has, at the constant radius `1`, the norm of `f` at `ρ`. -/
theorem convNorm_rescale (ρ : Fin m → ℝ≥0) (f : MvPowerSeries (Fin m) K) :
    ConvNorm (fun _ => 1) (rescale ρ f) = ConvNorm ρ f := by
  unfold ConvNorm
  refine tsum_congr fun ν => ?_
  rw [coeff_rescale, monomialEval_one, ENNReal.coe_one, mul_one, enorm_mul, enorm_eq_nnnorm,
    enorm_eq_nnnorm, nnnorm_coe_monomialEval]

/-- The real weight `ρ^ν` in `K` is the product of the coerced entries. -/
theorem coe_monomialEval_eq_prod (ρ : Fin m → ℝ≥0) (ν : Fin m →₀ ℕ) :
    ((monomialEval ρ ν : ℝ) : K) = ν.prod fun k n => ((ρ k : ℝ) : K) ^ n := by
  rw [coe_monomialEval, Finsupp.prod, Finsupp.prod]
  push_cast
  rfl

theorem monomialEval_mul_left (ρ : Fin m → ℝ≥0) (y : Fin m → K) (ν : Fin m →₀ ℕ) :
    monomialEval (fun k => ((ρ k : ℝ) : K) * y k) ν
      = ((monomialEval ρ ν : ℝ) : K) * monomialEval y ν := by
  rw [coe_monomialEval_eq_prod, monomialEval, monomialEval, Finsupp.prod, Finsupp.prod,
    Finsupp.prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => mul_pow _ _ _

theorem evalSeries_rescale (ρ : Fin m → ℝ≥0) (f : MvPowerSeries (Fin m) K) (y : Fin m → K) :
    evalSeries (rescale ρ f) y = evalSeries f fun k => ((ρ k : ℝ) : K) * y k := by
  unfold evalSeries
  refine tsum_congr fun ν => ?_
  rw [coeff_rescale, monomialEval_mul_left]
  ring

/-- The function of a series of finite `ρ`-norm is analytic on the open polydisc
`{x | ∀ k, ‖x_k‖ < ρ_k}`. -/
theorem analyticOnNhd_evalSeries {ρ : Radius m} {f : MvPowerSeries (Fin m) K}
    (hf : ConvNorm ρ f ≠ ⊤) :
    AnalyticOnNhd K (evalSeries f) {x : Fin m → K | ∀ k, ‖x k‖ < ρ k} := by
  intro x hx
  have hres : ConvNorm (Radius.one m) (rescale ρ f) ≠ ⊤ := by
    change ConvNorm (fun _ => 1) (rescale ρ f) ≠ ⊤
    rw [convNorm_rescale]
    exact hf
  have hball := analyticOnNhd_evalSeries_ball hres one_pos fun k => le_rfl
  have hρk : ∀ k, (0 : ℝ) < ρ k := fun k => NNReal.coe_pos.mpr (ρ.pos k)
  have hρK : ∀ k, ((ρ k : ℝ) : K) ≠ 0 := fun k => by exact_mod_cast (hρk k).ne'
  let L : (Fin m → K) →L[K] (Fin m → K) :=
    ContinuousLinearMap.pi fun k => (((ρ k : ℝ) : K)⁻¹) • ContinuousLinearMap.proj k
  have hL : ∀ (z : Fin m → K) k, L z k = z k / ((ρ k : ℝ) : K) := fun z k => by
    simp [L, div_eq_inv_mul]
  have heq : evalSeries f = evalSeries (rescale ρ f) ∘ L := by
    funext z
    rw [Function.comp_apply, evalSeries_rescale]
    congr 1
    funext k
    rw [hL, mul_div_cancel₀ _ (hρK k)]
  rw [heq]
  refine (hball (L x) ?_).comp (L.analyticAt x)
  rw [mem_ball_zero_iff, NNReal.coe_one, pi_norm_lt_iff one_pos]
  intro k
  rw [hL, norm_div, RCLike.norm_ofReal, abs_of_pos (hρk k), div_lt_one (hρk k)]
  exact hx k

end Analytic

/-! ### The real case -/

open scoped ENNReal NNReal
open MvPowerSeries

namespace Analytic

variable {m : ℕ}

/-- The open box `∏_k (-ρ_k, ρ_k)` is the real norm-polydisc. -/
theorem pi_Ioo_eq_setOf_norm_lt (ρ : Radius m) :
    (Set.univ.pi fun k => Set.Ioo (-(ρ k : ℝ)) (ρ k)) = {x : Fin m → ℝ | ∀ k, ‖x k‖ < ρ k} := by
  ext x
  simp [Real.norm_eq_abs, abs_lt]

end Analytic
