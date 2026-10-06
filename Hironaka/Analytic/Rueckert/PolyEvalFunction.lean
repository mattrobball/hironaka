/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Rueckert.Specialize
public import Hironaka.Analytic.Rueckert.Embed
import Hironaka.Analytic.Rueckert.Reexpansion
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Positivity.Finset

/-!
# The function of a polynomial in one coordinate with base coefficients

The relations of the local parametrization theorem ([GR84, Chapter 3, §1]; [Fre17, Ch. I, 8.2])
are elements `W(X_i) = ∑_k W_k(x_base) X_i^k` of `𝒪_n`: a polynomial `W ∈ 𝒪_d[T]` with its
coefficients embedded from the base along `e` and evaluated at the coordinate series `X_i`. Near
`0`, the function of such an element at a point `x` is the polynomial over `ℂ` obtained by
evaluating the coefficients at the base point `x ∘ e` (`specialize`, `Specialize.lean`),
evaluated at `x_i`. This is the bridge between the algebra of the normalization and the division
argument (elements of `𝒪_n`) and the analysis of the graph structure (functions on `ℂⁿ`), through
the function-level identities `evalSeries_conv_{add,mul,pow,sum}_eventually`.
-/

public section

open Polynomial Filter Topology

namespace Analytic

variable {K : Type*} [RCLike K] {n d : ℕ}

/-- Near `0`, the function of `W(X_i)` (coefficients embedded along `e`) at `x` is
`(specialize W (x ∘ e)).eval (x i)`. -/
theorem evalSeries_eval_map_convEmbed_eventually (e : Fin d ↪ Fin n) (i : Fin n)
    (W : Polynomial (Conv K d)) :
    evalSeries (((W.map (convEmbed K e).toRingHom).eval (convX K i) : Conv K n) :
        MvPowerSeries (Fin n) K) =ᶠ[𝓝 (0 : Fin n → K)]
      fun x => (specialize W (x ∘ e)).eval (x i) := by
  have hsum : ((W.map (convEmbed K e).toRingHom).eval (convX K i) : Conv K n) =
      ∑ k ∈ Finset.range (W.natDegree + 1), convEmbed K e (W.coeff k) * convX K i ^ k := by
    rw [eval_map, eval₂_eq_sum_range]
    rfl
  rw [hsum]
  refine (evalSeries_conv_sum_eventually _ _).trans ?_
  have hterm : ∀ k ∈ Finset.range (W.natDegree + 1),
      evalSeries ((convEmbed K e (W.coeff k) * convX K i ^ k : Conv K n) :
        MvPowerSeries (Fin n) K) =ᶠ[𝓝 (0 : Fin n → K)]
        fun x => evalSeries (W.coeff k : MvPowerSeries (Fin d) K) (x ∘ e) * x i ^ k := by
    intro k _
    filter_upwards [evalSeries_conv_mul_eventually (convEmbed K e (W.coeff k)) (convX K i ^ k),
      evalSeries_conv_pow_eventually (convX K i) k] with x h1 h2
    rw [h1, h2, evalSeries_convX, evalSeries_convEmbed]
  refine ((Filter.eventually_all_finset _).2 hterm).mono fun x hx => ?_
  dsimp only
  rw [eval_specialize]
  exact Finset.sum_congr rfl fun k hk => hx k hk

end Analytic
