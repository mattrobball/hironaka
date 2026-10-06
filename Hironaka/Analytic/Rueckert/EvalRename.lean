/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.Eval
public import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Positivity.Finset

/-!
# Evaluation of a series in a subset of the coordinates

A convergent series `f` in `d` variables embedded along `e : Fin d ↪ Fin n` (`convEmbed`,
`MvPowerSeries.rename e`) evaluates at `x : Fin n → K` to `f` evaluated at `x ∘ e`
(`evalSeries_rename`): the coefficient of `rename e f` at a monomial is that of `f` at its
preimage and vanishes off the image of `Finsupp.embDomain e`, and the monomial
`x^{embDomain e μ}` is `(x ∘ e)^μ`. Used for the upper semicontinuity of the dimension: the base
coefficients of a Noether normalization, read as functions on `Kⁿ`, depend only on the base
coordinates (`Parameters.lean`, `Reexpansion.lean`).
-/

public section

open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K] {d n : ℕ}

/-- The monomial `x^{e(μ)}` in the coordinates `e i` is the monomial `(x ∘ e)^μ`. -/
theorem monomialEval_embDomain (e : Fin d ↪ Fin n) (x : Fin n → K) (μ : Fin d →₀ ℕ) :
    monomialEval x (Finsupp.embDomain e μ) = monomialEval (x ∘ e) μ := by
  unfold monomialEval
  rw [Finsupp.prod_embDomain]
  rfl

/-- Evaluating the series `rename e f` in the coordinates `e i` at `x` is evaluating `f` at
`x ∘ e`: the sum over the monomials of `rename e f` is the sum over the monomials of `f`
(`coeff_embDomain_rename`, `coeff_rename_eq_zero`). -/
theorem evalSeries_rename (e : Fin d ↪ Fin n) (f : MvPowerSeries (Fin d) K) (x : Fin n → K) :
    evalSeries (rename e f) x = evalSeries f (x ∘ e) := by
  unfold evalSeries
  have hsupp : Function.support (fun ν : Fin n →₀ ℕ => coeff ν (rename e f) * monomialEval x ν) ⊆
      Set.range (Finsupp.embDomain (M := ℕ) e) := by
    intro ν hν
    by_contra hnot
    apply hν
    have : ν ∉ Set.range (Finsupp.mapDomain e) := by
      rintro ⟨μ, hμ⟩
      exact hnot ⟨μ, by rw [Finsupp.embDomain_eq_mapDomain, hμ]⟩
    change coeff ν (rename e f) * monomialEval x ν = 0
    rw [coeff_rename_eq_zero _ f this, zero_mul]
  rw [← (Finsupp.embDomain_injective (M := ℕ) e).tsum_eq hsupp]
  refine tsum_congr fun μ => ?_
  rw [coeff_embDomain_rename, monomialEval_embDomain]

end Analytic
