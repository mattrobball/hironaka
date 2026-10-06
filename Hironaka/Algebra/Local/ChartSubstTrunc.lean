/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.ChartSubst

/-!
# The chart substitution and truncation

The chart substitution `xᵢ ↦ yᵢ y_r` (`i < r`), `xⱼ ↦ yⱼ` (`j ≥ r`) of
`Hironaka/Algebra/Local/ChartSubst.lean` raises degrees (`|σ(α)| ≥ |α|`), so the part of
`subst (chartSubst r) F` of degree `< n` depends only on the part of `F` of degree `< n`:
substituting the truncation `truncTotal n F` gives the same coefficients below degree `n`.  This
is the power-series input of the level-by-level identification of the completed chart map
(`Hironaka/Algebra/Local/ChartCompletion.lean`): both `φ̂(Φ(F))` and `Ψ(subst F)` are computed
modulo `𝔪ⁿ` from `truncTotal n F` alone.
-/

public section

namespace IsLocalRing

open MvPowerSeries

variable {n : ℕ} (r : Fin n) {K : Type*} [CommRing K]

/-- Below degree `N`, the chart substitution of `F` and of its truncation `truncTotal N F` agree
(the substitution does not lower degrees). -/
theorem coeff_subst_chartSubst_truncTotal (F : MvPowerSeries (Fin n) K) {N : ℕ}
    {β : Fin n →₀ ℕ} (hβ : β.degree < N) :
    coeff β (subst (chartSubst (K := K) r) (truncTotal N F : MvPowerSeries (Fin n) K)) =
      coeff β (subst (chartSubst (K := K) r) F) := by
  classical
  by_cases h : ∃ α, chartExp r α = β
  · obtain ⟨α, rfl⟩ := h
    rw [coeff_subst_chartSubst, coeff_subst_chartSubst, MvPolynomial.coeff_coe, coeff_truncTotal]
    exact lt_of_le_of_lt (by rw [degree_chartExp]; exact Nat.le_add_right _ _) hβ
  · push Not at h
    rw [coeff_subst_chartSubst_eq_zero r (fun d _ => h d),
      coeff_subst_chartSubst_eq_zero r (fun d _ => h d)]

end IsLocalRing
