/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.ConvNorm
public import Hironaka.Analytic.Weierstrass.Basic
import Hironaka.Analytic.ConvSeries.Units
import Hironaka.Analytic.Weierstrass.AdicComplete
import Hironaka.Analytic.Weierstrass.Contraction
import Hironaka.Analytic.Weierstrass.Normalize
import Hironaka.Analytic.Weierstrass.Poly
import Hironaka.Analytic.Weierstrass.Regular
import Hironaka.Analytic.Weierstrass.Splitting

/-!
# Convergent Weierstrass division

The Weierstrass division theorem for convergent power series [GR65, Chapter II, §B],
[Nar66, Chapter II, Theorem 2]: for convergent `f`, `g` with `g` `x_0`-regular of order `d`, there
are unique convergent `q`, `r` with `f = q g + r` and `r` of `x_0`-degree `< d`. Existence follows
the Banach-algebra argument [GR71, Kapitel I]: normalize `g = E (x_0^d - h)` (`Normalize.lean`),
pick a radius vector where `f` and `h` converge, shrink its tail so that `‖h‖_ρ ≤ ρ_0^d / 2`
(`Splitting.lean`), divide by the contraction (`Contraction.lean`), `f = q₁ (x_0^d - h) + r`, and
put `q := q₁ E⁻¹`. Uniqueness: a convergent division datum is a formal Weierstrass division over
the tail ring (`isWeierstrassDivision_of_eq` in `Poly.lean`), and Mathlib's formal uniqueness
(`PowerSeries.IsWeierstrassDivision.elim`) applies. The preparation theorem of
`Preparation.lean` is the division of `x_0^d` by `g`.

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

public section

open scoped ENNReal NNReal
open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K]

variable {m : ℕ}

/-- Uniqueness of Weierstrass division data, from the formal theorem. -/
theorem weierstrassDivision_unique {f g q r q' r' : MvPowerSeries (Fin (m + 1)) K} {d : ℕ}
    (hreg : IsRegularIn g d)
    (hrd : ∀ ν : Fin (m + 1) →₀ ℕ, d ≤ ν 0 → coeff ν r = 0)
    (hrd' : ∀ ν : Fin (m + 1) →₀ ℕ, d ≤ ν 0 → coeff ν r' = 0)
    (hfq : f = q * g + r) (hfq' : f = q' * g + r') : q' = q ∧ r' = r := by
  have H := isWeierstrassDivision_of_eq hreg hrd hfq
  have H' := isWeierstrassDivision_of_eq hreg hrd' hfq'
  obtain ⟨hq, hr⟩ := H'.elim (map_residue_ne_zero_of_isRegularIn hreg) H
  refine ⟨(splitFirst K m).injective hq, (splitFirst K m).injective ?_⟩
  rw [splitFirst_eq_trunc hrd', splitFirst_eq_trunc hrd, hr]

/-- Convergent Weierstrass division: unique convergent `q`, `r` with `f = q g + r` and `r` of
`x_0`-degree `< d` [GR65, Chapter II, §B], [Nar66, Chapter II, Theorem 2]. -/
theorem exists_unique_weierstrassDivision {f g : MvPowerSeries (Fin (m + 1)) K} {d : ℕ}
    (hf : f ∈ Conv K (m + 1)) (hg : g ∈ Conv K (m + 1)) (hreg : IsRegularIn g d) :
    ∃ q r : MvPowerSeries (Fin (m + 1)) K, q ∈ Conv K (m + 1) ∧ r ∈ Conv K (m + 1) ∧
      (∀ ν : Fin (m + 1) →₀ ℕ, d ≤ ν 0 → coeff ν r = 0) ∧ f = q * g + r ∧
      ∀ q' r' : MvPowerSeries (Fin (m + 1)) K,
        (∀ ν : Fin (m + 1) →₀ ℕ, d ≤ ν 0 → coeff ν r' = 0) → f = q' * g + r' →
          q' = q ∧ r' = r := by
  obtain ⟨e, h, heConv, he0, hhConv, hT, hgE⟩ := hreg.exists_normalized hg
  have hE : (liftFirst e : MvPowerSeries (Fin (m + 1)) K) ∈ Conv K (m + 1) :=
    liftFirst_mem_conv heConv
  have hE0 : constantCoeff (liftFirst e : MvPowerSeries (Fin (m + 1)) K) ≠ 0 := by
    rw [constantCoeff_liftFirst]; exact he0
  obtain ⟨u, hu⟩ := (isUnit_iff_constantCoeff_ne_zero hE).mpr hE0
  obtain ⟨E', hE'Conv, hEE'⟩ : ∃ E' ∈ Conv K (m + 1), E' * liftFirst e = 1 := by
    refine ⟨((u⁻¹ : (Conv K (m + 1))ˣ) : Conv K (m + 1)), Subtype.mem _, ?_⟩
    have h1 := u.inv_mul
    rw [hu] at h1
    exact congrArg Subtype.val h1
  obtain ⟨ρf, hρf⟩ := hf
  obtain ⟨ρh, hρh⟩ := hhConv
  have hf1 : ConvNorm (ρf.min ρh) f ≠ ⊤ :=
    ne_top_of_le_ne_top hρf (ConvNorm_mono (ρf.min_le_left ρh) f)
  have hh1 : ConvNorm (ρf.min ρh) h ≠ ⊤ :=
    ne_top_of_le_ne_top hρh (ConvNorm_mono (ρf.min_le_right ρh) h)
  have hε : (0 : ℝ≥0∞) < (((ρf.min ρh) 0 ^ d / 2 : ℝ≥0) : ℝ≥0∞) := by
    have : (0 : ℝ≥0) < (ρf.min ρh) 0 ^ d / 2 := by
      have := (ρf.min ρh).pos 0
      positivity
    exact_mod_cast this
  obtain ⟨ρ, hρ0, hρle, hρh'⟩ := exists_radius_convNorm_le hh1 hT hε
  have hf2 : ConvNorm ρ f ≠ ⊤ := ne_top_of_le_ne_top hf1 (ConvNorm_mono hρle f)
  rw [← hρ0] at hρh'
  obtain ⟨q₁, r, hq₁, hr, hrdeg, hfq⟩ := exists_division_of_convNorm_le ρ d hf2 hρh'
  have hfqg : f = q₁ * E' * g + r := by
    rw [hgE]
    calc f = q₁ * (X 0 ^ d - h) + r := hfq
      _ = q₁ * (E' * liftFirst e) * (X 0 ^ d - h) + r := by rw [hEE', mul_one]
      _ = q₁ * E' * (liftFirst e * (X 0 ^ d - h)) + r := by ring
  refine ⟨q₁ * E', r, mul_mem ⟨ρ, hq₁⟩ hE'Conv, ⟨ρ, hr⟩, hrdeg, hfqg, fun q' r' hr' hfq' =>
    weierstrassDivision_unique hreg hrdeg hr' hfqg hfq'⟩

end Analytic
