/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Weierstrass.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Regularity in the distinguished variable: the elementary reading

`IsRegularIn g d` says that the image of `splitFirst K m g` in the residue field of the tail ring
`MvPowerSeries (Fin m) K` has order `d`. The `k`-th coefficient of that image is the residue of
the coefficient series of `x_0^k`, which vanishes iff that series has zero constant term, i.e. iff
the pure `x_0`-coefficient of `g` at `x_0^k` vanishes. So `g` is regular of order `d` iff its pure
`x_0`-coefficients vanish below degree `d` and not at degree `d`, that is,
`g(x_0, 0, …, 0) = x_0^d e(x_0)` with `e(0) ≠ 0`: the printed `f_a(0, …, 0, x_m) ∼ x_m^e` of
[BM88, proof of Theorem 4.4, p. 24]. In particular the residue image is nonzero, which is the
hypothesis of Mathlib's Weierstrass theorems. The module ends with the remark that a factorization
`f = u · P` with `u` nowhere zero on a polydisc gives `f` and `P` the same zero set there, the
printed item (3) of the same proof.

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

public section

open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K]

variable {m : ℕ}

/-- The residue of a series in the tail variables vanishes iff its constant coefficient does. -/
theorem residue_eq_zero_iff (a : MvPowerSeries (Fin m) K) :
    IsLocalRing.residue (MvPowerSeries (Fin m) K) a = 0 ↔ constantCoeff a = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]

/-- The constant coefficient of the `k`-th `x_0`-coefficient series is the pure `x_0`-coefficient
of `g` at `x_0^k`. -/
theorem constantCoeff_coeff_splitFirst (g : MvPowerSeries (Fin (m + 1)) K) (k : ℕ) :
    constantCoeff (PowerSeries.coeff k (splitFirst K m g)) = coeff (Finsupp.single 0 k) g := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_coeff_finSuccEquiv]
  have h : Finsupp.cons k (0 : Fin m →₀ ℕ) = Finsupp.single 0 k := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [Finsupp.cons_succ, Fin.succ_ne_zero]
  rw [h]

/-- The elementary reading of regularity: the pure `x_0`-coefficients of `g` vanish below degree
`d` and not at degree `d`. -/
theorem isRegularIn_iff (g : MvPowerSeries (Fin (m + 1)) K) (d : ℕ) :
    IsRegularIn g d ↔
      (∀ k < d, coeff (Finsupp.single 0 k) g = 0) ∧ coeff (Finsupp.single 0 d) g ≠ 0 := by
  unfold IsRegularIn
  rw [PowerSeries.order_eq_nat]
  simp only [PowerSeries.coeff_map, ne_eq, residue_eq_zero_iff, constantCoeff_coeff_splitFirst]
  exact and_comm

/-- Regularity gives Mathlib's Weierstrass hypothesis `g.map (IsLocalRing.residue A) ≠ 0`. -/
theorem map_residue_ne_zero_of_isRegularIn {g : MvPowerSeries (Fin (m + 1)) K} {d : ℕ}
    (hg : IsRegularIn g d) :
    (splitFirst K m g).map (IsLocalRing.residue (MvPowerSeries (Fin m) K)) ≠ 0 := by
  intro h0
  have := (PowerSeries.order_eq_nat.mp hg).1
  rw [h0, map_zero] at this
  exact this rfl

/-- Where `f = u · P` with `u` nonvanishing, the zero sets of `f` and `P` agree: the printed
`{f = 0} = {f_1 ⋯ f_r g = 0}` of [BM88, proof of Theorem 4.4, p. 24, item (3)]. -/
theorem zero_iff_of_unit_mul {ρ : Radius (m + 1)} {f u P : (Fin (m + 1) → K) → K}
    (hu : ∀ x ∈ polydisc K ρ, u x ≠ 0) (hfP : ∀ x ∈ polydisc K ρ, f x = u x * P x) :
    ∀ x ∈ polydisc K ρ, f x = 0 ↔ P x = 0 := fun x hx => by
  rw [hfP x hx, mul_eq_zero, or_iff_right (hu x hx)]

end Analytic
