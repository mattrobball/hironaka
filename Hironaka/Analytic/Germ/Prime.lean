/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Germ.Base
public import Hironaka.Analytic.Germ.Coordinate
public import Mathlib.RingTheory.MvPowerSeries.Equiv
import Hironaka.Analytic.ConvSeries.Units
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.Tactic.Positivity.Finset

/-!
# Coordinate germs are prime

Restriction to the hyperplane `{x_k = 0}` is a ring homomorphism `resAt k` from series in `n + 1`
variables to series in `n` variables (a coordinate swap, Mathlib's `finSuccEquiv`, and the
constant coefficient in the split-off variable), and `resAt k f = 0` exactly when every monomial
of `f` free of `x_k` has zero coefficient (`x_k ∣ f`, Mathlib's `X_dvd_iff`). The target is a
domain, so `x_k ∣ F G` forces `x_k ∣ F` or `x_k ∣ G`, with convergent quotients by `divX`.
Hence `x_k`, which is not a unit (`not_isUnit_convX`), is prime in `Conv K n`. Not in the sources
as such: Bierstone and Milman use the local ring of germs as a domain in which the coordinates
are prime without comment [BM88, proof of Theorem 4.4, pp. 24–25].

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

@[expose] public section

open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K]

variable {n : ℕ}

variable (K) in
/-- Restriction to the hyperplane `{x_k = 0}`, as a ring homomorphism to the series in the other
variables. -/
noncomputable def resAt (k : Fin (n + 1)) :
    MvPowerSeries (Fin (n + 1)) K →+* MvPowerSeries (Fin n) K :=
  (PowerSeries.constantCoeff (R := MvPowerSeries (Fin n) K)).comp
    ((MvPowerSeries.finSuccEquiv K n).toRingHom.comp
      (MvPowerSeries.renameEquiv K (Equiv.swap 0 k)).toRingHom)

theorem coeff_resAt (k : Fin (n + 1)) (f : MvPowerSeries (Fin (n + 1)) K) (x : Fin n →₀ ℕ) :
    coeff x (resAt K k f) = coeff (Finsupp.embDomain (swapEmb k) (Finsupp.cons 0 x)) f := by
  change coeff x (PowerSeries.constantCoeff (MvPowerSeries.finSuccEquiv K n
    (MvPowerSeries.renameEquiv K (Equiv.swap 0 k) f))) = _
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_coeff_finSuccEquiv,
    MvPowerSeries.renameEquiv_apply]
  conv_lhs => rw [← embDomain_swapEmb_swapEmb k (Finsupp.cons 0 x)]
  exact coeff_embDomain_rename (swapEmb k) f _

/-- `resAt k f = 0` iff every monomial of `f` free of `x_k` has zero coefficient. -/
theorem resAt_eq_zero_iff (k : Fin (n + 1)) (f : MvPowerSeries (Fin (n + 1)) K) :
    resAt K k f = 0 ↔ ∀ ν : Fin (n + 1) →₀ ℕ, ν k = 0 → coeff ν f = 0 := by
  constructor
  · intro h ν hν
    set z := Finsupp.embDomain (swapEmb k) ν with hz
    have hz0 : z 0 = 0 := by rw [hz, embDomain_swapEmb_apply_zero, hν]
    have h1 := congrArg (coeff z.tail) h
    rw [coeff_resAt, map_zero, ← hz0, Finsupp.cons_tail, hz, embDomain_swapEmb_swapEmb] at h1
    exact h1
  · intro h
    ext x
    rw [coeff_resAt, map_zero]
    exact h _ (by rw [embDomain_swapEmb_apply_k, Finsupp.cons_zero])

/-- A coordinate is not a unit: its constant coefficient vanishes. -/
theorem not_isUnit_convX (k : Fin n) : ¬ IsUnit (convX K k) := by
  intro h
  unfold convX at h
  exact (isUnit_iff_constantCoeff_ne_zero (X_mem_conv k)).mp h (constantCoeff_X k)

/-- Coordinate germs are prime in `Conv K n`: restrict to `{x_k = 0}`, a domain, and divide the
factor that vanishes there by `x_k`. -/
theorem prime_convX (k : Fin n) : Prime (convX K k) := by
  cases n with
  | zero => exact k.elim0
  | succ n =>
    refine ⟨convX_ne_zero k, not_isUnit_convX k, fun F G hFG => ?_⟩
    obtain ⟨H, hH⟩ := hFG
    have h1 : resAt K k ((F * G : Conv K (n + 1)) : MvPowerSeries (Fin (n + 1)) K) = 0 := by
      rw [resAt_eq_zero_iff]
      intro ν hν
      have h2 : coeff ν ((F * G : Conv K (n + 1)) : MvPowerSeries (Fin (n + 1)) K) =
          coeff ν ((convX K k * H : Conv K (n + 1)) : MvPowerSeries (Fin (n + 1)) K) :=
        congrArg (fun z : Conv K (n + 1) => coeff ν (z : MvPowerSeries (Fin (n + 1)) K)) hH
      rw [h2, Subalgebra.coe_mul, coe_convX]
      exact (X_dvd_iff.mp (dvd_mul_right _ _)) ν hν
    rw [Subalgebra.coe_mul, map_mul, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact Or.inl (convX_dvd_of_coeff k ((resAt_eq_zero_iff k _).mp h1))
    · exact Or.inr (convX_dvd_of_coeff k ((resAt_eq_zero_iff k _).mp h1))

end Analytic
