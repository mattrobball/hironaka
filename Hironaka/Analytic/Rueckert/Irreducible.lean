/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Rueckert.Basic
public import Hironaka.Analytic.Weierstrass.Axis
public import Hironaka.Analytic.Weierstrass.Exponents
import Hironaka.Analytic.ConvSeries.Order
import Hironaka.Analytic.ConvSeries.Units
import Hironaka.Analytic.Germ.Base
import Hironaka.Analytic.Rueckert.MonicDivisor
import Hironaka.Analytic.Rueckert.Quotient
import Hironaka.Analytic.Rueckert.WeierstrassPolynomial
import Hironaka.Analytic.Weierstrass.Preparation
import Hironaka.Analytic.Weierstrass.Regular
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Irreducible Weierstrass polynomials stay irreducible in `Conv K (m+1)`

Let `W ∈ (Conv K m)[X]` be a Weierstrass polynomial, irreducible there, and
`P = W(x_0) ∈ Conv K (m+1)`. `P` is not a unit (`P(0) = 0` since `d ≥ 1`). If `P = a b`, then
`a` and `b` are `x_0`-regular of orders `d₁ + d₂ = d` (the axis restriction is multiplicative,
`axis_mul`, and orders add: `isRegularIn_of_mul`); the convergent Weierstrass preparation writes
`a = u₁ W₁(x_0)`, `b = u₂ W₂(x_0)` with Weierstrass polynomials `W₁, W₂`
(`exists_preparation_conv`), so `P = (u₁ u₂) (W₁ W₂)(x_0)` with `W₁ W₂` Weierstrass
(`exists_weierstrassPolynomial_mul`); the uniqueness clause of the preparation
(`preparation_unique`) gives `W = W₁ W₂`, and irreducibility of `W` forces `W₁ = 1` or `W₂ = 1`,
i.e. `a` or `b` is a unit. This is a standard step of the theory of the ring of convergent series
[GR65, Chapter II, §B]; `UFD.lean` uses the preparation lemmas of this module.

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

public section

open MvPowerSeries Polynomial

namespace Analytic

variable {K : Type*} [RCLike K]

variable {m : ℕ}

section Regular

/-- `x_0`-regularity of order `d` is the order of the axis restriction `axis`: the printed
`f_a(0, …, 0, x_m) ∼ x_m^e` of [BM88, proof of Theorem 4.4, p. 24]. -/
theorem isRegularIn_iff_order_axis (g : MvPowerSeries (Fin (m + 1)) K) (d : ℕ) :
    IsRegularIn g d ↔ (axis g).order = d := by
  rw [isRegularIn_iff, MvPowerSeries.order_eq_nat]
  constructor
  · rintro ⟨hlt, hd⟩
    refine ⟨⟨Finsupp.single 0 d, ?_, ?_⟩, fun ν hν => ?_⟩
    · rwa [coeff_single_axis]
    · rw [degree_fin1, Finsupp.single_eq_same]
    · rw [Fin1.eq_single ν, coeff_single_axis]
      apply hlt
      rwa [degree_fin1] at hν
  · rintro ⟨⟨ν, hν, hνd⟩, hlt⟩
    refine ⟨fun k hk => ?_, ?_⟩
    · have := hlt (Finsupp.single 0 k) (by rw [degree_fin1, Finsupp.single_eq_same]; exact hk)
      rwa [coeff_single_axis] at this
    · rw [degree_fin1] at hνd
      rw [Fin1.eq_single ν, coeff_single_axis, hνd] at hν
      exact hν

/-- The factors of an `x_0`-regular series are `x_0`-regular, with orders adding up (`axis_mul`
and `order_mul`). -/
theorem isRegularIn_of_mul {a b : MvPowerSeries (Fin (m + 1)) K} {d : ℕ}
    (h : IsRegularIn (a * b) d) :
    ∃ d₁ d₂ : ℕ, d₁ + d₂ = d ∧ IsRegularIn a d₁ ∧ IsRegularIn b d₂ := by
  rw [isRegularIn_iff_order_axis, axis_mul, order_mul] at h
  have ha : (axis a).order ≠ ⊤ := fun ht => by
    rw [ht, top_add] at h
    exact ENat.top_ne_natCast d h
  have hb : (axis b).order ≠ ⊤ := fun ht => by
    rw [ht, add_top] at h
    exact ENat.top_ne_natCast d h
  refine ⟨(axis a).order.toNat, (axis b).order.toNat, ?_, ?_, ?_⟩
  · have := congrArg ENat.toNat h
    rwa [ENat.toNat_add ha hb, ENat.toNat_natCast] at this
  · rw [isRegularIn_iff_order_axis, ENat.natCast_toNat ha]
  · rw [isRegularIn_iff_order_axis, ENat.natCast_toNat hb]

end Regular

section Preparation

/-- The convergent Weierstrass preparation for elements of `Conv K (m+1)`: a regular `g` is a unit
times the evaluation of a Weierstrass polynomial over `Conv K m`. -/
theorem exists_preparation_conv {g : Conv K (m + 1)} {d : ℕ}
    (hreg : IsRegularIn (g : MvPowerSeries (Fin (m + 1)) K) d) :
    ∃ (u : Conv K (m + 1)) (c : Fin d → Conv K m), IsUnit u ∧
      (∀ j, constantCoeff (c j : MvPowerSeries (Fin m) K) = 0) ∧
      g = u * convPolyEval K (weierstrassPolynomial d c) := by
  obtain ⟨u, c, hu, hu0, hc, hg, -⟩ := exists_unique_weierstrassPreparation g.2 hreg
  refine ⟨⟨u, hu⟩, fun j => ⟨c j, (hc j).1⟩, (isUnit_iff_constantCoeff_ne_zero hu).mpr hu0,
    fun j => (hc j).2, ?_⟩
  apply Subtype.ext
  rw [Subalgebra.coe_mul, coe_convPolyEval_weierstrassPolynomial]
  exact hg

/-- Uniqueness of the preparation in `Conv K (m+1)`. -/
theorem preparation_unique {g : Conv K (m + 1)} {d : ℕ}
    (hreg : IsRegularIn (g : MvPowerSeries (Fin (m + 1)) K) d) {u u' : Conv K (m + 1)}
    {c c' : Fin d → Conv K m} (hc : ∀ j, constantCoeff (c j : MvPowerSeries (Fin m) K) = 0)
    (hc' : ∀ j, constantCoeff (c' j : MvPowerSeries (Fin m) K) = 0)
    (h : g = u * convPolyEval K (weierstrassPolynomial d c))
    (h' : g = u' * convPolyEval K (weierstrassPolynomial d c')) : u = u' ∧ c = c' := by
  obtain ⟨u₀, c₀, -, -, -, -, huniq⟩ := exists_unique_weierstrassPreparation g.2 hreg
  have e1 := huniq (u : MvPowerSeries (Fin (m + 1)) K) (fun j => (c j : MvPowerSeries (Fin m) K))
    hc (by rw [h, Subalgebra.coe_mul, coe_convPolyEval_weierstrassPolynomial])
  have e2 := huniq (u' : MvPowerSeries (Fin (m + 1)) K)
    (fun j => (c' j : MvPowerSeries (Fin m) K)) hc'
    (by rw [h', Subalgebra.coe_mul, coe_convPolyEval_weierstrassPolynomial])
  refine ⟨Subtype.ext (e1.1.trans e2.1.symm), funext fun j => Subtype.ext ?_⟩
  exact congrFun (e1.2.trans e2.2.symm) j

end Preparation

section Irreducible

/-- A Weierstrass polynomial irreducible in `(Conv K m)[X]` is irreducible in `Conv K (m+1)`
[GR65, Chapter II, §B]: regularity of the factors, preparation, uniqueness of preparation. -/
theorem irreducible_convPolyEval_of_irreducible {d : ℕ} {c : Fin d → Conv K m}
    (hc : ∀ j, constantCoeff (c j : MvPowerSeries (Fin m) K) = 0)
    (hirr : Irreducible (weierstrassPolynomial d c)) :
    Irreducible (convPolyEval K (weierstrassPolynomial d c)) := by
  set W : Polynomial (Conv K m) := weierstrassPolynomial d c with hW
  set P : Conv K (m + 1) := convPolyEval K W with hP
  have hreg : IsRegularIn (P : MvPowerSeries (Fin (m + 1)) K) d :=
    isRegularIn_convPolyEval_weierstrassPolynomial hc
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exfalso
      subst h0
      exact hirr.not_isUnit (by rw [hW, weierstrassPolynomial_zero_eq_one]; exact isUnit_one)
    · exact h0
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have h1 := ((isRegularIn_iff _ _).mp hreg).1 0 hd
    rw [Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply] at h1
    have hu' : IsUnit (⟨(P : MvPowerSeries (Fin (m + 1)) K), P.2⟩ : Conv K (m + 1)) := hu
    exact (isUnit_iff_constantCoeff_ne_zero P.2).mp hu' h1
  · have hab' : IsRegularIn ((a : MvPowerSeries (Fin (m + 1)) K) *
        (b : MvPowerSeries (Fin (m + 1)) K)) d := by
      rw [← Subalgebra.coe_mul, ← hab]
      exact hreg
    obtain ⟨d₁, d₂, hd12, hra, hrb⟩ := isRegularIn_of_mul hab'
    obtain ⟨u₁, c₁, hu₁, hc₁, ha⟩ := exists_preparation_conv hra
    obtain ⟨u₂, c₂, hu₂, hc₂, hb⟩ := exists_preparation_conv hrb
    obtain ⟨c₁₂, hc₁₂, hprod⟩ := exists_weierstrassPolynomial_mul hc₁ hc₂
    subst hd12
    have hP' : P = (u₁ * u₂) * convPolyEval K (weierstrassPolynomial (d₁ + d₂) c₁₂) := by
      rw [← hprod, map_mul, hab, ha, hb]
      ring
    have hP1 : P = 1 * convPolyEval K W := by rw [one_mul]
    obtain ⟨-, hcc⟩ := preparation_unique hreg hc hc₁₂ hP1 hP'
    have hWmul : W = weierstrassPolynomial d₁ c₁ * weierstrassPolynomial d₂ c₂ := by
      rw [hprod, hW, hcc]
    rcases hirr.isUnit_or_isUnit hWmul with h1 | h1
    · left
      have hd₁ : d₁ = 0 := by
        have := Polynomial.natDegree_eq_zero_of_isUnit h1
        rwa [natDegree_weierstrassPolynomial] at this
      subst hd₁
      rw [ha, weierstrassPolynomial_zero_eq_one, map_one, mul_one]
      exact hu₁
    · right
      have hd₂ : d₂ = 0 := by
        have := Polynomial.natDegree_eq_zero_of_isUnit h1
        rwa [natDegree_weierstrassPolynomial] at this
      subst hd₂
      rw [hb, weierstrassPolynomial_zero_eq_one, map_one, mul_one]
      exact hu₂

end Irreducible

end Analytic
