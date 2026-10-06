/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.ConvNorm
public import Hironaka.Analytic.Weierstrass.Exponents
import Hironaka.Analytic.Rueckert.WeierstrassPolynomial
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic.Positivity.Finset

/-!
# Monic divisors of a Weierstrass polynomial are Weierstrass polynomials

A Weierstrass polynomial `W = X^d + ∑ c_j X^{d-1-j}` over `Conv K m` with `c_j(0) = 0` reduces to
`X^d` under the residue map `convResidue : Conv K m → K` (`map_weierstrassPolynomial`). A monic
divisor `Q` of `W` reduces to a monic divisor `Q̄` of `X^d` in `K[X]`; comparing trailing degrees
in `Q̄ · Q̄' = X^d` (`natTrailingDegree_mul`) forces the trailing degree of `Q̄` to equal its
degree, so all lower coefficients of `Q̄` vanish (`coeff_eq_zero_of_monic_dvd_X_pow`), i.e. the
lower coefficients of `Q` vanish at `0`: `Q` is the Weierstrass polynomial of its own coefficients
(`exists_weierstrassPolynomial_of_monic_dvd`). In the language of [GR65, Chapter II, §B]: since
`P(0, x_m) = x_m^d`, the restriction to the axis of each monic factor is a power of `x_m`. Used
for the irreducibility (`Irreducible.lean`) and the unique factorization (`UFD.lean`).

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

@[expose] public section

open Polynomial MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K]

variable {m : ℕ}

variable (K) in
/-- The residue map `Conv K m → K`, the constant coefficient. -/
noncomputable def convResidue : Conv K m →+* K :=
  (MvPowerSeries.constantCoeff).comp (Conv K m).val.toRingHom

@[simp] theorem convResidue_apply (c : Conv K m) :
    convResidue K c = constantCoeff (c : MvPowerSeries (Fin m) K) := rfl

/-- Ring maps act on Weierstrass polynomials coefficientwise. -/
theorem map_weierstrassPolynomial {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ)
    (c : Fin d → R) :
    (weierstrassPolynomial d c).map f = weierstrassPolynomial d fun j => f (c j) := by
  unfold weierstrassPolynomial
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C]

/-- A monic divisor of `X^d` over `K` has vanishing coefficients below its degree (compare
trailing degrees). -/
theorem coeff_eq_zero_of_monic_dvd_X_pow {a : Polynomial K} (ha : a.Monic) {d : ℕ}
    (hdvd : a ∣ Polynomial.X ^ d) {i : ℕ} (hi : i < a.natDegree) : a.coeff i = 0 := by
  obtain ⟨b, hb⟩ := hdvd
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hb
    exact pow_ne_zero d X_ne_zero hb
  have hbm : b.Monic := ha.of_mul_monic_left (hb ▸ monic_X_pow d)
  have hdeg : a.natDegree + b.natDegree = d := by
    rw [← ha.natDegree_mul hbm, ← hb, natDegree_X_pow]
  have htr : a.natTrailingDegree + b.natTrailingDegree = d := by
    rw [← natTrailingDegree_mul ha.ne_zero hb0, ← hb, natTrailingDegree_X_pow]
  have h1 := natTrailingDegree_le_natDegree a
  have h2 := natTrailingDegree_le_natDegree b
  by_contra hne
  have := natTrailingDegree_le_of_ne_zero hne
  omega

/-- If the residue of a monic `Q` divides `X^d`, the coefficients of `Q` below its degree vanish
at `0`. -/
theorem constantCoeff_coeff_eq_zero_of_map_dvd_X_pow {Q : Polynomial (Conv K m)} (hQ : Q.Monic)
    {d : ℕ} (hmap : Q.map (convResidue K) ∣ Polynomial.X ^ d) {i : ℕ} (hi : i < Q.natDegree) :
    MvPowerSeries.constantCoeff (Q.coeff i : MvPowerSeries (Fin m) K) = 0 := by
  have hi' : i < (Q.map (convResidue K)).natDegree := by rwa [hQ.natDegree_map]
  have := coeff_eq_zero_of_monic_dvd_X_pow (hQ.map _) hmap hi'
  rwa [Polynomial.coeff_map] at this

/-- A monic divisor in `(Conv K m)[X]` of a Weierstrass polynomial is a Weierstrass polynomial
(its lower coefficients vanish at `0`) [GR65, Chapter II, §B]. -/
theorem exists_weierstrassPolynomial_of_monic_dvd {d : ℕ} {c : Fin d → Conv K m}
    (hc : ∀ j, MvPowerSeries.constantCoeff (c j : MvPowerSeries (Fin m) K) = 0)
    {Q : Polynomial (Conv K m)} (hQ : Q.Monic) (hdvd : Q ∣ weierstrassPolynomial d c) :
    ∃ (d' : ℕ) (c' : Fin d' → Conv K m),
      (∀ j, MvPowerSeries.constantCoeff (c' j : MvPowerSeries (Fin m) K) = 0) ∧
      Q = weierstrassPolynomial d' c' := by
  refine ⟨Q.natDegree, fun j => Q.coeff (Q.natDegree - 1 - j), fun j => ?_,
    eq_weierstrassPolynomial_coeff_of_monic hQ⟩
  have hmap : Q.map (convResidue K) ∣ Polynomial.X ^ d := by
    have := Polynomial.map_dvd (convResidue K) hdvd
    rwa [map_weierstrassPolynomial,
      show (fun j => convResidue K (c j)) = fun _ : Fin d => (0 : K) from funext fun j => hc j,
      weierstrassPolynomial_zero] at this
  exact constantCoeff_coeff_eq_zero_of_map_dvd_X_pow hQ hmap (by omega)

/-- The product of two Weierstrass polynomials is a Weierstrass polynomial of degree the sum (its
residue is `X^{d₁} X^{d₂}`). -/
theorem exists_weierstrassPolynomial_mul {d₁ d₂ : ℕ} {c₁ : Fin d₁ → Conv K m}
    {c₂ : Fin d₂ → Conv K m}
    (hc₁ : ∀ j, MvPowerSeries.constantCoeff (c₁ j : MvPowerSeries (Fin m) K) = 0)
    (hc₂ : ∀ j, MvPowerSeries.constantCoeff (c₂ j : MvPowerSeries (Fin m) K) = 0) :
    ∃ c : Fin (d₁ + d₂) → Conv K m,
      (∀ j, MvPowerSeries.constantCoeff (c j : MvPowerSeries (Fin m) K) = 0) ∧
      weierstrassPolynomial d₁ c₁ * weierstrassPolynomial d₂ c₂ =
        weierstrassPolynomial (d₁ + d₂) c := by
  set Q := weierstrassPolynomial d₁ c₁ * weierstrassPolynomial d₂ c₂ with hQdef
  have hQ : Q.Monic := (monic_weierstrassPolynomial d₁ c₁).mul (monic_weierstrassPolynomial d₂ c₂)
  have hdeg : Q.natDegree = d₁ + d₂ := by
    rw [hQdef, (monic_weierstrassPolynomial d₁ c₁).natDegree_mul
      (monic_weierstrassPolynomial d₂ c₂), natDegree_weierstrassPolynomial,
      natDegree_weierstrassPolynomial]
  have hmap : Q.map (convResidue K) ∣ Polynomial.X ^ (d₁ + d₂) := by
    rw [hQdef, Polynomial.map_mul, map_weierstrassPolynomial, map_weierstrassPolynomial,
      show (fun j => convResidue K (c₁ j)) = fun _ : Fin d₁ => (0 : K) from funext fun j => hc₁ j,
      show (fun j => convResidue K (c₂ j)) = fun _ : Fin d₂ => (0 : K) from funext fun j => hc₂ j,
      weierstrassPolynomial_zero, weierstrassPolynomial_zero, ← pow_add]
  have hQW := eq_weierstrassPolynomial_coeff_of_monic hQ
  rw [hdeg] at hQW
  refine ⟨fun j => Q.coeff (d₁ + d₂ - 1 - j), fun j => ?_, hQW⟩
  exact constantCoeff_coeff_eq_zero_of_map_dvd_X_pow hQ hmap (by omega)

end Analytic
