/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Rueckert.Specialize
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Hironaka.Analytic.Rueckert.ZeroSet
public import Hironaka.Analytic.Weierstrass.Exponents
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Hironaka.Analytic.ConvSeries.Mul
import Hironaka.Analytic.ConvSeries.Rescale
import Hironaka.Analytic.ConvSeries.Units
import Hironaka.Analytic.Germ.CoordDiv
import Hironaka.Analytic.Rueckert.EvalTools
import Hironaka.Analytic.Rueckert.Irreducible
import Hironaka.Analytic.Rueckert.MonicDivisor
import Hironaka.Analytic.Rueckert.NullstellensatzReduction
import Hironaka.Analytic.Rueckert.Quotient
import Hironaka.Analytic.Rueckert.Slices
import Hironaka.Analytic.Rueckert.UFD
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Hypersurfaces: zeros of a square-free series

The hypersurface case of Rückert's Nullstellensatz [Fre17, Ch. I, 5.1], in its square-free form
over `ℂ`: if every zero of the nonzero square-free series `Q ∈ 𝒪_{m+1}` near `0` is a zero of
`P`, then `Q ∣ P` (`dvd_of_eventually_of_squarefree`). For a prime `Q` this is the first case of
the Nullstellensatz (`Nullstellensatz.lean`): a series vanishing on the zero-set germ of `(Q)`
lies in `(Q)` (`dvd_of_vanishesOn_of_prime`, `vanishingIdeal_span_singleton_le_of_prime`).

The proof follows Freitag's, with two replacements by Mathlib results:

* Freitag first reduces to the case where `Q` is a Weierstrass polynomial: a linear change of
  coordinates makes `Q` regular in `x_0` (`exists_substEquiv_isRegularIn`, `Subst.lean`; the
  hypothesis and the conclusion are invariant, `vanishesOn_image_substEquiv`,
  `squarefree_map_mulEquiv_iff`, `map_dvd_iff`), and the preparation theorem writes `Q = u W`
  with `u` a unit and `W` the series of a Weierstrass polynomial `W_p ∈ 𝒪_m[x_0]` of degree `d`
  (`exists_preparation_conv`); `u` does not vanish near `0`, so `V(Q) = V(W)` near `0`, and `W`
  is square-free with `Q`.
* The division theorem gives `P = A Q + B` with `B` a polynomial in `x_0` of degree `< d`:
  `exists_division_conv` and the slices (`eq_sum_convTail_sliceConv`, `Slices.lean`) give the
  remainder as the series of a polynomial `B` of degree `< d`; by assumption `W(z) = 0 ⇒ B(z) = 0`
  near `0`.
* `Q` is square-free in `𝒪_m[x_0]`, so its discriminant is nonzero: the Weierstrass polynomial
  `W_p` is square-free in `𝒪_m[x_0]` because its monic divisors are Weierstrass polynomials
  (`exists_weierstrassPolynomial_of_monic_dvd`) and a Weierstrass polynomial of positive degree
  is not a unit of `𝒪_{m+1}` (`squarefree_weierstrassPolynomial_of_squarefree`); the discriminant
  is replaced by the resultant `D = Res(W_p, W_p') ∈ 𝒪_m`, nonzero because `W_p` stays
  square-free, hence separable, over the fraction field of the integrally closed domain `𝒪_m`
  (`squarefree_map_fractionRing`, Mathlib's Gauss lemma `IsIntegrallyClosed.eq_map_mul_C_of_dvd`,
  `Monic.dvd_iff_fraction_map_dvd_fraction_map`, `PerfectField.separable_iff_squarefree`,
  `resultant_ne_zero`, `resultant_map_map`), with the Bezout identity `W_p U + W_p' V = C D`
  (Mathlib's `exists_mul_add_mul_eq_C_resultant`).
* On a dense subset of a small neighbourhood of `0` the specialization `Q_a` has `d` pairwise
  distinct small zeros: specializing the Bezout identity at a parameter `x` with `D(x) ≠ 0`
  (`Specialize.lean`) makes `W_p(x, ·)` coprime to its derivative, hence separable with `d`
  distinct roots over the algebraically closed `ℂ` (`eventually_isCoprime_specialize`,
  `card_roots_toFinset_specialize`); the roots are small by `norm_root_lt_of_monic`
  (`eventually_forall_root_norm_lt`).
* Hence `B_a` vanishes for these `a`, and `B = 0` by continuity: at such `x`, `B(x, ·)` of
  degree `< d` vanishes at the `d` roots, so it is `0`
  (`eq_zero_of_natDegree_lt_card_of_eval_eq_zero`); the coefficients of `B` vanish on the set
  `{D ≠ 0}`, which meets every open set near `0` (`exists_evalSeries_ne_zero_of_isOpen`), hence
  near `0` by continuity, hence are `0` by the identity theorem
  (`convPolyEval_dvd_of_eventually_of_squarefree`).
-/

@[expose] public section

open Filter Topology Polynomial

namespace Analytic

variable {K : Type*} [RCLike K] {m : ℕ}

/-- The germ ring has characteristic zero (a `K`-algebra). -/
instance instCharZeroConv : CharZero (Conv K m) :=
  charZero_of_injective_algebraMap (algebraMap K (Conv K m)).injective

/-- Square-freeness is invariant under a multiplicative equivalence. -/
theorem squarefree_map_mulEquiv_iff {R S : Type*} [CommMonoid R] [CommMonoid S] (σ : R ≃* S)
    (a : R) : Squarefree (σ a) ↔ Squarefree a := by
  constructor
  · intro h x hx
    have : σ x * σ x ∣ σ a := by rw [← map_mul]; exact map_dvd σ hx
    exact (MulEquiv.isUnit_map σ).mp (h _ this)
  · intro h y hy
    have : σ.symm y * σ.symm y ∣ a := by
      have := map_dvd σ.symm hy
      rwa [map_mul, MulEquiv.symm_apply_apply] at this
    exact (MulEquiv.isUnit_map σ.symm).mp (h _ this)

/-- A unit of the germ ring does not vanish near `0` (its inverse is convergent too). -/
theorem eventually_evalSeries_ne_zero_of_isUnit {n : ℕ} {u : Conv K n} (hu : IsUnit u) :
    ∀ᶠ x in 𝓝 (0 : Fin n → K), evalSeries (u : MvPowerSeries (Fin n) K) x ≠ 0 := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  filter_upwards [evalSeries_mul_eventually u.2 v.2] with x hx h0
  have : evalSeries ((u * v : Conv K n) : MvPowerSeries (Fin n) K) x = 1 := by
    rw [hv, Subalgebra.coe_one, evalSeries_one]
  rw [Subalgebra.coe_mul, hx, h0, zero_mul] at this
  exact zero_ne_one this

/-- The series of a Weierstrass polynomial of positive degree has constant coefficient `0`. -/
theorem constantCoeff_convPolyEval_weierstrassPolynomial {d : ℕ} {c : Fin d → Conv K m}
    (hc : ∀ j, MvPowerSeries.constantCoeff (c j : MvPowerSeries (Fin m) K) = 0) (hd : 0 < d) :
    MvPowerSeries.constantCoeff
      (convPolyEval K (weierstrassPolynomial d c) : MvPowerSeries (Fin (m + 1)) K) = 0 := by
  rw [coe_convPolyEval_weierstrassPolynomial, weierstrassPoly, map_add, map_pow,
    MvPowerSeries.constantCoeff_X, zero_pow hd.ne', zero_add, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_mul, map_pow, MvPowerSeries.constantCoeff_X]
  rcases Nat.eq_zero_or_pos (d - 1 - (j : ℕ)) with h0 | h0
  · rw [h0, pow_zero, mul_one, constantCoeff_liftTail, hc]
  · rw [zero_pow h0.ne', mul_zero]

/-- A Weierstrass polynomial whose series is square-free in `𝒪_{m+1}` is square-free in
`𝒪_m[x_0]`: its monic divisors are Weierstrass polynomials
(`exists_weierstrassPolynomial_of_monic_dvd`), and a Weierstrass polynomial of positive degree is
not a unit of `𝒪_{m+1}` (the square-freeness step of [Fre17, Ch. I, 5.1]). -/
theorem squarefree_weierstrassPolynomial_of_squarefree {d : ℕ} {c : Fin d → Conv K m}
    (hc : ∀ j, MvPowerSeries.constantCoeff (c j : MvPowerSeries (Fin m) K) = 0)
    (hsq : Squarefree (convPolyEval K (weierstrassPolynomial d c))) :
    Squarefree (weierstrassPolynomial d c) := by
  intro a ha
  have hadvd : a ∣ weierstrassPolynomial d c := (dvd_mul_right a a).trans ha
  obtain ⟨b, hb⟩ := hadvd
  have hmonic : (weierstrassPolynomial d c).Monic := monic_weierstrassPolynomial d c
  have hlead : a.leadingCoeff * b.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul, ← hb, hmonic.leadingCoeff]
  have hu : IsUnit a.leadingCoeff := isUnit_iff_exists.mpr ⟨_, hlead, by rwa [mul_comm]⟩
  obtain ⟨l, hl⟩ := hu.exists_right_inv
  have hlu : IsUnit l := isUnit_iff_exists.mpr ⟨_, by rwa [mul_comm], hl⟩
  obtain ⟨a', ha'⟩ : ∃ a' : Polynomial (Conv K m), a' = C l * a := ⟨_, rfl⟩
  have ha'monic : a'.Monic := by
    rw [Monic, ha', leadingCoeff_mul, leadingCoeff_C, mul_comm, hl]
  have haeq : a = C a.leadingCoeff * a' := by
    rw [ha', ← mul_assoc, ← C_mul, hl, C_1, one_mul]
  have ha'dvd : a' ∣ weierstrassPolynomial d c :=
    (Dvd.intro_left _ haeq.symm).trans ⟨b, hb⟩
  obtain ⟨d', c', hc', ha'eq⟩ := exists_weierstrassPolynomial_of_monic_dvd hc ha'monic ha'dvd
  have hφa : IsUnit (convPolyEval K a) := hsq _ (by rw [← map_mul]; exact map_dvd _ ha)
  have hφa' : IsUnit (convPolyEval K a') := by
    rw [ha', map_mul, convPolyEval_C]
    exact (hlu.map (convTail K)).mul hφa
  rcases Nat.eq_zero_or_pos d' with hd' | hd'
  · subst hd'
    have h1 : a' = 1 := by
      rw [ha'eq, weierstrassPolynomial, pow_zero, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    rw [haeq, h1, mul_one]
    exact isUnit_C.mpr hu
  · exfalso
    have h0 := constantCoeff_convPolyEval_weierstrassPolynomial hc' hd'
    rw [← ha'eq] at h0
    exact (isUnit_iff_constantCoeff_ne_zero (convPolyEval K a').2).mp
      (by rwa [Subtype.coe_eta]) h0

/-- A monic square-free polynomial over an integrally closed domain stays square-free over the
fraction field (Gauss's lemma: a monic factor over the fraction field descends). -/
theorem squarefree_map_fractionRing {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {W : R[X]} (hW : W.Monic) (hsq : Squarefree W) :
    Squarefree (W.map (algebraMap R (FractionRing R))) := by
  intro g hg
  have hgdvd : g ∣ W.map (algebraMap R (FractionRing R)) := (dvd_mul_right g g).trans hg
  by_contra hgu
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_dvd_iff] at hg
    exact (hW.map _).ne_zero hg
  obtain ⟨g', hg'⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (FractionRing R) hW hgdvd
  have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
  have hinj := IsFractionRing.injective R (FractionRing R)
  have h1 : (g'.map (algebraMap R (FractionRing R))).leadingCoeff * g.leadingCoeff =
      g.leadingCoeff := by
    conv_rhs => rw [← hg']
    rw [leadingCoeff_mul, leadingCoeff_C]
  have h2 : (g'.map (algebraMap R (FractionRing R))).leadingCoeff = 1 :=
    mul_right_cancel₀ hlc (by rw [h1, one_mul])
  have hg'monic : g'.Monic := by
    rw [Monic, ← hinj.eq_iff, ← leadingCoeff_map_of_injective hinj, h2, map_one]
  have hCu : IsUnit (C g.leadingCoeff : (FractionRing R)[X]) := isUnit_C.mpr hlc.isUnit
  have hgdvd' : g'.map (algebraMap R (FractionRing R)) ∣ g := by
    rw [← hg']
    exact dvd_mul_right _ _
  have hsqdvd : (g' * g').map (algebraMap R (FractionRing R)) ∣
      W.map (algebraMap R (FractionRing R)) := by
    rw [Polynomial.map_mul]
    exact (mul_dvd_mul hgdvd' hgdvd').trans hg
  rw [hW.dvd_iff_fraction_map_dvd_fraction_map (hg'monic.mul hg'monic)] at hsqdvd
  have hg'u : IsUnit g' := hsq _ hsqdvd
  apply hgu
  rw [← hg']
  exact (hg'u.map (mapRingHom (algebraMap R (FractionRing R)))).mul hCu

/-- A monic square-free polynomial over an integrally closed domain of characteristic zero is
separable over the fraction field, so its resultant with its derivative is nonzero (the nonzero
discriminant of [Fre17, Ch. I, 5.1], with the resultant of `W` and `W'` in place of the
discriminant). -/
theorem resultant_derivative_ne_zero_of_squarefree {R : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CharZero R] {W : R[X]} (hW : W.Monic) (hsq : Squarefree W) :
    resultant W (derivative W) ≠ 0 := by
  have hinj := IsFractionRing.injective R (FractionRing R)
  have : CharZero (FractionRing R) := charZero_of_injective_algebraMap hinj
  have hsqF := squarefree_map_fractionRing hW hsq
  have hsep : (W.map (algebraMap R (FractionRing R))).Separable :=
    PerfectField.separable_iff_squarefree.mpr hsqF
  have hcop : IsCoprime (W.map (algebraMap R (FractionRing R)))
      ((derivative W).map (algebraMap R (FractionRing R))) := by
    rw [← derivative_map]
    exact (separable_def _).mp hsep
  have h := resultant_ne_zero _ _ hcop
  rw [resultant_map_map, natDegree_map_eq_of_injective hinj,
    natDegree_map_eq_of_injective hinj] at h
  intro h0
  apply h
  rw [h0, map_zero]

/-! ### The analytic argument -/

/-- The Bezout identity `W U + W' V = C (Res(W, W'))` specialized at a parameter `x` near `0`: where
the resultant does not vanish, `W(x, ·)` is coprime to its derivative. -/
theorem eventually_isCoprime_specialize {W : Polynomial (Conv K m)} (hd : 0 < W.natDegree) :
    ∀ᶠ x in 𝓝 (0 : Fin m → K),
      evalSeries ((resultant W (derivative W) : Conv K m) : MvPowerSeries (Fin m) K) x ≠ 0 →
        IsCoprime (specialize W x) (derivative (specialize W x)) := by
  obtain ⟨p, q, -, -, hpq⟩ :=
    exists_mul_add_mul_eq_C_resultant W (derivative W) le_rfl le_rfl (Or.inl hd.ne')
  filter_upwards [specialize_add_eventually (W * p) (derivative W * q),
    specialize_mul_eventually W p, specialize_mul_eventually (derivative W) q,
    specialize_derivative_eventually W] with x h1 h2 h3 h4 hD
  have key : specialize W x * specialize p x + derivative (specialize W x) * specialize q x =
      C (evalSeries ((resultant W (derivative W) : Conv K m) : MvPowerSeries (Fin m) K) x) := by
    rw [← specialize_C, ← hpq, h1, h2, h3, h4]
  refine ⟨C (evalSeries ((resultant W (derivative W) : Conv K m) : MvPowerSeries (Fin m) K) x)⁻¹ *
    specialize p x,
    C (evalSeries ((resultant W (derivative W) : Conv K m) : MvPowerSeries (Fin m) K) x)⁻¹ *
      specialize q x, ?_⟩
  calc _ = C (evalSeries ((resultant W (derivative W) : Conv K m) : MvPowerSeries (Fin m) K) x)⁻¹ *
        (specialize W x * specialize p x + derivative (specialize W x) * specialize q x) := by ring
    _ = 1 := by rw [key, ← C_mul, inv_mul_cancel₀ hD, C_1]

/-- Over an algebraically closed field, a specialization coprime to its derivative has exactly
`deg W` distinct roots. -/
theorem card_roots_toFinset_specialize [IsAlgClosed K] {W : Polynomial (Conv K m)} (hW : W.Monic)
    {x : Fin m → K} (hcop : IsCoprime (specialize W x) (derivative (specialize W x))) :
    (specialize W x).roots.toFinset.card = W.natDegree := by
  classical
  rw [Multiset.toFinset_card_of_nodup (nodup_roots ((separable_def _).mpr hcop)),
    IsAlgClosed.card_roots_eq_natDegree, natDegree_specialize_of_monic hW]

/-- Near `0`, every root of the specialized Weierstrass polynomial has norm `< ε` (the small
zeros of [Fre17, Ch. I, 5.1]). -/
theorem eventually_forall_root_norm_lt {d : ℕ} {c : Fin d → Conv K m}
    (hc : ∀ j, MvPowerSeries.constantCoeff (c j : MvPowerSeries (Fin m) K) = 0) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ x in 𝓝 (0 : Fin m → K), ∀ t : K,
      (specialize (weierstrassPolynomial d c) x).eval t = 0 → ‖t‖ < ε := by
  have hW : (weierstrassPolynomial d c).Monic := monic_weierstrassPolynomial d c
  have hdeg : (weierstrassPolynomial d c).natDegree = d := natDegree_weierstrassPolynomial d c
  have hcoeff0 : ∀ i ∈ Finset.range d,
      evalSeries ((weierstrassPolynomial d c).coeff i : MvPowerSeries (Fin m) K) 0 = 0 := by
    intro i hi
    rw [evalSeries_zero_eq, coeff_weierstrassPolynomial_of_lt d c (Finset.mem_range.mp hi), hc]
  have htend : Tendsto (fun x : Fin m → K => ∑ i ∈ Finset.range d,
      ‖evalSeries ((weierstrassPolynomial d c).coeff i : MvPowerSeries (Fin m) K) x‖)
      (𝓝 0) (𝓝 0) := by
    have := tendsto_finsetSum (Finset.range d)
      (f := fun i (x : Fin m → K) =>
        ‖evalSeries ((weierstrassPolynomial d c).coeff i : MvPowerSeries (Fin m) K) x‖)
      (x := 𝓝 (0 : Fin m → K)) (a := fun _ => (0 : ℝ)) (fun i hi => by
        have hct :=
          (analyticAt_evalSeries_zero ((weierstrassPolynomial d c).coeff i).2).continuousAt
        have := hct.norm.tendsto
        rwa [hcoeff0 i hi, norm_zero] at this)
    simpa using this
  filter_upwards [htend.eventually_lt_const (pow_pos hε d)] with x hx t ht
  refine norm_root_lt_of_monic (specialize_monic hW x) hε hε1 ?_ ht
  rw [natDegree_specialize_of_monic hW, hdeg]
  simpa [coeff_specialize] using hx

/-- The hypersurface Nullstellensatz for a Weierstrass polynomial over `ℂ` [Fre17, Ch. I, 5.1]:
if the zero set of the square-free `W = convPolyEval (weierstrassPolynomial d c)` near `0` lies
in the zero set of `P`, then `W ∣ P`. -/
theorem convPolyEval_dvd_of_eventually_of_squarefree {d : ℕ} {c : Fin d → Conv ℂ m}
    (hc : ∀ j, MvPowerSeries.constantCoeff (c j : MvPowerSeries (Fin m) ℂ) = 0) (hd : 0 < d)
    (hsq : Squarefree (convPolyEval ℂ (weierstrassPolynomial d c))) {P : Conv ℂ (m + 1)}
    (h : ∀ᶠ z in 𝓝 (0 : Fin (m + 1) → ℂ),
      evalSeries (convPolyEval ℂ (weierstrassPolynomial d c) : MvPowerSeries (Fin (m + 1)) ℂ) z
        = 0 → evalSeries (P : MvPowerSeries (Fin (m + 1)) ℂ) z = 0) :
    convPolyEval ℂ (weierstrassPolynomial d c) ∣ P := by
  classical
  obtain ⟨Wp, hWp⟩ : ∃ Wp : Polynomial (Conv ℂ m), Wp = weierstrassPolynomial d c := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W : Conv ℂ (m + 1), W = convPolyEval ℂ Wp := ⟨_, rfl⟩
  rw [← hWp] at hsq h ⊢
  rw [← hWdef] at hsq h ⊢
  have hWmonic : Wp.Monic := by rw [hWp]; exact monic_weierstrassPolynomial d c
  have hWdeg : Wp.natDegree = d := by rw [hWp]; exact natDegree_weierstrassPolynomial d c
  have hreg : IsRegularIn (W : MvPowerSeries (Fin (m + 1)) ℂ) d := by
    rw [hWdef, hWp]; exact isRegularIn_convPolyEval_weierstrassPolynomial hc
  obtain ⟨q, r, hrd, hPqr⟩ := exists_division_conv (f := P) hreg
  obtain ⟨B, hBdef⟩ : ∃ B : Polynomial (Conv ℂ m),
      B = ∑ j : Fin d, C (sliceConv r (d - 1 - j)) * X ^ (d - 1 - (j : ℕ)) := ⟨_, rfl⟩
  have hrB : r = convPolyEval ℂ B := by
    rw [hBdef, map_sum]
    conv_lhs => rw [eq_sum_convTail_sliceConv hrd]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, convPolyEval_C, convPolyEval_X]
  have hBdeg : B.natDegree < d := by
    rw [hBdef]
    refine (natDegree_sum_le_of_forall_le _ _ fun j _ =>
      (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)).trans_lt (Nat.sub_one_lt hd.ne')
  suffices hB : B = 0 by
    refine ⟨q, ?_⟩
    rw [hPqr, hrB, hB, map_zero, add_zero, mul_comm]
  -- the hypothesis, for the remainder
  have hr : ∀ᶠ z in 𝓝 (0 : Fin (m + 1) → ℂ),
      evalSeries (W : MvPowerSeries (Fin (m + 1)) ℂ) z = 0 →
        evalSeries (r : MvPowerSeries (Fin (m + 1)) ℂ) z = 0 := by
    filter_upwards [h, evalSeries_add_eventually (q * W).2 r.2, evalSeries_mul_eventually q.2 W.2]
      with z hz h1 h2 hW0
    have hP := hz hW0
    rw [hPqr, Subalgebra.coe_add, h1, Subalgebra.coe_mul, h2, hW0, mul_zero, zero_add] at hP
    exact hP
  have hall : ∀ᶠ z in 𝓝 (0 : Fin (m + 1) → ℂ),
      (evalSeries (W : MvPowerSeries (Fin (m + 1)) ℂ) z = 0 →
        evalSeries (r : MvPowerSeries (Fin (m + 1)) ℂ) z = 0) ∧
      evalSeries (W : MvPowerSeries (Fin (m + 1)) ℂ) z = (specialize Wp (Fin.tail z)).eval (z 0) ∧
      evalSeries (r : MvPowerSeries (Fin (m + 1)) ℂ) z =
        (specialize B (Fin.tail z)).eval (z 0) := by
    filter_upwards [hr, evalSeries_convPolyEval_eq_eval_specialize Wp,
      evalSeries_convPolyEval_eq_eval_specialize B] with z h1 h2 h3
    exact ⟨h1, by rw [hWdef]; exact h2, by rw [hrB]; exact h3⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hall
  -- the resultant of the Weierstrass polynomial and its derivative
  obtain ⟨D, hDdef⟩ : ∃ D : Conv ℂ m, D = resultant Wp (derivative Wp) := ⟨_, rfl⟩
  have hD0 : D ≠ 0 := by
    rw [hDdef]
    refine resultant_derivative_ne_zero_of_squarefree hWmonic ?_
    rw [hWp]
    refine squarefree_weierstrassPolynomial_of_squarefree hc ?_
    rw [← hWp, ← hWdef]; exact hsq
  -- at parameters where the resultant does not vanish, the specialized remainder vanishes
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨ε, hε, hε1, hεδ⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε ≤ δ / 2 :=
    ⟨min (δ / 2) 1, lt_min hδ2 one_pos, min_le_right _ _, min_le_left _ _⟩
  have hgood : ∀ᶠ x in 𝓝 (0 : Fin m → ℂ),
      evalSeries (D : MvPowerSeries (Fin m) ℂ) x ≠ 0 →
        ∀ k, evalSeries (B.coeff k : MvPowerSeries (Fin m) ℂ) x = 0 := by
    have hroots := eventually_forall_root_norm_lt hc hε hε1
    rw [← hWp] at hroots
    filter_upwards [eventually_isCoprime_specialize (W := Wp) (by rw [hWdeg]; exact hd), hroots,
      Metric.eventually_nhds_iff.mpr ⟨δ / 2, hδ2, fun x hx => hx⟩] with x hcop hroots hxδ hDx k
    have hcop' := hcop (by rw [hDdef] at hDx; exact hDx)
    have hcard := card_roots_toFinset_specialize hWmonic hcop'
    have hzero : specialize B x = 0 := by
      refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero (specialize B x)
        (f := fun t : (specialize Wp x).roots.toFinset => (t : ℂ)) Subtype.val_injective
        (fun t => ?_) ?_
      · have ht : (specialize Wp x).eval (t : ℂ) = 0 := by
          have := t.2
          rw [Multiset.mem_toFinset, mem_roots (specialize_monic hWmonic x).ne_zero] at this
          exact this
        have htn : ‖(t : ℂ)‖ < ε := hroots (t : ℂ) ht
        obtain ⟨z, hz⟩ : ∃ z : Fin (m + 1) → ℂ, z = Fin.cons (t : ℂ) x := ⟨_, rfl⟩
        have hzball : dist z 0 < δ := by
          rw [dist_zero_right, pi_norm_lt_iff hδ]
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · rw [hz, Fin.cons_zero]
            exact htn.trans_le (hεδ.trans (by linarith))
          · rw [hz, Fin.cons_succ]
            have hx' : ‖x‖ < δ / 2 := by rwa [dist_zero_right] at hxδ
            exact ((pi_norm_lt_iff hδ2).mp hx' j).trans (by linarith)
        obtain ⟨h1, h2, h3⟩ := hball hzball
        have hW0 : evalSeries (W : MvPowerSeries (Fin (m + 1)) ℂ) z = 0 := by
          rw [h2, hz, Fin.tail_cons, Fin.cons_zero, ht]
        have := h1 hW0
        rw [h3, hz, Fin.tail_cons, Fin.cons_zero] at this
        exact this
      · rw [Fintype.card_coe, hcard, hWdeg]
        exact (natDegree_specialize_le B x).trans_lt hBdeg
    have := congrArg (fun p : Polynomial ℂ => p.coeff k) hzero
    simpa [coeff_specialize] using this
  -- density: each coefficient of `B` vanishes near `0`
  have hcoeff : ∀ k, evalSeries (B.coeff k : MvPowerSeries (Fin m) ℂ) =ᶠ[𝓝 (0 : Fin m → ℂ)] 0 := by
    intro k
    obtain ⟨δ₁, hδ₁, hgood'⟩ := Metric.eventually_nhds_iff.mp hgood
    obtain ⟨ρ, hρ⟩ := D.2
    obtain ⟨ρ', hρ'⟩ := (B.coeff k).2
    obtain ⟨U, hU⟩ : ∃ U : Set (Fin m → ℂ),
        U = Metric.ball (0 : Fin m → ℂ) δ₁ ∩ polydisc ℂ ρ ∩ polydisc ℂ ρ' := ⟨_, rfl⟩
    have hUopen : IsOpen U := by
      rw [hU]; exact (Metric.isOpen_ball.inter (isOpen_polydisc ρ)).inter (isOpen_polydisc ρ')
    have hU0 : (0 : Fin m → ℂ) ∈ U := by
      rw [hU]; exact ⟨⟨Metric.mem_ball_self hδ₁, zero_mem_polydisc ρ⟩, zero_mem_polydisc ρ'⟩
    filter_upwards [hUopen.mem_nhds hU0] with y hy
    by_contra hne
    have hcont : ContinuousOn (evalSeries (B.coeff k : MvPowerSeries (Fin m) ℂ)) U :=
      (analyticOnNhd_evalSeries hρ').continuousOn.mono (by rw [hU]; exact fun z hz => hz.2)
    have hVopen : IsOpen (U ∩ evalSeries (B.coeff k : MvPowerSeries (Fin m) ℂ) ⁻¹' {0}ᶜ) :=
      hcont.isOpen_inter_preimage hUopen isOpen_compl_singleton
    have hD0' : (D : MvPowerSeries (Fin m) ℂ) ≠ 0 := fun h0 => hD0 (Subtype.ext h0)
    obtain ⟨x, ⟨hxU, hx0⟩, hDx⟩ := exists_evalSeries_ne_zero_of_isOpen hρ hD0' hVopen
      ⟨y, hy, hne⟩ (by rw [hU]; exact fun z hz => hz.1.1.2)
    have hxδ : dist x 0 < δ₁ := by rw [hU] at hxU; exact Metric.mem_ball.mp hxU.1.1
    exact hx0 (hgood' hxδ hDx k)
  refine Polynomial.ext fun k => ?_
  rw [coeff_zero]
  exact Conv.ext_of_evalSeries_eventuallyEq (g := 0) (by
    filter_upwards [hcoeff k] with y hy
    rw [Subalgebra.coe_zero, evalSeries_zero]
    exact hy)

/-- The hypersurface Nullstellensatz over `ℂ` [Fre17, Ch. I, 5.1], square-free case: if every zero
of the nonzero square-free series `Q` near `0` is a zero of `P`, then `Q ∣ P`. -/
theorem dvd_of_eventually_of_squarefree {Q P : Conv ℂ (m + 1)} (hQ0 : Q ≠ 0) (hsq : Squarefree Q)
    (h : ∀ᶠ z in 𝓝 (0 : Fin (m + 1) → ℂ),
      evalSeries (Q : MvPowerSeries (Fin (m + 1)) ℂ) z = 0 →
        evalSeries (P : MvPowerSeries (Fin (m + 1)) ℂ) z = 0) : Q ∣ P := by
  classical
  obtain ⟨L, hreg⟩ := exists_substEquiv_isRegularIn hQ0
  have h' : ∀ᶠ z in 𝓝 (0 : Fin (m + 1) → ℂ),
      evalSeries ((substEquiv L Q : Conv ℂ (m + 1)) : MvPowerSeries (Fin (m + 1)) ℂ) z = 0 →
        evalSeries ((substEquiv L P : Conv ℂ (m + 1)) : MvPowerSeries (Fin (m + 1)) ℂ) z = 0 := by
    have hv : VanishesOn {Q} P := by
      unfold VanishesOn
      filter_upwards [h] with z hz hzQ
      exact hz (hzQ Q (Finset.mem_singleton_self Q))
    have := (vanishesOn_image_substEquiv L {Q} P).mpr hv
    rw [Finset.image_singleton] at this
    unfold VanishesOn at this
    filter_upwards [this] with z hz hzQ
    exact hz fun g hg => by rw [Finset.mem_singleton.mp hg]; exact hzQ
  have hsq' : Squarefree (substEquiv L Q) :=
    (squarefree_map_mulEquiv_iff (substEquiv L).toMulEquiv Q).mpr hsq
  suffices hdvd : substEquiv L Q ∣ substEquiv L P from (map_dvd_iff (substEquiv L)).mp hdvd
  obtain ⟨u, c, hu, hc, hQ'⟩ := exists_preparation_conv hreg
  rcases Nat.eq_zero_or_pos ((Q : MvPowerSeries (Fin (m + 1)) ℂ).order.toNat) with hd0 | hd
  · have h1 : weierstrassPolynomial _ c = 1 :=
      eq_one_of_monic_natDegree_zero (monic_weierstrassPolynomial _ c)
        (by rw [natDegree_weierstrassPolynomial]; exact hd0)
    have : IsUnit (substEquiv L Q) := by
      rw [hQ', h1, map_one, mul_one]; exact hu
    exact this.dvd
  · have hsqW : Squarefree (convPolyEval ℂ (weierstrassPolynomial _ c)) := by
      rw [hQ'] at hsq'; exact hsq'.of_mul_right
    have hW : ∀ᶠ z in 𝓝 (0 : Fin (m + 1) → ℂ),
        evalSeries (convPolyEval ℂ (weierstrassPolynomial _ c) : MvPowerSeries (Fin (m + 1)) ℂ) z
          = 0 →
        evalSeries ((substEquiv L P : Conv ℂ (m + 1)) : MvPowerSeries (Fin (m + 1)) ℂ) z = 0 := by
      filter_upwards [h', evalSeries_mul_eventually u.2
        (convPolyEval ℂ (weierstrassPolynomial _ c)).2] with z hz hmul hW0
      apply hz
      rw [hQ', Subalgebra.coe_mul, hmul, hW0, mul_zero]
    have := convPolyEval_dvd_of_eventually_of_squarefree hc hd hsqW hW
    rw [hQ']
    exact hu.mul_left_dvd.mpr this

/-- The hypersurface Nullstellensatz for a prime `Q` [Fre17, Ch. I, 5.1]: a series vanishing on
the zero-set germ of the prime `Q` is divisible by `Q`. -/
theorem dvd_of_vanishesOn_of_prime {Q f : Conv ℂ (m + 1)} (hQ : Prime Q) (hf : VanishesOn {Q} f) :
    Q ∣ f := by
  refine dvd_of_eventually_of_squarefree hQ.ne_zero hQ.irreducible.squarefree ?_
  unfold VanishesOn at hf
  filter_upwards [hf] with z hz hzQ
  exact hz fun g hg => by rw [Finset.mem_singleton.mp hg]; exact hzQ

/-- The Nullstellensatz for a principal prime ideal: `𝓘(V((Q))) ⊆ (Q)` for `Q` prime. -/
theorem vanishingIdeal_span_singleton_le_of_prime {Q : Conv ℂ (m + 1)} (hQ : Prime Q) :
    vanishingIdeal (Ideal.span {Q}) ≤ Ideal.span {Q} := fun f hf => by
  rw [mem_vanishingIdeal_iff (S := {Q}) (by rw [Finset.coe_singleton])] at hf
  exact Ideal.mem_span_singleton.mpr (dvd_of_vanishesOn_of_prime hQ hf)

end Analytic
