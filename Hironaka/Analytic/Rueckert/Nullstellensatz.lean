/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Rueckert.Basic
public import Hironaka.Analytic.Rueckert.ZeroSet
public import Hironaka.Analytic.Weierstrass.Exponents
public import Mathlib.Analysis.Complex.Basic
import Hironaka.Analytic.Rueckert.EvalTools
import Hironaka.Analytic.Rueckert.Hypersurface
import Hironaka.Analytic.Rueckert.Irreducible
import Hironaka.Analytic.Rueckert.NoetherNormalization
import Hironaka.Analytic.Rueckert.Noetherian
import Hironaka.Analytic.Rueckert.NullstellensatzReduction
import Hironaka.Analytic.Rueckert.Parametrization
import Hironaka.Analytic.Rueckert.Quotient
import Hironaka.Analytic.Weierstrass.FunctionLevel
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Rückert's Nullstellensatz over `ℂ`

For an ideal `I` of the germ ring `𝒪_n = ℂ{x_1, …, x_n}`, `𝓘(V(I)) = √I`
(`vanishingIdeal_eq_radical`), and a series vanishing near `0` on the common zero set of a finite
system of generators of `I` lies in `√I` (`mem_radical_of_vanishesOn`). The proof follows
[Fre17, Ch. I, Theorem 9.1], by induction on the number of variables:

* `n = 0`: `𝒪_0 = ℂ`, whose ideals are `⊥` and `⊤` (`vanishingIdeal_eq_radical_conv_zero`).
* The reduction to prime ideals (every proper radical ideal in a Noetherian ring is the
  intersection of finitely many primes) is `NullstellensatzReduction.lean`
  (`vanishingIdeal_eq_radical_of_forall_isPrime`, Mathlib's `Ideal.sInf_minimalPrimes`).
* A prime `P ⊆ 𝒪_{m+1}`: a linear change of coordinates makes a nonzero element of `P` regular
  in `x_0` (`exists_substEquiv_isRegularIn`, `Subst.lean`; the statement is invariant,
  `vanishingIdeal_le_radical_of_map_substEquiv`), and the preparation theorem puts the series of
  a Weierstrass polynomial into `P` (`vanishingIdeal_le_of_isPrime`). Freitag's two alternatives
  (`vanishingIdeal_le_of_isPrime_of_weierstrass_mem`): a principal `P = (Q)` is the hypersurface
  case [Fre17, Ch. I, 5.1] (`Hypersurface.lean`, `vanishingIdeal_span_singleton_le_of_prime`);
  otherwise, for `f ∈ 𝓘(V(P))`, Lemma 7.1 (`finite_mk_comp_convTail`,
  `NoetherNormalization.lean`) makes `f` integral over `𝒪_m` modulo `P`, and a monic relation
  `q(f) ∈ P` of minimal degree is examined as in the proof of 9.1: if the constant term
  `q_0 ∈ 𝔭 = P ∩ 𝒪_m` then `f · q'(f) ∈ P` with `q'` monic of smaller degree, so `f ∈ P` by
  primality and minimality; if `q_0 ∉ 𝔭`, the parametrization lemma (`Parametrization.lean`)
  gives `A ∉ 𝔭` and, over the points `y ∈ V(𝔭)` near `0` with `A(y) ≠ 0`, points `(t, y) ∈ V(P)`
  near `0`; there `f(t, y) = 0` and `q(f)(t, y) = 0`, so `q_0(y) = 0`
  (`evalSeries_eval₂_convTail_eventually`): `A q_0 ∈ 𝓘(V(𝔭)) = 𝔭` by the induction hypothesis,
  hence `q_0 ∈ 𝔭` (`𝔭` prime, `A ∉ 𝔭`), a contradiction.

Followed from [Fre17]: 5.1, 7.1, the mechanism of 8.3, and 9.1 (reduction, case split, minimal
integral equation, `A q_0 ∈ 𝓘(V(𝔭)) = 𝔭`). Replaced: 7.3, 7.4 and 8.2, by the argument over a
principal ideal domain of `Parametrization.lean`. The failure of the statement over `ℝ`
(`not_nullstellensatz_real`) is in `NullstellensatzReduction.lean`. The Nullstellensatz is what
identifies the vanishing ideal of an irreducible germ with its prime;
the Nullstellensatz for analytic spaces (`Hironaka/AnalyticSpace/Nullstellensatz.lean`) applies it
to the stalks.
-/

public section

open Filter Topology Polynomial

namespace Analytic

variable {m : ℕ}

/-- The base case `n = 0`: `𝒪_0 = ℂ`, whose ideals are `⊥` and `⊤`. -/
theorem vanishingIdeal_eq_radical_conv_zero (I : Ideal (Conv ℂ 0)) :
    vanishingIdeal I = I.radical := by
  by_cases hI : I = ⊤
  · rw [hI, vanishingIdeal_top, Ideal.radical_top]
  · have hbot : I = ⊥ := by
      by_contra hne
      obtain ⟨f, hfI, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      exact hI (I.eq_top_of_isUnit_mem hfI (isUnit_of_ne_zero_conv_zero hf0))
    rw [hbot, vanishingIdeal_bot]
    simp

/-- Near `0`, the series `q(f)` (`q ∈ 𝒪_m[T]` evaluated at `f ∈ 𝒪_{m+1}`) evaluates as
`∑ q_i(x') f(x)^i`. -/
theorem evalSeries_eval₂_convTail_eventually (q : Polynomial (Conv ℂ m)) (f : Conv ℂ (m + 1)) :
    evalSeries ((q.eval₂ (convTail ℂ).toRingHom f : Conv ℂ (m + 1)) :
        MvPowerSeries (Fin (m + 1)) ℂ) =ᶠ[𝓝 (0 : Fin (m + 1) → ℂ)]
      fun z => ∑ i ∈ Finset.range (q.natDegree + 1),
        evalSeries (q.coeff i : MvPowerSeries (Fin m) ℂ) (Fin.tail z) *
          evalSeries (f : MvPowerSeries (Fin (m + 1)) ℂ) z ^ i := by
  rw [eval₂_eq_sum_range]
  have hsum := evalSeries_finsetSum_eventually (Finset.range (q.natDegree + 1))
    fun i => (convTail ℂ).toRingHom (q.coeff i) * f ^ i
  rw [← AddSubmonoidClass.coe_finsetSum] at hsum
  have hterm : ∀ i, evalSeries (((convTail ℂ).toRingHom (q.coeff i) * f ^ i : Conv ℂ (m + 1)) :
      MvPowerSeries (Fin (m + 1)) ℂ) =ᶠ[𝓝 (0 : Fin (m + 1) → ℂ)]
        fun z => evalSeries (q.coeff i : MvPowerSeries (Fin m) ℂ) (Fin.tail z) *
          evalSeries (f : MvPowerSeries (Fin (m + 1)) ℂ) z ^ i := by
    intro i
    filter_upwards [evalSeries_mul_eventually ((convTail ℂ).toRingHom (q.coeff i)).2 (f ^ i).2,
      evalSeries_pow_eventually f.2 i] with z h1 h2
    rw [Subalgebra.coe_mul, h1, Subalgebra.coe_pow, h2, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, coe_convTail, evalSeries_liftTail]
  filter_upwards [hsum, (eventually_all_finset (Finset.range (q.natDegree + 1))).mpr
    fun i _ => hterm i] with z hz hi
  rw [hz]
  exact Finset.sum_congr rfl fun i hi' => hi i hi'

/-- The prime case of [Fre17, Ch. I, 9.1] for a prime ideal containing the series of a Weierstrass
polynomial in `x_0`, given the Nullstellensatz in `m` variables: `𝓘(V(P)) ⊆ P`. Freitag's case
split is kept: a principal `P` is the first alternative ([Fre17, Ch. I, 5.1],
`vanishingIdeal_span_singleton_le_of_prime`); otherwise the minimal integral equation of a series
`f ∈ 𝓘(V(P))` over `𝒪_m` modulo `P` (Lemma 7.1, `finite_mk_comp_convTail`) and the
parametrization lemma give `f ∈ P`. -/
theorem vanishingIdeal_le_of_isPrime_of_weierstrass_mem
    (ih : ∀ I : Ideal (Conv ℂ m), vanishingIdeal I = I.radical)
    {P : Ideal (Conv ℂ (m + 1))} [hP : P.IsPrime] {d : ℕ} {c : Fin d → Conv ℂ m}
    (hc : ∀ j, MvPowerSeries.constantCoeff (c j : MvPowerSeries (Fin m) ℂ) = 0)
    (hW : convPolyEval ℂ (weierstrassPolynomial d c) ∈ P) :
    vanishingIdeal P ≤ P := by
  classical
  by_cases hprinc : ∃ Q : Conv ℂ (m + 1), P = Ideal.span {Q}
  · obtain ⟨Q, rfl⟩ := hprinc
    have hQ0 : Q ≠ 0 := by
      rintro rfl
      have h0 := zero_dvd_iff.mp (Ideal.mem_span_singleton.mp hW)
      exact (monic_weierstrassPolynomial d c).ne_zero
        (convPolyEval_injective (by rw [h0, map_zero]))
    exact vanishingIdeal_span_singleton_le_of_prime ((Ideal.span_singleton_prime hQ0).mp hP)
  intro f hf
  obtain ⟨S, hS⟩ := exists_finset_span_eq P
  obtain ⟨p, hpdef⟩ : ∃ p : Ideal (Conv ℂ m), p = P.comap (convTail ℂ).toRingHom := ⟨_, rfl⟩
  obtain ⟨Sp, hSp⟩ := exists_finset_span_eq p
  have hp : p.IsPrime := by rw [hpdef]; exact Ideal.comap_isPrime _ _
  have hfS : VanishesOn S f := (mem_vanishingIdeal_iff hS).mp hf
  -- Lemma 7.1: `f` is integral over `𝒪_m` modulo `P`
  have hreg : IsRegularIn (convPolyEval ℂ (weierstrassPolynomial d c) :
      MvPowerSeries (Fin (m + 1)) ℂ) d := isRegularIn_convPolyEval_weierstrassPolynomial hc
  have hfin := finite_mk_comp_convTail hW hreg
  have hint : ∃ q : Polynomial (Conv ℂ m), q.Monic ∧ q.eval₂ (convTail ℂ).toRingHom f ∈ P := by
    let alg : Algebra (Conv ℂ m) (Conv ℂ (m + 1) ⧸ P) := RingHom.toAlgebra (R := Conv ℂ m)
      (S := Conv ℂ (m + 1) ⧸ P) ((Ideal.Quotient.mk P).comp (convTail ℂ).toRingHom)
    let hmod : Module (Conv ℂ m) (Conv ℂ (m + 1) ⧸ P) := @Algebra.toModule _ _ _ _ alg
    have hfin' : @Module.Finite (Conv ℂ m) (Conv ℂ (m + 1) ⧸ P) _ _ hmod := hfin
    obtain ⟨q, hqm, hq⟩ :=
      @IsIntegral.of_finite (Conv ℂ m) (Conv ℂ (m + 1) ⧸ P) _ _ alg hfin' (Ideal.Quotient.mk P f)
    refine ⟨q, hqm, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, hom_eval₂]
    exact hq
  have hex : ∃ k, ∃ q : Polynomial (Conv ℂ m), q.Monic ∧ q.natDegree = k ∧
      q.eval₂ (convTail ℂ).toRingHom f ∈ P :=
    let ⟨q, hqm, hq⟩ := hint; ⟨q.natDegree, q, hqm, rfl, hq⟩
  obtain ⟨q, hqm, hqdeg, hq⟩ := Nat.find_spec hex
  have hmin : ∀ q' : Polynomial (Conv ℂ m), q'.Monic → q'.eval₂ (convTail ℂ).toRingHom f ∈ P →
      Nat.find hex ≤ q'.natDegree := fun q' hq'm hq' => Nat.find_min' hex ⟨q', hq'm, rfl, hq'⟩
  have hk : 0 < q.natDegree := by
    rcases Nat.eq_zero_or_pos q.natDegree with h0 | h
    · exfalso
      have hq1 : q = 1 := eq_one_of_monic_natDegree_zero hqm h0
      rw [hq1, eval₂_one] at hq
      exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr hq)
    · exact h
  have hdivX_monic : (Polynomial.divX q).Monic := by
    rw [Monic, leadingCoeff, Polynomial.natDegree_divX_eq_natDegree_tsub_one, Polynomial.coeff_divX,
      Nat.sub_add_cancel (Nat.succ_le_of_lt hk)]
    exact hqm.coeff_natDegree
  have heval : q.eval₂ (convTail ℂ).toRingHom f =
      f * (Polynomial.divX q).eval₂ (convTail ℂ).toRingHom f + convTail ℂ (q.coeff 0) := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add q]
    rw [eval₂_add, eval₂_mul, eval₂_X, eval₂_C]
    rfl
  by_cases hc0 : q.coeff 0 ∈ p
  · -- first case: `q_0 ∈ p`, so `f · q'(f) ∈ P` with `q'` monic of smaller degree
    have h2 : convTail ℂ (q.coeff 0) ∈ P := by rw [hpdef] at hc0; exact Ideal.mem_comap.mp hc0
    have h1 : f * (Polynomial.divX q).eval₂ (convTail ℂ).toRingHom f ∈ P := by
      have := P.sub_mem hq h2
      rwa [heval, add_sub_cancel_right] at this
    rcases hP.mem_or_mem h1 with h | h
    · exact h
    · exfalso
      have := hmin (Polynomial.divX q) hdivX_monic h
      rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, ← hqdeg] at this
      omega
  · -- second case: `q_0 ∉ p`; the parametrization lemma gives `A q_0 ∈ 𝓘(V(p)) = p`
    exfalso
    have hqvan : VanishesOn S (q.eval₂ (convTail ℂ).toRingHom f) :=
      VanishesOn.of_mem_span (by rw [hS]; exact hq)
    have hall : ∀ᶠ z in 𝓝 (0 : Fin (m + 1) → ℂ),
        (z ∈ zeroSet S → evalSeries (f : MvPowerSeries (Fin (m + 1)) ℂ) z = 0) ∧
        (z ∈ zeroSet S → evalSeries ((q.eval₂ (convTail ℂ).toRingHom f : Conv ℂ (m + 1)) :
          MvPowerSeries (Fin (m + 1)) ℂ) z = 0) ∧
        evalSeries ((q.eval₂ (convTail ℂ).toRingHom f : Conv ℂ (m + 1)) :
          MvPowerSeries (Fin (m + 1)) ℂ) z = ∑ i ∈ Finset.range (q.natDegree + 1),
            evalSeries (q.coeff i : MvPowerSeries (Fin m) ℂ) (Fin.tail z) *
              evalSeries (f : MvPowerSeries (Fin (m + 1)) ℂ) z ^ i :=
      hfS.and (hqvan.and (evalSeries_eval₂_convTail_eventually q f))
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hall
    have hδ2 : 0 < δ / 2 := by positivity
    obtain ⟨A, hAp, hA⟩ := exists_eventually_exists_cons_mem_zeroSet hc hW hS
      (by rw [← hpdef]; exact hSp) hδ2
    rw [← hpdef] at hAp
    have hmem : A * q.coeff 0 ∈ vanishingIdeal p := by
      rw [mem_vanishingIdeal_iff hSp]
      unfold VanishesOn
      filter_upwards [hA, evalSeries_mul_eventually A.2 (q.coeff 0).2,
        Metric.eventually_nhds_iff.mpr ⟨δ / 2, hδ2, fun y hy => hy⟩] with y hA hmul hyδ hySp
      rw [Subalgebra.coe_mul, hmul]
      by_cases hAy : evalSeries (A : MvPowerSeries (Fin m) ℂ) y = 0
      · rw [hAy, zero_mul]
      · obtain ⟨t, htδ, hzS⟩ := hA hySp hAy
        obtain ⟨z, hz⟩ : ∃ z : Fin (m + 1) → ℂ, z = Fin.cons t y := ⟨_, rfl⟩
        have hzball : dist z 0 < δ := by
          rw [dist_zero_right, pi_norm_lt_iff hδ]
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · rw [hz, Fin.cons_zero]; exact htδ.trans (by linarith)
          · rw [hz, Fin.cons_succ]
            have hy' : ‖y‖ < δ / 2 := by rwa [dist_zero_right] at hyδ
            exact ((pi_norm_lt_iff hδ2).mp hy' j).trans (by linarith)
        obtain ⟨h1, h2, h3⟩ := hball hzball
        rw [← hz] at hzS
        have hf0 := h1 hzS
        have hq0 := h2 hzS
        rw [h3, hf0, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos _))
          (fun i _ hi => by rw [zero_pow hi, mul_zero]), pow_zero, mul_one, hz, Fin.tail_cons]
          at hq0
        rw [hq0, mul_zero]
    rw [ih p, hp.radical] at hmem
    rcases hp.mem_or_mem hmem with h | h
    · exact hAp h
    · exact hc0 h

/-- The induction step: the Nullstellensatz in `m` variables gives `𝓘(V(P)) ⊆ P` for every prime
`P ⊆ 𝒪_{m+1}`: a linear change of coordinates makes a nonzero element of `P` regular in `x_0`
(`exists_substEquiv_isRegularIn`), the preparation theorem puts the series of a Weierstrass
polynomial into the image ideal, and the statement is invariant under the change
(`vanishingIdeal_le_radical_of_map_substEquiv`). -/
theorem vanishingIdeal_le_of_isPrime (ih : ∀ I : Ideal (Conv ℂ m), vanishingIdeal I = I.radical)
    (P : Ideal (Conv ℂ (m + 1))) [hP : P.IsPrime] : vanishingIdeal P ≤ P := by
  by_cases hbot : P = ⊥
  · rw [hbot, vanishingIdeal_bot]
  obtain ⟨f, hfP, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨L, hreg⟩ := exists_substEquiv_isRegularIn hf0
  obtain ⟨σ, hσ⟩ : ∃ σ : Conv ℂ (m + 1) ≃+* Conv ℂ (m + 1), σ = (substEquiv L).toRingEquiv :=
    ⟨_, rfl⟩
  have hP' : (P.map (σ : Conv ℂ (m + 1) →+* Conv ℂ (m + 1))).IsPrime := by
    rw [hσ]; exact Ideal.map_isPrime_of_equiv _
  have hσf : σ f ∈ P.map (σ : Conv ℂ (m + 1) →+* Conv ℂ (m + 1)) := Ideal.mem_map_of_mem _ hfP
  have hreg' : IsRegularIn ((σ f : Conv ℂ (m + 1)) : MvPowerSeries (Fin (m + 1)) ℂ)
      (f : MvPowerSeries (Fin (m + 1)) ℂ).order.toNat := by rw [hσ]; exact hreg
  obtain ⟨u, c, hu, hc, hσf_eq⟩ := exists_preparation_conv hreg'
  have hW : convPolyEval ℂ (weierstrassPolynomial _ c) ∈
      P.map (σ : Conv ℂ (m + 1) →+* Conv ℂ (m + 1)) := by
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    have : convPolyEval ℂ (weierstrassPolynomial _ c) = v * σ f := by
      rw [hσf_eq, ← mul_assoc, hv, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ hσf
  have hle := vanishingIdeal_le_of_isPrime_of_weierstrass_mem ih (hP := hP') hc hW
  have := vanishingIdeal_le_radical_of_map_substEquiv L (I := P) (by
    rw [← hσ]; exact hle.trans Ideal.le_radical)
  rwa [hP.radical] at this

/-- Rückert's Nullstellensatz over `ℂ` [Fre17, Ch. I, Theorem 9.1]: `𝓘(V(I)) = √I` for every
ideal `I` of `𝒪_n`, by induction on the number of variables. -/
theorem vanishingIdeal_eq_radical : ∀ (n : ℕ) (I : Ideal (Conv ℂ n)), vanishingIdeal I = I.radical
  | 0, I => vanishingIdeal_eq_radical_conv_zero I
  | m + 1, I => vanishingIdeal_eq_radical_of_forall_isPrime
      (fun P hP => vanishingIdeal_le_of_isPrime (vanishingIdeal_eq_radical m) P (hP := hP)) I

/-- The pointwise form: a series vanishing near `0` on the common zero set of a finite system of
generators of `I` lies in `√I`. -/
theorem mem_radical_of_vanishesOn {n : ℕ} {S : Finset (Conv ℂ n)} {f : Conv ℂ n}
    (hf : VanishesOn S f) : f ∈ (Ideal.span (S : Set (Conv ℂ n))).radical :=
  mem_radical_of_vanishesOn_of_eq (vanishingIdeal_eq_radical n _) hf

end Analytic
