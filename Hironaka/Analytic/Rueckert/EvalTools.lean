/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.Eval
public import Hironaka.Analytic.Rueckert.Basic
import Hironaka.Analytic.ConvSeries.Rescale
import Hironaka.Analytic.Germ.CoordDiv
import Hironaka.Analytic.Rueckert.Quotient
import Hironaka.Analytic.Rueckert.Subst
import Hironaka.Analytic.Weierstrass.FunctionLevel
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Positivity.Finset

/-!
# Analytic tools for the Nullstellensatz: density of non-zeros, polynomial evaluation, roots

Three general facts about convergent power series used by the proof of Rückert's Nullstellensatz
(`Nullstellensatz.lean`), none specific to it; they rest on Mathlib's identity theorem and on
elementary estimates:

* the open polydisc is convex, and a nonzero convergent series takes a nonzero value on every
  nonempty open subset of its polydisc of convergence (`exists_evalSeries_ne_zero_of_isOpen`),
  the fact behind the "dense subset of a small neighbourhood of `0`" in the proof of
  [Fre17, Ch. I, 5.1] and the negligible set of [Fre17, Ch. I, §9]: the identity theorem
  `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` on the connected polydisc plus
  the uniqueness of coefficients in the form `Conv.ext_of_evalSeries_eventuallyEq` (`Subst.lean`);
* near `0`, `evalSeries` of a finite sum is the sum of the values
  (`evalSeries_finsetSum_eventually`), and `convPolyEval Q`, the series of a polynomial
  `Q ∈ 𝒪_m[x_0]`, evaluates as the polynomial `∑_k Q_k(x') x_0^k`
  (`evalSeries_convPolyEval_eventually`);
* a root of a monic polynomial over `K` whose lower coefficients have total norm `< ε^d`
  (`ε ≤ 1`) has norm `< ε` (`norm_root_lt_of_monic`): the continuity of the zeros of a
  Weierstrass polynomial, used repeatedly in [Fre17, Ch. I, 5.1, 8.1, 8.2], in the quantitative
  form the proofs need.
-/

public section

open Filter Topology MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K] {m n : ℕ}

/-! ### The polydisc is convex; a nonzero series does not vanish on any open subset -/

/-- The origin lies in every open polydisc. -/
theorem zero_mem_polydisc (ρ : Radius m) : (0 : Fin m → K) ∈ polydisc K ρ := fun k => by
  simp [ρ.pos k]

/-- The open polydisc `{x | ∀ k, ‖x k‖ < ρ k}` is convex (hence connected). -/
theorem convex_polydisc (ρ : Radius m) : Convex ℝ (polydisc K ρ) := by
  intro x hx y hy a b ha hb hab k
  have hx' := hx k
  have hy' := hy k
  calc ‖(a • x + b • y) k‖ = ‖a • x k + b • y k‖ := rfl
    _ ≤ ‖a • x k‖ + ‖b • y k‖ := norm_add_le _ _
    _ = a * ‖x k‖ + b * ‖y k‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ < a * (ρ k : ℝ) + b * (ρ k : ℝ) := by
      rcases ha.lt_or_eq with ha' | rfl
      · rcases hb.lt_or_eq with hb' | rfl
        · exact add_lt_add (mul_lt_mul_of_pos_left hx' ha') (mul_lt_mul_of_pos_left hy' hb')
        · simp only [zero_mul, add_zero]
          exact mul_lt_mul_of_pos_left hx' ha'
      · simp only [zero_mul, zero_add] at hab ⊢
        exact mul_lt_mul_of_pos_left hy' (by rw [hab]; exact one_pos)
    _ = (ρ k : ℝ) := by rw [← add_mul, hab, one_mul]

/-- A nonzero convergent series takes a nonzero value on every nonempty open subset of its
polydisc of convergence (the identity theorem on the connected polydisc). -/
theorem exists_evalSeries_ne_zero_of_isOpen {ρ : Radius m} {f : MvPowerSeries (Fin m) K}
    (hf : ConvNorm ρ f ≠ ⊤) (hf0 : f ≠ 0) {V : Set (Fin m → K)} (hV : IsOpen V)
    (hVne : V.Nonempty) (hVρ : V ⊆ polydisc K ρ) : ∃ y ∈ V, evalSeries f y ≠ 0 := by
  by_contra h
  push Not at h
  have han : AnalyticOnNhd K (evalSeries f) (polydisc K ρ) := analyticOnNhd_evalSeries hf
  obtain ⟨y0, hy0⟩ := hVne
  have hev : evalSeries f =ᶠ[𝓝 y0] 0 := by
    filter_upwards [hV.mem_nhds hy0] with y hy
    exact h y hy
  have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_polydisc ρ).isPreconnected (hVρ hy0) hev
  apply hf0
  have : (⟨f, ⟨ρ, hf⟩⟩ : Conv K m) = 0 := Conv.ext_of_evalSeries_eventuallyEq (by
    filter_upwards [(isOpen_polydisc ρ).mem_nhds (zero_mem_polydisc ρ)] with y hy
    rw [Subalgebra.coe_zero, evalSeries_zero]
    exact hzero hy)
  exact congrArg Subtype.val this

/-! ### Evaluation of finite sums and of `convPolyEval` near `0` -/

/-- Near `0`, the value of a finite sum of convergent series is the sum of the values (each
summand converges on a neighbourhood of `0`). -/
theorem evalSeries_finsetSum_eventually {ι : Type*} (s : Finset ι) (F : ι → Conv K n) :
    evalSeries (∑ i ∈ s, (F i : MvPowerSeries (Fin n) K)) =ᶠ[𝓝 (0 : Fin n → K)]
      fun x => ∑ i ∈ s, evalSeries (F i : MvPowerSeries (Fin n) K) x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Eventually.of_forall fun x => by simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hmem : (∑ i ∈ s, (F i : MvPowerSeries (Fin n) K)) ∈ Conv K n :=
      Subalgebra.sum_mem _ fun i _ => (F i).2
    filter_upwards [ih, evalSeries_add_eventually (F a).2 hmem] with x ih h
    rw [h, ih, Finset.sum_insert ha]

/-- Near `0`, `convPolyEval Q` evaluates as the polynomial `∑ Q_k(x') x_0^k` in the first
coordinate with the coefficients evaluated at the tail. -/
theorem evalSeries_convPolyEval_eventually (Q : Polynomial (Conv K m)) :
    evalSeries (convPolyEval K Q : MvPowerSeries (Fin (m + 1)) K) =ᶠ[𝓝 (0 : Fin (m + 1) → K)]
      fun x => ∑ k ∈ Finset.range (Q.natDegree + 1),
        evalSeries (Q.coeff k : MvPowerSeries (Fin m) K) (Fin.tail x) * x 0 ^ k := by
  rw [coe_convPolyEval_eq_sum]
  have hterm : ∀ k, evalSeries (liftTail (Q.coeff k : MvPowerSeries (Fin m) K) * X 0 ^ k)
      =ᶠ[𝓝 (0 : Fin (m + 1) → K)]
        fun x => evalSeries (Q.coeff k : MvPowerSeries (Fin m) K) (Fin.tail x) * x 0 ^ k := by
    intro k
    have h := evalSeries_mul_eventually (convTail K (Q.coeff k)).2 (convX K (0 : Fin (m + 1)) ^ k).2
    rw [coe_convTail, Subalgebra.coe_pow, coe_convX] at h
    filter_upwards [h] with x hx
    rw [hx, evalSeries_liftTail, evalSeries_X_pow]
  have hsum := evalSeries_finsetSum_eventually (Finset.range (Q.natDegree + 1))
    fun k => convTail K (Q.coeff k) * convX K (0 : Fin (m + 1)) ^ k
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, coe_convTail, coe_convX] at hsum
  filter_upwards [hsum, (eventually_all_finset (Finset.range (Q.natDegree + 1))).mpr
    fun k _ => hterm k] with x hx hk
  rw [hx]
  exact Finset.sum_congr rfl fun k hk' => hk k hk'

/-! ### Roots of a monic polynomial with small coefficients are small -/

/-- Continuity of roots at a Weierstrass polynomial, in the form used: a root `t` of a monic
polynomial of degree `d ≥ 1` whose lower coefficients have total norm `< ε ^ d` (with `ε ≤ 1`)
satisfies `‖t‖ < ε`. -/
theorem norm_root_lt_of_monic {p : Polynomial K} (hp : p.Monic) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ < ε ^ p.natDegree) {t : K}
    (ht : p.eval t = 0) : ‖t‖ < ε := by
  by_contra hle
  push Not at hle
  set d := p.natDegree with hd'
  have heval : p.eval t = t ^ d + ∑ i ∈ Finset.range d, p.coeff i * t ^ i := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul,
      add_comm]
  rw [heval] at ht
  have hsum : ‖t‖ ^ d = ‖∑ i ∈ Finset.range d, p.coeff i * t ^ i‖ := by
    rw [← norm_pow, eq_neg_of_add_eq_zero_left ht, norm_neg]
  have hbound : ‖∑ i ∈ Finset.range d, p.coeff i * t ^ i‖ ≤
      ∑ i ∈ Finset.range d, ‖p.coeff i‖ * ‖t‖ ^ i := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, norm_pow]
  rcases le_or_gt ‖t‖ 1 with h1 | h1
  · -- `‖t‖ ≤ 1`: each `‖t‖ ^ i ≤ 1`
    have : ∑ i ∈ Finset.range d, ‖p.coeff i‖ * ‖t‖ ^ i ≤ ∑ i ∈ Finset.range d, ‖p.coeff i‖ :=
      Finset.sum_le_sum fun i _ =>
        mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) h1)
    have hlt : ‖t‖ ^ d < ε ^ d := (hsum.le.trans hbound).trans_lt (this.trans_lt hsmall)
    exact absurd (pow_le_pow_left₀ hε.le hle d) (not_le.mpr hlt)
  · -- `‖t‖ > 1`: `‖t‖ ^ i ≤ ‖t‖ ^ (d - 1)` for `i < d`
    have : ∑ i ∈ Finset.range d, ‖p.coeff i‖ * ‖t‖ ^ i ≤
        ‖t‖ ^ (d - 1) * ∑ i ∈ Finset.range d, ‖p.coeff i‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ h1.le (Nat.le_sub_one_of_lt (Finset.mem_range.mp hi))) (norm_nonneg _)
    have hεd : ε ^ d ≤ 1 := pow_le_one₀ hε.le hε1
    have hlt : ‖t‖ ^ d < ‖t‖ ^ (d - 1) * 1 := by
      calc ‖t‖ ^ d ≤ ‖t‖ ^ (d - 1) * ∑ i ∈ Finset.range d, ‖p.coeff i‖ :=
            (hsum.le.trans hbound).trans this
        _ < ‖t‖ ^ (d - 1) * 1 := by
            refine mul_lt_mul_of_pos_left (hsmall.trans_le hεd) (pow_pos ?_ _)
            exact zero_lt_one.trans h1
    rw [mul_one] at hlt
    exact absurd (pow_le_pow_right₀ h1.le (Nat.sub_le d 1)) (not_le.mpr hlt)

end Analytic
