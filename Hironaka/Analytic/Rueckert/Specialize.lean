/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Hironaka.Analytic.ConvSeries.Eval
public import Hironaka.Analytic.Rueckert.Basic
import Hironaka.Analytic.ConvSeries.Mul
import Hironaka.Analytic.Germ.CoordDiv
import Hironaka.Analytic.Rueckert.EvalTools
import Hironaka.Analytic.Rueckert.Subst
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Positivity.Finset

/-!
# Specialization of a polynomial over `𝒪_m` at a parameter point

The polynomial `Q_a(z) = Q(a_1, …, a_{n−1})(z) ∈ ℂ[z]` for a fixed small parameter `a` of the
proof of [Fre17, Ch. I, 5.1], and the polynomials in `z_n` over `𝒪_{n−1}` of [Fre17, Ch. I, §8]:
for `W ∈ 𝒪_m[x_0]` (Mathlib's `Polynomial (Conv K m)`, sent to the series ring by `convPolyEval`)
and a point `x ∈ K^m`, `specialize W x ∈ K[X]` is the polynomial whose coefficients are the
values of the coefficients of `W` at `x`. Near `0` this specialization is a ring homomorphism in
the sense of germs of maps: it preserves sums, products and the derivative for `x` in a
neighbourhood of `0` depending on the finitely many coefficients involved
(`specialize_add_eventually`, `specialize_mul_eventually`, `specialize_derivative_eventually`;
`evalSeries` is multiplicative only where both factors converge, `evalSeries_mul_eventually`), it
is exact on constants and on `X`, it preserves monicity and the degree of a monic polynomial, and
the series `convPolyEval W` evaluates at `(t, x)` as the specialized polynomial at `t`
(`evalSeries_convPolyEval_eq_eval_specialize`). Used by the hypersurface case of the
Nullstellensatz through the specialization of a Bezout identity `U W + V W' = D`
(`Hypersurface.lean`), and by the parametrization through the specialization of the Weierstrass
polynomial (`Parametrization.lean`).
-/

@[expose] public section

open Filter Topology Polynomial

namespace Analytic

variable {K : Type*} [RCLike K] {m : ℕ}

/-- The specialization of a polynomial over `𝒪_m` at a parameter point `x ∈ K^m`: the polynomial
over `K` whose coefficients are the values of the coefficients at `x`. -/
noncomputable def specialize (W : Polynomial (Conv K m)) (x : Fin m → K) : Polynomial K :=
  ∑ k ∈ Finset.range (W.natDegree + 1),
    Polynomial.C (evalSeries (W.coeff k : MvPowerSeries (Fin m) K) x) * Polynomial.X ^ k

/-- The coefficients of the specialization are the values of the coefficients. -/
theorem coeff_specialize (W : Polynomial (Conv K m)) (x : Fin m → K) (k : ℕ) :
    (specialize W x).coeff k = evalSeries (W.coeff k : MvPowerSeries (Fin m) K) x := by
  rw [specialize, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt (by simpa using hk), Subalgebra.coe_zero, evalSeries_zero]

/-- Specialization does not raise the degree. -/
theorem natDegree_specialize_le (W : Polynomial (Conv K m)) (x : Fin m → K) :
    (specialize W x).natDegree ≤ W.natDegree := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
  rw [coeff_specialize, coeff_eq_zero_of_natDegree_lt hk, Subalgebra.coe_zero, evalSeries_zero]

/-- The value of the specialized polynomial as the finite sum `∑ W_k(x) t^k`. -/
theorem eval_specialize (W : Polynomial (Conv K m)) (x : Fin m → K) (t : K) :
    (specialize W x).eval t =
      ∑ k ∈ Finset.range (W.natDegree + 1),
        evalSeries (W.coeff k : MvPowerSeries (Fin m) K) x * t ^ k := by
  rw [eval_eq_sum_range' ((natDegree_specialize_le W x).trans_lt (Nat.lt_succ_self _))]
  simp_rw [coeff_specialize]

/-- Near `0`, the series of a polynomial `W ∈ 𝒪_m[x_0]` evaluates as the specialized polynomial at
the tail, evaluated at the first coordinate. -/
theorem evalSeries_convPolyEval_eq_eval_specialize (W : Polynomial (Conv K m)) :
    ∀ᶠ x in 𝓝 (0 : Fin (m + 1) → K),
      evalSeries (convPolyEval K W : MvPowerSeries (Fin (m + 1)) K) x =
        (specialize W (Fin.tail x)).eval (x 0) := by
  filter_upwards [evalSeries_convPolyEval_eventually W] with x hx
  rw [hx, eval_specialize]

/-- Specialization is exact on constants. -/
theorem specialize_C (c : Conv K m) (x : Fin m → K) :
    specialize (Polynomial.C c) x = Polynomial.C (evalSeries (c : MvPowerSeries (Fin m) K) x) := by
  ext k
  rw [coeff_specialize, Polynomial.coeff_C, Polynomial.coeff_C]
  split_ifs
  · rfl
  · rw [Subalgebra.coe_zero, evalSeries_zero]

/-- Specialization is exact on `X`. -/
theorem specialize_X (x : Fin m → K) :
    specialize (Polynomial.X : Polynomial (Conv K m)) x = Polynomial.X := by
  ext k
  rw [coeff_specialize, Polynomial.coeff_X, Polynomial.coeff_X]
  split_ifs
  · rw [Subalgebra.coe_one, evalSeries_one]
  · rw [Subalgebra.coe_zero, evalSeries_zero]

/-- Near `0`, specialization is additive (each coefficient converges on a neighbourhood of `0`). -/
theorem specialize_add_eventually (W₁ W₂ : Polynomial (Conv K m)) :
    ∀ᶠ x in 𝓝 (0 : Fin m → K), specialize (W₁ + W₂) x = specialize W₁ x + specialize W₂ x := by
  filter_upwards [(eventually_all_finset (Finset.range (max W₁.natDegree W₂.natDegree + 1))).mpr
    fun k _ => evalSeries_add_eventually (W₁.coeff k).2 (W₂.coeff k).2] with x hx
  ext k
  rw [coeff_add, coeff_specialize, coeff_specialize, coeff_specialize, coeff_add,
    Subalgebra.coe_add]
  by_cases hk : k ∈ Finset.range (max W₁.natDegree W₂.natDegree + 1)
  · exact hx k hk
  · have hk' := Finset.mem_range.not.mp hk
    push Not at hk'
    have h1 : W₁.coeff k = 0 := coeff_eq_zero_of_natDegree_lt
      ((le_max_left _ _).trans_lt (Nat.lt_of_succ_le hk'))
    have h2 : W₂.coeff k = 0 := coeff_eq_zero_of_natDegree_lt
      ((le_max_right _ _).trans_lt (Nat.lt_of_succ_le hk'))
    rw [h1, h2, Subalgebra.coe_zero, add_zero, evalSeries_zero, add_zero]

/-- Near `0`, specialization is multiplicative (the products of coefficients evaluate as products,
`evalSeries_mul_eventually`). -/
theorem specialize_mul_eventually (W₁ W₂ : Polynomial (Conv K m)) :
    ∀ᶠ x in 𝓝 (0 : Fin m → K), specialize (W₁ * W₂) x = specialize W₁ x * specialize W₂ x := by
  classical
  have hpair : ∀ k : ℕ, ∀ᶠ x in 𝓝 (0 : Fin m → K),
      evalSeries ((W₁ * W₂).coeff k : MvPowerSeries (Fin m) K) x =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
          evalSeries (W₁.coeff p.1 : MvPowerSeries (Fin m) K) x *
            evalSeries (W₂.coeff p.2 : MvPowerSeries (Fin m) K) x := by
    intro k
    rw [coeff_mul]
    have hsum := evalSeries_finsetSum_eventually (Finset.HasAntidiagonal.antidiagonal k)
      fun p => W₁.coeff p.1 * W₂.coeff p.2
    filter_upwards [hsum, (eventually_all_finset (Finset.HasAntidiagonal.antidiagonal k)).mpr
      fun p _ => evalSeries_mul_eventually (W₁.coeff p.1).2 (W₂.coeff p.2).2] with x hx hp
    rw [AddSubmonoidClass.coe_finsetSum]
    rw [hx]
    refine Finset.sum_congr rfl fun p hp' => ?_
    rw [Subalgebra.coe_mul, hp p hp']
  filter_upwards [(eventually_all_finset (Finset.range (W₁.natDegree + W₂.natDegree + 1))).mpr
    fun k _ => hpair k] with x hx
  ext k
  rw [coeff_specialize, coeff_mul (specialize W₁ x)]
  simp_rw [coeff_specialize]
  by_cases hk : k ∈ Finset.range (W₁.natDegree + W₂.natDegree + 1)
  · exact hx k hk
  · have hk' := Finset.mem_range.not.mp hk
    push Not at hk'
    have h0 : (W₁ * W₂).coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt (Nat.lt_of_succ_le hk'))
    rw [h0, Subalgebra.coe_zero, evalSeries_zero]
    refine (Finset.sum_eq_zero fun p hp => ?_).symm
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rcases le_or_gt p.1 W₁.natDegree with h1 | h1
    · have : W₂.natDegree < p.2 := by omega
      rw [coeff_eq_zero_of_natDegree_lt this, Subalgebra.coe_zero, evalSeries_zero, mul_zero]
    · rw [coeff_eq_zero_of_natDegree_lt h1, Subalgebra.coe_zero, evalSeries_zero, zero_mul]

/-- The natural numbers of `𝒪_m` are the constant series. -/
theorem coe_natCast_conv (k : ℕ) :
    ((k : Conv K m) : MvPowerSeries (Fin m) K) = (k : MvPowerSeries (Fin m) K) :=
  map_natCast (Conv K m).val k

/-- A natural number, as a series, evaluates to itself. -/
theorem evalSeries_natCast (k : ℕ) (x : Fin m → K) :
    evalSeries ((k : Conv K m) : MvPowerSeries (Fin m) K) x = k := by
  rw [coe_natCast_conv, ← map_natCast (MvPowerSeries.C (σ := Fin m) (R := K)), evalSeries_C']

/-- Near `0`, specialization commutes with the derivative in `X`. -/
theorem specialize_derivative_eventually (W : Polynomial (Conv K m)) :
    ∀ᶠ x in 𝓝 (0 : Fin m → K),
      specialize (derivative W) x = derivative (specialize W x) := by
  filter_upwards [(eventually_all_finset (Finset.range (W.natDegree + 1))).mpr
    fun k _ => evalSeries_mul_eventually (W.coeff (k + 1)).2 ((k + 1 : ℕ) : Conv K m).2] with x hx
  ext k
  rw [coeff_derivative, coeff_specialize, coeff_specialize, coeff_derivative, Subalgebra.coe_mul]
  by_cases hk : k ∈ Finset.range (W.natDegree + 1)
  · have := hx k hk
    rw [show ((k : Conv K m) + 1 : Conv K m) = ((k + 1 : ℕ) : Conv K m) by push_cast; rfl]
    rw [this, evalSeries_natCast]
    push_cast
    rfl
  · have hk' := Finset.mem_range.not.mp hk
    push Not at hk'
    have h0 : W.coeff (k + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [h0, Subalgebra.coe_zero, zero_mul, evalSeries_zero, zero_mul]

/-- The specialization of a monic polynomial is monic. -/
theorem specialize_monic {W : Polynomial (Conv K m)} (hW : W.Monic) (x : Fin m → K) :
    (specialize W x).Monic := by
  have h1 : (specialize W x).coeff W.natDegree = 1 := by
    rw [coeff_specialize, hW.coeff_natDegree, Subalgebra.coe_one, evalSeries_one]
  have hdeg : (specialize W x).natDegree = W.natDegree :=
    le_antisymm (natDegree_specialize_le W x)
      (le_natDegree_of_ne_zero (by rw [h1]; exact one_ne_zero))
  rw [Monic, leadingCoeff, hdeg, h1]

/-- The specialization of a monic polynomial has the same degree. -/
theorem natDegree_specialize_of_monic {W : Polynomial (Conv K m)} (hW : W.Monic) (x : Fin m → K) :
    (specialize W x).natDegree = W.natDegree :=
  le_antisymm (natDegree_specialize_le W x) (le_natDegree_of_ne_zero (by
    rw [coeff_specialize, hW.coeff_natDegree, Subalgebra.coe_one, evalSeries_one]
    exact one_ne_zero))

end Analytic
