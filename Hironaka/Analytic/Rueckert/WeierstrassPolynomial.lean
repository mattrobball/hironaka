/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Weierstrass.Exponents
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.EReal.Operations
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Weierstrass polynomials over a commutative ring

Lemmas about polynomials over an arbitrary commutative ring that do not depend on the coefficient
field: the Weierstrass polynomial with zero coefficients is `X^d`, the one of degree `0` is `1`, a
monic polynomial is the Weierstrass polynomial of its own coefficients, and a monic polynomial of
degree `0` is `1`.
-/

public section

open scoped ENNReal NNReal Topology
open MvPowerSeries Filter

namespace Analytic

variable {m n : ℕ}

/-! ### Weierstrass polynomials over a commutative ring -/

variable {m : ℕ}

/-- The Weierstrass polynomial with zero coefficients is `X^d`. -/
theorem weierstrassPolynomial_zero {R : Type*} [CommRing R] (d : ℕ) :
    weierstrassPolynomial d (fun _ : Fin d => (0 : R)) = Polynomial.X ^ d := by
  unfold weierstrassPolynomial
  simp

/-- `weierstrassPolynomial 0 c = 1`. -/
theorem weierstrassPolynomial_zero_eq_one {R : Type*} [CommRing R] (c : Fin 0 → R) :
    weierstrassPolynomial 0 c = 1 := by
  unfold weierstrassPolynomial
  simp

/-- A monic polynomial is the Weierstrass polynomial of its own coefficients. -/
theorem eq_weierstrassPolynomial_coeff_of_monic {R : Type*} [CommRing R]
    {Q : Polynomial R} (hQ : Q.Monic) :
    Q = weierstrassPolynomial Q.natDegree fun j => Q.coeff (Q.natDegree - 1 - j) := by
  refine Polynomial.ext fun n => ?_
  by_cases hn : n < Q.natDegree
  · rw [coeff_weierstrassPolynomial_of_lt _ _ hn]
    change Q.coeff n = Q.coeff (Q.natDegree - 1 - (Q.natDegree - 1 - n))
    congr 1
    omega
  · by_cases hn' : n = Q.natDegree
    · subst hn'
      rw [coeff_weierstrassPolynomial_self, hQ.coeff_natDegree]
    · rw [coeff_weierstrassPolynomial_of_gt _ _ (by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-! ### Monic polynomials of degree zero -/

variable {m : ℕ}

/-- A monic polynomial of degree `0` is `1`. -/
theorem eq_one_of_monic_natDegree_eq_zero {R : Type*} [CommRing R] {p : Polynomial R}
    (hp : p.Monic) (h0 : p.natDegree = 0) : p = 1 := by
  rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
  have h : p.coeff 0 = 1 := by
    have := hp.coeff_natDegree
    rwa [h0] at this
  rw [h, Polynomial.C_1]

section Succ

end Succ

end Analytic
