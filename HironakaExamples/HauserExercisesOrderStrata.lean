/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Defs
public import Hironaka.Scheme.Smooth.CoordinateSystem
import Hironaka.Scheme.IdealSheaf.Order.AffineSpace
import Mathlib.Data.Nat.Choose.Multinomial
/-!
# Hauser's Exercise 4 on the order: the four coordinate hyperplanes of `𝔸⁴`

Exercise 4 of Appendix B of [Hau03] asks for the strata of constant order of the union `X` of
the four coordinate hyperplanes of `𝔸⁴`, and of the subscheme `Y = V(xᵏyˡzᵐwⁿ)`. Over a field
`K` of characteristic zero and at the `K`-rational point `a`, the order of the ideal `(xyzw)` is
the number of coordinates of `a` that vanish (`ord_hauserEx4_eq_card`), and the order of
`(xᵏyˡzᵐwⁿ)` is the sum of the exponents of the coordinates that vanish at `a`
(`ord_hauserEx4_monomial_eq_sum`); so the stratum of order `j` of `X` is the set of points with
exactly `j` vanishing coordinates. Both follow from the computation of the order of a monomial at
a rational point in `Hironaka/Scheme/IdealSheaf/Order/AffineSpace.lean`: the order is additive on
the regular local ring at `a`, and `ord_a xᵢ` is `1` or `0` according as `aᵢ` vanishes. There the
order at a rational point is read off the partial derivatives, as in [Hau03, Appendix A, Exercise
1], through the derivative ideals of [Kol07, Definition 73]. Exercise 3 of the same appendix, `f =
x³ + yᵏzᵐ`, is treated in `HironakaExamples/OrderStrata.lean`.
-/

public section

namespace Hironaka.Order.Examples

open AlgebraicGeometry

open AlgebraicGeometry MvPolynomial

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Hauser's Exercise 4, first part: the order of `xyzw` at the rational point `a` of `𝔸⁴` is the
number of coordinates of `a` that vanish. -/
theorem ord_hauserEx4_eq_card (a : Fin 4 → K) :
    (specIdealSheaf (Ideal.span
        {(X 0 * X 1 * X 2 * X 3 : MvPolynomial (Fin 4) K)})).ord (ratPoint a) =
      Nat.card {i : Fin 4 // a i = 0} := by
  rw [show (X 0 * X 1 * X 2 * X 3 : MvPolynomial (Fin 4) K) = ∏ i, X i from
    (Fin.prod_univ_four fun i => (X i : MvPolynomial (Fin 4) K)).symm]
  exact ord_specIdealSheaf_span_singleton_prod_X a

open scoped Classical in
/-- Hauser's Exercise 4, second part: the order of `xᵏyˡzᵐwⁿ` at the rational point `a` is the
sum of the exponents of the coordinates that vanish at `a`. -/
theorem ord_hauserEx4_monomial_eq_sum (e : Fin 4 → ℕ) (a : Fin 4 → K) :
    (specIdealSheaf (Ideal.span {(∏ i, X i ^ e i : MvPolynomial (Fin 4) K)})).ord (ratPoint a) =
      ∑ i, if a i = 0 then (e i : ℕ∞) else 0 :=
  ord_specIdealSheaf_span_singleton_prod_pow_X e a

end Hironaka.Order.Examples

