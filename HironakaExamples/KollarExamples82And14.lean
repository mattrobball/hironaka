/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Derivative.Basic
import HironakaExamples.MaximalContact.Example82
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
/-!
# Going down along a blow-up: Kollár's Examples 82 and 14

[Kol07, Example 82] (`I = (xy − zⁿ)`, `ord₀ I = 2`, `D(I) = (x, y, z^{n−1})`, and its second part:
`f = x³ + xy⁵ + z⁴` with the general hypersurface of maximal contact
`x + u₁xy³ + u₂y⁴ + u₃z² = 0`, `uᵢ` units, followed through two blow-ups) and [Kol07, Example 14]
(the points of multiplicity `m` on the blow-up of a hypersurface lie on the birational transform
of the hyperplane `y = 0`) are computed in `HironakaExamples/MaximalContact/Example82.lean` and
`Example14.lean`. This file records the coordinate and chart notation of those computations and
states the eight results on the second part of Example 82 over an arbitrary nontrivial
commutative `ℚ`-algebra `R`, with the algebra instances of `R` as explicit hypotheses of each
theorem (in `Example82.lean` they are section variables): the orders at the origin of `f` (three)
and of the maximal-contact element `h` (one); `h ∈ D²(f)`; the two chart rows `σ f = y³ · f'`,
`σ f' = y³ · f''` with the corresponding rows for `h`; the order of `f''` at the origin (two); the
elimination identity writing `(1 + u₁y³)³ f''` as a remainder plus a multiple of the transformed
`h''`; the membership of the remainder in `(y³, y²z⁴)`; and its order at the origin (three, and
exactly three when `u₂` is a unit).

All are computations in polynomial rings. The identities (the chart rows of Example 82, the
elimination identity, Example 14's transform and its formulas (14.3) and (14.5)) are polynomial
identities after the substitution lemmas of `aeval`; memberships in powers of a point's maximal
ideal are exhibited by witnesses; non-memberships (the exact orders and multiplicities) come from
two tools, a partial derivative lowers the power of an ideal by one (the Leibniz rule) and
evaluation at the point kills its maximal ideal, applied to a `(k−1)`-fold partial derivative that
does not vanish at the point; the derivative ideals are computed from the partial derivatives of
the generators (`derivative_span_pderiv`), with `D(xy − zⁿ) = (x, y, z^{n−1})` from
`derivative_example52`; `h ∈ D²(f)` divides `∂∂f` by nonzero rationals over the `ℚ`-algebra `R`;
[Kol07, Claim 14.7] at every `ℚ`-point of `y' = 0` uses that the restriction `y' ↦ 0` maps `𝔪_p^k`
into itself and that `∂_{y'}` lowers the order by one. -/

public section

open MvPolynomial

namespace Hironaka.Examples.GoingDown

/-! ### Example 82, first part: `I = (xy − zⁿ)` -/

section ExampleEightyTwo

/-- Kollár's `x = X 0` in `ℚ[x, y, z]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 3) ℚ)
/-- Kollár's `y = X 1` in `ℚ[x, y, z]`. -/
local notation "y" => (X 1 : MvPolynomial (Fin 3) ℚ)
/-- Kollár's `z = X 2` in `ℚ[x, y, z]`. -/
local notation "z" => (X 2 : MvPolynomial (Fin 3) ℚ)

variable (n : ℕ)

end ExampleEightyTwo

/-! ### Example 82, second part: `f = x³ + xy⁵ + z⁴` -/

section ExampleEightyTwoSecond

variable {R : Type*} [CommRing R] [Algebra ℚ R] [Nontrivial R] (u₁ u₂ u₃ : R)

/-- Kollár's `x = X 0` in `R[x, y, z]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 3) R)
/-- Kollár's `y = X 1` in `R[x, y, z]`. -/
local notation "y" => (X 1 : MvPolynomial (Fin 3) R)
/-- Kollár's `z = X 2` in `R[x, y, z]`. -/
local notation "z" => (X 2 : MvPolynomial (Fin 3) R)
/-- The chart `x = x₁y₁`, `y = y₁`, `z = z₁y₁` (pivot `y`), as a substitution. -/
local notation "σ" => (aeval ![X 0 * X 1, X 1, X 2 * X 1] :
  MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 3) R)

/-- `h ∈ D²(f) = MC(f)`: the maximal-contact element lies in the second derivative ideal of `f`. -/
theorem mem_MC_example82_second :
    x + C u₁ * (x * y ^ 3) + C u₂ * y ^ 4 + C u₃ * z ^ 2 ∈
      Ideal.derivativeIter ℚ 2 (Ideal.span {x ^ 3 + x * y ^ 5 + z ^ 4}) := by
  let _ := ‹Algebra ℚ R›
  have _ : Nontrivial R := ‹_›
  exact Hironaka.Examples.mem_MC_example82_second u₁ u₂ u₃

/-- The first blow-up, chart `x = x₁y₁`, `y = y₁`, `z = z₁y₁`: `f` and `h` transform to
`y³ · (x³ + xy³ + yz⁴)` and `y · (x + u₁xy³ + u₂y³ + u₃yz²)`, Kollár's second row. -/
theorem transform_example82_second_one :
    σ (x ^ 3 + x * y ^ 5 + z ^ 4) = y ^ 3 * (x ^ 3 + x * y ^ 3 + y * z ^ 4) ∧
      σ (x + C u₁ * (x * y ^ 3) + C u₂ * y ^ 4 + C u₃ * z ^ 2) =
        y * (x + C u₁ * (x * y ^ 3) + C u₂ * y ^ 3 + C u₃ * (y * z ^ 2)) := by
  let _ := ‹Algebra ℚ R›
  have _ : Nontrivial R := ‹_›
  exact Hironaka.Examples.transform_example82_second_one u₁ u₂ u₃

/-- The second blow-up in the same chart: Kollár's third row, `y³ · (x³ + xy + y²z⁴)` and
`y · (x + u₁xy³ + u₂y² + u₃y²z²)`. -/
theorem transform_example82_second_two :
    σ (x ^ 3 + x * y ^ 3 + y * z ^ 4) = y ^ 3 * (x ^ 3 + x * y + y ^ 2 * z ^ 4) ∧
      σ (x + C u₁ * (x * y ^ 3) + C u₂ * y ^ 3 + C u₃ * (y * z ^ 2)) =
        y * (x + C u₁ * (x * y ^ 3) + C u₂ * y ^ 2 + C u₃ * (y ^ 2 * z ^ 2)) := by
  let _ := ‹Algebra ℚ R›
  have _ : Nontrivial R := ‹_›
  exact Hironaka.Examples.transform_example82_second_two u₁ u₂ u₃

/-- The elimination identity: `(1 + u₁y³)³ · f''` is a remainder free of `x` plus a multiple of the
transformed maximal-contact element `h'' = x + u₁xy³ + u₂y² + u₃y²z²`; so `f''` restricted to
`h'' = 0` is the remainder, up to the unit `(1 + u₁y³)³`. -/
theorem restrict_example82_second_two :
    (1 + C u₁ * y ^ 3) ^ 3 * (x ^ 3 + x * y + y ^ 2 * z ^ 4) =
      (-(y ^ 6 * (C u₂ + C u₃ * z ^ 2) ^ 3) -
          (1 + C u₁ * y ^ 3) ^ 2 * y ^ 3 * (C u₂ + C u₃ * z ^ 2) +
          (1 + C u₁ * y ^ 3) ^ 3 * y ^ 2 * z ^ 4) +
        (x + C u₁ * (x * y ^ 3) + C u₂ * y ^ 2 + C u₃ * (y ^ 2 * z ^ 2)) *
          ((x * (1 + C u₁ * y ^ 3)) ^ 2 - x * (1 + C u₁ * y ^ 3) * y ^ 2 * (C u₂ + C u₃ * z ^ 2) +
            y ^ 4 * (C u₂ + C u₃ * z ^ 2) ^ 2 + (1 + C u₁ * y ^ 3) ^ 2 * y) := by
  let _ := ‹Algebra ℚ R›
  have _ : Nontrivial R := ‹_›
  exact Hironaka.Examples.restrict_example82_second_two u₁ u₂ u₃

/-- The remainder lies in the ideal `(y³, y²z⁴)`. -/
theorem mem_span_example82_second_two :
    -(y ^ 6 * (C u₂ + C u₃ * z ^ 2) ^ 3) - (1 + C u₁ * y ^ 3) ^ 2 * y ^ 3 * (C u₂ + C u₃ * z ^ 2) +
        (1 + C u₁ * y ^ 3) ^ 3 * y ^ 2 * z ^ 4 ∈
      Ideal.span {y ^ 3, y ^ 2 * z ^ 4} := by
  let _ := ‹Algebra ℚ R›
  have _ : Nontrivial R := ‹_›
  exact Hironaka.Examples.mem_span_example82_second_two u₁ u₂ u₃

end ExampleEightyTwoSecond

/-! ### Example 14 on the instance `m = 3`, `n = 2` -/

section ExampleFourteen

/-- Kollár's `x₁ = X 0` in `ℚ[x₁, x₂, y]`. -/
local notation "x₁" => (X 0 : MvPolynomial (Fin 3) ℚ)
/-- Kollár's `x₂ = X 1` in `ℚ[x₁, x₂, y]`. -/
local notation "x₂" => (X 1 : MvPolynomial (Fin 3) ℚ)
/-- Kollár's `y = X 2` in `ℚ[x₁, x₂, y]`. -/
local notation "y" => (X 2 : MvPolynomial (Fin 3) ℚ)
/-- The chart `x₁ = x₁'x₂'`, `x₂ = x₂'`, `y = y'x₂'` (pivot `x₂`), as a substitution. -/
local notation "σ'" => (aeval ![X 0 * X 1, X 1, X 2 * X 1] :
  MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 3) ℚ)
/-- Restriction to `y' = 0`, as a substitution. -/
local notation "ρ" =>
  (aeval ![X 0, X 1, 0] : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 3) ℚ)

end ExampleFourteen

end Hironaka.Examples.GoingDown
