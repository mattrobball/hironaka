/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

import Mathlib.Algebra.Algebra.Hom
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Sheaves.Init
import HironakaExamples.MaximalContact.Example106Stages  -- shake: keep (used only by `example`s)
import HironakaExamples.MaximalContact.Example11Stages  -- shake: keep (used only by `example`s)
import HironakaExamples.MaximalContact.Example12Stages  -- shake: keep (used only by `example`s)
import HironakaExamples.Balanced.Example106  -- shake: keep (used only by `example`s)
import HironakaExamples.Balanced.Example11  -- shake: keep (used only by `example`s)
/-!
# Kollár's Examples 11, 12 and 106: coordinates and charts

Kollár's three running examples of maximal contact and of the uniqueness theorem for hypersurfaces
of maximal contact, [Kol07, Theorem 97], are computed in
`Hironaka/Resolution/Algebraic/MaximalContact/`: `Example11Charts.lean` and `Example11Stages.lean`
treat [Kol07, Example 11] (`I = (x² + y³ − z⁶)`, `m = 2`, the hypersurfaces `H = (x)` and `H' = (x +
y²)`), `Example12Charts.lean` and `Example12Stages.lean` treat [Kol07, Example 12]
(`I = (x³ + (y² − z⁶)² + z²¹)`, `m = 3`, `H = (x)` and `H' = (x + 3y² − z⁶)`), and
`Example106Charts.lean` and `Example106Stages.lean` treat [Kol07, Example 106]
(`I = (x³ − y², x⁴ + xz² − w³)`, `m = 2`, `H = (y)` and `H' = (y − x²)`). This file imports them
and records, as local notation, the coordinates of the polynomial rings, the substitutions
`σx, σy, σz, σw` giving the charts of the blow-up of the origin, the restriction `ρH` to the
hypersurface `H = (x = 0)`, and the maximal ideal `𝔪(a, b, c, d)` of a rational point; it declares
no constant of its own.

The computations in those files follow one pattern: each chart identity `σ g = vᵐ · g'` is a
polynomial identity, checked after evaluating the substitution on the variables; each order bound
`J ≤ 𝔪_p^m` is an explicit membership in a power of the maximal ideal of the `ℚ`-point `p`; each
strict bound `¬ J ≤ 𝔪_p^{m+1}` and each computation of a locus evaluates iterated partial
derivatives at `p` (an element of `𝔪_p^{k+1}` has all its `k`-th partials in `𝔪_p`, hence
vanishing at `p`) and solves the resulting rational equations by case analysis; the equalities of
derivative ideals `D`, `D²` are proved in both directions, `⊆` from the partial derivatives of
the generators and `⊇` by explicit `ℚ`-linear combinations of them.
-/

-- The module consists of `example`s only, so it declares nothing public.
set_option linter.privateModule false

open MvPolynomial

namespace Hironaka.Examples.Theorem97

/-! ### Kollár Example 11: `I = (x² + y³ − z⁶)`, `m = 2`, `H = (x)`, `H' = (x + y²)` -/

section ExampleEleven

/-- `x = X 0` in `ℚ[x, y, z]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 3) ℚ)
/-- `y = X 1` in `ℚ[x, y, z]`. -/
local notation "y" => (X 1 : MvPolynomial (Fin 3) ℚ)
/-- `z = X 2` in `ℚ[x, y, z]`. -/
local notation "z" => (X 2 : MvPolynomial (Fin 3) ℚ)
/-- The `x`-chart of the blow-up of the origin: `x ↦ x₁`, `y ↦ y₁x₁`, `z ↦ z₁x₁`. -/
local notation "σx" => (aeval ![X 0, X 1 * X 0, X 2 * X 0] :
  MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 3) ℚ)
/-- The `y`-chart: `x ↦ x₁y₁`, `y ↦ y₁`, `z ↦ z₁y₁`. -/
local notation "σy" => (aeval ![X 0 * X 1, X 1, X 2 * X 1] :
  MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 3) ℚ)
/-- The `z`-chart: `x ↦ x₁z₁`, `y ↦ y₁z₁`, `z ↦ z₁`. -/
local notation "σz" => (aeval ![X 0 * X 2, X 1 * X 2, X 2] :
  MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 3) ℚ)
/-- Restriction to `H = (x = 0)`: `x ↦ 0`, `y ↦ X 0`, `z ↦ X 1` into `ℚ[y, z]`. -/
local notation "ρH" => (aeval ![0, X 0, X 1] :
  MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ)

end ExampleEleven

/-! ### Kollár Example 12: `I = (x³ + (y² − z⁶)² + z²¹)`, `m = 3`, `H = (x)`, `H' = (x + 3y² − z⁶)`
-/

section ExampleTwelve

/-- `x = X 0` in `ℚ[x, y, z]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 3) ℚ)
/-- `y = X 1` in `ℚ[x, y, z]`. -/
local notation "y" => (X 1 : MvPolynomial (Fin 3) ℚ)
/-- `z = X 2` in `ℚ[x, y, z]`. -/
local notation "z" => (X 2 : MvPolynomial (Fin 3) ℚ)
/-- The `z`-chart: `x ↦ x₁z₁`, `y ↦ y₁z₁`, `z ↦ z₁`. -/
local notation "σz" => (aeval ![X 0 * X 2, X 1 * X 2, X 2] :
  MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 3) ℚ)
/-- Restriction to `H = (x = 0)` into `ℚ[y, z]`. -/
local notation "ρH" => (aeval ![0, X 0, X 1] :
  MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ)

end ExampleTwelve

/-! ### Kollár Example 106: `I = (x³ − y², x⁴ + xz² − w³)`, `m = 2`, `H = (y)`, `H' = (y − x²)` -/

section ExampleOneHundredSix

/-- `x = X 0` in `ℚ[x, y, z, w]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 4) ℚ)
/-- `y = X 1` in `ℚ[x, y, z, w]`. -/
local notation "y" => (X 1 : MvPolynomial (Fin 4) ℚ)
/-- `z = X 2` in `ℚ[x, y, z, w]`. -/
local notation "z" => (X 2 : MvPolynomial (Fin 4) ℚ)
/-- `w = X 3` in `ℚ[x, y, z, w]`. -/
local notation "w" => (X 3 : MvPolynomial (Fin 4) ℚ)
/-- The `x`-chart of a point blow-up: `x ↦ x₁`, `y ↦ y₁x₁`, `z ↦ z₁x₁`, `w ↦ w₁x₁`. -/
local notation "σx" => (aeval ![X 0, X 1 * X 0, X 2 * X 0, X 3 * X 0] :
  MvPolynomial (Fin 4) ℚ →ₐ[ℚ] MvPolynomial (Fin 4) ℚ)
/-- The `y`-chart. -/
local notation "σy" => (aeval ![X 0 * X 1, X 1, X 2 * X 1, X 3 * X 1] :
  MvPolynomial (Fin 4) ℚ →ₐ[ℚ] MvPolynomial (Fin 4) ℚ)
/-- The `z`-chart. -/
local notation "σz" => (aeval ![X 0 * X 2, X 1 * X 2, X 2, X 3 * X 2] :
  MvPolynomial (Fin 4) ℚ →ₐ[ℚ] MvPolynomial (Fin 4) ℚ)
/-- The `w`-chart. -/
local notation "σw" => (aeval ![X 0 * X 3, X 1 * X 3, X 2 * X 3, X 3] :
  MvPolynomial (Fin 4) ℚ →ₐ[ℚ] MvPolynomial (Fin 4) ℚ)
/-- The maximal ideal of the `ℚ`-point `(a, b, c, d)`. -/
local notation "𝔪(" a ", " b ", " c ", " d ")" =>
  Ideal.span {x - C a, y - C b, z - C c, w - C d}

end ExampleOneHundredSix

end Hironaka.Examples.Theorem97

