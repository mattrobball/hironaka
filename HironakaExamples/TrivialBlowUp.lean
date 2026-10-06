/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Sheaves.Init
import HironakaExamples.BlowUp.TrivialBlowUp  -- shake: keep (used only by `example`s)

/-!
# Blowing up a principal ideal: Hauser's Examples 4.28, 4.29 and 4.31

Examples of [Hau14] on the affine model `affineBlowUp` of the blow-up of `Spec R`. The `example`s
check:

* `R[gt] ≅ R[v]` for a nonzerodivisor `g`, as graded `R`-algebras ([Hau14, Example 4.29]): the
  isomorphism `reesAlgebra.polynomialEquiv` exists, sends `v` to `g t`, and sends each monomial
  `r vⁿ` into the degree-`n` piece; over a polynomial ring `k[x]` with `g = x`.
* `B_{(g)} Spec R = Spec R` for a nonzerodivisor `g`: the blow-up map of the affine model is an
  isomorphism; over `k[x]` with `g = x` (the blow-up of the affine line at the origin, a Cartier
  divisor, is the identity, [Hau14, Example 4.28]).
* The zero-divisor case, [Hau14, Example 4.31], in corrected form. For any `g` the single chart
  ring `R[(g)/g]` is the image of `R` in `R_g`, with kernel the `g`-power torsion `T_g`, so
  `B_{(g)} Spec R = Spec (R/T_g)`; for `h g = 0` the blow-up lies in `V(h)`, which is what remains
  of Hauser's description of it as the subscheme cut out by `h`. Concrete instance: `R = k × k`,
  `g = (0, 1)`, `h = (1, 0)`, where `T_g = (h)` and the blow-up is the second point
  `V(h) = Spec k`. This is why the definition of an invertible ideal asks for a nonzerodivisor
  generator: without it the blow-up along `(g)` is the proper closed subscheme `Spec (R/T_g)`, not
  `Spec R`.

The example `R = k[x, y, z]/(xy, xz)`, `g = x`, `T_x = (y, z)`, where Hauser's `V(h)` fails, is
discussed in `HironakaExamples/BlowUp.lean`.
-/

-- The module consists of `example`s only, so it declares nothing public.
set_option linter.privateModule false

namespace Hironaka.BlowUp.Examples

open AlgebraicGeometry

open AlgebraicGeometry CategoryTheory Polynomial Hironaka.BlowUp

noncomputable section

section Rees

variable {R : Type*} [CommRing R]

/-- Hauser's Example 4.29: `R[gt] ≅ R[v]` for a nonzerodivisor `g`. -/
example (g : R) (hg : g ∈ nonZeroDivisors R) : R[X] ≃ₐ[R] reesAlgebra (Ideal.span {g}) :=
  reesAlgebra.polynomialEquiv g hg

/-- The isomorphism sends `v` to the degree-one element `g t` of the Rees algebra. -/
example (g : R) (hg : g ∈ nonZeroDivisors R) :
    reesAlgebra.polynomialEquiv g hg X =
      reesAlgebra.degreeOne (Ideal.span {g}) ⟨g, Ideal.mem_span_singleton_self g⟩ := by
  change reesAlgebra.ofPolynomial g X = _
  rw [reesAlgebra.ofPolynomial, aeval_X]

/-- "As a graded ring": `r vⁿ ↦ r gⁿ tⁿ` lands in degree `n`. -/
example (g : R) (hg : g ∈ nonZeroDivisors R) (n : ℕ) (r : R) :
    reesAlgebra.polynomialEquiv g hg (monomial n r) ∈ reesAlgebra.grading (Ideal.span {g}) n :=
  reesAlgebra.ofPolynomial_monomial_mem_grading g n r

/-- Over `k[x]`, the Rees algebra of `(x)` is a polynomial ring in one variable over `k[x]`. -/
example (k : Type*) [Field k] : (k[X])[X] ≃ₐ[k[X]] reesAlgebra (Ideal.span {(X : k[X])}) :=
  reesAlgebra.polynomialEquiv X (mem_nonZeroDivisors_of_ne_zero X_ne_zero)

end Rees

section Affine

universe u

variable {R : Type u} [CommRing R]

/-- Hauser's Example 4.29: `B_{(g)} Spec R = Spec R` for a nonzerodivisor `g`. -/
example (g : R) (hg : g ∈ nonZeroDivisors R) : IsIso (affineBlowUp.π (Ideal.span {g})) :=
  affineBlowUp.isIso_π_span_singleton g hg

/-- Hauser's Example 4.28: the blow-up of the affine line at the origin, the Cartier divisor
`(x)`, is the identity. -/
example (k : Type u) [Field k] : IsIso (affineBlowUp.π (Ideal.span {(X : k[X])})) :=
  affineBlowUp.isIso_π_span_singleton X (mem_nonZeroDivisors_of_ne_zero X_ne_zero)

/-- The chart ring `R[(g)/g]` is `R` for a nonzerodivisor `g`. -/
example (g : R) (hg : g ∈ nonZeroDivisors R) :
    Function.Bijective (algebraMap R (affineBlowUpAlgebra (Ideal.span {g}) g)) :=
  affineBlowUpAlgebra.bijective_algebraMap_span_singleton g hg

/-- Hauser's Example 4.31, corrected: for any `g`, the single chart ring is the image of `R` in
`R_g`, with kernel the `g`-power torsion: `B_{(g)} Spec R = Spec (R/T_g)`. -/
example (g : R) : Function.Surjective (algebraMap R (affineBlowUpAlgebra (Ideal.span {g}) g)) :=
  affineBlowUpAlgebra.surjective_algebraMap_span_singleton g

example (g r : R) :
    r ∈ RingHom.ker (algebraMap R (affineBlowUpAlgebra (Ideal.span {g}) g)) ↔
      ∃ n : ℕ, g ^ n * r = 0 :=
  affineBlowUpAlgebra.mem_ker_algebraMap_span_singleton_iff g r

/-- Hauser's Example 4.31, the part that remains: for `h g = 0` the blow-up lies in `V(h)`. -/
example (g h : R) (hgh : h * g = 0) :
    algebraMap R (affineBlowUpAlgebra (Ideal.span {g}) g) h = 0 :=
  affineBlowUpAlgebra.algebraMap_span_singleton_eq_zero_of_mul_eq_zero g hgh

/-- Concrete zero-divisor instance: `R = k × k`, `g = (0, 1)`, `h = (1, 0)`, `h g = 0`; the
blow-up along `(g)` lies in `V(h)`, the second point (and equals it, `T_g = (h)`). -/
example (k : Type u) [Field k] :
    algebraMap (k × k) (affineBlowUpAlgebra (Ideal.span {((0 : k), (1 : k))}) ((0 : k), (1 : k)))
      ((1 : k), (0 : k)) = 0 :=
  affineBlowUpAlgebra.algebraMap_span_singleton_eq_zero_of_mul_eq_zero _ (by ext <;> simp)

end Affine

end

end Hironaka.BlowUp.Examples
