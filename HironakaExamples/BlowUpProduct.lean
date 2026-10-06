/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.CategoryTheory.Iso
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Sheaves.Init
import Hironaka.Scheme.BlowUp.Glue.Product  -- shake: keep (used only by `example`s)
import Mathlib.Algebra.MvPolynomial.CommRing  -- shake: keep (used only by `example`s)
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Admissible
import Hironaka.Scheme.BlowUp.ProductCenter

/-!
# Hauser's examples of blowing up a product ideal

Two examples of [Hau14] in which the blow-up of a product ideal is read as an iterated blow-up,
through `blowUp.exists_mulIso` (the blow-up of `I · J` is, canonically, the blow-up of `I`
followed by the blow-up of the inverse image of `J`) for the blow-up
`AlgebraicGeometry.Scheme.IdealSheafData.blowUp`.

* [Hau14, Example 4.50] asks to interpret the blow-up of `𝔸²` in the ideal `(x, y²)(x, y)` as a
  composite of blow-ups in regular centers. The blow-up of `𝔸²_k` in `(x, y²)(x, y)` is the point
  blow-up (center `(x, y)`) followed by the blow-up of the inverse image of `(x, y²)`, canonically
  over `𝔸²_k`.
* [Hau14, Example 4.66]: the zero set in `𝔸³` of the non-reduced ideal `(x, yz)(x, y)(x, z)`,
  printed there as `(x³, x²y, x²z, xyz, y²z)`, is the union of the `y`- and the `z`-axis, and
  Hauser describes its blow-up as the composite of the blow-up with center `(x, yz)` and a point
  blow-up of the resulting threefold `W₁` at its singular point. The blow-up of `𝔸³_k` in
  `(x, yz)(x, y)(x, z)` is the blow-up with center `(x, yz)` followed by the blow-up of the inverse
  image of `(x, y)(x, z)`; Hauser's
  identification of that second blow-up with the point blow-up of the singular point of `W₁` is
  taken up in `HironakaExamples/BlowUpComposite.lean`. A remark on the printed generators, not
  checked in Lean (the `MvPolynomial` ideal computation is too expensive for the elaborator):
  expanding the eight products of generators gives `(x, yz)(x, y)(x, z) = (x³, x²y, x²z, xyz,
  y²z²)`, and Hauser's printed last generator `y²z` is not in the product (its degree-`3` part is
  spanned by `x³, x²y, x²z, xyz`, all divisible by `x`); the zero set `V(x, yz)` is the same either
  way.

Ideals of `k[x, y, z]` are read as ideal sheaves on `𝔸ⁿ_k = Spec k[x₁, …, xₙ]` through
`specIdealSheaf`, which is multiplicative (`specIdealSheaf_mul`).
-/

@[expose] public section

namespace Hironaka.BlowUp.Examples

open AlgebraicGeometry AlgebraicGeometry.Scheme.IdealSheafData

open AlgebraicGeometry CategoryTheory MvPolynomial Scheme.IdealSheafData

universe u

variable (k : Type u) [Field k]

section Hauser450

/-- The origin of `𝔸²_k`, the center `(x, y)` of the point blow-up. -/
noncomputable abbrev origin2 : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {X 0, X 1}

/-- The center `(x, y²)` of Hauser Ex. 4.50. -/
noncomputable abbrev cusp2 : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {X 0, X 1 ^ 2}

/-- Hauser's Example 4.50: the blow-up of `𝔸²_k` in `(x, y²)(x, y)` is, canonically over `𝔸²_k`,
the point blow-up followed by the blow-up of the inverse image of `(x, y²)`. -/
example :
    ∃ e : blowUp ((specIdealSheaf (cusp2 k)).comap (blowUpπ (specIdealSheaf (origin2 k)))) ≅
        blowUp (specIdealSheaf (cusp2 k * origin2 k)),
      e.hom ≫ blowUpπ (specIdealSheaf (cusp2 k * origin2 k)) =
        blowUpπ ((specIdealSheaf (cusp2 k)).comap (blowUpπ (specIdealSheaf (origin2 k)))) ≫
          blowUpπ (specIdealSheaf (origin2 k)) := by
  rw [specIdealSheaf_mul, mul_comm]
  obtain ⟨e, he, -⟩ :=
    blowUp.exists_mulIso (specIdealSheaf (origin2 k)) (specIdealSheaf (cusp2 k))
  exact ⟨e, he⟩

end Hauser450

section Hauser466

/-- The center `(x, yz)` of the first blow-up of Hauser Ex. 4.66. -/
noncomputable abbrev center1 : Ideal (MvPolynomial (Fin 3) k) := Ideal.span {X 0, X 1 * X 2}

/-- The `z`-axis `(x, y)` of `𝔸³_k`. -/
noncomputable abbrev zAxis : Ideal (MvPolynomial (Fin 3) k) := Ideal.span {X 0, X 1}

/-- The `y`-axis `(x, z)` of `𝔸³_k`. -/
noncomputable abbrev yAxis : Ideal (MvPolynomial (Fin 3) k) := Ideal.span {X 0, X 2}

/-- Hauser's Example 4.66: the blow-up of `𝔸³_k` in `(x, yz)(x, y)(x, z)` is, canonically over
`𝔸³_k`, the blow-up with center `(x, yz)` followed by the blow-up of the inverse image of
`(x, y)(x, z)`. -/
example :
    ∃ e : blowUp ((specIdealSheaf (zAxis k * yAxis k)).comap
          (blowUpπ (specIdealSheaf (center1 k)))) ≅
        blowUp (specIdealSheaf (center1 k * zAxis k * yAxis k)),
      e.hom ≫ blowUpπ (specIdealSheaf (center1 k * zAxis k * yAxis k)) =
        blowUpπ ((specIdealSheaf (zAxis k * yAxis k)).comap
          (blowUpπ (specIdealSheaf (center1 k)))) ≫ blowUpπ (specIdealSheaf (center1 k)) := by
  rw [mul_assoc, specIdealSheaf_mul (center1 k) (zAxis k * yAxis k)]
  obtain ⟨e, he, -⟩ :=
    blowUp.exists_mulIso (specIdealSheaf (center1 k)) (specIdealSheaf (zAxis k * yAxis k))
  exact ⟨e, he⟩

end Hauser466

end Hironaka.BlowUp.Examples
