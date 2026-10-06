/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Model
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Membership  -- shake: keep (used only by `example`s)
import Hironaka.Scheme.BlowUp.Composite.ChartIdeal  -- shake: keep (used only by `example`s)
import Hironaka.Scheme.BlowUp.Glue.Trivial  -- shake: keep (used only by `example`s)

/-!
# Hauser's examples of blow-ups of affine schemes

Worked examples of [Hau14] on the blow-up `AlgebraicGeometry.Scheme.IdealSheafData.blowUp` and on
its affine model `affineBlowUp` (the component `blowUp.ι ⊤` of the blow-up of an affine scheme).

* (i) [Hau14, Example 4.34]: `B_{(x, y)} 𝔸²_k` has the two charts `k[x, y/x]` and `k[x/y, y]`,
  glued along `k[x, y/x][x/y]`. The chart rings are polynomial rings in two variables over `k`
  (`coordinateSubspaceEquiv`), with `y/x ↦ y` on the first chart (`coordinateSubspaceEquiv_frac`);
  the chart of `x` meets the chart of `y` in the basic open of the ratio `y/x`
  (`affineBlowUp.chart_preimage_chart`), i.e. `k[x, y/x][1/(y/x)]`. The exceptional divisor
  `ℙ¹_k` is described through its `k`-points in (iv).
* (ii) [Hau14, Example 4.29]: `B_{(g)} X = X` for a nonzerodivisor `g`. The blow-up map
  `IdealSheafData.blowUpπ (specIdealSheaf (g))` is an isomorphism (`isIso_π_of_isInvertible`), the
  ideal sheaf of `(g)` on `Spec R` being invertible; on the affine model this is
  `affineBlowUp.isIso_π_span_singleton` (`HironakaExamples/TrivialBlowUp.lean`).
* (iii) [Hau14, Examples 4.31 and 4.32], in corrected form: `B_{(g)} Spec R = Spec (R / T_g)`
  with `T_g` the `g`-power torsion, because the chart ring `R[(g)/g]` is the image of `R` in `R_g`
  with kernel `T_g` (`surjective_algebraMap_span_singleton`, `ker_algebraMap_span_singleton` in
  `HironakaExamples/TrivialBlowUp.lean`; Hauser's `V(h)` is the case `h · g = 0`, and the blow-up
  lies in `V(h)`). The example `R = k[x, y, z]/(xy, xz)`, `g = x`, `T_x = (y, z)`, where the
  blow-up is smaller than `V(h)`, is not formalized: its content is the torsion computation in the
  quotient ring, which the general kernel description already settles (`ker = ⋃ₖ Ann(gᵏ)`), and
  the equality `⋃ₖ Ann(xᵏ) = (y, z)` in that ring is a hand computation.
* (iv) ([Sta, Tag 0806]) The two `k`-points `(1 : 0)` and `(0 : 1)` of the exceptional `ℙ¹_k` of
  `B_{(x, y)} 𝔸²_k` are distinct morphisms `Spec k ⟶ B` with equal composite to `𝔸²_k`
  (`HironakaExamples/AffineBlowUpUniversal.lean`: `g₀ k ≠ g₁ k`, equal composites with
  `affineBlowUp.π`), so the blow-up map is not a monomorphism over the center.
-/

@[expose] public section

namespace Hironaka.BlowUp.Examples

open AlgebraicGeometry AlgebraicGeometry.Scheme.IdealSheafData

open AlgebraicGeometry CategoryTheory MvPolynomial Scheme.IdealSheafData
open affineBlowUpAlgebra

universe u

variable (k : Type u) [Field k]

section Charts

/-- The center `(x, y)` of the point blow-up of `𝔸²_k`, as the coordinate ideal of `S = {0, 1}`. -/
noncomputable abbrev originIdeal : Ideal (MvPolynomial (Fin 2) k) :=
  coordinateIdeal k ({0, 1} : Set (Fin 2))

theorem zero_mem_pair : (0 : Fin 2) ∈ ({0, 1} : Set (Fin 2)) := Set.mem_insert 0 _

theorem one_mem_pair : (1 : Fin 2) ∈ ({0, 1} : Set (Fin 2)) :=
  Set.mem_insert_of_mem 0 (Set.mem_singleton 1)

/-- The generator `x` of the center. -/
noncomputable abbrev genX : originIdeal k :=
  ⟨X 0, X_mem_coordinateIdeal k ({0, 1} : Set (Fin 2)) zero_mem_pair⟩

/-- The generator `y` of the center. -/
noncomputable abbrev genY : originIdeal k :=
  ⟨X 1, X_mem_coordinateIdeal k ({0, 1} : Set (Fin 2)) one_mem_pair⟩

/-- (i): the chart of `x` is the polynomial ring `k[x, y/x]`. -/
noncomputable example : affineBlowUpAlgebra (originIdeal k) (X 0) ≃ₐ[k] MvPolynomial (Fin 2) k :=
  coordinateSubspaceEquiv k ({0, 1} : Set (Fin 2)) 0

/-- (i): the chart of `y` is the polynomial ring `k[x/y, y]`. -/
noncomputable example : affineBlowUpAlgebra (originIdeal k) (X 1) ≃ₐ[k] MvPolynomial (Fin 2) k :=
  coordinateSubspaceEquiv k ({0, 1} : Set (Fin 2)) 1

/-- (i): on the chart of `x`, the fraction `y/x` is the second variable. -/
example :
    coordinateSubspaceEquiv k ({0, 1} : Set (Fin 2)) 0
      (affineBlowUpAlgebra.frac (a := X (R := k) 0)
        (X_mem_coordinateIdeal k ({0, 1} : Set (Fin 2)) one_mem_pair)) = X 1 :=
  coordinateSubspaceEquiv_frac k ({0, 1} : Set (Fin 2)) 0 one_mem_pair (by decide) _

/-- (i): the charts of `x` and `y` are glued along the basic open of the ratio `y/x` of the first
chart (`k[x, y/x][x/y]`). -/
example :
    affineBlowUp.chart (originIdeal k) (genX k) ⁻¹ᵁ
        (affineBlowUp.chart (originIdeal k) (genY k)).opensRange =
      PrimeSpectrum.basicOpen (affineBlowUpAlgebra.ratio (originIdeal k) (genX k) (genY k)) :=
  affineBlowUp.chart_preimage_chart (originIdeal k) (genX k) (genY k)

end Charts

section Trivial

variable {R : Type u} [CommRing R]

/-- (ii), Hauser's Example 4.29: blowing up `Spec R` along a nonzerodivisor `g` changes nothing:
the blow-up map is an isomorphism. -/
example (g : R) (hg : g ∈ nonZeroDivisors R) : IsIso (blowUpπ (specIdealSheaf (Ideal.span {g}))) :=
  blowUp.isIso_π_of_isInvertible _ (isInvertible_specIdealSheaf_span_singleton hg)

/-- (ii) for `𝔸¹_k` and the ideal `(x)` of the origin. -/
example : IsIso (blowUpπ (specIdealSheaf (Ideal.span {(X 0 : MvPolynomial (Fin 1) k)}))) :=
  blowUp.isIso_π_of_isInvertible _
    (isInvertible_specIdealSheaf_span_singleton (mem_nonZeroDivisors_of_ne_zero (X_ne_zero 0)))

end Trivial

end Hironaka.BlowUp.Examples
