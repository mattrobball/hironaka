/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import HironakaExamples.BlowUpProduct
public import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Admissible
import Hironaka.Scheme.BlowUp.Composite.ChartIdeal
import Hironaka.Scheme.BlowUp.ProductCenter
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Hironaka.Scheme.BlowUp.Composite.Iso

/-!
# Hauser's Example 4.66: a blow-up of `𝔸³` as the composite of two blow-ups

[Hau14, Example 4.66] describes the blow-up of `𝔸³` with center the non-reduced ideal
`(x, yz)(x, y)(x, z)` as the composite of two blow-ups: the first with center `(x, yz)`, the
second "the point blow-up of `W₁` with center this singular point", `W₁` the threefold the first
produces. This file reads the statement through the two-step theorem `blowUp.exists_comp_iso`
for the blow-up `AlgebraicGeometry.Scheme.IdealSheafData.blowUp`: the
composite of the blow-up of `𝔸³_k` with center `(x, yz)` and the blow-up of the inverse image of
`(x, y)(x, z)` is a single blow-up of `𝔸³_k`, canonically over `𝔸³_k`, whose center is supported
on `V(x, yz)`, the union of the `y`- and `z`-axes: the image of the second center lies in
`V((x, y)(x, z)) = V(x, y) ∪ V(x, z) ⊆ V(x, yz)`. Hauser's identification of the inverse image of
`(x, y)(x, z)` with the ideal of the singular point of `W₁`, up to the exceptional factor, is a
chart computation that this file does not check. The centers `center1 = (x, yz)`,
`zAxis = (x, y)`, `yAxis = (x, z)` are those of `HironakaExamples/BlowUpProduct.lean`.
-/

public section

namespace Hironaka.BlowUp.Examples

open AlgebraicGeometry AlgebraicGeometry.Scheme.IdealSheafData

open AlgebraicGeometry CategoryTheory MvPolynomial Scheme.IdealSheafData

universe u

variable (k : Type u) [Field k]

/-- `(x, yz) ⊆ (x, y)`: the `z`-axis lies in `V(x, yz)`. -/
theorem center1_le_zAxis : center1 k ≤ zAxis k :=
  Ideal.span_le.mpr (Set.insert_subset_iff.mpr ⟨Ideal.subset_span (Set.mem_insert _ _),
    Set.singleton_subset_iff.mpr (Ideal.mul_mem_right _ _
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))⟩)

/-- `(x, yz) ⊆ (x, z)`: the `y`-axis lies in `V(x, yz)`. -/
theorem center1_le_yAxis : center1 k ≤ yAxis k :=
  Ideal.span_le.mpr (Set.insert_subset_iff.mpr ⟨Ideal.subset_span (Set.mem_insert _ _),
    Set.singleton_subset_iff.mpr (Ideal.mul_mem_left _ _
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))⟩)

/-- `V((x, y)(x, z)) ⊆ V(x, yz)` as sets: `support` is antitone and `specIdealSheaf` is
multiplicative and order-reflecting. -/
theorem support_axes_subset :
    ((specIdealSheaf (zAxis k * yAxis k)).support : Set (Spec (.of (MvPolynomial (Fin 3) k)))) ⊆
      (specIdealSheaf (center1 k)).support := by
  rw [specIdealSheaf_mul, support_mul, TopologicalSpace.Closeds.coe_sup]
  exact Set.union_subset
    (support_antitone ((specIdealSheaf_le_iff _ _).mpr (center1_le_zAxis k)))
    (support_antitone ((specIdealSheaf_le_iff _ _).mpr (center1_le_yAxis k)))

/-- Hauser's Example 4.66: the blow-up of `𝔸³_k` with center `(x, yz)` followed by the blow-up of
the inverse image of `(x, y)(x, z)` is, canonically over `𝔸³_k`, a single blow-up of `𝔸³_k`, with
center supported on `V(x, yz)`, the union of the two axes. -/
example :
    ∃ K : (Spec (.of (MvPolynomial (Fin 3) k))).IdealSheafData,
      (K.support : Set (Spec (.of (MvPolynomial (Fin 3) k)))) =
        (specIdealSheaf (center1 k)).support ∧
      ∃ e : blowUp ((specIdealSheaf (zAxis k * yAxis k)).comap
            (blowUpπ (specIdealSheaf (center1 k)))) ≅ blowUp K,
        e.hom ≫ blowUpπ K =
          blowUpπ ((specIdealSheaf (zAxis k * yAxis k)).comap
            (blowUpπ (specIdealSheaf (center1 k)))) ≫ blowUpπ (specIdealSheaf (center1 k)) := by
  obtain ⟨K, hK, e, he, -⟩ := blowUp.exists_comp_iso (specIdealSheaf (center1 k))
    ((specIdealSheaf (zAxis k * yAxis k)).comap (blowUpπ (specIdealSheaf (center1 k))))
  refine ⟨K, ?_, e, he⟩
  rw [hK, support_comap]
  exact Set.union_eq_left.mpr
    ((Set.image_preimage_subset _ _).trans (support_axes_subset k))

end Hironaka.BlowUp.Examples
