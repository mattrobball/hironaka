/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Model
public import Hironaka.Scheme.BlowUp.AffineBlowUp.Chart
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Existence  -- shake: keep (used only by `example`s)
import Hironaka.Scheme.BlowUp.AffineBlowUp.Exceptional
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Uniqueness
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Membership

/-!
# The universal property of the affine blow-up in Hauser's Example 4.34

Let `B = B_{(x,y)} 𝔸²_k = affineBlowUp (x, y)` over `k[x, y] = MvPolynomial (Fin 2) k` be the
blow-up of the plane at the origin, [Hau14, Example 4.34] (see also [Sta, Tag 0806]).

* (i) The two `k`-points `(1 : 0)` and `(0 : 1)` of the exceptional `ℙ¹` over the origin (the
  points `x = 0, y/x = 0` of the chart `Spec k[x, y/x]` and `y = 0, x/y = 0` of the chart
  `Spec k[x/y, y]`) are distinct morphisms `Spec k ⟶ B` with the same composite to `𝔸²_k` (the
  origin). So uniqueness of lifts fails without admissibility: `Spec k → 𝔸²` at the origin pulls
  `(x, y)` back to `0`, which is not invertible. Distinctness: a common value would lie in both
  charts, hence in `D(y/x) ⊆ Spec k[x, y/x]`, but the point `(1 : 0)` has `y/x = 0`.
* (ii) The chart map `chart x ≫ π : Spec k[x, y/x] ⟶ 𝔸²_k` is admissible (its inverse image of
  `(x, y)` is the exceptional ideal on the chart, `(x)` with `x` a nonzerodivisor) and the chart
  immersion is its unique lift.

The `k`-points are built from the isomorphism `k[x, y][(x, y)/x] ≅ k[x, y]`
(`coordinateSubspaceEquiv`), `x ↦ x`, `y/x ↦ y`, composed with evaluation at the origin.
-/

@[expose] public section

namespace Hironaka.BlowUp.Examples

open AlgebraicGeometry

open AlgebraicGeometry CategoryTheory MvPolynomial Scheme.IdealSheafData
open affineBlowUpAlgebra

universe u

variable (k : Type u) [Field k]

/-- The center `(x, y) ⊆ k[x, y]`, as the coordinate ideal of the subset `{0, 1}`. -/
noncomputable abbrev center : Ideal (MvPolynomial (Fin 2) k) :=
  coordinateIdeal k ({0, 1} : Set (Fin 2))

example : center k = Ideal.span {X 0, X 1} := by
  rw [center, coordinateIdeal, Set.image_pair]

/-- `x ∈ (x, y)`. -/
noncomputable abbrev x₀ : center k := ⟨X 0, X_mem_coordinateIdeal k _ (by simp)⟩
/-- `y ∈ (x, y)`. -/
noncomputable abbrev x₁ : center k := ⟨X 1, X_mem_coordinateIdeal k _ (by simp)⟩

/-- Evaluation at the origin. -/
noncomputable abbrev evalOrigin : MvPolynomial (Fin 2) k →ₐ[k] k := aeval fun _ => 0

/-- The chart isomorphism `k[x, y][(x, y)/x] ≅ k[x, y]`, `x ↦ x`, `y/x ↦ y`. -/
noncomputable abbrev e₀ := coordinateSubspaceEquiv k ({0, 1} : Set (Fin 2)) 0
/-- The chart isomorphism `k[x, y][(x, y)/y] ≅ k[x, y]`, `y ↦ y`, `x/y ↦ x`. -/
noncomputable abbrev e₁ := coordinateSubspaceEquiv k ({0, 1} : Set (Fin 2)) 1

/-- The `k`-point `(1 : 0)`: `x = 0`, `y/x = 0` in the chart `k[x, y/x] ≅ k[x, y]`. -/
noncomputable def pt₀ : affineBlowUpAlgebra (center k) (X 0) →+* k :=
  (evalOrigin k : MvPolynomial (Fin 2) k →+* k).comp (e₀ k : _ →+* MvPolynomial (Fin 2) k)

/-- The `k`-point `(0 : 1)`: `y = 0`, `x/y = 0` in the chart `k[x/y, y] ≅ k[x, y]`. -/
noncomputable def pt₁ : affineBlowUpAlgebra (center k) (X 1) →+* k :=
  (evalOrigin k : MvPolynomial (Fin 2) k →+* k).comp (e₁ k : _ →+* MvPolynomial (Fin 2) k)

theorem pt₀_apply (z : affineBlowUpAlgebra (center k) (X 0)) :
    pt₀ k z = evalOrigin k (e₀ k z) := rfl

theorem pt₁_apply (z : affineBlowUpAlgebra (center k) (X 1)) :
    pt₁ k z = evalOrigin k (e₁ k z) := rfl

/-- Both `k`-points restrict to evaluation at the origin on `k[x, y]`. -/
theorem pt₀_comp_algebraMap :
    (pt₀ k).comp (algebraMap (MvPolynomial (Fin 2) k) (affineBlowUpAlgebra (center k) (X 0))) =
      (evalOrigin k : MvPolynomial (Fin 2) k →+* k) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp only [RingHom.comp_apply, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
      pt₀_apply, AlgEquiv.commutes, RingHom.coe_coe, AlgHom.commutes]
  · fin_cases i
    · rw [RingHom.comp_apply, pt₀_apply]
      change evalOrigin k (e₀ k (algebraMap _ _ (X (0 : Fin 2)))) = evalOrigin k (X 0)
      rw [coordinateSubspaceEquiv_algebraMap_X_of_not k ({0, 1} : Set (Fin 2)) 0 (by simp)]
    · rw [RingHom.comp_apply, pt₀_apply]
      change evalOrigin k (e₀ k (algebraMap _ _ (X (1 : Fin 2)))) = evalOrigin k (X 1)
      rw [coordinateSubspaceEquiv_algebraMap_X_of_mem k ({0, 1} : Set (Fin 2)) 0 (by simp)
        (by decide)]
      simp

theorem pt₁_comp_algebraMap :
    (pt₁ k).comp (algebraMap (MvPolynomial (Fin 2) k) (affineBlowUpAlgebra (center k) (X 1))) =
      (evalOrigin k : MvPolynomial (Fin 2) k →+* k) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp only [RingHom.comp_apply, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
      pt₁_apply, AlgEquiv.commutes, RingHom.coe_coe, AlgHom.commutes]
  · fin_cases i
    · rw [RingHom.comp_apply, pt₁_apply]
      change evalOrigin k (e₁ k (algebraMap _ _ (X (0 : Fin 2)))) = evalOrigin k (X 0)
      rw [coordinateSubspaceEquiv_algebraMap_X_of_mem k ({0, 1} : Set (Fin 2)) 1 (by simp)
        (by decide)]
      simp
    · rw [RingHom.comp_apply, pt₁_apply]
      change evalOrigin k (e₁ k (algebraMap _ _ (X (1 : Fin 2)))) = evalOrigin k (X 1)
      rw [coordinateSubspaceEquiv_algebraMap_X_of_not k ({0, 1} : Set (Fin 2)) 1 (by simp)]

/-- The point `(1 : 0)` has `y/x = 0`. -/
theorem pt₀_ratio : pt₀ k (ratio (center k) (x₀ k) (x₁ k)) = 0 := by
  have h : ratio (center k) (x₀ k) (x₁ k) = frac (a := X 0) (x₁ k).2 :=
    Subtype.ext (coe_frac_eq_awayFrac _).symm
  rw [h, pt₀_apply, coordinateSubspaceEquiv_frac k ({0, 1} : Set (Fin 2)) 0 (by simp) (by decide)]
  simp

/-- The two `k`-points as morphisms `Spec k ⟶ B`. -/
noncomputable abbrev g₀ : Spec (.of k) ⟶ affineBlowUp (center k) :=
  Spec.map (CommRingCat.ofHom (pt₀ k)) ≫ affineBlowUp.chart (center k) (x₀ k)

noncomputable abbrev g₁ : Spec (.of k) ⟶ affineBlowUp (center k) :=
  Spec.map (CommRingCat.ofHom (pt₁ k)) ≫ affineBlowUp.chart (center k) (x₁ k)

/-- (i), same composite: both points lie over the origin. -/
example : g₀ k ≫ affineBlowUp.π (center k) = g₁ k ≫ affineBlowUp.π (center k) := by
  rw [Category.assoc, Category.assoc, affineBlowUp.chart_π, affineBlowUp.chart_π, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  exact (pt₀_comp_algebraMap k).trans (pt₁_comp_algebraMap k).symm

/-- The closed point of `Spec k`. -/
noncomputable abbrev origin : Spec (.of k) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)

/-- (i), distinct: a common value would lie in `D(y/x) ⊆ Spec k[x, y/x]`, but `y/x` vanishes at
`(1 : 0)`. -/
example : g₀ k ≠ g₁ k := by
  intro h
  have hmem : g₀ k (origin k) ∈ (affineBlowUp.chart (center k) (x₁ k)).opensRange := by
    rw [h]
    exact ⟨_, rfl⟩
  rw [Scheme.Hom.comp_apply, ← Scheme.Hom.mem_preimage, affineBlowUp.chart_preimage_chart] at hmem
  refine (PrimeSpectrum.mem_basicOpen _ _).mp hmem ?_
  change ratio (center k) (x₀ k) (x₁ k) ∈
    (PrimeSpectrum.comap (pt₀ k) (origin k)).asIdeal
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, pt₀_ratio]
  exact Ideal.zero_mem _

/-- (ii): the chart map is admissible and the chart is its unique lift. -/
example : ((specIdealSheaf (center k)).comap
      (affineBlowUp.chart (center k) (x₀ k) ≫ affineBlowUp.π (center k))).IsInvertible ∧
    ∀ g : Spec (.of (affineBlowUpAlgebra (center k) (X 0))) ⟶ affineBlowUp (center k),
      g ≫ affineBlowUp.π (center k) =
        affineBlowUp.chart (center k) (x₀ k) ≫ affineBlowUp.π (center k) →
      g = affineBlowUp.chart (center k) (x₀ k) := by
  have hinv : ((specIdealSheaf (center k)).comap
      (affineBlowUp.chart (center k) (x₀ k) ≫ affineBlowUp.π (center k))).IsInvertible := by
    rw [Scheme.IdealSheafData.comap_comp]
    change ((affineBlowUp.exceptionalIdeal (center k)).comap _).IsInvertible
    rw [affineBlowUp.comap_exceptionalIdeal_chart, Ideal.map_span, Set.image_singleton]
    exact isInvertible_ofIdealTop_span_singleton
      (affineBlowUp.chartGenerator_mem_nonZeroDivisors (center k) (x₀ k))
  exact ⟨hinv, fun g hg => affineBlowUp.hom_ext (center k) _ hinv g _ hg rfl⟩

end Hironaka.BlowUp.Examples
