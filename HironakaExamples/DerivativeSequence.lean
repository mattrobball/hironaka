/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.TransformDeriv
import Hironaka.Algebra.Local.Transform
import Hironaka.Algebra.Local.TransformLogDeriv

/-!
# The derivative ideal under one blow-up: the cusp `x² + y³`

For `X = 𝔸²`, `I = (x² + y³)`, `m = 2`, the blow-up of the origin and `j = 1` (a plane-curve
instance in the spirit of [Kol07, Example 11]): `D(I) = (x, y²)`; in the chart `x = x₁ y₁`,
`y = y₁` of the blow-up, `I₁ = π_*^{-1}(I, 2) = (x₁² + y₁)`, `J₁ = π_*^{-1}(D(I), 1) = (x₁, y₁)`,
and `D(I₁) = (x₁² + y₁, x₁, 1) = (1)`; so `J₁ ⊆ D(I₁)`, which is [Kol07, Theorem 76]
(`Π_*^{-1}(D^j(I, m)) ⊆ D^j Π_*^{-1}(I, m)`) for one blow-up and `j = 1`, and the inclusion is
strict.

The computation is done on the local model of the blow-up at the origin: `R` a regular local
`ℚ`-algebra with a two-dimensional coordinate system `c` (`x₀ = x`, `x₁ = y`), the center
`P = chartCenter c.x 1 = (x₀, x₁)`, the chart ring `R' = R[x₀/x₁]` of the coordinate `x₁`
(`y₀ = x₀/x₁` is Kollár's `x₁`, and `x₁` his `y₁`), the coordinate derivative `c.D` on `R` and
the derivative `c.chartD 1` of the chart with respect to the transformed derivations `∂'ⱼ`. The
transform `π_*^{-1}(x₀² + x₁³, 2) = y₀² + x₁` is `transformElem_sq_add_cube`.
-/

@[expose] public section

namespace Hironaka.Local.Examples.DerivativeSequence

open IsLocalRing

open IsLocalRing Ideal

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] (c : RegularCoords R 2)

/-- `∂₀(x₀² + x₁³) = 2 x₀`. -/
theorem pderiv_zero_sq_add_cube : c.pderiv 0 (c.x 0 ^ 2 + c.x 1 ^ 3) = 2 * c.x 0 := by
  rw [map_add, Derivation.leibniz_pow, Derivation.leibniz_pow, c.pderiv_x, c.pderiv_x]
  simp

/-- `∂₁(x₀² + x₁³) = 3 x₁²`. -/
theorem pderiv_one_sq_add_cube : c.pderiv 1 (c.x 0 ^ 2 + c.x 1 ^ 3) = 3 * c.x 1 ^ 2 := by
  rw [map_add, Derivation.leibniz_pow, Derivation.leibniz_pow, c.pderiv_x, c.pderiv_x]
  simp

/-- `∂ᵢ(x₀² + x₁³) ∈ (x₀, x₁²)` for both coordinates. -/
theorem pderiv_sq_add_cube_mem (i : Fin 2) :
    c.pderiv i (c.x 0 ^ 2 + c.x 1 ^ 3) ∈ span {c.x 0, c.x 1 ^ 2} := by
  have h0 : c.x 0 ∈ span {c.x 0, c.x 1 ^ 2} := subset_span (Set.mem_insert _ _)
  have h1 : c.x 1 ^ 2 ∈ span {c.x 0, c.x 1 ^ 2} := subset_span (Set.mem_insert_of_mem _ rfl)
  revert i
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · rw [pderiv_zero_sq_add_cube]
    exact mul_mem_left _ _ h0
  · rw [pderiv_one_sq_add_cube]
    exact mul_mem_left _ _ h1

/-- `x₀² + x₁³ ∈ (x₀, x₁²)`. -/
theorem sq_add_cube_mem : c.x 0 ^ 2 + c.x 1 ^ 3 ∈ span {c.x 0, c.x 1 ^ 2} := by
  have h0 : c.x 0 ∈ span {c.x 0, c.x 1 ^ 2} := subset_span (Set.mem_insert _ _)
  have h1 : c.x 1 ^ 2 ∈ span {c.x 0, c.x 1 ^ 2} := subset_span (Set.mem_insert_of_mem _ rfl)
  refine add_mem (pow_mem_of_mem _ h0 2 two_pos) ?_
  rw [show c.x 1 ^ 3 = c.x 1 ^ 2 * c.x 1 from pow_succ _ _]
  exact mul_mem_right _ _ h1

/-- `D(x² + y³) = (x, y²)` (characteristic zero: `2` and `3` are units). -/
theorem D_sq_add_cube : c.D (span {c.x 0 ^ 2 + c.x 1 ^ 3}) = span {c.x 0, c.x 1 ^ 2} := by
  refine le_antisymm (c.D_le_iff.mpr ⟨span_le.mpr ?_, fun i g hg => ?_⟩) (span_le.mpr ?_)
  · rintro _ rfl
    exact sq_add_cube_mem c
  · obtain ⟨a, rfl⟩ := mem_span_singleton'.mp hg
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem_left _ _ (pderiv_sq_add_cube_mem c i))
      (mul_mem_right _ _ (sq_add_cube_mem c))
  · have h2 : (2 : R) * algebraMap ℚ R (1 / 2) = 1 := by
      rw [← map_ofNat (algebraMap ℚ R) 2, ← map_mul]
      norm_num
    have h3 : (3 : R) * algebraMap ℚ R (1 / 3) = 1 := by
      rw [← map_ofNat (algebraMap ℚ R) 3, ← map_mul]
      norm_num
    rintro _ (rfl | rfl)
    · have hx : c.x 0 = c.pderiv 0 (c.x 0 ^ 2 + c.x 1 ^ 3) * algebraMap ℚ R (1 / 2) := by
        rw [pderiv_zero_sq_add_cube, mul_right_comm, h2, one_mul]
      have hmem := mul_mem_right (algebraMap ℚ R (1 / 2)) _
        (c.pderiv_mem_D (subset_span (Set.mem_singleton (c.x 0 ^ 2 + c.x 1 ^ 3))) 0)
      rwa [← hx] at hmem
    · have hx : c.x 1 ^ 2 = c.pderiv 1 (c.x 0 ^ 2 + c.x 1 ^ 3) * algebraMap ℚ R (1 / 3) := by
        rw [pderiv_one_sq_add_cube, mul_right_comm, h3, one_mul]
      have hmem := mul_mem_right (algebraMap ℚ R (1 / 3)) _
        (c.pderiv_mem_D (subset_span (Set.mem_singleton (c.x 0 ^ 2 + c.x 1 ^ 3))) 1)
      rwa [← hx] at hmem

/-- `x₀ ∈ P` and `x₁² ∈ P`. -/
theorem x_zero_mem_chartCenter : c.x 0 ∈ chartCenter c.x 1 :=
  x_mem_chartCenter c.x 1 (Fin.zero_le _)

theorem x_one_sq_mem_chartCenter : c.x 1 ^ 2 ∈ chartCenter c.x 1 := by
  rw [sq]; exact mul_mem_left _ _ (x_mem_chartCenter c.x 1 le_rfl)

/-- `π_*^{-1}(x₀, 1) = y₀`. -/
theorem transformElem_x_zero :
    transformElem (m := 1) c.x 1 (c.x 0) (by rw [pow_one]; exact x_zero_mem_chartCenter c) =
      chartYR c.x 1 0 := by
  symm
  apply eq_transformElem_of_pow_mul_eq
  rw [pow_one, ← algebraMap_x_eq_mul_chartYR c.x 1 (show (0 : Fin 2) < 1 by decide)]

/-- `π_*^{-1}(x₁², 1) = x₁`. -/
theorem transformElem_x_one_sq :
    transformElem (m := 1) c.x 1 (c.x 1 ^ 2) (by rw [pow_one]; exact x_one_sq_mem_chartCenter c) =
      algebraMap R (chartRing c.x 1) (c.x 1) := by
  symm
  apply eq_transformElem_of_pow_mul_eq
  rw [pow_one, ← map_mul, sq]

/-- `J₁ = π_*^{-1}((x, y²), 1) = (x₁, y₁)`; in the model, `(y₀, x₁)`. -/
theorem transformIdeal_D_sq_add_cube :
    transformIdeal c.x 1 (span {c.x 0, c.x 1 ^ 2}) 1 =
      span {chartYR c.x 1 0, algebraMap R (chartRing c.x 1) (c.x 1)} := by
  have hP : span {c.x 0, c.x 1 ^ 2} ≤ chartCenter c.x 1 ^ 1 := by
    rw [pow_one]
    exact span_le.mpr (by rintro _ (rfl | rfl) <;> [exact x_zero_mem_chartCenter c;
      exact x_one_sq_mem_chartCenter c])
  refine le_antisymm (c.transformIdeal_le_of_le_transformPreimage 1 hP ?_) (span_le.mpr ?_)
  · rw [span_le]
    rintro _ (rfl | rfl)
    · refine ⟨by rw [pow_one]; exact x_zero_mem_chartCenter c, ?_⟩
      rw [transformElem_x_zero]
      exact subset_span (Set.mem_insert _ _)
    · refine ⟨by rw [pow_one]; exact x_one_sq_mem_chartCenter c, ?_⟩
      rw [transformElem_x_one_sq]
      exact subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · rintro _ (rfl | rfl)
    · rw [SetLike.mem_coe, ← transformElem_x_zero c]
      exact transformElem_mem_transformIdeal c.x 1 (subset_span (Set.mem_insert _ _)) _
    · rw [SetLike.mem_coe, ← transformElem_x_one_sq c]
      exact transformElem_mem_transformIdeal c.x 1
        (subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton (c.x 1 ^ 2)))) _

/-- `I₁ = π_*^{-1}((x² + y³), 2) = (x₁² + y₁)`; in the model, `(y₀² + x₁)`. -/
theorem transformIdeal_sq_add_cube :
    transformIdeal c.x 1 (span {c.x 0 ^ 2 + c.x 1 ^ 3}) 2 =
      span {chartYR c.x 1 0 ^ 2 + algebraMap R (chartRing c.x 1) (c.x 1)} := by
  have hf := sq_add_cube_mem_chartCenter_sq c.x
  have hP : span {c.x 0 ^ 2 + c.x 1 ^ 3} ≤ chartCenter c.x 1 ^ 2 :=
    span_le.mpr (by rintro _ rfl; exact hf)
  refine le_antisymm (c.transformIdeal_le_of_le_transformPreimage 1 hP ?_) (span_le.mpr ?_)
  · rw [span_le]
    rintro _ rfl
    refine ⟨hf, ?_⟩
    rw [transformElem_sq_add_cube c.x hf]
    exact subset_span (Set.mem_singleton _)
  · rintro _ rfl
    rw [SetLike.mem_coe, ← transformElem_sq_add_cube c.x hf]
    exact transformElem_mem_transformIdeal c.x 1 (subset_span (Set.mem_singleton _)) hf

/-- `∂'₁(y₀² + x₁) = 1` in the chart ring. -/
theorem chartDerivRing_one_transform :
    c.chartDerivRing 1 1 (chartYR c.x 1 0 ^ 2 + algebraMap R (chartRing c.x 1) (c.x 1)) = 1 := by
  apply Subtype.ext
  rw [RegularCoords.coe_chartDerivRing, Subalgebra.coe_add, Subalgebra.coe_pow, coe_chartYROf,
    Subalgebra.coe_algebraMap, ← chartYOf_self c.x 1 (c.x 1), map_add, Derivation.leibniz_pow]
  change 2 • chartY c.x 1 0 ^ (2 - 1) • c.chartDeriv 1 1 (chartY c.x 1 0) +
    c.chartDeriv 1 1 (chartY c.x 1 1) = 1
  rw [c.chartDeriv_chartY, c.chartDeriv_chartY]
  simp

/-- `D'(I₁) = (x₁² + y₁, x₁, 1) = (1)`. -/
theorem chartD_transform_sq_add_cube :
    c.chartD 1 (span {chartYR c.x 1 0 ^ 2 + algebraMap R (chartRing c.x 1) (c.x 1)}) = ⊤ := by
  rw [eq_top_iff_one, ← chartDerivRing_one_transform c]
  exact c.chartDerivRing_mem_chartD 1 (subset_span (Set.mem_singleton _)) 1

/-- `J₁ = (y₀, x₁)` is a proper ideal: it lies in the origin of the chart. -/
theorem span_transform_ne_top :
    span {chartYR c.x 1 0, algebraMap R (chartRing c.x 1) (c.x 1)} ≠ ⊤ := by
  rw [ne_top_iff_one]
  intro h
  refine one_notMem_chartOrigin c.x 1 c.span_x c.card (span_le.mpr ?_ h)
  rintro _ (rfl | rfl)
  · exact chartYROf_mem_chartOriginOf c.x 1 (c.x 1) 0
  · exact algebraMap_x_mem_chartOrigin c.x 1 1

/-- `J₁ ⊆ D'(I₁)`, [Kol07, Theorem 76] for one blow-up at `j = 1` on the cusp, and the inclusion
is strict. -/
example :
    transformIdeal c.x 1 (c.D (span {c.x 0 ^ 2 + c.x 1 ^ 3})) 1 ≤
        c.chartD 1 (transformIdeal c.x 1 (span {c.x 0 ^ 2 + c.x 1 ^ 3}) 2) ∧
      transformIdeal c.x 1 (c.D (span {c.x 0 ^ 2 + c.x 1 ^ 3})) 1 ≠
        c.chartD 1 (transformIdeal c.x 1 (span {c.x 0 ^ 2 + c.x 1 ^ 3}) 2) := by
  rw [D_sq_add_cube, transformIdeal_D_sq_add_cube, transformIdeal_sq_add_cube,
    chartD_transform_sq_add_cube]
  exact ⟨le_top, span_transform_ne_top c⟩

/-- The inclusion of the example is an instance of the general `transform_D_le_chartD` (`I ≤ P²`,
`m = 1`): the computation agrees with the general theorem. -/
example :
    transformIdeal c.x 1 (c.D (span {c.x 0 ^ 2 + c.x 1 ^ 3})) 1 ≤
      c.chartD 1 (transformIdeal c.x 1 (span {c.x 0 ^ 2 + c.x 1 ^ 3}) 2) :=
  c.transform_D_le_chartD 1
    (span_le.mpr (by rintro _ rfl; exact sq_add_cube_mem_chartCenter_sq c.x))

end Hironaka.Local.Examples.DerivativeSequence
