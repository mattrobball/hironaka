/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.BirationalTransform
import Hironaka.Algebra.Local.Chart
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.Local.Transform

/-!
# Warning 63: the chart-level input

[Kol07, Warning 63]: the birational transform of a marked ideal along a blow-up sequence depends on
the sequence, not only on the composite morphism. Kollár's example compares two sequences with the
same composite `Π = Σ`; the discrepancy comes from one chart-level fact: blowing up a centre
`Z₁ ⊂ E₀'` contained in the exceptional divisor `E₀'` of the first blow-up, the *pullback* of `E₀'`
picks up the new exceptional divisor (`σ₁^* 𝒪(E₀') = 𝒪(E₀' + E₁')`), whereas the *marked
transform* `π⁻¹_*(𝒪(E₀'), 1)` is the strict transform, so
`Σ⁻¹_*(I, 1) = 𝒪(E₀' + 2E₁') Σ^* I ≠ 𝒪(E₀ + E₁) Π^* I = Π⁻¹_*(I, 1)`.

Locally (zero-based indices): `E₀' = V(x₀)`, centre `Z₁ = V(x₀, x₁)` (`chartCenter x 1`), chart
`y₀ = x₀/x₁, y₁ = x₁` (dividing by `x₁`). Then `⟨x₀⟩ R' = ⟨y₀ y₁⟩` (the total transform
`E₀'' + E₁'`, `map_span_x_zero`), while `π⁻¹_*(⟨x₀⟩, 1) = ⟨y₀⟩` (the strict transform `E₀''`,
`transformIdeal_span_x_zero`), and the two ideals differ (`transformIdeal_span_x_zero_ne_map`):
`y₁ = x₁` is not a unit of `R'`, lying in the origin ideal of the chart, and `R'` is a domain. The
statement for blow-up sequences, on Kollár's example, is
`Hironaka/Resolution/Algebraic/Kol07/Warning63.lean`; nothing else depends on this module.
-/

public section

namespace Hironaka.Local

open IsLocalRing

open IsLocalRing

variable {R : Type*} [CommRing R] {n : ℕ} (x : Fin (n + 2) → R)

theorem fin_zero_lt_one : (0 : Fin (n + 2)) < 1 := Fin.lt_def.mpr (by simp)

theorem fin_zero_le_one : (0 : Fin (n + 2)) ≤ 1 := (fin_zero_lt_one (n := n)).le

/-- `y₁ = x₁` in the chart dividing by `x₁`. -/
theorem chartYR_self (r : Fin (n + 2)) : chartYR x r r = algebraMap R (chartRing x r) (x r) :=
  Subtype.ext (by rw [coe_chartYROf, chartYOf_self, Subalgebra.coe_algebraMap])

/-- Kollár's "`σ₁^* 𝒪(E₀') = 𝒪(E₀' + E₁')`" ([Kol07, Warning 63]): the pullback of `E₀' = V(x₀)`
to the chart `y₀ = x₀/x₁, y₁ = x₁` is `⟨y₀ y₁⟩`, the total transform. -/
theorem map_span_x_zero :
    (Ideal.span {x 0}).map (algebraMap R (chartRing x 1)) =
      Ideal.span {chartYR x 1 0 * chartYR x 1 1} := by
  rw [Ideal.map_span, Set.image_singleton, algebraMap_x_eq_mul_chartYR x 1 fin_zero_lt_one,
    chartYR_self, mul_comm]

/-- The transform of the element `x₀` with mark `1` is `y₀`. -/
theorem transformElem_x_zero :
    transformElem (m := 1) x 1 (x 0)
        (by rw [pow_one]; exact x_mem_chartCenter x 1 fin_zero_le_one) =
      chartYR x 1 0 := by
  symm
  apply eq_transformElem_of_pow_mul_eq
  rw [pow_one, ← algebraMap_x_eq_mul_chartYR x 1 fin_zero_lt_one]

/-- The marked transform `π⁻¹_*(⟨x₀⟩, 1)` is `⟨y₀⟩`, the strict transform of `E₀'`
([Kol07, Warning 63]). -/
theorem transformIdeal_span_x_zero :
    transformIdeal x 1 (Ideal.span {x 0}) 1 = Ideal.span {chartYR x 1 0} := by
  have hI : Ideal.span {x 0} ≤ chartCenter x 1 ^ 1 := by
    rw [pow_one, Ideal.span_singleton_le_iff_mem]
    exact x_mem_chartCenter x 1 fin_zero_le_one
  rw [transformIdeal_eq_span_range_transformElem _ _ hI]
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro _ ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hg
    change transformElem x 1 (a * x 0) (hI hg) ∈ _
    have hsplit : transformElem x 1 (a * x 0) (hI hg) =
        algebraMap R (chartRing x 1) a *
          transformElem x 1 (x 0) (hI (Ideal.mem_span_singleton_self _)) := by
      symm
      apply eq_transformElem_of_pow_mul_eq
      rw [mul_left_comm, algebraMap_pow_mul_transformElem, map_mul]
    rw [hsplit, transformElem_x_zero]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rintro _ rfl
    exact Ideal.subset_span ⟨⟨x 0, Ideal.mem_span_singleton_self _⟩, transformElem_x_zero x⟩

/-- The discrepancy of [Kol07, Warning 63], "`Π⁻¹_*(I, 1) ≠ Σ⁻¹_*(I, 1)`", at the chart level: for
a regular system of parameters, the marked transform of `E₀' = V(x₀)` is not its pullback,
`⟨y₀⟩ ≠ ⟨y₀ y₁⟩`, because `y₁ = x₁` lies in the origin ideal of the chart and `R'` is a domain. -/
theorem transformIdeal_span_x_zero_ne_map [IsRegularLocalRing R]
    (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hn : ((n + 2 : ℕ) : WithBot ℕ∞) = ringKrullDim R) :
    transformIdeal x 1 (Ideal.span {x 0}) 1 ≠
      (Ideal.span {x 0}).map (algebraMap R (chartRing x 1)) := by
  rw [transformIdeal_span_x_zero, map_span_x_zero]
  intro h
  have := isDomain_chartRing x 1 hx hn
  have h0 : chartYR x 1 0 ∈ Ideal.span {chartYR x 1 0 * chartYR x 1 1} :=
    h ▸ Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h0
  have hy0 : chartYR x 1 0 ≠ 0 := by
    intro h0'
    have h := congrArg (fun z : chartRing x 1 => (z : Localization.Away (x 1))) h0'
    rw [coe_chartYROf, chartYOf_of_lt _ _ _ fin_zero_lt_one,
      mk_eq_algebraMap_mul_invX, Subalgebra.coe_zero] at h
    have := isDomain_away x 1 hx hn
    rcases mul_eq_zero.mp h with h1 | h1
    · exact x_ne_zero_of_span_eq x hx hn 0
        (algebraMap_away_injective x 1 hx hn (by rw [h1, map_zero]))
    · have := algebraMap_mul_invX x 1
      rw [h1, mul_zero] at this
      exact zero_ne_one this
  have hunit : chartYR x 1 1 * c = 1 := by
    have : chartYR x 1 0 * (chartYR x 1 1 * c - 1) = 0 := by linear_combination hc
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hy0
    · exact sub_eq_zero.mp h1
  have hmem : chartYR x 1 1 ∈ chartOrigin x 1 := chartYROf_mem_chartOriginOf x 1 (x 1) 1
  have h1 : (1 : chartRing x 1) ∈ chartOrigin x 1 := by
    rw [← hunit]
    exact Ideal.mul_mem_right _ _ hmem
  exact one_notMem_chartOrigin x 1 hx hn h1

end Hironaka.Local
