/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Charts
import Hironaka.Manifold.BlowUp.Divisor
import Hironaka.Manifold.BlowUp.Exists
import Hironaka.Manifold.BlowUp.Transition
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The blowing-up as a quadratic transformation in charts

Bierstone–Milman's axiom (3.8)(4) requires their category of spaces to be closed under
blowing-up, and a blowing-up with smooth centre to be described locally as a quadratic
transformation in regular coordinate charts: on the chart `U'_i` of `π⁻¹(U)`, `w' = w`,
`z'_i = z_i`, `z'_j = z_j / z_i` [BM97, (3.8)(4) and §3, "Blowing-up", pp. 26–27]. This file
identifies the three descriptions of the blowing-up in the sources with the blowing-up `IsBlowUp`:
the chart map `blowUpChartMap σ i` is the formula
`x_i = x_{ii}`, `x_j = x_{ii} x_{ij}` of [BM88, Definition 4.1] by definition, and
`IsBlowUpChart.comm` says that `π` reads as that map in a blow-up chart over an adapted chart of
the centre; unfolding it gives `z_i ∘ π = u_i`, `z_k ∘ π = u_i · u_k`, `w_j ∘ π = u_j`, and off
the exceptional divisor (where the scaling coordinate `u_i` is nonzero) the chart coordinates
`z'_j = z_j / z_i` of Bierstone–Milman are `blowUpChartInv σ i`. Kollár's chart `y_j = x_j / x_r`
(`j < r`), `y_r = x_r`, `y_j = x_j` (`j > r`) [Kol07, Definition 60, (60.2)] is the same map read
in Kollár's ordering of the coordinates (a permutation `τ`). Finally every blowing-up is covered
by such charts (`IsBlowUp.cover`), and `exists_isBlowUp` realizes the axiom: for every closed
submanifold there is a blowing-up, described locally as a quadratic transformation.
-/

public section

open TopologicalSpace Filter Topology Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] {Y : Set M} {c : ℕ}
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] {π : M' → M}
  {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n} {i : Fin c} {Φ : OpenPartialHomeomorph M' E}

/-- The quadratic transformation, scaling coordinate: `z_i ∘ π = u_i` on the blow-up chart of
index `i` (`IsBlowUpChart.comm` unfolded; [BM97, §3, "Blowing-up"], [BM88, Definition 4.1]). -/
theorem blowUpChart_coord_scaling (hΦ : IsBlowUpChart ψ π φ σ i Φ) {p : M'} (hp : p ∈ Φ.source) :
    ψ (φ (π p)) (σ i) = ψ (Φ p) (σ i) := by
  rw [hΦ.comm p hp, blowUpChartMap_apply_scaling]

/-- The quadratic transformation, the other centre coordinates: `z_k ∘ π = u_i · u_k` for
`k ≠ i` ([BM97, §3, "Blowing-up"], [BM88, Definition 4.1]). -/
theorem blowUpChart_coord_ratio (hΦ : IsBlowUpChart ψ π φ σ i Φ) {p : M'} (hp : p ∈ Φ.source)
    {k : Fin c} (hk : k ≠ i) :
    ψ (φ (π p)) (σ k) = ψ (Φ p) (σ i) * ψ (Φ p) (σ k) := by
  rw [hΦ.comm p hp, blowUpChartMap_apply_ratio (σ := σ) (u := ψ (Φ p)) hk]

/-- The quadratic transformation, the off-centre coordinates: `w_j ∘ π = u_j` for `j` outside the
centre indices (`w' = w` in [BM97, §3, "Blowing-up"]). -/
theorem blowUpChart_coord_off (hΦ : IsBlowUpChart ψ π φ σ i Φ) {p : M'} (hp : p ∈ Φ.source)
    {j : Fin n} (hj : ∀ k, σ k ≠ j) :
    ψ (φ (π p)) j = ψ (Φ p) j := by
  rw [hΦ.comm p hp, blowUpChartMap_apply_off (σ := σ) (i := i) (u := ψ (Φ p)) hj]

variable [ChartedSpace E M]

/-- Off the exceptional divisor the scaling coordinate of the blow-up chart is nonzero. -/
theorem IsBlowUpChart.coord_scaling_ne_zero (hφ : IsAdaptedChart ψ Y φ σ)
    (hΦ : IsBlowUpChart ψ π φ σ i Φ) {p : M'} (hp : p ∈ Φ.source) (hpY : π p ∉ Y) :
    ψ (Φ p) (σ i) ≠ 0 :=
  fun h0 => hpY ((IsBlowUpChart.mem_preimage_iff hφ hΦ hp).mpr h0)

/-- Off the exceptional divisor the blow-up chart coordinates are the quotients `z'_j = z_j / z_i`
of [BM97, §3, "Blowing-up"]. -/
theorem blowUpChart_coord_ratio_div (hφ : IsAdaptedChart ψ Y φ σ) (hΦ : IsBlowUpChart ψ π φ σ i Φ)
    {p : M'} (hp : p ∈ Φ.source) (hpY : π p ∉ Y) {k : Fin c} (hk : k ≠ i) :
    ψ (Φ p) (σ k) = ψ (φ (π p)) (σ k) / ψ (φ (π p)) (σ i) := by
  rw [blowUpChart_coord_ratio hΦ hp hk, blowUpChart_coord_scaling hΦ hp,
    mul_div_cancel_left₀ _ (hΦ.coord_scaling_ne_zero hφ hp hpY)]

/-- Off the exceptional divisor the blow-up chart is the inverse quadratic transformation
`blowUpChartInv σ i` of the adapted chart. -/
theorem blowUpChart_eq_blowUpChartInv (hφ : IsAdaptedChart ψ Y φ σ)
    (hΦ : IsBlowUpChart ψ π φ σ i Φ) {p : M'} (hp : p ∈ Φ.source) (hpY : π p ∉ Y) :
    ψ (Φ p) = blowUpChartInv σ i (ψ (φ (π p))) := by
  rw [hΦ.comm p hp]
  exact (blowUpChartInv_blowUpChartMap σ (ψ (Φ p)) (hΦ.coord_scaling_ne_zero hφ hp hpY)).symm

/-- In Kollár's ordering `τ` of the coordinates (`τ r = σ i`, the other centre indices before `r`)
the blow-up chart coordinates are Kollár's `y_j = x_j / x_r` (`j < r`), `y_r = x_r`, `y_j = x_j`
(`j > r`) [Kol07, Definition 60, (60.2)]: the chart `U'_i` of [BM97], the chart `V'_i` of [BM88]
and Kollár's chart are the same map. -/
theorem blowUpChartMap_eq_kollarChart (hφ : IsAdaptedChart ψ Y φ σ)
    (hΦ : IsBlowUpChart ψ π φ σ i Φ) {p : M'} (hp : p ∈ Φ.source) (hpY : π p ∉ Y) (r : Fin n)
    (τ : Fin n ≃ Fin n) (hτr : τ r = σ i) (hlt : ∀ j, j < r ↔ ∃ k, k ≠ i ∧ τ j = σ k) :
    (∀ j, j < r → ψ (Φ p) (τ j) = ψ (φ (π p)) (τ j) / ψ (φ (π p)) (τ r)) ∧
      ψ (Φ p) (τ r) = ψ (φ (π p)) (τ r) ∧
      ∀ j, r < j → ψ (Φ p) (τ j) = ψ (φ (π p)) (τ j) := by
  refine ⟨fun j hj => ?_, ?_, fun j hj => ?_⟩
  · obtain ⟨k, hk, hτj⟩ := (hlt j).mp hj
    rw [hτj, hτr]
    exact blowUpChart_coord_ratio_div hφ hΦ hp hpY hk
  · rw [hτr]
    exact (blowUpChart_coord_scaling hΦ hp).symm
  · refine (blowUpChart_coord_off hΦ hp fun k hk => ?_).symm
    by_cases hki : k = i
    · subst hki
      rw [← hτr] at hk
      exact hj.ne (τ.injective hk)
    · exact hj.not_gt ((hlt j).mpr ⟨k, hki, hk.symm⟩)

variable [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M']

/-- A blowing-up with smooth centre is described locally as a quadratic transformation in regular
coordinate charts [BM97, (3.8)(4)]: every point over an adapted chart of the centre lies in a
blow-up chart of some index on which `x ∘ π = blowUpChartMap σ i ∘ u` (the clauses `cover` and
`comm` of `IsBlowUp`). -/
theorem isBlowUp_quadraticTransformation (h : IsBlowUp ψ Y c π) (hφ : IsAdaptedChart ψ Y φ σ)
    {p : M'} (hp : π p ∈ φ.source) :
    ∃ (i : Fin c) (Φ : OpenPartialHomeomorph M' E), IsBlowUpChart ψ π φ σ i Φ ∧ p ∈ Φ.source ∧
      ∀ q ∈ Φ.source, ψ (φ (π q)) = blowUpChartMap σ i (ψ (Φ q)) := by
  obtain ⟨i, Φ, hΦ, hpΦ⟩ := h.cover φ σ hφ p hp
  exact ⟨i, Φ, hΦ, hpΦ, fun q hq => hΦ.comm q hq⟩

end Manifold

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] {Y : Set M} {c : ℕ}

/-- The category of analytic manifolds is closed under blowing-up with smooth centre, and the
blowing-up is described locally as a quadratic transformation in the adapted charts of the centre
[BM97, (3.8)(4)]; the blowing-up is the one of `exists_isBlowUp`. -/
theorem exists_isBlowUp_quadraticTransformation (hY : IsClosedSubmanifold ψ Y c) :
    ∃ (M' : Type u) (_ : TopologicalSpace M') (_ : ChartedSpace E M')
      (_ : IsManifold 𝓘(𝕜, E) ω M') (_ : T2Space M') (_ : SecondCountableTopology M')
      (π : M' → M), IsBlowUp ψ Y c π ∧
        ∀ (φ : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n), IsAdaptedChart ψ Y φ σ →
          ∀ p : M', π p ∈ φ.source →
            ∃ (i : Fin c) (Φ : OpenPartialHomeomorph M' E), IsBlowUpChart ψ π φ σ i Φ ∧
              p ∈ Φ.source ∧ ∀ q ∈ Φ.source, ψ (φ (π q)) = blowUpChartMap σ i (ψ (Φ q)) := by
  obtain ⟨M', _, _, _, _, _, π, h⟩ := exists_isBlowUp ψ hY
  exact ⟨M', _, _, _, _, _, π, h, fun φ σ hφ p hp => isBlowUp_quadraticTransformation h hφ hp⟩

end Manifold
