/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Submanifold
import Hironaka.Manifold.AdaptedChart
import Hironaka.Manifold.Submanifold.Generators
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Independence of differentials read in a chart

`HasIndependentDifferentialsAt E z a` — the linear independence of the manifold derivatives of the
`z i` at `a` — is the linear independence of the derivatives of the `z i ∘ φ⁻¹` at `φ a` for any
chart `φ` of the maximal atlas at `a`, hence chart-independent
(`linearIndependent_fderiv_chart_iff'`). `hasIndependentDifferentialsAt_iff_chart` of
`Hironaka/Manifold/AdaptedChart.lean` proves this for functions differentiable at `a`; here the
hypothesis is removed: a function not differentiable at `a` has `mfderiv = 0` and, read in the
chart, `fderiv = 0` (differentiability of `z i ∘ φ⁻¹` at `φ a` would make `z i` differentiable at
`a`), so both families contain `0` and neither is independent. This is the chart form of the
independence of differentials of Bierstone–Milman's regular coordinate charts [BM97, (0.3)] and
Kollár's local coordinates [Kol07, Definition 73].
-/

public section

noncomputable section

open TopologicalSpace Filter Topology Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- A function whose chart reading is differentiable at `φ a` is `MDifferentiableAt a`. -/
theorem mdifferentiableAt_of_differentiableAt_comp_symm {φ : OpenPartialHomeomorph M E}
    (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {a : M} (ha : a ∈ φ.source) {z : M → 𝕜}
    (hd : DifferentiableAt 𝕜 (z ∘ φ.symm) (φ a)) : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜) z a := by
  have hφa : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E) φ a :=
    (mdifferentiable_of_mem_maximalAtlas hφ).mdifferentiableAt ha
  have hcomp : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜) ((z ∘ φ.symm) ∘ φ) a :=
    (mdifferentiableAt_iff_differentiableAt.mpr hd).comp a hφa
  exact hcomp.congr_of_eventuallyEq ((φ.eventually_left_inverse ha).mono fun y hy => by
    simp [Function.comp, hy])

/-- Independence of the differentials at `a` is the linear independence of the derivatives read
in any chart of the maximal atlas at `a` ([BM97, (0.3)]; [Kol07, Definition 73]). -/
theorem linearIndependent_fderiv_chart_iff' {φ : OpenPartialHomeomorph M E}
    (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {a : M} (ha : a ∈ φ.source) {c : ℕ}
    (z : Fin c → M → 𝕜) :
    HasIndependentDifferentialsAt E z a ↔
      LinearIndependent 𝕜 fun i => fderiv 𝕜 (z i ∘ φ.symm) (φ a) := by
  by_cases hz : ∀ i, MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜) (z i) a
  · exact hasIndependentDifferentialsAt_iff_chart hφ ha hz
  · obtain ⟨i, hi⟩ := not_forall.mp hz
    have h1 : mderivFun E (z i) a = 0 := mfderiv_zero_of_not_mdifferentiableAt hi
    have h2 : fderiv 𝕜 (z i ∘ φ.symm) (φ a) = 0 :=
      fderiv_zero_of_not_differentiableAt fun hd =>
        hi (mdifferentiableAt_of_differentiableAt_comp_symm hφ ha hd)
    constructor
    · intro h
      exact absurd h1 (h.ne_zero i)
    · intro h
      exact absurd h2 (h.ne_zero i)

end Manifold

end
