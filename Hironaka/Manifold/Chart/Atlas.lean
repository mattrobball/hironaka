/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Hironaka.Manifold.Submanifold.Manifold
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Charts of the maximal atlas as partial diffeomorphisms

Bookkeeping for the charts of the maximal analytic atlas of a manifold: an analytic open partial
homeomorphism of the model space with analytic inverse lies in the analytic groupoid
(`mem_contDiffGroupoid_omega_of_analytic'`, from `mem_contDiffGroupoid_self` with
`AnalyticOnNhd.contDiffOn`); every chart of the maximal atlas is a
`PartialDiffeomorph 𝓘 𝓘 M E ω` (Mathlib's `contMDiffOn_of_mem_maximalAtlas` and
`contMDiffOn_symm_of_mem_maximalAtlas`), so the composite `e'⁻¹ ∘ e` of two charts is a
`PartialDiffeomorph 𝓘 𝓘 M M ω` (`PartialDiffeomorph.chartChange`, from `PartialDiffeomorph.trans`
and `.symm`) and a local analytic isomorphism at every point of its source
(`PartialDiffeomorph.isLocalDiffeomorphAt`). The composite of a chart with an analytic open
partial homeomorphism of `E` with analytic inverse is again a chart of the maximal atlas
(`trans_mem_maximalAtlas_of_analytic'` of `Hironaka/Manifold/AdaptedChart.lean`). The chart
change is the coordinate swap of `Hironaka/Manifold/Chart/Swap.lean`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Filter Topology Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u


variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- An open partial homeomorphism of `E` that is analytic with analytic inverse lies in the
analytic groupoid of the model space; the form used by `trans_mem_maximalAtlas_of_analytic'` and
by the blow-up atlas. -/
theorem Manifold.mem_contDiffGroupoid_omega_of_analytic' (e₀ : OpenPartialHomeomorph E E)
    (h : AnalyticOnNhd 𝕜 e₀ e₀.source) (h' : AnalyticOnNhd 𝕜 e₀.symm e₀.target) :
    e₀ ∈ contDiffGroupoid ω 𝓘(𝕜, E) :=
  mem_contDiffGroupoid_self e₀ (h.contDiffOn e₀.open_source.uniqueDiffOn)
    (h'.contDiffOn e₀.open_target.uniqueDiffOn)

/-- A chart of the maximal atlas as a `PartialDiffeomorph 𝓘 𝓘 M E ω`. -/
def PartialDiffeomorph.ofMemMaximalAtlas {e : OpenPartialHomeomorph M E}
    (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M) : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M E ω where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he

/-- The underlying partial equivalence of `ofMemMaximalAtlas` is the chart's. -/
theorem PartialDiffeomorph.ofMemMaximalAtlas_toPartialEquiv {e : OpenPartialHomeomorph M E}
    (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M) :
    (PartialDiffeomorph.ofMemMaximalAtlas he).toPartialEquiv = e.toPartialEquiv := rfl

/-- Every chart of the maximal atlas is a `PartialDiffeomorph 𝓘 𝓘 M E ω`. -/
theorem Manifold.exists_partialDiffeomorph_of_mem_maximalAtlas' {e : OpenPartialHomeomorph M E}
    (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M) :
    ∃ Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M E ω, Φ.toPartialEquiv = e.toPartialEquiv :=
  ⟨PartialDiffeomorph.ofMemMaximalAtlas he, rfl⟩

/-- The chart change `e'⁻¹ ∘ e` of two charts of the maximal atlas as a
`PartialDiffeomorph 𝓘 𝓘 M M ω`. -/
def PartialDiffeomorph.chartChange {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M) (he' : e' ∈ maximalAtlas 𝓘(𝕜, E) ω M) :
    PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M M ω :=
  (PartialDiffeomorph.ofMemMaximalAtlas he).trans (PartialDiffeomorph.ofMemMaximalAtlas he').symm

/-- The chart change as a partial equivalence is `e ≫ e'.symm`. -/
theorem PartialDiffeomorph.chartChange_toPartialEquiv {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M) (he' : e' ∈ maximalAtlas 𝓘(𝕜, E) ω M) :
    (PartialDiffeomorph.chartChange he he').toPartialEquiv = (e.trans e'.symm).toPartialEquiv :=
  rfl

/-- The composite `e'⁻¹ ∘ e` of two charts of the maximal atlas is a `PartialDiffeomorph 𝓘 𝓘 M M ω`,
a local analytic isomorphism at every point of its source. -/
theorem Manifold.exists_partialDiffeomorph_chartChange' {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M) (he' : e' ∈ maximalAtlas 𝓘(𝕜, E) ω M) :
    ∃ Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M M ω,
      Φ.toPartialEquiv = (e.trans e'.symm).toPartialEquiv ∧
      ∀ x ∈ Φ.source, IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω Φ x :=
  ⟨PartialDiffeomorph.chartChange he he', rfl, fun _ hx =>
    PartialDiffeomorph.isLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      (PartialDiffeomorph.chartChange he he') hx⟩


end
