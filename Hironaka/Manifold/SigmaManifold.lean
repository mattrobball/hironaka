/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.AnalyticManifold.Defs
/-!
# The disjoint union of a countable family of analytic manifolds

`sigmaManifold M : AnalyticManifold K E`, for a countable family `M : ι → AnalyticManifold K E`
with `ι : Type u` (the universe of the manifolds, so that the `Σ`-type lives there too): the
`Σ`-type with the charted-space and manifold structure `ChartedSpace.sigma`, `IsManifold.sigma`
(the chart at `p` is the chart of the summand at `p.2`, lifted along `Sigma.mk p.1`:
`ChartedSpace.sigma_chartAt`), Hausdorff by Mathlib's `Sigma.t2Space` and second countable for a
countable index. The inclusion `Sigma.mk i` of a summand is `C^n` (`ContMDiff.sigmaMk`, the family
version of Mathlib's `ContMDiff.inl`: in the lifted charts it is the identity), and `sigmaMk M i`
is the bundled analytic map `M i → sigmaManifold M`.

This bundle is the coproduct of analytic manifolds modelled on `E`; the coproduct in the category
of analytic spaces is formed from it (`Hironaka/AnalyticSpace/Manifold/Sigma.lean`), and the gluing
arguments of the `Hironaka` library use it to assemble a manifold from a countable family of
pieces.
-/

@[expose] public section

open Topology Set
open scoped Manifold ContDiff

universe u

namespace ChartedSpace

variable {ι : Type*} {H : Type*} [TopologicalSpace H] (M : ι → Type*)
  [∀ i, TopologicalSpace (M i)] [cm : ∀ i, ChartedSpace H (M i)]

theorem sigma_chartAt [Nonempty H] (p : Σ i, M i) :
    chartAt H p = ((cm p.1).chartAt p.2).lift_openEmbedding IsOpenEmbedding.sigmaMk := by
  simp +instances only [chartAt, sigma, ‹Nonempty H›, ↓reduceDIte]
  rfl

end ChartedSpace

section ContMDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
  {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]

/-- The inclusion of a summand into the disjoint union `Σ i, M i` (with the charted-space
structure `ChartedSpace.sigma`) is `C^n`: in the lifted charts it is the identity. The family
version of Mathlib's `ContMDiff.inl`. -/
theorem ContMDiff.sigmaMk (i : ι) : ContMDiff I I n (@Sigma.mk ι M i) := by
  obtain (hH | hH) := isEmpty_or_nonempty H
  · intro x
    exact ((isEmpty_of_chartedSpace H (M := M i)).false x).elim
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuous_sigmaMk.continuousAt, ?_⟩
  apply contDiffWithinAt_id.congr_of_eventuallyEq; swap
  · simp [ChartedSpace.sigma_chartAt, sigma_mk_injective.extend_apply (chartAt H x)]
  set C := chartAt H x with hC
  have : I.symm ⁻¹' C.target ∩ range I ∈ 𝓝[range I] (extChartAt I x) x := by
    rw [← I.image_eq (chartAt H x).target]
    exact (chartAt H x).extend_image_target_mem_nhds (mem_chart_source _ x)
  filter_upwards [this] with y hy
  simp [extChartAt, ChartedSpace.sigma_chartAt, ← hC, sigma_mk_injective.extend_apply C,
    C.right_inv hy.1, I.right_inv hy.2]

end ContMDiff

namespace Manifold

variable {K : Type} [RCLike K] {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
  {ι : Type u} [Countable ι] (M : ι → AnalyticManifold.{u} K E)

/-- **The disjoint union of a countable family of analytic manifolds** as a bundled analytic
manifold: the `Σ`-type with the charted-space and manifold structure `ChartedSpace.sigma`,
`IsManifold.sigma`, Hausdorff (`Sigma.t2Space`) and second countable (countable index). -/
noncomputable def sigmaManifold : AnalyticManifold.{u} K E where
  carrier := Σ i, (M i : Type u)

theorem sigmaManifold_carrier : (sigmaManifold M : Type u) = Σ i, (M i : Type u) :=
  rfl

/-- The inclusion of the `i`-th summand as an analytic map. -/
noncomputable def sigmaMk (i : ι) : AnalyticMap (M i) (sigmaManifold M) :=
  ⟨fun x => (Sigma.mk i x : Σ j, (M j : Type u)),
    ContMDiff.sigmaMk (I := 𝓘(K, E)) (n := ω) (M := fun j => (M j : Type u)) i⟩

theorem sigmaMk_apply (i : ι) (x : M i) : sigmaMk M i x = Sigma.mk i x :=
  rfl

end Manifold
