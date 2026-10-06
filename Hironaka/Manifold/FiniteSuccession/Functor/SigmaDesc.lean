/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.DisjointUnion.Defs
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Hironaka.AnalyticSpace.Manifold.Sigma
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The coproduct of analytic maps out of a disjoint union

For an open cover `X = ⋃ Uᵢ`, the disjoint union `X' := ∐ Uᵢ` comes with a smooth surjection
`g : X' → X` (the proof of [Kol07, Proposition 37]). On the disjoint union of analytic manifolds
(`ChartedSpace.sigma`, `IsManifold.sigma`, `sigmaManifold`): the coproduct `fun p => f p.1 p.2` of
a family of `C^n` maps `f i : M i → P` is `C^n` (the family version of Mathlib's
`ContMDiff.sumElim`: in the lifted charts of the disjoint union the coproduct reads as `f i`,
`extChartAt_sigma_mk`), and it is surjective iff the ranges of the `f i` cover
(`surjective_sigmaDesc_iff`). That the coproduct of local diffeomorphisms is a local
diffeomorphism is `Hironaka.Manifold.FiniteSuccession.Functor.SigmaLocalDiffeo`.
-/

public section

open Set Topology
open scoped Manifold ContDiff

universe u

section ContMDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} {n : WithTop ℕ∞}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]

/-- The inverse of the extended chart of the disjoint union at `⟨i, x⟩` lands in the `i`-th piece,
through the inverse of the piece's extended chart. -/
theorem extChartAt_sigma_mk_symm [Nonempty H] {i : ι} (x : M i) (z : E) :
    (extChartAt I (⟨i, x⟩ : Sigma M)).symm z = ⟨i, (extChartAt I x).symm z⟩ := by
  change (chartAt H (⟨i, x⟩ : Sigma M)).symm (I.symm z) = ⟨i, (chartAt H x).symm (I.symm z)⟩
  rw [ChartedSpace.sigma_chartAt]
  exact congrFun (OpenPartialHomeomorph.lift_openEmbedding_symm _ _) (I.symm z)

/-- The coproduct of a family
of `C^n` maps out of the pieces is `C^n` on the disjoint union — in the lifted charts it reads as
the piece's map. -/
theorem ContMDiff.sigmaDesc {f : ∀ i, M i → P} (hf : ∀ i, ContMDiff I J n (f i)) :
    ContMDiff I J n (fun p : Σ i, M i => f p.1 p.2) := by
  obtain (hH | hH) := isEmpty_or_nonempty H
  · rintro ⟨i, x⟩
    exact ((isEmpty_of_chartedSpace H (M := M i)).false x).elim
  rintro ⟨i, x⟩
  rw [contMDiffAt_iff]
  refine ⟨(continuous_sigma fun i => (hf i).continuous).continuousAt, ?_⟩
  have h := hf i x
  rw [contMDiffAt_iff] at h
  have hfun : (extChartAt J ((fun p : Σ i, M i => f p.1 p.2) ⟨i, x⟩) ∘
      (fun p : Σ i, M i => f p.1 p.2) ∘ (extChartAt I (⟨i, x⟩ : Sigma M)).symm) =
      extChartAt J (f i x) ∘ f i ∘ (extChartAt I x).symm := by
    funext z
    simp only [Function.comp_apply]
    rw [extChartAt_sigma_mk_symm]
  rw [hfun, extChartAt_sigma_mk]
  exact h.2

end ContMDiff

section Surjective

variable {ι : Type*} {M : ι → Type*} {P : Type*}

/-- [Kol07, Proposition 37] ("there is a smooth surjection `g : X' → X`"): the
coproduct of the `f i` is surjective iff their ranges cover. -/
theorem surjective_sigmaDesc_iff (f : ∀ i, M i → P) :
    Function.Surjective (fun p : Σ i, M i => f p.1 p.2) ↔ (⋃ i, range (f i)) = univ := by
  rw [Set.eq_univ_iff_forall]
  constructor
  · intro hs y
    obtain ⟨⟨i, x⟩, rfl⟩ := hs y
    exact mem_iUnion.mpr ⟨i, mem_range_self x⟩
  · intro h y
    obtain ⟨i, x, rfl⟩ := mem_iUnion.mp (h y)
    exact ⟨⟨i, x⟩, rfl⟩

end Surjective
