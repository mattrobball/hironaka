/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Disjoint unions of manifolds indexed by a type

Mathlib has the disjoint union of two manifolds (`ChartedSpace.sum`, `IsManifold.disjointUnion`) but
not of a family. The `Hironaka` library forms countable disjoint unions `Σ i, M i` of manifolds
modelled on one space (the coproducts of analytic manifolds and of analytic spaces); this module
adds the family version, mirroring Mathlib's binary one: the charts of `Σ i, M i` are the charts of
the `M i` lifted along the open embeddings `Sigma.mk i` (`ChartedSpace.sigma`), and `Σ i, M i` is a
`C^n` manifold when every `M i` is (`IsManifold.sigma`), chart changes between different summands
having empty domain. The bundled disjoint union of a countable family of analytic manifolds is
`Manifold.sigmaManifold`.
-/

@[expose] public section

open Topology
open scoped ContDiff

namespace ChartedSpace

variable {ι : Type*} {H : Type*} [TopologicalSpace H] (M : ι → Type*)
  [∀ i, TopologicalSpace (M i)] [cm : ∀ i, ChartedSpace H (M i)]

/-- The disjoint union of a family of charted spaces modelled on a nonempty `H` is a charted
space modelled on `H`: the charts are the charts of the `M i`, lifted along the open embeddings
`Sigma.mk i`. -/
@[instance_reducible]
noncomputable def sigmaOfNonempty [Nonempty H] : ChartedSpace H (Σ i, M i) where
  atlas := ⋃ i, (fun e => e.lift_openEmbedding (IsOpenEmbedding.sigmaMk (i := i))) '' (cm i).atlas
  chartAt p := ((cm p.1).chartAt p.2).lift_openEmbedding IsOpenEmbedding.sigmaMk
  mem_chart_source p := by
    rcases p with ⟨i, x⟩
    rw [OpenPartialHomeomorph.lift_openEmbedding_source]
    exact ⟨x, (cm i).mem_chart_source x, rfl⟩
  chart_mem_atlas p :=
    Set.mem_iUnion.mpr ⟨p.1, ⟨_, (cm p.1).chart_mem_atlas p.2, rfl⟩⟩

/-- The disjoint union `Σ i, M i` of charted spaces modelled on `H` is a charted space modelled
on `H` (for `H` empty every `M i` is empty, and so is the union). -/
noncomputable instance sigma : ChartedSpace H (Σ i, M i) := by
  by_cases! h : Nonempty H
  · exact sigmaOfNonempty M
  have hM : ∀ i, IsEmpty (M i) := fun i => isEmpty_of_chartedSpace H
  have : IsEmpty (Σ i, M i) := ⟨fun p => (hM p.1).false p.2⟩
  exact empty H (Σ i, M i)

theorem mem_atlas_sigma [h : Nonempty H] {e : OpenPartialHomeomorph (Σ i, M i) H}
    (he : e ∈ atlas H (Σ i, M i)) :
    ∃ (i : ι) (f : OpenPartialHomeomorph (M i) H), f ∈ atlas H (M i) ∧
      e = f.lift_openEmbedding IsOpenEmbedding.sigmaMk := by
  simp +instances only [atlas, sigma, h, ↓reduceDIte] at he
  obtain ⟨i, f, hf, hfe⟩ := Set.mem_iUnion.mp he
  exact ⟨i, f, hf, hfe.symm⟩

end ChartedSpace

namespace IsManifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
  {ι : Type*} (M : ι → Type*) [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [hM : ∀ i, IsManifold I n (M i)]

/-- The disjoint union `Σ i, M i` of a family of `C^n` manifolds modelled on `(E, H)` is a `C^n`
manifold modelled on `(E, H)`: chart changes within one `M i` are those of `M i`, and chart
changes between different summands have empty domain. -/
instance sigma : IsManifold I n (Σ i, M i) where
  compatible {e} e' he he' := by
    obtain (h | h) := isEmpty_or_nonempty H
    · exact ContDiffGroupoid.mem_of_source_eq_empty _ (Set.eq_empty_of_isEmpty _)
    obtain ⟨i, f, hf, rfl⟩ := ChartedSpace.mem_atlas_sigma M he
    obtain ⟨j, f', hf', rfl⟩ := ChartedSpace.mem_atlas_sigma M he'
    by_cases hij : i = j
    · subst hij
      rw [f.lift_openEmbedding_trans f' IsOpenEmbedding.sigmaMk]
      exact (hM i).compatible hf hf'
    · apply ContDiffGroupoid.mem_of_source_eq_empty
      ext x
      refine ⟨fun ⟨_, hx₂⟩ => ?_, fun hx => hx.elim⟩
      rw [OpenPartialHomeomorph.lift_openEmbedding_source] at hx₂
      obtain ⟨y, -, hy⟩ := hx₂
      exact hij (Sigma.mk.inj_iff.mp hy).1.symm

end IsManifold
