/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Restrict.Defs
import Hironaka.AnalyticSpace.ClosedSubspaceLemmas
import Hironaka.AnalyticSpace.RegDensityLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init

/-!
# Properties local on an open cover: non-singularity and properness

Two locality statements used when a resolution is assembled from pieces: the glued space is
covered by the images of its pieces, and the resolution morphism is covered on the target by an
exhaustion, so both non-singularity ([Kol07, Theorem 45 (1)]) and properness
([Kol07, Theorem 45 (4)]; the properness of the glued desingularization in [Wlo09, §4]) are
checked piecewise.

* `AnalyticSpace.isNonsingular_of_openCover`: an analytic `K`-space covered by opens whose open
  subspaces are non-singular is non-singular, since the stalk of an open subspace at a point is
  the stalk of the space (`isRegularLocalRing_stalk_restrictOpen_iff`,
  `Hironaka/AnalyticSpace/RegDensityLemmas.lean`).
* `isProperMap_of_restrictPreimage_cover`: a continuous map whose restrictions over the members
  of an open cover of the target are proper is proper — Mathlib's
  `isProperMap_iff_isClosedMap_and_compact_fibers` with `isClosedMap_iff_restrictPreimage`, the
  fibres being those of the restrictions.

Used by `Hironaka/AnalyticSpace/ProperRestrict.lean` and
`Hironaka/Resolution/Analytic/Functor/LimitProperties.lean`.
-/

public section

open TopologicalSpace Set

universe u


variable {K : Type} [RCLike K]

/-- Non-singularity is local: an analytic `K`-space covered by opens whose open subspaces are
non-singular is non-singular ([Kol07, Theorem 45 (1)], checked on the pieces of a gluing). -/
theorem AnalyticSpace.isNonsingular_of_openCover (X : AnalyticSpace.{u} K) {ι : Type*}
    (V : ι → Set X) (hV : ∀ i, IsOpen (V i)) (hcov : ⋃ i, V i = univ)
    (h : ∀ i, (X.restrictSet (V i)).IsNonsingular) : X.IsNonsingular := by
  rw [AnalyticSpace.isNonsingular_iff]
  intro x
  obtain ⟨i, hi⟩ : ∃ i, x ∈ V i := mem_iUnion.mp (hcov ▸ mem_univ x)
  have hx : x ∈ AnalyticSpace.openOf X (V i) := by
    rw [AnalyticSpace.openOf_of_isOpen X (hV i)]; exact hi
  have hreg := (AnalyticSpace.isNonsingular_iff _).mp (h i) ⟨x, hx⟩
  exact (isRegularLocalRing_stalk_restrictOpen_iff X.toKLocallyRingedSpace
    (AnalyticSpace.openOf X (V i)) ⟨x, hx⟩).mp hreg

/-- Properness is local on the target: a continuous map whose restrictions over the members of an
open cover of the target are proper is proper — closedness by Mathlib's
`isClosedMap_iff_restrictPreimage`, the fibres being the fibres of the restrictions. Compare the
properness of the glued desingularization in [Wlo09, §4]. -/
theorem AnalyticSpace.isProperMap_of_restrictPreimage_cover {Y X : Type*} [TopologicalSpace Y]
    [TopologicalSpace X] (f : Y → X) (hf : Continuous f) {ι : Type*} (V : ι → Set X)
    (hV : ∀ i, IsOpen (V i)) (hcov : ⋃ i, V i = univ)
    (h : ∀ i, IsProperMap ((V i).restrictPreimage f)) : IsProperMap f := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨hf, ?_, ?_⟩
  · rw [(TopologicalSpace.IsOpenCover.of_sets hV hcov).isClosedMap_iff_restrictPreimage]
    intro i
    exact (h i).isClosedMap
  · intro x
    obtain ⟨i, hi⟩ : ∃ i, x ∈ V i := mem_iUnion.mp (hcov ▸ mem_univ x)
    have hc : IsCompact (((V i).restrictPreimage f) ⁻¹' {⟨x, hi⟩}) :=
      (h i).isCompact_preimage isCompact_singleton
    have himg : Subtype.val '' (((V i).restrictPreimage f) ⁻¹' {⟨x, hi⟩}) = f ⁻¹' {x} := by
      ext y
      constructor
      · rintro ⟨⟨y', hy'⟩, hy, rfl⟩
        have := congrArg Subtype.val (mem_singleton_iff.mp hy)
        exact mem_singleton_iff.mpr this
      · intro hy
        have hyV : f y ∈ V i := by rw [mem_singleton_iff.mp hy]; exact hi
        exact ⟨⟨y, hyV⟩, mem_singleton_iff.mpr (Subtype.ext (mem_singleton_iff.mp hy)), rfl⟩
    rw [← himg]
    exact hc.image continuous_subtype_val

