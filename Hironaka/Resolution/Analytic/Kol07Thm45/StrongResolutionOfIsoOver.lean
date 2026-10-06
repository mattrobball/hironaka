/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Resolution.Defs
import Hironaka.AnalyticSpace.RegPoints
import Hironaka.AnalyticSpace.SncBoundaryChart
import Hironaka.AnalyticSpace.SncDivisorSetLocal

/-!
# Strong resolutions from the isomorphism over the simple locus

A morphism `π : R → X` of analytic spaces with `R` non-singular, `π` proper, `π` an isomorphism over
the simple locus of `X` and `π⁻¹(Sing X)` the support of a simple normal crossing divisor is a
strong resolution (`Hom.IsStrongResolution`): the one field not listed, the bimeromorphy of `π` onto
its image, is the density of `π⁻¹(Reg X)`, the complement of the support of a simple normal
crossing divisor (`ClosedSubspace.isSncDivisorSet_of_isSncBoundary`, `IsSncDivisorSet.dense_compl`).
The lemma `Hom.isStrongResolution_of_isIsoOver_regularLocus` serves the assembly of the resolution
of analytic spaces (`ResolutionAssembly.lean`).
-/

public section

universe u

open scoped CategoryTheory
open TopologicalSpace

namespace AnalyticSpace.Hom

/-- A morphism with the other fields of a strong resolution is bimeromorphic onto its image, hence
a strong resolution: the preimage of the simple locus, over which `π` is an isomorphism, is the
complement of the support of a simple normal crossing divisor of `R`, hence dense
(`ClosedSubspace.isSncDivisorSet_of_isSncBoundary`, `IsSncDivisorSet.dense_compl`). -/
theorem isStrongResolution_of_isIsoOver_regularLocus {K : Type} [RCLike K]
    {X R : AnalyticSpace.{u} K} {π : R ⟶ X}
    (hR : R.IsNonsingular) (hπ : IsProperMap π) (hiso : π.IsIsoOver X.regularLocus)
    (hsnc : ∃ E : R.ClosedSubspace, E.IsSncBoundary ∧ E.support = π ⁻¹' X.singularLocus) :
    π.IsStrongResolution := by
  obtain ⟨E, hE, hsupp⟩ := hsnc
  refine ⟨⟨hR, hπ, X.regularLocus, isOpen_reg X, hiso, ?_⟩, hiso, E, hE, hsupp⟩
  have hd := (ClosedSubspace.isSncDivisorSet_of_isSncBoundary E hE).dense_compl
  rw [hsupp] at hd
  simpa [singularLocus, Set.preimage_compl] using hd

end AnalyticSpace.Hom

end
