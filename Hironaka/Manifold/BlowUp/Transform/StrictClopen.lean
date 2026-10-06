/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Transform.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The strict transform of a clopen part

The strict transform `closure (π⁻¹(H ∖ Z))` of a clopen part `H ∩ O` of a closed set `H` under a
continuous map `π` is the corresponding clopen part `π⁻¹(O)` of the strict transform of `H`
(`strictTransformSet_inter_of_isOpen`). This is used for the pieces of the boundary divisor in the
order-reduction algorithm (clopen parts of the members of the boundary): the strict transform of a
piece is a clopen part of the strict transform of its member, hence a closed hypersurface when the
member's strict transform is one. A point-set lemma, not in the sources.
-/

public section

open TopologicalSpace Filter Topology Set

universe u

namespace Manifold

variable {M : Type u} [TopologicalSpace M] {M' : Type u} [TopologicalSpace M']

/-- The strict transform of a clopen part `H ∩ O` of a closed set `H` is the part `π⁻¹(O)` of the
strict transform of `H`. -/
theorem strictTransformSet_inter_of_isOpen {π : M' → M} (hπ : Continuous π) (Z : Set M)
    {H O : Set M} (hO : IsOpen O) (hHO : IsClosed (H ∩ O)) :
    strictTransformSet π Z (H ∩ O) = strictTransformSet π Z H ∩ π ⁻¹' O := by
  unfold strictTransformSet
  apply Set.Subset.antisymm
  · refine Set.subset_inter (closure_mono ?_) ?_
    · exact Set.preimage_mono (Set.sdiff_subset_sdiff_left Set.inter_subset_left)
    · refine (closure_minimal ?_ (hHO.preimage hπ)).trans (Set.preimage_mono Set.inter_subset_right)
      exact Set.preimage_mono Set.sdiff_subset
  · intro p hp
    have h1 : p ∈ π ⁻¹' O ∩ closure (π ⁻¹' (H \ Z)) := ⟨hp.2, hp.1⟩
    have h2 := (hO.preimage hπ).inter_closure h1
    refine closure_mono ?_ h2
    rintro q ⟨hqO, hqH, hqZ⟩
    exact ⟨⟨hqH, hqO⟩, hqZ⟩

end Manifold
