/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Submanifold.Defs
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.IdealSheaf.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The ideal sheaf of a closed submanifold depends only on the set

`IsClosedSubmanifold.idealSheaf` is defined from a witness `hY : IsClosedSubmanifold ψ Y c` of the
statement that `Y` is a closed submanifold of codimension `c`, read in the model chart `ψ`, but the
ideal sheaf it produces is intrinsic to the set `Y`: at a point of `Y` a germ lies in it iff its
section vanishes on `Y` nearby (`germ_mem_stalkIdeal_idealSheaf_iff`), and off `Y` it is the unit
ideal. So two witnesses `(ψ, c)`, `(ψ', c')` for the same set, or for sets equal by hypothesis,
give the same ideal sheaf (`IsClosedSubmanifold.idealSheaf_congr`).

The fact is needed because a finite succession of blowings-up chooses the witnesses of its
centres (the model chart and the codimension) from its monoidal-transformation clauses, while the
proofs work at a fixed model chart and codimension;
`Hironaka.Manifold.FiniteSuccession.DerivTransform` and the restriction and transport modules of
`Hironaka.Manifold.Sequence` use it. A bookkeeping lemma, not in the sources.
-/

public section

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n n' : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {ψ' : E ≃L[𝕜] (Fin n' → 𝕜)}
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y Y' : Set M} {c c' : ℕ}

/-- The ideal sheaf of a closed submanifold depends only on the set: two witnesses `(ψ, c)`,
`(ψ', c')` of `IsClosedSubmanifold` for the same set `Y` (or for equal sets) give the same
`idealSheaf`, stalk by stalk: at a point of `Y` a germ lies in the stalk ideal iff its section
vanishes on `Y` nearby (`germ_mem_stalkIdeal_idealSheaf_iff`), and off `Y` the stalk ideal is the
unit ideal. -/
theorem IsClosedSubmanifold.idealSheaf_congr (hY : IsClosedSubmanifold ψ Y c)
    (hY' : IsClosedSubmanifold ψ' Y' c') (hYY' : Y = Y') : hY.idealSheaf = hY'.idealSheaf := by
  subst hYY'
  refine IdealSheaf.ext fun a => ?_
  by_cases ha : a ∈ Y
  · ext s
    obtain ⟨V, haV, g, rfl⟩ := (structureSheaf 𝕜 E M).presheaf.exists_germ_eq s
    rw [hY.germ_mem_stalkIdeal_idealSheaf_iff V ha haV,
      hY'.germ_mem_stalkIdeal_idealSheaf_iff V ha haV]
  · rw [hY.stalkIdeal_idealSheaf_of_notMem ha, hY'.stalkIdeal_idealSheaf_of_notMem ha]

end Manifold

end
