/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Snc.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The multiple locus of a family of hypersurfaces

`HypersurfaceFamily.singularLocus F`, the set of points lying on two distinct components of the
family — the analytic counterpart of the multiple locus of a divisor family in the `Hironaka`
library (here a `Set`; closedness, for locally finite families, is left to the uses). For an snc
family it is exactly the locus where the support `|F|` is not a smooth hypersurface. Kollár's
principalization is an isomorphism "over `X ∖ cosupp I`" [Kol07, Theorem 35 (3)]; when the boundary
components are first made disjoint by the preliminary blow-ups of [Kol07, 72], whose centres — the
`k`-fold meet loci of the components — lie in `Sing F`, the isomorphism holds over the complement of
`cosupp 𝓘 ∪ Sing F`.
-/

@[expose] public section

universe u

namespace Manifold.HypersurfaceFamily

variable {M : Type u}

/-- **The multiple locus** `Sing F` of a family of hypersurfaces: the points lying on two distinct
components. For an snc family it is the locus where the support is not a smooth hypersurface; the
preliminary blow-ups that make the components of the boundary disjoint [Kol07, 72] have their
centres inside it. -/
def singularLocus (F : HypersurfaceFamily M) : Set M :=
  {x | ∃ i j : F.ι, i ≠ j ∧ x ∈ F.hyp i ∧ x ∈ F.hyp j}

theorem mem_singularLocus {F : HypersurfaceFamily M} {x : M} :
    x ∈ F.singularLocus ↔ ∃ i j : F.ι, i ≠ j ∧ x ∈ F.hyp i ∧ x ∈ F.hyp j :=
  Iff.rfl

/-- The multiple locus lies in the support. -/
theorem singularLocus_subset_support (F : HypersurfaceFamily M) : F.singularLocus ⊆ F.support := by
  rintro x ⟨i, _, _, hi, _⟩
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- The empty family has empty multiple locus. -/
theorem singularLocus_empty : (HypersurfaceFamily.empty M).singularLocus = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨i, -, -, -, -⟩ := hx
  exact i.elim

end Manifold.HypersurfaceFamily
