/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Snc.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Order reduction on manifolds: the members processed by Step 2.1 of the proof of Theorem 103

Step 2.1 of the proof of [Kol07, Theorem 103] clears the boundary from the cosupport: for
`E = ∑_{i=1}^s E^i`, "we apply (102) to each `E^i`", obtaining at the end a blow-up sequence
`Π : X_r → X` with `cosupp(I_r, m)` disjoint from `Π^{-1}_* E`, the members being taken
in the order of the index set of `E`. On analytic manifolds the boundary of a triple has a
linearly ordered index set and, on the class `BOClass m`, only finitely many nonempty members;
the nonempty members are processed in the order of the index set and the empty ones are skipped.

* `HypersurfaceFamily.nonemptyFinset`, `HypersurfaceFamily.nonemptyList` — the nonempty members
  of a family with finitely many of them, as a finite set and as the list sorted by the order of the
  index set.

Step 2.1 itself is constructed in the compatible-family form, over data `bd : BDanFamData ψ₀ s`
for the functor `BD_{n,s,j}` of [Kol07, Lemma 102], in `Step21Fam.lean`; Step 2.2 follows in
`Step22Fam.lean`.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

namespace HypersurfaceFamily

variable {M : Type u} (F : HypersurfaceFamily M) (hF : Finite {j // F.hyp j ≠ ∅})

/-- The finite set of nonempty members of a family with finitely many of them. -/
def nonemptyFinset : Finset F.ι := (Set.finite_coe_iff.mp hF).toFinset

theorem mem_nonemptyFinset (j : F.ι) : j ∈ F.nonemptyFinset hF ↔ F.hyp j ≠ ∅ :=
  Set.Finite.mem_toFinset _

/-- The nonempty members of a family with finitely many of them, listed in the order of the index
set (Kollár uses the ordering of the index set of `E` in Step 2.1 of the proof of
[Kol07, Theorem 103]). -/
def nonemptyList : List F.ι := (F.nonemptyFinset hF).sort (· ≤ ·)

theorem mem_nonemptyList (j : F.ι) : j ∈ F.nonemptyList hF ↔ F.hyp j ≠ ∅ := by
  rw [nonemptyList, Finset.mem_sort, mem_nonemptyFinset]

end HypersurfaceFamily

end Manifold

end
