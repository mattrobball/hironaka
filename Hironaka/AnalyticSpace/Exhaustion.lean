/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Defs
import Hironaka.AnalyticSpace.Restrict.Defs
import Hironaka.Manifold.Exhaustion
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Exhaustions of analytic `K`-spaces

An analytic `K`-space is countable at infinity [Hir64, Ch. 0, §1, p. 120, clause (ii)] — a
countable increasing union of relatively compact open subspaces, as [Hir64, Ch. 0, §1, p. 121,
footnote 10] words it for real spaces — and the resolution of [Kol07, 44] is obtained on such a
space from resolutions of neighbourhoods of compact sets; the gluing of [Wlo09, §4] and
[Wlo09, §4.3] likewise starts from an open cover with compact closures.

* `exists_opens_isCompact_closure_superset`: in a weakly locally compact Hausdorff space a compact
  set lies in an open set with compact closure (the interior of Mathlib's
  `exists_compact_superset`).
* `AnalyticSpace.exists_exhaustion`: an analytic `K`-space is exhausted by relatively compact opens
  `U₀ ⋐ U₁ ⋐ ⋯` with `⋃ Uₙ = X` — the opens `relCompactOpen` of
  `Hironaka/Manifold/Exhaustion.lean` cut out of Mathlib's `CompactExhaustion.choice`, which
  exists because the space is locally compact, σ-compact and Hausdorff.

Used by `Hironaka/Resolution/Analytic/Kol07Thm45/PieceGlueIndep.lean` and
`Hironaka/Resolution/Analytic/Kol07Thm45/PieceGlueProof.lean`.
-/

public section

open TopologicalSpace Set

universe u

namespace AnalyticSpace

/-- In a weakly locally compact Hausdorff space, a compact set lies in an open set with compact
closure (compare the opens `Vᵢ ⊆ Wᵢ` with compact closures of [Wlo09, §4]): the interior of a
compact neighbourhood `K'` (`exists_compact_superset`), whose closure is a closed subset of `K'`. -/
theorem exists_opens_isCompact_closure_superset {M : Type*} [TopologicalSpace M]
    [WeaklyLocallyCompactSpace M] [T2Space M] {S : Set M} (hS : IsCompact S) :
    ∃ W : Opens M, S ⊆ W ∧ IsCompact (closure (W : Set M)) := by
  obtain ⟨K', hK', hSK'⟩ := exists_compact_superset hS
  exact ⟨⟨interior K', isOpen_interior⟩, hSK',
    hK'.of_isClosed_subset isClosed_closure (closure_minimal interior_subset hK'.isClosed)⟩

variable {K : Type} [RCLike K]

/-- An analytic `K`-space is exhausted by relatively compact opens `U₀ ⋐ U₁ ⋐ ⋯` with `⋃ Uₙ = X`
([Kol07, 44]; [Hir64, Ch. 0, §1, p. 120, clause (ii)]): the opens `relCompactOpen` of
`Hironaka/Manifold/Exhaustion.lean` cut out of Mathlib's `CompactExhaustion.choice X`, which
exists by local compactness and σ-compactness. -/
theorem exists_exhaustion (X : AnalyticSpace.{u} K) :
    ∃ U : ℕ → Opens X, (∀ n, IsCompact (closure (U n : Set X))) ∧
      (∀ n, closure (U n : Set X) ⊆ U (n + 1)) ∧ ⋃ n, (U n : Set X) = univ :=
  ⟨Manifold.relCompactOpen (CompactExhaustion.choice X),
    fun n => Manifold.isCompact_closure_relCompactOpen _ n,
    fun n => Manifold.closure_relCompactOpen_subset_succ _ n,
    Manifold.iUnion_relCompactOpen _⟩

end AnalyticSpace
