/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Induced
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The non-original members of the boundary family are finitely many

Along a finite succession the boundary family `totalTransformSeqFrom F` gains one member per stage
(the exceptional divisor, [Kol07, Definition 25]); the members that are not transforms of the
original ones (`originalIdx`) are therefore finitely many. This is the finiteness clause required
of the boundary of the disjoined triple of [Kol07, 72], whose boundary is the total transform of
finitely many components with the original members collapsed into one (`Collapse.lean`,
`DisjoinInput.lean`).
-/

public section

universe u

open Set

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M) (F : HypersurfaceFamily M)

/-- The non-original members of the boundary family at stage `k` form a finite set: none at stage
`0`, and at stage `k + 1` the exceptional divisor together with the images of the non-original
members of stage `k`. -/
theorem finite_setOf_notMem_range_originalIdxAux :
    ∀ (k : ℕ) (h : k < S.length + 1),
      {x : (S.totalTransformSeqFromAux F k h).ι | x ∉ Set.range (S.originalIdxAux F k h)}.Finite
  | 0, _ => Set.finite_empty.subset fun x hx => hx ⟨x, rfl⟩
  | k + 1, h => by
    have ih := finite_setOf_notMem_range_originalIdxAux k (Nat.lt_of_succ_lt h)
    refine ((ih.image fun y => (toLex (Sum.inl y) :
      (S.totalTransformSeqFromAux F k (Nat.lt_of_succ_lt h)).ι ⊕ₗ PUnit.{u + 1})).union
      (Set.finite_singleton (toLex (Sum.inr PUnit.unit)))).subset fun x hx => ?_
    rcases hx' : ofLex x with y | u
    · left
      refine ⟨y, fun ⟨j, hj⟩ => hx ⟨j, ?_⟩, ?_⟩
      · change toLex (Sum.inl (S.originalIdxAux F k (Nat.lt_of_succ_lt h) j)) = x
        rw [hj, ← hx']
        rfl
      · change toLex (Sum.inl y) = x
        rw [← hx']
        rfl
    · right
      rw [Set.mem_singleton_iff, ← hx']
      rfl

/-- The non-original members of the boundary family at stage `i` are finitely many. -/
theorem finite_notMem_range_originalIdx (i : Fin (S.length + 1)) :
    Finite {x : (S.totalTransformSeqFrom F i).ι // x ∉ Set.range (S.originalIdx F i)} :=
  (S.finite_setOf_notMem_range_originalIdxAux F i.1 i.2).to_subtype

end AnalyticManifold.FiniteSuccession
