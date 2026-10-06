/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Step21Defs
public import Hironaka.Resolution.Analytic.OrderReduction.ConcatPullback
public import Hironaka.Resolution.Analytic.OrderReduction.Induced
import Hironaka.Resolution.Analytic.OrderReduction.Step21Cosupp
import Hironaka.Resolution.Analytic.OrderReduction.Step22Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Step 2.1 along an arbitrary local analytic isomorphism: preparatory lemmas

Kollár asks that a blow-up sequence functor commute with every smooth morphism, the value on a
non-surjective one being the pull-back with its empty blow-ups deleted ([Kol07, 34.1], second
bullet); the functoriality of Step 2.1 of the proof of [Kol07, Theorem 103] is that of Lemma 102
([Kol07, 104, Step 2.3]). Along a local analytic isomorphism `h : N → M` that is not surjective a
member `E^j` may become empty, so the iteration over the nonempty members of the pulled-back
boundary runs over a sublist of the original one. This module proves the bookkeeping facts the
induction over the members along `h` needs (`Step21FamIndep.lean`); they are not in the sources.

* `BlowUpSequence.concat_nil_right` — the empty sequence is a right unit for the concatenation (the
  contribution of a member emptied by `h` disappears);
* `HypersurfaceFamily.nonemptyList_comap_eq_filter` — the nonempty members of `h⁻¹E` in the
  order of the index set are the nonempty members of `E` whose preimage is nonempty (both lists
  are sorted without duplicates and have the same members);
* `hyp_originalIdx_pullbackLiftLast_eq_empty` — in the pull-back of the induced triple along the
  lift of `h` to the last stage, the member coming from an emptied `E^j` is empty (the strict
  transform of `∅` is `∅`).
-/

public section

noncomputable section

open Set Topology AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The empty sequence of centres is a right unit for the concatenation. -/
theorem concat_nil_right : ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M),
    L.concat (nil (L.stage (Fin.last _))) = L
  | _, nil _ => rfl
  | _, cons hY rest => congrArg (cons hY) (concat_nil_right rest)

end AnalyticManifold.BlowUpSequence

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace HypersurfaceFamily

variable {M N : Type u} (F : HypersurfaceFamily M) (h : N → M)

/-- The nonempty members of the pulled-back family, in the order of the index set, are the nonempty
members of the family whose preimage is nonempty: both lists are sorted without duplicates and
have the same members (a member with nonempty preimage is nonempty). -/
theorem nonemptyList_comap_eq_filter (hF : Finite {j // F.hyp j ≠ ∅})
    (hF' : Finite {j // (F.comap h).hyp j ≠ ∅}) :
    (F.comap h).nonemptyList hF' =
      (F.nonemptyList hF).filter fun j => decide ((F.comap h).hyp j ≠ ∅) := by
  have e1 : (F.comap h).nonemptyList hF' =
      Finset.sort (α := F.ι) ((F.comap h).nonemptyFinset hF') (· ≤ ·) := rfl
  have e2 : F.nonemptyList hF = Finset.sort (α := F.ι) (F.nonemptyFinset hF) (· ≤ ·) := rfl
  rw [e1, e2]
  apply List.Perm.eq_of_sortedLE
  · exact (Finset.pairwise_sort _ _).sortedLE
  · exact ((Finset.pairwise_sort _ _).filter _).sortedLE
  · refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _)
      ((Finset.sort_nodup _ _).filter _)).mpr fun j => ?_
    constructor
    · intro hj
      have hne : (F.comap h).hyp j ≠ ∅ :=
        (HypersurfaceFamily.mem_nonemptyFinset _ _ _).mp
          ((Finset.mem_sort (α := F.ι) (· ≤ ·)).mp hj)
      refine List.mem_filter.mpr ⟨(Finset.mem_sort (α := F.ι) (· ≤ ·)).mpr
        ((HypersurfaceFamily.mem_nonemptyFinset _ _ _).mpr fun h0 => hne ?_), decide_eq_true hne⟩
      change h ⁻¹' F.hyp j = ∅
      rw [h0, Set.preimage_empty]
    · intro hj
      obtain ⟨-, hne⟩ := List.mem_filter.mp hj
      exact (Finset.mem_sort (α := F.ι) (· ≤ ·)).mpr
        ((HypersurfaceFamily.mem_nonemptyFinset _ _ _).mpr (of_decide_eq_true hne))

end HypersurfaceFamily

end Manifold

namespace Hironaka.Manifold.BO

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

variable {M N : AnalyticManifold.{u} 𝕜 E}

/-- In the pull-back along the lift to the last stage of the triple induced by a sequence `L`, the
member coming from a member `E^j` with `h⁻¹(E^j) = ∅` is empty: it is the strict transform of `∅`
along the pulled-back sequence (`strictTransformSeq_last_pullbackLiftLast`,
`strictTransformSeq_empty`). -/
theorem hyp_originalIdx_pullbackLiftLast_eq_empty (F : HypersurfaceFamily M)
    (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (j : F.ι)
    (hj : ⇑h ⁻¹' F.hyp j = ∅) :
    ((L.toSuccession.totalTransformSeqFrom F (Fin.last _)).comap
        ⇑(L.pullbackLiftLast h hh)).hyp (L.toSuccession.originalIdx F (Fin.last _) j) = ∅ := by
  rw [HypersurfaceFamily.comap_hyp, FiniteSuccession.hyp_originalIdx,
    ← BlowUpSequence.strictTransformSeq_last_pullbackLiftLast L h hh (F.hyp j), hj,
    FiniteSuccession.strictTransformSeq_empty]

end Hironaka.Manifold.BO

end
