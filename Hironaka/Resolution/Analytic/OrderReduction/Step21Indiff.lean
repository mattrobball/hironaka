/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BoundaryEnlarge
public import Hironaka.Resolution.Analytic.OrderReduction.Step21Defs
import Hironaka.Resolution.Analytic.OrderReduction.Step21Cosupp
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Steps 2.1 and 2 and empty boundary members: the index correspondence

Kollár's functors ignore empty blow-ups ([Kol07, 32]); the counterpart of this convention for
the members of the boundary is the indifference of a functor to empty boundary members
(`AnalyticBlowUpSequenceAssignment.IndifferentToEmptyMembers`). For a boundary `F'`
with simple normal crossings embedding order-preservingly into `E` along `e`, the members matched
along `e` and empty outside its range, Step 2.1 of the proof of [Kol07, Theorem 103] on `(M, 𝓘, E)`
equals Step 2.1 on `(M, 𝓘, F')`: the nonempty members of `E` in the order of the index set are the
images along `e` of those of `F'` (`nonemptyList_eq_map`, both lists sorted and permutations of
each other), and at each step the data of Lemma 102 are indifferent on the induced triples, whose
boundaries correspond along the index correspondence of `BoundaryEnlarge.lean`, here an order
embedding (`corrIdx`) matching the members and empty outside its range. Step 2.2 then coincides,
since the exceptional divisors, the transform of the hypersurface of maximal contact and the
controlled transform do not see the index set of the boundary, so Step 2 is indifferent as well.

* `FiniteSuccession.corrIdxAux_le_iff`, `FiniteSuccession.corrIdx` — the index correspondence as an
  order embedding; `hyp_corrIdxAux_of_forall`, `hyp_eq_empty_of_notMem_range_corrIdx` — matched
  members, empty outside the range.
* `BO.nonemptyList_eq_map` — the sorted lists of nonempty members correspond along `e`.

The argument itself is carried out in the compatible-family form in `Step21FamIndiff.lean`
(Step 2.1) and `Step2AssemblyComm.lean` (Step 2).
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)
  {F G : HypersurfaceFamily M}

/-- The index correspondence induced by an order embedding is order-reflecting at every stage:
transforms of original members compare as the originals, exceptional divisors as themselves, and
the lexicographic sum puts the new divisor last. -/
theorem corrIdxAux_le_iff (e : G.ι ↪o F.ι) : ∀ (i : ℕ) (h : i < S.length + 1)
    (a b : (S.totalTransformSeqFromAux G i h).ι),
    S.corrIdxAux e i h a ≤ S.corrIdxAux e i h b ↔ a ≤ b
  | 0, _, a, b => e.le_iff_le
  | i + 1, h, a, b => by
    obtain ⟨a', rfl⟩ : ∃ a', toLex a' = a := ⟨ofLex a, rfl⟩
    obtain ⟨b', rfl⟩ : ∃ b', toLex b' = b := ⟨ofLex b, rfl⟩
    rcases a' with a' | ua <;> rcases b' with b' | ub
    · change toLex (Sum.inl (S.corrIdxAux e i _ a')) ≤ toLex (Sum.inl (S.corrIdxAux e i _ b')) ↔
        toLex (Sum.inl a') ≤ toLex (Sum.inl b')
      exact (Sum.Lex.inl_le_inl_iff.trans (corrIdxAux_le_iff e i (Nat.lt_of_succ_lt h) a' b')).trans
        Sum.Lex.inl_le_inl_iff.symm
    · change toLex (Sum.inl (S.corrIdxAux e i _ a')) ≤ toLex (Sum.inr ub) ↔
        toLex (Sum.inl a') ≤ toLex (Sum.inr ub)
      exact iff_of_true (Sum.Lex.inl_le_inr _ _) (Sum.Lex.inl_le_inr _ _)
    · change toLex (Sum.inr ua) ≤ toLex (Sum.inl (S.corrIdxAux e i _ b')) ↔
        toLex (Sum.inr ua) ≤ toLex (Sum.inl b')
      exact iff_of_false Sum.Lex.not_inr_le_inl Sum.Lex.not_inr_le_inl
    · exact iff_of_true (Sum.Lex.inr_le_inr_iff.mpr (le_of_eq (Subsingleton.elim ua ub)))
        (Sum.Lex.inr_le_inr_iff.mpr (le_of_eq (Subsingleton.elim ua ub)))

/-- The index correspondence at stage `i` induced by an order embedding, as an order embedding. -/
def corrIdx (e : G.ι ↪o F.ι) (i : Fin (S.length + 1)) :
    (S.totalTransformSeqFrom G i).ι ↪o (S.totalTransformSeqFrom F i).ι :=
  OrderEmbedding.ofMapLEIff (S.corrIdxAux e i.1 i.2) (S.corrIdxAux_le_iff e i.1 i.2)

theorem corrIdx_apply (e : G.ι ↪o F.ι) (i : Fin (S.length + 1))
    (a : (S.totalTransformSeqFrom G i).ι) : S.corrIdx e i a = S.corrIdxAux e i.1 i.2 a := rfl

/-- When the members of `G` are members of `F` along `e`, the members of the stage-`i` families
correspond along the index correspondence. -/
theorem hyp_corrIdxAux_of_forall (e : G.ι → F.ι) (hmem : ∀ j, G.hyp j = F.hyp (e j))
    (i : Fin (S.length + 1)) (kk : (S.totalTransformSeqFrom G i).ι) :
    (S.totalTransformSeqFrom G i).hyp kk =
      (S.totalTransformSeqFrom F i).hyp (S.corrIdxAux e i.1 i.2 kk) := by
  rcases S.originalIdxAux_or_exceptionalEmb G i.1 i.2 kk with ⟨j, rfl⟩ | ⟨k, rfl⟩
  · rw [S.corrIdxAux_originalIdxAux e]
    change (S.totalTransformSeqFrom G i).hyp (S.originalIdx G i j) =
      (S.totalTransformSeqFrom F i).hyp (S.originalIdx F i (e j))
    rw [hyp_originalIdx, hyp_originalIdx, hmem j]
  · rw [S.corrIdxAux_exceptionalEmb e]
    change (S.totalTransformSeqFromAux G i.1 i.2).hyp (S.exceptionalEmb G i.1 i.2 k) =
      (S.totalTransformSeqFromAux F i.1 i.2).hyp (S.exceptionalEmb F i.1 i.2 k)
    rw [hyp_exceptionalEmb, hyp_exceptionalEmb]

/-- When the members of `F` outside the range of `e` are empty, the members of the stage-`i` family
from `F` outside the range of the index correspondence are empty (the exceptional divisors all lie
in the range). -/
theorem hyp_eq_empty_of_notMem_range_corrIdx (e : G.ι ↪o F.ι)
    (hout : ∀ b, b ∉ Set.range e → F.hyp b = ∅) (i : Fin (S.length + 1))
    (b : (S.totalTransformSeqFrom F i).ι) (hb : b ∉ Set.range (S.corrIdx e i)) :
    (S.totalTransformSeqFrom F i).hyp b = ∅ := by
  rcases S.originalIdxAux_or_exceptionalEmb F i.1 i.2 b with ⟨j, rfl⟩ | ⟨k, rfl⟩
  · have hj : j ∉ Set.range e := by
      rintro ⟨j', rfl⟩
      exact hb ⟨S.originalIdx G i j', S.corrIdxAux_originalIdxAux e i.1 i.2 j'⟩
    change (S.totalTransformSeqFrom F i).hyp (S.originalIdx F i j) = ∅
    rw [hyp_originalIdx, hout j hj, strictTransformSeq_empty]
  · exact absurd ⟨S.exceptionalEmb G i.1 i.2 k, S.corrIdxAux_exceptionalEmb e i.1 i.2 k⟩ hb

end AnalyticManifold.FiniteSuccession

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  {s : ℕ}

namespace BO

open _root_.Manifold

section StepTwoOne

variable (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BOClass s T)
  (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc ψ₀) (e : F'.ι ↪o T.F.ι)
  (he : ∀ i, T.F.hyp (e i) = F'.hyp i) (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅)

omit [FiniteDimensional 𝕜 E] in
include he he' in
/-- The nonempty members of `E` in the order of the index set are the images along `e` of the
nonempty members of `F'` in the order of theirs: both lists are sorted and are permutations of each
other, the nonempty members of `E` lying in the range of `e` with the matched members. -/
theorem nonemptyList_eq_map (hF : Finite {j // T.F.hyp j ≠ ∅}) (hF' : Finite {j // F'.hyp j ≠ ∅}) :
    T.F.nonemptyList hF = (F'.nonemptyList hF').map e := by
  have hfin : T.F.nonemptyFinset hF = (F'.nonemptyFinset hF').map e.toEmbedding := by
    ext b
    rw [HypersurfaceFamily.mem_nonemptyFinset, Finset.mem_map]
    constructor
    · intro hb
      by_cases hr : b ∈ Set.range e
      · obtain ⟨a, rfl⟩ := hr
        refine ⟨a, (HypersurfaceFamily.mem_nonemptyFinset _ _ _).mpr ?_, rfl⟩
        rw [← he a]
        exact hb
      · exact absurd (he' b hr) hb
    · rintro ⟨a, ha, rfl⟩
      change T.F.hyp (e a) ≠ ∅
      rw [he a]
      exact (HypersurfaceFamily.mem_nonemptyFinset _ _ _).mp ha
  apply List.Perm.eq_of_sortedLE
  · exact (Finset.pairwise_sort _ _).sortedLE
  · exact ((Finset.pairwise_sort _ _).map (f := ⇑e) fun a b hab => e.map_rel_iff.mpr hab).sortedLE
  · rw [← Multiset.coe_eq_coe, ← Multiset.map_coe]
    unfold HypersurfaceFamily.nonemptyList
    rw [Finset.sort_eq, Finset.sort_eq, hfin, Finset.map_val]
    rfl

end StepTwoOne

end BO

end Hironaka.Manifold

end
