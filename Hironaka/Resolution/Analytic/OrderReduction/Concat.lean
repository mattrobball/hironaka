/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmpty
public import Hironaka.Manifold.FiniteSuccession.Order
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Concatenation of sequences of centres

Step 2.1 of the proof of [Kol07, Theorem 103] applies Lemma 102 to each boundary member in turn,
"at the end we get a blow-up sequence" `Π : X_r → X`: the blow-up sequences of the successive
applications are composed, the value on the induced triple at the last stage being appended. This
module defines the composition on sequences of centres, by recursion on the first sequence:

* `BlowUpSequence.concat L L'` — the sequence `L` followed by the sequence `L'` on the last stage of
  `L` (`concat_nil`, `concat_cons`, `length_concat`);
* `noEmptyCenters_concat` — the convention of no empty centres ([Kol07, 32]) is inherited from the
  pieces;
* `isOfOrderGe_concat` — the clauses (1′)–(4′) of [Kol07, Definition 66] hold for the concatenation
  when they hold for `L` starting with `(𝓘, m, E)` and for `L'` starting with the controlled
  transform and the boundary of `L` at its last stage.

The concatenation is the operation iterated in `Step21Defs.lean`.
-/

@[expose] public section

noncomputable section

open Set Topology AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The concatenation of a sequence of centres `L` on `M` with a sequence `L'` on the last stage of
`L` (the composition of blow-up sequences in Step 2.1 of the proof of [Kol07, Theorem 103]). -/
def concat : {M : AnalyticManifold.{u} 𝕜 E} → (L : BlowUpSequence ψ₀ M) →
    BlowUpSequence ψ₀ (L.stage (Fin.last _)) → BlowUpSequence ψ₀ M
  | _, nil _, L' => L'
  | _, cons hY rest, L' => cons hY (rest.concat L')

variable {M : AnalyticManifold.{u} 𝕜 E}

theorem concat_nil (L' : BlowUpSequence ψ₀ M) : (nil (ψ₀ := ψ₀) M).concat L' = L' := rfl

theorem concat_cons {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY)) (L' : BlowUpSequence ψ₀ ((cons hY rest).stage
        (Fin.last _))) :
    (cons hY rest).concat L' = cons hY (rest.concat L') := rfl

/-- The length of a concatenation is the sum of the lengths. -/
theorem length_concat : ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (L' : BlowUpSequence ψ₀ (L.stage (Fin.last _))), (L.concat L').length = L.length + L'.length
  | _, nil _, L' => (Nat.zero_add _).symm
  | _, cons hY rest, L' => by
    change (rest.concat L').length + 1 = rest.length + 1 + L'.length
    rw [length_concat rest L']
    exact Nat.add_right_comm _ _ _

/-- A concatenation has no empty centre when the pieces have none ([Kol07, 32]). -/
theorem noEmptyCenters_concat : ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (L' : BlowUpSequence ψ₀ (L.stage (Fin.last _))), L.NoEmptyCenters → L'.NoEmptyCenters →
    (L.concat L').NoEmptyCenters
  | _, nil _, _, _, h' => h'
  | _, cons hY rest, L', h, h' => by
    rw [concat_cons, noEmptyCenters_cons_iff]
    obtain ⟨hne, hrest⟩ := (noEmptyCenters_cons_iff hY rest).mp h
    exact ⟨hne, noEmptyCenters_concat rest L' hrest h'⟩

/-- The concatenation is a smooth blow-up sequence of order `≥ m` starting with `(𝓘, m, E₀)`
([Kol07, Definition 66 (1′)–(4′)]) when `L` is, and `L'` is one starting with the controlled
transform and the boundary of `L` at its last stage. -/
theorem isOfOrderGe_concat : ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (L' : BlowUpSequence ψ₀ (L.stage (Fin.last _))) {I E₀ : IdealSheaf M} {m : ℕ},
    L.toSuccession.IsOfOrderGe I m E₀ →
    L'.toSuccession.IsOfOrderGe (L.toSuccession.markedTransformSeq I m (Fin.last _)) m
      (L.toSuccession.boundarySeq E₀ (Fin.last _)) →
    (L.concat L').toSuccession.IsOfOrderGe I m E₀
  | _, nil _, _, _, _, _, _, h' => h'
  | _, cons hY rest, L', I, E₀, m, h, h' => by
    rw [concat_cons, toSuccession_cons, FiniteSuccession.isOfOrderGe_cons_iff]
    rw [toSuccession_cons, FiniteSuccession.isOfOrderGe_cons_iff] at h
    refine ⟨h.1, isOfOrderGe_concat rest L' h.2 ?_⟩
    have e1 : (cons hY rest).toSuccession.markedTransformSeq I m
          (Fin.last (cons hY rest).toSuccession.length) =
        rest.toSuccession.markedTransformSeq
          ((FiniteSuccession.cons ψ₀ hY rest.toSuccession).markedTransformSeq I m
            (Fin.succ (0 : Fin (rest.length + 1)))) m (Fin.last rest.toSuccession.length) :=
      FiniteSuccession.cons_markedTransformSeqAux_succ hY rest.toSuccession I m rest.length
        (Fin.last (rest.length + 1)).2
    have e2 : (cons hY rest).toSuccession.boundarySeq E₀
          (Fin.last (cons hY rest).toSuccession.length) =
        rest.toSuccession.boundarySeq
          (IdealSheaf.reducedTransform (blowUpπ ψ₀ hY) E₀ hY.idealSheaf)
          (Fin.last rest.toSuccession.length) :=
      FiniteSuccession.cons_boundarySeqAux_succ hY rest.toSuccession E₀ rest.length
        (Fin.last (rest.length + 1)).2
    rw [e1, e2] at h'
    exact h'

end AnalyticManifold.BlowUpSequence

end
