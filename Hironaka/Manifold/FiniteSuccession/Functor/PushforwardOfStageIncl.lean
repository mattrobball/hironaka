/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.ToSuccessionPushforward
import Hironaka.Manifold.BlowUp.Transform.Object
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The inclusions of the stages into the push-forward from a stage

The push-forward `PushforwardStage.pushforwardOfStage P T` of a finite succession `T` from a
push-forward stage `P = (X, S ⊆ X, e : T₀ ≃ S)` ([Kol07, Definition 30.3] from an arbitrary start;
`Hironaka.Manifold.FiniteSuccession.Functor.ToSuccessionPushforward`) carries the natural
inclusions `j_i ∘ e_i : T_i → X_i` of the stages of `T` into its own stages, Kollár's `j_i`
composed with the identifications `e_i`:

* `PushforwardStage.inclStage P T i`, a closed embedding (`isClosedEmbedding_inclStage`), equal to
  `P.incl` at stage `0` (`inclStage_zero`);
* the inclusions commute with the blow-downs (`inclStage_map`) and with the composite blow-downs
  (`stageMap_inclStage`: the inclusion followed by `σ^X_i` is `σ^T_i` followed by `P.incl`);
* the centre `Z_i^X` of the push-forward is the image of the centre `Z_i^T`
  (`support_center_pushforwardOfStage`).

These are the lemmas of `Hironaka.Manifold.FiniteSuccession.Restrict.Pushforward` on
`FiniteSuccession.pushforwardIncl` for the push-forward from the canonical start `(M, S, id)`,
repeated for an arbitrary start — the start `(U, S ∩ U, e)` of the push-forward over one open
(`IsClosedSubmanifold.restrictStageOf`), through which a blow-up sequence functor commutes with
closed embeddings over the compact sets.
-/

@[expose] public section

noncomputable section

open Set
open scoped Manifold ContDiff

universe u

namespace Manifold.PushforwardStage

open AnalyticManifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n s : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {T₀ : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)}
  (P : PushforwardStage ψ s T₀) (T : FiniteSuccession T₀)

/-- The natural inclusions `j_i ∘ e_i : T_i → X_i` of the stages of `T` into the stages of its
push-forward from `P` ([Kol07, Definition 30.3]). -/
def inclStage : ∀ i : Fin (T.length + 1),
    C^ω⟮𝓘(𝕜, Fin (n - s) → 𝕜), T.stage i; 𝓘(𝕜, E), (pushforwardOfStage P T).stage i⟯
  | ⟨0, hi⟩ => (stageAux P T 0 hi).incl
  | ⟨i + 1, hi⟩ => (stageAux P T (i + 1) hi).incl

/-- The inclusions are closed embeddings. -/
theorem isClosedEmbedding_inclStage (i : Fin (T.length + 1)) :
    Topology.IsClosedEmbedding (inclStage P T i) := by
  obtain ⟨i, hi⟩ := i
  rcases i with _ | i
  · exact (stageAux P T 0 hi).isClosedEmbedding_incl
  · exact (stageAux P T (i + 1) hi).isClosedEmbedding_incl

/-- The inclusion at stage `0` is the inclusion of the start stage. -/
theorem inclStage_zero : inclStage P T 0 = P.incl :=
  ContMDiffMap.ext fun _ => rfl

/-- The centre of the push-forward at step `i` is the image of the centre of `T` under the
inclusion (`Z_i^X := (j_i)_* Z_i^T`, [Kol07, Definition 30.3]). -/
theorem support_center_pushforwardOfStage (i : Fin T.length) :
    ((pushforwardOfStage P T).center i).support =
      inclStage P T i.castSucc '' (T.center i).support := by
  obtain ⟨i, hi⟩ := i
  rcases i with _ | i
  · change (centerOf P T 0 hi).support = (stageAux P T 0 _).incl '' (T.center ⟨0, hi⟩).support
    rw [centerOf, (centerOfSub P T 0 hi).cosupport_idealSheaf]
    exact (stageAux P T 0 _).imageVal_image_eq _
  · change (centerOf P T (i + 1) hi).support =
      (stageAux P T (i + 1) _).incl '' (T.center ⟨i + 1, hi⟩).support
    rw [centerOf, (centerOfSub P T (i + 1) hi).cosupport_idealSheaf]
    exact (stageAux P T (i + 1) _).imageVal_image_eq _

/-- The inclusions commute with the blow-downs (the squares of Kollár's diagram). -/
theorem inclStage_map (i : Fin T.length) (p : T.stage i.succ) :
    inclStage P T i.castSucc (T.map i p) =
      (pushforwardOfStage P T).map i (inclStage P T i.succ p) := by
  obtain ⟨i, hi⟩ := i
  rcases i with _ | i
  · exact (congrArg Subtype.val
      ((stageAux P T 0 (Nat.lt_succ_of_lt hi)).restrictMap_blowUpStep_iso
        (T.centerSub 0 hi) (T.isBlowUpSub 0 hi) p)).symm
  · exact (congrArg Subtype.val
      ((stageAux P T (i + 1) (Nat.lt_succ_of_lt hi)).restrictMap_blowUpStep_iso
        (T.centerSub (i + 1) hi) (T.isBlowUpSub (i + 1) hi) p)).symm

/-- The inclusions commute with the composite blow-downs: the inclusion at stage `i` followed by
`σ^X_i` is `σ^T_i` followed by the inclusion of the start stage. -/
theorem stageMap_inclStage : ∀ (i : ℕ) (hi : i < T.length + 1) (p : T.stage ⟨i, hi⟩),
    (pushforwardOfStage P T).stageMap ⟨i, hi⟩ (inclStage P T ⟨i, hi⟩ p) =
      P.incl (T.stageMap ⟨i, hi⟩ p)
  | 0, _, _ => rfl
  | i + 1, hi, p => by
    have ih := stageMap_inclStage i (Nat.lt_of_succ_lt hi) (T.map ⟨i, Nat.lt_of_succ_lt_succ hi⟩ p)
    have hsq := inclStage_map P T ⟨i, Nat.lt_of_succ_lt_succ hi⟩ p
    exact (congrArg ((pushforwardOfStage P T).stageMap ⟨i, Nat.lt_of_succ_lt hi⟩) hsq).symm.trans ih

/-- `stageMap_inclStage` for a stage index in `Fin`. -/
theorem stageMap_inclStage' (i : Fin (T.length + 1)) (p : T.stage i) :
    (pushforwardOfStage P T).stageMap i (inclStage P T i p) = P.incl (T.stageMap i p) :=
  stageMap_inclStage P T i.1 i.2 p

end Manifold.PushforwardStage

end

end
