/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.CenterList
public import Hironaka.Manifold.FiniteSuccession.Restrict.Pushforward
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The push-forward of a list of centres along a closed submanifold

A blow-up sequence functor `B` commutes with closed embeddings if `B(X, I_X, E) = j_* B(Y, I_Y,
E|_Y)` whenever `j : Y ↪ X` is a closed embedding of smooth schemes, `0 ≠ I_Y ⊂ 𝒪_Y` and
`0 ≠ I_X ⊂ 𝒪_X` are ideal sheaves with `𝒪_X/I_X = j_*(𝒪_Y/I_Y)`, and `E` is a simple normal
crossing divisor on `X` such that `E|_Y` is one on `Y` [Kol07, 34.3]; the form used in the proof
of the order-reduction theorem is `BO_{n,1}(X, I, ∅) = τ_* BMO_{n−1,1}(Y, J, 1, ∅)`
[Kol07, Theorem 103, (3)]. The push-forward `j_* B` of a blow-up sequence of the closed
submanifold `S` [Kol07, Definition 30, 30.3] is `FiniteSuccession.pushforward` of
`Hironaka.Manifold.FiniteSuccession.Restrict.Pushforward` on finite successions; here the same
recursion is run on the lists of centres: `BlowUpSequence.pushforward hS L` for `L` a list on the
bundled submanifold `hS.toAnalyticManifold` (model `𝕜^{n−s}`, identity chart), with centres
`Z_i^X := (j_i)_* Z_i^S` (`PushforwardStage`, `blowUpStep`, with the identification
`e_i : T_i ≃ S_i` carried by the recursion), the stages being the chosen blowings-up along them.
The identification with the push-forward of the succession is `toSuccession`
(`Hironaka.Manifold.FiniteSuccession.Functor.ToSuccessionPushforward`).
-/

@[expose] public section

noncomputable section

open Set
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n s : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- [Kol07, Definition 30, 30.3] on lists, the recursion: from a push-forward stage
`(X_i, S_i ⊆ X_i, e_i : T_i ≃ S_i)` and a list on `T_i`, the list on `X_i` with centres
`Z_i^X := (j_i)_* Z_i^S` (`PushforwardStage.blowUpStep` carries the next stage). -/
def pushforwardAux : {Tᵢ : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)} →
    (P : PushforwardStage ψ s Tᵢ) →
    BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Tᵢ → BlowUpSequence ψ P.space
  | _, P, nil _ => nil P.space
  | _, P, cons hZ rest =>
    cons (P.isClosedSubmanifold_imageVal_image hZ)
      (pushforwardAux (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)) rest)

/-- [Kol07, Definition 30, 30.3], the push-forward `j_* B` on lists of centres: for a closed
submanifold `hS : IsClosedSubmanifold ψ S s` and a list `L` on the bundled `S`, the list on `M`
whose centres are `Z_i^X := (j_i)_* Z_i^S` — the recursion `pushforwardAux` started at
`(M, S, e_0 = id)`. -/
def pushforward {M : AnalyticManifold.{u} 𝕜 E} {S : Set M} (hS : IsClosedSubmanifold ψ S s)
    (L : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) hS.toAnalyticManifold) :
    BlowUpSequence ψ M :=
  pushforwardAux (⟨M, S, hS, Diffeomorph.refl _ _ _⟩ : PushforwardStage ψ s hS.toAnalyticManifold)
    L

end AnalyticManifold.BlowUpSequence

end
