/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.ConcatPullback
public import Hironaka.Resolution.Analytic.Functor.EraseEmptyConcat
public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
public import Hironaka.Resolution.Analytic.Functor.Family
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The end results of a compatible family embed

The second clause of [Kol07, 34.1], [Wlo09, Theorem 2.0.3, (4)] and [Wlo09, Theorem 3.5.1, (2)],
per open: for `U₁ ≤ U₂` relatively compact, the end result of a compatible family's value on `U₁`
sits inside the end result of its value on `U₂`. The value on `U₁` is the value on `U₂` pulled
back along the open inclusion with the empty blow-ups erased (`CompatibleFamily.compat`), so the
last stages are identified by the last-stage transport of the erasure (`eraseEmptyLast`,
`stageOfEq`) followed by the last-stage lift of the inclusion (`pullbackLiftLast`). This module
builds the embedding `CompatibleFamily.endResultEmbedding`; its properties (an open embedding
onto the preimage of `U₁`, over `M`, functorial) are proved in
`Hironaka.Resolution.Analytic.Functor.EndResultEmbeddingLemmas` and feed the direct limit of the
end results (`Hironaka.Resolution.Analytic.Functor.LimitFamily`).
-/

@[expose] public section

universe u

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {T : Manifold.AnalyticTriple ψ₀ M}

/-- **The
embedding of the end result over `U₁` into the end result over `U₂`** for `U₁ ≤ U₂` — the last-stage
transport of the erasure identity `compat` (`stageOfEq`), the inverse of the erasure's last-stage
isomorphism (`eraseEmptyLast`), then the last-stage lift of the open inclusion `U₁ ⊆ U₂`
(`pullbackLiftLast`). Its properties (an open embedding onto the preimage of `U₁`, over `M`,
functorial) are proved in `Hironaka.Resolution.Analytic.Functor.EndResultEmbeddingLemmas`. -/
noncomputable def CompatibleFamily.endResultEmbedding (C : CompatibleFamily T) {U₁ U₂ : Opens M}
    (hU₁ : IsCompact (closure (U₁ : Set M))) (hU₂ : IsCompact (closure (U₂ : Set M)))
    (h : U₁ ≤ U₂) :
    AnalyticMap ((C.seqOn U₁ hU₁).stage (Fin.last _)) ((C.seqOn U₂ hU₂).stage (Fin.last _)) :=
  ((C.seqOn U₂ hU₂).pullbackLiftLast (M.restrictLE h) (isLocalDiffeomorph_restrictLE h)).comp
    ((Diffeomorph.toAnalyticMap
      ((C.seqOn U₂ hU₂).pullback (M.restrictLE h)
        (isLocalDiffeomorph_restrictLE h)).eraseEmptyLast.symm).comp
      (Diffeomorph.toAnalyticMap (AnalyticManifold.BlowUpSequence.stageOfEq
          (C.compat U₁ U₂ hU₁ hU₂ h))))

end Hironaka.Manifold
