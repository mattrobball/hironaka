/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The ideal-theoretic strict transforms of a closed subspace along a blow-up sequence

A closed subspace `Y ⊆ M`, given by its ideal sheaf `J`, is carried along a finite blow-up sequence
`π_0, …, π_{r-1}` with smooth centres by its **strict transforms** `Y_0 = Y`, `Y_{k+1} =
(π_k)^{-1}_* Y_k`: the stages of Kollár's restricted sequence [Kol07, Definition 30.2] and the
strict transforms `Ỹ_Z ⊂ Ũ_Z` in Włodarczyk's canonical embedded desingularization of a germ [Wlo09,
§4, (2)⇒(3) and (3)⇒(4)]. On manifolds each step is the strict transform of a closed subspace under
one blowing-up (`strictTransformSubspace`: the saturation of the total transform by the exceptional
divisor, [BM97, §3, Proposition 3.13]), taken at the witnesses of the `k`-th blow-up
(`FiniteSuccession.isClosedSubmanifold_center`, `FiniteSuccession.isBlowUp_map`). This is the
ideal-level counterpart of the set-level `FiniteSuccession.strictTransformSeq`, and
exactly the recursion that the fields `transform_zero`/`transform_succ` of
`AmbientBlowUpFactorization` spell out for the chain `Y_0, …, Y_r`: for the chain defined here both
fields hold by `rfl`.

The chain itself, `FiniteSuccession.strictTransformSubspaceSeq S J i` (the strict transform
`Y_i ⊆ U_i` of the closed subspace `J` of `M` at stage `i`, by recursion on `i`), is statement
vocabulary and lives in `Hironaka/Manifold/FiniteSuccession/Defs.lean`; this file holds its two
defining equations.

* `FiniteSuccession.strictTransformSubspaceSeq_zero`, `strictTransformSubspaceSeq_succ`.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- The chain starts with `Y_0 = J` (the field `transform_zero` of
`AmbientBlowUpFactorization`). -/
theorem strictTransformSubspaceSeq_zero (J : IdealSheaf M) :
    S.strictTransformSubspaceSeq J 0 = J := rfl

/-- `Y_{i+1}` is the strict transform of `Y_i` under the `i`-th blow-up at the succession's
witnesses (the field `transform_succ` of `AmbientBlowUpFactorization`). -/
theorem strictTransformSubspaceSeq_succ (J : IdealSheaf M) (i : Fin S.length) :
    S.strictTransformSubspaceSeq J i.succ =
      strictTransformSubspace (S.isClosedSubmanifold_center i) (S.isBlowUp_map i)
        (S.strictTransformSubspaceSeq J i.castSucc) := rfl

end AnalyticManifold.FiniteSuccession
