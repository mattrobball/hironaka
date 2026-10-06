/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.StrictTransformSeq
import Hironaka.Manifold.BlowUp.Transform.Strict
import Hironaka.Manifold.BlowUp.Transform.StrictCharts
import Hironaka.Manifold.FiniteSuccession.Restrict.Bundle
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The strict transforms along a succession are closed submanifolds

In Kollár's restriction of a blow-up sequence to a closed subscheme `S`, the stage `S_{i+1}`, the
strict transform of `S_i` (the closure of `π_i⁻¹(S_i ∖ Z_i)`), is a closed subscheme of `X_{i+1}`,
with natural embeddings `S_i ↪ X_i` [Kol07, Definition 30.2]. The one-step statement for
manifolds is `IsClosedSubmanifold.strictTransform` (`Transform/StrictCharts.lean`, in the
codimension-`s` form: the strict transform of a closed submanifold containing the centre is a
closed submanifold, covered by the blow-up charts singled out in [Kol07, Theorem 88, proof]).
Along a succession (`FiniteSuccession.strictTransformSeq`): every strict transform of
a closed set is closed (`isClosed_strictTransformSeq`), the blow-downs carry `S_{i+1}` into `S_i`
(`strictTransformSeq_succ_subset_preimage`), and under the hypothesis `CentersIn` every `S_i` is a
closed submanifold of `X_i` of codimension `s` (`isClosedSubmanifold_strictTransformSeq`, by
induction on the stage; the step's chosen chart `chartAt i` is exchanged for the given `ψ` through
`IsClosedSubmanifold.congr_chart`). The strict transform of a closed subspace is described in
[BM97, §3, Proposition 3.13].
-/

public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M) (H : Set M)
  {s : ℕ}

/-- The strict transforms of a closed set along the succession are closed. -/
theorem isClosed_strictTransformSeqAux (hH : IsClosed H) :
    ∀ (i : ℕ) (hi : i < S.length + 1), IsClosed (S.strictTransformSeqAux H i hi)
  | 0, _ => hH
  | _ + 1, _ => isClosed_closure

/-- The strict transforms of a closed set along the succession are closed. -/
theorem isClosed_strictTransformSeq (hH : IsClosed H) (i : Fin (S.length + 1)) :
    IsClosed (S.strictTransformSeq H i) :=
  S.isClosed_strictTransformSeqAux H hH i.1 i.2

/-- For closed `H`, the blow-down carries `S_{i+1}` into `S_i` (the maps `π_i^S : S_{i+1} → S_i`
of a restricted blow-up sequence, [Kol07, Definition 30.2]). -/
theorem strictTransformSeq_succ_subset_preimage (hH : IsClosed H) (i : Fin S.length) :
    S.strictTransformSeq H i.succ ⊆ S.map i ⁻¹' S.strictTransformSeq H i.castSucc :=
  strictTransform_subset_preimage (S.map i).contMDiff.continuous
    (S.isClosed_strictTransformSeq H hH i.castSucc)

/-- The strict transforms of a closed submanifold along the succession are closed submanifolds of
the same codimension, at the level of the recursion. -/
theorem isClosedSubmanifold_strictTransformSeqAux (hH : IsClosedSubmanifold ψ H s)
    (hc : S.CentersIn H) :
    ∀ (i : ℕ) (hi : i < S.length + 1), IsClosedSubmanifold ψ (S.strictTransformSeqAux H i hi) s
  | 0, _ => hH
  | i + 1, hi => by
    have ih := isClosedSubmanifold_strictTransformSeqAux hH hc i (Nat.lt_of_succ_lt hi)
    have ih' := ih.congr_chart (S.chartAt ⟨i, Nat.lt_of_succ_lt_succ hi⟩)
    exact (ih'.strictTransform (S.isClosedSubmanifold_center ⟨i, Nat.lt_of_succ_lt_succ hi⟩)
      (S.isBlowUp_map ⟨i, Nat.lt_of_succ_lt_succ hi⟩)
      (hc ⟨i, Nat.lt_of_succ_lt_succ hi⟩)).congr_chart ψ

/-- Under the hypothesis `Z_i ⊆ S_i` for all `i`, every strict transform `S_i` is a closed
submanifold of `X_i` of the codimension of `S` (the natural embeddings `S_i ↪ X_i` of
[Kol07, Definition 30.2]). -/
theorem isClosedSubmanifold_strictTransformSeq (hH : IsClosedSubmanifold ψ H s)
    (hc : S.CentersIn H) (i : Fin (S.length + 1)) :
    IsClosedSubmanifold ψ (S.strictTransformSeq H i) s :=
  S.isClosedSubmanifold_strictTransformSeqAux H hH hc i.1 i.2

end AnalyticManifold.FiniteSuccession

end
