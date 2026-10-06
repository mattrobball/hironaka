/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Transform.Basic
public import Hironaka.Manifold.FiniteSuccession.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Strict transforms of a subset along a blow-up sequence; centres inside a submanifold

Kollár restricts a blow-up sequence `Π : X_r → ⋯ → X_0 = X` with centres `Z_i` to a closed
subscheme `S ⊆ X` [Kol07, Definition 30.2]: the restricted sequence runs through the subschemes
`S_{i+1} := Bl_{Z_i ∩ S_i} S_i`, naturally identified with the birational transform of `S_i` in
`X_{i+1}`. On analytic manifolds the `S_i` are the iterated strict transforms `S_0 = S`,
`S_{i+1} = closure (π_i⁻¹(S_i ∖ Z_i))` (`strictTransformSet`). Since the restriction of a smooth
blow-up sequence need not be a smooth blow-up sequence [Kol07, Definition 30.2], and a finite
succession (`FiniteSuccession`) has smooth centres, the restricted succession is formed under the
hypothesis that every centre lies in the strict transform of `S` at its stage, so that the
restricted centres `Z_i ∩ S_i = Z_i` are smooth. This module provides

* `FiniteSuccession.strictTransformSeq S H i`: the strict transforms `H_i ⊆ X_i` of a subset
  `H ⊆ M` along the succession, by recursion on `i` (`H_0 = H`, `H_{i+1} =
  strictTransformSet (S.map i) (S.center i).support H_i`);
* `FiniteSuccession.CentersIn S H`: every centre `Z_i` lies in the strict transform `H_i`.

These are the stages and the hypothesis of the restricted succession constructed in
`StrictSubmanifold.lean` and `Restrict.lean`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- The strict transforms `H_i ⊆ X_i` of a subset `H ⊆ M` along the succession, indexed by a
natural number together with a proof that it is a stage: `H_0 = H`,
`H_{i+1} = closure (π_i⁻¹(H_i ∖ Z_i))` (`strictTransformSet`); Kollár's `S_{i+1}`, identified with
the birational transform of `S_i` [Kol07, Definition 30.2]. -/
def strictTransformSeqAux (H : Set M) :
    ∀ (i : ℕ) (h : i < S.length + 1), Set (finStages M S.later ⟨i, h⟩)
  | 0, _ => H
  | i + 1, h =>
    strictTransformSet (S.map ⟨i, Nat.lt_of_succ_lt_succ h⟩)
      (S.center ⟨i, Nat.lt_of_succ_lt_succ h⟩).support
      (strictTransformSeqAux H i (Nat.lt_of_succ_lt h))

/-- The strict transform `H_i ⊆ X_i` of `H ⊆ M` at the stage `i` of the succession, Kollár's
`S_i` [Kol07, Definition 30.2]. -/
def strictTransformSeq (H : Set M) (i : Fin (S.length + 1)) : Set (S.stage i) :=
  S.strictTransformSeqAux H i.1 i.2

theorem strictTransformSeq_zero (H : Set M) : S.strictTransformSeq H 0 = H := rfl

theorem strictTransformSeq_succ (H : Set M) (i : Fin S.length) :
    S.strictTransformSeq H i.succ =
      strictTransformSet (S.map i) (S.center i).support (S.strictTransformSeq H i.castSucc) :=
  rfl

/-- Every centre of the succession lies in the strict transform of `H` at its stage: the
hypothesis under which the restriction of the succession to `H` [Kol07, Definition 30.2] has the
smooth centres `Z_i ∩ H_i = Z_i`. -/
def CentersIn (H : Set M) : Prop :=
  ∀ i : Fin S.length, (S.center i).support ⊆ S.strictTransformSeq H i.castSucc

end AnalyticManifold.FiniteSuccession

end
