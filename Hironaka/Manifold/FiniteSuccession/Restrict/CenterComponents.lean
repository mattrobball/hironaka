/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.StrictSubspaceSeq
public import Hironaka.AnalyticSpace.Manifold.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
/-!
# The lift of the simple locus and the components of a centre

Kollár's proof of Corollary 22 [Kol07, Corollary 22, proof] compares, at the first stage `j` where
a centre `Z_j` contains the generic point `η_X` of the variety `X`, the centre with the strict
transform `X_j`: `η_X` is the generic point of `Z_j`, so that `Z_j → X̄` is birational and `Z_j`,
being blown up, is smooth. Analytically the generic point is replaced by the **lift of the simple
locus** `Reg X` of the closed subspace `X = V(𝓘)`, and the centre by the union of its connected
components meeting that lift. This module names the two sets:

* `AnalyticManifold.IdealSheaf.regSet J`: the simple locus of the closed subspace `V(J) ⊆ A` as
  a subset of the ambient manifold — the image of
  `J.toAnalyticSpace.regularLocus` (the simple points of the analytic
  space `IdealSheaf.toAnalyticSpace`) under the inclusion `toAnalyticSpaceι`; no separate
  definition of `Reg` is made.
* `AnalyticManifold.FiniteSuccession.liftReg S J i`: the lift of `Reg X` to the stage `i` of a
  blow-up sequence — the preimage of `regSet J` under the composite `σ^i = stageMap i` intersected
  with the support of the ideal-theoretic strict transform `X_i` (`strictTransformSubspaceSeq`).
* `AnalyticManifold.FiniteSuccession.IsCenterComponent S j C`: `C` is a connected component of
  the support of the centre `Z_j` (Mathlib's `connectedComponentIn`).

Over `ℂ` the strict transform of a reduced subspace is described set-theoretically in
[BM97, Remark 3.15]. The statements about `regSet` are proved in `RegSetBasic.lean` and
`LiftRegDense.lean`.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace AnalyticManifold.IdealSheaf

variable {K : Type} [RCLike K] {n : ℕ} {A : AnalyticManifold.{u} K (Fin n → K)}

/-- The simple locus `Reg X` of the closed subspace `X = V(J)` as a subset of the ambient
manifold: the image of `J.toAnalyticSpace.regularLocus` (the points
whose local ring is regular) under the inclusion `toAnalyticSpaceι`. -/
def regSet (J : IdealSheaf A) : Set A :=
  (fun y => (J.toAnalyticSpaceι y : A)) ''
    J.toAnalyticSpace.regularLocus

end AnalyticManifold.IdealSheaf

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {K : Type} [RCLike K] {n : ℕ} {A : AnalyticManifold.{u} K (Fin n → K)}
  (S : FiniteSuccession A)

/-- **The lift of `Reg X` to the stage `i`**: the points of the strict transform `X_i`
(`strictTransformSubspaceSeq`) lying over the simple locus of `X = V(J)` under the composite
`σ^i`. The analytic counterpart of the generic point `η_X` of the variety at the stage `j` in
[Kol07, Corollary 22, proof]. -/
def liftReg (J : IdealSheaf A) (i : Fin (S.length + 1)) : Set (S.stage i) :=
  S.stageMap i ⁻¹' IdealSheaf.regSet J ∩
      (S.strictTransformSubspaceSeq J i).support

/-- `C` is a connected component of the support of the centre `Z_j` (Mathlib's
`connectedComponentIn`): the analytic counterpart of the centre `Z_j` containing the generic
point at the stage `j` in [Kol07, Corollary 22, proof], one component at a time. -/
def IsCenterComponent (j : Fin S.length) (C : Set (S.stage j.castSucc)) : Prop :=
  ∃ z ∈ (S.center j).support, C = connectedComponentIn (S.center j).support z

end AnalyticManifold.FiniteSuccession

end
