/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimAt
public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1For
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The stage predicates of CP1

The tower induction for the statement CP1 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) runs on two predicates indexed by the
stage `n` of the tower of order reductions (`tower stage0 n`; [Kol07, 70]), the analogues for CP1 of
`ClaimBOAt` and `ClaimBMOAt` (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimAt`): CP1 along the
run of the stage-`n` order reduction `BO_{n,1}` on every triple of `BOClass n 1`, and along the run
of the stage-`n` marked order reduction `BMO_{n,1}` on every marked triple of `BMOClass n 1`, for a
generic point `η` of `V(I)` off the boundary at which `I` is the component's ideal (the three
hypotheses of `cp1For_concat`, kept verbatim). The run `bmoOneRun` of the loop is the instance
`n = T.dim` (`dimFreeBMO_seq`). The predicates are proved along the tower in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step1`, `EmbeddedCP1Step2` and `EmbeddedCP1Tower`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData Hironaka.BMO Hironaka.Stage

namespace Hironaka.Resolution

variable (k : Type u) [Field k] [CharZero k]

/-- **The stage predicate of CP1 for `BO_{n,1}`**: CP1 holds along the run of the stage-`n` order
reduction on every triple of `BOClass n 1`, for a generic point `η` of `V(I)` off the boundary at
which `I` is the component's ideal — the analogue for CP1 of `ClaimBOAt`. -/
def CP1BOAt (n : ℕ) : Prop :=
  ∀ (T : Triple k) (hT : T.BOClass n 1) (η : T.X.left), η ∈ T.I.support.genericPoints →
    (∀ i, η ∉ (T.E.component i).support) →
    T.I.stalkIdeal η = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η →
    CP1For (boRun k n T hT) T.I T.E η

/-- **The stage predicate of CP1 for `BMO_{n,1}`**: CP1 along the run of the stage-`n` marked order
reduction on every marked triple of `BMOClass n 1` — the analogue for CP1 of `ClaimBMOAt`. -/
def CP1BMOAt (n : ℕ) : Prop :=
  ∀ (T : MarkedTriple k) (hT : T.BMOClass n 1) (η : T.X.left), η ∈ T.I.support.genericPoints →
    (∀ i, η ∉ (T.E.component i).support) →
    T.I.stalkIdeal η = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η →
    CP1For (bmoRun k n T hT) T.I T.E η

end Hironaka.Resolution
