/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Absorbed
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Tower
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP1 at the absorbing stage: the two statements

The two forms of the statement CP1 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) at the absorbing stage of the loop, as
compositions: the local chain form (`chainRelativeAt_of_absorbed`, which is
`chainRelativeAt_of_absorbed_of_cp1For` applied to `cp1For_bmoOneRun_of_cp1BMOAt` and `cp1BMOAt`)
and the disjointness of the strict transforms of the other members from the absorbed one there
(`disjoint_strictTransformSeq_of_absorbed`, which is
`disjoint_strictTransformSeq_of_absorbed_of_chainRelativeAt` at the former). These are the inputs
of the entry into the protected state (CP2, `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP2Entry`),
of the invariant CP5 and of the end identity CP6. The absorbing moment is that of the proof of
[Wlo05, Theorem 4.7.1]; the tower induction behind `cp1BMOAt` is that of [Kol07, 70].
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

open Classical in
/-- **CP1, the local form at the absorbing stage of the loop**: at the first absorbing stage of the
run of `BMO_1` on a state of the loop, the marked transform is in chain form along the strict
transform of the absorbed member at every point of it. -/
theorem chainRelativeAt_of_absorbed (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) (hinv : InvCE T.I T.E C)
    (h : ∃ n, HasAbsorptionAt T hm C n)
    {c : T.X.left.IdealSheafData} (hcC : c ∈ C)
    (hcc : CenterContains (bmoOneRun T hm) c (Nat.find h)) :
    ∀ p ∈ (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)).support,
      ChainRelativeAt (stageTriple T hm (Nat.find h)).E (stageTriple T hm (Nat.find h)).I
        (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)) p :=
  chainRelativeAt_of_absorbed_of_cp1For T hm C hinv h hcC hcc fun _ hη hηE hIc =>
    cp1For_bmoOneRun_of_cp1BMOAt (cp1BMOAt k) T hm hη hηE hIc

open Classical in
/-- **CP1, the disjointness**: no other member's strict transform meets the absorbed one at the
absorbing stage. -/
theorem disjoint_strictTransformSeq_of_absorbed (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) (hinv : InvCE T.I T.E C)
    (h : ∃ n, HasAbsorptionAt T hm C n)
    {c : T.X.left.IdealSheafData} (hcC : c ∈ C)
    (hcc : CenterContains (bmoOneRun T hm) c (Nat.find h))
    {c' : T.X.left.IdealSheafData} (hc'C : c' ∈ C) (hne : c' ≠ c) :
    Disjoint (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c' (Fin.last _)).support
      (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)).support :=
  disjoint_strictTransformSeq_of_absorbed_of_chainRelativeAt T hm C hinv h hcC hcc
    (chainRelativeAt_of_absorbed T hm C hinv h hcC hcc) hc'C hne

end Hironaka.Resolution
