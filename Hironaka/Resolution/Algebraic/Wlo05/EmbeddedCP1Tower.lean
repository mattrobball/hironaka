/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1At
import Hironaka.Resolution.Algebraic.Stage.DimZero
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step1
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step2
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP1 at every stage of the tower and along `bmoOneRun`

The induction of [Kol07, 70] for the statement CP1 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`): in dimension `0` the ideal of a
triple is the unit ideal (`Triple.I_eq_top_of_hasDimLE_zero`), so `V(I)` has no generic point and
CP1 holds vacuously (`cp1BMOAt_zero`); `CP1BMOAt n` gives `CP1BOAt (n + 1)` (the Step 2 descent,
`cp1BOAt_succ_of_cp1BMOAt` of `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step2`) and `CP1BOAt
(n + 1)` gives `CP1BMOAt (n + 1)` (the Step 1 reduction, `cp1BMOAt_succ_of_cp1BOAt` of
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step1`), so CP1 holds at every stage (`cp1BMOAt`).
The run `bmoOneRun` of the loop `BED` (`Hironaka.Resolution.Algebraic.Wlo05.Embedded`) is the marked
family of the tower at the triple's own dimension (`dimFreeBMO_seq`, by `rfl`), so CP1 holds along
it for every generic point of `V(I)` off the boundary at which `I` is reduced
(`cp1For_bmoOneRun_of_cp1BMOAt`), by the argument of `claimKC_of_claimBMOAt`
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimAt`). Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Main` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Absorbed`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData Hironaka.Stage

namespace Hironaka.Resolution

variable (k : Type u) [Field k] [CharZero k]

/-- The base of the tower ([Kol07, 70]): in dimension `0` the ideal is the unit ideal, so `V(I)`
has no generic point and CP1 holds vacuously. -/
theorem cp1BMOAt_zero : CP1BMOAt k 0 := by
  intro T hT η hη _ _
  exfalso
  have hI := Triple.I_eq_top_of_hasDimLE_zero T.toTriple hT.2.1
  have hmem := hη.1
  rw [hI, Scheme.IdealSheafData.support_top, ← SetLike.mem_coe, Closeds.coe_bot] at hmem
  exact hmem

/-- CP1 at every stage of the tower ([Kol07, 70]): the Step 2 descent, then the Step 1
reduction. -/
theorem cp1BMOAt (n : ℕ) : CP1BMOAt k n := by
  induction n with
  | zero => exact cp1BMOAt_zero k
  | succ n ih => exact cp1BMOAt_succ_of_cp1BOAt n (cp1BOAt_succ_of_cp1BMOAt k n ih)

variable {k}

/-- CP1 along `bmoOneRun` for every generic point of `V(I)` off the boundary at which `I` is the
reduced ideal of its closure: `bmoOneRun` is the marked family of the tower at the triple's own
dimension (`dimFreeBMO_seq`). -/
theorem cp1For_bmoOneRun_of_cp1BMOAt (h : ∀ n, CP1BMOAt k n) (T : MarkedTriple k) (hm : T.m = 1)
    {η : T.X.left} (hη : η ∈ T.I.support.genericPoints) (hηE : ∀ i, η ∉ (T.E.component i).support)
    (hIc : T.I.stalkIdeal η = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        {η})).stalkIdeal η) :
    CP1For (bmoOneRun T hm) T.I T.E η :=
  h T.toTriple.dim T (MarkedTriple.bmoClass_of_bmoClassFree ⟨le_rfl, hm⟩) η hη hηE hIc

end Hironaka.Resolution
