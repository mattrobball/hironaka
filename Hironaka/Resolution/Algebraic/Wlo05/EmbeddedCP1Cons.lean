/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1For
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP1 across a first blow-up that does not contain the component

The `cons` case of `cp1For_concat` (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1For`): when the
first blow-up of `cons X D R` does not contain `c̃`, CP1 for the sequence follows from CP1 for its
tail `R` at the lifted generic point, with the transforms of the data along the first blow-up —
`cons X D R` is the concatenation of the single blow-up `cons X D nil` with `R` (the blow-up
sequences of [Kol07, Definition 29]), and CP1 holds vacuously along the single blow-up. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step22Core`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData
  BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.Resolution

variable {X : Scheme.{u}}

/-- `cp1For_concat` for the single blow-up `cons X D nil` followed by `R`, which is `cons X D R`:
when the first blow-up does not contain `c̃`, CP1 for the sequence follows from CP1 for its tail at
the lifted generic point (the generic lift along the single blow-up), with the transforms along the
first blow-up. -/
theorem cp1For_cons_of_not_centerContains [IsLocallyNoetherian X] (D : X.IdealSheafData)
    (R : BlowUpSequence D.blowUp) (I : X.IdealSheafData) (E : DivisorFamily X) {η : X}
    (hη : η ∈ I.support.genericPoints) (hηE : ∀ j, η ∉ (E.component j).support)
    (hIc : I.stalkIdeal η = (vanishingIdeal (Closeds.closure {η})).stalkIdeal η)
    (hD : ¬ CenterContains (BlowUpSequence.cons X D R) (vanishingIdeal (Closeds.closure {η})) 0)
    (hR : ∀ η' : D.blowUp,
      GenericLift (BlowUpSequence.cons X D (BlowUpSequence.nil _)) I E 1 η (Fin.last _) η' →
      CP1For R (I.markedTransform D 1) (E.totalTransform D) η') :
    CP1For (BlowUpSequence.cons X D R) I E η := by
  -- CP1 holds vacuously along the single blow-up: its only centre does not contain `c̃`
  have hS : CP1For (BlowUpSequence.cons X D (BlowUpSequence.nil _)) I E η := by
    rintro ⟨i, hi1⟩ hi -
    exfalso
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi1
    obtain ⟨h0, hle⟩ := hi
    exact hD ⟨Nat.succ_pos _, hle⟩
  exact cp1For_concat (BlowUpSequence.cons X D (BlowUpSequence.nil _)) R I E hη hηE hIc hS hR

end Hironaka.Resolution
