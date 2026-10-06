/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Transform
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Hironaka.Scheme.BlowUpSequence.Defs  -- shake: keep (used only by `example`s)
import Hironaka.Scheme.BlowUpSequence.InducedData  -- shake: keep (used only by `example`s)
/-!
# The marked transform of the centre and of the unit ideal

Two values of the marked transform `π_*^{-1}(J, m) = (π^* J : F^m)` of [Kol07, Definition 60]:
the transform of the centre itself with mark `1` is the unit ideal, `(F : F) = 𝒪`
(`markedTransform_self`), and the transform of the unit ideal is the unit ideal, `(𝒪 : F^m) = 𝒪`
(`markedTransform_top`). They give the values along `Σ` in Kollár's Warning 63 on the model of
Remark 33 (`HironakaExamples/Sequence/Warning63.lean`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData
  Scheme.BlowUpSequence AlgebraicGeometry.Scheme.IdealSheafData

namespace Hironaka.Sequence

variable {X : Scheme.{u}}

/-- The marked transform of the center itself with mark `1` is the unit ideal: `(F : F) = 𝒪`. -/
theorem markedTransform_self (Z : X.IdealSheafData) : Z.markedTransform Z 1 = ⊤ := by
  change (Z.comap Z.blowUpπ).colon (Z.exceptionalDivisor ^ 1) = ⊤
  rw [pow_one]
  exact le_antisymm le_top ((Scheme.IdealSheafData.le_colon_iff_mul_le _ _ _).mpr (top_mul _).le)

/-- The marked transform of the unit ideal is the unit ideal: `(𝒪 : F^m) = 𝒪`. -/
theorem markedTransform_top (Z : X.IdealSheafData) (m :
    ℕ) : Scheme.IdealSheafData.markedTransform ⊤ Z m = ⊤ := by
  change ((⊤ : X.IdealSheafData).comap Z.blowUpπ).colon
      (Z.exceptionalDivisor ^ m) = ⊤
  rw [comap_top]
  exact le_antisymm le_top (le_colon_self _ _)

end Hironaka.Sequence
