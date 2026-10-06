/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import HironakaExamples.Sequence.Remark33Model
import Hironaka.Resolution.Algebraic.Kol07.Warning63
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Warning 63 on the model of Remark 33

On `𝔸³_k` with the origin `p = V(x, y, z)` and the `z`-axis `C = V(x, y)`, Kollár compares the
marked transforms of `(I_C, 1)` along the two sequences of [Kol07, Remark 33]: `Π` (blow up `p`,
then the strict transform of `C`) and `Σ` (blow up `C`, then `D = σ_0^{-1}(p)`), and finds
`Π_*^{-1}(I_C, 1) ≠ Σ_*^{-1}(I_C, 1)` although `Π = Σ` [Kol07, Warning 63]. With the marked
transform defined as the colon ideal `π_*^{-1}(J, m) = (π^* J : F^m)`, the computation along `Σ`
is immediate: `σ_0^* I_C` is the exceptional divisor `E_0'` itself, so
`(σ_0)_*^{-1}(I_C, 1) = (E_0' : E_0') = 𝒪`, and the transform of `(𝒪, 1)` under any blow-up is
`(𝒪 : F) = 𝒪`. Kollár's printed value `𝒪(E_0' + 2E_1') · Σ^* I_C = 𝒪(E_1')` is a fractional
ideal: Definition 60 is applied with `ord_D 𝒪 = 0 < 1`, outside its domain `m ≤ ord_Z I`, which is
exactly why `Σ` is not a sequence of order `≥ 1` for `(𝔸³, I_C, 1, ∅)` while `Π` is
(`not_isOrderGeSeq_seqCurvePoint` in `HironakaExamples/Sequence/Remark33Warning63.lean`). The two
processes with the same end result are told apart by the marked ideals they induce.

The model sequences are defined in `HironakaExamples/Sequence/Remark33Model.lean`.

The two general facts used, `markedTransform_self` and `markedTransform_top`, are in the
library module `Hironaka/Resolution/Algebraic/Kol07/Warning63.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData Scheme.BlowUpSequence
  Hironaka.Sequence.Remark33 AlgebraicGeometry.Scheme.IdealSheafData

namespace Hironaka.Sequence

section Model

variable (k : Type u) [Field k]

/-- The first step of `Σ`: `(σ_0)_*^{-1}(I_C, 1) = 𝒪`, since `σ_0^* I_C = E_0'`
[Kol07, Warning 63]. -/
theorem markedTransformSeq_seqCurvePoint_one :
    (seqCurvePoint k).markedTransformSeq (curve k) 1
        ⟨1, Nat.lt_succ_of_lt (Nat.lt_of_lt_of_eq one_lt_two (length_seqCurvePoint k).symm)⟩ =
      ⊤ := by
  change (curve k).markedTransform (curve k) 1 = ⊤
  exact markedTransform_self _

/-- The end of `Σ`: `Σ_*^{-1}(I_C, 1) = 𝒪`, the transform of `(𝒪, 1)` [Kol07, Warning 63]. -/
theorem markedTransformSeq_seqCurvePoint :
    (seqCurvePoint k).markedTransformSeq (curve k) 1 (Fin.last 2) = ⊤ := by
  change ((curve k).markedTransform (curve k) 1).markedTransform _ 1 = ⊤
  rw [markedTransform_self, markedTransform_top]

end Model

end Hironaka.Sequence
