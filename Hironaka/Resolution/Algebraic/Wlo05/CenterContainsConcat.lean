/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine
import Hironaka.Resolution.Algebraic.Kol07.Thm36.CentersMiss
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The stop rule along a concatenation

The stop rule `CenterContains S c i` of `Hironaka/Resolution/Algebraic/Kol07/Thm36/Affine.lean` (the
center at stage `i` contains the strict transform of the closed subscheme `V(c)`; it locates the
blow-up whose center has the generic point of the variety in the proof of [Kol07, Corollary 22])
read on a concatenation `S.concat T`: at an index below `S.length` it is the stop rule on `S`; at an
index `S.length + i` it is the stop rule on `T` at `i` for the strict transform of `c` along `S`
(`strictTransformSeq_concat_last` of `Hironaka/Scheme/BlowUpSequence/ConcatTransforms.lean` in the
form the recursion needs). Structural recursion on `S`, as for `centerContains_take_iff`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData BlowUpSequence Hironaka.Resolution

namespace Hironaka.Sequence

/-- The stop rule on a concatenation below the first sequence's length is the stop rule on the
first sequence. -/
theorem centerContains_concat_iff_of_lt :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (T : BlowUpSequence S.last) (c : X.IdealSheafData)
      (i : ℕ), i < S.length → (CenterContains (S.concat T) c i ↔ CenterContains S c i)
  | _, nil _, _, _, _, hi => (Nat.not_lt_zero _ hi).elim
  | _, cons X D rest, T, c, 0, _ => by
    rw [concat_cons]
    exact ⟨fun h => ⟨Nat.succ_pos _, h.2⟩, fun h => ⟨Nat.succ_pos _, h.2⟩⟩
  | _, cons X D rest, T, c, i + 1, hi => by
    rw [concat_cons]
    exact (centerContains_cons_succ_iff D (rest.concat T) c i).trans
      ((centerContains_concat_iff_of_lt rest T (c.strictTransform D) i
        (Nat.lt_of_succ_lt_succ hi)).trans (centerContains_cons_succ_iff D rest c i).symm)

/-- The stop rule on a concatenation at an index `S.length + i` is the stop rule on the second
sequence at `i` for the strict transform along the first. -/
theorem centerContains_concat_add_iff :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (T : BlowUpSequence S.last) (c : X.IdealSheafData)
      (i : ℕ), CenterContains (S.concat T) c (S.length + i) ↔
        CenterContains T (S.strictTransformSeq c (Fin.last _)) i
  | _, nil X, T, c, i => by
    change CenterContains T c (0 + i) ↔ CenterContains T c i
    rw [Nat.zero_add]
  | _, cons X D rest, T, c, i => by
    rw [concat_cons]
    change CenterContains (cons X D (rest.concat T)) c (rest.length + 1 + i) ↔ _
    rw [Nat.add_right_comm, centerContains_cons_succ_iff]
    exact centerContains_concat_add_iff rest T (c.strictTransform D) i

end Hironaka.Sequence
