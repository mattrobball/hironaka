/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

import Mathlib.Algebra.Order.Module.Field
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Sheaves.Init
import Hironaka.Resolution.Algebraic.Tuning.Assemble  -- shake: keep (used only by `example`s)

/-!
# Kollár's Theorem 100 at `s = 1`: the tautological instances

[Kol07, Theorem 100] (tuning of ideals) says that for `m = max-ord I`, an integer `s ≥ 1` and an
ideal sheaf `J` with `I^s ⊆ J ⊆ W_{ms}(I)`, a smooth blow-up sequence is of order `≥ m` for
`(I, m)` exactly when it is of order `≥ ms` for `(J, ms)`; the library proves it as
`Hironaka.Sequence.tuning_iff`. This file checks the two instances with `s = 1`: `J = I` gives the
tautology `(I, m) ↔ (I, m)`, and `J = W_m(I)` gives "order `≥ m` for `(I, m)` iff order `≥ m` for
`(W_m(I), m)`". The hypothesis `I ⊆ J ⊆ W_m(I)` holds in both cases because `I ⊆ W_m(I)`
(`pow_le_W` at the exponent `1`), and the marks are `m · 1 = m`. Everything is checked as
`example`s; nothing is exported.
-/

-- The module consists of `example`s only, so it declares nothing public.
set_option linter.privateModule false

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Examples.Theorem100

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (S : BlowUpSequence X) (I : X.IdealSheafData)
  (E : DivisorFamily X) (m : ℕ)

include n

/-- `s = 1`, `J = I`: Theorem 100 is the tautology `(I, m) ↔ (I, m)`. -/
example (hI : I.maxOrd = m) : S.IsOrderGeSeq f I m E ↔ S.IsOrderGeSeq f I (m * 1) E :=
  Hironaka.Sequence.tuning_iff f n S I I E m 1 hI le_rfl (pow_one I).le
    ((pow_one I).symm.le.trans (IdealSheafData.pow_le_W f le_rfl))

/-- `s = 1`, `J = W_m(I)`: order `≥ m` for `(I, m)` iff order `≥ m` for `(W_m(I), m)`. -/
example (hI : I.maxOrd = m) : S.IsOrderGeSeq f I m E ↔ S.IsOrderGeSeq f
    (IdealSheafData.W f I m m) m E := by
  have h := Hironaka.Sequence.tuning_iff_W f n S I E m 1 hI le_rfl
  rwa [mul_one] at h

/-- The lower bound at `s = 1` is the tautology in `tuning_iff_pow`'s form. -/
example (hI : I.maxOrd = m) : S.IsOrderGeSeq f I m E ↔ S.IsOrderGeSeq f (I ^ 1) (m * 1) E :=
  Hironaka.Sequence.tuning_iff_pow f n S I E m 1 hI le_rfl

end Hironaka.Examples.Theorem100
