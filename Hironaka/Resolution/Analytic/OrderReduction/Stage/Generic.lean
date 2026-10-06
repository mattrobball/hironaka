/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Tactic.ToDual
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Sheaves.Init

/-!
# The order-reduction tower over arbitrary families of structures

The induction of [Kol07, 70] is a recursion on the dimension whose data are two families of
structures, the order-reduction data `BO n m` and the marked order-reduction data `BMO n m`, and
two reduction steps between them: (70.1) order reduction for marked ideals in dimension `n` gives
order reduction for ideals in dimension `n + 1` ([Kol07, Theorem 103]), and (70.2) order reduction
for ideals in dimension `n` gives order reduction for marked ideals in dimension `n`
([Kol07, Theorem 107]). This module states the recursion once, over arbitrary families
`BO BMO : ℕ → ℕ → Type u`, of which the tower on the compatible-family structures `BOanFam` and
`BMOanFam` (`Stage/Family.lean`) is an instance.

* `StageOf BO BMO n` — a stage: order-reduction data and marked data at every mark;
* `StepBOOf BO BMO`, `StepBMOOf BO BMO` — the two reduction steps as data;
* `succOfBMOOf`, `succOf` — the successor stage;
* `towerOf base h103 h107` — the recursion from a base stage, with its unfolding lemmas
  (`towerOf_zero`, `towerOf_succ`, `towerOf_succ_bo`, `towerOf_succ_bmo`, all by definition) and
  existence statements (`exists_towerOf`, `nonempty_bo_of_tower`, `nonempty_bmo_of_tower`).

Nothing about the structures `BO n m` and `BMO n m` is used: the module only threads them through
the recursion.
-/

@[expose] public section

noncomputable section

universe u

namespace Hironaka.Manifold

/-- A stage of the recursion of [Kol07, 70] over arbitrary families of structures: order-reduction
data and marked data at every mark, in dimension `n`. -/
structure StageOf (BO BMO : ℕ → ℕ → Type u) (n : ℕ) : Type u where
  /-- The order-reduction data at every mark. -/
  bo : ∀ m : ℕ, BO n m
  /-- The marked data at every mark. -/
  bmo : ∀ m : ℕ, BMO n m

/-- The first reduction step of [Kol07, 70] as data: order reduction for ideals in dimension
`n + 1` from order reduction for marked ideals at every mark in dimension `n`
([Kol07, Theorem 103]). -/
structure StepBOOf (BO BMO : ℕ → ℕ → Type u) : Type u where
  /-- Theorem 103 in dimension `n + 1` from Theorem 107 in dimension `n`, at every mark. -/
  bo : ∀ n : ℕ, (∀ s : ℕ, BMO n s) → ∀ m : ℕ, BO (n + 1) m

/-- The second reduction step of [Kol07, 70] as data: order reduction for marked ideals in
dimension `n` from order reduction for ideals at every mark in the same dimension
([Kol07, Theorem 107]). -/
structure StepBMOOf (BO BMO : ℕ → ℕ → Type u) : Type u where
  /-- Theorem 107 from Theorem 103 in the same dimension, at every mark. -/
  bmo : ∀ n : ℕ, (∀ d : ℕ, BO n d) → ∀ m : ℕ, BMO n m

variable {BO BMO : ℕ → ℕ → Type u} (h103 : StepBOOf BO BMO) (h107 : StepBMOOf BO BMO) {n : ℕ}

/-- The stage `n + 1` from the marked data of the stage `n`: the first reduction step applied to the
marked data, then the second applied to the result. -/
def succOfBMOOf (bmo : ∀ s : ℕ, BMO n s) : StageOf BO BMO (n + 1) where
  bo := h103.bo n bmo
  bmo := h107.bmo (n + 1) (h103.bo n bmo)

/-- The successor stage: `succOfBMOOf` at the marked data of the given stage. -/
def succOf (S : StageOf BO BMO n) : StageOf BO BMO (n + 1) :=
  succOfBMOOf h103 h107 S.bmo

theorem succOf_eq_succOfBMOOf (S : StageOf BO BMO n) :
    succOf h103 h107 S = succOfBMOOf h103 h107 S.bmo := rfl

theorem succOf_bo (S : StageOf BO BMO n) : (succOf h103 h107 S).bo = h103.bo n S.bmo := rfl

theorem succOf_bmo (S : StageOf BO BMO n) :
    (succOf h103 h107 S).bmo = h107.bmo (n + 1) (succOf h103 h107 S).bo := rfl

/-- The successor stage depends on the stage below only through its marked data, as in the
hypothesis "assume that (69) holds in dimensions `< n`" of [Kol07, Theorem 103]. -/
theorem succOf_congr (S S' : StageOf BO BMO n) (h : S.bmo = S'.bmo) :
    succOf h103 h107 S = succOf h103 h107 S' :=
  congrArg (succOfBMOOf h103 h107) h

theorem exists_succOf (S : StageOf BO BMO n) :
    ∃ S' : StageOf BO BMO (n + 1), S'.bo = h103.bo n S.bmo ∧ S'.bmo = h107.bmo (n + 1) S'.bo :=
  ⟨succOf h103 h107 S, rfl, rfl⟩

/-- The tower ([Kol07, 70]): the stage in every dimension, by recursion from a base stage along the
two reduction steps. -/
def towerOf (base : StageOf BO BMO 0) (h103 : StepBOOf BO BMO) (h107 : StepBMOOf BO BMO) :
    ∀ n : ℕ, StageOf BO BMO n
  | 0 => base
  | n + 1 => succOf h103 h107 (towerOf base h103 h107 n)

variable (base : StageOf BO BMO 0)

theorem towerOf_zero : towerOf base h103 h107 0 = base := rfl

theorem towerOf_succ (n : ℕ) :
    towerOf base h103 h107 (n + 1) = succOf h103 h107 (towerOf base h103 h107 n) := rfl

theorem towerOf_succ_bo (n m : ℕ) :
    (towerOf base h103 h107 (n + 1)).bo m = h103.bo n (towerOf base h103 h107 n).bmo m := rfl

theorem towerOf_succ_bmo (n m : ℕ) :
    (towerOf base h103 h107 (n + 1)).bmo m =
      h107.bmo (n + 1) (towerOf base h103 h107 (n + 1)).bo m := rfl

/-- The recursion as an existence statement: there is a stage in every dimension, equal to the base
stage at `0` and to the successor of the previous stage at each `n + 1`. -/
theorem exists_towerOf :
    ∃ st : ∀ n : ℕ, StageOf BO BMO n,
      st 0 = base ∧ ∀ n : ℕ, st (n + 1) = succOf h103 h107 (st n) :=
  ⟨towerOf base h103 h107, rfl, fun _ => rfl⟩

include base h103 h107 in
/-- Given a base stage and the two reduction steps, the order-reduction data exist in every
dimension and at every mark. -/
theorem nonempty_bo_of_tower (n m : ℕ) : Nonempty (BO n m) :=
  ⟨(towerOf base h103 h107 n).bo m⟩

include base h103 h107 in
/-- Given a base stage and the two reduction steps, the marked data exist in every dimension and at
every mark. -/
theorem nonempty_bmo_of_tower (n m : ℕ) : Nonempty (BMO n m) :=
  ⟨(towerOf base h103 h107 n).bmo m⟩

end Hironaka.Manifold

end
