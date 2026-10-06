/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Stage.Dim
public import Hironaka.Resolution.Algebraic.Stage.Tower
import Hironaka.Resolution.Algebraic.Stage.Base
import Hironaka.Resolution.Algebraic.Stage.Coherence
import Hironaka.Resolution.Algebraic.Stage.DimZero
import Hironaka.Scheme.BlowUp.ExceptionalSetSmooth
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Canonicity of the base stage and the dimension bookkeeping

[Kol07, 70] starts the induction on `n = dim X` with the case `dim X = 0`, where `I = 𝒪_X` since `I`
is nonzero on every irreducible component and "everything is resolved without blow-ups". The step
`n → n + 1` is `Hironaka.Stage.tower base`, a tower over an arbitrary base
`base : OrderReductionStage 0`, and `Hironaka.Resolution.Algebraic.Stage.Base` supplies the base
`stage0`, whose functors are the empty sequence `nil`. This module proves that the base is FORCED,
at two levels:

* **Sequence level.** Every stage-`0` package `S` is `nil` on its class: a triple of dimension `≤ 0`
  has `I = 𝒪_X` (`Triple.I_eq_top_of_hasDimLE_zero`), so any smooth blow-up sequence of order
  `m ≥ 1` on it has no centre of order `≥ m` to blow up —
  `OrderSeqAssignment.seq_eq_nil_of_hasDimLE_zero` and its marked form, applied to the functor
  fields of `S.bo m` and `S.bmo m` (`bo_seq_eq_nil`, `bmo_seq_eq_nil`).
* **Structure level.** Two stage-`0` packages are EQUAL (`OrderReductionStage.zero_subsingleton`, a
  `Subsingleton` instance): a `BOData`/`BMOData` is its functor plus propositions, a functor is its
  `seq` plus propositions (`OrderSeqAssignment.ext`, `OrderGeSeqAssignment.ext`), and the two `seq`s
  agree by the sequence-level fact. Hence `tower base = tower stage0` for every base by `congrArg`,
  the form used when a statement about the tower is proved over an arbitrary base. `exists_stage0`
  is the existential form.

The dimension bookkeeping: `Triple.dim` (`Hironaka.Resolution.Algebraic.Stage.Dim`) is a relative
dimension of the structure morphism; on a nonempty scheme it is THE relative dimension
(`SmoothOfRelativeDimension.eq_of_nonempty`), so `HasDim n ↔ dim = n` and `HasDimLE n ↔ dim ≤ n`
(`[Nonempty T.X.left]` is needed: on `X = ∅` every `n` is a relative dimension). The classes at the
canonical stage `dim X` lose their dimension clause (`boClass_dim`, `bmoClass_dim`), and
"`stage (dim X)` is the canonical stage" is the coherence of
`Hironaka.Resolution.Algebraic.Stage.Coherence` at `n' := dim X` (`tower_bo_dim`, `tower_bmo_dim`):
every stage `n ≥ dim X` of the tower takes the same value at `X`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka Scheme BlowUpSequence

namespace AlgebraicGeometry.Scheme.IdealSheafData

end AlgebraicGeometry.Scheme.IdealSheafData

namespace Hironaka.Stage

/-- "Everything is resolved without blow-ups" [Kol07, 70]: EVERY stage-`0` package is `nil` on the
unmarked class — the dimension-`0` lemma at the functor field of `S.bo m` (the class gives `1 ≤ m`
and `HasDimLE 0`). -/
theorem bo_seq_eq_nil (S : OrderReductionStage.{u} 0) (m : ℕ) (k : Type u) [Field k] [CharZero k]
    (T : Triple k) (hT : T.BOClass 0 m) :
    ((S.bo m).functor k).seq T hT = BlowUpSequence.nil T.X.left :=
  OrderSeqAssignment.seq_eq_nil_of_hasDimLE_zero _ T hT hT.2.1 hT.1

/-- EVERY stage-`0` package is `nil` on the marked class — the marked dimension-`0` lemma at the
functor field of `S.bmo m` (the class gives `T.m = m ≥ 1` and `HasDimLE 0`). -/
theorem bmo_seq_eq_nil (S : OrderReductionStage.{u} 0) (m : ℕ) (k : Type u) [Field k] [CharZero k]
    (T : MarkedTriple k) (hT : T.BMOClass 0 m) :
    ((S.bmo m).functor k).seq T hT = BlowUpSequence.nil T.X.left :=
  OrderGeSeqAssignment.seq_eq_nil_of_hasDimLE_zero _ T hT hT.2.1 (by rw [hT.2.2]; exact hT.1)

/-- **The base is unique**: two stage-`0` packages are equal, because their functors take the same
value `nil` on every triple of the class (`bo_seq_eq_nil`, `bmo_seq_eq_nil`) and the remaining
fields are propositions (`BOData.ext`, `BMOData.ext`). Consequently `tower base = tower stage0` for
every base, by `congrArg`. -/
theorem _root_.Hironaka.OrderReductionStage.zero_subsingleton
    (S S' : OrderReductionStage.{u} 0) : S = S' := by
  cases S with
  | mk bo bmo =>
    cases S' with
    | mk bo' bmo' =>
      obtain rfl : bo = bo' := funext fun m => BOData.ext fun k _ _ T hT => by
        rw [OrderSeqAssignment.seq_eq_nil_of_hasDimLE_zero _ T hT hT.2.1 hT.1,
          OrderSeqAssignment.seq_eq_nil_of_hasDimLE_zero _ T hT hT.2.1 hT.1]
      obtain rfl : bmo = bmo' := funext fun m => BMOData.ext fun k _ _ T hT => by
        have hm : 1 ≤ T.m := by rw [hT.2.2]; exact hT.1
        rw [OrderGeSeqAssignment.seq_eq_nil_of_hasDimLE_zero _ T hT hT.2.1 hm,
          OrderGeSeqAssignment.seq_eq_nil_of_hasDimLE_zero _ T hT hT.2.1 hm]
      rfl

/-- The base stage as a `Subsingleton` instance (`tower base = tower stage0` by
`Subsingleton.elim`). -/
instance _root_.Hironaka.OrderReductionStage.instSubsingletonZero :
    Subsingleton (OrderReductionStage.{u} 0) :=
  ⟨OrderReductionStage.zero_subsingleton⟩

/-- The existential form of `stage0`: a stage-`0` package with `nil`-valued functors exists. -/
theorem exists_stage0 :
    ∃ S : OrderReductionStage.{u} 0,
      (∀ (m : ℕ) (k : Type u) [Field k] [CharZero k] (T : Triple k) (hT : T.BOClass 0 m),
        ((S.bo m).functor k).seq T hT = BlowUpSequence.nil T.X.left) ∧
      ∀ (m : ℕ) (k : Type u) [Field k] [CharZero k] (T : MarkedTriple k) (hT : T.BMOClass 0 m),
        ((S.bmo m).functor k).seq T hT = BlowUpSequence.nil T.X.left :=
  ⟨stage0, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

section Dim

variable {k : Type u} [Field k]

/-- On a nonempty scheme the chosen dimension is THE relative dimension: `n` is a relative dimension
of the structure morphism iff `n = dim` (uniqueness of the relative dimension of a smooth morphism
with nonempty source, `SmoothOfRelativeDimension.eq_of_nonempty`). -/
theorem _root_.AlgebraicGeometry.Triple.hasDim_iff_dim_eq (T : Triple k)
    [Nonempty T.X.left] (n : ℕ) : T.HasDim n ↔ T.dim = n := by
  constructor
  · intro h
    exact @SmoothOfRelativeDimension.eq_of_nonempty _ _ (T.X.left ↘ Spec (CommRingCat.of k)) _ _ _
      T.hasDim_dim h
  · rintro rfl
    exact T.hasDim_dim

/-- On a nonempty scheme, "dimension `≤ n`" is `dim ≤ n`. -/
theorem _root_.AlgebraicGeometry.Triple.hasDimLE_iff_dim_le (T : Triple k)
    [Nonempty T.X.left] (n : ℕ) : T.HasDimLE n ↔ T.dim ≤ n := by
  constructor
  · rintro ⟨n', hn', h⟩
    rw [(T.hasDim_iff_dim_eq n').mp h]
    exact hn'
  · intro h
    exact ⟨T.dim, h, T.hasDim_dim⟩

/-- At the canonical stage `dim X` the unmarked class loses its dimension clause:
`BOClass (dim X) m` is `1 ≤ m ∧ max-ord I ≤ m`, the domain of [Kol07, Theorem 68]. -/
theorem _root_.AlgebraicGeometry.Triple.boClass_dim (T : Triple k) (m : ℕ) :
    T.BOClass T.dim m ↔ 1 ≤ m ∧ T.I.maxOrd ≤ (m : ℕ∞) :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, T.hasDimLE_dim, h.2⟩⟩

/-- At the canonical stage `dim X` the marked class loses its dimension clause: `BMOClass (dim X) m`
is `1 ≤ m ∧ T.m = m`, the domain of [Kol07, Theorem 69]. -/
theorem _root_.Hironaka.MarkedTriple.bmoClass_dim (T : MarkedTriple k) (m : ℕ) :
    T.BMOClass T.toTriple.dim m ↔ 1 ≤ m ∧ T.m = m :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, T.toTriple.hasDimLE_dim, h.2⟩⟩

end Dim

section CanonicalStage

variable (base : OrderReductionStage.{u} 0) {k : Type u} [Field k] [CharZero k]

/-- **`stage (dim X)` is the canonical stage** ([Kol07, 70]): every stage `n ≥ dim X` of the tower
takes at `X` the value of stage `dim X` (`tower_bo_coherent` at `n' := dim X`). -/
theorem tower_bo_dim {n m : ℕ} (T : Triple k) (hle : T.dim ≤ n) (hT : T.BOClass n m)
    (hT' : T.BOClass T.dim m) :
    (((tower base n).bo m).functor k).seq T hT =
      (((tower base T.dim).bo m).functor k).seq T hT' :=
  tower_bo_coherent base m hle T hT hT'

/-- The marked form of `tower_bo_dim` (`tower_bmo_coherent` at `n' := dim X`). -/
theorem tower_bmo_dim {n m : ℕ} (T : MarkedTriple k) (hle : T.toTriple.dim ≤ n)
    (hT : T.BMOClass n m) (hT' : T.BMOClass T.toTriple.dim m) :
    (((tower base n).bmo m).functor k).seq T hT =
      (((tower base T.toTriple.dim).bmo m).functor k).seq T hT' :=
  tower_bmo_coherent base m hle T hT hT'

end CanonicalStage

end Hironaka.Stage
