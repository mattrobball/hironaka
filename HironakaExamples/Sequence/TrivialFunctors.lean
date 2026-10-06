/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Scheme.BlowUpSequence.InducedData
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# The trivial blow-up sequence functors

The structures `OrderSeqFunctor` and `OrderGeSeqFunctor` are inhabited: the trivial functor
`(X, I, E) ↦ nil X`, assigning the empty blow-up sequence to every input, is a smooth blow-up
sequence functor of every order `m` on every class of triples, and the trivial marked functor is a
marked one on every class of marked triples. Both commute with every morphism in the sense of
[Kol07, 34.1] (`CommutesWith`, `CommutesWithSmooth`), since the pullback of the empty sequence is
the empty sequence; the `example`s record this.

The functoriality clause of [Kol07, 34.1] itself, and its locality, are proved in
`Hironaka/Scheme/BlowUpSequence/Functoriality.lean`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Hironaka Scheme.BlowUpSequence

namespace Hironaka.Sequence

variable {k : Type u} [Field k]

/-! ### Pullback data and commuting with a morphism -/

section CommutesWith

variable {m : ℕ} {Dom : Triple k → Prop} {Dom' : MarkedTriple k → Prop}

end CommutesWith

/-! ### Smooth surjections -/

section Surjections

variable {m : ℕ} {Dom : Triple k → Prop} {Dom' : MarkedTriple k → Prop}

end Surjections

/-! ### Smooth morphisms, with deletion of the empty blow-ups -/

section Smooth

variable {m : ℕ} {Dom : Triple k → Prop} {Dom' : MarkedTriple k → Prop}

end Smooth

/-! ### Locality of the functoriality clause -/

section Locality

variable {m : ℕ} {Dom : Triple k → Prop} {Dom' : MarkedTriple k → Prop}

end Locality

/-! ### The order predicates along pullback data -/

section Interface

variable [CharZero k]

/-! ### The structures are inhabited: the trivial functor `(X, I, E) ↦ nil X` is a smooth blow-up
sequence functor of every order on every class, and it commutes with every morphism. -/

section Inhabited

variable {m : ℕ} {Dom : Triple k → Prop} {Dom' : MarkedTriple k → Prop}

/-- The trivial functor of order `m`: every input gets the empty sequence. -/
noncomputable def trivialFunctor : OrderSeqAssignment k m Dom where
  seq T _ := nil T.X.left
  isOrderSeq _ _ := by apply isOrderSeq_nil
  noEmptyCenters _ _ i := i.elim0

/-- The trivial marked functor. -/
noncomputable def trivialGeFunctor : OrderGeSeqAssignment k Dom' where
  seq T _ := nil T.X.left
  isOrderGeSeq _ _ := by apply isOrderGeSeq_nil
  noEmptyCenters _ _ i := i.elim0

example (T T' : Triple k) (h : T'.X.left ⟶ T.X.left) :
    (trivialFunctor (m := m) (Dom := Dom)).CommutesWith h :=
  fun _ _ => rfl

example : (trivialFunctor (k := k) (m := m) (Dom := Dom)).CommutesWithSmooth :=
  ⟨fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

example (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) :
    (trivialGeFunctor (Dom' := Dom')).CommutesWith h :=
  fun _ _ => rfl

end Inhabited

end Interface

end Hironaka.Sequence

