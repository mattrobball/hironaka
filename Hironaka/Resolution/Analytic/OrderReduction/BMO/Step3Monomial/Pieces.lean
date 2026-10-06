/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.State
public import Hironaka.Manifold.Snc.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Labelled piece families on an analytic manifold

Step 3 of the proof of [Kol07, Theorem 107] (item 111) lowers the order of a monomial ideal
`M(𝓘) = ∏_j 𝓘_{E^j}^{a_j}` below `m` by blowing up intersections of members `E^j` of the boundary in
an order prescribed by the exponents `a_j` and the order of the index set: at level `r` one takes
the lexicographically smallest `r`-tuple `j₁ < ⋯ < j_r` of members with nonempty intersection and
maximal exponent sum `≥ m`, blows up the intersection, appends the exceptional divisor as the last
member with exponent `a_{j₁} + ⋯ + a_{j_r} − m`, and repeats. The bookkeeping of that procedure is
purely combinatorial: which sets of members meet (the **nerve**), their labels and exponents. It is
carried out on the combinatorial state `Hironaka.Monomial.MonomialState` (a shared module of this
library, where the procedure `MonomialState.step3`, its termination and its postconditions are
proved). This file provides the geometric data on an analytic manifold that such a state records.

A `PieceFamily N` consists of finitely many **pieces**, closed subsets of `N` indexed by
`c < nextComp` (the empty set standing for a piece no longer present), each with a **label**
`< nextLabel` (the position of its boundary member in the order of the members) and an **exponent**.
Its nerve is the set of nonempty sets of pieces with a common point; its state is the corresponding
`MonomialState`, with every data field definitionally the family's. A piece family **realises** a
boundary family `F` through an order embedding `e` of its labels into the members of `F` when each
embedded member is the union of the pieces with its label, the members off the range of `e` are
empty (on a relatively compact open set only finitely many members meet the closure), and pieces
with the same label are pairwise disjoint: the pieces are then the connected components of the
members, which is how the monomial part of this library is indexed (`BMO/MonomialPart.lean`). The
**centre** of a set `S` of faces is the union of their loci; for Kollár's choice at level `r` this
is the whole intersection `E^{j₁} ∩ ⋯ ∩ E^{j_r}` of the chosen members, with all its connected
components, as in [Kol07, 111, Step 3].
-/

@[expose] public section

open Set Topology Hironaka.Monomial
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A **labelled piece family** on the analytic manifold `N`: pieces indexed by `c < nextComp`
(closed sets, the empty set for a piece no longer present), each with a label `< nextLabel` (the
position of its boundary member in the order of the members) and an exponent `a c`. The geometric
data behind a combinatorial state `Hironaka.Monomial.MonomialState` of the monomial procedure of
[Kol07, 111, Step 3]. -/
structure PieceFamily (N : AnalyticManifold.{u} 𝕜 E) where
  /-- The number of components allocated so far. -/
  nextComp : ℕ
  /-- The number of labels (members) allocated so far. -/
  nextLabel : ℕ
  /-- The underlying closed set of a component (`∅` for a dead component). -/
  piece : ℕ → Set N
  /-- The label (member) of a component. -/
  label : ℕ → ℕ
  /-- The exponent of a component. -/
  a : ℕ → ℕ
  /-- Live components carry live labels. -/
  label_lt : ∀ c, c < nextComp → label c < nextLabel
  /-- Every piece is closed. -/
  isClosed_piece : ∀ c, IsClosed (piece c)

/-- The common cardinality of the faces of a centre, its codimension: the maximum of the
cardinalities (for a centre of the state all faces have the same label tuple, hence the same
cardinality). -/
def faceCard (S : Finset (Finset ℕ)) : ℕ := S.sup Finset.card

namespace PieceFamily

variable {N : AnalyticManifold.{u} 𝕜 E} (Φ : PieceFamily N)

/-! ### Faces and their loci -/

/-- The locus of a face `T`: the intersection of its pieces (the whole manifold for `T = ∅`). -/
def faceSet (T : Finset ℕ) : Set N := ⋂ c ∈ T, Φ.piece c

theorem mem_faceSet {T : Finset ℕ} {x : N} : x ∈ Φ.faceSet T ↔ ∀ c ∈ T, x ∈ Φ.piece c := by
  simp [faceSet]

@[simp] theorem faceSet_empty : Φ.faceSet ∅ = univ := by
  simp [faceSet]

theorem faceSet_anti {T T' : Finset ℕ} (h : T ⊆ T') : Φ.faceSet T' ⊆ Φ.faceSet T := by
  intro x hx
  rw [mem_faceSet] at hx ⊢
  exact fun c hc => hx c (h hc)

theorem isClosed_faceSet (T : Finset ℕ) : IsClosed (Φ.faceSet T) :=
  isClosed_biInter fun c _ => Φ.isClosed_piece c

theorem faceSet_subset_piece {T : Finset ℕ} {c : ℕ} (hc : c ∈ T) : Φ.faceSet T ⊆ Φ.piece c :=
  fun _ hx => (Φ.mem_faceSet.mp hx) c hc

/-- The exponent sum of a face. -/
def total (T : Finset ℕ) : ℕ := ∑ c ∈ T, Φ.a c

/-- The labels of a set of pieces. -/
def labels (T : Finset ℕ) : Finset ℕ := T.image Φ.label

/-! ### The nerve and the state -/

/-- The **nerve** of the family: the nonempty sets of pieces with a common point. -/
noncomputable def nerve : Finset (Finset ℕ) :=
  haveI := Classical.decPred fun T : Finset ℕ => T.Nonempty ∧ (Φ.faceSet T).Nonempty
  (Finset.range Φ.nextComp).powerset.filter fun T => T.Nonempty ∧ (Φ.faceSet T).Nonempty

/-- A set of indices is a face if and only if it consists of indices of pieces, is nonempty, and its
pieces have a common point. -/
theorem mem_nerve_iff (T : Finset ℕ) :
    T ∈ Φ.nerve ↔ T ⊆ Finset.range Φ.nextComp ∧ T.Nonempty ∧ ∃ x, ∀ c ∈ T, x ∈ Φ.piece c := by
  simp only [nerve, Finset.mem_filter, Finset.mem_powerset]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  simp only [Set.Nonempty, mem_faceSet]

theorem nonempty_of_mem_nerve {T : Finset ℕ} (hT : T ∈ Φ.nerve) : T.Nonempty :=
  ((Φ.mem_nerve_iff T).mp hT).2.1

theorem lt_nextComp_of_mem_nerve {T : Finset ℕ} (hT : T ∈ Φ.nerve) {c : ℕ} (hc : c ∈ T) :
    c < Φ.nextComp :=
  Finset.mem_range.mp (((Φ.mem_nerve_iff T).mp hT).1 hc)

theorem faceSet_nonempty_of_mem_nerve {T : Finset ℕ} (hT : T ∈ Φ.nerve) :
    (Φ.faceSet T).Nonempty := by
  obtain ⟨x, hx⟩ := ((Φ.mem_nerve_iff T).mp hT).2.2
  exact ⟨x, Φ.mem_faceSet.mpr hx⟩

/-- The nerve is closed under nonempty subsets: the locus of a face is contained in the locus of
each of its subsets. -/
theorem mem_nerve_of_subset {T T' : Finset ℕ} (hT : T ∈ Φ.nerve) (hT' : T' ⊆ T)
    (hne : T'.Nonempty) : T' ∈ Φ.nerve := by
  rw [mem_nerve_iff] at hT ⊢
  obtain ⟨hsub, -, x, hx⟩ := hT
  exact ⟨hT'.trans hsub, hne, x, fun c hc => hx c (hT' hc)⟩

/-- The invariants of a combinatorial state (`Hironaka.Monomial.MonomialState.Valid`) on the
family's data: `m ≥ 1`, faces nonempty and consisting of pieces, labels below `nextLabel`, the nerve
closed under nonempty subsets, faces of cardinality at most `n`, and pairwise distinct labels on a
face. -/
abbrev IsValid (n m : ℕ) : Prop :=
  MonomialState.Valid n m Φ.nextComp Φ.nextLabel Φ.label Φ.nerve

/-- The combinatorial state of the family: the state of `Hironaka.Monomial.MonomialState` with the
family's number of pieces and labels, labels, exponents and nerve, each field definitionally the
family's. -/
noncomputable def toState (n m : ℕ) (hV : Φ.IsValid n m) : MonomialState :=
  MonomialState.ofValid n m Φ.nextComp Φ.nextLabel Φ.label Φ.a Φ.nerve hV

variable {n m : ℕ} (hV : Φ.IsValid n m)

@[simp] theorem toState_n : (Φ.toState n m hV).n = n := rfl
@[simp] theorem toState_m : (Φ.toState n m hV).m = m := rfl
@[simp] theorem toState_nextComp : (Φ.toState n m hV).nextComp = Φ.nextComp := rfl
@[simp] theorem toState_nextLabel : (Φ.toState n m hV).nextLabel = Φ.nextLabel := rfl
@[simp] theorem toState_label : (Φ.toState n m hV).label = Φ.label := rfl
@[simp] theorem toState_a : (Φ.toState n m hV).a = Φ.a := rfl
@[simp] theorem toState_nerve : (Φ.toState n m hV).nerve = Φ.nerve := rfl

theorem toState_total (T : Finset ℕ) : (Φ.toState n m hV).total T = Φ.total T := rfl

theorem toState_labels (T : Finset ℕ) : (Φ.toState n m hV).labels T = Φ.labels T := rfl

/-- The index allocated to the new piece created from the face `P` of a centre `S`: the pieces so
far, plus the rank of `P` in `S` (`Hironaka.Monomial.MonomialState.rank`). -/
noncomputable def newComp (S : Finset (Finset ℕ)) (P : Finset ℕ) : ℕ :=
  Φ.nextComp + MonomialState.rank S P

theorem toState_newComp (S : Finset (Finset ℕ)) (P : Finset ℕ) :
    (Φ.toState n m hV).newComp S P = Φ.newComp S P := rfl

/-! ### The face through a point -/

/-- The face through a point: the pieces containing it. -/
noncomputable def faceAt (x : N) : Finset ℕ :=
  haveI := Classical.decPred fun c : ℕ => x ∈ Φ.piece c
  (Finset.range Φ.nextComp).filter fun c => x ∈ Φ.piece c

theorem mem_faceAt {x : N} {c : ℕ} : c ∈ Φ.faceAt x ↔ c < Φ.nextComp ∧ x ∈ Φ.piece c := by
  simp [faceAt, Finset.mem_filter, Finset.mem_range]

theorem faceAt_subset_range (x : N) : Φ.faceAt x ⊆ Finset.range Φ.nextComp := fun _ hc =>
  Finset.mem_range.mpr (Φ.mem_faceAt.mp hc).1

theorem mem_faceSet_faceAt (x : N) : x ∈ Φ.faceSet (Φ.faceAt x) :=
  Φ.mem_faceSet.mpr fun _ hc => (Φ.mem_faceAt.mp hc).2

/-- The face through a point lying on some piece is a face of the nerve. -/
theorem faceAt_mem_nerve {x : N} (hx : (Φ.faceAt x).Nonempty) : Φ.faceAt x ∈ Φ.nerve :=
  (Φ.mem_nerve_iff _).mpr ⟨Φ.faceAt_subset_range x, hx, x, fun _ hc => (Φ.mem_faceAt.mp hc).2⟩

/-- A face whose locus contains `x` is contained in the face through `x`. -/
theorem subset_faceAt_of_mem_faceSet {T : Finset ℕ} (hT : T ⊆ Finset.range Φ.nextComp) {x : N}
    (hx : x ∈ Φ.faceSet T) : T ⊆ Φ.faceAt x := fun c hc =>
  Φ.mem_faceAt.mpr ⟨Finset.mem_range.mp (hT hc), Φ.mem_faceSet.mp hx c hc⟩

/-! ### The centre of a set of faces -/

/-- The **centre** of a set `S` of faces: the union of their loci. For Kollár's choice at level `r`,
`S` consists of all the faces with the lexicographically smallest label tuple `j₁ < ⋯ < j_r` of
maximal exponent sum, so the centre is the whole intersection `E^{j₁} ∩ ⋯ ∩ E^{j_r}`, with all its
connected components, as in [Kol07, 111, Step 3]. -/
def centerOf (S : Finset (Finset ℕ)) : Set N := ⋃ P ∈ S, Φ.faceSet P

theorem mem_centerOf {S : Finset (Finset ℕ)} {x : N} :
    x ∈ Φ.centerOf S ↔ ∃ P ∈ S, x ∈ Φ.faceSet P := by
  simp [centerOf]

@[simp] theorem centerOf_empty : Φ.centerOf ∅ = ∅ := by
  simp [centerOf]

theorem faceSet_subset_centerOf {S : Finset (Finset ℕ)} {P : Finset ℕ} (hP : P ∈ S) :
    Φ.faceSet P ⊆ Φ.centerOf S := fun _ hx => Φ.mem_centerOf.mpr ⟨P, hP, hx⟩

theorem isClosed_centerOf (S : Finset (Finset ℕ)) : IsClosed (Φ.centerOf S) :=
  isClosed_biUnion_finset fun P _ => Φ.isClosed_faceSet P

/-! ### Realising a hypersurface family -/

/-- The family **realises** the boundary family `F` through the order embedding `e` of its labels
into the members of `F`: each embedded member is the union of the pieces with its label, the members
off the range of `e` are empty, and pieces with the same label are pairwise disjoint. The pieces of
a realising family are the connected components of the members. -/
structure Realizes (F : Manifold.HypersurfaceFamily N) (e : Fin Φ.nextLabel ↪o F.ι) : Prop where
  /-- An embedded member is the union of the pieces of its label. -/
  hyp_eq : ∀ ℓ : Fin Φ.nextLabel,
    F.hyp (e ℓ) = ⋃ c ∈ (Finset.range Φ.nextComp).filter (fun c => Φ.label c = ℓ.1), Φ.piece c
  /-- The members off the range of `e` are empty. -/
  hyp_eq_empty : ∀ j, j ∉ Set.range e → F.hyp j = ∅
  /-- Pieces of one label are pairwise disjoint. -/
  disjoint : ∀ c c', c < Φ.nextComp → c' < Φ.nextComp → c ≠ c' → Φ.label c = Φ.label c' →
    Disjoint (Φ.piece c) (Φ.piece c')

namespace Realizes

variable {Φ} {F : Manifold.HypersurfaceFamily N} {e : Fin Φ.nextLabel ↪o F.ι} (hΦ : Φ.Realizes F e)
include hΦ

/-- A point lies on the member with label `ℓ` if and only if it lies on a piece with that label. -/
theorem mem_hyp_iff (ℓ : Fin Φ.nextLabel) (x : N) :
    x ∈ F.hyp (e ℓ) ↔ ∃ c, c < Φ.nextComp ∧ Φ.label c = ℓ.1 ∧ x ∈ Φ.piece c := by
  rw [hΦ.hyp_eq ℓ]
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_range, exists_prop]
  constructor
  · rintro ⟨c, ⟨hc, hl⟩, hx⟩
    exact ⟨c, hc, hl, hx⟩
  · rintro ⟨c, hc, hl, hx⟩
    exact ⟨c, ⟨hc, hl⟩, hx⟩

/-- A piece lies in the member of its label. -/
theorem piece_subset_hyp {c : ℕ} (hc : c < Φ.nextComp) :
    Φ.piece c ⊆ F.hyp (e ⟨Φ.label c, Φ.label_lt c hc⟩) := fun x hx =>
  (hΦ.mem_hyp_iff _ x).mpr ⟨c, hc, rfl, hx⟩

/-- Through a point passes at most one piece with a given label. -/
theorem eq_of_label_eq_of_mem {c c' : ℕ} (hc : c < Φ.nextComp) (hc' : c' < Φ.nextComp)
    (hl : Φ.label c = Φ.label c') {x : N} (hx : x ∈ Φ.piece c) (hx' : x ∈ Φ.piece c') : c = c' := by
  by_contra hne
  exact Set.disjoint_left.mp (hΦ.disjoint c c' hc hc' hne hl) hx hx'

/-- The labels of the pieces of a face are pairwise distinct: the pieces have a common point. -/
theorem injOn_label_of_mem_nerve {T : Finset ℕ} (hT : T ∈ Φ.nerve) : Set.InjOn Φ.label ↑T := by
  obtain ⟨hsub, -, x, hx⟩ := (Φ.mem_nerve_iff T).mp hT
  intro c hc c' hc' hl
  exact hΦ.eq_of_label_eq_of_mem (Finset.mem_range.mp (hsub hc)) (Finset.mem_range.mp (hsub hc')) hl
    (hx c hc) (hx c' hc')

/-- A face has as many labels as pieces. -/
theorem card_labels_of_mem_nerve {T : Finset ℕ} (hT : T ∈ Φ.nerve) : (Φ.labels T).card = T.card :=
  Finset.card_image_of_injOn (hΦ.injOn_label_of_mem_nerve hT)

end Realizes

end PieceFamily

end Hironaka.Manifold.BMO
