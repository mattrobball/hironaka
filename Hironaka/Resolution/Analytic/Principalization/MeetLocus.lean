/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Snc.Sing
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The `m`-fold meet loci of a family of hypersurfaces

Kollár's preliminary blow-ups make the components `E_1, …, E_k` of the boundary disjoint by
blowing up, in turn, "the subset where `m` of the `E_i` intersect" for `m = k, k − 1, …, 2`
[Kol07, 72]. This module defines that subset for a family of hypersurfaces —
`HypersurfaceFamily.meetLocus F m`, the points lying on at least `m` distinct members — and proves
its elementary properties: the cases `m = 0, 1, 2` (everything, the support, the multiple locus
`sing` of `Hironaka/Manifold/Snc/Sing.lean`), monotonicity in `m`, and emptiness beyond the
number of nonempty members. That the `m`-fold locus is a closed submanifold of codimension `m`
with which the family has simple normal crossings, where no point lies on `m + 1` members, is
proved in `MeetLocusChart.lean` of this directory; the disjoining sequence itself is assembled in
`Disjoin.lean`.
-/

@[expose] public section

universe u

open Set

namespace Manifold.HypersurfaceFamily

variable {M : Type u} (F : HypersurfaceFamily M)

/-- Kollár's "the subset where `m` of the `E_i` intersect" [Kol07, 72]: the set of points lying on
at least `m` distinct members of the family — witnessed by a finite set of `m` indices all of
whose members pass through the point. For `m = 2` it is the multiple locus `sing`; for `m = 0` it
is everything; beyond the number of nonempty members it is empty. -/
def meetLocus (m : ℕ) : Set M :=
  {x | ∃ s : Finset F.ι, s.card = m ∧ ∀ j ∈ s, x ∈ F.hyp j}

variable {F}

theorem mem_meetLocus {m : ℕ} {x : M} :
    x ∈ F.meetLocus m ↔ ∃ s : Finset F.ι, s.card = m ∧ ∀ j ∈ s, x ∈ F.hyp j :=
  Iff.rfl

/-- A member through a point is nonempty. -/
theorem hyp_ne_empty_of_mem {j : F.ι} {x : M} (hx : x ∈ F.hyp j) : F.hyp j ≠ ∅ :=
  nonempty_iff_ne_empty.mp ⟨x, hx⟩

variable (F)

/-- Every point lies on at least zero members. -/
theorem meetLocus_zero : F.meetLocus 0 = univ := by
  refine eq_univ_of_forall fun x => ⟨∅, Finset.card_empty, ?_⟩
  intro j hj
  exact absurd hj (Finset.notMem_empty j)

/-- The `1`-fold locus is the support of the family. -/
theorem meetLocus_one : F.meetLocus 1 = F.support := by
  ext x
  constructor
  · rintro ⟨s, hs, h⟩
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hs
    exact mem_iUnion.mpr ⟨j, h j (Finset.mem_singleton_self j)⟩
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    refine ⟨{j}, Finset.card_singleton j, fun k hk => ?_⟩
    rw [Finset.mem_singleton] at hk
    rw [hk]
    exact hj

/-- The `2`-fold locus is the multiple locus `sing` (`Hironaka/Manifold/Snc/Sing.lean`). -/
theorem meetLocus_two : F.meetLocus 2 = F.singularLocus := by
  ext x
  constructor
  · rintro ⟨s, hs, h⟩
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hs
    exact ⟨i, j, hij, h i (Finset.mem_insert_self i {j}),
      h j (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨{i, j}, Finset.card_pair hij, fun k hk => ?_⟩
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hi
    · rw [Finset.mem_singleton] at hk
      rw [hk]
      exact hj

/-- Lying on `m'` members implies lying on `m` of them for `m ≤ m'`. -/
theorem meetLocus_antitone : Antitone F.meetLocus := by
  intro m m' hmm' x hx
  obtain ⟨s, hs, h⟩ := hx
  obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq (hs ▸ hmm' : m ≤ s.card)
  exact ⟨t, ht, fun j hj => h j (hts hj)⟩

/-- For `m ≥ 2` the `m`-fold locus lies in the multiple locus. -/
theorem meetLocus_subset_singularLocus {m : ℕ} (hm : 2 ≤ m) : F.meetLocus m ⊆ F.singularLocus := by
  rw [← meetLocus_two]
  exact meetLocus_antitone F hm

/-- If no `m` distinct members pass through any point, the `m`-fold locus is empty. -/
theorem meetLocus_eq_empty_of_forall_card_lt {m : ℕ}
    (h : ∀ (x : M) (s : Finset F.ι), (∀ j ∈ s, x ∈ F.hyp j) → s.card < m) :
    F.meetLocus m = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨s, hs, hsx⟩ := hx
  exact absurd hs (Nat.ne_of_lt (h x s hsx))

/-- With finitely many nonempty members, no point lies on more members than there are nonempty
ones: the `(k + 1)`-fold locus is empty for `k` the number of nonempty members (Kollár's
`E_1, …, E_k`, the finitely many irreducible components of `E` [Kol07, 72]; on an analytic
manifold the boundary has finitely many members over a relatively compact open). -/
theorem meetLocus_eq_empty_of_finite_nonempty [Finite {j // F.hyp j ≠ ∅}] :
    F.meetLocus (Nat.card {j // F.hyp j ≠ ∅} + 1) = ∅ := by
  refine meetLocus_eq_empty_of_forall_card_lt F fun x s hs => ?_
  have hle : s.card ≤ Nat.card {j // F.hyp j ≠ ∅} := by
    have : Fintype {j // F.hyp j ≠ ∅} := Fintype.ofFinite _
    have h1 : Fintype.card {j // j ∈ s} ≤ Fintype.card {j // F.hyp j ≠ ∅} :=
      Fintype.card_le_of_injective
        (fun j : {j // j ∈ s} => (⟨j.1, hyp_ne_empty_of_mem (hs j.1 j.2)⟩ : {j // F.hyp j ≠ ∅}))
        (fun a b hab => Subtype.ext (Subtype.mk.inj hab))
    rw [Fintype.card_coe] at h1
    rw [Nat.card_eq_fintype_card]
    exact h1
  exact Nat.lt_succ_of_le hle

end Manifold.HypersurfaceFamily
