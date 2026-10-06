/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Compactness.Compact

/-!
# Shrinking a family of compact cores to open subsets avoiding finitely many closed sets

Point-set topology for the shrinking of the pieces in the gluing of local complexifications [BW59,
Proposition 1]. Given spaces `Y i`, compact cores `K i ⊆ Y i`, a family `S₂` of pairs `(a, b)` with
closed sets `E₂ (a, b) ⊆ Y a × Y b` disjoint from `K a × K b`, and a family `S₃` of triples with
closed sets `E₃ (a, b, c) ⊆ Y a × Y b × Y c` disjoint from `K a × K b × K c`, such that every index
meets only finitely many pairs and triples, there are open subsets `A i ⊇ K i` with `A a × A b`
disjoint from `E₂ (a, b)` and `A a × A b × A c` disjoint from `E₃ (a, b, c)` (`exists_shrink`): the
tube lemma for each constraint (Mathlib's `generalized_tube_lemma`), and finite intersections.

Conventions. The constraint open subsets are indexed so that no transport along an equality of
indices is needed: for the index `i` the pairs `(i, j)` contribute their first open subsets, the
pairs `(j, i)` their second, and likewise the three positions of the triples. With no constraints
`A i = univ`; an empty `K i` may still be constrained by the other cores. Not in the sources.
-/

public section

open Topology Set

namespace AnalyticSpace.Glue

universe u v

/-! ### The tube lemma as disjointness from a closed set -/

theorem exists_isOpen_prod_disjoint {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} {t : Set Y} (hs : IsCompact s) (ht : IsCompact t) {E : Set (X × Y)}
    (hE : IsClosed E) (hd : Disjoint (s ×ˢ t) E) :
    ∃ (u : Set X) (v : Set Y), IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ Disjoint (u ×ˢ v) E := by
  obtain ⟨u, v, hu, hv, hsu, htv, huv⟩ := generalized_tube_lemma hs ht hE.isOpen_compl
    (Set.subset_compl_iff_disjoint_right.mpr hd)
  exact ⟨u, v, hu, hv, hsu, htv, Set.subset_compl_iff_disjoint_right.mp huv⟩

theorem exists_isOpen_prod3_disjoint {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {s : Set X} {t : Set Y} {r : Set Z} (hs : IsCompact s) (ht : IsCompact t)
    (hr : IsCompact r) {E : Set (X × Y × Z)} (hE : IsClosed E) (hd : Disjoint (s ×ˢ t ×ˢ r) E) :
    ∃ (u : Set X) (v : Set Y) (w : Set Z), IsOpen u ∧ IsOpen v ∧ IsOpen w ∧ s ⊆ u ∧ t ⊆ v ∧
      r ⊆ w ∧ Disjoint (u ×ˢ v ×ˢ w) E := by
  obtain ⟨u, m, hu, hm, hsu, htm, hum⟩ := exists_isOpen_prod_disjoint hs (ht.prod hr) hE hd
  obtain ⟨v, w, hv, hw, htv, hrw, hvw⟩ := generalized_tube_lemma ht hr hm htm
  exact ⟨u, v, w, hu, hv, hw, hsu, htv, hrw, hum.mono_left (Set.prod_mono le_rfl hvw)⟩

/-! ### The shrinking -/

variable {ι : Type u} {Y : ι → Type v} [∀ i, TopologicalSpace (Y i)]

/-- **The shrinking.** Open subsets `A i ⊇ K i` avoiding finitely many closed pair and triple
constraints. -/
theorem exists_shrink (K : ∀ i, Set (Y i)) (hK : ∀ i, IsCompact (K i))
    (S₂ : Set (ι × ι)) (E₂ : ∀ p : ι × ι, Set (Y p.1 × Y p.2))
    (hE₂ : ∀ p ∈ S₂, IsClosed (E₂ p)) (hK₂ : ∀ p ∈ S₂, Disjoint (K p.1 ×ˢ K p.2) (E₂ p))
    (hfin₂ : ∀ i, {p ∈ S₂ | p.1 = i ∨ p.2 = i}.Finite)
    (S₃ : Set (ι × ι × ι)) (E₃ : ∀ t : ι × ι × ι, Set (Y t.1 × Y t.2.1 × Y t.2.2))
    (hE₃ : ∀ t ∈ S₃, IsClosed (E₃ t))
    (hK₃ : ∀ t ∈ S₃, Disjoint (K t.1 ×ˢ K t.2.1 ×ˢ K t.2.2) (E₃ t))
    (hfin₃ : ∀ i, {t ∈ S₃ | t.1 = i ∨ t.2.1 = i ∨ t.2.2 = i}.Finite) :
    ∃ A : ∀ i, Set (Y i), (∀ i, IsOpen (A i)) ∧ (∀ i, K i ⊆ A i) ∧
      (∀ p ∈ S₂, Disjoint (A p.1 ×ˢ A p.2) (E₂ p)) ∧
      (∀ t ∈ S₃, Disjoint (A t.1 ×ˢ A t.2.1 ×ˢ A t.2.2) (E₃ t)) := by
  classical
  choose! u v hu hv hKu hKv hduv using fun (p : ι × ι) (hp : p ∈ S₂) =>
    exists_isOpen_prod_disjoint (hK p.1) (hK p.2) (hE₂ p hp) (hK₂ p hp)
  choose! u₃ v₃ w₃ hu₃ hv₃ hw₃ hKu₃ hKv₃ hKw₃ hd₃ using fun (t : ι × ι × ι) (ht : t ∈ S₃) =>
    exists_isOpen_prod3_disjoint (hK t.1) (hK t.2.1) (hK t.2.2) (hE₃ t ht) (hK₃ t ht)
  -- the constraints touching an index, by position
  let L : ι → Set ι := fun i => {j | (i, j) ∈ S₂}
  let R : ι → Set ι := fun i => {j | (j, i) ∈ S₂}
  let T₁ : ι → Set (ι × ι) := fun i => {q | (i, q.1, q.2) ∈ S₃}
  let T₂ : ι → Set (ι × ι) := fun i => {q | (q.1, i, q.2) ∈ S₃}
  let T₃ : ι → Set (ι × ι) := fun i => {q | (q.1, q.2, i) ∈ S₃}
  have hL : ∀ i, (L i).Finite := fun i =>
    (((hfin₂ i).subset (t := {p ∈ S₂ | p.1 = i}) fun p hp => ⟨hp.1, Or.inl hp.2⟩).image
      Prod.snd).subset fun j hj => ⟨(i, j), ⟨hj, rfl⟩, rfl⟩
  have hR : ∀ i, (R i).Finite := fun i =>
    (((hfin₂ i).subset (t := {p ∈ S₂ | p.2 = i}) fun p hp => ⟨hp.1, Or.inr hp.2⟩).image
      Prod.fst).subset fun j hj => ⟨(j, i), ⟨hj, rfl⟩, rfl⟩
  have hT₁ : ∀ i, (T₁ i).Finite := fun i =>
    (((hfin₃ i).subset (t := {t ∈ S₃ | t.1 = i}) fun t ht => ⟨ht.1, Or.inl ht.2⟩).image
      Prod.snd).subset fun q hq => ⟨(i, q.1, q.2), ⟨hq, rfl⟩, rfl⟩
  have hT₂ : ∀ i, (T₂ i).Finite := fun i =>
    (((hfin₃ i).subset (t := {t ∈ S₃ | t.2.1 = i}) fun t ht => ⟨ht.1, Or.inr (Or.inl ht.2)⟩).image
      fun t => (t.1, t.2.2)).subset fun q hq => ⟨(q.1, i, q.2), ⟨hq, rfl⟩, rfl⟩
  have hT₃ : ∀ i, (T₃ i).Finite := fun i =>
    (((hfin₃ i).subset (t := {t ∈ S₃ | t.2.2 = i}) fun t ht => ⟨ht.1, Or.inr (Or.inr ht.2)⟩).image
      fun t => (t.1, t.2.1)).subset fun q hq => ⟨(q.1, q.2, i), ⟨hq, rfl⟩, rfl⟩
  let A : ∀ i, Set (Y i) := fun i =>
    (⋂ j ∈ L i, u (i, j)) ∩ (⋂ j ∈ R i, v (j, i)) ∩ (⋂ q ∈ T₁ i, u₃ (i, q.1, q.2)) ∩
      (⋂ q ∈ T₂ i, v₃ (q.1, i, q.2)) ∩ (⋂ q ∈ T₃ i, w₃ (q.1, q.2, i))
  refine ⟨A, fun i => ?_, fun i => ?_, ?_, ?_⟩
  · exact ((((hL i).isOpen_biInter fun j hj => hu (i, j) hj).inter
      ((hR i).isOpen_biInter fun j hj => hv (j, i) hj)).inter
      ((hT₁ i).isOpen_biInter fun q hq => hu₃ (i, q.1, q.2) hq)).inter
      ((hT₂ i).isOpen_biInter fun q hq => hv₃ (q.1, i, q.2) hq) |>.inter
      ((hT₃ i).isOpen_biInter fun q hq => hw₃ (q.1, q.2, i) hq)
  · refine Set.subset_inter (Set.subset_inter (Set.subset_inter (Set.subset_inter ?_ ?_) ?_) ?_) ?_
    · exact Set.subset_iInter₂ fun j hj => hKu (i, j) hj
    · exact Set.subset_iInter₂ fun j hj => hKv (j, i) hj
    · exact Set.subset_iInter₂ fun q hq => hKu₃ (i, q.1, q.2) hq
    · exact Set.subset_iInter₂ fun q hq => hKv₃ (q.1, i, q.2) hq
    · exact Set.subset_iInter₂ fun q hq => hKw₃ (q.1, q.2, i) hq
  · rintro ⟨a, b⟩ hp
    refine (hduv (a, b) hp).mono_left (Set.prod_mono ?_ ?_)
    · exact fun y hy => Set.mem_iInter₂.mp hy.1.1.1.1 b hp
    · exact fun y hy => Set.mem_iInter₂.mp hy.1.1.1.2 a hp
  · rintro ⟨a, b, c⟩ ht
    refine (hd₃ (a, b, c) ht).mono_left (Set.prod_mono ?_ (Set.prod_mono ?_ ?_))
    · exact fun y hy => Set.mem_iInter₂.mp hy.1.1.2 (b, c) ht
    · exact fun y hy => Set.mem_iInter₂.mp hy.1.2 (a, c) ht
    · exact fun y hy => Set.mem_iInter₂.mp hy.2 (a, b) ht

end AnalyticSpace.Glue
