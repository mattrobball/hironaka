/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Principalization.MeetLocus
import Hironaka.Manifold.Submanifold.Charts
import Hironaka.Resolution.Analytic.Principalization.MeetLocusChart
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Collapsing pairwise disjoint members of a divisor into one

Kollár's remark in the construction of the principalization functor [Kol07, 72]: when the
irreducible components of `E` happen to be disjoint one may "declare that `E` is a single divisor",
the components of a divisor being allowed to be reducible in his (68) — after the disjoining
blow-ups, the strict transforms `E^0 := π^{-1}_*(E_1 + ⋯ + E_k)` become one member, placed first,
and the exceptional divisors `E^1 < ⋯ < E^{k-1}` keep their order. This module defines
`HypersurfaceFamily.collapse G p`, the family in which the members satisfying `p` are replaced by
their union as a single first member, and proves it is a simple normal crossings divisor when those
members are pairwise disjoint (no point on two of them, `(G.subfamily p).meetLocus 2 = ∅`): the
union is a closed smooth hypersurface (near each of its points it is the one member through the
point), the family stays locally finite, and the snc chart of `G` at a point serves, the union
taking the coordinate of the one `p`-member through the point. The collapse is applied to the
boundary at the last stage of the disjoining list to form the disjoined triple
(`DisjoinInput.lean`).
-/

@[expose] public section

universe u

open Set
open scoped Manifold ContDiff

namespace Manifold.HypersurfaceFamily

variable {M : Type u}

/-- The subfamily of the members satisfying `p`. -/
def subfamily (G : HypersurfaceFamily M) (p : G.ι → Prop) : HypersurfaceFamily M where
  ι := {j // p j}
  hyp j := G.hyp j.1

/-- The family with the members satisfying `p` collapsed into their union as a single first member
(Kollár's `E^0 = π^{-1}_*(E_1 + ⋯ + E_k)`, [Kol07, 72]), the others keeping their order
(`E^1 < ⋯ < E^{k-1}`). -/
def collapse (G : HypersurfaceFamily M) (p : G.ι → Prop) : HypersurfaceFamily M where
  ι := PUnit.{u + 1} ⊕ₗ {j // ¬ p j}
  countable := inferInstanceAs (Countable (PUnit.{u + 1} ⊕ {j // ¬ p j}))
  hyp k := Sum.elim (fun _ => ⋃ j : {j // p j}, G.hyp j.1) (fun j => G.hyp j.1) (ofLex k)

variable {G : HypersurfaceFamily M} {p : G.ι → Prop}

theorem collapse_hyp_inl (G : HypersurfaceFamily M) (p : G.ι → Prop) :
    (G.collapse p).hyp (toLex (Sum.inl PUnit.unit)) = ⋃ j : {j // p j}, G.hyp j.1 :=
  rfl

theorem collapse_hyp_inr (G : HypersurfaceFamily M) (p : G.ι → Prop) (j : {j // ¬ p j}) :
    (G.collapse p).hyp (toLex (Sum.inr j)) = G.hyp j.1 :=
  rfl

/-- The collapsed member whose index unlexes to `Sum.inl` is the union. -/
theorem collapse_hyp_of_ofLex_eq_inl {k : PUnit.{u + 1} ⊕ₗ {j // ¬ p j}} {u : PUnit.{u + 1}}
    (hk : ofLex k = Sum.inl u) : (G.collapse p).hyp k = ⋃ j : {j // p j}, G.hyp j.1 := by
  change Sum.elim _ _ (ofLex k) = _
  rw [hk]
  rfl

/-- The collapsed member whose index unlexes to `Sum.inr j` is the original member `j`. -/
theorem collapse_hyp_of_ofLex_eq_inr {k : PUnit.{u + 1} ⊕ₗ {j // ¬ p j}} {j : {j // ¬ p j}}
    (hk : ofLex k = Sum.inr j) : (G.collapse p).hyp k = G.hyp j.1 := by
  change Sum.elim _ _ (ofLex k) = _
  rw [hk]
  rfl

/-- The support is unchanged by collapsing. -/
theorem support_collapse (G : HypersurfaceFamily M) (p : G.ι → Prop) :
    (G.collapse p).support = G.support := by
  classical
  ext x
  simp only [support, mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩
    rcases hk' : ofLex k with u | j
    · rw [collapse_hyp_of_ofLex_eq_inl hk'] at hk
      obtain ⟨j, hj⟩ := mem_iUnion.mp hk
      exact ⟨j.1, hj⟩
    · rw [collapse_hyp_of_ofLex_eq_inr hk'] at hk
      exact ⟨j.1, hk⟩
  · rintro ⟨j, hj⟩
    by_cases hpj : p j
    · exact ⟨toLex (Sum.inl PUnit.unit), mem_iUnion.mpr ⟨⟨j, hpj⟩, hj⟩⟩
    · exact ⟨toLex (Sum.inr ⟨j, hpj⟩), hj⟩

/-- Where no point lies on two members satisfying `p`, a point of their union lies on exactly one of
them: the member through it is unique. -/
theorem eq_of_mem_of_mem_subfamily (hdisj : (G.subfamily p).meetLocus 2 = ∅) {x : M}
    {j j' : (G.subfamily p).ι} (hj : x ∈ (G.subfamily p).hyp j) (hj' : x ∈ (G.subfamily p).hyp j') :
    j = j' := by
  classical
  by_contra hne
  have hx : x ∈ (G.subfamily p).meetLocus 2 := by
    refine ⟨({j, j'} : Finset (G.subfamily p).ι), Finset.card_pair hne, fun k hk => ?_⟩
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hj
    · rw [Finset.mem_singleton] at hk
      rw [hk]
      exact hj'
  rw [hdisj] at hx
  exact hx

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} [TopologicalSpace M] [ChartedSpace E M]

/-- Near a point `a` of the union of the `p`-members, when they are pairwise disjoint, the union
coincides with the one member through `a`. -/
theorem exists_nhds_iUnion_eq_hyp (hG : G.IsSnc ψ) (hdisj : (G.subfamily p).meetLocus 2 = ∅)
    {a : M} (j₀ : {j // p j}) (ha : a ∈ G.hyp j₀.1) :
    ∃ V : Set M, IsOpen V ∧ a ∈ V ∧
      ∀ x ∈ V, x ∈ (⋃ j : {j // p j}, G.hyp j.1) ↔ x ∈ G.hyp j₀.1 := by
  obtain ⟨V, hVo, haV, hV⟩ := hG.exists_nhds_forall_mem_imp a
  refine ⟨V, hVo, haV, fun x hx => ⟨fun hxu => ?_, fun hxj => mem_iUnion.mpr ⟨j₀, hxj⟩⟩⟩
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hxu
  have haj : a ∈ G.hyp j.1 := hV x hx j.1 hxj
  have := eq_of_mem_of_mem_subfamily hdisj haj ha
  rw [← this]
  exact hxj

/-- The union of pairwise disjoint closed smooth hypersurfaces of a locally finite family is a
closed smooth hypersurface. -/
theorem isClosedSubmanifold_iUnion_subfamily (hG : G.IsSnc ψ)
    (hdisj : (G.subfamily p).meetLocus 2 = ∅) :
    IsClosedSubmanifold ψ (⋃ j : {j // p j}, G.hyp j.1) 1 := by
  have hlfp : LocallyFinite fun j : {j // p j} => G.hyp j.1 :=
    hG.2.1.comp_injective Subtype.val_injective
  refine ⟨hlfp.isClosed_iUnion fun j => (hG.1 j.1).isClosed, fun a ha => ?_⟩
  obtain ⟨j₀, hj₀⟩ := mem_iUnion.mp ha
  obtain ⟨V, hVo, haV, hV⟩ := exists_nhds_iUnion_eq_hyp hG hdisj j₀ hj₀
  obtain ⟨φ, σ, haφ, hφ⟩ := (hG.1 j₀.1).exists_adaptedChart a hj₀
  have hφ' := hφ.restrOpen' V hVo
  refine ⟨φ.restrOpen V hVo, σ, ?_, hφ'.1, fun x hx => ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨haφ, haV⟩
  · have hxV : x ∈ V := by
      rw [OpenPartialHomeomorph.restrOpen_source] at hx
      exact hx.2
    exact (hV x hxV).trans (hφ'.2 x hx)

omit [TopologicalSpace M] in
/-- The index bookkeeping of the collapsed snc chart at `a`: every collapsed member through `a`
comes from a member of `G` through `a` — the `¬ p` member itself, or (for the union) the given
`p`-member `j₀` through `a`. -/
theorem exists_mem_of_mem_collapse_hyp {a : M} {j₀ : G.ι} (ha₀ : a ∈ G.hyp j₀)
    {k : PUnit.{u + 1} ⊕ₗ {j // ¬ p j}} (hk : a ∈ (G.collapse p).hyp k) :
    ∃ j : G.ι, a ∈ G.hyp j ∧
      ((∃ u, ofLex k = Sum.inl u) ∧ j = j₀ ∨ ∃ hj : ¬ p j, ofLex k = Sum.inr ⟨j, hj⟩) := by
  rcases hk' : ofLex k with u | j
  · exact ⟨j₀, ha₀, Or.inl ⟨⟨u, rfl⟩, rfl⟩⟩
  · rw [collapse_hyp_of_ofLex_eq_inr hk'] at hk
    exact ⟨j.1, hk, Or.inr ⟨j.2, rfl⟩⟩

omit [TopologicalSpace M] in
/-- The same, at a point `a` off the union: only `¬ p` members pass. -/
theorem exists_mem_of_mem_collapse_hyp_of_notMem {a : M}
    (ha : a ∉ ⋃ j : {j // p j}, G.hyp j.1) {k : PUnit.{u + 1} ⊕ₗ {j // ¬ p j}}
    (hk : a ∈ (G.collapse p).hyp k) :
    ∃ j : G.ι, a ∈ G.hyp j ∧ ∃ hj : ¬ p j, ofLex k = Sum.inr ⟨j, hj⟩ := by
  rcases hk' : ofLex k with u | j
  · rw [collapse_hyp_of_ofLex_eq_inl hk'] at hk
    exact absurd hk ha
  · rw [collapse_hyp_of_ofLex_eq_inr hk'] at hk
    exact ⟨j.1, hk, j.2, rfl⟩

/-- Collapsing pairwise disjoint members into their union keeps the family a simple normal
crossings divisor ([Kol07, 72]): the union is a closed smooth hypersurface (near each of its points
it is the one member through the point), the family stays locally finite, and the snc chart of `G`
at a point serves, the collapsed member taking the index of the one `p`-member through the
point. -/
theorem isSnc_collapse (hG : G.IsSnc ψ) (hdisj : (G.subfamily p).meetLocus 2 = ∅) :
    (G.collapse p).IsSnc ψ := by
  classical
  refine ⟨fun k => ?_, ?_, fun a => ?_⟩
  · -- each member is a closed smooth hypersurface
    rcases hk : ofLex k with u | j
    · rw [collapse_hyp_of_ofLex_eq_inl hk]
      exact isClosedSubmanifold_iUnion_subfamily hG hdisj
    · rw [collapse_hyp_of_ofLex_eq_inr hk]
      exact hG.1 j.1
  · -- locally finite: one extra set beside a subfamily
    change LocallyFinite
      (Sum.elim (fun _ : PUnit.{u + 1} => ⋃ j : {j // p j}, G.hyp j.1)
        (fun j : {j // ¬ p j} => G.hyp j.1) ∘ ⇑ofLex)
    exact ((locallyFinite_of_finite _).sumElim
      (hG.2.1.comp_injective Subtype.val_injective)).comp_injective ofLex.injective
  · -- the snc chart at `a`
    obtain ⟨φ₀, c, hφ₀⟩ := hG.2.2 a
    by_cases ha : a ∈ ⋃ j : {j // p j}, G.hyp j.1
    · -- `a` on the union: the one `p`-member `j₀` through `a` lends its coordinate to the union
      obtain ⟨j₀, hj₀⟩ := mem_iUnion.mp ha
      obtain ⟨V, hVo, haV, hV⟩ := exists_nhds_iUnion_eq_hyp hG hdisj j₀ hj₀
      have hφ := hφ₀.restrOpen_of_isOpen hVo haV
      -- the member of `G` behind each collapsed member through `a`
      let src : {k // a ∈ (G.collapse p).hyp k} → {j // a ∈ G.hyp j} := fun k =>
        ⟨Classical.choose (exists_mem_of_mem_collapse_hyp hj₀ k.2),
          (Classical.choose_spec (exists_mem_of_mem_collapse_hyp hj₀ k.2)).1⟩
      have hsrc : ∀ k : {k // a ∈ (G.collapse p).hyp k},
          ((∃ u, ofLex k.1 = Sum.inl u) ∧ (src k).1 = j₀.1) ∨
            ∃ hj : ¬ p (src k).1, ofLex k.1 = Sum.inr ⟨(src k).1, hj⟩ := fun k =>
        (Classical.choose_spec (exists_mem_of_mem_collapse_hyp hj₀ k.2)).2
      refine ⟨φ₀.restrOpen V hVo, fun k => c (src k), hφ.1, hφ.2.1, fun k x hx => ?_, ?_⟩
      · -- the coordinate description of each collapsed member through `a`
        have hxV : x ∈ V := by
          rw [OpenPartialHomeomorph.restrOpen_source] at hx
          exact hx.2
        rcases hsrc k with ⟨⟨u, hku⟩, hj⟩ | ⟨hj, hkj⟩
        · rw [collapse_hyp_of_ofLex_eq_inl hku, hV x hxV, ← hφ.2.2.1 (src k) x hx, hj]
        · rw [collapse_hyp_of_ofLex_eq_inr hkj]
          exact hφ.2.2.1 (src k) x hx
      · -- injectivity: the source member determines the collapsed member
        intro k k' hkk'
        have h1 : src k = src k' := hφ.2.2.2 hkk'
        have h1' : (src k).1 = (src k').1 := congrArg Subtype.val h1
        rcases hsrc k with ⟨⟨u, hku⟩, hj⟩ | ⟨hj, hkj⟩ <;>
          rcases hsrc k' with ⟨⟨u', hku'⟩, hj'⟩ | ⟨hj', hkj'⟩
        · exact Subtype.ext (ofLex.injective (by rw [hku, hku']))
        · exact absurd (h1' ▸ hj ▸ j₀.2 : p (src k').1) hj'
        · exact absurd (h1' ▸ hj' ▸ j₀.2 : p (src k).1) hj
        · refine Subtype.ext (ofLex.injective ?_)
          rw [hkj, hkj']
          exact congrArg Sum.inr (Subtype.ext h1')
    · -- `a` off the union: only `¬ p` members pass, each its own member of `G`
      let src : {k // a ∈ (G.collapse p).hyp k} → {j // a ∈ G.hyp j} := fun k =>
        ⟨Classical.choose (exists_mem_of_mem_collapse_hyp_of_notMem ha k.2),
          (Classical.choose_spec (exists_mem_of_mem_collapse_hyp_of_notMem ha k.2)).1⟩
      have hsrc : ∀ k : {k // a ∈ (G.collapse p).hyp k},
          ∃ hj : ¬ p (src k).1, ofLex k.1 = Sum.inr ⟨(src k).1, hj⟩ := fun k =>
        (Classical.choose_spec (exists_mem_of_mem_collapse_hyp_of_notMem ha k.2)).2
      refine ⟨φ₀, fun k => c (src k), hφ₀.1, hφ₀.2.1, fun k x hx => ?_, fun k k' hkk' => ?_⟩
      · obtain ⟨hj, hkj⟩ := hsrc k
        rw [collapse_hyp_of_ofLex_eq_inr hkj]
        exact hφ₀.2.2.1 (src k) x hx
      · have h1' : (src k).1 = (src k').1 := congrArg Subtype.val (hφ₀.2.2.2 hkk')
        obtain ⟨hj, hkj⟩ := hsrc k
        obtain ⟨hj', hkj'⟩ := hsrc k'
        refine Subtype.ext (ofLex.injective ?_)
        rw [hkj, hkj']
        exact congrArg Sum.inr (Subtype.ext h1')

end Manifold.HypersurfaceFamily
