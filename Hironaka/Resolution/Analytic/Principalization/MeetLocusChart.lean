/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Principalization.MeetLocus
import Hironaka.Manifold.Submanifold.Charts
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The `m`-fold meet locus as a closed submanifold

Kollár's disjoining blows up "the subset where `m` of the `E_i` intersect" at a stage where no
point lies on `m + 1` of them, and this subset is smooth since the `E_i` "do not have any
`(m+1)`-fold intersections" [Kol07, 72]. Under that hypothesis the `m`-fold meet locus is a closed
submanifold of codimension `m` with which the family has simple normal crossings: at a point `a`
of the locus exactly `m` members pass, and the snc chart of the family at `a`, shrunk to a
neighbourhood where every member through a nearby point already passes through `a` (local
finiteness), exhibits the locus as the coordinate subspace of the `m` coordinates of those
members. This module proves that chart statement (`IsSnc.exists_adaptedChart_meetLocus`) and its
two consequences (`IsSnc.isClosedSubmanifold_meetLocus`, `IsSnc.hasSncWith_meetLocus`) — the
centre of each disjoining blow-up is a closed submanifold having simple normal crossings with the
boundary, as the order-reduction algorithm requires of its centres [Kol07, Definition 66 (3)].
-/

public section

universe u

open Set
open scoped Manifold ContDiff

namespace Manifold.HypersurfaceFamily

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  {F : HypersurfaceFamily M}

/-- Near a point `a`, every member through a nearby point passes through `a`: local finiteness of
the family (the members missing `a` that meet a neighbourhood are finitely many, and their
complements cut the neighbourhood down). The strengthening of `IsSnc.exists_nhds_support_eq` the
meet loci need. -/
theorem IsSnc.exists_nhds_forall_mem_imp (hF : F.IsSnc ψ) (a : M) :
    ∃ V : Set M, IsOpen V ∧ a ∈ V ∧ ∀ x ∈ V, ∀ j, x ∈ F.hyp j → a ∈ F.hyp j := by
  classical
  obtain ⟨U, hU, hfin⟩ := hF.2.1 a
  refine ⟨interior U ∩ ⋂ j ∈ hfin.toFinset.filter (fun j => a ∉ F.hyp j), (F.hyp j)ᶜ,
    isOpen_interior.inter (isOpen_biInter_finset fun j _ => (hF.1 j).isClosed.isOpen_compl),
    ⟨mem_interior_iff_mem_nhds.mpr hU, Set.mem_iInter₂.mpr fun j hj => (Finset.mem_filter.mp hj).2⟩,
    fun x hx j hxj => ?_⟩
  by_contra haj
  have hjT : j ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨x, hxj, interior_subset hx.1⟩
  exact Set.mem_iInter₂.mp hx.2 j (Finset.mem_filter.mpr ⟨hjT, haj⟩) hxj

/-- The `m`-fold meet locus of an snc family is closed: near a point off it, a point on `m` members
would put the point itself on those `m` members. -/
theorem IsSnc.isClosed_meetLocus (hF : F.IsSnc ψ) (m : ℕ) : IsClosed (F.meetLocus m) := by
  rw [← isOpen_compl_iff]
  refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
  obtain ⟨V, hVo, hxV, hV⟩ := hF.exists_nhds_forall_mem_imp x
  refine ⟨V, fun y hy hym => hx ?_, hVo, hxV⟩
  obtain ⟨s, hs, hys⟩ := hym
  exact ⟨s, hs, fun j hj => hV y hy j (hys j hj)⟩

omit [TopologicalSpace M] in
/-- Where no point lies on `m + 1` members, the members through a point of the `m`-fold locus are
exactly the `m` witnesses: any further member through the point would make `m + 1`. -/
theorem mem_of_mem_hyp_of_meetLocus_succ_eq_empty {m : ℕ} (hm : F.meetLocus (m + 1) = ∅) {a : M}
    {s : Finset F.ι} (hs : s.card = m) (has : ∀ j ∈ s, a ∈ F.hyp j) {j : F.ι}
    (haj : a ∈ F.hyp j) : j ∈ s := by
  classical
  by_contra hj
  have hmem : a ∈ F.meetLocus (m + 1) := by
    refine ⟨insert j s, by rw [Finset.card_insert_of_notMem hj, hs], fun k hk => ?_⟩
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact haj
    · exact has k hk
  rw [hm] at hmem
  exact hmem

/-- The restriction of an snc chart at `a` to an open set containing `a` is an snc chart at `a`,
for any charted space (`IsSncChartAt.restrOpen` is stated for a bundled analytic manifold; the
proof is the same — the maximal atlas is closed under restriction to opens). -/
theorem IsSncChartAt.restrOpen_of_isOpen {φ : OpenPartialHomeomorph M E} {a : M}
    {c : {j // a ∈ F.hyp j} → Fin n} (hc : F.IsSncChartAt ψ φ a c) {s : Set M} (hs : IsOpen s)
    (has : a ∈ s) : F.IsSncChartAt ψ (φ.restrOpen s hs) a c := by
  refine ⟨?_, ?_, fun j x hx => ?_, hc.injective⟩
  · rw [OpenPartialHomeomorph.restrOpen_eq_restr]
    exact restr_mem_maximalAtlas _ hc.mem_maximalAtlas hs
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hc.mem_source, has⟩
  · rw [OpenPartialHomeomorph.restrOpen_source] at hx
    exact hc.mem_iff j hx.1

/-- Kollár's "`Z_t` is the subset where `k − t` of the `E_i` intersect", a smooth subvariety
[Kol07, 72]: where no point lies on `m + 1` members, at every point `a` of the `m`-fold meet locus
there is a chart, an snc chart of the family at `a`, adapted to the locus with the `m` coordinates
of the members through `a` as its block — the locus is, near `a`, the intersection of the `m`
coordinate hyperplanes. The block's index set is exactly the set of coordinate indices of the
members through `a`. -/
theorem IsSnc.exists_adaptedChart_meetLocus (hF : F.IsSnc ψ) {m : ℕ} (hm : F.meetLocus (m + 1) = ∅)
    {a : M} (ha : a ∈ F.meetLocus m) :
    ∃ (φ : OpenPartialHomeomorph M E) (σ : Fin m ↪ Fin n) (cidx : {j // a ∈ F.hyp j} → Fin n),
      IsAdaptedChart ψ (F.meetLocus m) φ σ ∧ F.IsSncChartAt ψ φ a cidx ∧
        Set.range σ = Set.range cidx := by
  classical
  obtain ⟨s, hs, has⟩ := ha
  obtain ⟨φ₀, cidx, hφ₀⟩ := hF.2.2 a
  obtain ⟨V, hVo, haV, hV⟩ := hF.exists_nhds_forall_mem_imp a
  have hφ := hφ₀.restrOpen_of_isOpen hVo haV
  -- the coordinate indices of the members through `a`
  set idx : Finset (Fin n) := s.attach.image (fun j => cidx ⟨j.1, has j.1 j.2⟩) with hidx
  have hidxmem : ∀ k, k ∈ idx ↔ ∃ j, ∃ hj : j ∈ s, cidx ⟨j, has j hj⟩ = k := by
    intro k
    rw [hidx, Finset.mem_image]
    constructor
    · rintro ⟨j, -, rfl⟩
      exact ⟨j.1, j.2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, Finset.mem_attach _ _, rfl⟩
  have hidxcard : idx.card = m := by
    rw [hidx, Finset.card_image_of_injective _ ?_, Finset.card_attach, hs]
    intro j j' hjj'
    have h1 := hφ.injective hjj'
    exact Subtype.ext (Subtype.mk.inj h1)
  have hσmem : ∀ i, idx.orderEmbOfFin hidxcard i ∈ idx := fun i =>
    Finset.orderEmbOfFin_mem idx hidxcard i
  -- every member through a point of the chart passes through `a`, hence lies in `s`
  have hmem : ∀ x ∈ (φ₀.restrOpen V hVo).source, ∀ j, x ∈ F.hyp j → j ∈ s := by
    intro x hx j hxj
    have hxV : x ∈ V := by
      rw [OpenPartialHomeomorph.restrOpen_source] at hx
      exact hx.2
    exact mem_of_mem_hyp_of_meetLocus_succ_eq_empty hm hs has (hV x hxV j hxj)
  refine ⟨φ₀.restrOpen V hVo, (idx.orderEmbOfFin hidxcard).toEmbedding, cidx,
    ⟨hφ.mem_maximalAtlas, fun x hx => ?_⟩, hφ, ?_⟩
  · have hcoord : ∀ j (hj : j ∈ s),
        x ∈ F.hyp j ↔ ψ ((φ₀.restrOpen V hVo) x) (cidx ⟨j, has j hj⟩) = 0 :=
      fun j hj => hφ.mem_iff ⟨j, has j hj⟩ hx
    constructor
    · rintro ⟨t, ht, hxt⟩ i
      have hts : t ⊆ s := fun j hj => hmem x hx j (hxt j hj)
      have hteq : t = s := Finset.eq_of_subset_of_card_le hts (by rw [ht, hs])
      obtain ⟨j, hj, hjk⟩ := (hidxmem _).mp (hσmem i)
      change ψ ((φ₀.restrOpen V hVo) x) (idx.orderEmbOfFin hidxcard i) = 0
      rw [← hjk]
      exact (hcoord j hj).mp (hxt j (hteq ▸ hj))
    · intro hall
      refine ⟨s, hs, fun j hj => (hcoord j hj).mpr ?_⟩
      have hk : cidx ⟨j, has j hj⟩ ∈ idx := (hidxmem _).mpr ⟨j, hj, rfl⟩
      have hk' : cidx ⟨j, has j hj⟩ ∈ Set.range (idx.orderEmbOfFin hidxcard) := by
        rw [Finset.range_orderEmbOfFin]
        exact hk
      obtain ⟨i, hi⟩ := hk'
      rw [← hi]
      exact hall i
  · ext k
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj, hjk⟩ := (hidxmem _).mp (hσmem i)
      exact ⟨⟨j, has j hj⟩, hjk⟩
    · rintro ⟨⟨j, haj⟩, rfl⟩
      have hj : j ∈ s := mem_of_mem_hyp_of_meetLocus_succ_eq_empty hm hs has haj
      have hk : cidx ⟨j, haj⟩ ∈ idx := (hidxmem _).mpr ⟨j, hj, rfl⟩
      have hk' : cidx ⟨j, haj⟩ ∈ Set.range (idx.orderEmbOfFin hidxcard) := by
        rw [Finset.range_orderEmbOfFin]
        exact hk
      obtain ⟨i, hi⟩ := hk'
      exact ⟨i, hi⟩

/-- Where no point lies on `m + 1` members, the `m`-fold meet locus is a closed submanifold of
codimension `m` (possibly empty) [Kol07, 72]. -/
theorem IsSnc.isClosedSubmanifold_meetLocus (hF : F.IsSnc ψ) {m : ℕ}
    (hm : F.meetLocus (m + 1) = ∅) : IsClosedSubmanifold ψ (F.meetLocus m) m where
  isClosed := hF.isClosed_meetLocus m
  exists_adaptedChart := fun a ha => by
    obtain ⟨φ, σ, cidx, hφ, hc, -⟩ := hF.exists_adaptedChart_meetLocus hm ha
    exact ⟨φ, σ, hc.mem_source, hφ⟩

/-- Where no point lies on `m + 1` members, the family has simple normal crossings with its
`m`-fold meet locus — the condition on the centre of each disjoining blow-up ([Kol07, 72]; the
hypothesis on the centres in [Kol07, Definition 66 (3)]). -/
theorem IsSnc.hasSncWith_meetLocus (hF : F.IsSnc ψ) {m : ℕ} (hm : F.meetLocus (m + 1) = ∅) :
    F.HasSncWith ψ (F.meetLocus m) m := fun a ha => by
  obtain ⟨φ, σ, cidx, hφ, hc, -⟩ := hF.exists_adaptedChart_meetLocus hm ha
  exact ⟨φ, σ, cidx, hφ, hc⟩

end Manifold.HypersurfaceFamily
