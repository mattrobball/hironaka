/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Principalization.Collapse
import Hironaka.Resolution.Analytic.Principalization.MeetLocusChart
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The meet locus of a subfamily as a centre

At the `t`-th disjoining step of [Kol07, 72] the current divisor is the total transform (the
strict transforms of the components of `E` together with the exceptional divisors introduced so
far), while the centre is the meet locus of the strict transforms alone; the centre must have
simple normal crossings with the whole current divisor [Kol07, Definition 66 (3)]. This module is
the subfamily form of `MeetLocusChart.lean`: for an snc family `G` and a predicate `p` on its
members, where no point lies on `m + 1` of the `p`-members, at every point of the `m`-fold meet
locus of the `p`-members there is a chart adapted to that locus which is an snc chart of the
whole family `G` — so the locus is a closed submanifold of codimension `m` and `G` has snc with it
(`IsSnc.hasSncWith_meetLocus_subfamily`). With `p := fun _ => True` this is the statement of
`MeetLocusChart.lean`. Also: the subfamily of an snc family is snc (`IsSnc.subfamily`). Used for
the centres of the disjoining blow-ups (`DisjoinBoundary.lean`) and of the monomial step of the
order reduction.
-/

public section

universe u

open Set
open scoped Manifold ContDiff

namespace Manifold.HypersurfaceFamily

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  {G : HypersurfaceFamily M} {p : G.ι → Prop}

/-- The subfamily of an snc family is snc. -/
theorem IsSnc.subfamily (hG : G.IsSnc ψ) (p : G.ι → Prop) : (G.subfamily p).IsSnc ψ := by
  refine ⟨fun j => hG.1 j.1, hG.2.1.comp_injective Subtype.val_injective, fun a => ?_⟩
  obtain ⟨φ, c, hφ⟩ := hG.2.2 a
  refine ⟨φ, fun j => c ⟨j.1.1, j.2⟩, hφ.1, hφ.2.1, fun j x hx => ?_,
    fun j j' hjj' => ?_⟩
  · exact hφ.2.2.1 ⟨j.1.1, j.2⟩ x hx
  have h := hφ.2.2.2 hjj'
  exact Subtype.ext (Subtype.ext (Subtype.mk.inj h))

/-- The subfamily form of `IsSnc.exists_adaptedChart_meetLocus` [Kol07, 72]: where no point lies on
`m + 1` of the `p`-members, at every point `a` of their `m`-fold meet locus there is a chart, an
snc chart of the whole family `G` at `a`, adapted to the locus with the `m` coordinates of the
`p`-members through `a` as its block. -/
theorem IsSnc.exists_adaptedChart_meetLocus_subfamily (hG : G.IsSnc ψ) {m : ℕ}
    (hm : (G.subfamily p).meetLocus (m + 1) = ∅) {a : M} (ha : a ∈ (G.subfamily p).meetLocus m) :
    ∃ (φ : OpenPartialHomeomorph M E) (σ : Fin m ↪ Fin n) (cidx : {j // a ∈ G.hyp j} → Fin n),
      IsAdaptedChart ψ ((G.subfamily p).meetLocus m) φ σ ∧ G.IsSncChartAt ψ φ a cidx := by
  classical
  obtain ⟨s, hs, has⟩ := ha
  -- the `p`-members through `a`, as members of `G`
  have has' : ∀ j ∈ s, a ∈ G.hyp j.1 := has
  obtain ⟨φ₀, cidx, hφ₀⟩ := hG.2.2 a
  obtain ⟨V, hVo, haV, hV⟩ := hG.exists_nhds_forall_mem_imp a
  have hφ := hφ₀.restrOpen_of_isOpen hVo haV
  -- the coordinate indices of the `p`-members through `a`
  set idx : Finset (Fin n) := s.attach.image (fun j => cidx ⟨j.1.1, has' j.1 j.2⟩) with hidx
  have hidxmem : ∀ k, k ∈ idx ↔ ∃ j, ∃ hj : j ∈ s, cidx ⟨j.1, has' j hj⟩ = k := by
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
    exact Subtype.ext (Subtype.ext (Subtype.mk.inj h1))
  have hσmem : ∀ i, idx.orderEmbOfFin hidxcard i ∈ idx := fun i =>
    Finset.orderEmbOfFin_mem idx hidxcard i
  -- every `p`-member through a point of the chart passes through `a`, hence lies in `s`
  have hmem : ∀ x ∈ (φ₀.restrOpen V hVo).source, ∀ j : (G.subfamily p).ι,
      x ∈ (G.subfamily p).hyp j → j ∈ s := by
    intro x hx j hxj
    have hxV : x ∈ V := by
      rw [OpenPartialHomeomorph.restrOpen_source] at hx
      exact hx.2
    exact mem_of_mem_hyp_of_meetLocus_succ_eq_empty hm hs has (hV x hxV j.1 hxj)
  refine ⟨φ₀.restrOpen V hVo, (idx.orderEmbOfFin hidxcard).toEmbedding, cidx,
    ⟨hφ.mem_maximalAtlas, fun x hx => ?_⟩, hφ⟩
  have hcoord : ∀ j (hj : j ∈ s),
      x ∈ (G.subfamily p).hyp j ↔ ψ ((φ₀.restrOpen V hVo) x) (cidx ⟨j.1, has' j hj⟩) = 0 :=
    fun j hj => hφ.mem_iff ⟨j.1, has' j hj⟩ hx
  constructor
  · rintro ⟨t, ht, hxt⟩ i
    have hts : t ⊆ s := fun j hj => hmem x hx j (hxt j hj)
    have hteq : t = s := Finset.eq_of_subset_of_card_le hts (hs.trans ht.symm).le
    obtain ⟨j, hj, hjk⟩ := (hidxmem _).mp (hσmem i)
    change ψ ((φ₀.restrOpen V hVo) x) (idx.orderEmbOfFin hidxcard i) = 0
    rw [← hjk]
    exact (hcoord j hj).mp (hxt j (hteq ▸ hj))
  · intro hall
    refine ⟨s, hs, fun j hj => (hcoord j hj).mpr ?_⟩
    have hk : cidx ⟨j.1, has' j hj⟩ ∈ idx := (hidxmem _).mpr ⟨j, hj, rfl⟩
    have hk' : cidx ⟨j.1, has' j hj⟩ ∈ Set.range (idx.orderEmbOfFin hidxcard) := by
      rw [Finset.range_orderEmbOfFin]
      exact hk
    obtain ⟨i, hi⟩ := hk'
    rw [← hi]
    exact hall i

/-- Subfamily form: the `m`-fold meet locus of the `p`-members is a closed submanifold of
codimension `m` where no point lies on `m + 1` of them. -/
theorem IsSnc.isClosedSubmanifold_meetLocus_subfamily (hG : G.IsSnc ψ) {m : ℕ}
    (hm : (G.subfamily p).meetLocus (m + 1) = ∅) :
    IsClosedSubmanifold ψ ((G.subfamily p).meetLocus m) m where
  isClosed := (hG.subfamily p).isClosed_meetLocus m
  exists_adaptedChart := fun a ha => by
    obtain ⟨φ, σ, cidx, hφ, hc⟩ := hG.exists_adaptedChart_meetLocus_subfamily hm ha
    exact ⟨φ, σ, hc.mem_source, hφ⟩

/-- The whole family `G` has simple normal crossings with the `m`-fold meet locus of its
`p`-members where no point lies on `m + 1` of them (the centre condition of
[Kol07, Definition 66 (3)] at a disjoining step of [Kol07, 72]). -/
theorem IsSnc.hasSncWith_meetLocus_subfamily (hG : G.IsSnc ψ) {m : ℕ}
    (hm : (G.subfamily p).meetLocus (m + 1) = ∅) :
    G.HasSncWith ψ ((G.subfamily p).meetLocus m) m := fun a ha => by
  obtain ⟨φ, σ, cidx, hφ, hc⟩ := hG.exists_adaptedChart_meetLocus_subfamily hm ha
  exact ⟨φ, σ, cidx, hφ, hc⟩

end Manifold.HypersurfaceFamily
