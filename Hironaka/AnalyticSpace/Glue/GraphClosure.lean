/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Order.BourbakiWitt
public import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Closing the graph of a transition map

Three point-set lemmas behind the Hausdorffness of the space glued from local complexifications
[BW59, Proposition 1]. For a continuous map `φ` on an open subset `Ω ⊆ Y` into `Y'` write
`graphOn φ S ⊆ Y × Y'` for its graph over `S ⊆ Ω`.

1. `exists_isOpen_graphOn_closure_disjoint`: given `G ⊆ graphOn φ Ω` and a closed `E ⊆ Y × Y'` with
   `closure G` disjoint from `E`, there is an open `S` with `fst '' G ⊆ S ⊆ Ω` such that
   `closure (graphOn φ S)` is still disjoint from `E`. (For the gluing: `G` is the graph of the
   transition over the real overlap, `E` the pairs of real points outside the two domains.)
2. `closure_graphOn_inter_subset`, `isClosed_closure_diff_graphOn`: over an open `S`, the closure of
   the graph meets `S × Y'` only in the graph, so the boundary `closure Γ ∖ Γ` is a closed set, the
   set the pieces must avoid; `closure_graphOn_inter_prod_subset` is the version for a homeomorphism
   between open subsets whose graph closes away from the pairs outside both domains.
3. `isClosed_image_prodMap_of_eq`: for closed embeddings `f : A → Y`, `g : B → Y'` and continuous
   `a : A → X`, `b : B → X` into a Hausdorff `X`, the set `{(f u, g v) | a u = b v}` is closed in
   `Y × Y'` (the "real diagonal" of two complexifications is closed because `X` is Hausdorff).

Conventions. `Y`, `Y'` are metrizable (analytic spaces are regular and second countable), and the
metric of Mathlib's `metrizableSpaceMetric` on the product is used only inside the proof of (1):
`S := {y ∈ Ω | infDist (y, φ y) G < infDist (y, φ y) E}`; the cases `G = ∅` (take `S = ∅`) and
`E = ∅` (take `S = Ω`) are separate. For `Ω = ∅` every graph is empty; for `E = ∅` there is no
shrinking; for `S = Ω`, (2) says that the graph of a continuous map on an open set into a Hausdorff
space is closed in `Ω × Y'`. Not in the sources.
-/

@[expose] public section

open Topology Set

namespace AnalyticSpace.Glue

universe u v

variable {Y : Type u} {Y' : Type v}

/-- The graph of `φ : Ω → Y'` over the subset `S` of the base. -/
def graphOn {Ω : Set Y} (φ : Ω → Y') (S : Set Y) : Set (Y × Y') :=
  {p | ∃ y : Ω, (y : Y) ∈ S ∧ p = ((y : Y), φ y)}

theorem graphOn_mono {Ω : Set Y} (φ : Ω → Y') {S T : Set Y} (h : S ⊆ T) :
    graphOn φ S ⊆ graphOn φ T := by
  rintro p ⟨y, hy, rfl⟩
  exact ⟨y, h hy, rfl⟩

theorem fst_mem_of_mem_graphOn {Ω : Set Y} {φ : Ω → Y'} {S : Set Y} {p : Y × Y'}
    (hp : p ∈ graphOn φ S) : p.1 ∈ S := by
  obtain ⟨y, hy, rfl⟩ := hp
  exact hy

/-- The graph of `φ` over `Ω` is the transpose of the graph of its inverse `ψ` over `Ω'`. -/
theorem graphOn_eq_preimage_swap {Ω : Set Y} {φ : Ω → Y'} {Ω' : Set Y'} {ψ : Ω' → Y}
    (hφΩ : ∀ y : Ω, φ y ∈ Ω') (hψφ : ∀ y : Ω, ψ ⟨φ y, hφΩ y⟩ = y)
    (hψΩ : ∀ y' : Ω', ψ y' ∈ Ω) (hφψ : ∀ y' : Ω', φ ⟨ψ y', hψΩ y'⟩ = y') :
    graphOn φ Ω = Prod.swap ⁻¹' graphOn ψ Ω' := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨y, -, h⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨⟨φ y, hφΩ y⟩, hφΩ y, Prod.ext rfl (hψφ y).symm⟩
  · rintro ⟨y', -, h⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨⟨ψ y', hψΩ y'⟩, hψΩ y', Prod.ext rfl (hφψ y').symm⟩

variable [TopologicalSpace Y] [TopologicalSpace Y']

/-! ### (1) Shrinking the domain so that the closure of the graph avoids a closed set -/

/-- Shrinking the domain of a continuous partial map so that the closure of its graph avoids a
closed set `E`, keeping a given subgraph `G` whose closure already avoids `E`. -/
theorem exists_isOpen_graphOn_closure_disjoint [TopologicalSpace.MetrizableSpace Y]
    [TopologicalSpace.MetrizableSpace Y']
    {Ω : Set Y} (hΩ : IsOpen Ω) {φ : Ω → Y'} (hφ : Continuous φ) {G E : Set (Y × Y')}
    (hG : G ⊆ graphOn φ Ω) (hE : IsClosed E) (hGE : Disjoint (closure G) E) :
    ∃ S : Set Y, IsOpen S ∧ S ⊆ Ω ∧ Prod.fst '' G ⊆ S ∧ Disjoint (closure (graphOn φ S)) E := by
  rcases G.eq_empty_or_nonempty with hGe | hGne
  · refine ⟨∅, isOpen_empty, empty_subset _, by simp [hGe], ?_⟩
    have : graphOn φ (∅ : Set Y) = ∅ := by
      ext p
      simp [graphOn]
    simp [this]
  rcases E.eq_empty_or_nonempty with hEe | hEne
  · refine ⟨Ω, hΩ, le_rfl, ?_, by simp [hEe]⟩
    rintro _ ⟨p, hp, rfl⟩
    exact fst_mem_of_mem_graphOn (hG hp)
  let _ : MetricSpace (Y × Y') := TopologicalSpace.metrizableSpaceMetric (Y × Y')
  -- the continuous map `y ↦ (y, φ y)` on `Ω`
  let Φ : Ω → Y × Y' := fun y => ((y : Y), φ y)
  have hΦ : Continuous Φ := continuous_subtype_val.prodMk hφ
  let T : Set (Y × Y') := {p | Metric.infDist p G < Metric.infDist p E}
  have hT : IsOpen T := isOpen_lt (Metric.continuous_infDist_pt G) (Metric.continuous_infDist_pt E)
  refine ⟨Subtype.val '' (Φ ⁻¹' T), ?_, ?_, ?_, ?_⟩
  · exact hΩ.isOpenMap_subtype_val _ (hT.preimage hΦ)
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨y, -, rfl⟩ := hG hp
    refine ⟨y, ?_, rfl⟩
    change Metric.infDist ((y : Y), φ y) G < Metric.infDist ((y : Y), φ y) E
    rw [Metric.infDist_zero_of_mem hp]
    exact (Metric.infDist_pos_iff_notMem_closure hEne).mp
      (fun h => hGE.notMem_of_mem_left (subset_closure hp) (hE.closure_eq ▸ h))
  · rw [Set.disjoint_left]
    intro p hp hpE
    have hsub : graphOn φ (Subtype.val '' (Φ ⁻¹' T)) ⊆
        {q : Y × Y' | Metric.infDist q G ≤ Metric.infDist q E} := by
      rintro _ ⟨y, ⟨y', hy', hyy'⟩, rfl⟩
      have : y' = y := Subtype.ext hyy'
      subst this
      have hlt : Metric.infDist (Φ y') G < Metric.infDist (Φ y') E := hy'
      exact le_of_lt hlt
    have hcl : p ∈ {q : Y × Y' | Metric.infDist q G ≤ Metric.infDist q E} :=
      closure_minimal hsub
        (isClosed_le (Metric.continuous_infDist_pt G) (Metric.continuous_infDist_pt E)) hp
    have h0 : Metric.infDist p G = 0 :=
      le_antisymm (by simpa [Metric.infDist_zero_of_mem hpE] using hcl) Metric.infDist_nonneg
    exact hGE.notMem_of_mem_left ((Metric.mem_closure_iff_infDist_zero hGne).mpr h0) hpE

/-! ### (2) The boundary of the graph over an open set is closed -/

/-- Over an open `S`, the closure of the graph meets `S × Y'` only in the graph. -/
theorem closure_graphOn_inter_subset [T2Space Y'] {Ω : Set Y} {φ : Ω → Y'} (hφ : Continuous φ)
    {S : Set Y} (hS : IsOpen S) (hSΩ : S ⊆ Ω) :
    closure (graphOn φ S) ∩ S ×ˢ (univ : Set Y') ⊆ graphOn φ S := by
  -- the graph is the image of a closed set under the open embedding `S × Y' → Y × Y'`
  let ψ : S → Y' := fun y => φ ⟨y.1, hSΩ y.2⟩
  have hψ : Continuous ψ := hφ.comp (Continuous.subtype_mk continuous_subtype_val _)
  let e : S × Y' → Y × Y' := Prod.map Subtype.val id
  have he : IsOpenEmbedding e := hS.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id
  have hgraph : IsClosed {q : S × Y' | ψ q.1 = q.2} :=
    isClosed_eq (hψ.comp continuous_fst) continuous_snd
  have himage : graphOn φ S = e '' {q : S × Y' | ψ q.1 = q.2} := by
    ext p
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(⟨y.1, hy⟩, φ y), rfl, rfl⟩
    · rintro ⟨⟨y, y'⟩, hq, rfl⟩
      exact ⟨⟨y.1, hSΩ y.2⟩, y.2, Prod.ext rfl hq.symm⟩
  rintro p ⟨hp, hpS, -⟩
  obtain ⟨q, rfl⟩ : p ∈ range e := ⟨(⟨p.1, hpS⟩, p.2), rfl⟩
  have hq : q ∈ closure {q : S × Y' | ψ q.1 = q.2} := by
    rw [he.isInducing.closure_eq_preimage_closure_image, ← himage]
    exact hp
  rw [hgraph.closure_eq] at hq
  rw [himage]
  exact ⟨q, hq, rfl⟩

/-- The boundary `closure Γ ∖ Γ` of the graph over an open set is closed. -/
theorem isClosed_closure_diff_graphOn [T2Space Y'] {Ω : Set Y} {φ : Ω → Y'} (hφ : Continuous φ)
    {S : Set Y} (hS : IsOpen S) (hSΩ : S ⊆ Ω) :
    IsClosed (closure (graphOn φ S) \ graphOn φ S) := by
  have : closure (graphOn φ S) \ graphOn φ S = closure (graphOn φ S) ∩ Sᶜ ×ˢ (univ : Set Y') := by
    ext p
    constructor
    · rintro ⟨hp, hpG⟩
      refine ⟨hp, fun hpS => hpG ?_, trivial⟩
      exact closure_graphOn_inter_subset hφ hS hSΩ ⟨hp, hpS, trivial⟩
    · rintro ⟨hp, hpS, -⟩
      exact ⟨hp, fun hpG => hpS (fst_mem_of_mem_graphOn hpG)⟩
  rw [this]
  exact isClosed_closure.inter (hS.isClosed_compl.prod isClosed_univ)

/-! ### (1′) With an inverse: the closure of the graph meets `R × R'` only in the graph -/

/-- If `φ : Ω → Y'` is a homeomorphism onto the open `Ω'` with inverse `ψ`, and the closure of its
graph avoids the pairs of `R × R'` outside both domains, then the closure of the graph meets
`R × R'` only in the graph: a limit `(a, b)` with `a ∈ Ω` lies on the graph by continuity of `φ`,
one with `b ∈ Ω'` by continuity of `ψ`, and the remaining pairs are excluded. -/
theorem closure_graphOn_inter_prod_subset [T2Space Y] [T2Space Y'] {Ω : Set Y} (hΩ : IsOpen Ω)
    {φ : Ω → Y'} (hφ : Continuous φ) {Ω' : Set Y'} (hΩ' : IsOpen Ω') {ψ : Ω' → Y}
    (hψ : Continuous ψ) (hφΩ : ∀ y : Ω, φ y ∈ Ω') (hψφ : ∀ y : Ω, ψ ⟨φ y, hφΩ y⟩ = y)
    (hψΩ : ∀ y' : Ω', ψ y' ∈ Ω) (hφψ : ∀ y' : Ω', φ ⟨ψ y', hψΩ y'⟩ = y') {R : Set Y}
    {R' : Set Y'} (hE : Disjoint (closure (graphOn φ Ω)) ((R \ Ω) ×ˢ (R' \ Ω'))) :
    closure (graphOn φ Ω) ∩ R ×ˢ R' ⊆ graphOn φ Ω := by
  rintro ⟨a, b⟩ ⟨hp, ha, hb⟩
  by_cases haΩ : a ∈ Ω
  · exact closure_graphOn_inter_subset hφ hΩ le_rfl ⟨hp, haΩ, trivial⟩
  by_cases hbΩ : b ∈ Ω'
  · have hswap := graphOn_eq_preimage_swap hφΩ hψφ hψΩ hφψ
    have hcl : closure (Prod.swap ⁻¹' graphOn ψ Ω') = Prod.swap ⁻¹' closure (graphOn ψ Ω') :=
      ((Homeomorph.prodComm Y Y').preimage_closure _).symm
    have hp' : (b, a) ∈ closure (graphOn ψ Ω') := by
      rw [hswap, hcl] at hp
      exact hp
    rw [hswap]
    exact closure_graphOn_inter_subset hψ hΩ' le_rfl ⟨hp', hbΩ, trivial⟩
  · exact absurd ⟨⟨ha, haΩ⟩, ⟨hb, hbΩ⟩⟩ (hE.notMem_of_mem_left hp)

/-! ### (3) The real diagonal is closed -/

/-- For closed embeddings `f`, `g` and continuous maps `a`, `b` into a Hausdorff space, the set
of pairs `(f u, g v)` with `a u = b v` is closed. -/
theorem isClosed_image_prodMap_of_eq {X : Type*} {A : Type*} {B : Type*} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace A] [TopologicalSpace B] {f : A → Y} {g : B → Y'}
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) {a : A → X} {b : B → X}
    (ha : Continuous a) (hb : Continuous b) :
    IsClosed {p : Y × Y' | ∃ u v, a u = b v ∧ p = (f u, g v)} := by
  have h : {p : Y × Y' | ∃ u v, a u = b v ∧ p = (f u, g v)} =
      Prod.map f g '' {q : A × B | a q.1 = b q.2} := by
    ext p
    constructor
    · rintro ⟨u, v, huv, rfl⟩
      exact ⟨(u, v), huv, rfl⟩
    · rintro ⟨⟨u, v⟩, huv, rfl⟩
      exact ⟨u, v, huv, rfl⟩
  rw [h]
  exact (hf.prodMap hg).isClosedMap _
    (isClosed_eq (ha.comp continuous_fst) (hb.comp continuous_snd))

end AnalyticSpace.Glue
