/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.DirectLimit.Chain
import Hironaka.Manifold.LocalDiffeomorph
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The direct limit of a chain of open embeddings: the manifold

The direct limit `Limit` of `DirectLimit/Chain.lean` is an analytic manifold, and the inclusions
of the pieces are analytic open embeddings: `limitManifold : AnalyticManifold 𝕜 E` with its
`IsManifold`, `T2Space` and `SecondCountableTopology` instances, Włodarczyk's glued manifold `M̃`
[Wlo09, §4.1] (the increasing union of compact subsets of [Kol07, 44]; [BM97, §13]).

Hausdorff: two points lie in a common piece (`exists_common_toLimit`), separated there, and the
inclusion is an open map. Second countable: the pieces' images are an open countable cover by
second countable subspaces (`secondCountableTopology_of_countable_cover`). Charts: for a nonempty
piece `X n` the inclusion is an open partial homeomorphism `pieceOpenEmb n`
(`IsOpenEmbedding.toOpenPartialHomeomorph`, the pattern of `BlowUp/GluedCharts.lean`), and every
chart `φ` of `X n` gives the chart `limitChart n φ := (pieceOpenEmb n).symm ≫ₕ φ` of the limit;
the atlas is all of them. The chart change between a chart from `X n` and one from `X m` is
`ψ ∘ transition n m ∘ φ.symm` with `transition n m : X n ⊇ toLimit n ⁻¹' range (toLimit m) → X m`
the transition through the limit (`(pieceOpenEmb m).symm ∘ toLimit n`), and `transition` is
analytic: at a point `x` with local inverse `Φ` of the composite embedding `X m → X (max n m)` at
`transition n m x` (`isLocalDiffeomorph_iter`), `transition n m = Φ.symm ∘ iter (n ≤ max n m)`
near `x`. This is where Włodarczyk's canonicity supplies the identifications of the pieces on
their overlaps [Wlo09, §4.1], here read through the composites (`contMDiffOn_transition`,
`limitIsManifold` by `isManifold_of_contDiffOn`). The inclusions are then analytic
(`toLimit n = (limitChart n (chartAt x)).symm ∘ chartAt x` near `x`) and local analytic
isomorphisms (`pieceDiffeomorph`), hence analytic open embeddings onto their open images
(`isAnalyticOpenEmbedding_toLimitMap`, `isAnalyticIsoOver_toLimitMap`).

* `limitT2Space`, `limitSecondCountableTopology`.
* `pieceOpenEmb`, `repIdx`, `rep`, `limitChart`, `limitChartedSpace`, `mem_atlas_limit_iff`,
  `limitChart_mem_atlas`.
* `transition`, `contMDiffOn_transition`, `mem_source_trans_limitChart`, `limitIsManifold`.
* `limitManifold`, `contMDiff_toLimit`, `toLimitMap`, `pieceDiffeomorph`,
  `isLocalDiffeomorph_toLimit`, `isAnalyticOpenEmbedding_toLimitMap`,
  `isAnalyticIsoOver_toLimitMap`.

The gluing is elementary and not in the sources in this form.
-/

@[expose] public noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace OpenEmbeddingChain

variable (c : OpenEmbeddingChain.{u} 𝕜 E)

/-! ### Hausdorff and second countable -/

/-- The limit is Hausdorff — two points lie in a common piece, are separated there,
and the inclusion is an open injective map. -/
instance limitT2Space : T2Space c.Limit := by
  refine ⟨fun p q hpq => ?_⟩
  obtain ⟨k, x, y, rfl, rfl⟩ := c.exists_common_toLimit p q
  have hxy : x ≠ y := fun h => hpq (congrArg (c.toLimit k) h)
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hxy
  exact ⟨c.toLimit k '' U, c.toLimit k '' V, c.isOpenMap_toLimit k U hU,
    c.isOpenMap_toLimit k V hV, ⟨x, hxU, rfl⟩, ⟨y, hyV, rfl⟩,
    (Set.disjoint_image_iff (c.toLimit_injective k)).mpr hUV⟩

/-- The limit is second countable — a countable open cover by the images of the
pieces, each homeomorphic to a second countable manifold. -/
instance limitSecondCountableTopology : SecondCountableTopology c.Limit := by
  have : ∀ n, SecondCountableTopology (Set.range (c.toLimit n)) := fun n =>
    (c.isOpenEmbedding_toLimit n).isEmbedding.toHomeomorph.symm.secondCountableTopology
  exact secondCountableTopology_of_countable_cover c.isOpen_range_toLimit c.iUnion_range_toLimit

/-! ### The charts of the limit -/

/-- The inclusion of a nonempty piece as an open partial homeomorphism (source the
whole piece, target its image). -/
def pieceOpenEmb (n : ℕ) [Nonempty (c.X n)] : OpenPartialHomeomorph (c.X n) c.Limit :=
  (c.isOpenEmbedding_toLimit n).toOpenPartialHomeomorph (c.toLimit n)

/-- `pieceOpenEmb` is the inclusion. -/
theorem pieceOpenEmb_apply (n : ℕ) [Nonempty (c.X n)] (x : c.X n) :
    c.pieceOpenEmb n x = c.toLimit n x :=
  congr_fun ((c.isOpenEmbedding_toLimit n).toOpenPartialHomeomorph_apply (c.toLimit n)) x

/-- The source of `pieceOpenEmb` is the whole piece. -/
theorem pieceOpenEmb_source (n : ℕ) [Nonempty (c.X n)] : (c.pieceOpenEmb n).source = univ :=
  (c.isOpenEmbedding_toLimit n).toOpenPartialHomeomorph_source (c.toLimit n)

/-- The target of `pieceOpenEmb` is the image of the piece. -/
theorem pieceOpenEmb_target (n : ℕ) [Nonempty (c.X n)] :
    (c.pieceOpenEmb n).target = Set.range (c.toLimit n) :=
  (c.isOpenEmbedding_toLimit n).toOpenPartialHomeomorph_target (c.toLimit n)

/-- The inverse of `pieceOpenEmb` undoes the inclusion. -/
theorem pieceOpenEmb_symm_toLimit (n : ℕ) [Nonempty (c.X n)] (x : c.X n) :
    (c.pieceOpenEmb n).symm (c.toLimit n x) = x :=
  (c.isOpenEmbedding_toLimit n).toOpenPartialHomeomorph_left_inv (c.toLimit n)

/-- The inclusion undoes the inverse of `pieceOpenEmb` on the image of the piece. -/
theorem toLimit_pieceOpenEmb_symm (n : ℕ) [Nonempty (c.X n)] {p : c.Limit}
    (hp : p ∈ Set.range (c.toLimit n)) : c.toLimit n ((c.pieceOpenEmb n).symm p) = p :=
  (c.isOpenEmbedding_toLimit n).toOpenPartialHomeomorph_right_inv (c.toLimit n) hp

/-- A piece containing a given point of the limit (chosen). -/
def repIdx (p : c.Limit) : ℕ := (c.toLimit_surjective p).choose

/-- The point of the piece `repIdx p` over `p` (chosen). -/
def rep (p : c.Limit) : c.X (c.repIdx p) := (c.toLimit_surjective p).choose_spec.choose

/-- `rep p` lies over `p`. -/
theorem toLimit_rep (p : c.Limit) : c.toLimit (c.repIdx p) (c.rep p) = p :=
  (c.toLimit_surjective p).choose_spec.choose_spec

/-- The piece `repIdx p` is nonempty. -/
theorem nonempty_repIdx (p : c.Limit) : Nonempty (c.X (c.repIdx p)) := ⟨c.rep p⟩

/-- The chart of the limit over a nonempty piece obtained from a chart `φ` of the
piece — the inverse of the piece's inclusion followed by `φ`. -/
def limitChart (n : ℕ) [Nonempty (c.X n)] (φ : OpenPartialHomeomorph (c.X n) E) :
    OpenPartialHomeomorph c.Limit E :=
  (c.pieceOpenEmb n).symm.trans φ

/-- The source of `limitChart n φ` — the points of the image of the piece whose
representative lies in `φ`'s source. -/
theorem limitChart_source (n : ℕ) [Nonempty (c.X n)] (φ : OpenPartialHomeomorph (c.X n) E) :
    (c.limitChart n φ).source = Set.range (c.toLimit n) ∩ (c.pieceOpenEmb n).symm ⁻¹' φ.source := by
  rw [limitChart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    pieceOpenEmb_target]

/-- The target of `limitChart n φ` is the target of `φ`. -/
theorem limitChart_target (n : ℕ) [Nonempty (c.X n)] (φ : OpenPartialHomeomorph (c.X n) E) :
    (c.limitChart n φ).target = φ.target := by
  rw [limitChart, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
    pieceOpenEmb_source, preimage_univ, inter_univ]

/-- `limitChart n φ` reads `φ` at the representative in the piece. -/
theorem limitChart_apply (n : ℕ) [Nonempty (c.X n)] (φ : OpenPartialHomeomorph (c.X n) E)
    (p : c.Limit) : c.limitChart n φ p = φ ((c.pieceOpenEmb n).symm p) := rfl

/-- The inverse of `limitChart n φ` is the inclusion after the inverse of `φ`. -/
theorem limitChart_symm_apply (n : ℕ) [Nonempty (c.X n)] (φ : OpenPartialHomeomorph (c.X n) E)
    (v : E) : (c.limitChart n φ).symm v = c.toLimit n (φ.symm v) := by
  rw [limitChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm]
  exact c.pieceOpenEmb_apply n _

/-- The inverse of the inclusion of the piece `repIdx p` sends `p` to `rep p`. -/
theorem pieceOpenEmb_symm_rep (p : c.Limit) :
    haveI := c.nonempty_repIdx p
    (c.pieceOpenEmb (c.repIdx p)).symm p = c.rep p := by
  have := c.nonempty_repIdx p
  have h := c.pieceOpenEmb_symm_toLimit (c.repIdx p) (c.rep p)
  rwa [c.toLimit_rep p] at h

/-- The charted-space structure of the limit — the charts `limitChart n φ` of the
nonempty pieces' charts; the chart at `p` is the one from `chartAt (rep p)`. -/
instance limitChartedSpace : ChartedSpace E c.Limit where
  atlas := {Φ | ∃ (n : ℕ) (_ : Nonempty (c.X n)) (φ : OpenPartialHomeomorph (c.X n) E),
    φ ∈ atlas E (c.X n) ∧ Φ = c.limitChart n φ}
  chartAt p :=
    haveI := c.nonempty_repIdx p
    c.limitChart (c.repIdx p) (chartAt E (c.rep p))
  mem_chart_source p := by
    have := c.nonempty_repIdx p
    rw [limitChart_source, mem_inter_iff, mem_preimage, c.pieceOpenEmb_symm_rep p]
    exact ⟨⟨c.rep p, c.toLimit_rep p⟩, mem_chart_source E _⟩
  chart_mem_atlas p :=
    haveI := c.nonempty_repIdx p
    ⟨c.repIdx p, inferInstance, chartAt E (c.rep p), chart_mem_atlas E _, rfl⟩

/-- The atlas of the limit consists of the charts `limitChart n φ` of the nonempty
pieces' charts. -/
theorem mem_atlas_limit_iff {Φ : OpenPartialHomeomorph c.Limit E} :
    Φ ∈ atlas E c.Limit ↔ ∃ (n : ℕ) (_ : Nonempty (c.X n)) (φ : OpenPartialHomeomorph (c.X n) E),
      φ ∈ atlas E (c.X n) ∧ Φ = c.limitChart n φ := Iff.rfl

/-- Each `limitChart n φ` of a chart `φ` of a nonempty piece lies in the atlas. -/
theorem limitChart_mem_atlas (n : ℕ) [Nonempty (c.X n)] {φ : OpenPartialHomeomorph (c.X n) E}
    (hφ : φ ∈ atlas E (c.X n)) : c.limitChart n φ ∈ atlas E c.Limit :=
  ⟨n, inferInstance, φ, hφ, rfl⟩

/-! ### The transition between two pieces is analytic -/

/-- The transition `X n ⊇ toLimit n ⁻¹' range (toLimit m) → X m` through the
limit, `(pieceOpenEmb m).symm ∘ toLimit n` (defined everywhere, meaningful on the domain). -/
def transition (n m : ℕ) [Nonempty (c.X m)] (x : c.X n) : c.X m :=
  (c.pieceOpenEmb m).symm (c.toLimit n x)

/-- The transition is over the limit. -/
theorem toLimit_transition (n m : ℕ) [Nonempty (c.X m)] {x : c.X n}
    (hx : c.toLimit n x ∈ Set.range (c.toLimit m)) :
    c.toLimit m (c.transition n m x) = c.toLimit n x :=
  c.toLimit_pieceOpenEmb_symm m hx

/-- The transition agrees with the composites in the piece `max n m`. -/
theorem iter_transition (n m : ℕ) [Nonempty (c.X m)] {x : c.X n}
    (hx : c.toLimit n x ∈ Set.range (c.toLimit m)) :
    c.iter (le_max_right n m) (c.transition n m x) = c.iter (le_max_left n m) x :=
  (c.toLimit_eq_iff_iter (le_max_right n m) (le_max_left n m)).mp (c.toLimit_transition n m hx)

/-- The domain of the transition is open. -/
theorem isOpen_transitionDomain (n m : ℕ) :
    IsOpen (c.toLimit n ⁻¹' Set.range (c.toLimit m)) :=
  (c.isOpen_range_toLimit m).preimage (c.continuous_toLimit n)

/-- The transition is continuous on its domain. -/
theorem continuousOn_transition (n m : ℕ) [Nonempty (c.X m)] :
    ContinuousOn (c.transition n m) (c.toLimit n ⁻¹' Set.range (c.toLimit m)) :=
  (c.pieceOpenEmb m).symm.continuousOn.comp (c.continuous_toLimit n).continuousOn fun x hx => by
    rw [OpenPartialHomeomorph.symm_source, pieceOpenEmb_target]
    exact hx

/-- The transition is analytic on its domain: near `x` it is `Φ.symm ∘ iter`, `Φ` a local inverse of
the composite embedding `X m → X (max n m)` at `transition n m x` (Włodarczyk's identifications
of the pieces on their overlaps by canonicity, [Wlo09, §4.1], read through the composites). -/
theorem contMDiffOn_transition (n m : ℕ) [Nonempty (c.X m)] :
    ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω (c.transition n m)
      (c.toLimit n ⁻¹' Set.range (c.toLimit m)) := by
  intro x hx
  have hD := c.isOpen_transitionDomain n m
  obtain ⟨Φ, hΦx, hΦ⟩ :=
    (c.isLocalDiffeomorph_iter (le_max_right n m) (c.transition n m x)).exists_partialDiffeomorph
  have key : c.transition n m =ᶠ[𝓝 x] fun y => Φ.symm (c.iter (le_max_left n m) y) := by
    have h1 : ∀ᶠ y in 𝓝 x, y ∈ c.toLimit n ⁻¹' Set.range (c.toLimit m) := hD.mem_nhds hx
    have h2 : ∀ᶠ y in 𝓝 x, c.transition n m y ∈ Φ.source :=
      ((c.continuousOn_transition n m).continuousAt (hD.mem_nhds hx)).preimage_mem_nhds
        (Φ.open_source.mem_nhds hΦx)
    filter_upwards [h1, h2] with y hyD hyΦ
    rw [← c.iter_transition n m hyD, hΦ hyΦ]
    exact (Φ.left_inv hyΦ).symm
  refine (ContMDiffAt.congr_of_eventuallyEq ?_ key).contMDiffWithinAt
  have hmem : c.iter (le_max_left n m) x ∈ Φ.target := by
    rw [← c.iter_transition n m hx, hΦ hΦx]
    exact Φ.map_source hΦx
  exact (Φ.symm.contMDiffOn.contMDiffAt (Φ.open_target.mem_nhds hmem)).comp x
    (c.iter (le_max_left n m)).contMDiff.contMDiffAt

/-! ### The limit is an analytic manifold -/

/-- A point `v` of the source of the chart change from `limitChart n φ` to
`limitChart m ψ` lies in `φ`'s target, and `φ.symm v` in the transition's domain, in `φ`'s source
and over `ψ`'s source. -/
theorem mem_source_trans_limitChart (n m : ℕ) [Nonempty (c.X n)] [Nonempty (c.X m)]
    (φ : OpenPartialHomeomorph (c.X n) E) (ψ : OpenPartialHomeomorph (c.X m) E) {v : E}
    (hv : v ∈ ((c.limitChart n φ).symm ≫ₕ c.limitChart m ψ).source) :
    v ∈ φ.target ∧ φ.symm v ∈ c.toLimit n ⁻¹' Set.range (c.toLimit m) ∩ φ.source ∩
      c.transition n m ⁻¹' ψ.source := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    limitChart_target] at hv
  obtain ⟨hv1, hv2⟩ := hv
  rw [mem_preimage, limitChart_symm_apply, limitChart_source, mem_inter_iff, mem_preimage] at hv2
  exact ⟨hv1, ⟨⟨hv2.1, φ.map_target hv1⟩, hv2.2⟩⟩

/-- The limit is an analytic manifold — its chart changes are the transitions read
in the pieces' charts (`ψ ∘ transition n m ∘ φ.symm`), analytic by `contMDiffOn_transition`
(`isManifold_of_contDiffOn`, `contMDiffOn_iff_of_mem_maximalAtlas'`). -/
instance limitIsManifold : IsManifold 𝓘(𝕜, E) ω c.Limit := by
  refine isManifold_of_contDiffOn 𝓘(𝕜, E) ω c.Limit ?_
  rintro _ _ ⟨n, hn, φ, hφ, rfl⟩ ⟨m, hm, ψ, hψ, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ]
  have h1 : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω (c.transition n m)
      (c.toLimit n ⁻¹' Set.range (c.toLimit m) ∩ φ.source ∩ c.transition n m ⁻¹' ψ.source) :=
    (c.contMDiffOn_transition n m).mono fun x hx => hx.1.1
  rw [contMDiffOn_iff_of_mem_maximalAtlas' (IsManifold.subset_maximalAtlas hφ)
    (IsManifold.subset_maximalAtlas hψ) (fun x hx => hx.1.2) fun x hx => hx.2] at h1
  simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp] at h1
  refine h1.congr_mono (fun v _ => ?_) fun v hv => ?_
  · exact congrArg (fun p => ψ ((c.pieceOpenEmb m).symm p)) (c.limitChart_symm_apply n φ v)
  · obtain ⟨hvt, hvs⟩ := c.mem_source_trans_limitChart n m φ ψ hv
    exact ⟨φ.symm v, hvs, φ.right_inv hvt⟩

/-- The direct limit as a bundled analytic manifold (Włodarczyk's glued manifold `M̃`, [Wlo09,
§4.1]). -/
def limitManifold : AnalyticManifold.{u} 𝕜 E := ⟨c.Limit⟩

/-! ### The inclusions of the pieces are analytic open embeddings -/

/-- The inverse of a piece's inclusion is analytic on the image of the piece — near
`toLimit n y` it is `(chartAt y).symm ∘ limitChart n (chartAt y)`. -/
theorem contMDiffOn_pieceOpenEmb_symm (n : ℕ) [Nonempty (c.X n)] :
    ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω (c.pieceOpenEmb n).symm (Set.range (c.toLimit n)) := by
  rintro _ ⟨y, rfl⟩
  have hΦ : c.limitChart n (chartAt E y) ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω c.Limit :=
    IsManifold.subset_maximalAtlas (c.limitChart_mem_atlas n (chart_mem_atlas E y))
  have hsrc : c.toLimit n y ∈ (c.limitChart n (chartAt E y)).source := by
    rw [limitChart_source, mem_inter_iff, mem_preimage, pieceOpenEmb_symm_toLimit]
    exact ⟨⟨y, rfl⟩, mem_chart_source E y⟩
  have h1 : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω ((chartAt E y).symm ∘ c.limitChart n (chartAt E y))
      (c.limitChart n (chartAt E y)).source :=
    (contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (chart_mem_atlas E y))).comp
      (contMDiffOn_of_mem_maximalAtlas hΦ) fun p hp => by
        have h := (c.limitChart n (chartAt E y)).map_source hp
        rwa [limitChart_target] at h
  refine ((h1.congr fun p hp => ?_).contMDiffAt
    ((c.limitChart n (chartAt E y)).open_source.mem_nhds hsrc)).contMDiffWithinAt
  rw [limitChart_source, mem_inter_iff, mem_preimage] at hp
  rw [Function.comp_apply, limitChart_apply, (chartAt E y).left_inv hp.2]

/-- Each inclusion is analytic — near `x` it is
`(limitChart n (chartAt x)).symm ∘ chartAt x`. -/
theorem contMDiff_toLimit (n : ℕ) : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω (c.toLimit n) := by
  intro x
  have : Nonempty (c.X n) := ⟨x⟩
  have hΦ : c.limitChart n (chartAt E x) ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω c.Limit :=
    IsManifold.subset_maximalAtlas (c.limitChart_mem_atlas n (chart_mem_atlas E x))
  have h1 : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω ((c.limitChart n (chartAt E x)).symm ∘ chartAt E x)
      (chartAt E x).source :=
    (contMDiffOn_symm_of_mem_maximalAtlas hΦ).comp
      (contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (chart_mem_atlas E x)))
      fun y hy => by
        rw [limitChart_target]
        exact (chartAt E x).map_source hy
  refine (h1.congr fun y hy => ?_).contMDiffAt
    ((chartAt E x).open_source.mem_nhds (mem_chart_source E x))
  rw [Function.comp_apply, limitChart_symm_apply, (chartAt E x).left_inv hy]

/-- The inclusion of a piece as an analytic map into the limit manifold. -/
def toLimitMap (n : ℕ) : AnalyticMap (c.X n) c.limitManifold := ⟨c.toLimit n, c.contMDiff_toLimit n⟩

/-- `toLimitMap` is the inclusion. -/
theorem toLimitMap_apply (n : ℕ) (x : c.X n) : c.toLimitMap n x = c.toLimit n x := rfl

/-- The inclusion of a nonempty piece as a partial diffeomorphism onto its (open)
image. -/
def pieceDiffeomorph (n : ℕ) [Nonempty (c.X n)] :
    PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (c.X n) c.Limit ω where
  toPartialEquiv := (c.pieceOpenEmb n).toPartialEquiv
  open_source := (c.pieceOpenEmb n).open_source
  open_target := (c.pieceOpenEmb n).open_target
  contMDiffOn_toFun := (c.contMDiff_toLimit n).contMDiffOn.congr fun x _ => c.pieceOpenEmb_apply n x
  contMDiffOn_invFun := (c.contMDiffOn_pieceOpenEmb_symm n).mono (c.pieceOpenEmb_target n).subset

/-- Each inclusion is a local analytic isomorphism (`pieceDiffeomorph` at every
point). -/
theorem isLocalDiffeomorph_toLimit (n : ℕ) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (c.toLimit n) := fun x =>
  haveI : Nonempty (c.X n) := ⟨x⟩
  IsLocalDiffeomorphAt.of_eqOn (c.pieceDiffeomorph n)
    (by
      change x ∈ (c.pieceOpenEmb n).source
      rw [pieceOpenEmb_source]
      exact mem_univ x)
    fun y _ => (c.pieceOpenEmb_apply n y).symm

/-- Each inclusion is an analytic open embedding (Włodarczyk's open embeddings of desingularizations
along open embeddings, [Wlo09, §4]). -/
theorem isAnalyticOpenEmbedding_toLimitMap (n : ℕ) : IsAnalyticOpenEmbedding (c.toLimitMap n) :=
  ⟨c.isLocalDiffeomorph_toLimit n, c.toLimit_injective n⟩

/-- The range of `toLimitMap n` is the image of the piece. -/
theorem range_toLimitMap (n : ℕ) : Set.range (c.toLimitMap n) = Set.range (c.toLimit n) := rfl

/-- Each inclusion is an analytic isomorphism onto its open image (the identification `U_r = Ũ` of
[Wlo09, Theorem 2.0.3 (1)]; the field `toSpace_isIso` of `ExtensionCompatibleFamily`). -/
theorem isAnalyticIsoOver_toLimitMap (n : ℕ) :
    (c.toLimitMap n).IsIsoOver (Set.range (c.toLimitMap n)) :=
  ⟨fun x => c.isLocalDiffeomorph_toLimit n x, fun x _ => ⟨x, rfl⟩,
    fun _ _ _ _ hxy => c.toLimit_injective n hxy, fun _ ⟨x, hx⟩ => ⟨x, ⟨x, rfl⟩, hx⟩⟩

end OpenEmbeddingChain

end Manifold
