/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Atlas
public import Hironaka.Manifold.BlowUp.Lift
import Hironaka.Manifold.BlowUp.Transition
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The gluing of the blowing-up: pieces and transition maps

The blowing-up `M'` of `M` with centre `Y` is obtained by gluing the local blowings-up
`π⁻¹(U) = V' × W` over the adapted charts `φ : U → V × W` [BM88, Definition 4.1]. Here the
**pieces** are indexed by an adapted chart `(φ, σ)` of `Y` (shrunk to the universe of `M`)
together with a chart index `i < c`: the piece is the chart domain `S = π_i⁻¹(ψ(φ(U)))` of the
local model (`blowUpChartMap`), and its **blow-down** is `β = φ⁻¹ ∘ ψ⁻¹ ∘ π_i : S → U`. Two
pieces `(φ, σ, i)` and `(φ', σ', i')` are glued along the **transition domain**
`{u ∈ S | β u ∈ U' ∧ D_{i'}(u) ≠ 0}` by the **transition map**, the lift
(`Hironaka.Manifold.BlowUp.Lift`) of the coordinate change `ψ ∘ φ' ∘ φ⁻¹ ∘ ψ⁻¹` from chart `i`
to chart `i'`. The transition maps commute with the blow-downs, are the identity on a piece with
itself, and satisfy the inverse and cocycle laws, every law being an instance of the uniqueness
of lifts (two continuous lifts of the same coordinate change through the same chart agree, by
density of the complement of the exceptional hyperplane) or of the cocycle of the direction
quotients.

This file builds the pieces, the transition data and their laws;
`Hironaka.Manifold.BlowUp.Glued` feeds them to `TopCat.GlueData.mk'`. The gluing is not
carried out in the source, which states the result.
-/

@[expose] public section

open TopologicalSpace
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

namespace BlowUpGlue

noncomputable section

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : Type u} [TopologicalSpace M] [ChartedSpace E M] (Y : Set M)
  (c : ℕ)

/-! ### The pieces -/

/-- The adapted charts of `Y` with their block embeddings. -/
abbrev AdaptedChart : Type _ :=
  {x : OpenPartialHomeomorph M E × (Fin c ↪ Fin n) // IsAdaptedChart ψ Y x.1 x.2}

/-- The adapted charts form a small type in the universe of `M`: a chart is determined by its
map, its inverse and its source, and `E ≃ Kⁿ`. -/
instance small_adaptedChart : Small.{u} (AdaptedChart ψ Y c) := by
  have hE : Small.{u} E := small_map ψ.toEquiv
  have h1 : Small.{u} (OpenPartialHomeomorph M E) :=
    small_of_injective (f := fun e : OpenPartialHomeomorph M E =>
      ((⇑e : M → E), (⇑e.symm : E → M), e.source)) fun e e' h => by
      simp only [Prod.mk.injEq] at h
      exact e.ext e' (congrFun h.1) (congrFun h.2.1) h.2.2
  infer_instance

/-- The index type of the pieces: an adapted chart (shrunk to the universe of `M`) and a chart
index `i < c`. -/
abbrev PieceIdx : Type u := Shrink.{u} (AdaptedChart ψ Y c) × Fin c

variable {ψ Y c}

/-- The adapted chart of a piece. -/
def pieceData (j : PieceIdx ψ Y c) : AdaptedChart ψ Y c :=
  (equivShrink (AdaptedChart ψ Y c)).symm j.1

/-- The chart of a piece. -/
def pieceChart (j : PieceIdx ψ Y c) : OpenPartialHomeomorph M E := (pieceData j).1.1

/-- The block embedding of a piece. -/
def pieceEmb (j : PieceIdx ψ Y c) : Fin c ↪ Fin n := (pieceData j).1.2

/-- The chart of a piece is adapted to `Y`, with the piece's block indices. -/
theorem isAdaptedChart_piece (j : PieceIdx ψ Y c) :
    IsAdaptedChart ψ Y (pieceChart j) (pieceEmb j) := (pieceData j).2

/-- The chart of a piece lies in the maximal atlas of `M`. -/
theorem mem_maximalAtlas_piece (j : PieceIdx ψ Y c) :
    pieceChart j ∈ maximalAtlas 𝓘(𝕜, E) ω M := (isAdaptedChart_piece j).1

/-- Every adapted chart with every index is a piece. -/
theorem exists_piece {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n}
    (hφ : IsAdaptedChart ψ Y φ σ) (i : Fin c) :
    ∃ j : PieceIdx ψ Y c, pieceChart j = φ ∧ pieceEmb j = σ ∧ j.2 = i :=
  ⟨(equivShrink (AdaptedChart ψ Y c) ⟨(φ, σ), hφ⟩, i), by simp [pieceChart, pieceData],
    by simp [pieceEmb, pieceData], rfl⟩

/-- The chart map `π_i` of a piece. -/
abbrev pieceMap (j : PieceIdx ψ Y c) : (Fin n → 𝕜) → (Fin n → 𝕜) :=
  blowUpChartMap (pieceEmb j) j.2

/-- The chart domain `π_i⁻¹(ψ(φ(U)))` of a piece. -/
def pieceSet (j : PieceIdx ψ Y c) : Set (Fin n → 𝕜) :=
  pieceMap j ⁻¹' (ψ '' (pieceChart j).target)

/-- The coordinate set of a piece is open (the preimage of an open set under the polynomial `π_i`).
-/
theorem isOpen_pieceSet (j : PieceIdx ψ Y c) : IsOpen (pieceSet j) :=
  (ψ.toHomeomorph.isOpenMap _ (pieceChart j).open_target).preimage
    (contDiff_blowUpChartMap _).continuous

/-- The blow-down `β = φ⁻¹ ∘ ψ⁻¹ ∘ π_i` of a piece. -/
def blowDown (j : PieceIdx ψ Y c) (u : Fin n → 𝕜) : M :=
  (pieceChart j).symm (ψ.symm (pieceMap j u))

/-- For `u` in the piece set, `ψ⁻¹(π_i u)` lies in the target of the piece's chart. -/
theorem symm_pieceMap_mem_target {j : PieceIdx ψ Y c} {u : Fin n → 𝕜} (hu : u ∈ pieceSet j) :
    ψ.symm (pieceMap j u) ∈ (pieceChart j).target := by
  obtain ⟨y, hy, hyu⟩ := hu
  rw [← hyu, ψ.symm_apply_apply]
  exact hy

/-- The blow-down of a point of the piece set lies in the source of the piece's chart. -/
theorem blowDown_mem_source {j : PieceIdx ψ Y c} {u : Fin n → 𝕜} (hu : u ∈ pieceSet j) :
    blowDown j u ∈ (pieceChart j).source :=
  (pieceChart j).map_target (symm_pieceMap_mem_target hu)

/-- The blow-down commutes with the chart: `ψ (φ (blowDown j u)) = π_i u` (condition (2) of
[BM88, Definition 4.1], chartwise). -/
theorem apply_blowDown {j : PieceIdx ψ Y c} {u : Fin n → 𝕜} (hu : u ∈ pieceSet j) :
    ψ (pieceChart j (blowDown j u)) = pieceMap j u := by
  rw [blowDown, (pieceChart j).right_inv (symm_pieceMap_mem_target hu), ψ.apply_symm_apply]

/-- The blow-down of a piece is continuous on the piece set. -/
theorem continuousOn_blowDown (j : PieceIdx ψ Y c) : ContinuousOn (blowDown j) (pieceSet j) :=
  (pieceChart j).continuousOn_symm.comp
    (ψ.symm.continuous.comp_continuousOn (contDiff_blowUpChartMap _).continuous.continuousOn)
    fun _ hu => symm_pieceMap_mem_target hu

/-! ### The transition data -/

/-- The coordinate change between the charts of two pieces. -/
abbrev pieceChange (j j' : PieceIdx ψ Y c) : (Fin n → 𝕜) → (Fin n → 𝕜) :=
  chartChange ψ (pieceChart j) (pieceChart j')

/-- The domain of the coordinate change between the charts of two pieces. -/
abbrev pieceChangeDom (j j' : PieceIdx ψ Y c) : Set (Fin n → 𝕜) :=
  chartChangeDom ψ (pieceChart j) (pieceChart j')

/-- The direction quotient `D_{i'}` of the lift of the coordinate change from chart `i` of the
first piece to chart `i'` of the second. -/
abbrev transDir (j j' : PieceIdx ψ Y c) : (Fin n → 𝕜) → 𝕜 :=
  liftDir (pieceEmb j) (pieceEmb j') j.2 (pieceChange j j') j'.2

/-- The transition domain: the points of the first piece over the second chart whose direction
lies in chart `i'`. -/
def transDom (j j' : PieceIdx ψ Y c) : Set (Fin n → 𝕜) :=
  pieceMap j ⁻¹' pieceChangeDom j j' ∩ {v | transDir j j' v ≠ 0}

/-- The transition map: the lift of the coordinate change to the blow-up charts. -/
def transMap (j j' : PieceIdx ψ Y c) : (Fin n → 𝕜) → (Fin n → 𝕜) :=
  liftMap (pieceEmb j) (pieceEmb j') j.2 (pieceChange j j') j'.2

section Laws

variable (j j' j'' : PieceIdx ψ Y c)

/-- The domain of the coordinate change between two pieces is open. -/
theorem isOpen_pieceChangeDom : IsOpen (pieceChangeDom j j') := isOpen_chartChangeDom ψ

/-- The coordinate change between two pieces is analytic on its domain. -/
theorem analyticOnNhd_pieceChange :
    AnalyticOnNhd 𝕜 (pieceChange j j') (pieceChangeDom j j') :=
  analyticOnNhd_chartChange ψ (mem_maximalAtlas_piece j) (mem_maximalAtlas_piece j')

/-- The coordinate change between two pieces preserves the centre in both directions (both charts
are adapted to `Y`). -/
theorem mem_center_iff_pieceChange {x : Fin n → 𝕜} (hx : x ∈ pieceChangeDom j j') :
    x ∈ blowUpCenter (pieceEmb j) ↔ pieceChange j j' x ∈ blowUpCenter (pieceEmb j') :=
  mem_center_iff_chartChange ψ (isAdaptedChart_piece j) (isAdaptedChart_piece j') hx

/-- The transition domain lies in the piece set. -/
theorem transDom_subset : transDom j j' ⊆ pieceSet j := fun _ hu =>
  chartChangeDom_subset ψ hu.1

/-- The transition domain is open. -/
theorem isOpen_transDom : IsOpen (transDom j j') :=
  (analyticOnNhd_liftDir (isOpen_pieceChangeDom j j') (analyticOnNhd_pieceChange j j')
    (fun _ hx => mem_center_iff_pieceChange j j' hx) j'.2).continuousOn.isOpen_inter_preimage
    ((isOpen_pieceChangeDom j j').preimage (contDiff_blowUpChartMap _).continuous)
    isOpen_compl_singleton

/-- The transition map is analytic on the transition domain. -/
theorem analyticOnNhd_transMap : AnalyticOnNhd 𝕜 (transMap j j') (transDom j j') :=
  analyticOnNhd_liftMap (isOpen_pieceChangeDom j j') (analyticOnNhd_pieceChange j j')
    (fun _ hx => mem_center_iff_pieceChange j j' hx) j'.2

/-- The direction quotient of the transition is analytic where the coordinate change is defined. -/
theorem analyticOnNhd_transDir :
    AnalyticOnNhd 𝕜 (transDir j j') (pieceMap j ⁻¹' pieceChangeDom j j') :=
  analyticOnNhd_liftDir (isOpen_pieceChangeDom j j') (analyticOnNhd_pieceChange j j')
    (fun _ hx => mem_center_iff_pieceChange j j' hx) j'.2

variable {j j' j''}

/-- The points of the first piece over the second chart. -/
theorem pieceMap_mem_pieceChangeDom_iff {u : Fin n → 𝕜} (hu : u ∈ pieceSet j) :
    pieceMap j u ∈ pieceChangeDom j j' ↔ blowDown j u ∈ (pieceChart j').source := by
  rw [mem_chartChangeDom_iff]
  exact and_iff_right (symm_pieceMap_mem_target hu)

/-- `π_i u` lies in the domain of the trivial coordinate change of a piece with itself. -/
theorem pieceMap_mem_pieceChangeDom_self {u : Fin n → 𝕜} (hu : u ∈ pieceSet j) :
    pieceMap j u ∈ pieceChangeDom j j :=
  (pieceMap_mem_pieceChangeDom_iff hu).mpr (blowDown_mem_source hu)

/-- The transition map commutes with the chart maps: `π_{i'} ∘ T = g ∘ π_i`. -/
theorem pieceMap_transMap {u : Fin n → 𝕜} (hu : u ∈ transDom j j') :
    pieceMap j' (transMap j j' u) = pieceChange j j' (pieceMap j u) :=
  blowUpChartMap_liftMap (fun _ hx => mem_center_iff_pieceChange j j' hx) j'.2 hu.1 hu.2

/-- The transition map commutes with the blow-downs. -/
theorem blowDown_transMap {u : Fin n → 𝕜} (hu : u ∈ transDom j j') :
    blowDown j' (transMap j j' u) = blowDown j u := by
  have hx : pieceMap j u ∈ pieceChangeDom j j' := hu.1
  rw [mem_chartChangeDom_iff] at hx
  rw [blowDown, pieceMap_transMap hu, blowDown]
  simp only [pieceChange, chartChange, ContinuousLinearEquiv.symm_apply_apply,
    (pieceChart j').left_inv hx.2]

/-- The transition map carries the transition domain into the target piece set. -/
theorem transMap_mem_pieceSet {u : Fin n → 𝕜} (hu : u ∈ transDom j j') :
    transMap j j' u ∈ pieceSet j' := by
  change pieceMap j' (transMap j j' u) ∈ ψ '' (pieceChart j').target
  rw [pieceMap_transMap hu]
  exact chartChangeDom_subset ψ (chartChange_mem ψ hu.1)

/-- The direction quotient of a piece with itself is `1`. -/
theorem transDir_self {u : Fin n → 𝕜} (hu : u ∈ pieceSet j) : transDir j j u = 1 :=
  liftDir_self_of_eqOn_id (isOpen_pieceChangeDom j j) (fun _ hx => chartChange_self ψ hx)
    (pieceMap_mem_pieceChangeDom_self hu)

/-- The transition domain of a piece with itself is the whole piece set. -/
theorem transDom_self : transDom j j = pieceSet j := by
  refine Set.Subset.antisymm (transDom_subset j j) fun u hu =>
    ⟨pieceMap_mem_pieceChangeDom_self hu, ?_⟩
  change transDir j j u ≠ 0
  rw [transDir_self hu]
  exact one_ne_zero

/-- The transition map of a piece with itself is the identity. -/
theorem transMap_self {u : Fin n → 𝕜} (hu : u ∈ pieceSet j) : transMap j j u = u := by
  rw [transMap, liftMap_eq_blowUpTransition (isOpen_pieceChangeDom j j)
    (fun _ hx => chartChange_self ψ hx) j.2 (pieceMap_mem_pieceChangeDom_self hu)
    (by change transDir j j u ≠ 0; rw [transDir_self hu]; exact one_ne_zero), blowUpTransition_self,
    id]

/-- The cocycle of the direction quotients through a third piece. -/
theorem transDir_transMap {u : Fin n → 𝕜} (hu : u ∈ transDom j j')
    (hu' : pieceMap j u ∈ pieceChangeDom j j'') :
    transDir j j'' u = transDir j j' u * transDir j' j'' (transMap j j' u) := by
  have hV : IsOpen (pieceChangeDom j j' ∩ pieceChangeDom j j'') :=
    (isOpen_pieceChangeDom j j').inter (isOpen_pieceChangeDom j j'')
  have hcomp : ∀ x ∈ pieceChangeDom j j' ∩ pieceChangeDom j j'',
      (pieceChange j' j'' ∘ pieceChange j j') x = pieceChange j j'' x := fun x hx =>
    chartChange_comp ψ hx.1
  change liftDir (pieceEmb j) (pieceEmb j'') j.2 (pieceChange j j'') j''.2 u = _
  rw [← liftDir_congr hV hcomp j''.2 ⟨hu.1, hu'⟩]
  exact liftDir_comp hV ((analyticOnNhd_pieceChange j j').mono Set.inter_subset_left)
    (fun _ hx => mem_center_iff_pieceChange j j' hx.1) (isOpen_pieceChangeDom j' j'')
    (analyticOnNhd_pieceChange j' j'') (fun _ hx => mem_center_iff_pieceChange j' j'' hx)
    (fun _ hx => chartChange_mem_of_mem ψ hx.1 hx.2) j'.2 j''.2 ⟨hu.1, hu'⟩ hu.2

/-- The transition map lands in the reverse transition domain: `D^{-1}(T u) ≠ 0`, by the cocycle
of the direction quotients through the first piece itself (`D_i^{id} = 1`). -/
theorem transMap_mem {u : Fin n → 𝕜} (hu : u ∈ transDom j j') :
    transMap j j' u ∈ transDom j' j := by
  have h1 : pieceMap j' (transMap j j' u) ∈ pieceChangeDom j' j := by
    rw [pieceMap_transMap hu]
    exact chartChange_mem ψ hu.1
  refine ⟨h1, ?_⟩
  change transDir j' j (transMap j j' u) ≠ 0
  have hS := transDom_subset j j' hu
  have h := transDir_transMap hu (pieceMap_mem_pieceChangeDom_self hS)
  rw [transDir_self hS] at h
  exact right_ne_zero_of_mul_eq_one h.symm

/-- The transition map carries the transition domain towards a third piece into the transition
domain of the second piece towards it. -/
theorem transMap_mem_of_mem {u : Fin n → 𝕜} (hu : u ∈ transDom j j') (hu' : u ∈ transDom j j'') :
    transMap j j' u ∈ transDom j' j'' := by
  have h1 : pieceMap j' (transMap j j' u) ∈ pieceChangeDom j' j'' := by
    rw [pieceMap_transMap hu]
    exact chartChange_mem_of_mem ψ hu.1 hu'.1
  refine ⟨h1, fun h0 => ?_⟩
  have h := transDir_transMap hu hu'.1
  rw [h0, mul_zero] at h
  exact hu'.2 h

/-- The cocycle law of the transition maps: two continuous lifts of the same coordinate change
through the same chart agree (uniqueness of lifts, `eqOn_of_lift_blowUpChartMap`). -/
theorem transMap_transMap {u : Fin n → 𝕜} (hu : u ∈ transDom j j') (hu' : u ∈ transDom j j'') :
    transMap j' j'' (transMap j j' u) = transMap j j'' u := by
  have hN : IsOpen (transDom j j' ∩ transDom j j'') :=
    (isOpen_transDom j j').inter (isOpen_transDom j j'')
  have hmaps : Set.MapsTo (transMap j j') (transDom j j' ∩ transDom j j'') (transDom j' j'') :=
    fun _ hv => transMap_mem_of_mem hv.1 hv.2
  refine eqOn_of_lift_blowUpChartMap (σ := pieceEmb j) (τ := pieceEmb j'') (i := j.2) (k := j''.2)
    (g := pieceChange j j'') hN
    ((analyticOnNhd_transMap j' j'').continuousOn.comp
      ((analyticOnNhd_transMap j j').continuousOn.mono Set.inter_subset_left) hmaps)
    ((analyticOnNhd_transMap j j'').continuousOn.mono Set.inter_subset_right) ?_ ?_ ?_ ⟨hu, hu'⟩
  · rintro v ⟨hv, hv'⟩
    change pieceMap j'' (transMap j' j'' (transMap j j' v)) = pieceChange j j'' (pieceMap j v)
    rw [pieceMap_transMap (transMap_mem_of_mem hv hv'), pieceMap_transMap hv]
    exact chartChange_comp ψ hv.1
  · rintro v ⟨-, hv'⟩
    exact pieceMap_transMap hv'
  · rintro v ⟨-, hv'⟩ hvi hmem
    have h := (mem_center_iff_pieceChange j j'' hv'.1).mpr hmem
    exact hvi ((blowUpChartMap_mem_center_iff (pieceEmb j) v).mp h)

end Laws

end

end BlowUpGlue

end Manifold
