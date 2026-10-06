/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.GluedCharts
import Hironaka.Manifold.BlowUp.Transition
import Hironaka.Manifold.Submanifold
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The blow-down of the glued space and the blow-up charts

For the glued space `Glued ψ Y c` and its blow-down `gluedProj`:

* pieces over the same adapted chart are glued by the transition maps `T_ik` of the local model,
  and a point of a piece over the chart `φ'` lies in the transition domain towards some piece
  over `φ'` (the direction vector of the lift is nonzero);
* a point of a piece lies over the centre exactly when its scaling coordinate vanishes;
* every point of `M` lies under some piece (given adapted charts at every point: those of the
  closed submanifold `Y` at the points of `Y`, the translated charts of
  `Hironaka.Manifold.BlowUp.Atlas` off `Y`), so the blow-down is surjective;
* the blow-down is analytic (in the chart of a piece it is `φ⁻¹ ∘ ψ⁻¹ ∘ π_i ∘ ψ`);
* the chart of a piece is a blow-up chart in the sense of `IsBlowUpChart`, condition (2) of
  [BM88, Definition 4.1] in coordinates, and every adapted chart and every index has one, the
  blow-up charts over an adapted chart covering the preimage of its source (the clauses
  `IsBlowUp.exists_chart` and `IsBlowUp.cover`).

Together with `Hironaka.Manifold.BlowUp.GluedOffCenter` (condition (1)) and
`Hironaka.Manifold.BlowUp.GluedTopology` (Hausdorff, second countable, proper), this shows
that the glued space is a blowing-up of `M` with centre `Y` (`Hironaka.Manifold.BlowUp.Exists`).
-/

public section

open TopologicalSpace Topology
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

namespace BlowUpGlue

noncomputable section

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M}
  {c : ℕ}

/-! ### Pieces over the same chart -/

section SameChart

variable (s : Shrink.{u} (AdaptedChart ψ Y c)) (k k' : Fin c)

/-- Two pieces over the same adapted chart have the same chart. -/
theorem pieceChart_mk : pieceChart (s, k) = pieceChart (s, k') := rfl

/-- Two pieces over the same adapted chart have the same block indices. -/
theorem pieceEmb_mk : pieceEmb (s, k) = pieceEmb (s, k') := rfl

/-- Between two pieces over the same chart the direction quotient is the ratio coordinate. -/
theorem transDir_same {u : Fin n → 𝕜} (hu : u ∈ pieceSet (s, k)) (hkk' : k' ≠ k) :
    transDir (s, k) (s, k') u = u (pieceEmb (s, k) k') :=
  liftDir_of_eqOn_id (isOpen_pieceChangeDom (s, k) (s, k')) (fun _ hx => chartChange_self ψ hx)
    hkk' (pieceMap_mem_pieceChangeDom_self hu)

/-- The transition domain between two pieces over the same chart is `{u_{k'} ≠ 0}` inside the piece
set. -/
theorem mem_transDom_same {u : Fin n → 𝕜} (hkk' : k' ≠ k) :
    u ∈ transDom (s, k) (s, k') ↔ u ∈ pieceSet (s, k) ∧ u (pieceEmb (s, k) k') ≠ 0 := by
  constructor
  · intro hu
    have hS := transDom_subset _ _ hu
    refine ⟨hS, ?_⟩
    have h : transDir (s, k) (s, k') u ≠ 0 := hu.2
    rwa [transDir_same s k k' hS hkk'] at h
  · rintro ⟨hS, hne⟩
    refine ⟨pieceMap_mem_pieceChangeDom_self hS, ?_⟩
    change transDir (s, k) (s, k') u ≠ 0
    rw [transDir_same s k k' hS hkk']
    exact hne

/-- Between two pieces over the same chart the transition map is the transition map `T_ik` of the
local model. -/
theorem transMap_same {u : Fin n → 𝕜} (hu : u ∈ transDom (s, k) (s, k')) :
    transMap (s, k) (s, k') u = blowUpTransition (pieceEmb (s, k)) k k' u :=
  liftMap_eq_blowUpTransition (isOpen_pieceChangeDom (s, k) (s, k'))
    (fun _ hx => chartChange_self ψ hx) k' hu.1 hu.2

end SameChart

/-- A point of a piece over the chart of another piece lies in the transition domain towards some
piece over that chart: the direction vector of the lift is nonzero (`exists_liftDir_ne_zero`). -/
theorem exists_mem_transDom {j : PieceIdx ψ Y c} {u : Fin n → 𝕜} (hu : u ∈ pieceSet j)
    (s : Shrink.{u} (AdaptedChart ψ Y c)) (hs : blowDown j u ∈ (pieceChart (s, j.2)).source) :
    ∃ k, u ∈ transDom j (s, k) := by
  have hx : pieceMap j u ∈ pieceChangeDom j (s, j.2) := (pieceMap_mem_pieceChangeDom_iff hu).mpr hs
  obtain ⟨k, hk⟩ := exists_liftDir_ne_zero (isOpen_pieceChangeDom j (s, j.2))
    (analyticOnNhd_pieceChange j (s, j.2)) (fun _ hx => mem_center_iff_pieceChange j (s, j.2) hx)
    (isOpen_pieceChangeDom (s, j.2) j) (bijOn_chartChange ψ) (analyticOnNhd_pieceChange (s, j.2) j)
    (fun _ hx => chartChange_chartChange ψ hx) hx
  exact ⟨k, hx, hk⟩

/-- Every point of the glued space over the chart of a piece lies in the image of a piece over
that chart. -/
theorem exists_toGlued_eq (p : Glued ψ Y c) (s : Shrink.{u} (AdaptedChart ψ Y c)) {k₀ : Fin c}
    (hs : gluedProj p ∈ (pieceChart (s, k₀)).source) :
    ∃ (k : Fin c) (w : pieceSet (s, k)), toGlued (s, k) w = p := by
  have hs' : blowDown (pieceOf p) (pieceElt p) ∈ (pieceChart (s, (pieceOf p).2)).source := by
    rw [← gluedProj_toGlued, toGlued_pieceElt]
    exact hs
  obtain ⟨k, hk⟩ := exists_mem_transDom (pieceElt p).2 s hs'
  exact ⟨k, ⟨_, transMap_mem_pieceSet hk⟩, (toGlued_transMap hk).trans (toGlued_pieceElt p)⟩

/-! ### The blow-down and the centre -/

/-- A point of a piece lies over the centre exactly when its scaling coordinate vanishes. -/
theorem gluedProj_mem_iff (j : PieceIdx ψ Y c) (u : pieceSet j) :
    gluedProj (toGlued j u) ∈ Y ↔ (u : Fin n → 𝕜) (pieceEmb j j.2) = 0 := by
  rw [gluedProj_toGlued]
  have h := (isAdaptedChart_piece j).2 _ (blowDown_mem_source u.2)
  rw [apply_blowDown u.2] at h
  rw [h]
  exact blowUpChartMap_mem_center_iff (pieceEmb j) u.1

/-- A point of piece `j` blows down off the centre iff its scaling coordinate is nonzero. -/
theorem gluedProj_notMem_iff (j : PieceIdx ψ Y c) (u : pieceSet j) :
    gluedProj (toGlued j u) ∉ Y ↔ (u : Fin n → 𝕜) (pieceEmb j j.2) ≠ 0 :=
  not_congr (gluedProj_mem_iff j u)

/-- The coordinate change between two pieces carries the chart map of a point to the chart map
of any point of the other piece over the same point of `M`. -/
theorem pieceChange_pieceMap_eq {j j' : PieceIdx ψ Y c} (u : pieceSet j) (u' : pieceSet j')
    (h : blowDown j u = blowDown j' u') : pieceChange j j' (pieceMap j u) = pieceMap j' u' := by
  change ψ (pieceChart j' ((pieceChart j).symm (ψ.symm (pieceMap j u)))) = _
  rw [← blowDown, h, apply_blowDown u'.2]

/-! ### Surjectivity of the blow-down -/

section Surjective

variable [IsManifold 𝓘(𝕜, E) ω M] (hY : IsClosedSubmanifold ψ Y c) (σ₀ : Fin c ↪ Fin n)
  (i₀ : Fin c)
include hY σ₀ i₀

/-- Every point of `M` lies in the chart of a piece: an adapted chart of the closed submanifold at
a point of `Y`, a translated chart (`exists_isAdaptedChart_of_notMem`) off `Y`. -/
theorem exists_piece_mem_source (a : M) :
    ∃ s : Shrink.{u} (AdaptedChart ψ Y c), a ∈ (pieceChart (s, i₀)).source := by
  by_cases ha : a ∈ Y
  · obtain ⟨j, h1, -, -⟩ := exists_piece (hY.isAdaptedChart_adaptedChartAt ⟨a, ha⟩) i₀
    refine ⟨j.1, ?_⟩
    rw [pieceChart_mk j.1 i₀ j.2, h1]
    exact hY.mem_source_adaptedChartAt ⟨a, ha⟩
  · obtain ⟨φ, haφ, hφ⟩ := exists_isAdaptedChart_of_notMem ψ hY σ₀ i₀ ha
    obtain ⟨j, h1, -, -⟩ := exists_piece hφ i₀
    refine ⟨j.1, ?_⟩
    rw [pieceChart_mk j.1 i₀ j.2, h1]
    exact haφ

/-- Every point of `M` lies under some piece. -/
theorem exists_blowDown_eq (a : M) :
    ∃ (j : PieceIdx ψ Y c) (u : pieceSet j), blowDown j u = a := by
  obtain ⟨s, hs⟩ := exists_piece_mem_source hY σ₀ i₀ a
  set x := ψ (pieceChart (s, i₀) a) with hx_def
  have hxt : ψ.symm x ∈ (pieceChart (s, i₀)).target := by
    rw [hx_def, ψ.symm_apply_apply]
    exact (pieceChart (s, i₀)).map_source hs
  by_cases hx : x ∈ blowUpCenter (pieceEmb (s, i₀))
  · refine ⟨(s, i₀), ⟨x, ?_⟩, ?_⟩
    · change blowUpChartMap (pieceEmb (s, i₀)) i₀ x ∈ ψ '' _
      rw [blowUpChartMap_of_mem_center hx]
      exact ⟨_, hxt, ψ.apply_symm_apply x⟩
    · change (pieceChart (s, i₀)).symm (ψ.symm (blowUpChartMap (pieceEmb (s, i₀)) i₀ x)) = a
      rw [blowUpChartMap_of_mem_center hx, hx_def, ψ.symm_apply_apply,
        (pieceChart (s, i₀)).left_inv hs]
  · obtain ⟨i, u, hu, -⟩ := exists_mem_box_of_ne_center (pieceEmb (s, i₀)) x hx
    refine ⟨(s, i), ⟨u, ?_⟩, ?_⟩
    · change blowUpChartMap (pieceEmb (s, i₀)) i u ∈ ψ '' (pieceChart (s, i₀)).target
      rw [hu]
      exact ⟨_, hxt, ψ.apply_symm_apply x⟩
    · change (pieceChart (s, i₀)).symm (ψ.symm (blowUpChartMap (pieceEmb (s, i₀)) i u)) = a
      rw [hu, hx_def, ψ.symm_apply_apply, (pieceChart (s, i₀)).left_inv hs]

/-- The blow-down of the glued space is onto `M`. -/
theorem gluedProj_surjective : Function.Surjective (gluedProj : Glued ψ Y c → M) := by
  intro a
  obtain ⟨j, u, h⟩ := exists_blowDown_eq hY σ₀ i₀ a
  exact ⟨toGlued j u, by rw [gluedProj_toGlued, h]⟩

/-- The glued space is nonempty when `M` is. -/
theorem nonempty_glued [Nonempty M] : Nonempty (Glued ψ Y c) :=
  (gluedProj_surjective hY σ₀ i₀).nonempty

end Surjective

/-! ### Analyticity of the blow-down -/

theorem contMDiffOn_gluedProj_range (j : PieceIdx ψ Y c) (hj : (pieceSet j).Nonempty) :
    ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω (gluedProj : Glued ψ Y c → M) (Set.range (toGlued j)) := by
  have h1 : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω (gluedChart j hj) (Set.range (toGlued j)) :=
    contMDiffOn_of_mem_maximalAtlas (gluedChart_mem_maximalAtlas j hj)
  have h2 : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω (fun v : E => ψ.symm (pieceMap j (ψ v))) :=
    contMDiff_iff_contDiff.mpr (ψ.symm.contDiff.comp ((contDiff_blowUpChartMap _).comp ψ.contDiff))
  have h3 : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω (pieceChart j).symm (pieceChart j).target :=
    contMDiffOn_symm_of_mem_maximalAtlas (mem_maximalAtlas_piece j)
  have h4 : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      ((pieceChart j).symm ∘ (fun v : E => ψ.symm (pieceMap j (ψ v))) ∘ gluedChart j hj)
      (Set.range (toGlued j)) := by
    refine h3.comp (h2.comp_contMDiffOn h1) ?_
    rintro _ ⟨u, rfl⟩
    change ψ.symm (pieceMap j (ψ (gluedChart j hj (toGlued j u)))) ∈ (pieceChart j).target
    rw [gluedChart_toGlued, ψ.apply_symm_apply]
    exact symm_pieceMap_mem_target u.2
  refine h4.congr ?_
  rintro _ ⟨u, rfl⟩
  change gluedProj (toGlued j u) =
    (pieceChart j).symm (ψ.symm (pieceMap j (ψ (gluedChart j hj (toGlued j u)))))
  rw [gluedProj_toGlued, gluedChart_toGlued, ψ.apply_symm_apply, blowDown]

/-- The blow-down is analytic. -/
theorem contMDiff_gluedProj : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω (gluedProj : Glued ψ Y c → M) := by
  intro p
  have hp : Set.range (toGlued (pieceOf p)) ∈ 𝓝 p :=
    (isOpenEmbedding_toGlued _).isOpen_range.mem_nhds ⟨pieceElt p, toGlued_pieceElt p⟩
  exact (contMDiffOn_gluedProj_range (pieceOf p) (pieceSet_pieceOf_nonempty p)).contMDiffAt hp

/-! ### Condition (2) of the definition: the blow-up charts -/

/-- The chart of a piece is a blow-up chart of its index over its adapted chart. -/
theorem isBlowUpChart_gluedChart (j : PieceIdx ψ Y c) (hj : (pieceSet j).Nonempty) :
    IsBlowUpChart ψ gluedProj (pieceChart j) (pieceEmb j) j.2 (gluedChart j hj) where
  mem_maximalAtlas := gluedChart_mem_maximalAtlas j hj
  source_subset := by
    rintro _ ⟨u, rfl⟩
    exact gluedProj_mem_source j u
  mem_target_iff _ := Iff.rfl
  comm := by
    rintro _ ⟨u, rfl⟩
    rw [gluedProj_toGlued, apply_blowDown u.2, gluedChart_toGlued, ψ.apply_symm_apply]

/-- A chart of the maximal atlas with empty source and target. -/
theorem exists_mem_maximalAtlas_source_empty [Nonempty (Glued ψ Y c)] :
    ∃ Φ : OpenPartialHomeomorph (Glued ψ Y c) E,
      Φ ∈ maximalAtlas 𝓘(𝕜, E) ω (Glued ψ Y c) ∧ Φ.source = ∅ ∧ Φ.target = ∅ := by
  obtain ⟨p⟩ := ‹Nonempty (Glued ψ Y c)›
  refine ⟨(chartAt E p).restr ∅,
    restr_mem_maximalAtlas _ (IsManifold.chart_mem_maximalAtlas p) isOpen_empty, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restr_source' _ _ isOpen_empty, Set.inter_empty]
  · rw [OpenPartialHomeomorph.restr_toPartialEquiv, PartialEquiv.restr_target, interior_empty,
      Set.preimage_empty, Set.inter_empty]

/-- Condition (2) of [BM88, Definition 4.1]: every adapted chart and every index has a blow-up
chart. -/
theorem exists_isBlowUpChart [Nonempty (Glued ψ Y c)] {φ : OpenPartialHomeomorph M E}
    {σ : Fin c ↪ Fin n} (hφ : IsAdaptedChart ψ Y φ σ) (i : Fin c) :
    ∃ Φ : OpenPartialHomeomorph (Glued ψ Y c) E, IsBlowUpChart ψ gluedProj φ σ i Φ := by
  obtain ⟨j, rfl, rfl, rfl⟩ := exists_piece hφ i
  by_cases hj : (pieceSet j).Nonempty
  · exact ⟨_, isBlowUpChart_gluedChart j hj⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hj
    obtain ⟨Φ, hΦ, hs, ht⟩ := exists_mem_maximalAtlas_source_empty (ψ := ψ) (Y := Y) (c := c)
    refine ⟨Φ, hΦ, by rw [hs]; exact Set.empty_subset _, fun v => ?_, ?_⟩
    · rw [ht]
      refine ⟨fun h => h.elim, fun h => ?_⟩
      have h' : ψ v ∈ pieceSet j := h
      rw [hj] at h'
      exact h'.elim
    · rw [hs]
      intro p hp
      exact hp.elim

/-- Condition (2) of [BM88, Definition 4.1]: the blow-up charts over an adapted chart cover the
preimage of its source. -/
theorem exists_isBlowUpChart_mem_source {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n}
    (hφ : IsAdaptedChart ψ Y φ σ) (p : Glued ψ Y c) (hp : gluedProj p ∈ φ.source) :
    ∃ (i : Fin c) (Φ : OpenPartialHomeomorph (Glued ψ Y c) E),
      IsBlowUpChart ψ gluedProj φ σ i Φ ∧ p ∈ Φ.source := by
  obtain ⟨j₀, h1, h2, -⟩ := exists_piece hφ (pieceOf p).2
  have hs' : blowDown (pieceOf p) (pieceElt p) ∈ (pieceChart (j₀.1, (pieceOf p).2)).source := by
    rw [← gluedProj_toGlued, toGlued_pieceElt, pieceChart_mk j₀.1 (pieceOf p).2 j₀.2, h1]
    exact hp
  obtain ⟨k, hk⟩ := exists_mem_transDom (pieceElt p).2 j₀.1 hs'
  have hne : (pieceSet (j₀.1, k)).Nonempty := ⟨_, transMap_mem_pieceSet hk⟩
  refine ⟨k, gluedChart (j₀.1, k) hne, ?_, ?_⟩
  · have h := isBlowUpChart_gluedChart (j₀.1, k) hne
    rwa [pieceChart_mk j₀.1 k j₀.2, h1, pieceEmb_mk j₀.1 k j₀.2, h2] at h
  · exact ⟨_, (toGlued_transMap hk).trans (toGlued_pieceElt p)⟩

end

end BlowUpGlue

end Manifold
