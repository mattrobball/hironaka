/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.GluedCharts
public import Hironaka.Manifold.BlowUp.GluedBlowDown
public import Hironaka.Manifold.BlowUp.Transition
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The blow-down off the exceptional divisor

Off the exceptional divisor the blow-down of the glued space is an analytic isomorphism onto
`M ∖ Y`, condition (1) of [BM88, Definition 4.1]: in a piece it reads `φ⁻¹ ∘ ψ⁻¹ ∘ π_i ∘ ψ`, and
`π_i` is a diffeomorphism of `{u_i ≠ 0}` onto `{x_i ≠ 0}` with inverse `blowUpChartInv`, so the
blow-down is a local diffeomorphism at every point off the divisor. It is bijective from the
complement of the divisor onto `M ∖ Y`: surjective since every point of `M` lies under some piece,
injective since two points over the same point of `M ∖ Y` are related by the transition map
(uniqueness of the lift off the centre) and `π_{i'}` is injective on `{u_{i'} ≠ 0}`.

This is one of the clauses showing that the glued space is a blowing-up
(`Hironaka.Manifold.BlowUp.Exists`).
-/

@[expose] public section

open TopologicalSpace Topology
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

namespace BlowUpGlue

noncomputable section

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

/-- The chart map `π_i`, read in `E`, as a partial diffeomorphism of the complement of the
exceptional hyperplane `{u_i = 0}` onto the complement of `{x_i = 0}`, with inverse
`blowUpChartInv`. -/
def blowUpChartMapDiffeo (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {c : ℕ} (σ : Fin c ↪ Fin n) (i : Fin c) :
    PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) E E ω where
  toFun v := ψ.symm (blowUpChartMap σ i (ψ v))
  invFun x := ψ.symm (blowUpChartInv σ i (ψ x))
  source := {v | ψ v (σ i) ≠ 0}
  target := {x | ψ x (σ i) ≠ 0}
  map_source' v hv := by
    change ψ (ψ.symm _) (σ i) ≠ 0
    rw [ψ.apply_symm_apply, blowUpChartMap_apply_scaling]
    exact hv
  map_target' x hx := by
    change ψ (ψ.symm _) (σ i) ≠ 0
    rw [ψ.apply_symm_apply, blowUpChartInv_apply_scaling]
    exact hx
  left_inv' v hv := by
    rw [ψ.apply_symm_apply, blowUpChartInv_blowUpChartMap σ _ hv, ψ.symm_apply_apply]
  right_inv' x hx := by
    rw [ψ.apply_symm_apply, blowUpChartMap_blowUpChartInv σ _ hx, ψ.symm_apply_apply]
  open_source := isOpen_compl_singleton.preimage ((continuous_apply (σ i)).comp ψ.continuous)
  open_target := isOpen_compl_singleton.preimage ((continuous_apply (σ i)).comp ψ.continuous)
  contMDiffOn_toFun := contMDiffOn_iff_contDiffOn.mpr
    (ψ.symm.contDiff.comp ((contDiff_blowUpChartMap σ).comp ψ.contDiff)).contDiffOn
  contMDiffOn_invFun := by
    have hopen : IsOpen {x : E | ψ x (σ i) ≠ 0} :=
      isOpen_compl_singleton.preimage ((continuous_apply (σ i)).comp ψ.continuous)
    refine contMDiffOn_iff_contDiffOn.mpr (AnalyticOnNhd.contDiffOn ?_ hopen.uniqueDiffOn)
    intro x hx
    exact (ψ.symm.toContinuousLinearMap.analyticAt _).comp
      (((analyticOnNhd_blowUpChartInv σ) _ hx).comp (ψ.toContinuousLinearMap.analyticAt x))

variable {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  {Y : Set M} {c : ℕ}

section OffCenter

variable (j : PieceIdx ψ Y c) (hj : (pieceSet j).Nonempty)

/-- The blow-down restricted to the points of a piece off the exceptional hyperplane, as a partial
diffeomorphism onto the points of the chart off the centre: in the chart it is
`φ⁻¹ ∘ ψ⁻¹ ∘ π_i ∘ ψ`, with inverse `(chart)⁻¹ ∘ ψ⁻¹ ∘ blowUpChartInv ∘ ψ ∘ φ`. -/
def offCenterDiffeo : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (Glued ψ Y c) M ω where
  toFun := gluedProj
  invFun a :=
    (gluedChart j hj).symm (ψ.symm (blowUpChartInv (pieceEmb j) j.2 (ψ (pieceChart j a))))
  source := toGlued j '' {u | (u : Fin n → 𝕜) (pieceEmb j j.2) ≠ 0}
  target := (pieceChart j).source ∩ pieceChart j ⁻¹' {x | ψ x (pieceEmb j j.2) ≠ 0}
  map_source' := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨gluedProj_mem_source j u, ?_⟩
    change ψ (pieceChart j (gluedProj (toGlued j u))) (pieceEmb j j.2) ≠ 0
    rw [gluedProj_toGlued, apply_blowDown u.2]
    change blowUpChartMap (pieceEmb j) j.2 (u : Fin n → 𝕜) (pieceEmb j j.2) ≠ 0
    rw [blowUpChartMap_apply_scaling]
    exact hu
  map_target' a ha := by
    obtain ⟨has, hax⟩ := ha
    have hx : ψ (pieceChart j a) (pieceEmb j j.2) ≠ 0 := hax
    have hmem :
        ψ (ψ.symm (blowUpChartInv (pieceEmb j) j.2 (ψ (pieceChart j a)))) ∈ pieceSet j := by
      rw [ψ.apply_symm_apply]
      change blowUpChartMap (pieceEmb j) j.2
        (blowUpChartInv (pieceEmb j) j.2 (ψ (pieceChart j a))) ∈ ψ '' (pieceChart j).target
      rw [blowUpChartMap_blowUpChartInv _ _ hx]
      exact ⟨_, (pieceChart j).map_source has, rfl⟩
    change (gluedChart j hj).symm _ ∈ toGlued j '' _
    rw [gluedChart_symm_apply j hj hmem]
    refine ⟨⟨_, hmem⟩, ?_, rfl⟩
    change ψ (ψ.symm _) (pieceEmb j j.2) ≠ 0
    rw [ψ.apply_symm_apply, blowUpChartInv_apply_scaling]
    exact hx
  left_inv' := by
    rintro _ ⟨u, hu, rfl⟩
    have hu' : (u : Fin n → 𝕜) (pieceEmb j j.2) ≠ 0 := hu
    change (gluedChart j hj).symm
      (ψ.symm (blowUpChartInv (pieceEmb j) j.2 (ψ (pieceChart j (gluedProj (toGlued j u)))))) =
        toGlued j u
    rw [gluedProj_toGlued, apply_blowDown u.2]
    change (gluedChart j hj).symm
      (ψ.symm (blowUpChartInv (pieceEmb j) j.2 (blowUpChartMap (pieceEmb j) j.2 u))) = _
    rw [blowUpChartInv_blowUpChartMap _ _ hu']
    have hmem : ψ (ψ.symm (u : Fin n → 𝕜)) ∈ pieceSet j := by
      rw [ψ.apply_symm_apply]
      exact u.2
    rw [gluedChart_symm_apply j hj hmem]
    congr 1
    exact Subtype.ext (ψ.apply_symm_apply _)
  right_inv' a ha := by
    obtain ⟨has, hax⟩ := ha
    have hx : ψ (pieceChart j a) (pieceEmb j j.2) ≠ 0 := hax
    have hmem :
        ψ (ψ.symm (blowUpChartInv (pieceEmb j) j.2 (ψ (pieceChart j a)))) ∈ pieceSet j := by
      rw [ψ.apply_symm_apply]
      change blowUpChartMap (pieceEmb j) j.2
        (blowUpChartInv (pieceEmb j) j.2 (ψ (pieceChart j a))) ∈ ψ '' (pieceChart j).target
      rw [blowUpChartMap_blowUpChartInv _ _ hx]
      exact ⟨_, (pieceChart j).map_source has, rfl⟩
    change gluedProj ((gluedChart j hj).symm _) = a
    rw [gluedChart_symm_apply j hj hmem, gluedProj_toGlued]
    change (pieceChart j).symm (ψ.symm (blowUpChartMap (pieceEmb j) j.2
      (ψ (ψ.symm (blowUpChartInv (pieceEmb j) j.2 (ψ (pieceChart j a))))))) = a
    rw [ψ.apply_symm_apply, blowUpChartMap_blowUpChartInv _ _ hx, ψ.symm_apply_apply,
      (pieceChart j).left_inv has]
  open_source := (isOpenEmbedding_toGlued j).isOpenMap _
    (isOpen_compl_singleton.preimage ((continuous_apply _).comp continuous_subtype_val))
  open_target := (pieceChart j).isOpen_inter_preimage
    (isOpen_compl_singleton.preimage ((continuous_apply _).comp ψ.continuous))
  contMDiffOn_toFun := contMDiff_gluedProj.contMDiffOn
  contMDiffOn_invFun := by
    have h1 : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω (pieceChart j) (pieceChart j).source :=
      contMDiffOn_of_mem_maximalAtlas (mem_maximalAtlas_piece j)
    have h2 : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω
        (fun x : E => ψ.symm (blowUpChartInv (pieceEmb j) j.2 (ψ x)))
        {x | ψ x (pieceEmb j j.2) ≠ 0} :=
      (blowUpChartMapDiffeo ψ (pieceEmb j) j.2).contMDiffOn_invFun
    have h3 : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω (gluedChart j hj).symm (gluedChart j hj).target :=
      contMDiffOn_symm_of_mem_maximalAtlas (gluedChart_mem_maximalAtlas j hj)
    have h4 : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω
        ((gluedChart j hj).symm ∘ (fun x : E => ψ.symm (blowUpChartInv (pieceEmb j) j.2 (ψ x))) ∘
          pieceChart j)
        ((pieceChart j).source ∩ pieceChart j ⁻¹' {x | ψ x (pieceEmb j j.2) ≠ 0}) := by
      refine h3.comp (h2.comp (h1.mono Set.inter_subset_left) fun a ha => ha.2) ?_
      rintro a ⟨has, hax⟩
      have hx : ψ (pieceChart j a) (pieceEmb j j.2) ≠ 0 := hax
      change ψ (ψ.symm (blowUpChartInv (pieceEmb j) j.2 (ψ (pieceChart j a)))) ∈ pieceSet j
      rw [ψ.apply_symm_apply]
      change blowUpChartMap (pieceEmb j) j.2
        (blowUpChartInv (pieceEmb j) j.2 (ψ (pieceChart j a))) ∈ ψ '' (pieceChart j).target
      rw [blowUpChartMap_blowUpChartInv _ _ hx]
      exact ⟨_, (pieceChart j).map_source has, rfl⟩
    exact h4

include hj in
/-- The blow-down is a local diffeomorphism at every point of a piece off the exceptional
hyperplane. -/
theorem isLocalDiffeomorphAt_gluedProj (u : pieceSet j)
    (hu : (u : Fin n → 𝕜) (pieceEmb j j.2) ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω (gluedProj : Glued ψ Y c → M) (toGlued j u) :=
  (offCenterDiffeo j hj).isLocalDiffeomorphAt _ _ _ ⟨u, hu, rfl⟩

end OffCenter

/-- The blow-down is a local diffeomorphism off the exceptional divisor (towards condition (1) of
[BM88, Definition 4.1]). -/
theorem isLocalDiffeomorphOn_gluedProj :
    IsLocalDiffeomorphOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω (gluedProj : Glued ψ Y c → M) (gluedProj ⁻¹' Yᶜ) := by
  rintro ⟨p, hp⟩
  obtain ⟨j, u, rfl⟩ := toGlued_jointly_surjective p
  have hu : (u : Fin n → 𝕜) (pieceEmb j j.2) ≠ 0 := (gluedProj_notMem_iff j u).mp hp
  exact isLocalDiffeomorphAt_gluedProj j ⟨u, u.2⟩ u hu

/-- Two points of pieces off the exceptional divisor over the same point of `M` coincide. -/
theorem toGlued_eq_of_gluedProj_eq {j j' : PieceIdx ψ Y c} (u : pieceSet j) (u' : pieceSet j')
    (hu' : (u' : Fin n → 𝕜) (pieceEmb j' j'.2) ≠ 0) (hpq : blowDown j u = blowDown j' u') :
    toGlued j u = toGlued j' u' := by
  have hx : pieceMap j u ∈ pieceChangeDom j j' :=
    (pieceMap_mem_pieceChangeDom_iff u.2).mpr (by rw [hpq]; exact blowDown_mem_source u'.2)
  have hg : pieceChange j j' (pieceMap j u) = blowUpChartMap (pieceEmb j') j'.2 u' :=
    pieceChange_pieceMap_eq u u' hpq
  have hmul := mul_liftDir (fun _ hx => mem_center_iff_pieceChange j j' hx) j'.2 hx
  rw [hg, blowUpChartMap_apply_scaling] at hmul
  have hD : transDir j j' u ≠ 0 := by
    intro h
    change liftDir (pieceEmb j) (pieceEmb j') j.2 (pieceChange j j') j'.2 u = 0 at h
    rw [h, mul_zero] at hmul
    exact hu' hmul.symm
  have hdom : (u : Fin n → 𝕜) ∈ transDom j j' := ⟨hx, hD⟩
  have hk : transMap j j' u (pieceEmb j' j'.2) ≠ 0 := by
    rw [transMap, liftMap_apply_k, hmul]
    exact hu'
  have heq : pieceMap j' (transMap j j' u) = pieceMap j' u' := by
    rw [pieceMap_transMap hdom, hg]
  have h := blowUpChartMap_injOn (pieceEmb j') hk hu' heq
  rw [← toGlued_transMap hdom]
  congr 1
  exact Subtype.ext h

section Bijective

variable [IsManifold 𝓘(𝕜, E) ω M] (hY : IsClosedSubmanifold ψ Y c) (σ₀ : Fin c ↪ Fin n)
  (i₀ : Fin c)
include hY σ₀ i₀

/-- The blow-down is a bijection from the complement of the exceptional divisor onto `M ∖ Y`
(condition (1) of [BM88, Definition 4.1]). -/
theorem bijOn_gluedProj : Set.BijOn (gluedProj : Glued ψ Y c → M) (gluedProj ⁻¹' Yᶜ) Yᶜ := by
  refine ⟨fun _ hp => hp, ?_, ?_⟩
  · intro p _ q hq hpq
    obtain ⟨j, u, rfl⟩ := toGlued_jointly_surjective p
    obtain ⟨j', u', rfl⟩ := toGlued_jointly_surjective q
    have hu' : (u' : Fin n → 𝕜) (pieceEmb j' j'.2) ≠ 0 := (gluedProj_notMem_iff j' u').mp hq
    rw [gluedProj_toGlued, gluedProj_toGlued] at hpq
    exact toGlued_eq_of_gluedProj_eq u u' hu' hpq
  · intro a ha
    obtain ⟨j, u, hu⟩ := exists_blowDown_eq hY σ₀ i₀ a
    refine ⟨toGlued j u, ?_, by rw [gluedProj_toGlued, hu]⟩
    change gluedProj (toGlued j u) ∈ Yᶜ
    rw [gluedProj_toGlued, hu]
    exact ha

end Bijective

end

end BlowUpGlue

end Manifold
