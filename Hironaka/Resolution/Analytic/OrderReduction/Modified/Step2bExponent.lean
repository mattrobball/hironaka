/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bStep
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.DerivTransform
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Dictionary
import Hironaka.Resolution.Analytic.Functor.PullbackTransport
import Hironaka.Resolution.Analytic.OrderReduction.Modified.ColonPrincipal
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bLocal
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bTools
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The exponents after a step of the monomial phase

A step of the monomial phase at the mark `1` blows up the positive locus `Z` of the top member `E^j`
and carries the ideal by the marked transform at the mark `1` (`Step2bStep.lean`). The
decomposition of [Kol07, Definition–Lemma 110] and the remarks after [Wlo09, Theorem 2.0.3] say
what happens to the exponents `a_D = ord_D 𝓘` along the boundary components: the controlled
transform is `(M(𝓘)/𝓘(D)) · N(𝓘)` with the blow-down an isomorphism, so the exponent along the
exceptional divisor `D' = π⁻¹(Z)` (the new last member) is one less than the exponent along `Z`,
the exponents along the other members are unchanged, and the strict transform of `E^j` carries only
its components of exponent `0`. This module proves these facts:

* the stalks: off `Z` the ideal after the step is the pull-back of `𝓘`
  (`stalkIdeal_stepIdeal_of_notMem`, from `birationalTransform_stalkIdeal_of_notMem`); everywhere it
  is the colon of the pulled-back stalk by the pulled-back stalk of `𝓘_Z` (`stalkIdeal_stepIdeal`,
  from `isDivExceptional_birationalTransform` at the mark `1`, the transform (60.1) of
  [Kol07, Definition 60]);
* the ideal sheaves of the members: the new member's is the pull-back of `𝓘_Z`
  (`isIdealSheafOf_exceptionalIdealSheaf`), the other members' are the pull-backs of theirs (the
  identification of the strict transforms in `Step2bTools.lean`,
  `comap_idealSheaf_of_isLocalDiffeomorph`);
* the orders along the members, through the bijective germ map of the blow-up (an isomorphism,
  `isLocalDiffeomorph_blowUpπ_of_codimOne`) and the algebra of `ColonPrincipal.lean` on the prime,
  pairwise non-dividing coordinates of a chart with simple normal crossings
  (`IsSncChartAt.prime_coord`, `IsSncChartAt.not_coord_dvd`): `ordAlong_stepIdeal_inr_add_one`
  (`ord_{D'} 𝓘' + 1 = ord_Z 𝓘`), `ordAlong_stepIdeal_inl_of_ne` (`ord_{E'^k} 𝓘' = ord_{E^k} 𝓘` for
  `k ≠ j`), `ordAlong_stepIdeal_inl_top` (the strict transform of `E^j`:
  `ord_{E'^j} 𝓘' = ord_{E^j} 𝓘 = 0`, the point lying off `Z`).

These feed the termination measure of the phase (`Step2bMeasure.lean`).
-/

@[expose] public section

noncomputable section

open Set Topology Filter
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Hironaka.Manifold

open _root_.Manifold

section SpanSingleton

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- The stalk of the ideal sheaf of a codimension-one submanifold at a point of the submanifold is
the principal ideal of the adapted coordinate (the span form of the stalk on `Fin 1`). -/
theorem _root_.Manifold.IsClosedSubmanifold.stalkIdeal_idealSheaf_eq_span_singleton {Y : Set M}
    (hY : IsClosedSubmanifold ψ Y 1) {a : M} (ha : a ∈ Y) {φ : OpenPartialHomeomorph M E}
    {σ : Fin 1 ↪ Fin n} (hφ : IsAdaptedChart ψ Y φ σ) (haφ : a ∈ φ.source) :
    hY.idealSheaf.stalkIdeal a = Ideal.span {coord E ψ φ hφ.1 haφ (σ 0)} := by
  rw [hY.stalkIdeal_idealSheaf_eq_span ha hφ haφ, Set.range_unique]
  rfl

end SpanSingleton

namespace BMOmod

open _root_.Manifold

open Hironaka.Manifold.BD

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  (T : AnalyticTriple ψ₀ M) (hfin : (activeMembers T).Finite) (hne : (activeMembers T).Nonempty)

/-! ### The stalks of the step ideal -/

/-- Off the exceptional divisor the ideal after the step is the pull-back of `𝓘`
(`birationalTransform_stalkIdeal_of_notMem`). -/
theorem stalkIdeal_stepIdeal_of_notMem {x' : stepStage T hfin hne}
    (hx' : stepπ T hfin hne x' ∉ step2bCenter T hfin hne) :
    (stepIdeal T hfin hne).stalkIdeal x' =
      (T.I.pullback _ (stepπ T hfin hne).contMDiff).stalkIdeal x' :=
  birationalTransform_stalkIdeal_of_notMem (stepCenter T hfin hne)
    (isBlowUp_blowUpπ ψ₀ (stepCenter T hfin hne)) (one_le_ordAlong_step2bCenter T hfin hne) hx'

/-- The transform (60.1) of [Kol07, Definition 60] at the mark `1`
(`isDivExceptional_birationalTransform`): the stalk of the ideal after the step is the colon of the
pulled-back stalk of `𝓘` by the pulled-back stalk of `𝓘_Z`. -/
theorem stalkIdeal_stepIdeal (x' : stepStage T hfin hne) :
    (stepIdeal T hfin hne).stalkIdeal x' =
      ((T.I.pullback _ (stepπ T hfin hne).contMDiff).stalkIdeal x').colon
        ↑(((stepCenter T hfin hne).idealSheaf.pullback _ (stepπ T hfin hne).contMDiff).stalkIdeal
            x') := by
  have h := isDivExceptional_birationalTransform (stepCenter T hfin hne)
    (isBlowUp_blowUpπ ψ₀ (stepCenter T hfin hne)) ⟨T.I, 1⟩
    (one_le_ordAlong_step2bCenter T hfin hne) x'
  simp only [pow_one] at h
  exact h

/-! ### The members' ideal sheaves after the step -/

/-- The ideal sheaf of the new member `D' = π⁻¹(Z)` is the pull-back of `𝓘_Z`
(`isIdealSheafOf_exceptionalIdealSheaf`). -/
theorem idealSheaf_stepFamily_inr :
    ((isSnc_stepFamily T hfin hne).1 (toLex (Sum.inr PUnit.unit))).idealSheaf =
      (stepCenter T hfin hne).idealSheaf.pullback _ (stepπ T hfin hne).contMDiff :=
  (IsIdealSheafOf.eq_idealSheaf _ (isIdealSheafOf_exceptionalIdealSheaf (stepCenter T hfin hne)
    (isBlowUp_blowUpπ ψ₀ (stepCenter T hfin hne)))).symm

/-- For `k ≠ j` the ideal sheaf of the strict transform `E'^k = π⁻¹(E^k)` is the pull-back of
`𝓘_{E^k}` (`stepFamily_hyp_inl_of_ne`, `comap_idealSheaf_of_isLocalDiffeomorph`). -/
theorem idealSheaf_stepFamily_inl_of_ne {k : T.F.ι} (hk : k ≠ topMember T hfin hne) :
    ((isSnc_stepFamily T hfin hne).1 (toLex (Sum.inl k))).idealSheaf =
      (T.isSnc.1 k).idealSheaf.pullback _ (stepπ T hfin hne).contMDiff := by
  rw [comap_idealSheaf_of_isLocalDiffeomorph ψ₀ (stepπ T hfin hne)
    (isLocalDiffeomorph_stepπ T hfin hne) (T.isSnc.1 k)]
  exact IsClosedSubmanifold.idealSheaf_congr _ _ (stepFamily_hyp_inl_of_ne T hfin hne hk)

/-- At a point of the strict transform of the top member (which lies off `Z`), the stalk of its
ideal sheaf is the stalk of the pull-back of `𝓘_{E^j}` (`stalkIdeal_idealSheaf_congr_nhds` on the
open `π⁻¹(Zᶜ)`, where the strict transform is the preimage). -/
theorem stalkIdeal_idealSheaf_stepFamily_inl_top {x' : stepStage T hfin hne}
    (hx' : x' ∈ (stepFamily T hfin hne).hyp (toLex (Sum.inl (topMember T hfin hne)))) :
    ((isSnc_stepFamily T hfin hne).1 (toLex (Sum.inl (topMember T hfin hne)))).idealSheaf.stalkIdeal
        x' =
      ((T.isSnc.1 (topMember T hfin hne)).idealSheaf.pullback _ (stepπ T hfin
          hne).contMDiff).stalkIdeal x' := by
  rw [comap_idealSheaf_of_isLocalDiffeomorph ψ₀ (stepπ T hfin hne)
    (isLocalDiffeomorph_stepπ T hfin hne) (T.isSnc.1 (topMember T hfin hne))]
  refine IsClosedSubmanifold.stalkIdeal_idealSheaf_congr_nhds _ _ hx'
    ((stepCenter T hfin hne).isClosed.isOpen_compl.preimage
      (stepπ T hfin hne).contMDiff.continuous)
    (notMem_step2bCenter_of_mem_stepFamily_top T hfin hne hx')
    (stepFamily_hyp_inl_inter_compl T hfin hne _)

/-! ### The germ map of the blow-down and the transported stalks -/

/-- The germ map of the blow-down of the step at `x'`. -/
abbrev stepGermMap (x' : stepStage T hfin hne) :=
  germMap ⇑(stepπ T hfin hne) (stepπ T hfin hne).contMDiff x'

theorem stepGermMap_bijective (x' : stepStage T hfin hne) :
    Function.Bijective (stepGermMap T hfin hne x') :=
  germMap_bijective_of_isLocalDiffeomorphAt _ _ (isLocalDiffeomorph_stepπ T hfin hne x')

theorem stalkIdeal_comap_stepπ (J : AnalyticManifold.IdealSheaf M) (x' : stepStage T hfin hne) :
    (J.pullback _ (stepπ T hfin hne).contMDiff).stalkIdeal x' =
      Ideal.map (stepGermMap T hfin hne x') (J.stalkIdeal (stepπ T hfin hne x')) :=
  IdealSheaf.stalkIdeal_pullback _ _ J x'

/-! ### The exponent along the new member drops by one -/

/-- **Along the new member `D' = π⁻¹(Z)` the order of the ideal after the step is one less than the
order of `𝓘` along `Z`**: `ord_{D'} 𝓘' + 1 = ord_Z 𝓘` at every point over `Z`
([Kol07, Definition–Lemma 110]; the remarks after [Wlo09, Theorem 2.0.3]). -/
theorem ordAlong_stepIdeal_inr_add_one {x' : stepStage T hfin hne}
    (hx' : stepπ T hfin hne x' ∈ step2bCenter T hfin hne) :
    IdealSheaf.ordAlongIdeal
        ((isSnc_stepFamily T hfin hne).1 (toLex (Sum.inr PUnit.unit))).idealSheaf
        (stepIdeal T hfin hne) x' + 1 =
      IdealSheaf.ordAlongIdeal (stepCenter T hfin hne).idealSheaf T.I (stepπ T hfin hne x') := by
  obtain ⟨φ, σ, hyφ, hφ⟩ := (stepCenter T hfin hne).exists_adaptedChart _ hx'
  set g := coord E ψ₀ φ hφ.1 hyφ (σ 0) with hg
  have hZy : (stepCenter T hfin hne).idealSheaf.stalkIdeal (stepπ T hfin hne x') =
      Ideal.span {g} :=
    (stepCenter T hfin hne).stalkIdeal_idealSheaf_eq_span_singleton hx' hφ hyφ
  have hIy : T.I.stalkIdeal (stepπ T hfin hne x') ≤ Ideal.span {g} := by
    have := (IdealSheaf.le_ordAlongIdeal_iff _ T.I _ 1).mp
      (one_le_ordAlong_step2bCenter T hfin hne _ hx')
    rwa [pow_one, hZy] at this
  have hbij := stepGermMap_bijective T hfin hne x'
  have hdom : IsDomain ((structureSheaf 𝕜 E (stepStage T hfin hne)).presheaf.stalk x') :=
    isDomain_stalk ψ₀ (IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, E)) (n := ω) x')
      (mem_chart_source E x')
  have hg0 : stepGermMap T hfin hne x' g ≠ 0 := fun h =>
    coord_ne_zero hφ.1 hyφ (σ 0) (hbij.1 (h.trans (map_zero _).symm))
  have hexc : ((stepCenter T hfin hne).idealSheaf.pullback _ (stepπ T hfin
      hne).contMDiff).stalkIdeal x' =
        Ideal.span {stepGermMap T hfin hne x' g} := by
    rw [stalkIdeal_comap_stepπ, hZy, Ideal.map_span, Set.image_singleton]
  have hD : ((isSnc_stepFamily T hfin hne).1
      (toLex (Sum.inr PUnit.unit))).idealSheaf.stalkIdeal x' =
        Ideal.span {stepGermMap T hfin hne x' g} := by
    rw [idealSheaf_stepFamily_inr, hexc]
  have hJ : (T.I.pullback _ (stepπ T hfin hne).contMDiff).stalkIdeal x' ≤
      Ideal.span {stepGermMap T hfin hne x' g} := by
    rw [stalkIdeal_comap_stepπ, ← Set.image_singleton, ← Ideal.map_span]
    exact Ideal.map_mono hIy
  have hJ' : (stepIdeal T hfin hne).stalkIdeal x' =
      ((T.I.pullback _ (stepπ T hfin hne).contMDiff).stalkIdeal x').colon
        (Ideal.span {stepGermMap T hfin hne x' g}) := by
    rw [stalkIdeal_stepIdeal, hexc]
  rw [IdealSheaf.ordAlongIdeal_colon_add_one _ _ _ hD hg0 hJ hJ', idealSheaf_stepFamily_inr]
  exact IdealSheaf.ordAlongIdeal_comap_of_isLocalDiffeomorphAt (stepπ T hfin hne) _ T.I
    (isLocalDiffeomorph_stepπ T hfin hne x')

/-! ### The exponents along the other members are unchanged -/

/-- **For a member `k ≠ j`, the order of the ideal after the step along `E'^k = π⁻¹(E^k)` equals the
order of `𝓘` along `E^k`** at the point below (the other exponents are untouched,
[Kol07, Definition–Lemma 110]). Off `Z` the ideal after the step is the pull-back; over `Z` its
stalk is the colon by the coordinate of `Z = E^j` (locally), which does not change the order along
the transversal prime coordinate of `E^k` (`ordAlongIdeal_colon_of_prime`). -/
theorem ordAlong_stepIdeal_inl_of_ne {k : T.F.ι} (hk : k ≠ topMember T hfin hne)
    {x' : stepStage T hfin hne} (hxk : stepπ T hfin hne x' ∈ T.F.hyp k) :
    IdealSheaf.ordAlongIdeal ((isSnc_stepFamily T hfin hne).1 (toLex (Sum.inl k))).idealSheaf
        (stepIdeal T hfin hne) x' =
      IdealSheaf.ordAlongIdeal (T.isSnc.1 k).idealSheaf T.I (stepπ T hfin hne x') := by
  have hbij := stepGermMap_bijective T hfin hne x'
  have hcomap : IdealSheaf.ordAlongIdeal
      ((isSnc_stepFamily T hfin hne).1 (toLex (Sum.inl k))).idealSheaf
        (T.I.pullback _ (stepπ T hfin hne).contMDiff) x' =
      IdealSheaf.ordAlongIdeal (T.isSnc.1 k).idealSheaf T.I (stepπ T hfin hne x') := by
    rw [idealSheaf_stepFamily_inl_of_ne T hfin hne hk]
    exact IdealSheaf.ordAlongIdeal_comap_of_isLocalDiffeomorphAt (stepπ T hfin hne) _ T.I
      (isLocalDiffeomorph_stepπ T hfin hne x')
  by_cases hZ : stepπ T hfin hne x' ∈ step2bCenter T hfin hne
  · -- over `Z`: the snc chart at the point below names the two coordinates
    have hyj : stepπ T hfin hne x' ∈ T.F.hyp (topMember T hfin hne) :=
      step2bCenter_subset T hfin hne hZ
    obtain ⟨φ, cidx, hc⟩ := T.isSnc.2.2 (stepπ T hfin hne x')
    have hyφ : stepπ T hfin hne x' ∈ φ.source := hc.2.1
    set f := coord E ψ₀ φ hc.1 hyφ (cidx ⟨k, hxk⟩) with hf
    set g := coord E ψ₀ φ hc.1 hyφ (cidx ⟨topMember T hfin hne, hyj⟩) with hg
    have hadk : IsAdaptedChart ψ₀ (T.F.hyp k) φ (singleEmb (cidx ⟨k, hxk⟩)) :=
      isAdaptedChart_singleIdx hc.1 fun x hx => hc.2.2.1 ⟨k, hxk⟩ x hx
    have hadj : IsAdaptedChart ψ₀ (T.F.hyp (topMember T hfin hne)) φ
        (singleEmb (cidx ⟨topMember T hfin hne, hyj⟩)) :=
      isAdaptedChart_singleIdx hc.1 fun x hx => hc.2.2.1 ⟨topMember T hfin hne, hyj⟩ x hx
    have hEk : (T.isSnc.1 k).idealSheaf.stalkIdeal (stepπ T hfin hne x') = Ideal.span {f} :=
      (T.isSnc.1 k).stalkIdeal_idealSheaf_eq_span_singleton hxk hadk hyφ
    -- `Z` agrees with `E^j` near the point
    obtain ⟨U, hU, hyU, hsub⟩ := exists_isOpen_inter_subset_positiveLocus T hZ
    have hZy : (stepCenter T hfin hne).idealSheaf.stalkIdeal (stepπ T hfin hne x') =
        Ideal.span {g} := by
      rw [IsClosedSubmanifold.stalkIdeal_idealSheaf_congr_nhds (stepCenter T hfin hne)
        (T.isSnc.1 (topMember T hfin hne)) hZ hU hyU ?_]
      · exact (T.isSnc.1 _).stalkIdeal_idealSheaf_eq_span_singleton hyj hadj hyφ
      · refine Set.Subset.antisymm (Set.inter_subset_inter_left _ (step2bCenter_subset T hfin hne))
          fun z hz => ⟨hsub ⟨hz.2, hz.1⟩, hz.2⟩
    have hIy : T.I.stalkIdeal (stepπ T hfin hne x') ≤ Ideal.span {g} := by
      have := (IdealSheaf.le_ordAlongIdeal_iff _ T.I _ 1).mp
        (one_le_ordAlong_step2bCenter T hfin hne _ hZ)
      rwa [pow_one, hZy] at this
    have hne' : (⟨k, hxk⟩ : {j // stepπ T hfin hne x' ∈ T.F.hyp j}) ≠
        ⟨topMember T hfin hne, hyj⟩ := fun h => hk (congrArg Subtype.val h)
    have hdom : IsDomain ((structureSheaf 𝕜 E (stepStage T hfin hne)).presheaf.stalk x') :=
      isDomain_stalk ψ₀ (IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, E)) (n := ω) x')
        (mem_chart_source E x')
    have hfp : Prime (stepGermMap T hfin hne x' f) :=
      (MulEquiv.prime_iff (RingEquiv.ofBijective _ hbij)).mpr (hc.prime_coord ⟨k, hxk⟩)
    have hfg : ¬ stepGermMap T hfin hne x' f ∣ stepGermMap T hfin hne x' g := by
      rintro ⟨s, hs⟩
      obtain ⟨t, rfl⟩ := hbij.2 s
      exact hc.not_coord_dvd hne' ⟨t, hbij.1 (by rw [map_mul]; exact hs)⟩
    have hexc : ((stepCenter T hfin hne).idealSheaf.pullback _ (stepπ T hfin
        hne).contMDiff).stalkIdeal x' =
        Ideal.span {stepGermMap T hfin hne x' g} := by
      rw [stalkIdeal_comap_stepπ, hZy, Ideal.map_span, Set.image_singleton]
    have hD' : ((isSnc_stepFamily T hfin hne).1 (toLex (Sum.inl k))).idealSheaf.stalkIdeal x' =
        Ideal.span {stepGermMap T hfin hne x' f} := by
      rw [idealSheaf_stepFamily_inl_of_ne T hfin hne hk, stalkIdeal_comap_stepπ, hEk,
        Ideal.map_span, Set.image_singleton]
    have hJ : (T.I.pullback _ (stepπ T hfin hne).contMDiff).stalkIdeal x' ≤
        Ideal.span {stepGermMap T hfin hne x' g} := by
      rw [stalkIdeal_comap_stepπ, ← Set.image_singleton, ← Ideal.map_span]
      exact Ideal.map_mono hIy
    have hJ' : (stepIdeal T hfin hne).stalkIdeal x' =
        ((T.I.pullback _ (stepπ T hfin hne).contMDiff).stalkIdeal x').colon
          (Ideal.span {stepGermMap T hfin hne x' g}) := by
      rw [stalkIdeal_stepIdeal, hexc]
    rw [IdealSheaf.ordAlongIdeal_colon_of_prime _ _ _ hD' hfp hfg hJ hJ']
    exact hcomap
  · rw [IdealSheaf.ordAlongIdeal_congr_stalk _ _ _ _ (stalkIdeal_stepIdeal_of_notMem T hfin hne hZ)]
    exact hcomap

/-- The strict transform of the top member carries only components of exponent `0`: at each of its
points the order of the ideal after the step along it is the order of `𝓘` along `E^j` at the point
below, which lies off the positive locus, so it is `0`. -/
theorem ordAlong_stepIdeal_inl_top {x' : stepStage T hfin hne}
    (hx' : x' ∈ (stepFamily T hfin hne).hyp (toLex (Sum.inl (topMember T hfin hne)))) :
    IdealSheaf.ordAlongIdeal
        ((isSnc_stepFamily T hfin hne).1 (toLex (Sum.inl (topMember T hfin hne)))).idealSheaf
        (stepIdeal T hfin hne) x' =
      IdealSheaf.ordAlongIdeal (T.isSnc.1 (topMember T hfin hne)).idealSheaf T.I
        (stepπ T hfin hne x') := by
  have hZ := notMem_step2bCenter_of_mem_stepFamily_top T hfin hne hx'
  refine IdealSheaf.ordAlongIdeal_eq_of_map (stepGermMap T hfin hne x')
    (stepGermMap_bijective T hfin hne x') _ _ _ _ ?_ ?_
  · rw [stalkIdeal_idealSheaf_stepFamily_inl_top T hfin hne hx', stalkIdeal_comap_stepπ]
  · rw [stalkIdeal_stepIdeal_of_notMem T hfin hne hZ, stalkIdeal_comap_stepπ]

omit [FiniteDimensional 𝕜 E] in
/-- The order of `𝓘` along `E^j` vanishes off the positive locus (the locality of
`Step2bLocal.lean`). -/
theorem ordAlong_eq_zero_of_notMem_positiveLocus {j : T.F.ι} {y : M} (hyj : y ∈ T.F.hyp j)
    (hy : y ∉ positiveLocus T j) :
    IdealSheaf.ordAlongIdeal (T.isSnc.1 j).idealSheaf T.I y = 0 := by
  by_contra h
  apply hy
  rw [mem_positiveLocus_iff_one_le_ordAlong]
  refine ⟨hyj, ?_⟩
  rw [Nat.cast_one, Order.one_le_iff_ne_zero]
  exact h

end BMOmod

end Hironaka.Manifold

end
