/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bStep
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.Snc.TotalTransform
import Hironaka.Manifold.Submanifold.Charts
import Hironaka.Manifold.Submanifold.Components
import Hironaka.Resolution.Analytic.OrderReduction.FirstStep
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Tools for the exponents of a step of the monomial phase

Facts used by `Step2bExponent.lean`:

* the stalk of the ideal sheaf of a closed submanifold at a point depends only on the submanifold
  near the point (`IsClosedSubmanifold.stalkIdeal_idealSheaf_congr_nhds`, by the span form of the
  stalk on an adapted chart shrunk to the neighbourhood);
* the order along a centre transports along a bijective ring homomorphism of stalks carrying both
  ideals (`IdealSheaf.ordAlongIdeal_eq_of_map`, the pointwise form of
  `ordAlongIdeal_pullback_diffeomorph`);
* the blow-down of a step is a local analytic isomorphism (`isLocalDiffeomorph_stepπ`): the centre
  has codimension one (`exists_diffeomorph_of_codim_one`; see the remarks after
  [Wlo09, Theorem 2.0.3]);
* the centre `Z` is open in its member (a union of components of `E^j`), so the strict transform of
  the top member lies over `E^j ∖ Z` (`notMem_step2bCenter_of_mem_stepFamily_top`);
* two distinct members of a simple normal crossing divisor through a point: the point lies in the
  closure of the first minus the second (`mem_closure_hyp_diff_hyp_of_ne`, along the coordinate
  line of the chart; the transversality of [Kol07, Definition 24] in the form the strict transform
  needs), so the strict transform of every other member under the blow-up is its whole preimage
  (`stepFamily_hyp_inl_of_ne`; the blow-up is an open map), and every strict transform agrees with
  the preimage off the exceptional divisor (`stepFamily_hyp_inl_inter_compl`,
  `mem_strictTransform_iff_of_notMem`).
-/

public section

noncomputable section

open Set Topology Filter
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Hironaka.Manifold

open _root_.Manifold

section General

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- The stalk at `a` of the ideal sheaf of a closed submanifold depends only on the submanifold near
`a`: two closed submanifolds of the same codimension which agree on an open neighbourhood of `a`
have the same stalk ideal there (the span form on an adapted chart shrunk to the neighbourhood is
adapted to both). -/
theorem _root_.Manifold.IsClosedSubmanifold.stalkIdeal_idealSheaf_congr_nhds {Y Y' : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ Y c) (hY' : IsClosedSubmanifold ψ Y' c) {a : M} (ha : a ∈ Y)
    {U : Set M} (hU : IsOpen U) (haU : a ∈ U) (hYY' : Y ∩ U = Y' ∩ U) :
    hY.idealSheaf.stalkIdeal a = hY'.idealSheaf.stalkIdeal a := by
  obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart a ha
  have haU' : a ∈ (φ.restrOpen U hU).source := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨haφ, haU⟩
  have hmem : φ.restrOpen U hU ∈ maximalAtlas 𝓘(𝕜, E) ω M := by
    rw [OpenPartialHomeomorph.restrOpen_eq_restr]
    exact restr_mem_maximalAtlas _ hφ.1 hU
  have hφU : IsAdaptedChart ψ Y (φ.restrOpen U hU) σ := ⟨hmem, fun x hx => by
    rw [OpenPartialHomeomorph.restrOpen_source] at hx
    exact hφ.2 x hx.1⟩
  have hφU' : IsAdaptedChart ψ Y' (φ.restrOpen U hU) σ := ⟨hmem, fun x hx => by
    rw [OpenPartialHomeomorph.restrOpen_source] at hx
    have h1 : x ∈ Y ↔ x ∈ Y' :=
      ⟨fun h => (hYY'.subset ⟨h, hx.2⟩).1, fun h => (hYY'.symm.subset ⟨h, hx.2⟩).1⟩
    rw [← h1]
    exact hφ.2 x hx.1⟩
  have ha' : a ∈ Y' := (hYY'.subset ⟨ha, haU⟩).1
  rw [hY.stalkIdeal_idealSheaf_eq_span ha hφU haU', hY'.stalkIdeal_idealSheaf_eq_span ha' hφU' haU']

end General

/-- The order of `J` along `D` transports along a bijective ring homomorphism of stalks carrying
both stalk ideals: inclusions and powers of ideals are preserved by `Ideal.map` along a bijection
(the pointwise form of `ordAlongIdeal_pullback_diffeomorph`). -/
theorem _root_.Manifold.IdealSheaf.ordAlongIdeal_eq_of_map {X X' : TopCat}
    {𝒪 : TopCat.Sheaf CommRingCat X}
    {𝒪' : TopCat.Sheaf CommRingCat X'} {a : X} {a' : X'}
    (f : 𝒪.presheaf.stalk a →+* 𝒪'.presheaf.stalk a') (hf : Function.Bijective f)
    (D J : IdealSheaf 𝒪) (D' J' : IdealSheaf 𝒪')
    (hD : D'.stalkIdeal a' = Ideal.map f (D.stalkIdeal a))
    (hJ : J'.stalkIdeal a' = Ideal.map f (J.stalkIdeal a)) :
    IdealSheaf.ordAlongIdeal D' J' a' = IdealSheaf.ordAlongIdeal D J a := by
  have hiff : ∀ A C : Ideal (𝒪.presheaf.stalk a), Ideal.map f A ≤ Ideal.map f C ↔ A ≤ C :=
    fun A C => by rw [Ideal.map_le_iff_le_comap, Ideal.comap_map_of_bijective _ hf]
  simp only [IdealSheaf.ordAlongIdeal, hD, hJ]
  refine iSup_congr fun p => ?_
  rw [← Ideal.map_pow]
  exact iSup_congr_Prop (hiff _ _) fun _ => rfl

namespace BMOmod

open _root_.Manifold

open Hironaka.Manifold.BD

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  (T : AnalyticTriple ψ₀ M)

/-! ### The positive locus is open in its member -/

omit [FiniteDimensional 𝕜 E] in
/-- The positive locus is open in its member: near each of its points the member lies in the
component of the point (`exists_adaptedChart_source_inter_subset`), which lies in the positive locus
(`connectedComponentIn_subset_Zminus1`). -/
theorem exists_isOpen_inter_subset_positiveLocus {j : T.F.ι} {x : M}
    (hx : x ∈ positiveLocus T j) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ∩ T.F.hyp j ⊆ positiveLocus T j := by
  obtain ⟨φ, σ, hxφ, -, hsub⟩ := (T.isSnc.1 j).exists_adaptedChart_source_inter_subset hx.1
  exact ⟨φ.source, φ.open_source, hxφ,
    fun y hy => connectedComponentIn_subset_Zminus1 hx (hsub hy)⟩

/-! ### Two members through a point: the closure of the difference -/

omit [FiniteDimensional 𝕜 E] in
/-- For two distinct members `E^k`, `E^j` of the simple normal crossing divisor through `y`, `y`
lies in the closure of `E^k ∖ E^j` [Kol07, Definition 24]: in a chart at `y` the points
`φ⁻¹(φ y + ε e_j)` (`e_j` the coordinate direction of `E^j`) lie on `E^k`, off `E^j` for `ε ≠ 0`,
and tend to `y`. -/
theorem mem_closure_hyp_diff_hyp_of_ne {j k : T.F.ι} (hjk : k ≠ j) {y : M}
    (hyk : y ∈ T.F.hyp k) (hyj : y ∈ T.F.hyp j) : y ∈ closure (T.F.hyp k \ T.F.hyp j) := by
  obtain ⟨φ, cidx, hc⟩ := T.isSnc.2.2 y
  have hyφ : y ∈ φ.source := hc.2.1
  set e : E := ψ₀.symm (Pi.single (cidx ⟨j, hyj⟩) (1 : 𝕜)) with he
  have hne : cidx ⟨k, hyk⟩ ≠ cidx ⟨j, hyj⟩ :=
    fun h => hjk (congrArg Subtype.val (hc.2.2.2 h))
  have h1 : Tendsto (fun ε : 𝕜 => φ y + ε • e) (𝓝[≠] (0 : 𝕜)) (𝓝 (φ y)) := by
    have : Tendsto (fun ε : 𝕜 => φ y + ε • e) (𝓝 (0 : 𝕜)) (𝓝 (φ y + (0 : 𝕜) • e)) :=
      tendsto_const_nhds.add (tendsto_id.smul_const e)
    rw [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have htend : Tendsto (fun ε : 𝕜 => φ.symm (φ y + ε • e)) (𝓝[≠] (0 : 𝕜)) (𝓝 y) := by
    have h2 : ContinuousAt φ.symm (φ y) := φ.continuousAt_symm (φ.map_source hyφ)
    have := h2.tendsto.comp h1
    rwa [φ.left_inv hyφ] at this
  have : NeBot (𝓝[≠] (0 : 𝕜)) := NormedField.nhdsNE_neBot 0
  refine mem_closure_of_tendsto htend ?_
  have hev : ∀ᶠ ε : 𝕜 in 𝓝[≠] (0 : 𝕜), φ y + ε • e ∈ φ.target :=
    h1 (φ.open_target.mem_nhds (φ.map_source hyφ))
  filter_upwards [hev, self_mem_nhdsWithin] with ε hεt hε
  have hsrc : φ.symm (φ y + ε • e) ∈ φ.source := φ.map_target hεt
  have hval : φ (φ.symm (φ y + ε • e)) = φ y + ε • e := φ.right_inv hεt
  have hcoord : ∀ i, ψ₀ (φ (φ.symm (φ y + ε • e))) i =
      ψ₀ (φ y) i + ε * (Pi.single (cidx ⟨j, hyj⟩) (1 : 𝕜) : Fin n → 𝕜) i := by
    intro i
    rw [hval, map_add, map_smul, he, ψ₀.apply_symm_apply]
    rfl
  constructor
  · rw [hc.2.2.1 ⟨k, hyk⟩ _ hsrc, hcoord, Pi.single_eq_of_ne hne, mul_zero, add_zero]
    exact (hc.2.2.1 ⟨k, hyk⟩ y hyφ).mp hyk
  · intro hmem
    have h0 : ψ₀ (φ y) (cidx ⟨j, hyj⟩) = 0 := (hc.2.2.1 ⟨j, hyj⟩ y hyφ).mp hyj
    have := (hc.2.2.1 ⟨j, hyj⟩ _ hsrc).mp hmem
    rw [hcoord, Pi.single_eq_same, mul_one, h0, zero_add] at this
    exact hε this

/-! ### The strict transforms under the Step 2b blow-up -/

variable (hfin : (activeMembers T).Finite) (hne : (activeMembers T).Nonempty)

/-- The blow-down of a step is a local analytic isomorphism: its centre has codimension one
(`exists_diffeomorph_of_codim_one`; the remarks after [Wlo09, Theorem 2.0.3]). -/
theorem isLocalDiffeomorph_stepπ :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (stepπ T hfin hne) := by
  obtain ⟨g, hg⟩ := (isBlowUp_blowUpπ ψ₀ (stepCenter T hfin hne)).exists_diffeomorph_of_codim_one
    (stepCenter T hfin hne)
  have hπ : ⇑(stepπ T hfin hne) = ⇑g := funext fun p => (hg p).symm
  change IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ⇑(stepπ T hfin hne)
  rw [hπ]
  exact g.isLocalDiffeomorph

/-- The strict transform of the TOP member lies over `E^j \ Z`: the positive locus `Z` is open in
`E^j`, so no point of `Z` is a limit of points of `E^j \ Z`. -/
theorem notMem_step2bCenter_of_mem_stepFamily_top {x' : stepStage T hfin hne}
    (hx' : x' ∈ (stepFamily T hfin hne).hyp (toLex (Sum.inl (topMember T hfin hne)))) :
    stepπ T hfin hne x' ∉ step2bCenter T hfin hne := by
  intro hZ
  have hx'' : x' ∈ closure (⇑(stepπ T hfin hne) ⁻¹'
      (T.F.hyp (topMember T hfin hne) \ step2bCenter T hfin hne)) := hx'
  obtain ⟨U, hU, hxU, hsub⟩ := exists_isOpen_inter_subset_positiveLocus T hZ
  have hnhds : ⇑(stepπ T hfin hne) ⁻¹' U ∈ 𝓝 x' :=
    (hU.preimage (stepπ T hfin hne).contMDiff.continuous).mem_nhds hxU
  obtain ⟨y, hyU, hy⟩ := mem_closure_iff_nhds.mp hx'' _ hnhds
  exact hy.2 (hsub ⟨hyU, hy.1⟩)

/-- Under the blow-up of a step (an open map) the strict transform of every other member is its
whole preimage: `E^k ∖ Z` is dense in `E^k` (`mem_closure_hyp_diff_hyp_of_ne` at the points of
`E^k ∩ Z ⊆ E^k ∩ E^j`). -/
theorem stepFamily_hyp_inl_of_ne {k : T.F.ι} (hk : k ≠ topMember T hfin hne) :
    (stepFamily T hfin hne).hyp (toLex (Sum.inl k)) = ⇑(stepπ T hfin hne) ⁻¹' T.F.hyp k := by
  refine Set.Subset.antisymm
    (strictTransform_subset_preimage (stepπ T hfin hne).contMDiff.continuous
      (T.isSnc.1 k).isClosed) fun x' hx' => ?_
  change x' ∈ closure (⇑(stepπ T hfin hne) ⁻¹' (T.F.hyp k \ step2bCenter T hfin hne))
  refine (isLocalDiffeomorph_stepπ T hfin hne).isOpenMap.preimage_closure_subset_closure_preimage ?_
  change stepπ T hfin hne x' ∈ closure (T.F.hyp k \ step2bCenter T hfin hne)
  by_cases hZ : stepπ T hfin hne x' ∈ step2bCenter T hfin hne
  · exact closure_mono (Set.sdiff_subset_sdiff_right (step2bCenter_subset T hfin hne))
      (mem_closure_hyp_diff_hyp_of_ne T hk hx' (step2bCenter_subset T hfin hne hZ))
  · exact subset_closure ⟨hx', hZ⟩

/-- Off the exceptional divisor every strict transform is the preimage
(`mem_strictTransform_iff_of_notMem`). -/
theorem stepFamily_hyp_inl_inter_compl (k : T.F.ι) :
    (stepFamily T hfin hne).hyp (toLex (Sum.inl k)) ∩
        ⇑(stepπ T hfin hne) ⁻¹' (step2bCenter T hfin hne)ᶜ =
      ⇑(stepπ T hfin hne) ⁻¹' T.F.hyp k ∩ ⇑(stepπ T hfin hne) ⁻¹' (step2bCenter T hfin hne)ᶜ := by
  ext x'
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨HypersurfaceFamily.mem_hyp_of_mem_strictTransform (isBlowUp_blowUpπ ψ₀ _) T.isSnc h1,
      h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(HypersurfaceFamily.mem_strictTransform_iff_of_notMem (isBlowUp_blowUpπ ψ₀ _) T.isSnc
      h2 k).mpr h1, h2⟩

end BMOmod

end Hironaka.Manifold

end
