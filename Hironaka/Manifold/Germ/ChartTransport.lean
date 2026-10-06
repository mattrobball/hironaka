/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.StructureSheaf
public import Mathlib.Topology.Germ
import Hironaka.Manifold.Sheaf.LocalRing
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Chart transport of germs

For a chart `φ` of the maximal atlas of an analytic manifold `M` over a complete field `𝕜`, with
`a` in its source, the stalk `𝒪_{M,a}` of the structure sheaf is isomorphic to the ring
`𝒪_{E,φ(a)} = analyticGermsAt 𝕜 E (φ a)` of germs at `φ(a)` of functions analytic at `φ(a)`, by
`f ↦ f ∘ φ⁻¹` (`chartTransport`, satisfying the specification `IsChartTransport` of
`Hironaka/Manifold/StructureSheaf.lean`); the isomorphism respects the maximal ideals. This is
the identification, in a regular coordinate chart, of the local ring of an analytic manifold with
the ring of analytic function germs [BM97, §3, "Regular coordinate charts"].

The construction: the stalk embeds into the germs at `a` (`stalkToGerm`), composition with `φ⁻¹`
is a ring homomorphism of germs (`germCompChart`), and the composite `stalkToChartGerm` is
injective with range the analytic germs (`range_stalkToChartGerm`): a `C^ω` germ on `M` composed
with `φ⁻¹` is analytic (`ContMDiffAt` in the chart at `a`), and an analytic germ `g` at `φ(a)` is
`C^ω` near `φ(a)` (the field is complete), so `g ∘ φ` is a `C^ω` section on
`φ⁻¹(V) ∩ φ.source` for a neighbourhood `V` on which `g` is analytic. The transport is the first
step of the Taylor homomorphism (`Hironaka/Manifold/Germ/TaylorHom.lean`) and is used wherever a
statement about the stalk is read in a chart.
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  (φ : OpenPartialHomeomorph M E) {a : M} (ha : a ∈ φ.source)

omit [NormedSpace 𝕜 E] [ChartedSpace E M] in
theorem germCompRingHom_coe {α β : Type*} {l : Filter α} {l' : Filter β} (g : α → β)
    (hg : Tendsto g l l') (f : β → 𝕜) :
    germCompRingHom (𝕜 := 𝕜) g hg (↑f : l'.Germ 𝕜) = (↑(f ∘ g) : l.Germ 𝕜) := rfl

omit [NormedSpace 𝕜 E] in
/-- Composition with the inverse chart `φ⁻¹` of a chart `φ` at `a`, as a ring homomorphism of germs
`Filter.Germ (𝓝 a) 𝕜 →+* Filter.Germ (𝓝 (φ a)) 𝕜`. -/
abbrev germCompChart : (𝓝 a).Germ 𝕜 →+* (𝓝 (φ a)).Germ 𝕜 :=
  germCompRingHom φ.symm (φ.tendsto_symm ha)

omit [NormedSpace 𝕜 E] [ChartedSpace E M] in
theorem germCompChart_coe (f : M → 𝕜) :
    germCompChart E φ ha (↑f : (𝓝 a).Germ 𝕜) = (↑(f ∘ φ.symm) : (𝓝 (φ a)).Germ 𝕜) := rfl

omit [NormedSpace 𝕜 E] [ChartedSpace E M] in
/-- Composition with the inverse chart is injective on germs at `a`: compose back with `φ`. -/
theorem germCompChart_injective : Function.Injective (germCompChart (𝕜 := 𝕜) E φ ha) := by
  intro f g hfg
  induction f using Germ.inductionOn with | h f => ?_
  induction g using Germ.inductionOn with | h g => ?_
  rw [germCompChart_coe, germCompChart_coe, Germ.coe_eq] at hfg
  refine Germ.coe_eq.mpr ?_
  have h1 := (φ.continuousAt ha).eventually hfg
  filter_upwards [h1, φ.eventually_left_inverse ha] with x hx hx'
  simpa only [Function.comp_apply, hx'] using hx

/-- The stalk `𝒪_{M,a}` mapped to the germs at `φ(a)`, `f ↦ f ∘ φ⁻¹`. -/
def stalkToChartGerm : (structureSheaf 𝕜 E M).presheaf.stalk a →+* (𝓝 (φ a)).Germ 𝕜 :=
  (germCompChart E φ ha).comp (stalkToGerm 𝓘(𝕜, E) ω M a)

omit φ ha in
theorem stalkToGerm_structureSheaf_germ (U : Opens M) (hU : a ∈ U)
    (f : (structureSheaf 𝕜 E M).presheaf.obj (op U)) :
    stalkToGerm 𝓘(𝕜, E) ω M a ((structureSheaf 𝕜 E M).presheaf.germ U a hU f) =
      ↑(extendSection 𝕜 E f) :=
  stalkToGerm_germ 𝓘(𝕜, E) ω M a U hU f

theorem stalkToChartGerm_germ (U : Opens M) (hU : a ∈ U)
    (f : (structureSheaf 𝕜 E M).presheaf.obj (op U)) :
    stalkToChartGerm E φ ha ((structureSheaf 𝕜 E M).presheaf.germ U a hU f) =
      ↑(extendSection 𝕜 E f ∘ φ.symm) := by
  rw [stalkToChartGerm, RingHom.comp_apply, stalkToGerm_structureSheaf_germ, germCompChart_coe]

theorem stalkToChartGerm_injective :
    Function.Injective (stalkToChartGerm (𝕜 := 𝕜) E (M := M) φ ha) :=
  (germCompChart_injective E φ ha).comp (stalkToGerm_injective 𝓘(𝕜, E) ω M a)

variable (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M)

include ha hφ in
/-- A chart `φ⁻¹` of the maximal atlas is an analytic map near `φ(a)`. -/
theorem contMDiffAt_chart_symm : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω φ.symm (φ a) :=
  (contMDiffOn_symm_of_mem_maximalAtlas (n := ω) hφ).contMDiffAt
    (φ.open_target.mem_nhds (φ.map_source ha))

variable [CompleteSpace 𝕜]

include hφ in
/-- The range of `f ↦ f ∘ φ⁻¹` on the stalk is exactly the ring of analytic germs at `φ(a)`. -/
theorem range_stalkToChartGerm :
    Set.range (stalkToChartGerm (𝕜 := 𝕜) E (M := M) φ ha) =
      (analyticGermsAt 𝕜 E (φ a) : Set ((𝓝 (φ a)).Germ 𝕜)) := by
  ext g
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨h, hg, U, haU, hU⟩ := (mem_range_stalkToGerm_iff 𝓘(𝕜, E) ω M a
      (stalkToGerm 𝓘(𝕜, E) ω M a s)).mp ⟨s, rfl⟩
    refine ⟨h ∘ φ.symm, ?_, ?_⟩
    · rw [stalkToChartGerm, RingHom.comp_apply, hg, germCompChart_coe]
    · have h1 : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω h a := hU.contMDiffAt (U.2.mem_nhds haU)
      have h2 : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω (h ∘ φ.symm) (φ a) :=
        ContMDiffAt.comp_of_eq h1 (contMDiffAt_chart_symm E φ ha hφ) (φ.left_inv ha)
      exact (contMDiffAt_iff_contDiffAt.mp h2).analyticAt
  · rintro ⟨g, rfl, hg⟩
    obtain ⟨V, hVg, hVo, haV⟩ := eventually_nhds_iff.mp hg.eventually_analyticAt
    let U : Opens M := ⟨φ.source ∩ φ ⁻¹' V,
      φ.continuousOn_toFun.isOpen_inter_preimage φ.open_source hVo⟩
    have haU : a ∈ U := ⟨ha, (haV : φ a ∈ V)⟩
    have hU : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω (g ∘ φ) U := by
      intro x hx
      refine ContMDiffAt.contMDiffWithinAt ?_
      have hφ' : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω φ x :=
        (contMDiffOn_of_mem_maximalAtlas (n := ω) hφ).contMDiffAt
          (φ.open_source.mem_nhds hx.1)
      have hg' : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω g (φ x) :=
        contMDiffAt_iff_contDiffAt.mpr ((hVg _ hx.2).contDiffAt)
      exact hg'.comp x hφ'
    obtain ⟨s, hs⟩ := (mem_range_stalkToGerm_iff 𝓘(𝕜, E) ω M a ↑(g ∘ φ)).mpr
      ⟨g ∘ φ, rfl, U, haU, hU⟩
    refine ⟨s, ?_⟩
    rw [stalkToChartGerm, RingHom.comp_apply, hs, germCompChart_coe]
    refine Germ.coe_eq.mpr ?_
    filter_upwards [φ.eventually_right_inverse' ha] with y hy
    exact congrArg g hy

/-- **The chart transport of germs**: the ring isomorphism `𝒪_{M,a} ≃+* 𝒪_{E, φ(a)}`, `f ↦ f ∘ φ⁻¹`,
for a chart `φ` of the maximal atlas containing `a` [BM97, §3, "Regular coordinate charts"]. -/
def chartTransport :
    (structureSheaf 𝕜 E M).presheaf.stalk a ≃+* analyticGermsAt 𝕜 E (φ a) :=
  RingEquiv.ofBijective ((stalkToChartGerm E φ ha).codRestrict (analyticGermsAt 𝕜 E (φ a))
    fun s => (range_stalkToChartGerm E φ ha hφ).le ⟨s, rfl⟩)
    ⟨fun s t hst => stalkToChartGerm_injective E φ ha (congr_arg Subtype.val hst),
      fun g => by
        obtain ⟨s, hs⟩ := (range_stalkToChartGerm E φ ha hφ).ge g.2
        exact ⟨s, Subtype.ext hs⟩⟩

theorem chartTransport_apply_coe (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    (chartTransport E φ ha hφ s : (𝓝 (φ a)).Germ 𝕜) = stalkToChartGerm E φ ha s := rfl

/-- `chartTransport` satisfies the specification `IsChartTransport`. -/
theorem isChartTransport_chartTransport :
    IsChartTransport 𝕜 E φ a (chartTransport E φ ha hφ) :=
  fun U hU f => by rw [chartTransport_apply_coe, stalkToChartGerm_germ]

omit ha [CompleteSpace 𝕜] in
/-- The chart transport is determined by its specification. -/
theorem IsChartTransport.eq
    {e e' : (structureSheaf 𝕜 E M).presheaf.stalk a ≃+* analyticGermsAt 𝕜 E (φ a)}
    (he : IsChartTransport 𝕜 E φ a e) (he' : IsChartTransport 𝕜 E φ a e') : e = e' := by
  ext s
  obtain ⟨U, haU, f, rfl⟩ := (structureSheaf 𝕜 E M).presheaf.exists_germ_eq s
  exact (he U haU f).trans (he' U haU f).symm

omit [CompleteSpace 𝕜] in
include ha in
/-- The chart transport respects `𝔪_a`: a germ is a non-unit iff its transport vanishes at
`φ(a)`. -/
theorem IsChartTransport.mem_nonunits_iff'
    {e : (structureSheaf 𝕜 E M).presheaf.stalk a ≃+* analyticGermsAt 𝕜 E (φ a)}
    (he : IsChartTransport 𝕜 E φ a e) (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    s ∈ nonunits ((structureSheaf 𝕜 E M).presheaf.stalk a) ↔
      ((e s : (𝓝 (φ a)).Germ 𝕜)).value = 0 := by
  obtain ⟨U, haU, f, rfl⟩ := (structureSheaf 𝕜 E M).presheaf.exists_germ_eq s
  rw [he U haU f]
  have h1 : (structureSheaf 𝕜 E M).presheaf.germ U a haU f ∈
      nonunits ((structureSheaf 𝕜 E M).presheaf.stalk a) ↔
      eval 𝕜 E M a ((structureSheaf 𝕜 E M).presheaf.germ U a haU f) = 0 := by
    rw [show nonunits ((structureSheaf 𝕜 E M).presheaf.stalk a) =
      ↑(RingHom.ker (eval 𝕜 E M a)) from contMDiffSheafCommRing.nonunits_stalk 𝓘(𝕜, E) ω M a]
    exact RingHom.mem_ker
  have h2 : eval 𝕜 E M a ((structureSheaf 𝕜 E M).presheaf.germ U a haU f) = f ⟨a, haU⟩ :=
    contMDiffSheafCommRing.eval_germ 𝓘(𝕜, E) 𝓘(𝕜) ω M 𝕜 U a haU f
  rw [h1, h2]
  change _ ↔ extendSection 𝕜 E f (φ.symm (φ a)) = 0
  rw [φ.left_inv ha]
  exact Iff.of_eq (congrArg (· = 0) (extendBy0_of_mem 𝓘(𝕜, E) ω M f haU).symm)

end Manifold
