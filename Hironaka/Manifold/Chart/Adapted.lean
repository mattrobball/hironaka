/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Order
public import Hironaka.Manifold.Germ.CoordDeriv
public import Hironaka.Manifold.Submanifold
import Hironaka.Manifold.AdaptedChart
import Hironaka.Manifold.Chart.Order
import Hironaka.Manifold.Germ.CoordDerivChart
import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Manifold.IdealSheaf.Order
import Hironaka.Manifold.Submanifold.Charts
import Hironaka.Manifold.Submanifold.Generators
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Consequences of the chart-extension theorem: adapted charts and order one

The chart-extension theorem `exists_chart_extending` of `Hironaka/Manifold/AdaptedChart.lean`
(analytic functions vanishing at `a` with independent differentials are coordinates of a chart
centred at `a`) has the following consequences for adapted charts and for sections of order one:

* the chart it produces is an adapted chart for the common zero set of the `z_i` on its source
  (`exists_adaptedChart_zeroSet'`, through `isAdaptedChart_zeroSet'`);
* a section `h` of `𝒪_M` has order one at `a` iff `h(a) = 0` and `dh(a) ≠ 0`
  (`ord_eq_one_iff_fderiv_ne_zero'`): the chart form of `Hironaka/Manifold/Chart/Order.lean`
  (some `∂_i h(a) ≠ 0`) is translated through the chain rule `mfderiv_eq_fderiv_comp_chart` and the
  invertibility of the chart's derivative — `dh(a)` vanishes iff all its values on the basis
  `ψ⁻¹(e_i)` vanish;
* the order-one form (Kollár's construction of hypersurfaces of maximal contact,
  [Kol07, Theorem 80 (2)] and its proof: a local section of order one at `x` has a smooth zero
  divisor near `x`): a section of order one at `a` is a coordinate of a chart centred at `a`, and
  its zero set is on that chart's source a closed smooth hypersurface with that chart as adapted
  chart (`exists_adapted_chart_of_ord_eq_one'`; `IsClosedSubmanifoldOn` through
  `IsAdaptedChart.isClosedSubmanifoldOn'`).

The third point is the analytic implicit function theorem in the form the maximal-contact
construction uses (`Hironaka/Manifold/Chart/MaximalContact.lean`); the sources take it for
granted ("by the implicit function theorem, `z = 0` defines a regular submanifold" [BM97, §1];
[Hir64, p. 121]).
-/

public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))

section ZeroSet

variable [IsManifold 𝓘(𝕜, E) ω M]

/-- The chart of `exists_chart_extending` is an adapted chart for the common zero set of the `z_i`
on its source. -/
theorem exists_adaptedChart_zeroSet' {c : ℕ} (z : Fin c → M → 𝕜) (a : M)
    (hz : ∀ i, ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω (z i) a) (hz0 : ∀ i, z i a = 0)
    (hind : HasIndependentDifferentialsAt E z a) :
    ∃ (e : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n), e ∈ maximalAtlas 𝓘(𝕜, E) ω M ∧
      a ∈ e.source ∧ e a = 0 ∧ IsAdaptedChart ψ (e.source ∩ {x | ∀ i, z i x = 0}) e σ ∧
      ∀ x ∈ e.source, ∀ i, z i x = ψ (e x) (σ i) := by
  obtain ⟨e, σ, he, ha, h0, hz'⟩ := exists_chart_extending ψ z a hz hz0 hind
  refine ⟨e, σ, he, ha, h0, ?_, hz'⟩
  have hset : e.source ∩ {x | ∀ i, z i x = 0} = e.source ∩ {x | ∀ i, ψ (e x) (σ i) = 0} := by
    ext x
    constructor <;> rintro ⟨hx, h⟩ <;> refine ⟨hx, fun i => ?_⟩
    · rw [← hz' x hx i]
      exact h i
    · rw [hz' x hx i]
      exact h i
  rw [hset]
  exact isAdaptedChart_zeroSet' he σ

end ZeroSet

section OrderOne

variable (φ : OpenPartialHomeomorph M E) (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {a : M}
  (ha : a ∈ φ.source)

/-- The value at `a` of `∂_i` of the germ of a section is the derivative of the section read in
the chart, in the direction `ψ⁻¹(e_i)` (`coordDeriv_apply`). -/
theorem eval_coordDerivStalk_germ {U : Opens M} (haU : a ∈ U)
    (h : (structureSheaf 𝕜 E M).presheaf.obj (op U)) (i : Fin n) :
    eval 𝕜 E M a (coordDerivStalk E ψ φ hφ ha i ((structureSheaf 𝕜 E M).presheaf.germ U a haU h)) =
      fderiv 𝕜 (extendSection 𝕜 E h ∘ φ.symm) (φ a) (ψ.symm (Pi.single i 1)) := by
  set V : Opens M := U ⊓ ⟨φ.source, φ.open_source⟩ with hVdef
  have hV : (V : Set M) ⊆ φ.source := fun x hx => hx.2
  have haV : a ∈ V := ⟨haU, ha⟩
  set h' := (structureSheaf 𝕜 E M).presheaf.map (homOfLE (inf_le_left : V ≤ U)).op h with hh'
  have hres : (structureSheaf 𝕜 E M).presheaf.germ U a haU h =
      (structureSheaf 𝕜 E M).presheaf.germ V a haV h' :=
    ((structureSheaf 𝕜 E M).presheaf.germ_res_apply (homOfLE inf_le_left) a haV h).symm
  rw [hres, coordDerivStalk_germ E ψ φ hφ ha V hV haV i, eval_eq_value,
    stalkToGerm_structureSheaf_germ, Germ.value_ofFun, extendSection_of_mem 𝕜 E _ haV,
    coordDeriv_apply]
  congr 1
  apply Filter.EventuallyEq.fderiv_eq
  have hmem : ∀ᶠ y in 𝓝 (φ a), φ.symm y ∈ (V : Set M) :=
    (φ.continuousAt_symm (φ.map_source ha)).tendsto.eventually_mem
      (by rw [φ.left_inv ha]; exact V.2.mem_nhds haV)
  filter_upwards [hmem] with y hy
  simp only [Function.comp]
  rw [extendSection_of_mem 𝕜 E _ hy, extendSection_of_mem 𝕜 E _ hy.1]
  rfl

variable [FiniteDimensional 𝕜 E] [IsManifold 𝓘(𝕜, E) ω M]

omit ψ φ hφ ha in
/-- A section `h` of `𝒪_M` has order one at `a` iff `h(a) = 0` and `dh(a) ≠ 0` (the criterion
Kollár uses in the proof of [Kol07, Theorem 80]). -/
theorem ord_eq_one_iff_fderiv_ne_zero' {U : Opens M} {a : M} (ha : a ∈ U)
    (h : (structureSheaf 𝕜 E M).presheaf.obj (op U)) :
    IsLocalRing.ordElem ((structureSheaf 𝕜 E M).presheaf.germ U a ha h) = 1 ↔
      extendSection 𝕜 E h a = 0 ∧ mderivFun E (extendSection 𝕜 E h) a ≠ 0 := by
  set χ := chartAt E a with hχdef
  have hχ : χ ∈ maximalAtlas 𝓘(𝕜, E) ω M := IsManifold.chart_mem_maximalAtlas a
  have haχ : a ∈ χ.source := mem_chart_source E a
  set ψ := IdealSheaf.modelCoord (𝕜 := 𝕜) (E := E)
  rw [ord_eq_one_iff_exists_coordDerivStalk_ne_zero' E ψ χ hχ haχ]
  have hev : eval 𝕜 E M a ((structureSheaf 𝕜 E M).presheaf.germ U a ha h) =
      extendSection 𝕜 E h a := by
    rw [eval_eq_value, stalkToGerm_structureSheaf_germ, Germ.value_ofFun]
  rw [hev]
  refine and_congr_right fun _ => ?_
  simp_rw [eval_coordDerivStalk_germ E ψ χ hχ haχ ha h]
  set L := fderiv 𝕜 (extendSection 𝕜 E h ∘ χ.symm) (χ a) with hL
  have hmd : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜) (extendSection 𝕜 E h) a :=
    ((contMDiffOn_extendSection h).contMDiffAt (U.2.mem_nhds ha)).mdifferentiableAt (by simp)
  have hcomp : mderivFun E (extendSection 𝕜 E h) a = L.comp (mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) χ a) :=
    mfderiv_eq_fderiv_comp_chart hχ haχ hmd
  have hsurj := (mdifferentiable_of_mem_maximalAtlas hχ).mfderiv_surjective haχ
  rw [hcomp]
  constructor
  · rintro ⟨i, hi⟩ hzero
    apply hi
    obtain ⟨v, hv⟩ := hsurj (ψ.symm (Pi.single i 1))
    have h1 : L (mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) χ a v) = 0 := congrArg (fun T => T v) hzero
    exact hv ▸ h1
  · intro hne
    by_contra hall
    have hall' : ∀ i, L (ψ.symm (Pi.single i 1)) = 0 := fun i => by
      by_contra hi
      exact hall ⟨i, hi⟩
    apply hne
    have hL0 : L = 0 := by
      have hpi : ((L.comp (ψ.symm : (Fin (Module.finrank 𝕜 E) → 𝕜) →L[𝕜] E) :
          (Fin (Module.finrank 𝕜 E) → 𝕜) →L[𝕜] 𝕜) : (Fin (Module.finrank 𝕜 E) → 𝕜) →ₗ[𝕜] 𝕜) = 0
      := by
        apply LinearMap.pi_ext
        intro i x
        have : Pi.single i x = x • Pi.single i (1 : 𝕜) := by
          rw [← Pi.single_smul, smul_eq_mul, mul_one]
        simp [this, hall' i]
      have hpi' : L.comp (ψ.symm : (Fin (Module.finrank 𝕜 E) → 𝕜) →L[𝕜] E) = 0 :=
        ContinuousLinearMap.coe_injective hpi
      have : L = (L.comp (ψ.symm : (Fin (Module.finrank 𝕜 E) → 𝕜) →L[𝕜] E)).comp
          (ψ : E →L[𝕜] (Fin (Module.finrank 𝕜 E) → 𝕜)) := by
        ext v
        simp
      rw [this, hpi']
      simp
    rw [hL0]
    exact ContinuousLinearMap.zero_comp _

omit [FiniteDimensional 𝕜 E] in
/-- The order-one form of the chart-extension theorem ([Kol07, Theorem 80 (2)] and its proof): a
section `h` of `𝒪_M` with `ord_a h = 1` is the `σ 0`-th coordinate of a chart `e` centred at `a`
with source inside the domain of `h`, and `H = (h = 0)` is, on the source of `e`, a closed smooth
hypersurface with `e` as adapted chart and a closed submanifold of codimension one of that
source. -/
theorem exists_adapted_chart_of_ord_eq_one' {U : Opens M} {a : M} (ha : a ∈ U)
    (h : (structureSheaf 𝕜 E M).presheaf.obj (op U))
    (hord : IsLocalRing.ordElem ((structureSheaf 𝕜 E M).presheaf.germ U a ha h) = 1) :
    ∃ (e : OpenPartialHomeomorph M E) (σ : Fin 1 ↪ Fin n), e ∈ maximalAtlas 𝓘(𝕜, E) ω M ∧
      a ∈ e.source ∧ e.source ⊆ U ∧ e a = 0 ∧
      (∀ x ∈ e.source, extendSection 𝕜 E h x = ψ (e x) (σ 0)) ∧
      IsAdaptedChart ψ (e.source ∩ {x | extendSection 𝕜 E h x = 0}) e σ ∧
      IsClosedSubmanifoldOn ψ e.source (e.source ∩ {x | extendSection 𝕜 E h x = 0}) 1 := by
  have : FiniteDimensional 𝕜 E := ψ.symm.toLinearEquiv.finiteDimensional
  obtain ⟨h0, hd⟩ := (ord_eq_one_iff_fderiv_ne_zero' E ha h).mp hord
  have hind : HasIndependentDifferentialsAt E (fun _ : Fin 1 => extendSection 𝕜 E h) a := by
    change LinearIndependent 𝕜 fun _ : Fin 1 => mderivFun E (extendSection 𝕜 E h) a
    exact linearIndependent_unique_iff.mpr hd
  obtain ⟨e₀, σ, he₀, hae₀, he₀0, hz⟩ := exists_chart_extending ψ
    (fun _ : Fin 1 => extendSection 𝕜 E h) a
    (fun _ => (contMDiffOn_extendSection h).contMDiffAt (U.2.mem_nhds ha)) (fun _ => h0) hind
  -- restrict the chart to the domain of `h`
  set e := e₀.restrOpen (U : Set M) U.2 with hedef
  have hsrc : e.source = e₀.source ∩ U := OpenPartialHomeomorph.restrOpen_source _ _ _
  have he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M := by
    rw [hedef, OpenPartialHomeomorph.restrOpen_eq_restr]
    exact restr_mem_maximalAtlas _ he₀ U.2
  have hae : a ∈ e.source := by
    rw [hsrc]
    exact ⟨hae₀, ha⟩
  have hsub : e.source ⊆ U := by
    rw [hsrc]
    exact inter_subset_right
  have hcoord : ∀ x ∈ e.source, extendSection 𝕜 E h x = ψ (e x) (σ 0) := fun x hx => by
    rw [hsrc] at hx
    exact hz x hx.1 0
  have hset : e.source ∩ {x | extendSection 𝕜 E h x = 0} =
      e.source ∩ {x | ∀ i, ψ (e x) (σ i) = 0} := by
    ext x
    constructor <;> rintro ⟨hx, hx'⟩ <;> refine ⟨hx, ?_⟩
    · intro i
      rw [Fin.fin_one_eq_zero i, ← hcoord x hx]
      exact hx'
    · change extendSection 𝕜 E h x = 0
      rw [hcoord x hx]
      exact hx' 0
  have hadapt : IsAdaptedChart ψ (e.source ∩ {x | extendSection 𝕜 E h x = 0}) e σ := by
    rw [hset]
    exact isAdaptedChart_zeroSet' he σ
  exact ⟨e, σ, he, hae, hsub, he₀0, hcoord, hadapt, hadapt.isClosedSubmanifoldOn'⟩

end OrderOne

end Manifold

end
