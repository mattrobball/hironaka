/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Germ.ChartTransport
public import Hironaka.Manifold.Germ.Taylor
import Hironaka.Analytic.ConvSeries.Mul
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The Taylor homomorphism of the structure sheaf

In a chart `φ` of the maximal atlas containing `a`, with coordinates `ψ : E ≃L[𝕜] 𝕜ⁿ`, the
**Taylor homomorphism** `T_a : 𝒪_{M,a} →+* 𝕜[[X₁, …, Xₙ]]` sends the germ of a section `f` to the
power series of `f ∘ φ⁻¹ ∘ ψ⁻¹` at `ψ(φ(a))`: it is the chart transport
(`Hironaka/Manifold/Germ/ChartTransport.lean`) followed by the power series of an analytic germ
(`taylorGerm`, `Hironaka/Manifold/Germ/Taylor.lean`, valued in the ring `Conv 𝕜 n` of
convergent series). This is Bierstone–Milman's injective "Taylor series homomorphism"
[BM97, (0.3)]. `taylorHom` satisfies the specification `IsTaylorHom` of
`Hironaka/Manifold/StructureSheaf.lean` (`isTaylorHom_taylorHom`); any map satisfying it is
unique (`IsTaylorHom.eq`), injective (`IsTaylorHom.injective'`: a germ whose power series vanishes
is eventually zero) and has the value at `a` as constant term (`IsTaylorHom.constantCoeff'`). Its
range, its behaviour on the maximal ideal and the induced isomorphism of completions are in
`Hironaka/Manifold/Germ/TaylorIdeal.lean` and `Hironaka/Manifold/Germ/TaylorCompletion.lean`.
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology Analytic
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))
  (φ : OpenPartialHomeomorph M E) {a : M} (ha : a ∈ φ.source) (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M)

/-- **The Taylor homomorphism** `T_a : 𝒪_{M,a} →+* 𝕜[[X₁, …, Xₙ]]` in the chart `φ` with
coordinates `ψ` [BM97, (0.3)]: the chart transport of germs followed by the power series of an
analytic germ. -/
def taylorHom : (structureSheaf 𝕜 E M).presheaf.stalk a →+* MvPowerSeries (Fin n) 𝕜 :=
  ((Analytic.Conv 𝕜 n).val.toRingHom.comp (taylorGerm ψ (φ a))).comp
      (chartTransport E φ ha hφ).toRingHom

theorem taylorHom_apply (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    taylorHom E ψ φ ha hφ s =
      (taylorGerm ψ (φ a) (chartTransport E φ ha hφ s) : MvPowerSeries (Fin n) 𝕜) :=
  rfl

theorem taylorHom_mem_conv (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    taylorHom E ψ φ ha hφ s ∈ Analytic.Conv 𝕜 n :=
  (taylorGerm ψ (φ a) (chartTransport E φ ha hφ s)).2

/-- `taylorHom` satisfies the specification `IsTaylorHom`. -/
theorem isTaylorHom_taylorHom : IsTaylorHom E ψ φ a (taylorHom E ψ φ ha hφ) := by
  refine ⟨taylorHom_mem_conv E ψ φ ha hφ, fun U hU f => ?_⟩
  have h1 := (isSeriesOf_taylorGerm ψ (φ a) (chartTransport E φ ha hφ
    ((structureSheaf 𝕜 E M).presheaf.germ U a hU f))).2
  rw [isChartTransport_chartTransport E φ ha hφ U hU f, germCompCoord_coe] at h1
  rw [taylorHom_apply]
  exact Germ.coe_eq.mp h1

/-- Two maps satisfying the specification agree (uniqueness of the power series of a germ,
`eq_of_evalSeries_eventuallyEq`). -/
theorem IsTaylorHom.eq {T T' : (structureSheaf 𝕜 E M).presheaf.stalk a →+* MvPowerSeries (Fin n) 𝕜}
    (hT : IsTaylorHom E ψ φ a T) (hT' : IsTaylorHom E ψ φ a T') : T = T' := by
  refine RingHom.ext fun s => ?_
  obtain ⟨U, hU, f, rfl⟩ := (structureSheaf 𝕜 E M).presheaf.exists_germ_eq s
  exact eq_of_evalSeries_sub_eventuallyEq ψ (φ a) (hT.1 _) (hT'.1 _)
    ((hT.2 U hU f).symm.trans (hT'.2 U hU f))

include ha in
/-- A map satisfying the specification is injective [BM97, (0.3)]: two germs with the same power
series have the same germ in the chart, hence the same germ. -/
theorem IsTaylorHom.injective'
    {T : (structureSheaf 𝕜 E M).presheaf.stalk a →+* MvPowerSeries (Fin n) 𝕜}
    (hT : IsTaylorHom E ψ φ a T) : Function.Injective T := by
  intro s t hst
  obtain ⟨U, hU, f, rfl⟩ := (structureSheaf 𝕜 E M).presheaf.exists_germ_eq s
  obtain ⟨V, hV, g, rfl⟩ := (structureSheaf 𝕜 E M).presheaf.exists_germ_eq t
  have h1 := hT.2 U hU f
  have h2 := hT.2 V hV g
  rw [hst] at h1
  have h3 : (extendSection 𝕜 E f ∘ φ.symm ∘ ψ.symm) =ᶠ[𝓝 (ψ (φ a))]
      (extendSection 𝕜 E g ∘ φ.symm ∘ ψ.symm) := h1.trans h2.symm
  have h4 : germCompCoord ψ (φ a) (↑(extendSection 𝕜 E f ∘ φ.symm) : (𝓝 (φ a)).Germ 𝕜) =
      germCompCoord ψ (φ a) ↑(extendSection 𝕜 E g ∘ φ.symm) := by
    rw [germCompCoord_coe, germCompCoord_coe]
    exact Germ.coe_eq.mpr h3
  have h5 := germCompCoord_injective ψ (φ a) h4
  apply stalkToChartGerm_injective E φ ha
  rw [stalkToChartGerm_germ, stalkToChartGerm_germ]
  exact h5

include ha in
/-- The constant term of the power series of a germ is its value at `a`. -/
theorem IsTaylorHom.constantCoeff'
    {T : (structureSheaf 𝕜 E M).presheaf.stalk a →+* MvPowerSeries (Fin n) 𝕜}
    (hT : IsTaylorHom E ψ φ a T) (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    MvPowerSeries.constantCoeff (T s) = eval 𝕜 E M a s := by
  obtain ⟨U, hU, f, rfl⟩ := (structureSheaf 𝕜 E M).presheaf.exists_germ_eq s
  have h1 := (hT.2 U hU f).eq_of_nhds
  simp only [Function.comp_apply, ψ.symm_apply_apply, φ.left_inv ha, sub_self,
    evalSeries_zero_eq] at h1
  rw [← h1, extendSection_of_mem 𝕜 E f hU]
  exact (contMDiffSheafCommRing.eval_germ 𝓘(𝕜, E) 𝓘(𝕜) ω M 𝕜 U a hU f).symm

end Manifold
