/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.StructureSheaf
import Hironaka.Analytic.ConvSeries.Bridge
import Hironaka.Analytic.ConvSeries.Mul
import Hironaka.Analytic.Germ.CoordDiv
import Hironaka.Analytic.Weierstrass.FunctionLevel
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The Taylor series of an analytic germ

In coordinates `ψ : E ≃L[𝕜] 𝕜ⁿ`, an analytic germ `g` at `b ∈ E` has a unique convergent power
series `c ∈ Conv 𝕜 n` (the ring of convergent series of `Hironaka/Analytic/`) with
`g(ψ⁻¹ y) = c(y − ψ b)` near `ψ b` (`IsSeriesOf`, `exists_isSeriesOf`, `IsSeriesOf.unique`, from
`AnalyticAt.exists_eventuallyEq_evalSeries` and `eq_of_evalSeries_eventuallyEq`). Taking the
series is a ring homomorphism `taylorGerm ψ b : analyticGermsAt 𝕜 E b →+* Conv 𝕜 n`
(multiplicativity and additivity of the evaluation of convergent series on a common polydisc,
`evalSeries_mul`, `evalSeries_add`), and it is injective (`taylorGerm_injective`). Composed with
the chart transport of `Hironaka/Manifold/Germ/ChartTransport.lean` this is Bierstone–Milman's
Taylor series homomorphism `T_a` [BM97, (0.3)] (`taylorHom` in
`Hironaka/Manifold/Germ/TaylorHom.lean`).
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology Analytic
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜))

/-- The coordinates `ψ⁻¹` tend to `b` at `ψ b`. -/
theorem tendsto_coord_symm (b : E) : Tendsto ψ.symm (𝓝 (ψ b)) (𝓝 b) := by
  have := ψ.symm.continuous.continuousAt (x := ψ b)
  rwa [ContinuousAt, ψ.symm_apply_apply] at this

/-- Composition with the coordinates `ψ⁻¹`, as a ring homomorphism of germs
`Filter.Germ (𝓝 b) 𝕜 →+* Filter.Germ (𝓝 (ψ b)) 𝕜` (an instance of `germCompRingHom`). -/
abbrev germCompCoord (b : E) : (𝓝 b).Germ 𝕜 →+* (𝓝 (ψ b)).Germ 𝕜 :=
  germCompRingHom ψ.symm (tendsto_coord_symm ψ b)

theorem germCompCoord_coe (b : E) (f : E → 𝕜) :
    germCompCoord ψ b (↑f : (𝓝 b).Germ 𝕜) = (↑(f ∘ ψ.symm) : (𝓝 (ψ b)).Germ 𝕜) := rfl

theorem germCompCoord_injective (b : E) : Function.Injective (germCompCoord ψ b) := by
  intro f g hfg
  induction f using Germ.inductionOn with | h f => ?_
  induction g using Germ.inductionOn with | h g => ?_
  rw [germCompCoord_coe, germCompCoord_coe, Germ.coe_eq] at hfg
  refine Germ.coe_eq.mpr ?_
  have h1 := (ψ.continuous.continuousAt (x := b)).eventually hfg
  filter_upwards [h1] with x hx
  simpa only [Function.comp_apply, ψ.symm_apply_apply] using hx

/-- `c` is **the power series of the germ `g` at `b`** in the coordinates `ψ`: `c` is a convergent
series and `g(ψ⁻¹ y) = c(y − ψ b)` for `y` near `ψ b`. -/
def IsSeriesOf (b : E) (g : (𝓝 b).Germ 𝕜) (c : MvPowerSeries (Fin n) 𝕜) : Prop :=
  c ∈ Analytic.Conv 𝕜 n ∧ germCompCoord ψ b g = ↑(fun y : Fin n → 𝕜 => evalSeries c (y - ψ b))

/-- The translation `y ↦ y + ψ b` sends `𝓝 0` to `𝓝 (ψ b)`. -/
theorem tendsto_add_coord (b : E) :
    Tendsto (fun y : Fin n → 𝕜 => y + ψ b) (𝓝 0) (𝓝 (ψ b)) := by
  have := (continuous_add_const (ψ b)).tendsto (0 : Fin n → 𝕜)
  rwa [zero_add] at this

/-- Two convergent series with the same germ of evaluations at `ψ b` are equal. -/
theorem eq_of_evalSeries_sub_eventuallyEq (b : E) {c c' : MvPowerSeries (Fin n) 𝕜}
    (hc : c ∈ Analytic.Conv 𝕜 n) (hc' : c' ∈ Analytic.Conv 𝕜 n)
    (h : (fun y : Fin n → 𝕜 => evalSeries c (y - ψ b)) =ᶠ[𝓝 (ψ b)]
      fun y => evalSeries c' (y - ψ b)) : c = c' := by
  refine eq_of_evalSeries_eventuallyEq hc hc' ?_
  have := h.comp_tendsto (tendsto_add_coord ψ b)
  filter_upwards [this] with y hy
  simpa only [Function.comp_apply, add_sub_cancel_right] using hy

/-- The power series of a germ is unique. -/
theorem IsSeriesOf.unique {b : E} {g : (𝓝 b).Germ 𝕜} {c c' : MvPowerSeries (Fin n) 𝕜}
    (hc : IsSeriesOf ψ b g c) (hc' : IsSeriesOf ψ b g c') : c = c' :=
  eq_of_evalSeries_sub_eventuallyEq ψ b hc.1 hc'.1
    (Germ.coe_eq.mp (hc.2.symm.trans hc'.2))

/-- Every analytic germ has a power series (`AnalyticAt.exists_eventuallyEq_evalSeries`). -/
theorem exists_isSeriesOf {b : E} {g : (𝓝 b).Germ 𝕜} (hg : g ∈ analyticGermsAt 𝕜 E b) :
    ∃ c : MvPowerSeries (Fin n) 𝕜, IsSeriesOf ψ b g c := by
  obtain ⟨f, rfl, hf⟩ := hg
  have hfψ : AnalyticAt 𝕜 (f ∘ ψ.symm) (ψ b) := by
    have := (ψ.symm : (Fin n → 𝕜) →L[𝕜] E).analyticAt (ψ b)
    rw [ContinuousLinearEquiv.coe_coe] at this
    exact AnalyticAt.comp (by rwa [ψ.symm_apply_apply]) this
  obtain ⟨ρ, c, hc, hfc⟩ := AnalyticAt.exists_eventuallyEq_evalSeries hfψ
  exact ⟨c, ⟨ρ, hc⟩, by rw [germCompCoord_coe]; exact Germ.coe_eq.mpr hfc⟩

/-- The power series of a product is the product of the power series (evaluation is
multiplicative on a common polydisc, `evalSeries_mul`). -/
theorem IsSeriesOf.mul {b : E} {g g' : (𝓝 b).Germ 𝕜} {c c' : MvPowerSeries (Fin n) 𝕜}
    (hc : IsSeriesOf ψ b g c) (hc' : IsSeriesOf ψ b g' c') : IsSeriesOf ψ b (g * g') (c * c') := by
  obtain ⟨ρ, hρ⟩ := hc.1
  obtain ⟨ρ', hρ'⟩ := hc'.1
  have h1 : ConvNorm (ρ.min ρ') c ≠ ⊤ := BanachSeries.mono (ρ.min_le_left ρ') hρ
  have h2 : ConvNorm (ρ.min ρ') c' ≠ ⊤ := BanachSeries.mono (ρ.min_le_right ρ') hρ'
  refine ⟨(Analytic.Conv 𝕜 n).mul_mem hc.1 hc'.1, ?_⟩
  rw [map_mul, hc.2, hc'.2, ← Germ.coe_mul]
  refine Germ.coe_eq.mpr ?_
  filter_upwards [Analytic.eventually_norm_sub_lt (ψ b) (ρ.min ρ')] with y hy
  exact (evalSeries_mul h1 h2 fun k => (hy k).le).symm

/-- The power series of a sum is the sum of the power series (`evalSeries_add`). -/
theorem IsSeriesOf.add {b : E} {g g' : (𝓝 b).Germ 𝕜} {c c' : MvPowerSeries (Fin n) 𝕜}
    (hc : IsSeriesOf ψ b g c) (hc' : IsSeriesOf ψ b g' c') : IsSeriesOf ψ b (g + g') (c + c') := by
  obtain ⟨ρ, hρ⟩ := hc.1
  obtain ⟨ρ', hρ'⟩ := hc'.1
  have h1 : ConvNorm (ρ.min ρ') c ≠ ⊤ := BanachSeries.mono (ρ.min_le_left ρ') hρ
  have h2 : ConvNorm (ρ.min ρ') c' ≠ ⊤ := BanachSeries.mono (ρ.min_le_right ρ') hρ'
  refine ⟨(Analytic.Conv 𝕜 n).add_mem hc.1 hc'.1, ?_⟩
  rw [map_add, hc.2, hc'.2, ← Germ.coe_add]
  refine Germ.coe_eq.mpr ?_
  filter_upwards [Analytic.eventually_norm_sub_lt (ψ b) (ρ.min ρ')] with y hy
  exact (evalSeries_add h1 h2 fun k => (hy k).le).symm

theorem IsSeriesOf.one (b : E) : IsSeriesOf ψ b (1 : (𝓝 b).Germ 𝕜) 1 :=
  ⟨(Analytic.Conv 𝕜 n).one_mem, by
    rw [map_one]
    refine Germ.coe_eq.mpr (Eventually.of_forall fun y => ?_)
    exact (evalSeries_one _).symm⟩

theorem IsSeriesOf.zero (b : E) : IsSeriesOf ψ b (0 : (𝓝 b).Germ 𝕜) 0 :=
  ⟨(Analytic.Conv 𝕜 n).zero_mem, by
    rw [map_zero]
    refine Germ.coe_eq.mpr (Eventually.of_forall fun y => ?_)
    exact (evalSeries_zero _).symm⟩

/-- **The power series of an analytic germ**, the unique convergent series `c` with
`g(ψ⁻¹ y) = c(y − ψ b)` near `ψ b`. -/
def taylorGermFun (b : E) (g : (𝓝 b).Germ 𝕜) (hg : g ∈ analyticGermsAt 𝕜 E b) :
    MvPowerSeries (Fin n) 𝕜 :=
  (exists_isSeriesOf ψ hg).choose

theorem isSeriesOf_taylorGermFun (b : E) (g : (𝓝 b).Germ 𝕜) (hg : g ∈ analyticGermsAt 𝕜 E b) :
    IsSeriesOf ψ b g (taylorGermFun ψ b g hg) :=
  (exists_isSeriesOf ψ hg).choose_spec

theorem taylorGermFun_eq_of_isSeriesOf {b : E} {g : (𝓝 b).Germ 𝕜} (hg : g ∈ analyticGermsAt 𝕜 E b)
    {c : MvPowerSeries (Fin n) 𝕜} (hc : IsSeriesOf ψ b g c) : taylorGermFun ψ b g hg = c :=
  IsSeriesOf.unique ψ (isSeriesOf_taylorGermFun ψ b g hg) hc

theorem taylorGermFun_one (b : E) :
    taylorGermFun ψ b 1 (analyticGermsAt 𝕜 E b).one_mem = 1 :=
  taylorGermFun_eq_of_isSeriesOf ψ _ (IsSeriesOf.one ψ b)

theorem taylorGermFun_zero (b : E) :
    taylorGermFun ψ b 0 (analyticGermsAt 𝕜 E b).zero_mem = 0 :=
  taylorGermFun_eq_of_isSeriesOf ψ _ (IsSeriesOf.zero ψ b)

theorem taylorGermFun_mul (b : E) {g g' : (𝓝 b).Germ 𝕜} (hg : g ∈ analyticGermsAt 𝕜 E b)
    (hg' : g' ∈ analyticGermsAt 𝕜 E b) :
    taylorGermFun ψ b (g * g') ((analyticGermsAt 𝕜 E b).mul_mem hg hg') =
      taylorGermFun ψ b g hg * taylorGermFun ψ b g' hg' :=
  taylorGermFun_eq_of_isSeriesOf ψ _
    (IsSeriesOf.mul ψ (isSeriesOf_taylorGermFun ψ b g hg) (isSeriesOf_taylorGermFun ψ b g' hg'))

theorem taylorGermFun_add (b : E) {g g' : (𝓝 b).Germ 𝕜} (hg : g ∈ analyticGermsAt 𝕜 E b)
    (hg' : g' ∈ analyticGermsAt 𝕜 E b) :
    taylorGermFun ψ b (g + g') ((analyticGermsAt 𝕜 E b).add_mem hg hg') =
      taylorGermFun ψ b g hg + taylorGermFun ψ b g' hg' :=
  taylorGermFun_eq_of_isSeriesOf ψ _
    (IsSeriesOf.add ψ (isSeriesOf_taylorGermFun ψ b g hg) (isSeriesOf_taylorGermFun ψ b g' hg'))

/-- Taking the power series is a ring homomorphism into the ring `Conv 𝕜 n` of convergent
series. -/
def taylorGerm (b : E) : analyticGermsAt 𝕜 E b →+* Analytic.Conv 𝕜 n where
  toFun g := ⟨taylorGermFun ψ b g.1 g.2, (isSeriesOf_taylorGermFun ψ b g.1 g.2).1⟩
  map_one' := Subtype.ext (taylorGermFun_one ψ b)
  map_mul' g g' := Subtype.ext (taylorGermFun_mul ψ b g.2 g'.2)
  map_zero' := Subtype.ext (taylorGermFun_zero ψ b)
  map_add' g g' := Subtype.ext (taylorGermFun_add ψ b g.2 g'.2)

theorem coe_taylorGerm (b : E) (g : analyticGermsAt 𝕜 E b) :
    (taylorGerm ψ b g : MvPowerSeries (Fin n) 𝕜) = taylorGermFun ψ b g.1 g.2 := rfl

theorem isSeriesOf_taylorGerm (b : E) (g : analyticGermsAt 𝕜 E b) :
    IsSeriesOf ψ b g.1 (taylorGerm ψ b g) :=
  isSeriesOf_taylorGermFun ψ b g.1 g.2

/-- The power series determines the germ: a germ whose series vanishes is eventually zero. -/
theorem taylorGerm_injective (b : E) : Function.Injective (taylorGerm ψ b) := by
  intro g g' h
  have h1 := isSeriesOf_taylorGerm ψ b g
  have h2 := isSeriesOf_taylorGerm ψ b g'
  rw [h] at h1
  exact Subtype.ext (germCompCoord_injective ψ b (h1.2.trans h2.2.symm))

end Manifold
