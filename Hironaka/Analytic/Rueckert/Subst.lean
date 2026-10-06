/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.Eval
public import Hironaka.Analytic.Weierstrass.Basic
import Hironaka.Analytic.ConvSeries.Mul
import Hironaka.Analytic.ConvSeries.Rescale
import Hironaka.Analytic.Germ.Axis
import Hironaka.Analytic.Weierstrass.FunctionLevel
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Positivity.Finset

/-!
# Linear changes of variables on `Conv K n`

Rückert's induction makes a series regular in a distinguished variable by a linear change of
coordinates [GR65, Chapter II, §B]; the printed condition is "there are local coordinates … such
that `f_a(0, …, 0, x_m) ∼ x_m^e`" [BM88, proof of Theorem 4.4, p. 24]. The generic linear change
of `Hironaka/Analytic/Germ/Axis.lean` is a function-level statement
(`evalSeries f (L (Pi.single 0 t)) = t^d e(t)`); this file supplies the series-level automorphism
it induces. For a continuous linear `L : K^n → K^n` and `f ∈ Conv K n`, the function
`evalSeries f ∘ L` is analytic at `0`, so the expansion of an analytic function into a convergent
series (`Hironaka/Analytic/ConvSeries/Bridge.lean`) gives it a coefficient family of finite
majorant norm: `substConv L f`. Uniqueness of the coefficient family makes `substConv L` a
`K`-algebra map (`substHom L`) and, for an invertible `L`, an automorphism (`substEquiv L`,
inverse `substHom L.symm`). `exists_substEquiv_isRegularIn` is the generic linear change
transported: every nonzero `f ∈ Conv K (m+1)` becomes `x_0`-regular of order `ord f` after some
linear change. These substitutions are used throughout the Nullstellensatz and the parametrization
theorem, and, on the stalks of an analytic space, throughout `Hironaka/Space` (the coherence
theorem, the dimension theory, the regular components).

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

@[expose] public section

open MvPowerSeries Filter
open scoped Topology

namespace Analytic

variable {K : Type*} [RCLike K]

variable {n : ℕ}

section Analytic

/-- The sum of a convergent series is analytic at `0`. -/
theorem analyticAt_evalSeries_zero {f : MvPowerSeries (Fin n) K} (hf : f ∈ Conv K n) :
    AnalyticAt K (evalSeries f) 0 := by
  obtain ⟨ρ, hρ⟩ := hf
  refine analyticOnNhd_evalSeries hρ 0 ?_
  intro k
  rw [Pi.zero_apply, norm_zero]
  exact NNReal.coe_pos.mpr (ρ.2 k)

/-- A convergent series composed with a linear map is analytic at `0`. -/
theorem analyticAt_evalSeries_comp {f : MvPowerSeries (Fin n) K} (hf : f ∈ Conv K n)
    (L : (Fin n → K) →L[K] (Fin n → K)) : AnalyticAt K (evalSeries f ∘ L) 0 := by
  have h := analyticAt_evalSeries_zero hf
  rw [← map_zero L] at h
  exact h.comp (L.analyticAt 0)

/-- Near `0`, `evalSeries` of a product is the product. -/
theorem evalSeries_mul_eventually {f g : MvPowerSeries (Fin n) K} (hf : f ∈ Conv K n)
    (hg : g ∈ Conv K n) :
    evalSeries (f * g) =ᶠ[𝓝 (0 : Fin n → K)] fun x => evalSeries f x * evalSeries g x := by
  obtain ⟨ρ, hρ⟩ := hf
  obtain ⟨ρ', hρ'⟩ := hg
  have hf' : ConvNorm (ρ.min ρ') f ≠ ⊤ :=
    ne_top_of_le_ne_top hρ (ConvNorm_mono (Radius.min_le_left ρ ρ') f)
  have hg' : ConvNorm (ρ.min ρ') g ≠ ⊤ :=
    ne_top_of_le_ne_top hρ' (ConvNorm_mono (Radius.min_le_right ρ ρ') g)
  filter_upwards [eventually_norm_sub_lt 0 (ρ.min ρ')] with x hx
  exact evalSeries_mul hf' hg' fun k => by simpa using (hx k).le

/-- Near `0`, `evalSeries` of a sum is the sum. -/
theorem evalSeries_add_eventually {f g : MvPowerSeries (Fin n) K} (hf : f ∈ Conv K n)
    (hg : g ∈ Conv K n) :
    evalSeries (f + g) =ᶠ[𝓝 (0 : Fin n → K)] fun x => evalSeries f x + evalSeries g x := by
  obtain ⟨ρ, hρ⟩ := hf
  obtain ⟨ρ', hρ'⟩ := hg
  have hf' : ConvNorm (ρ.min ρ') f ≠ ⊤ :=
    ne_top_of_le_ne_top hρ (ConvNorm_mono (Radius.min_le_left ρ ρ') f)
  have hg' : ConvNorm (ρ.min ρ') g ≠ ⊤ :=
    ne_top_of_le_ne_top hρ' (ConvNorm_mono (Radius.min_le_right ρ ρ') g)
  filter_upwards [eventually_norm_sub_lt 0 (ρ.min ρ')] with x hx
  exact evalSeries_add hf' hg' fun k => by simpa using (hx k).le

theorem evalSeries_C' (r : K) (x : Fin n → K) :
    evalSeries (C r : MvPowerSeries (Fin n) K) x = r := by
  rw [← congrFun MvPowerSeries.monomial_zero_eq_C r, evalSeries_monomial]
  simp [monomialEval]

/-- Two elements of `Conv K n` whose sums agree near `0` are equal (uniqueness of
coefficients). -/
theorem Conv.ext_of_evalSeries_eventuallyEq {f g : Conv K n}
    (h : evalSeries (f : MvPowerSeries (Fin n) K) =ᶠ[𝓝 0]
      evalSeries (g : MvPowerSeries (Fin n) K)) :
    f = g :=
  Subtype.ext (eq_of_evalSeries_eventuallyEq f.2 g.2 h)

theorem tendsto_clm_zero (L : (Fin n → K) →L[K] (Fin n → K)) :
    Tendsto L (𝓝 (0 : Fin n → K)) (𝓝 0) := by
  have := L.continuous.tendsto 0
  rwa [map_zero] at this

end Analytic

section Subst

/-- `evalSeries f ∘ L` is the sum of a convergent series near `0` (the expansion of an analytic
function). -/
theorem exists_substConv_spec (L : (Fin n → K) →L[K] (Fin n → K)) (f : Conv K n) :
    ∃ g : Conv K n, evalSeries (g : MvPowerSeries (Fin n) K) =ᶠ[𝓝 0]
      evalSeries (f : MvPowerSeries (Fin n) K) ∘ L := by
  obtain ⟨ρ, c, hc, hfc⟩ := AnalyticAt.exists_eventuallyEq_evalSeries
    (analyticAt_evalSeries_comp f.2 L)
  exact ⟨⟨c, mem_conv.mpr ⟨ρ, hc⟩⟩,
    (hfc.trans (Eventually.of_forall fun x => by simp only [sub_zero])).symm⟩

/-- The coefficient family at `0` of `evalSeries f ∘ L`, for `f ∈ Conv K n` and a continuous
linear `L`: the series `f(L x)` (the change of coordinates of [GR65, Chapter II, §B]). -/
noncomputable def substConv (L : (Fin n → K) →L[K] (Fin n → K)) (f : Conv K n) : Conv K n :=
  Classical.choose (exists_substConv_spec L f)

/-- The defining property of `substConv`: its sum is `evalSeries f ∘ L` near `0`. -/
theorem evalSeries_substConv (L : (Fin n → K) →L[K] (Fin n → K)) (f : Conv K n) :
    evalSeries (substConv L f : MvPowerSeries (Fin n) K) =ᶠ[𝓝 0]
      evalSeries (f : MvPowerSeries (Fin n) K) ∘ L :=
  Classical.choose_spec (exists_substConv_spec L f)

theorem substConv_one (L : (Fin n → K) →L[K] (Fin n → K)) : substConv L (1 : Conv K n) = 1 := by
  refine Conv.ext_of_evalSeries_eventuallyEq
    ((evalSeries_substConv L 1).trans (Eventually.of_forall fun x => ?_))
  simp only [Function.comp, Subalgebra.coe_one, evalSeries_one]

theorem substConv_mul (L : (Fin n → K) →L[K] (Fin n → K)) (f g : Conv K n) :
    substConv L (f * g) = substConv L f * substConv L g := by
  refine Conv.ext_of_evalSeries_eventuallyEq ((evalSeries_substConv L (f * g)).trans ?_)
  have h1 := (evalSeries_mul_eventually f.2 g.2).comp_tendsto (tendsto_clm_zero L)
  have h2 := evalSeries_mul_eventually (substConv L f).2 (substConv L g).2
  have h3 := evalSeries_substConv L f
  have h4 := evalSeries_substConv L g
  filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4
  simp only [Subalgebra.coe_mul, Function.comp] at hx1 hx2 hx3 hx4 ⊢
  rw [hx1, hx2, hx3, hx4]

theorem substConv_add (L : (Fin n → K) →L[K] (Fin n → K)) (f g : Conv K n) :
    substConv L (f + g) = substConv L f + substConv L g := by
  refine Conv.ext_of_evalSeries_eventuallyEq ((evalSeries_substConv L (f + g)).trans ?_)
  have h1 := (evalSeries_add_eventually f.2 g.2).comp_tendsto (tendsto_clm_zero L)
  have h2 := evalSeries_add_eventually (substConv L f).2 (substConv L g).2
  have h3 := evalSeries_substConv L f
  have h4 := evalSeries_substConv L g
  filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4
  simp only [Subalgebra.coe_add, Function.comp] at hx1 hx2 hx3 hx4 ⊢
  rw [hx1, hx2, hx3, hx4]

theorem substConv_algebraMap (L : (Fin n → K) →L[K] (Fin n → K)) (r : K) :
    substConv L (algebraMap K (Conv K n) r) = algebraMap K (Conv K n) r := by
  refine Conv.ext_of_evalSeries_eventuallyEq
    ((evalSeries_substConv L _).trans (Eventually.of_forall fun x => ?_))
  simp only [Function.comp, Subalgebra.coe_algebraMap, MvPowerSeries.algebraMap_apply,
    evalSeries_C']

/-- `f ↦ f ∘ L` as a `K`-algebra map of `Conv K n`. -/
noncomputable def substHom (L : (Fin n → K) →L[K] (Fin n → K)) : Conv K n →ₐ[K] Conv K n where
  toFun := substConv L
  map_one' := substConv_one L
  map_mul' := substConv_mul L
  map_zero' := by
    have := substConv_add L (0 : Conv K n) 0
    rw [add_zero] at this
    exact (add_eq_left.mp this.symm)
  map_add' := substConv_add L
  commutes' := substConv_algebraMap L

@[simp] theorem substHom_apply (L : (Fin n → K) →L[K] (Fin n → K)) (f : Conv K n) :
    substHom L f = substConv L f := rfl

theorem substConv_substConv (L L' : (Fin n → K) →L[K] (Fin n → K)) (f : Conv K n) :
    substConv L (substConv L' f) = substConv (L' ∘L L) f := by
  refine Conv.ext_of_evalSeries_eventuallyEq ((evalSeries_substConv L _).trans ?_)
  refine (((evalSeries_substConv L' f).comp_tendsto (tendsto_clm_zero L)).trans ?_).trans
    (evalSeries_substConv (L' ∘L L) f).symm
  exact Eventually.of_forall fun x => rfl

theorem substConv_id (f : Conv K n) : substConv (ContinuousLinearMap.id K (Fin n → K)) f = f :=
  Conv.ext_of_evalSeries_eventuallyEq ((evalSeries_substConv _ f).trans
    (Eventually.of_forall fun _ => rfl))

/-- A linear automorphism of `K^n` induces a `K`-algebra automorphism of `Conv K n`,
`f ↦ f ∘ L`. -/
noncomputable def substEquiv (L : (Fin n → K) ≃L[K] (Fin n → K)) : Conv K n ≃ₐ[K] Conv K n :=
  AlgEquiv.ofAlgHom (substHom (L : (Fin n → K) →L[K] (Fin n → K)))
    (substHom (L.symm : (Fin n → K) →L[K] (Fin n → K)))
    (AlgHom.ext fun f => by
      simp only [AlgHom.comp_apply, substHom_apply, AlgHom.id_apply]
      rw [substConv_substConv]
      have : ((L.symm : (Fin n → K) →L[K] (Fin n → K)) ∘L (L : (Fin n → K) →L[K] (Fin n → K))) =
          ContinuousLinearMap.id K (Fin n → K) :=
        ContinuousLinearMap.ext fun x => by simp
      rw [this]
      exact substConv_id f)
    (AlgHom.ext fun f => by
      simp only [AlgHom.comp_apply, substHom_apply, AlgHom.id_apply]
      rw [substConv_substConv]
      have : ((L : (Fin n → K) →L[K] (Fin n → K)) ∘L (L.symm : (Fin n → K) →L[K] (Fin n → K))) =
          ContinuousLinearMap.id K (Fin n → K) :=
        ContinuousLinearMap.ext fun x => by simp
      rw [this]
      exact substConv_id f)

@[simp] theorem substEquiv_apply (L : (Fin n → K) ≃L[K] (Fin n → K)) (f : Conv K n) :
    substEquiv L f = substConv (L : (Fin n → K) →L[K] (Fin n → K)) f := rfl

end Subst

section Regular

variable {m : ℕ}

/-- If the sum of `F ∈ Conv K (m+1)` restricted to the `x_0`-axis is `t^d e(t)` near `0` with
`e(0) ≠ 0`, then `F` is `x_0`-regular of order `d` (the printed `f_a(0, …, 0, x_m) ∼ x_m^e` of
[BM88, proof of Theorem 4.4, p. 24], read through the expansion on the axis). -/
theorem isRegularIn_of_eventually_axis {F : MvPowerSeries (Fin (m + 1)) K} (hF : F ∈ Conv K (m + 1))
    {d : ℕ} {e : K → K} (he : AnalyticAt K e 0) (he0 : e 0 ≠ 0)
    (hfe : ∀ᶠ t in 𝓝 (0 : K), evalSeries F (Pi.single 0 t) = t ^ d * e t) : IsRegularIn F d := by
  have he' : AnalyticAt K (fun y : Fin 1 → K => e (y 0)) 0 := by
    have hproj : AnalyticAt K (fun y : Fin 1 → K => y 0) 0 :=
      (ContinuousLinearMap.proj (R := K) (φ := fun _ : Fin 1 => K) (0 : Fin 1)).analyticAt 0
    exact he.comp_of_eq hproj rfl
  obtain ⟨ρE, E, hE, hEe⟩ := AnalyticAt.exists_conv_coeff he'
  simp only [zero_add] at hEe
  have hEConv : E ∈ Conv K 1 := ⟨ρE, hE⟩
  have hE0 : constantCoeff E ≠ 0 := by
    rw [← evalSeries_zero_eq, ← hEe 0 fun k => by
      rw [Pi.zero_apply, norm_zero]; exact_mod_cast ρE.pos k]
    exact he0
  have haxis : axis F = X 0 ^ d * E := by
    refine eq_of_evalSeries_eventuallyEq (axis_mem_conv hF)
      (mul_mem (pow_mem (X_mem_conv 0) d) hEConv) ?_
    have hproj0 : Tendsto (fun y : Fin 1 → K => y 0) (𝓝 0) (𝓝 0) :=
      (continuous_apply (0 : Fin 1)).tendsto (0 : Fin 1 → K)
    filter_upwards [hproj0.eventually hfe, eventually_abs_lt ρE] with y hy hyE
    calc evalSeries (axis F) y = evalSeries F (Pi.single 0 (y 0)) := evalSeries_axis F y
      _ = (y 0) ^ d * e (y 0) := hy
      _ = evalSeries (X 0 ^ d : MvPowerSeries (Fin 1) K) y * evalSeries E y := by
        rw [evalSeries_X_pow, hEe y hyE]
      _ = evalSeries (X 0 ^ d * E) y :=
        (evalSeries_mul (convNorm_X_pow_ne_top ρE 0 d) hE fun k => (hyE k).le).symm
  exact isRegularIn_of_axis_eq haxis hE0

/-- Every nonzero `f ∈ Conv K (m+1)` becomes `x_0`-regular of order `ord f` after a linear change
of variables: "there are local coordinates … such that `f_a(0, …, 0, x_m) ∼ x_m^e`"
[BM88, proof of Theorem 4.4, p. 24] (the generic linear change of
`Hironaka/Analytic/Germ/Axis.lean`, transported to `Conv`). -/
theorem exists_substEquiv_isRegularIn {f : Conv K (m + 1)} (hf0 : f ≠ 0) :
    ∃ L : (Fin (m + 1) → K) ≃L[K] (Fin (m + 1) → K),
      IsRegularIn (substEquiv L f : MvPowerSeries (Fin (m + 1)) K)
        (f : MvPowerSeries (Fin (m + 1)) K).order.toNat := by
  have hf0' : (f : MvPowerSeries (Fin (m + 1)) K) ≠ 0 := fun h => hf0 (Subtype.ext h)
  obtain ⟨L, e, he, he0, hfe⟩ := exists_linearChange_axis_regular f.2 hf0'
  refine ⟨L, isRegularIn_of_eventually_axis (substEquiv L f).2 he he0 ?_⟩
  have hsingle : Tendsto (fun t : K => (Pi.single (0 : Fin (m + 1)) t : Fin (m + 1) → K))
      (𝓝 0) (𝓝 0) := by
    have := (ContinuousLinearMap.single K (fun _ : Fin (m + 1) => K) 0).continuous.tendsto 0
    rwa [ContinuousLinearMap.single_apply, Pi.single_zero] at this
  filter_upwards [hsingle.eventually (evalSeries_substConv (L : (Fin (m + 1) → K) →L[K] _) f),
    hfe] with t ht hft
  rw [substEquiv_apply, ht]
  exact hft

end Regular

end Analytic
