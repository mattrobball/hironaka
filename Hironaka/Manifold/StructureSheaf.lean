/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Sheaf.ContMDiff
public import Hironaka.Analytic.ConvSeries.Eval
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Hironaka.Manifold.Sheaf.LocalRing
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The structure sheaf of analytic functions: evaluation, constants, charts

The stalk `𝒪_{M,a}` of the structure sheaf `structureSheaf 𝕜 E M` of an analytic manifold (the
`n = ω` case of `contMDiffSheafCommRing`, the sheaf of "regular functions" of Bierstone–Milman's
regular coordinate charts [BM97, (0.3)], which for an analytic manifold is the sheaf of analytic
functions [BM97, §3, "Regular coordinate charts"]) is a local ring with the evaluation
`eval 𝕜 E M a : 𝒪_{M,a} →+* 𝕜`. This module provides, besides `eval`:

* `analyticGermsAt 𝕜 E b`, the ring `𝒪_{E,b}` of germs at `b ∈ E` of functions analytic at `b`,
  as a subring of `(𝓝 b).Germ 𝕜`, and the specification `IsChartTransport φ a e` of the chart
  transport `e : 𝒪_{M,a} ≃+* 𝒪_{E,φ(a)}`, `f ↦ f ∘ φ⁻¹`, in a chart `φ` at `a` (any chart of the
  maximal atlas whose source contains `a`; the transport is `chartTransport`);
* the constants `const 𝕜 E M a : 𝕜 →+* 𝒪_{M,a}`, the germs at `a` of the constant sections
  `constHom`, and the extension by zero `extendSection` of a section to a function on `M`;
* for `𝕜 ∈ {ℝ, ℂ}` and coordinates `ψ : E ≃L[𝕜] (Fin n → 𝕜)`: the specification
  `IsTaylorHom ψ φ a T` of the Taylor homomorphism `T_a : 𝒪_{M,a} →+* 𝕜[[X₁, …, Xₙ]]` of
  [BM97, (0.3)] (`T_a f` is the convergent power series of `f ∘ φ⁻¹ ∘ ψ⁻¹` at `ψ(φ(a))`), the
  formal partial derivatives `pderivGerm` on analytic germs (on power series they are Mathlib's
  `MvPowerSeries.pderiv`),
  and the values of the coordinate germs `coord ψ φ hφ ha i` (the germs `x_i = ψ_i ∘ φ ∈ 𝒪_{M,a}`
  of a chart) and of the constants (`eval_const`, `eval_coord`), the maximal ideal
  `𝔪_a = ker (ev_a)` (`mem_maximalIdeal_iff_eval`) and `x_i − x_i(a) ∈ 𝔪_a`
  (`coord_sub_mem_maximalIdeal`).

The field lives in `Type` and the manifold in `Type u`: Mathlib's stalk API needs the sheaf of
rings in `CommRingCat.{u}` over `TopCat.of M`. The Taylor homomorphism, its injectivity and its
description of the powers of the maximal ideal are constructed in `Hironaka/Manifold/Germ/`;
the ideal sheaves of `𝒪_M`, the objects of the analytic main theorems, are built on this sheaf
(`Hironaka/Manifold/IdealSheaf/`).
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

section General

variable (𝕜 : Type) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] (M : Type u) [TopologicalSpace M] [ChartedSpace E M]

/-- The evaluation `ev_a : 𝒪_{M,a} →+* 𝕜` at the point `a`. -/
def eval (a : M) : (structureSheaf 𝕜 E M).presheaf.stalk a →+* 𝕜 :=
  contMDiffSheafCommRing.eval 𝓘(𝕜, E) 𝓘(𝕜) ω M 𝕜 a

/-- The stalk `𝒪_{M,a}` is a local ring (`Hironaka/Manifold/Sheaf/LocalRing.lean`, as an
instance for the structure sheaf). -/
instance structureSheaf.instLocalRing_stalk (a : M) :
    IsLocalRing ((structureSheaf 𝕜 E M).presheaf.stalk a) :=
  contMDiffSheafCommRing.instLocalRing_stalk 𝓘(𝕜, E) ω M a

variable {M}

/-- **The ring `𝒪_{E,b}` of analytic germs** at `b ∈ E`: the subring of `Filter.Germ (𝓝 b) 𝕜` of
germs of functions analytic at `b`. -/
def analyticGermsAt (b : E) : Subring ((𝓝 b).Germ 𝕜) where
  carrier := {g | ∃ f : E → 𝕜, g = ↑f ∧ AnalyticAt 𝕜 f b}
  mul_mem' := by
    rintro _ _ ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
    exact ⟨f * g, rfl, hf.mul hg⟩
  one_mem' := ⟨fun _ => 1, rfl, analyticAt_const⟩
  add_mem' := by
    rintro _ _ ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
    exact ⟨f + g, rfl, hf.add hg⟩
  zero_mem' := ⟨fun _ => 0, rfl, analyticAt_const⟩
  neg_mem' := by
    rintro _ ⟨f, rfl, hf⟩
    exact ⟨-f, rfl, hf.neg⟩

/-- The extension by zero of a section of `𝒪_M` over `U` to a function on `M` (`extendBy0` for
the structure sheaf). -/
abbrev extendSection {U : Opens M} (f : (structureSheaf 𝕜 E M).presheaf.obj (op U)) : M → 𝕜 :=
  extendBy0 𝓘(𝕜, E) ω M f

@[simp]
theorem extendSection_of_mem {U : Opens M} (f : (structureSheaf 𝕜 E M).presheaf.obj (op U))
    {x : M} (hx : x ∈ U) : extendSection 𝕜 E f x = f ⟨x, hx⟩ :=
  extendBy0_of_mem 𝓘(𝕜, E) ω M f hx

/-- The specification of **the chart transport of germs** in a chart `φ` at `a`: a ring
isomorphism `e : 𝒪_{M,a} ≃+* 𝒪_{E, φ(a)}` is the chart transport when it sends the germ of every
section `f` to the germ at `φ(a)` of `f ∘ φ⁻¹` (`f` extended by zero off its domain). Any chart of
the maximal atlas whose source contains `a` is admitted; `chartAt E a` is the special case. -/
def IsChartTransport (φ : OpenPartialHomeomorph M E) (a : M)
    (e : (structureSheaf 𝕜 E M).presheaf.stalk a ≃+* analyticGermsAt 𝕜 E (φ a)) : Prop :=
  ∀ (U : Opens M) (hU : a ∈ U) (f : (structureSheaf 𝕜 E M).presheaf.obj (op U)),
    (e ((structureSheaf 𝕜 E M).presheaf.germ U a hU f) : (𝓝 (φ a)).Germ 𝕜) =
      ↑(extendSection 𝕜 E f ∘ φ.symm)

variable (M) in
/-- The constants: the germ at `a` of the constant section `c`, as a ring homomorphism
`𝕜 →+* 𝒪_{M,a}` — the composite of `constHom` with the germ at `a`. -/
def const (a : M) : 𝕜 →+* (structureSheaf 𝕜 E M).presheaf.stalk a :=
  ((structureSheaf 𝕜 E M).presheaf.germ ⊤ a trivial).hom.comp (constHom 𝕜 E M)

theorem const_apply (a : M) (c : 𝕜) :
    const 𝕜 E M a c = (structureSheaf 𝕜 E M).presheaf.germ ⊤ a trivial (constSection 𝕜 E M c) :=
  rfl

end General

section RCLike

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))

/-- The specification of **the Taylor homomorphism** `T_a : 𝒪_{M,a} →+* 𝕜[[X₁, …, Xₙ]]` in a
chart `φ` at `a` with coordinates `ψ` [BM97, (0.3)]: every value is a convergent power series
(`Analytic.Conv 𝕜 n`), and `T_a f` is the power series of `f ∘ φ⁻¹ ∘ ψ⁻¹` at
`ψ(φ(a))`, i.e. that function agrees near `ψ(φ(a))` with `y ↦ (T_a f)(y - ψ(φ(a)))`
(`Analytic.evalSeries`). -/
def IsTaylorHom (φ : OpenPartialHomeomorph M E) (a : M)
    (T : (structureSheaf 𝕜 E M).presheaf.stalk a →+* MvPowerSeries (Fin n) 𝕜) : Prop :=
  (∀ s, T s ∈ Analytic.Conv 𝕜 n) ∧
    ∀ (U : Opens M) (hU : a ∈ U) (f : (structureSheaf 𝕜 E M).presheaf.obj (op U)),
      (extendSection 𝕜 E f ∘ φ.symm ∘ ψ.symm) =ᶠ[𝓝 (ψ (φ a))]
        fun y => Analytic.evalSeries
          (T ((structureSheaf 𝕜 E M).presheaf.germ U a hU f)) (y - ψ (φ a))

/-- The partial derivative `∂_i g` of an analytic germ `g` at `b ∈ E` in the direction of the
`i`-th coordinate vector `ψ⁻¹(e_i)`: the germ of `y ↦ Dg(y)(ψ⁻¹ e_i)`. -/
def pderivGerm (i : Fin n) (b : E) (g : analyticGermsAt 𝕜 E b) : analyticGermsAt 𝕜 E b :=
  ⟨Quotient.liftOn' g.1 (fun f => (↑(fun y => fderiv 𝕜 f y (ψ.symm (Pi.single i 1))) :
      (𝓝 b).Germ 𝕜)) (fun f g hfg => by
        refine Quotient.sound' ?_
        filter_upwards [(hfg : f =ᶠ[𝓝 b] g).eventually_nhds] with y hy
        rw [(show f =ᶠ[𝓝 y] g from hy).fderiv_eq]), by
    obtain ⟨g0, hg0⟩ := g
    obtain ⟨f, rfl, hfa⟩ := hg0
    exact ⟨fun y => fderiv 𝕜 f y (ψ.symm (Pi.single i 1)), rfl,
      ((ContinuousLinearMap.apply 𝕜 𝕜 (ψ.symm (Pi.single i 1))).analyticAt _).comp hfa.fderiv⟩⟩

end RCLike

/-! ### Evaluation of the constants and of the coordinate germs -/

section Eval

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))
  (φ : OpenPartialHomeomorph M E) {a : M} (ha : a ∈ φ.source) (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M)

open IsLocalRing

/-- A constant germ evaluates to the constant. -/
@[simp]
theorem eval_const (c : 𝕜) : eval 𝕜 E M a (const 𝕜 E M a c) = c :=
  contMDiffSheafCommRing.eval_germ 𝓘(𝕜, E) 𝓘(𝕜) ω M 𝕜 ⊤ a trivial (constSection 𝕜 E M c)

/-- The coordinate germ `x_i` evaluates to `x_i(a)`. -/
@[simp]
theorem eval_coord (i : Fin n) : eval 𝕜 E M a (coord E ψ φ hφ ha i) = ψ (φ a) i :=
  contMDiffSheafCommRing.eval_germ 𝓘(𝕜, E) 𝓘(𝕜) ω M 𝕜 _ a ha (chartSection E ψ φ hφ i)

/-- For the structure sheaf: `𝔪_a = ker (ev_a)`. -/
theorem mem_maximalIdeal_iff_eval (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    s ∈ maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) ↔ eval 𝕜 E M a s = 0 := by
  rw [show maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) = RingHom.ker (eval 𝕜 E M a) from
    contMDiffSheafCommRing.maximalIdeal_stalk 𝓘(𝕜, E) ω M a, RingHom.mem_ker]

/-- `x_i − x_i(a) ∈ 𝔪_a`. -/
theorem coord_sub_mem_maximalIdeal (i : Fin n) :
    coord E ψ φ hφ ha i - const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hφ ha i)) ∈
      maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) :=
  (mem_maximalIdeal_iff_eval E _).mpr (by rw [map_sub, eval_const, sub_self])

end Eval

end Manifold
