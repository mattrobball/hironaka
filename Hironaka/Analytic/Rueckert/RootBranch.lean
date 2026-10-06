/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The analytic root branch through a simple root

The analytic implicit function theorem behind the local parametrization theorem
[GR84, Chapter 3, §1], in one dependent variable: for `Φ₂(u, t)` analytic near `(u₀, t₀)` with
`Φ₂(u₀, t₀) = 0` and `∂_t Φ₂(u₀, t₀) ≠ 0`, there is an analytic `τ` near `u₀` with `τ(u₀) = t₀`,
`Φ₂(u, τ(u)) = 0`, and every zero `(u, t)` of `Φ₂` near `(u₀, t₀)` has `t = τ(u)`.

Mathlib has the inverse function theorem for `C^n` maps at every level `n`, including `ω`
(analytic), but no separate multivariable implicit function theorem for analytic maps; the branch
is therefore obtained from the local inverse `Ψ` of the joint map `Φ(u, t) = (u, Φ₂(u, t))`
(`ContDiffAt.localInverse` at level `ω`, `ContDiffAt.to_localInverse` for its analyticity,
`ContDiffAt.analyticAt`), as `τ(u) := (Ψ(u, 0))₂`. The derivative of `Φ` at `(u₀, t₀)` is
`(v, s) ↦ (v, DΦ₂(v, s))`, injective because `DΦ₂(0, s) = s · ∂_t Φ₂(u₀, t₀)`, hence bijective in
finite dimension (`ContinuousLinearEquiv.ofBijective`).
-/

public section

open scoped ContDiff
open Filter Topology

namespace Analytic

variable {d : ℕ}

/-- The analytic implicit function theorem in one dependent variable, from Mathlib's `C^ω` inverse
function theorem for the joint map `(u, t) ↦ (u, Φ₂(u, t))`: a simple zero `(u₀, t₀)` of an
analytic `Φ₂` (`∂_t Φ₂(u₀, t₀) = c ≠ 0`) lies on an analytic root branch `τ`, and near `(u₀, t₀)`
the zeros of `Φ₂` are exactly the points of the branch. -/
theorem exists_analytic_root_branch {Φ₂ : (Fin d → ℂ) × ℂ → ℂ} {u₀ : Fin d → ℂ} {t₀ c : ℂ}
    (hΦ : AnalyticAt ℂ Φ₂ (u₀, t₀)) (h0 : Φ₂ (u₀, t₀) = 0)
    (hder : HasDerivAt (fun t => Φ₂ (u₀, t)) c t₀) (hc : c ≠ 0) :
    ∃ τ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ τ u₀ ∧ τ u₀ = t₀ ∧ (∀ᶠ u in 𝓝 u₀, Φ₂ (u, τ u) = 0) ∧
      ∀ᶠ p in 𝓝 (u₀, t₀), Φ₂ p = 0 → p.2 = τ p.1 := by
  set a : (Fin d → ℂ) × ℂ := (u₀, t₀) with ha
  set Φ : (Fin d → ℂ) × ℂ → (Fin d → ℂ) × ℂ := fun p => (p.1, Φ₂ p) with hΦdef
  have hΦa : AnalyticAt ℂ Φ a := analyticAt_fst.prod hΦ
  -- the partial derivative in `t`
  have hD₂ : fderiv ℂ Φ₂ a (0, 1) = c := by
    have h1 : HasDerivAt (fun t => Φ₂ (u₀, t)) (fderiv ℂ Φ₂ a (0, 1)) t₀ := by
      have := hΦ.hasStrictFDerivAt.hasFDerivAt.comp_hasDerivAt t₀
        (hasFDerivAt_prodMk_right u₀ t₀).hasDerivAt
      exact this
    exact h1.unique hder
  -- the derivative of the joint map and its injectivity
  have hfd : fderiv ℂ Φ a = (ContinuousLinearMap.fst ℂ (Fin d → ℂ) ℂ).prod (fderiv ℂ Φ₂ a) :=
    (hasFDerivAt_fst.prodMk hΦ.hasStrictFDerivAt.hasFDerivAt).fderiv
  have hDapply : ∀ v : (Fin d → ℂ) × ℂ, fderiv ℂ Φ a v = (v.1, fderiv ℂ Φ₂ a v) := fun v => by
    rw [hfd, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst']
  have hinj : Function.Injective (fderiv ℂ Φ a) := by
    intro v w hvw
    rw [hDapply, hDapply, Prod.mk.injEq] at hvw
    obtain ⟨h1, h2⟩ := hvw
    have h3 : fderiv ℂ Φ₂ a (v - w) = 0 := by rw [map_sub, h2, sub_self]
    have h4 : v - w = (v.2 - w.2) • ((0 : Fin d → ℂ), (1 : ℂ)) := by
      ext
      · simp [h1]
      · simp
    rw [h4, map_smul, hD₂, smul_eq_mul, mul_eq_zero] at h3
    rcases h3 with h3 | h3
    · exact Prod.ext h1 (sub_eq_zero.mp h3)
    · exact absurd h3 hc
  have hker : LinearMap.ker (fderiv ℂ Φ a : (Fin d → ℂ) × ℂ →ₗ[ℂ] (Fin d → ℂ) × ℂ) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  have hrange : LinearMap.range (fderiv ℂ Φ a : (Fin d → ℂ) × ℂ →ₗ[ℂ] (Fin d → ℂ) × ℂ) = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hinj)
  let D' : ((Fin d → ℂ) × ℂ) ≃L[ℂ] ((Fin d → ℂ) × ℂ) :=
    ContinuousLinearEquiv.ofBijective (fderiv ℂ Φ a) hker hrange
  have hD' : HasFDerivAt Φ (D' : (Fin d → ℂ) × ℂ →L[ℂ] (Fin d → ℂ) × ℂ) a := by
    rw [ContinuousLinearEquiv.coe_ofBijective]
    exact hΦa.hasStrictFDerivAt.hasFDerivAt
  -- the local inverse at level `ω`
  have hcont : ContDiffAt ℂ ω Φ a := hΦa.contDiffAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := WithTop.top_ne_zero
  set Ψ := hcont.localInverse hD' hn with hΨdef
  have hΨ : AnalyticAt ℂ Ψ (Φ a) := (hcont.to_localInverse hD' hn).analyticAt
  have hΨa : Ψ (Φ a) = a := hcont.localInverse_apply_image hD' hn
  have hΦa0 : Φ a = (u₀, 0) := by
    change (a.1, Φ₂ a) = (u₀, 0)
    rw [h0, ha]
  have hstrict : HasStrictFDerivAt Φ (D' : (Fin d → ℂ) × ℂ →L[ℂ] (Fin d → ℂ) × ℂ) a :=
    hcont.hasStrictFDerivAt' hD' hn
  have hleft : ∀ᶠ p in 𝓝 a, Ψ (Φ p) = p := hstrict.eventually_left_inverse
  have hright : ∀ᶠ y in 𝓝 (Φ a), Φ (Ψ y) = y := hstrict.eventually_right_inverse
  refine ⟨fun u => (Ψ (u, 0)).2, ?_, ?_, ?_, ?_⟩
  · -- analyticity of the branch
    have h1 : AnalyticAt ℂ (fun u : Fin d → ℂ => Ψ (u, 0)) u₀ := by
      rw [hΦa0] at hΨ
      exact hΨ.comp₂ analyticAt_id analyticAt_const
    exact analyticAt_snd.comp h1
  · -- the branch passes through `(u₀, t₀)`
    change (Ψ (u₀, 0)).2 = t₀
    rw [← hΦa0, hΨa]
  · -- the branch consists of zeros
    have hright' : ∀ᶠ y in 𝓝 (u₀, (0 : ℂ)), Φ (Ψ y) = y := by rwa [hΦa0] at hright
    have hcont' : ContinuousAt (fun u : Fin d → ℂ => (u, (0 : ℂ))) u₀ :=
      ContinuousAt.prodMk continuousAt_id continuousAt_const
    filter_upwards [hcont'.tendsto.eventually hright'] with u hu
    have h1 : (Ψ (u, 0)).1 = u := congrArg Prod.fst hu
    have h2 : Φ₂ (Ψ (u, 0)) = 0 := congrArg Prod.snd hu
    have h3 : (u, (Ψ (u, 0)).2) = Ψ (u, 0) := Prod.ext h1.symm rfl
    change Φ₂ (u, (Ψ (u, 0)).2) = 0
    rw [h3]
    exact h2
  · -- uniqueness of the zero near `(u₀, t₀)`
    filter_upwards [hleft] with p hp hΦp
    have hΦp' : Φ p = (p.1, 0) := by rw [hΦdef]; simp [hΦp]
    change p.2 = (Ψ (p.1, 0)).2
    rw [← hΦp', hp]

end Analytic
