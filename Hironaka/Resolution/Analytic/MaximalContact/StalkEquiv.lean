/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.LocalDiffeomorph
public import Hironaka.Manifold.IdealSheaf.Deriv
import Hironaka.Algebra.Derivative.Equiv
import Hironaka.Manifold.IdealSheaf.DerivLemmas
public import Hironaka.Manifold.IdealSheaf.GermMapChainRule
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The stalk map of a local analytic isomorphism; derivatives commute with local isomorphisms

For an analytic map `h : N → M` that is a local analytic isomorphism at `b`, the stalk map
`h^* = germMap h b : 𝒪_{M, h b} →+* 𝒪_{N, b}` has the stalk map of a local inverse as a two-sided
inverse (the argument of `IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt`) and fixes the
constants, so it is a `𝕜`-algebra isomorphism `germAlgEquiv`. Consequently the derivative ideal
sheaves commute with the pull-back along a local analytic isomorphism: `h^*(D^r J) = D^r(h^*J)`
(`comap_iteratedDeriv`) — Kollár's "if `f : Y → X` is smooth, then `D(f^*I) = f^*(D(I))`"
[Kol07, Lemma 74 (4)], for local analytic isomorphisms; in particular `MC(h^*I) = h^*MC(I)` for
`MC = D^{m−1}` (`comap_iteratedDeriv_pred`), the identity behind condition (4′) of
[Kol07, Definition 91] and condition (2) of [Kol07, Definition 96], where `MC(ψ^*I)` appears.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory Set Filter Topology
open scoped Manifold ContDiff

universe u v

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M N : AnalyticManifold.{u} 𝕜 E}

section Equiv

variable (h : AnalyticMap N M) {b : N} (hb : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω h b)

/-- The stalk map of a local inverse of `h` at `b`: `𝒪_{N, b} →+* 𝒪_{M, h b}`. -/
def germMapInv :
    (structureSheaf 𝕜 E N).presheaf.stalk b →+* (structureSheaf 𝕜 E M).presheaf.stalk (h b) :=
  germMapOn hb.exists_partialDiffeomorph.choose.invFun
    (V := ⟨hb.exists_partialDiffeomorph.choose.target,
      hb.exists_partialDiffeomorph.choose.open_target⟩)
    hb.exists_partialDiffeomorph.choose.contMDiffOn_invFun
    (by
      have heq := hb.exists_partialDiffeomorph.choose_spec.2
        hb.exists_partialDiffeomorph.choose_spec.1
      rw [heq]
      exact hb.exists_partialDiffeomorph.choose.map_source
        hb.exists_partialDiffeomorph.choose_spec.1)
    (by
      have heq := hb.exists_partialDiffeomorph.choose_spec.2
        hb.exists_partialDiffeomorph.choose_spec.1
      rw [heq]
      exact hb.exists_partialDiffeomorph.choose.left_inv
        hb.exists_partialDiffeomorph.choose_spec.1)

theorem germMapInv_comp_germMap :
    (germMapInv h hb).comp (germMap (⇑h) h.contMDiff b) = RingHom.id _ := by
  set Φ := hb.exists_partialDiffeomorph.choose with hΦdef
  have hbΦ : b ∈ Φ.source := hb.exists_partialDiffeomorph.choose_spec.1
  have heq : EqOn (⇑h) Φ Φ.source := hb.exists_partialDiffeomorph.choose_spec.2
  refine RingHom.ext fun t => stalkToGerm_injective 𝓘(𝕜, E) ω M (h b) ?_
  rw [RingHom.comp_apply, germMapInv, stalkToGerm_germMapOn, stalkToGerm_germMap, RingHom.id_apply]
  induction stalkToGerm 𝓘(𝕜, E) ω M (h b) t using Germ.inductionOn with
  | h k =>
    rw [Germ.coe_compTendsto, Germ.coe_compTendsto]
    refine Germ.coe_eq.mpr ?_
    have hφb : h b ∈ Φ.target := heq hbΦ ▸ Φ.map_source hbΦ
    filter_upwards [Φ.open_target.mem_nhds hφb] with y hy
    simp only [Function.comp_apply]
    have hmem : Φ.invFun y ∈ Φ.source := Φ.map_target hy
    have hri : Φ.toPartialEquiv (Φ.invFun y) = y := Φ.right_inv hy
    rw [heq hmem, hri]

theorem germMap_comp_germMapInv :
    (germMap (⇑h) h.contMDiff b).comp (germMapInv h hb) = RingHom.id _ := by
  set Φ := hb.exists_partialDiffeomorph.choose with hΦdef
  have hbΦ : b ∈ Φ.source := hb.exists_partialDiffeomorph.choose_spec.1
  have heq : EqOn (⇑h) Φ Φ.source := hb.exists_partialDiffeomorph.choose_spec.2
  refine RingHom.ext fun t => stalkToGerm_injective 𝓘(𝕜, E) ω N b ?_
  rw [RingHom.comp_apply, germMapInv, stalkToGerm_germMap, stalkToGerm_germMapOn, RingHom.id_apply]
  induction stalkToGerm 𝓘(𝕜, E) ω N b t using Germ.inductionOn with
  | h k =>
    rw [Germ.coe_compTendsto, Germ.coe_compTendsto]
    refine Germ.coe_eq.mpr ?_
    filter_upwards [Φ.open_source.mem_nhds hbΦ] with x hx
    simp only [Function.comp_apply]
    rw [heq hx]
    exact congrArg k (Φ.left_inv hx)

/-- The stalk map of a local analytic isomorphism at `b` as a ring isomorphism (the inverse is the
stalk map of a local inverse of `h`). -/
def germRingEquiv :
    (structureSheaf 𝕜 E M).presheaf.stalk (h b) ≃+* (structureSheaf 𝕜 E N).presheaf.stalk b where
  toFun := germMap (⇑h) h.contMDiff b
  invFun := germMapInv h hb
  left_inv s := RingHom.congr_fun (germMapInv_comp_germMap h hb) s
  right_inv t := RingHom.congr_fun (germMap_comp_germMapInv h hb) t
  map_mul' := map_mul _
  map_add' := map_add _

/-- The stalk map of a local analytic isomorphism at `b`, as a `𝕜`-algebra isomorphism
`𝒪_{M, h b} ≃ₐ[𝕜] 𝒪_{N, b}` (the inverse is the stalk map of a local inverse of `h`). -/
def germAlgEquiv :
    (structureSheaf 𝕜 E M).presheaf.stalk (h b) ≃ₐ[𝕜] (structureSheaf 𝕜 E N).presheaf.stalk b :=
  AlgEquiv.ofRingEquiv (f := germRingEquiv h hb) (germMap_algebraMap (⇑h) h.contMDiff b)

theorem germAlgEquiv_apply (s : (structureSheaf 𝕜 E M).presheaf.stalk (h b)) :
    germAlgEquiv h hb s = germMap (⇑h) h.contMDiff b s := rfl

end Equiv

section Deriv

variable [FiniteDimensional 𝕜 E] (h : AnalyticMap N M)
  (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)

omit [FiniteDimensional 𝕜 E] in
/-- The stalk of the pull-back along a local analytic isomorphism, through the algebra
isomorphism. -/
theorem stalkIdeal_comap_eq_map_germAlgEquiv (J : AnalyticManifold.IdealSheaf M) (b : N) :
    (J.pullback h h.contMDiff).stalkIdeal b =
      (J.stalkIdeal (h b)).map (germAlgEquiv h (hh b)) := by
  rw [IdealSheaf.stalkIdeal_pullback]
  rfl

include hh in
/-- Kollár's "if `f : Y → X` is smooth, then `D(f^*I) = f^*(D(I))`" [Kol07, Lemma 74 (4)] for local
analytic isomorphisms: `h^*(D^r J) = D^r(h^*J)`. -/
theorem comap_iteratedDeriv (J : AnalyticManifold.IdealSheaf M) (r : ℕ) :
    (J.iteratedDeriv r).pullback h h.contMDiff =
      (J.pullback h h.contMDiff).iteratedDeriv r := by
  refine IdealSheaf.ext fun b => ?_
  rw [IdealSheaf.stalkIdeal_iteratedDeriv, stalkIdeal_comap_eq_map_germAlgEquiv h hh,
    stalkIdeal_comap_eq_map_germAlgEquiv h hh, IdealSheaf.stalkIdeal_iteratedDeriv,
    Ideal.derivativeIter_map_algEquiv]

include hh in
/-- `MC(h^*I) = h^*MC(I)` for a local analytic isomorphism `h`. -/
theorem comap_iteratedDeriv_pred (I : AnalyticManifold.IdealSheaf M) (m : ℕ) :
    (I.pullback h h.contMDiff).iteratedDeriv (m - 1) =
      (I.iteratedDeriv (m - 1)).pullback h h.contMDiff :=
  (comap_iteratedDeriv h hh I (m - 1)).symm

end Deriv

end Hironaka.Manifold

end
