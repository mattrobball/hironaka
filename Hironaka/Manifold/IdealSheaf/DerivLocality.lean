/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Deriv
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.IdealSheaf.DerivLemmas
import Hironaka.Manifold.IdealSheaf.GermMapChainRule
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.LocalDiffeomorph
import Hironaka.Scheme.BlowUpSequence.TransformDerivative
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial
/-!
# Locality of the derivative ideal sheaves

Kollár's `D(f^*I) = f^*(D(I))` for a smooth morphism `f` [Kol07, Lemma 74 (4)], proved here for the
maps the `Hironaka` library needs — local analytic isomorphisms, in particular the inclusion of
an open subset (the "local question" clause at the start of the proof of [Kol07, Theorem 80]) and
the blow-down off the centre. At a point `b` where `φ` is a local analytic isomorphism the germ map
`𝒪_{M, φ b} → 𝒪_{N, b}` is a ring isomorphism respecting `𝕜`
(`germMap_bijective_of_isLocalDiffeomorphAt`), and `Ideal.derivative_map_ringEquiv` transports
Kollár's derivative ideal along it; the derivative ideal sheaves are determined by their stalks
(`stalkIdeal_deriv`). Hence `D^j(φ^* J) = φ^*(D^j(J))` for a local analytic isomorphism
(`iteratedDeriv_pullback_of_isLocalDiffeomorph`) and `D^j(J|_U) = (D^j J)|_U` for an open subset
(`iteratedDeriv_restrictOpens`).

Also here, for local analytic isomorphisms: the vanishing ideal of a preimage along a
diffeomorphism is the image of the vanishing ideal under the germ map
(`vanishingStalk_preimage_diffeomorph`), the local-generator condition of the vanishing ideals is
invariant under a diffeomorphism (`hasLocalGenerators_vanishingStalk_preimage_iff`), and an
inequality of stalks at a point of the range of a local analytic isomorphism can be checked after
pulling back (`IdealSheaf.stalkIdeal_le_of_comap_le`). These are the transport lemmas used when
the resolution is built on charts and open subsets and glued
(`Hironaka/Resolution/Analytic/Functor/PullbackTransport.lean`,
`Hironaka/Resolution/Analytic/MaximalContactTheorem.lean`).
-/

public section

noncomputable section

open TopologicalSpace Filter
open scoped Manifold ContDiff Topology

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] {N : Type u} [TopologicalSpace N] [ChartedSpace E N]
  [IsManifold 𝓘(𝕜, E) ω N] (φ : N → M) (hφ : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω φ)
  (J : IdealSheaf (structureSheaf 𝕜 E M))

/-- At a point where the germ map is bijective, the stalk of `D(φ^* J)` is the stalk of
`φ^*(D(J))` (`Ideal.derivative_map_ringEquiv`). -/
theorem stalkIdeal_deriv_pullback_of_bijective {b : N}
    (hb : Function.Bijective (germMap φ hφ b)) :
    (J.pullback φ hφ).deriv.stalkIdeal b = (J.deriv.pullback φ hφ).stalkIdeal b := by
  rw [IdealSheaf.stalkIdeal_deriv, IdealSheaf.stalkIdeal_pullback, IdealSheaf.stalkIdeal_pullback,
    IdealSheaf.stalkIdeal_deriv]
  have h := Ideal.derivative_map_ringEquiv (RingEquiv.ofBijective _ hb)
    (fun a => germMap_algebraMap φ hφ b a) (J.stalkIdeal (φ b))
  have he : (RingEquiv.ofBijective _ hb).toRingHom = germMap φ hφ b := RingHom.ext fun _ => rfl
  rw [he] at h
  exact h.symm

/-- If the germ map is bijective at every point, `D(φ^* J) = φ^*(D(J))`. -/
theorem deriv_pullback_of_bijective (hb : ∀ b, Function.Bijective (germMap φ hφ b)) :
    (J.pullback φ hφ).deriv = J.deriv.pullback φ hφ :=
  IdealSheaf.ext fun b => stalkIdeal_deriv_pullback_of_bijective φ hφ J (hb b)

/-- If the germ map is bijective at every point, `D^j(φ^* J) = φ^*(D^j(J))`. -/
theorem iteratedDeriv_pullback_of_bijective (hb : ∀ b, Function.Bijective (germMap φ hφ b))
    (j : ℕ) : (J.pullback φ hφ).iteratedDeriv j = (J.iteratedDeriv j).pullback φ hφ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [IdealSheaf.iteratedDeriv_succ, ih, deriv_pullback_of_bijective φ hφ _ hb,
      IdealSheaf.iteratedDeriv_succ]

omit [FiniteDimensional 𝕜 E] [IsManifold 𝓘(𝕜, E) ω M] [IsManifold 𝓘(𝕜, E) ω N] J in
/-- At a point where `φ` is a local analytic isomorphism, the germ map is bijective: the germ map
of a local inverse is a two-sided inverse. -/
theorem germMap_bijective_of_isLocalDiffeomorphAt {b : N}
    (h : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω φ b) : Function.Bijective (germMap φ hφ b) := by
  obtain ⟨Φ, hbΦ, heq⟩ := h.exists_partialDiffeomorph
  have hφb : φ b ∈ Φ.target := heq hbΦ ▸ Φ.map_source hbΦ
  have hinv : Φ.invFun (φ b) = b := by rw [heq hbΦ]; exact Φ.left_inv hbΦ
  set g := germMapOn Φ.invFun (V := ⟨Φ.target, Φ.open_target⟩) Φ.contMDiffOn_invFun hφb hinv
    with hg
  have hcomp : g.comp (germMap φ hφ b) = RingHom.id _ := by
    refine RingHom.ext fun t => stalkToGerm_injective 𝓘(𝕜, E) ω M (φ b) ?_
    rw [RingHom.comp_apply, hg, stalkToGerm_germMapOn, stalkToGerm_germMap, RingHom.id_apply]
    induction stalkToGerm 𝓘(𝕜, E) ω M (φ b) t using Germ.inductionOn with
    | h k =>
      rw [Germ.coe_compTendsto, Germ.coe_compTendsto]
      refine Germ.coe_eq.mpr ?_
      filter_upwards [Φ.open_target.mem_nhds hφb] with y hy
      simp only [Function.comp_apply]
      have hmem : Φ.invFun y ∈ Φ.source := Φ.map_target hy
      have hri : Φ.toPartialEquiv (Φ.invFun y) = y := Φ.right_inv hy
      rw [heq hmem, hri]
  have hcomp' : (germMap φ hφ b).comp g = RingHom.id _ := by
    refine RingHom.ext fun t => stalkToGerm_injective 𝓘(𝕜, E) ω N b ?_
    rw [RingHom.comp_apply, stalkToGerm_germMap, hg, stalkToGerm_germMapOn, RingHom.id_apply]
    induction stalkToGerm 𝓘(𝕜, E) ω N b t using Germ.inductionOn with
    | h k =>
      rw [Germ.coe_compTendsto, Germ.coe_compTendsto]
      refine Germ.coe_eq.mpr ?_
      filter_upwards [Φ.open_source.mem_nhds hbΦ] with y hy
      simp only [Function.comp_apply]
      rw [heq hy]
      exact congrArg k (Φ.left_inv hy)
  refine ⟨Function.LeftInverse.injective (g := g) fun t => ?_,
    Function.RightInverse.surjective (g := g) fun t => ?_⟩
  · rw [← RingHom.comp_apply, hcomp, RingHom.id_apply]
  · rw [← RingHom.comp_apply, hcomp', RingHom.id_apply]

/-- Locality of `D` ([Kol07, Lemma 74 (4)] at a point where `φ` is a local analytic isomorphism):
the stalk of `D(φ^* J)` at `b` is the stalk of `φ^*(D(J))`. -/
theorem stalkIdeal_deriv_pullback_of_isLocalDiffeomorphAt {b : N}
    (hb : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω φ b) :
    (J.pullback φ hφ).deriv.stalkIdeal b = (J.deriv.pullback φ hφ).stalkIdeal b :=
  stalkIdeal_deriv_pullback_of_bijective φ hφ J (germMap_bijective_of_isLocalDiffeomorphAt φ hφ hb)

/-- Locality of `D` ([Kol07, Lemma 74 (4)] for a local analytic isomorphism `φ`):
`D^j(φ^* J) = φ^*(D^j(J))`. -/
theorem iteratedDeriv_pullback_of_isLocalDiffeomorph
    (hloc : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω φ) (j : ℕ) :
    (J.pullback φ hφ).iteratedDeriv j = (J.iteratedDeriv j).pullback φ hφ :=
  iteratedDeriv_pullback_of_bijective φ hφ J
    (fun b => germMap_bijective_of_isLocalDiffeomorphAt φ hφ (hloc b)) j


/-! ### The vanishing ideals along a diffeomorphism -/

section VanishingTransport

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M₁ M₂ : AnalyticManifold.{u} 𝕜 E} (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M₁ M₂ ω)

/-- Along a diffeomorphism the vanishing ideal of the preimage is the image of the vanishing ideal
under the (bijective) germ map. -/
theorem vanishingStalk_preimage_diffeomorph (Z : Set M₂) (x : M₁) :
    vanishingStalk (𝕜 := 𝕜) (E := E) (⇑g ⁻¹' Z) x =
      Ideal.map (germMap ⇑g g.contMDiff x) (vanishingStalk (𝕜 := 𝕜) (E := E) Z (g x)) := by
  rw [← comap_germMap_vanishingStalk g Z x]
  exact (Ideal.map_comap_of_surjective _
    (germMap_bijective_of_isLocalDiffeomorphAt ⇑g g.contMDiff (g.isLocalDiffeomorph x)).2 _).symm

/-- Local generators of the vanishing ideals transport along a diffeomorphism (the pullback of the
ideal sheaf they define). -/
theorem hasLocalGenerators_vanishingStalk_preimage_of (W : Set M₂)
    (h : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M₂) fun y : M₂ =>
      vanishingStalk (𝕜 := 𝕜) (E := E) W y) :
    IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M₁) fun x : M₁ =>
      vanishingStalk (𝕜 := 𝕜) (E := E) (⇑g ⁻¹' W) x := by
  have := hasLocalGenerators_pullback ⇑g g.contMDiff (IdealSheaf.ofStalks _ _ h)
  refine (congrArg IdealSheaf.HasLocalGenerators (funext fun x => ?_)).mp this
  rw [IdealSheaf.stalkIdeal_ofStalks, vanishingStalk_preimage_diffeomorph]

/-- The local-generator condition of the vanishing ideals is invariant under a diffeomorphism. -/
theorem hasLocalGenerators_vanishingStalk_preimage_iff (W : Set M₂) :
    IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M₁) (fun x : M₁ =>
      vanishingStalk (𝕜 := 𝕜) (E := E) (⇑g ⁻¹' W) x) ↔
    IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M₂) fun y : M₂ =>
      vanishingStalk (𝕜 := 𝕜) (E := E) W y := by
  refine ⟨fun h => ?_, hasLocalGenerators_vanishingStalk_preimage_of g W⟩
  have := hasLocalGenerators_vanishingStalk_preimage_of g.symm (⇑g ⁻¹' W) h
  refine (congrArg IdealSheaf.HasLocalGenerators (funext fun y => ?_)).mp this
  congr 1
  ext z
  simp only [Set.mem_preimage, Diffeomorph.apply_symm_apply]

end VanishingTransport

end Manifold

namespace AnalyticManifold.IdealSheaf

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E}

/-- Locality of `D` for the inclusion of an open subset ([Kol07, Lemma 74 (4)]; "being a
hypersurface of maximal contact is a local question", [Kol07, Theorem 80, proof]): the derivative
ideal sheaves of the restriction of `J` to an open `U` are the restrictions of the derivative
ideal sheaves of `J`, `D^j(J|_U) = (D^j J)|_U` (the germ map of the inclusion is bijective,
`germMap_val_bijective`). -/
theorem iteratedDeriv_restrictOpens (J : IdealSheaf M) (U : Opens M) (j : ℕ) :
    (J.restrict U).iteratedDeriv j = restrict (J.iteratedDeriv j) U :=
  iteratedDeriv_pullback_of_bijective _ _ J (fun p => germMap_val_bijective (𝕜 := 𝕜) (E := E) U p) j

end AnalyticManifold.IdealSheaf

/-! ### Stalk inequalities along a local isomorphism -/

namespace Manifold


variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M N : AnalyticManifold.{u} 𝕜 E}

/-- An inequality of stalks at a point of the range of a local analytic isomorphism `g` can be
checked after pulling back along `g`: the germ map is bijective. -/
theorem IdealSheaf.stalkIdeal_le_of_comap_le {g : AnalyticMap N M}
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) {A B : AnalyticManifold.IdealSheaf M} (y : N)
    (h : (A.pullback g g.contMDiff).stalkIdeal y ≤ (B.pullback g g.contMDiff).stalkIdeal y) :
    A.stalkIdeal (g y) ≤ B.stalkIdeal (g y) := by
  have hbij := germMap_bijective_of_isLocalDiffeomorphAt (⇑g) g.contMDiff (hg y)
  change (A.pullback ⇑g g.contMDiff).stalkIdeal y ≤ (B.pullback ⇑g g.contMDiff).stalkIdeal y at h
  rw [IdealSheaf.stalkIdeal_pullback, IdealSheaf.stalkIdeal_pullback] at h
  calc A.stalkIdeal (g y) = ((A.stalkIdeal (g y)).map (germMap (⇑g) g.contMDiff y)).comap _ :=
        (Ideal.comap_map_of_bijective _ hbij).symm
    _ ≤ ((B.stalkIdeal (g y)).map (germMap (⇑g) g.contMDiff y)).comap _ := Ideal.comap_mono h
    _ = B.stalkIdeal (g y) := Ideal.comap_map_of_bijective _ hbij

end Manifold

end
