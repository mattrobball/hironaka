/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Descent of a centre along a surjective local analytic isomorphism

In the proof of [Kol07, Proposition 37], the blow-up sequences `B(X')` and `B(X'')` start with
centres `Z₀' ⊂ X'` and `Z₀'' ⊂ X''`; since `B` commutes with the projections `τᵢ`,
`τ₁^*(Z₀') = Z₀'' = τ₂^*(Z₀')` (37.1), and the subschemes `Z₀ᵢ' ⊂ Uᵢ` glue to a subscheme
`Z₀ ⊂ X` (37.2). On manifolds: for a surjective local analytic isomorphism `g : N → M` with a
fibre product `(P, p₁, p₂)` of `g` with itself, the equation `p₁⁻¹(Z') = p₂⁻¹(Z')` says that `Z'`
is **saturated**, `g⁻¹(g(Z')) = Z'` (`saturated_of_isFibreProduct`); a saturated closed
submanifold descends: `g(Z')` is closed (its complement is `g(Z'ᶜ)`, open) and a closed
submanifold of the same codimension, its adapted charts the adapted charts of `Z'` transported
along local inverses of `g` (`transportChart`): `IsClosedSubmanifold.image_of_saturated`, the
gluing of (37.2).
-/

public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N P : AnalyticManifold.{u} 𝕜 E}

/-- Kollár (37.1)–(37.2): if the two pull-backs of `Z'` to a fibre product of `g` with itself
agree, `Z'` is saturated for `g`. -/
theorem saturated_of_isFibreProduct {g : AnalyticMap N M} {p₁ p₂ : AnalyticMap P N}
    (hp : IsFibreProduct g g p₁ p₂) {Z' : Set N} (hZ : p₁ ⁻¹' Z' = p₂ ⁻¹' Z') :
    g ⁻¹' (g '' Z') = Z' := by
  ext x
  refine ⟨fun hx => ?_, fun hx => mem_image_of_mem g hx⟩
  obtain ⟨z, hz, hgz⟩ := hx
  obtain ⟨w, ⟨hw₁, hw₂⟩, -⟩ := hp.2.2.2 x z hgz.symm
  have : w ∈ p₂ ⁻¹' Z' := by
    change p₂ w ∈ Z'
    rw [hw₂]
    exact hz
  rw [← hZ] at this
  change p₁ w ∈ Z' at this
  rwa [hw₁] at this

/-- A saturated set is the preimage of its image, so its complement's image is the complement of
its image (for surjective `g`). -/
theorem image_compl_of_saturated {g : N → M} (hs : Function.Surjective g) {Z' : Set N}
    (hsat : g ⁻¹' (g '' Z') = Z') : g '' Z'ᶜ = (g '' Z')ᶜ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ hy
    exact hx (hsat ▸ (hy : g x ∈ g '' Z'))
  · intro hy
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨x, fun hx => hy (mem_image_of_mem g hx), rfl⟩

/-- The image of a saturated set under a local inverse `Φ` of `g` is the image of the set. -/
theorem image_partialDiffeomorph_eq_of_saturated {g : AnalyticMap N M}
    (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N M ω) (hΦ : EqOn g Φ Φ.source) {Z' : Set N}
    (hsat : g ⁻¹' (g '' Z') = Z') : Φ '' (Z' ∩ Φ.source) = g '' Z' ∩ Φ.target := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxZ, hxΦ⟩, rfl⟩
    refine ⟨⟨x, hxZ, hΦ hxΦ⟩, Φ.map_source hxΦ⟩
  · rintro ⟨⟨z, hz, rfl⟩, hyΦ⟩
    refine ⟨Φ.toPartialEquiv.symm (g z), ⟨?_, Φ.toPartialEquiv.map_target hyΦ⟩,
      Φ.toPartialEquiv.right_inv hyΦ⟩
    have h1 : g (Φ.toPartialEquiv.symm (g z)) = g z := by
      rw [hΦ (Φ.toPartialEquiv.map_target hyΦ)]
      exact Φ.toPartialEquiv.right_inv hyΦ
    rw [← hsat]
    change g (Φ.toPartialEquiv.symm (g z)) ∈ g '' Z'
    rw [h1]
    exact mem_image_of_mem g hz

/-- Kollár (37.2), the subschemes `Z₀ᵢ' ⊂ Uᵢ` glue to a subscheme `Z₀ ⊂ X`: the image
of a saturated closed submanifold under a surjective local analytic isomorphism is a closed
submanifold of the same codimension — closed because its complement is the image of the open
complement, with adapted charts transported along local inverses. -/
theorem IsClosedSubmanifold.image_of_saturated {g : AnalyticMap N M}
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) (hs : Function.Surjective g) {Z' : Set N}
    {c : ℕ} (hZ' : IsClosedSubmanifold ψ₀ Z' c) (hsat : g ⁻¹' (g '' Z') = Z') :
    IsClosedSubmanifold ψ₀ (g '' Z') c where
  isClosed := by
    rw [← isOpen_compl_iff, ← image_compl_of_saturated hs hsat]
    exact hg.isOpenMap _ hZ'.isClosed.isOpen_compl
  exists_adaptedChart := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨Φ, hxΦ, hΦ⟩ := (hg x).exists_partialDiffeomorph
    obtain ⟨φ, σ, hxφ, hφ⟩ := hZ'.exists_adaptedChart x hx
    refine ⟨transportChart Φ φ, σ, ?_,
      isAdaptedChart_transportChart Φ (image_partialDiffeomorph_eq_of_saturated Φ hΦ hsat) hφ⟩
    rw [transportChart_source]
    refine ⟨?_, ?_⟩
    · rw [hΦ hxΦ]
      exact Φ.map_source hxΦ
    · change Φ.invFun (g x) ∈ φ.source
      rw [hΦ hxΦ]
      change Φ.toPartialEquiv.symm (Φ.toPartialEquiv x) ∈ φ.source
      rw [Φ.toPartialEquiv.left_inv hxΦ]
      exact hxφ

end Manifold

end
