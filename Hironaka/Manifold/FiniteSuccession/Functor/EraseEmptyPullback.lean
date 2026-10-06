/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmpty
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Deleting empty blow-ups commutes with pull-back along a surjective local isomorphism

The second bullet of [Kol07, 34.1] for the functor descended along a cover: the value of the
globalised functor on an open embedding `h` is read after pull-back along the surjective cover
`g₂` of the source, and `(h^* B(T)).eraseEmpty` pulled back along `g₂` must be
`(g₂^* h^* B(T)).eraseEmpty`; so **deleting empty blow-ups commutes with pull-back along a
surjective local analytic isomorphism** (`eraseEmpty_pullback`): a centre is empty iff its preimage
under a surjection is, and the transport of the cleaned tail along the analytic isomorphism
`Bl_∅ M ≃ M` of an empty blowing-up commutes with the pull-back because that transport is itself a
pull-back. The latter is `map_eq_pullback_symm`: the transport of a list along a diffeomorphism
`φ : A ≃ B` (`BlowUpSequence.map`, defined through `IsClosedSubmanifold.image_diffeomorph` and the
lifts `liftDiffeomorph`) is its pull-back along `φ⁻¹`, the two lifts to the blowings-up being the
same map over `φ⁻¹` (`liftStep_unique`) once the centres `φ(Y)` and `(φ⁻¹)⁻¹(Y)` are identified
(`cons_congr_heq`, `heq_pullback_of_heq`: the only place where two lists on the blowings-up of
propositionally equal centres are compared, by substitution of the set).
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### Comparing lists on the blowings-up of propositionally equal centres -/

/-- Two `cons` with
propositionally equal centres and heterogeneously equal tails are equal. -/
theorem cons_congr_heq {M : AnalyticManifold.{u} 𝕜 E} {Y₁ Y₂ : Set M} {c : ℕ} (e : Y₁ = Y₂)
    (h₁ : IsClosedSubmanifold ψ₀ Y₁ c) (h₂ : IsClosedSubmanifold ψ₀ Y₂ c)
    (r₁ : BlowUpSequence ψ₀ (blowUp ψ₀ h₁)) (r₂ : BlowUpSequence ψ₀ (blowUp ψ₀ h₂))
        (hr : HEq r₁ r₂) :
    cons h₁ r₁ = cons h₂ r₂ := by
  subst e
  obtain rfl := eq_of_heq hr
  rfl

/-- Pull-backs of a list
along heterogeneously equal maps out of the blowings-up of propositionally equal centres are
heterogeneously equal. -/
theorem heq_pullback_of_heq {M A : AnalyticManifold.{u} 𝕜 E} {Y₁ Y₂ : Set M} {c : ℕ}
    (e : Y₁ = Y₂) (h₁ : IsClosedSubmanifold ψ₀ Y₁ c) (h₂ : IsClosedSubmanifold ψ₀ Y₂ c)
    (Z : BlowUpSequence ψ₀ A) (f₁ : AnalyticMap (blowUp ψ₀ h₁) A) (f₂ : AnalyticMap
        (blowUp ψ₀ h₂) A)
    (hf₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f₁)
    (hf₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f₂) (hf : HEq f₁ f₂) :
    HEq (Z.pullback f₁ hf₁) (Z.pullback f₂ hf₂) := by
  subst e
  obtain rfl := eq_of_heq hf
  rfl

/-- A map over `h` from the blowing-up of a centre equal to `h⁻¹(Y)` to the blowing-up of `Y` is
the lift `liftStep` (`liftStep_unique`, up to the identification of the centres). -/
theorem heq_liftStep_of_forall {M N : AnalyticManifold.{u} 𝕜 E} (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) {S : Set N} (hS : IsClosedSubmanifold ψ₀ S c)
    (e : S = ⇑h ⁻¹' Y) (G : AnalyticMap (blowUp ψ₀ hS) (blowUp ψ₀ hY))
    (hcomm : ∀ q, blowUpπ ψ₀ hY (G q) = h (blowUpπ ψ₀ hS q)) : HEq G (liftStep h hh hY) := by
  subst e
  exact heq_of_eq
    (ContMDiffMap.ext (congrFun (liftStep_unique h hh hY G.contMDiff.continuous hcomm)))

/-! ### The transport along a diffeomorphism is a pull-back -/

/-- The diffeomorphism `φ : A ≃ B` as an analytic map. -/
abbrev _root_.Diffeomorph.toAnalyticMap {A B : AnalyticManifold.{u} 𝕜 E}
    (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) A B ω) : AnalyticMap A B :=
  ⟨⇑φ, φ.contMDiff⟩

/-- The inverse of the lift of `φ : A ≃ B` to the blowings-up
(`liftDiffeomorph`) is the pull-back lift of `φ⁻¹`, the centres `φ(Y)` and `(φ⁻¹)⁻¹(Y)`
identified. -/
theorem heq_liftDiffeomorph_symm {A B : AnalyticManifold.{u} 𝕜 E}
    (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) A B ω) {Y : Set A} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) :
    HEq (Diffeomorph.toAnalyticMap (liftDiffeomorph φ hY).symm)
      (liftStep (Diffeomorph.toAnalyticMap φ.symm) φ.symm.isLocalDiffeomorph hY) := by
  refine heq_liftStep_of_forall _ _ hY (hY.image_diffeomorph φ) ?_ _ fun q => ?_
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change φ.symm (φ y) ∈ Y
      rwa [Diffeomorph.symm_apply_apply]
    · intro hx
      exact ⟨φ.symm x, hx, φ.apply_symm_apply x⟩
  · have hspec : ∀ p, blowUpπ ψ₀ (hY.image_diffeomorph φ) (liftDiffeomorph φ hY p) =
        φ (blowUpπ ψ₀ hY p) := fun p => blowDown_liftPoint _ _ _ p
    have h1 := hspec ((liftDiffeomorph φ hY).symm q)
    rw [Diffeomorph.apply_symm_apply] at h1
    change blowUpπ ψ₀ hY ((liftDiffeomorph φ hY).symm q) = φ.symm (blowUpπ ψ₀ _ q)
    rw [h1, Diffeomorph.symm_apply_apply]

/-- The transport of a list along a diffeomorphism `φ : A ≃ B` (`map`) is its pull-back
along `φ⁻¹`. -/
theorem map_eq_pullback_symm : ∀ {A B : AnalyticManifold.{u} 𝕜 E} (Z : BlowUpSequence ψ₀ A)
    (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) A B ω),
    Z.map φ = Z.pullback (Diffeomorph.toAnalyticMap φ.symm) φ.symm.isLocalDiffeomorph
  | _, _, nil _, _ => rfl
  | _, _, @cons _ _ _ _ _ _ _ _ Y c hY rest, φ => by
    rw [map_cons, pullback_cons, map_eq_pullback_symm rest (liftDiffeomorph φ hY)]
    have e : ⇑φ '' Y = ⇑(Diffeomorph.toAnalyticMap φ.symm) ⁻¹' Y := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        change φ.symm (φ y) ∈ Y
        rwa [Diffeomorph.symm_apply_apply]
      · intro hx
        exact ⟨φ.symm x, hx, φ.apply_symm_apply x⟩
    exact cons_congr_heq e _ _ _ _
      (heq_pullback_of_heq e _ _ rest _ _ _ _ (heq_liftDiffeomorph_symm φ hY))

/-! ### `eraseEmpty` commutes with surjective pull-back -/

/-- [Kol07, 34.1] for a surjective local analytic isomorphism `g`:
**deleting the
empty blow-ups commutes with the pull-back along `g`** — a centre is empty iff its preimage is, and
the transport of the cleaned tail along the isomorphism of an empty blowing-up is a pull-back
(`map_eq_pullback_symm`), so the two sides are pull-backs of the cleaned tail along the two
composites `π⁻¹ ∘ g` and `g₁ ∘ π'⁻¹`, equal by the lift identity `π ∘ g₁ = g ∘ π'`. -/
theorem eraseEmpty_pullback : ∀ {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (g : AnalyticMap N M) (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g),
    Function.Surjective g → L.eraseEmpty.pullback g hg = (L.pullback g hg).eraseEmpty
  | _, _, nil _, _, _, _ => rfl
  | _, _, @cons _ _ _ _ _ _ _ _ Y c hY rest, g, hg, hs => by
    have hpre : ⇑g ⁻¹' Y = ∅ ↔ Y = ∅ :=
      ⟨fun h0 => Set.eq_empty_iff_forall_notMem.mpr fun y hy => by
          obtain ⟨x, rfl⟩ := hs y
          exact Set.eq_empty_iff_forall_notMem.mp h0 x hy,
        fun h0 => by rw [h0]; exact Set.preimage_empty⟩
    have hℓs := surjective_liftStep g hg hY hs
    rw [pullback_cons]
    by_cases hY₀ : Y = ∅
    · have hℓ := isLocalDiffeomorph_liftStep g hg hY
      set φ' := emptyBlowUpDiffeomorph (hY.preimage_of_isLocalDiffeomorph hg) (hpre.mpr hY₀)
      have hφ := (emptyBlowUpDiffeomorph hY hY₀).symm.isLocalDiffeomorph
      have hφ' := φ'.symm.isLocalDiffeomorph
      rw [eraseEmpty_cons_of_eq_empty hY rest hY₀,
        eraseEmpty_cons_of_eq_empty _ _ (hpre.mpr hY₀), ← eraseEmpty_pullback rest _ hℓ hℓs,
        map_eq_pullback_symm, map_eq_pullback_symm,
        pullback_comp _ _ hφ g hg, pullback_comp _ _ hℓ _ hφ']
      refine pullback_congr _ (ContMDiffMap.ext fun p => ?_) _ _
      have h1 : blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hg) (φ'.symm p) = p := by
        rw [← emptyBlowUpDiffeomorph_apply _ (hpre.mpr hY₀) (φ'.symm p)]
        exact φ'.apply_symm_apply p
      have h2 : g p = emptyBlowUpDiffeomorph hY hY₀ (liftStep g hg hY (φ'.symm p)) := by
        rw [emptyBlowUpDiffeomorph_apply, blowUpπ_liftStep, h1]
      change (emptyBlowUpDiffeomorph hY hY₀).symm (g p) = liftStep g hg hY (φ'.symm p)
      rw [h2, Diffeomorph.symm_apply_apply]
    · rw [eraseEmpty_cons_of_ne_empty hY rest hY₀,
        eraseEmpty_cons_of_ne_empty _ _ (fun h0 => hY₀ (hpre.mp h0)), pullback_cons,
        eraseEmpty_pullback rest _ _ hℓs]

end AnalyticManifold.BlowUpSequence

end
