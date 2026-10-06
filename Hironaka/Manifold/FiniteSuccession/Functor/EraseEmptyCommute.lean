/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.PushforwardPullback
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Deleting empty blow-ups commutes with pull-back and push-forward, up to a final deletion

`eraseEmpty_pullback` deletes empty blow-ups before or after a surjective local analytic
isomorphism with the same result. Along a non-surjective local isomorphism the pull-back may
create new empty centres (a nonempty centre with empty preimage), so both sides must be cleaned
at the end:

* `BlowUpSequence.eraseEmpty_pullback_eraseEmpty`:
  `(L.eraseEmpty.pullback h hh).eraseEmpty = (L.pullback h hh).eraseEmpty` for every local
  analytic isomorphism `h` ([Kol07, 34.1]);
* `BlowUpSequence.eraseEmpty_pushforward_eraseEmpty`:
  `((L.eraseEmpty).pushforward hS).eraseEmpty = (L.pushforward hS).eraseEmpty`
  ([Kol07, Definition 30, 30.3]): the push-forward of an empty centre is empty, and the
  push-forward from the next stage is, along the isomorphism of the empty blowing-up, the
  push-forward from the given stage (`pushforwardAux_pullback` with the identification of the
  empty blowing-up with its base, `IsPullbackStage` for the empty centre).

The counterpart for schemes is `AlgebraicGeometry.eraseEmpty_pullback_eraseEmpty'` of
`Hironaka.Scheme.BlowUpSequence.EraseEmptyTransport`. These are used for the non-surjective bullet
of [Kol07, 34.1] for the functors built by descent.
-/

public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### Pull-back -/

/-- [Kol07, 34.1] along any local analytic isomorphism `h`: deleting the empty
blow-ups of `L` and then pulling back, or pulling back first, give the same list after a final
deletion of empty blow-ups — a nonempty centre may have an empty preimage, which the final
deletion removes. The counterpart for schemes is
`AlgebraicGeometry.eraseEmpty_pullback_eraseEmpty'`, the same statement for blow-up sequences of
schemes. -/
theorem eraseEmpty_pullback_eraseEmpty : ∀ {M N : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h),
    (L.eraseEmpty.pullback h hh).eraseEmpty = (L.pullback h hh).eraseEmpty
  | _, _, nil _, _, _ => rfl
  | _, _, @cons _ _ _ _ _ _ _ _ Y c hY rest, h, hh => by
    have hℓ := isLocalDiffeomorph_liftStep h hh hY
    by_cases hY₀ : Y = ∅
    · have hpre : ⇑h ⁻¹' Y = ∅ := by rw [hY₀]; exact Set.preimage_empty
      set φ := emptyBlowUpDiffeomorph hY hY₀
      set φ' := emptyBlowUpDiffeomorph (hY.preimage_of_isLocalDiffeomorph hh) hpre
      have hφ := φ.symm.isLocalDiffeomorph
      have hφ' := φ'.symm.isLocalDiffeomorph
      rw [eraseEmpty_cons_of_eq_empty hY rest hY₀, pullback_cons,
        eraseEmpty_cons_of_eq_empty _ _ hpre, ← eraseEmpty_pullback_eraseEmpty rest _ hℓ,
        map_eq_pullback_symm, map_eq_pullback_symm,
        eraseEmpty_pullback (rest.eraseEmpty.pullback _ hℓ) _ hφ'
          (fun p => ⟨φ' p, φ'.symm_apply_apply p⟩),
        pullback_comp _ _ hφ h hh, pullback_comp _ _ hℓ _ hφ']
      congr 1
      refine pullback_congr _ (ContMDiffMap.ext fun p => ?_) _ _
      have h1 : blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh) (φ'.symm p) = p := by
        rw [← emptyBlowUpDiffeomorph_apply _ hpre (φ'.symm p)]
        exact φ'.apply_symm_apply p
      have h2 : h p = φ (liftStep h hh hY (φ'.symm p)) := by
        rw [emptyBlowUpDiffeomorph_apply, blowUpπ_liftStep, h1]
      change φ.symm (h p) = liftStep h hh hY (φ'.symm p)
      rw [h2, Diffeomorph.symm_apply_apply]
    · rw [eraseEmpty_cons_of_ne_empty hY rest hY₀, pullback_cons, pullback_cons]
      by_cases hpre : ⇑h ⁻¹' Y = ∅
      · rw [eraseEmpty_cons_of_eq_empty _ _ hpre, eraseEmpty_cons_of_eq_empty _ _ hpre,
          eraseEmpty_pullback_eraseEmpty rest _ hℓ]
      · rw [eraseEmpty_cons_of_ne_empty _ _ hpre, eraseEmpty_cons_of_ne_empty _ _ hpre,
          eraseEmpty_pullback_eraseEmpty rest _ hℓ]

/-! ### Push-forward -/

variable {s : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The pushed-forward centre is empty iff the centre is. -/
theorem imageVal_image_eq_empty_iff {Tᵢ : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)}
    (P : PushforwardStage ψ s Tᵢ) (Z : Set Tᵢ) :
    P.isClosedSubmanifold.imageVal (P.iso '' Z) = ∅ ↔ Z = ∅ := by
  rw [P.imageVal_image_eq, Set.image_eq_empty]

/-- The identification of the blowing-up along an empty pushed-forward centre with the stage. -/
theorem isPullbackStage_emptyBlowUp {Tᵢ : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)}
    (P : PushforwardStage ψ s Tᵢ) {Z : Set Tᵢ} {c : ℕ}
    (hZ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c) (hZ₀ : Z = ∅) :
    PushforwardStage.IsPullbackStage (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)) P
      (Diffeomorph.toAnalyticMap (emptyBlowUpDiffeomorph (P.isClosedSubmanifold_imageVal_image hZ)
        ((imageVal_image_eq_empty_iff P Z).mpr hZ₀)).symm)
      (Diffeomorph.toAnalyticMap (emptyBlowUpDiffeomorph hZ hZ₀).symm) := by
  set hY₁ := P.isClosedSubmanifold_imageVal_image hZ
  set hY₀ := (imageVal_image_eq_empty_iff P Z).mpr hZ₀
  set φ := emptyBlowUpDiffeomorph hY₁ hY₀ with hφ_def
  have hφπ : ∀ p, φ p = blowUpπ ψ hY₁ p := emptyBlowUpDiffeomorph_apply hY₁ hY₀
  refine ⟨φ.symm.isLocalDiffeomorph, ?_, fun q => ?_⟩
  · -- `P.sub = φ.symm ⁻¹' (closure (π ⁻¹' (P.sub \ ∅)))`, `π = φ` a homeomorphism
    change P.sub = ⇑φ.symm ⁻¹' strictTransformSet (blowUpπ ψ hY₁) _ P.sub
    unfold strictTransformSet
    have hπφ : ⇑(blowUpπ ψ hY₁) = ⇑φ := funext fun p => (hφπ p).symm
    have hdiff : P.sub \ P.isClosedSubmanifold.imageVal (P.iso '' Z) = P.sub := by
      rw [hY₀, Set.sdiff_empty]
    have hid : ⇑φ ∘ ⇑φ.symm = id := funext fun x => φ.apply_symm_apply x
    have hopen : IsOpenMap (⇑φ.symm) := φ.symm.toHomeomorph.isOpenMap
    rw [hπφ, hdiff, hopen.preimage_closure_eq_closure_preimage φ.symm.continuous,
      ← Set.preimage_comp, hid, Set.preimage_id, P.isClosedSubmanifold.isClosed.closure_eq]
  · -- the square: both sides blow down to `P.incl q`
    have hinj : Function.Injective (⇑φ) := fun a b hab => φ.toEquiv.injective hab
    refine hinj ?_
    change φ ((P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)).incl
        ((emptyBlowUpDiffeomorph hZ hZ₀).symm q)) =
      φ (φ.symm (P.incl q))
    rw [φ.apply_symm_apply]
    refine (hφπ _).trans ?_
    rw [PushforwardStage.blowUpπ_incl_blowUpStep]
    exact congrArg P.incl ((emptyBlowUpDiffeomorph_apply hZ hZ₀ _).symm.trans
      ((emptyBlowUpDiffeomorph hZ hZ₀).apply_symm_apply q))

/-- [Kol07, Definition 30, 30.3] with 34.1: the push-forward of a list with its empty blow-ups
deleted has, after a final deletion, the empty blow-ups of the push-forward deleted — by induction
through `pushforwardAux`, the empty first centre pushing forward to an empty centre and the
push-forward from the next stage being the push-forward from the given stage along the isomorphism
of the empty blowing-up (`pushforwardAux_pullback`). -/
theorem eraseEmpty_pushforwardAux_eraseEmpty :
    ∀ {Tᵢ : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)} (P : PushforwardStage ψ s Tᵢ)
      (L : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Tᵢ),
      (pushforwardAux P L.eraseEmpty).eraseEmpty = (pushforwardAux P L).eraseEmpty
  | _, _, nil _ => rfl
  | _, P, @cons _ _ _ _ _ _ _ _ Z c hZ rest => by
    by_cases hZ₀ : Z = ∅
    · have hY₀ : P.isClosedSubmanifold.imageVal (P.iso '' Z) = ∅ :=
        (imageVal_image_eq_empty_iff P Z).mpr hZ₀
      have hinv := isPullbackStage_emptyBlowUp P hZ hZ₀
      rw [eraseEmpty_cons_of_eq_empty hZ rest hZ₀, map_eq_pullback_symm,
        ← PushforwardStage.pushforwardAux_pullback _ P _ _
          (emptyBlowUpDiffeomorph hZ hZ₀).symm.isLocalDiffeomorph hinv rest.eraseEmpty,
        ← eraseEmpty_pullback _ _ hinv.isLocalDiffeomorph
          (emptyBlowUpDiffeomorph _ hY₀).symm.toEquiv.surjective,
        eraseEmpty_pushforwardAux_eraseEmpty (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)) rest]
      change _ = (cons (P.isClosedSubmanifold_imageVal_image hZ)
        (pushforwardAux (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)) rest)).eraseEmpty
      rw [eraseEmpty_cons_of_eq_empty (P.isClosedSubmanifold_imageVal_image hZ)
        (pushforwardAux (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)) rest) hY₀, map_eq_pullback_symm]
      rfl
    · have hY₀ : P.isClosedSubmanifold.imageVal (P.iso '' Z) ≠ ∅ :=
        fun h0 => hZ₀ ((imageVal_image_eq_empty_iff P Z).mp h0)
      rw [eraseEmpty_cons_of_ne_empty hZ rest hZ₀]
      change (cons (P.isClosedSubmanifold_imageVal_image hZ)
          (pushforwardAux (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)) rest.eraseEmpty)).eraseEmpty =
        (cons (P.isClosedSubmanifold_imageVal_image hZ)
          (pushforwardAux (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)) rest)).eraseEmpty
      rw [eraseEmpty_cons_of_ne_empty (P.isClosedSubmanifold_imageVal_image hZ)
          (pushforwardAux (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)) rest.eraseEmpty) hY₀,
        eraseEmpty_cons_of_ne_empty (P.isClosedSubmanifold_imageVal_image hZ)
          (pushforwardAux (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)) rest) hY₀]
      exact congrArg _
        (eraseEmpty_pushforwardAux_eraseEmpty (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)) rest)

/-- **Deleting empty blow-ups commutes with the push-forward along a closed submanifold
([Kol07, Definition 30, 30.3]) up to a final deletion**: `((L.eraseEmpty).pushforward
hS).eraseEmpty = (L.pushforward hS).eraseEmpty`.
-/
theorem eraseEmpty_pushforward_eraseEmpty {M : AnalyticManifold.{u} 𝕜 E} {S : Set M}
    (hS : IsClosedSubmanifold ψ S s)
    (L : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) hS.toAnalyticManifold) :
    (L.eraseEmpty.pushforward hS).eraseEmpty = (L.pushforward hS).eraseEmpty :=
  eraseEmpty_pushforwardAux_eraseEmpty _ L

end AnalyticManifold.BlowUpSequence

end
