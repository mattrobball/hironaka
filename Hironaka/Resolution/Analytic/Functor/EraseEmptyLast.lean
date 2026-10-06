/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.EraseEmptyConcat
public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
import Hironaka.Manifold.BlowUp.Transform.Bundled
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.Weak
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.PullbackTransport
import Hironaka.Resolution.Analytic.MaximalContact.MarkedOneLemmas
import Hironaka.Resolution.Analytic.MaximalContactLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The last-stage transforms along the deletion of empty blow-ups

Deleting the empty blow-ups of a list `L` ([Kol07, 34.1], `BlowUpSequence.eraseEmpty`) identifies
the
last stages along `BlowUpSequence.eraseEmptyLast`
(`Hironaka.Resolution.Analytic.Functor.EraseEmptyConcat`). This file transports the last-stage
data along that identification: **the weak transform**, **the marked transform** (for a list whose
markings are legitimate) and **the strict transform** at the last stage of the cleaned list are the
pull-backs along `eraseEmptyLast⁻¹` of those of the list (`weakTransformSeq_last_eraseEmpty`,
`markedTransformSeq_last_eraseEmpty`, `strictTransformSeq_last_eraseEmpty`; the counterparts for
schemes are in `Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced`).

The proofs are by recursion on the list. A kept step contributes the same transform on both
sides (`cons_*Aux_succ`). A deleted step contributes, on the list's side, the transform along an
**empty blowing-up**: the exceptional ideal sheaf is the unit ideal sheaf, so the marked and weak
transforms are the total transform (`birationalTransform_I_of_eq_empty`,
`weakTransformOf_of_eq_empty`), and the strict transform of a closed set is its preimage
(`strictTransformSet_empty_of_isClosed`); on the cleaned list's side it contributes the transport
of the cleaned tail along the isomorphism `Bl_∅ M ≃ M`, i.e. along `BlowUpSequence.map`. The
transports along `map` (`*_last_map`) are themselves by recursion, each step the naturality of the
one-step transform along the lift `liftDiffeomorph` of the isomorphism, obtained from the
naturalities along `liftStep` (`Hironaka.Resolution.Analytic.Functor.PullbackTransport`) by the
uniqueness of lifts (`*_of_square`).

The marked transport needs the markings to be legitimate along the list, i.e. the order clause
of [Kol07, Definition 66] alone (`FiniteSuccession.IsMarkedGe`, implied by `IsOfOrderGe`); its
normal-crossings clause plays no role, so the marked transport is stated for any `IsOfOrderGe`
boundary.
-/

@[expose] public section

noncomputable section

open Set Topology AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The transforms along an empty blowing-up -/

section EmptyStep

variable {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}

/-- The ideal sheaf of the empty submanifold is the unit ideal sheaf. -/
theorem _root_.Manifold.IsClosedSubmanifold.idealSheaf_eq_top_of_eq_empty
    (hY : IsClosedSubmanifold ψ₀ Y c)
    (hY₀ : Y = ∅) : hY.idealSheaf = ⊤ :=
  IdealSheaf.eq_top_of_support_eq_empty (hY.cosupport_idealSheaf.trans hY₀)

/-- Division by the unit ideal sheaf changes nothing: the colon by `⊤ ^ m` is the ideal itself. -/
theorem _root_.Manifold.IdealSheaf.isDivExceptional_top (Itot : AnalyticManifold.IdealSheaf M)
    (m : M → ℕ) :
    IdealSheaf.IsDivExceptional Itot ⊤ m Itot := fun a => by
  rw [IdealSheaf.stalkIdeal_top, Ideal.top_pow, Submodule.top_coe, Submodule.colon_univ]

variable {M' : AnalyticManifold.{u} 𝕜 E} {π : M' → M}

/-- Kollár (60.1) along an empty blowing-up: the exceptional ideal sheaf is the unit ideal
sheaf, so the marked transform is the total transform. -/
theorem _root_.Manifold.MarkedIdealSheaf.birationalTransform_I_of_eq_empty
    (hY : IsClosedSubmanifold ψ₀ Y c)
    (hY₀ : Y = ∅) (h : IsBlowUp ψ₀ Y c π) (J : MarkedIdealSheaf (structureSheaf 𝕜 E M)) :
    (MarkedIdealSheaf.birationalTransform hY h J).I = J.I.pullback π h.contMDiff := by
  have hE : hY.idealSheaf.pullback π h.contMDiff = ⊤ := by
    rw [hY.idealSheaf_eq_top_of_eq_empty hY₀, IdealSheaf.pullback_top]
  have hdiv : IdealSheaf.IsDivExceptional (J.I.pullback π h.contMDiff)
      (hY.idealSheaf.pullback π h.contMDiff) (fun _ => J.m) (J.I.pullback π h.contMDiff) := by
    rw [hE]
    exact IdealSheaf.isDivExceptional_top _ _
  exact IsDivExceptional.unique (isDivExceptional_birationalTransform hY h J fun a ha =>
    absurd (hY₀ ▸ ha) (Set.notMem_empty a)) hdiv

/-- Hironaka's weak transform [Hir64, Ch. 0, §5, p. 142] along an empty blowing-up: the weak
transform is the total transform. -/
theorem _root_.Manifold.IdealSheaf.weakTransformOf_of_eq_empty (hY : IsClosedSubmanifold ψ₀ Y c)
    (hY₀ : Y = ∅)
    (h : IsBlowUp ψ₀ Y c π) (I : AnalyticManifold.IdealSheaf M) :
    IdealSheaf.weakTransformOf hY h I = I.pullback π h.contMDiff := by
  have hE : hY.idealSheaf.pullback π h.contMDiff = ⊤ := by
    rw [hY.idealSheaf_eq_top_of_eq_empty hY₀, IdealSheaf.pullback_top]
  have hdiv : IdealSheaf.IsDivExceptional (I.pullback π h.contMDiff)
      (hY.idealSheaf.pullback π h.contMDiff)
      (fun a' => (IdealSheaf.genericOrdAlong hY.idealSheaf I (π a')).toNat)
      (I.pullback π h.contMDiff) := by
    rw [hE]
    exact IdealSheaf.isDivExceptional_top _ _
  exact IsDivExceptional.unique (isDivExceptional_weakTransformOf hY h I) hdiv

/-- The strict transform of a closed set under a blowing-up along the empty centre is its
preimage (the closure of the preimage of the complement of the centre, here everything). -/
theorem strictTransformSet_empty_of_isClosed {M' : Type u} [TopologicalSpace M'] {π : M' → M}
    (hπ : Continuous π) {H : Set M} (hH : IsClosed H) :
    strictTransformSet π (∅ : Set M) H = π ⁻¹' H := by
  unfold strictTransformSet
  rw [Set.sdiff_empty, (hH.preimage hπ).closure_eq]

/-- The bundled weak transform along the chosen blowing-up of an empty centre is the
pull-back. -/
theorem weakTransform_blowUpπ_of_eq_empty (hY : IsClosedSubmanifold ψ₀ Y c) (hY₀ : Y = ∅)
    (J : AnalyticManifold.IdealSheaf M) :
    IdealSheaf.weakTransform (blowUpπ ψ₀ hY) J hY.idealSheaf =
      J.pullback _ (blowUpπ ψ₀ hY).contMDiff :=
  (weakTransform_eq (blowUpπ ψ₀ hY) hY hY.isIdealSheafOf_idealSheaf (isBlowUp_blowUpπ ψ₀ hY)
    J).trans (IdealSheaf.weakTransformOf_of_eq_empty hY hY₀ _ J)

/-- Kollár (60.1) along the chosen blowing-up of an empty centre: the marked transform is the
pull-back. -/
theorem birationalTransform_I_blowUpπ_of_eq_empty (hY : IsClosedSubmanifold ψ₀ Y c) (hY₀ : Y = ∅)
    (J : MarkedIdealSheaf (structureSheaf 𝕜 E M)) :
    (MarkedIdealSheaf.birationalTransform hY (isBlowUp_blowUpπ ψ₀ hY) J).I =
      J.I.pullback _ (blowUpπ ψ₀ hY).contMDiff :=
  MarkedIdealSheaf.birationalTransform_I_of_eq_empty hY hY₀ _ J

/-- The analytic isomorphism `Bl_∅ M ≃ M` of an empty blowing-up, as an analytic map, is the
blow-down (`emptyBlowUpDiffeomorph_apply`, bundled). -/
theorem toAnalyticMap_emptyBlowUpDiffeomorph (hY : IsClosedSubmanifold ψ₀ Y c) (hY₀ : Y = ∅) :
    Diffeomorph.toAnalyticMap (BlowUpSequence.emptyBlowUpDiffeomorph hY hY₀) = blowUpπ ψ₀ hY :=
  ContMDiffMap.ext fun p => BlowUpSequence.emptyBlowUpDiffeomorph_apply hY hY₀ p

end EmptyStep

/-! ### Naturality of the one-step transforms along a lift over a local analytic isomorphism -/

section Square

variable {M N : AnalyticManifold.{u} 𝕜 E}

/-- `weakTransform_comap_liftStep` for any analytic map `G` between the chosen blowings-up lying
over `h` with `S = h⁻¹(Y)`: such a `G` is the lift `liftStep` (uniqueness of lifts,
`heq_liftStep_of_forall`). -/
theorem weakTransform_comap_of_square (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) {S : Set N} (hS : IsClosedSubmanifold ψ₀ S c)
    (e : S = ⇑h ⁻¹' Y) (G : AnalyticMap (blowUp ψ₀ hS) (blowUp ψ₀ hY))
    (hcomm : ∀ q, blowUpπ ψ₀ hY (G q) = h (blowUpπ ψ₀ hS q))
        (J : AnalyticManifold.IdealSheaf M) :
    (IdealSheaf.weakTransform (blowUpπ ψ₀ hY) J hY.idealSheaf).pullback G G.contMDiff =
      IdealSheaf.weakTransform (blowUpπ ψ₀ hS) (J.pullback h h.contMDiff) hS.idealSheaf := by
  subst e
  obtain rfl := eq_of_heq (BlowUpSequence.heq_liftStep_of_forall h hh hY hS rfl G hcomm)
  exact weakTransform_comap_liftStep h hh hY J

/-- `birationalTransform_comap_liftStep` for any `G` over `h` with `S = h⁻¹(Y)`. -/
theorem birationalTransform_comap_of_square (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) {S : Set N} (hS : IsClosedSubmanifold ψ₀ S c)
    (e : S = ⇑h ⁻¹' Y) (G : AnalyticMap (blowUp ψ₀ hS) (blowUp ψ₀ hY))
    (hcomm : ∀ q, blowUpπ ψ₀ hY (G q) = h (blowUpπ ψ₀ hS q))
    (J : MarkedIdealSheaf (structureSheaf 𝕜 E M))
    (hm : ∀ a ∈ Y, (J.m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J.I a) :
    (MarkedIdealSheaf.birationalTransform hY (isBlowUp_blowUpπ ψ₀ hY) J).I.pullback G G.contMDiff =
      (MarkedIdealSheaf.birationalTransform hS (isBlowUp_blowUpπ ψ₀ hS)
        ⟨J.I.pullback h h.contMDiff, J.m⟩).I := by
  subst e
  obtain rfl := eq_of_heq (BlowUpSequence.heq_liftStep_of_forall h hh hY hS rfl G hcomm)
  exact birationalTransform_comap_liftStep h hh hY J hm

/-- The strict transform (the closure of the preimage of the complement of the centre) is natural
along a local analytic isomorphism `G` between blowings-up lying over `h` with `S = h⁻¹(Y)`:
`G⁻¹(closure π⁻¹(H ∖ Y)) = closure π'⁻¹(h⁻¹(H) ∖ h⁻¹(Y))`, the preimage of a closure under an open
continuous map being the closure of the preimage. -/
theorem strictTransformSet_preimage_of_square (h : AnalyticMap N M) {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) {S : Set N} (hS : IsClosedSubmanifold ψ₀ S c)
    (e : S = ⇑h ⁻¹' Y) (G : AnalyticMap (blowUp ψ₀ hS) (blowUp ψ₀ hY))
    (hG : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω G)
    (hcomm : ∀ q, blowUpπ ψ₀ hY (G q) = h (blowUpπ ψ₀ hS q)) (H : Set M) :
    ⇑G ⁻¹' strictTransformSet (blowUpπ ψ₀ hY) Y H =
      strictTransformSet (blowUpπ ψ₀ hS) S (⇑h ⁻¹' H) := by
  subst e
  have hsq : ⇑(blowUpπ ψ₀ hY) ∘ ⇑G = ⇑h ∘ ⇑(blowUpπ ψ₀ hS) := funext hcomm
  unfold strictTransformSet
  rw [hG.isOpenMap.preimage_closure_eq_closure_preimage G.contMDiff.continuous, ← Set.preimage_comp,
    hsq, Set.preimage_comp, Set.preimage_sdiff]

/-- The total transform of a hypersurface family is natural along a local analytic
isomorphism `G` between blowings-up lying over `h` with `S = h⁻¹(Y)`: the strict transforms by
`strictTransformSet_preimage_of_square`, the exceptional divisor over `h`. -/
theorem _root_.Manifold.HypersurfaceFamily.totalTransform_comap_of_square (h : AnalyticMap N M)
    {Y : Set M}
    {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c) {S : Set N} (hS : IsClosedSubmanifold ψ₀ S c)
    (e : S = ⇑h ⁻¹' Y) (G : AnalyticMap (blowUp ψ₀ hS) (blowUp ψ₀ hY))
    (hG : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω G)
    (hcomm : ∀ q, blowUpπ ψ₀ hY (G q) = h (blowUpπ ψ₀ hS q)) (F : HypersurfaceFamily M) :
    (F.totalTransform (blowUpπ ψ₀ hY) Y).comap G =
      (F.comap h).totalTransform (blowUpπ ψ₀ hS) S := by
  subst e
  unfold HypersurfaceFamily.totalTransform HypersurfaceFamily.comap
  congr 1
  funext k
  obtain ⟨k', rfl⟩ : ∃ k', toLex k' = k := ⟨ofLex k, rfl⟩
  rcases k' with j | u
  · exact strictTransformSet_preimage_of_square h hY hS rfl G hG hcomm (F.hyp j)
  · ext q
    change blowUpπ ψ₀ hY (G q) ∈ Y ↔ blowUpπ ψ₀ hS q ∈ ⇑h ⁻¹' Y
    rw [hcomm q]
    exact Iff.rfl

end Square

/-! ### Transport along a diffeomorphism and its lift -/

section Diffeo

variable {M N P : AnalyticManifold.{u} 𝕜 E}

theorem preimage_image_diffeomorph (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) (Y : Set M) :
    ⇑(Diffeomorph.toAnalyticMap φ) ⁻¹' (⇑φ '' Y) = Y :=
  φ.toEquiv.preimage_image Y

theorem preimage_symm_preimage (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) (H : Set N) :
    ⇑φ.symm ⁻¹' (⇑φ ⁻¹' H) = H :=
  φ.toEquiv.symm_preimage_preimage H

theorem preimage_refl_symm (H : Set M) :
    ⇑(Diffeomorph.refl 𝓘(𝕜, E) M ω).symm ⁻¹' H = H := rfl

theorem preimage_trans_symm (h₁ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω)
    (h₂ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N P ω) (H : Set M) :
    ⇑(h₁.trans h₂).symm ⁻¹' H = ⇑h₂.symm ⁻¹' (⇑h₁.symm ⁻¹' H) := rfl

theorem comap_symm_comap (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω)
    (J : AnalyticManifold.IdealSheaf N) :
    (J.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff).pullback _ (Diffeomorph.toAnalyticMap
        φ.symm).contMDiff = J := by
  rw [IdealSheaf.pullback_comp]
  exact (IdealSheaf.pullback_congr J _ _ (funext fun x => φ.apply_symm_apply x)).trans
    (IdealSheaf.pullback_id_eq_self J)

theorem comap_refl_symm (J : AnalyticManifold.IdealSheaf M) :
    J.pullback _ (Diffeomorph.toAnalyticMap (Diffeomorph.refl 𝓘(𝕜, E) M ω).symm).contMDiff =
      J :=
  (IdealSheaf.pullback_congr J _ _ (funext fun _ => rfl)).trans (IdealSheaf.pullback_id_eq_self J)

theorem comap_trans_symm (h₁ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω)
    (h₂ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N P ω) (J : AnalyticManifold.IdealSheaf M) :
    J.pullback _ (Diffeomorph.toAnalyticMap (h₁.trans h₂).symm).contMDiff =
      (J.pullback _ (Diffeomorph.toAnalyticMap h₁.symm).contMDiff).pullback _
          (Diffeomorph.toAnalyticMap h₂.symm).contMDiff := by
  rw [IdealSheaf.pullback_comp]
  exact IdealSheaf.pullback_congr J _ _ (funext fun _ => rfl)

/-- The lift of `φ : M ≃ N` to the blowings-up lies over `φ` (`blowDown_liftPoint`). -/
theorem blowUpπ_liftDiffeomorph (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (q : blowUp ψ₀ hY) :
    blowUpπ ψ₀ (hY.image_diffeomorph φ) (BlowUpSequence.liftDiffeomorph φ hY q) =
      φ (blowUpπ ψ₀ hY q) :=
  blowDown_liftPoint _ _ _ q

/-- The ideal sheaf of the transported centre `φ(Y)` pulls back to the ideal sheaf of `Y`. -/
theorem comap_idealSheaf_image_diffeomorph (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) {Y : Set M}
    {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c) :
    (hY.image_diffeomorph φ).idealSheaf.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff =
      hY.idealSheaf :=
  (comap_idealSheaf_of_isLocalDiffeomorph ψ₀ (Diffeomorph.toAnalyticMap φ) φ.isLocalDiffeomorph
    (hY.image_diffeomorph φ)).trans
    (IsClosedSubmanifold.idealSheaf_congr _ hY (preimage_image_diffeomorph φ Y))

/-- The order along the transported centre `φ(Y)` at `φ a` is the order along `Y` of the pulled-back
ideal sheaf at `a` (`ordAlongIdeal_comap_of_isLocalDiffeomorphAt`). -/
theorem ordAlongIdeal_image_diffeomorph (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) {Y : Set M}
    {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c) (J : AnalyticManifold.IdealSheaf N) (a : M) :
    IdealSheaf.ordAlongIdeal (hY.image_diffeomorph φ).idealSheaf J (φ a) =
      IdealSheaf.ordAlongIdeal hY.idealSheaf
        (J.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff) a :=
  (IdealSheaf.ordAlongIdeal_comap_of_isLocalDiffeomorphAt (Diffeomorph.toAnalyticMap φ)
    (hY.image_diffeomorph φ).idealSheaf J (φ.isLocalDiffeomorph a)).symm.trans
    (congrArg (fun D => IdealSheaf.ordAlongIdeal D
      (J.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff) a)
      (comap_idealSheaf_image_diffeomorph φ hY))

end Diffeo

end Hironaka.Manifold

/-! ### The order clause of [Kol07, Definition 66] alone -/

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- Clause (4′) of [Kol07, Definition 66] alone: the marked transform of `(I, m)`
has order `≥ m` along every centre, so that every marked transform along the sequence is Kollár's
(60.1) (the marking legitimate). `IsOfOrderGe` is this clause together with the
normal-crossings clause (3′) (`IsOfOrderGe.isMarkedGe`). -/
def IsMarkedGe (S : FiniteSuccession M) (I : IdealSheaf M) (m : ℕ) : Prop :=
  ∀ i : Fin S.length, ∀ a ∈ (S.center i).support,
    (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (S.center i) (S.markedTransformSeq I m i.castSucc) a

theorem IsOfOrderGe.isMarkedGe {S : FiniteSuccession M} {I E₀ : IdealSheaf M} {m : ℕ}
    (h : S.IsOfOrderGe I m E₀) : S.IsMarkedGe I m := fun i => (h i).2

theorem isMarkedGe_nil (I : IdealSheaf M) (m : ℕ) : (nil M).IsMarkedGe I m := fun i => i.elim0

/-- The constructor form of `IsMarkedGe` (the order clause of `isOfOrderGe_cons_iff`). -/
theorem isMarkedGe_cons_iff {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : FiniteSuccession (blowUp ψ₀ hY)) (I : IdealSheaf M) (m : ℕ) :
    (cons ψ₀ hY rest).IsMarkedGe I m ↔
      (∀ a ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I a) ∧
        rest.IsMarkedGe
          ((cons ψ₀ hY rest).markedTransformSeq I m (Fin.succ (0 : Fin (rest.length + 1)))) m := by
  refine Iff.trans (Fin.forall_fin_succ (P := fun i : Fin (rest.length + 1) =>
      ∀ a ∈ ((cons ψ₀ hY rest).center i).support,
        (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal ((cons ψ₀ hY rest).center i)
          ((cons ψ₀ hY rest).markedTransformSeq I m i.castSucc) a))
    (and_congr ?_ (forall_congr' fun i => ?_))
  · change (∀ a ∈ hY.idealSheaf.support,
      (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I a) ↔ _
    rw [hY.cosupport_idealSheaf]
  · simp only [cons_center_succ, cons_markedTransformSeq_succ_castSucc]
    exact Iff.rfl

/-- The marked transform at the last stage of `cons ψ₀ hY rest` is the marked transform along
`rest` of the marked transform of the first step (`cons_markedTransformSeqAux_succ` with
`cons_markedTransformSeq_one`). -/
theorem cons_markedTransformSeq_last {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : FiniteSuccession (blowUp ψ₀ hY)) (I : IdealSheaf M) (m : ℕ) :
    (cons ψ₀ hY rest).markedTransformSeq I m (Fin.last _) =
      rest.markedTransformSeq
        (MarkedIdealSheaf.birationalTransform hY
          (isBlowUp_blowUpπ ψ₀ hY) ⟨I, m⟩).I m (Fin.last _) := by
  rw [← cons_markedTransformSeq_one hY rest I m]
  exact cons_markedTransformSeqAux_succ hY rest I m _ (Nat.lt_succ_self _)

/-- Along an empty first step the marked transform is the pull-back. -/
theorem cons_markedTransformSeq_one_of_eq_empty {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (hY₀ : Y = ∅)
    (rest : FiniteSuccession (blowUp ψ₀ hY)) (I : IdealSheaf M) (m : ℕ) :
    (cons ψ₀ hY rest).markedTransformSeq I m (Fin.succ (0 : Fin (rest.length + 1))) =
      I.pullback _ (blowUpπ ψ₀ hY).contMDiff :=
  (cons_markedTransformSeq_one hY rest I m).trans
    (MarkedIdealSheaf.birationalTransform_I_of_eq_empty hY hY₀ _ ⟨I, m⟩)

end AnalyticManifold.FiniteSuccession

namespace AnalyticManifold.BlowUpSequence

open Manifold Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### Transport of the last-stage data along `map` -/

section Map

variable {M N : AnalyticManifold.{u} 𝕜 E}

/-- The first marked transform along the transported list pulls back, along the lift of
`φ`, to the first marked transform along the list (`birationalTransform_comap_of_square` at the
first step). -/
theorem markedTransformSeq_one_map (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω)
    {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c) (I : IdealSheaf N)
        (m : ℕ)
    (hm : ∀ a ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf
      (I.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff) a) :
    (MarkedIdealSheaf.birationalTransform (hY.image_diffeomorph φ)
          (isBlowUp_blowUpπ ψ₀ (hY.image_diffeomorph φ)) ⟨I, m⟩).I.pullback _
              (Diffeomorph.toAnalyticMap (liftDiffeomorph φ hY)).contMDiff =
      (MarkedIdealSheaf.birationalTransform hY (isBlowUp_blowUpπ ψ₀ hY)
        ⟨I.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff, m⟩).I := by
  have hm' : ∀ b ∈ ⇑φ '' Y,
      (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (hY.image_diffeomorph φ).idealSheaf I b := by
    rintro _ ⟨a, ha, rfl⟩
    rw [ordAlongIdeal_image_diffeomorph]
    exact hm a ha
  exact birationalTransform_comap_of_square (Diffeomorph.toAnalyticMap φ) φ.isLocalDiffeomorph
    (hY.image_diffeomorph φ) hY (preimage_image_diffeomorph φ Y).symm
    (Diffeomorph.toAnalyticMap (liftDiffeomorph φ hY)) (blowUpπ_liftDiffeomorph φ hY) ⟨I, m⟩ hm'

/-- The marking stays legitimate along the transport of a list: `(φ^{-1})^*` of a marking legitimate
for `φ^* I` is legitimate for `I`. -/
theorem isMarkedGe_map : ∀ {M N : AnalyticManifold.{u} 𝕜 E}
    (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) (Z : BlowUpSequence ψ₀ M)
        (I : IdealSheaf N)
    (m : ℕ),
    Z.toSuccession.IsMarkedGe
        (I.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff) m →
    (Z.map φ).toSuccession.IsMarkedGe I m
  | _, _, _, nil _, I, m, _ => FiniteSuccession.isMarkedGe_nil I m
  | _, _, φ, @cons _ _ _ _ _ _ _ _ Y _ hY rest, I, m, hZ => by
    have := finiteDimensional_of_chartIso ψ₀
    obtain ⟨hm, hrest⟩ := (FiniteSuccession.isMarkedGe_cons_iff hY rest.toSuccession _ m).mp hZ
    refine (FiniteSuccession.isMarkedGe_cons_iff (hY.image_diffeomorph φ)
      (rest.map (liftDiffeomorph φ hY)).toSuccession I m).mpr ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩
      rw [ordAlongIdeal_image_diffeomorph]
      exact hm a ha
    · refine isMarkedGe_map (liftDiffeomorph φ hY) rest _ m ?_
      rw [FiniteSuccession.cons_markedTransformSeq_one, markedTransformSeq_one_map φ hY I m hm,
        ← FiniteSuccession.cons_markedTransformSeq_one hY rest.toSuccession]
      exact hrest

/-- The weak transform at the last stage of the transported list `Z.map φ` is the pull-back along
`(mapLast φ)⁻¹` of the weak transform of `φ^* J` at the last stage of `Z`
(`weakTransform_comap_of_square` at each step). -/
theorem weakTransformSeq_last_map : ∀ {M N : AnalyticManifold.{u} 𝕜 E}
    (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) (Z : BlowUpSequence ψ₀ M)
        (J : IdealSheaf N),
    (Z.map φ).toSuccession.weakTransformSeq J (Fin.last _) =
      (Z.toSuccession.weakTransformSeq
          (J.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff) (Fin.last _)).pullback _
              (Diffeomorph.toAnalyticMap (Z.mapLast φ).symm).contMDiff
  | _, _, φ, nil _, J => (comap_symm_comap φ J).symm
  | _, _, φ, @cons _ _ _ _ _ _ _ _ Y _ hY rest, J => by
    have := finiteDimensional_of_chartIso ψ₀
    have e1 : ((cons hY rest).map φ).toSuccession.weakTransformSeq J (Fin.last _) =
        (rest.map (liftDiffeomorph φ hY)).toSuccession.weakTransformSeq
          (IdealSheaf.weakTransform (blowUpπ ψ₀ (hY.image_diffeomorph φ)) J
              (hY.image_diffeomorph φ).idealSheaf) (Fin.last _) :=
      FiniteSuccession.cons_weakTransformSeqAux_succ (hY.image_diffeomorph φ)
        (rest.map (liftDiffeomorph φ hY)).toSuccession J _ (Nat.lt_succ_self _)
    have e2 : (cons hY rest).toSuccession.weakTransformSeq
          (J.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff) (Fin.last _) =
        rest.toSuccession.weakTransformSeq
            (IdealSheaf.weakTransform (blowUpπ ψ₀ hY)
              (J.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff) hY.idealSheaf)
          (Fin.last _) :=
      FiniteSuccession.cons_weakTransformSeqAux_succ hY rest.toSuccession _ _ (Nat.lt_succ_self _)
    have hsq := weakTransform_comap_of_square (Diffeomorph.toAnalyticMap φ) φ.isLocalDiffeomorph
      (hY.image_diffeomorph φ) hY (preimage_image_diffeomorph φ Y).symm
      (Diffeomorph.toAnalyticMap (liftDiffeomorph φ hY)) (blowUpπ_liftDiffeomorph φ hY) J
    change _ = Manifold.IdealSheaf.pullback (J := _) _ (Diffeomorph.toAnalyticMap (rest.mapLast
        (liftDiffeomorph φ
        hY)).symm).contMDiff
    rw [e1, e2, weakTransformSeq_last_map (liftDiffeomorph φ hY) rest, hsq]

/-- The marked transform at the last stage of the transported list `Z.map φ`, for a legitimate
marking, is the pull-back along `(mapLast φ)⁻¹` of the marked transform of `φ^* I` at the last
stage of `Z` (`birationalTransform_comap_of_square` at each step). -/
theorem markedTransformSeq_last_map : ∀ {M N : AnalyticManifold.{u} 𝕜 E}
    (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) (Z : BlowUpSequence ψ₀ M)
        (I : IdealSheaf N)
    (m : ℕ),
    Z.toSuccession.IsMarkedGe
        (I.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff) m →
    (Z.map φ).toSuccession.markedTransformSeq I m (Fin.last _) =
      (Z.toSuccession.markedTransformSeq
          (I.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff) m (Fin.last _)).pullback _
              (Diffeomorph.toAnalyticMap (Z.mapLast φ).symm).contMDiff
  | _, _, φ, nil _, I, m, _ => (comap_symm_comap φ I).symm
  | _, _, φ, @cons _ _ _ _ _ _ _ _ Y _ hY rest, I, m, hZ => by
    have := finiteDimensional_of_chartIso ψ₀
    obtain ⟨hm, hrest⟩ := (FiniteSuccession.isMarkedGe_cons_iff hY rest.toSuccession _ m).mp hZ
    have hsq := markedTransformSeq_one_map φ hY I m hm
    have hrest' : rest.toSuccession.IsMarkedGe
        ((MarkedIdealSheaf.birationalTransform (hY.image_diffeomorph φ)
            (isBlowUp_blowUpπ ψ₀ (hY.image_diffeomorph φ)) ⟨I, m⟩).I.pullback _
                (Diffeomorph.toAnalyticMap (liftDiffeomorph φ hY)).contMDiff) m := by
      rw [hsq, ← FiniteSuccession.cons_markedTransformSeq_one hY rest.toSuccession]
      exact hrest
    have e1 : ((cons hY rest).map φ).toSuccession.markedTransformSeq I m (Fin.last _) =
        (rest.map (liftDiffeomorph φ hY)).toSuccession.markedTransformSeq
          (MarkedIdealSheaf.birationalTransform (hY.image_diffeomorph φ)
            (isBlowUp_blowUpπ ψ₀ (hY.image_diffeomorph φ)) ⟨I, m⟩).I m (Fin.last _) :=
      FiniteSuccession.cons_markedTransformSeq_last (hY.image_diffeomorph φ)
        (rest.map (liftDiffeomorph φ hY)).toSuccession I m
    have e2 : (cons hY rest).toSuccession.markedTransformSeq
          (I.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff) m (Fin.last _) =
        rest.toSuccession.markedTransformSeq (MarkedIdealSheaf.birationalTransform hY
          (isBlowUp_blowUpπ ψ₀ hY)
          ⟨I.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff, m⟩).I m
              (Fin.last _) :=
      FiniteSuccession.cons_markedTransformSeq_last hY rest.toSuccession _ m
    rw [e1, e2]
    change _ = Manifold.IdealSheaf.pullback (J := _) _ (Diffeomorph.toAnalyticMap (rest.mapLast
        (liftDiffeomorph φ
        hY)).symm).contMDiff
    rw [markedTransformSeq_last_map (liftDiffeomorph φ hY) rest _ m hrest', hsq]

/-- The strict transform at the last stage of the transported list `Z.map φ` is the preimage under
`(mapLast φ)⁻¹` of the strict transform of `φ⁻¹(H)` at the last stage of `Z`
(`strictTransformSet_preimage_of_square` at each step). -/
theorem strictTransformSeq_last_map : ∀ {M N : AnalyticManifold.{u} 𝕜 E}
    (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) (Z : BlowUpSequence ψ₀ M) (H : Set N),
    (Z.map φ).toSuccession.strictTransformSeq H (Fin.last _) =
      ⇑(Z.mapLast φ).symm ⁻¹' (Z.toSuccession.strictTransformSeq (⇑φ ⁻¹' H) (Fin.last _))
  | _, _, φ, nil _, H => (preimage_symm_preimage φ H).symm
  | _, _, φ, @cons _ _ _ _ _ _ _ _ Y _ hY rest, H => by
    have e1 : ((cons hY rest).map φ).toSuccession.strictTransformSeq H (Fin.last _) =
        (rest.map (liftDiffeomorph φ hY)).toSuccession.strictTransformSeq
          (strictTransformSet (blowUpπ ψ₀ (hY.image_diffeomorph φ))
            (hY.image_diffeomorph φ).idealSheaf.support H) (Fin.last _) :=
      FiniteSuccession.cons_strictTransformSeqAux_succ (hY.image_diffeomorph φ)
        (rest.map (liftDiffeomorph φ hY)).toSuccession H _ (Nat.lt_succ_self _)
    have e2 : (cons hY rest).toSuccession.strictTransformSeq (⇑φ ⁻¹' H) (Fin.last _) =
        rest.toSuccession.strictTransformSeq
          (strictTransformSet (blowUpπ ψ₀ hY) hY.idealSheaf.support (⇑φ ⁻¹' H)) (Fin.last _) :=
      FiniteSuccession.cons_strictTransformSeqAux_succ hY rest.toSuccession _ _ (Nat.lt_succ_self _)
    have hsq : ⇑(liftDiffeomorph φ hY) ⁻¹'
          strictTransformSet (blowUpπ ψ₀ (hY.image_diffeomorph φ)) (⇑φ '' Y) H =
        strictTransformSet (blowUpπ ψ₀ hY) Y (⇑φ ⁻¹' H) :=
      strictTransformSet_preimage_of_square (Diffeomorph.toAnalyticMap φ) (hY.image_diffeomorph φ)
        hY (preimage_image_diffeomorph φ Y).symm (Diffeomorph.toAnalyticMap (liftDiffeomorph φ hY))
        (liftDiffeomorph φ hY).isLocalDiffeomorph (blowUpπ_liftDiffeomorph φ hY) H
    change _ = ⇑(rest.mapLast (liftDiffeomorph φ hY)).symm ⁻¹' _
    rw [e1, e2, strictTransformSeq_last_map (liftDiffeomorph φ hY) rest,
      (hY.image_diffeomorph φ).cosupport_idealSheaf, hY.cosupport_idealSheaf, hsq]

end Map

/-! ### Transport along an equality of lists -/

section OfEq

variable {M : AnalyticManifold.{u} 𝕜 E}

theorem weakTransformSeq_last_stageOfEq {L₁ L₂ : BlowUpSequence ψ₀ M} (e : L₁ = L₂)
    (I : IdealSheaf M) :
    L₂.toSuccession.weakTransformSeq I (Fin.last _) =
      (L₁.toSuccession.weakTransformSeq I (Fin.last _)).pullback _ (Diffeomorph.toAnalyticMap
          (stageOfEq e).symm).contMDiff := by
  subst e
  exact (comap_refl_symm _).symm

theorem markedTransformSeq_last_stageOfEq {L₁ L₂ : BlowUpSequence ψ₀ M} (e : L₁ = L₂)
    (I : IdealSheaf M) (m : ℕ) :
    L₂.toSuccession.markedTransformSeq I m (Fin.last _) =
      (L₁.toSuccession.markedTransformSeq I m (Fin.last _)).pullback _ (Diffeomorph.toAnalyticMap
          (stageOfEq e).symm).contMDiff := by
  subst e
  exact (comap_refl_symm _).symm

theorem strictTransformSeq_last_stageOfEq {L₁ L₂ : BlowUpSequence ψ₀ M} (e : L₁ = L₂) (H : Set M) :
    L₂.toSuccession.strictTransformSeq H (Fin.last _) =
      ⇑(stageOfEq e).symm ⁻¹' (L₁.toSuccession.strictTransformSeq H (Fin.last _)) := by
  subst e
  exact (preimage_refl_symm _).symm

theorem isMarkedGe_of_eq {L₁ L₂ : BlowUpSequence ψ₀ M} (e : L₁ = L₂)
    {I : IdealSheaf M}
    {m : ℕ} (h : L₁.toSuccession.IsMarkedGe I m) : L₂.toSuccession.IsMarkedGe I m := by
  subst e
  exact h

end OfEq

/-! ### The last-stage transforms along the deletion of empty blow-ups -/

section EraseEmpty

variable {M : AnalyticManifold.{u} 𝕜 E}

/-- [Kol07, 34.1]: **deleting the empty blow-ups keeps the markings legitimate** — an
empty step is a legitimate marking vacuously and transforms `(I, m)` by pull-back. -/
theorem isMarkedGe_eraseEmpty : ∀ {M : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M) (I : IdealSheaf M) (m : ℕ),
    L.toSuccession.IsMarkedGe I m → L.eraseEmpty.toSuccession.IsMarkedGe I m
  | _, nil _, I, m, _ => FiniteSuccession.isMarkedGe_nil I m
  | _, @cons _ _ _ _ _ _ _ _ Y _ hY rest, I, m, hL => by
    have := finiteDimensional_of_chartIso ψ₀
    obtain ⟨hm, hrest⟩ := (FiniteSuccession.isMarkedGe_cons_iff hY rest.toSuccession I m).mp hL
    by_cases hY₀ : Y = ∅
    · refine isMarkedGe_of_eq (eraseEmpty_cons_of_eq_empty hY rest hY₀).symm
        (isMarkedGe_map (emptyBlowUpDiffeomorph hY hY₀) rest.eraseEmpty I m ?_)
      rw [toAnalyticMap_emptyBlowUpDiffeomorph hY hY₀]
      refine isMarkedGe_eraseEmpty rest _ m ?_
      rwa [FiniteSuccession.cons_markedTransformSeq_one_of_eq_empty hY hY₀] at hrest
    · refine isMarkedGe_of_eq (eraseEmpty_cons_of_ne_empty hY rest hY₀).symm
        ((FiniteSuccession.isMarkedGe_cons_iff hY rest.eraseEmpty.toSuccession I m).mpr
          ⟨hm, ?_⟩)
      rw [FiniteSuccession.cons_markedTransformSeq_one]
      rw [FiniteSuccession.cons_markedTransformSeq_one] at hrest
      exact isMarkedGe_eraseEmpty rest _ m hrest

/-- [Kol07, 34.1], the analogue of `weakTransformSeq_eraseEmpty_last` for schemes: **the
weak transform of `I` at the last stage of the cleaned list is the pull-back along
`eraseEmptyLast⁻¹` of the weak transform at the last stage of the list** — a kept step contributes
the same weak transform on both sides, a deleted step the total transform along the empty
blowing-up, which the transport of the cleaned tail along `Bl_∅ M ≃ M` absorbs. -/
theorem weakTransformSeq_last_eraseEmpty : ∀ {M : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M) (I : IdealSheaf M),
    L.eraseEmpty.toSuccession.weakTransformSeq I (Fin.last _) =
      (L.toSuccession.weakTransformSeq I (Fin.last _)).pullback _ (Diffeomorph.toAnalyticMap
          L.eraseEmptyLast.symm).contMDiff
  | _, nil _, I => (comap_refl_symm I).symm
  | _, @cons _ _ _ _ _ _ _ _ Y _ hY rest, I => by
    have := finiteDimensional_of_chartIso ψ₀
    have e2 : (cons hY rest).toSuccession.weakTransformSeq I (Fin.last _) =
        rest.toSuccession.weakTransformSeq
          (IdealSheaf.weakTransform (blowUpπ ψ₀ hY) I hY.idealSheaf)
              (Fin.last _) :=
      FiniteSuccession.cons_weakTransformSeqAux_succ hY rest.toSuccession I _ (Nat.lt_succ_self _)
    by_cases hY₀ : Y = ∅
    · rw [eraseEmptyLast_cons_of_eq_empty hY rest hY₀, e2]
      change _ = Manifold.IdealSheaf.pullback (J := _) _ (Diffeomorph.toAnalyticMap
        ((rest.eraseEmptyLast.trans (rest.eraseEmpty.mapLast (emptyBlowUpDiffeomorph hY hY₀))).trans
          (stageOfEq (eraseEmpty_cons_of_eq_empty hY rest hY₀).symm)).symm).contMDiff
      rw [comap_trans_symm, comap_trans_symm,
        weakTransformSeq_last_stageOfEq (eraseEmpty_cons_of_eq_empty hY rest hY₀).symm I,
        weakTransformSeq_last_map, toAnalyticMap_emptyBlowUpDiffeomorph hY hY₀,
        ← weakTransform_blowUpπ_of_eq_empty hY hY₀ I, weakTransformSeq_last_eraseEmpty rest]
    · have e3 : (cons hY rest.eraseEmpty).toSuccession.weakTransformSeq I (Fin.last _) =
          rest.eraseEmpty.toSuccession.weakTransformSeq
            (IdealSheaf.weakTransform (blowUpπ ψ₀ hY) I hY.idealSheaf)
                (Fin.last _) :=
        FiniteSuccession.cons_weakTransformSeqAux_succ hY rest.eraseEmpty.toSuccession I _
          (Nat.lt_succ_self _)
      rw [eraseEmptyLast_cons_of_ne_empty hY rest hY₀, e2]
      exact (weakTransformSeq_last_stageOfEq (L₁ := cons hY rest.eraseEmpty)
        (eraseEmpty_cons_of_ne_empty hY rest hY₀).symm I).trans
        ((congrArg (Manifold.IdealSheaf.pullback _ (Diffeomorph.toAnalyticMap
          (stageOfEq (L₁ := cons hY rest.eraseEmpty)
            (eraseEmpty_cons_of_ne_empty hY rest hY₀).symm).symm).contMDiff)
          (e3.trans (weakTransformSeq_last_eraseEmpty rest _))).trans
          (comap_trans_symm rest.eraseEmptyLast _ _).symm)

/-- The marked version of `weakTransformSeq_last_eraseEmpty`, for a list whose markings are
legitimate (`markedTransformSeq_eraseEmpty_last`). -/
theorem markedTransformSeq_last_eraseEmpty_of_isMarkedGe :
    ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) (I : IdealSheaf M)
        (m : ℕ),
    L.toSuccession.IsMarkedGe I m →
    L.eraseEmpty.toSuccession.markedTransformSeq I m (Fin.last _) =
      (L.toSuccession.markedTransformSeq I m (Fin.last _)).pullback _ (Diffeomorph.toAnalyticMap
          L.eraseEmptyLast.symm).contMDiff
  | _, nil _, I, _, _ => (comap_refl_symm I).symm
  | _, @cons _ _ _ _ _ _ _ _ Y _ hY rest, I, m, hL => by
    have := finiteDimensional_of_chartIso ψ₀
    obtain ⟨-, hrest⟩ := (FiniteSuccession.isMarkedGe_cons_iff hY rest.toSuccession I m).mp hL
    rw [FiniteSuccession.cons_markedTransformSeq_one] at hrest
    have e2 : (cons hY rest).toSuccession.markedTransformSeq I m (Fin.last _) =
        rest.toSuccession.markedTransformSeq
          (MarkedIdealSheaf.birationalTransform hY (isBlowUp_blowUpπ ψ₀ hY) ⟨I, m⟩).I m
          (Fin.last _) :=
      FiniteSuccession.cons_markedTransformSeq_last hY rest.toSuccession I m
    by_cases hY₀ : Y = ∅
    · have hrest' :
        rest.toSuccession.IsMarkedGe (I.pullback _ (blowUpπ ψ₀ hY).contMDiff)
          m := by
        rwa [birationalTransform_I_blowUpπ_of_eq_empty hY hY₀] at hrest
      have hZ : rest.eraseEmpty.toSuccession.IsMarkedGe (I.pullback _ (Diffeomorph.toAnalyticMap
          (emptyBlowUpDiffeomorph hY hY₀)).contMDiff) m := by
        rw [toAnalyticMap_emptyBlowUpDiffeomorph hY hY₀]
        exact isMarkedGe_eraseEmpty rest _ m hrest'
      rw [eraseEmptyLast_cons_of_eq_empty hY rest hY₀, e2,
        birationalTransform_I_blowUpπ_of_eq_empty hY hY₀]
      change _ = Manifold.IdealSheaf.pullback (J := _) _ (Diffeomorph.toAnalyticMap
        ((rest.eraseEmptyLast.trans (rest.eraseEmpty.mapLast (emptyBlowUpDiffeomorph hY hY₀))).trans
          (stageOfEq (eraseEmpty_cons_of_eq_empty hY rest hY₀).symm)).symm).contMDiff
      rw [comap_trans_symm, comap_trans_symm,
        markedTransformSeq_last_stageOfEq (eraseEmpty_cons_of_eq_empty hY rest hY₀).symm I m,
        markedTransformSeq_last_map (emptyBlowUpDiffeomorph hY hY₀) rest.eraseEmpty I m hZ,
        toAnalyticMap_emptyBlowUpDiffeomorph hY hY₀,
        markedTransformSeq_last_eraseEmpty_of_isMarkedGe rest _ m hrest']
    · have e3 : (cons hY rest.eraseEmpty).toSuccession.markedTransformSeq I m (Fin.last _) =
          rest.eraseEmpty.toSuccession.markedTransformSeq
            (MarkedIdealSheaf.birationalTransform hY (isBlowUp_blowUpπ ψ₀ hY) ⟨I, m⟩).I m
            (Fin.last _) :=
        FiniteSuccession.cons_markedTransformSeq_last hY rest.eraseEmpty.toSuccession I m
      rw [eraseEmptyLast_cons_of_ne_empty hY rest hY₀, e2]
      exact (markedTransformSeq_last_stageOfEq (L₁ := cons hY rest.eraseEmpty)
        (eraseEmpty_cons_of_ne_empty hY rest hY₀).symm I m).trans
        ((congrArg (Manifold.IdealSheaf.pullback _ (Diffeomorph.toAnalyticMap
          (stageOfEq (L₁ := cons hY rest.eraseEmpty)
            (eraseEmpty_cons_of_ne_empty hY rest hY₀).symm).symm).contMDiff)
          (e3.trans (markedTransformSeq_last_eraseEmpty_of_isMarkedGe rest _ m hrest))).trans
          (comap_trans_symm rest.eraseEmptyLast _ _).symm)

/-- [Kol07, 34.1], the analogue of `markedTransformSeq_eraseEmpty_last` for schemes: for a
list of order `≥ m` for `(I, m, E₀)` ([Kol07, Definition 66], any boundary `E₀`), **the marked
transform of `(I, m)` at the last stage of the cleaned list is the pull-back along
`eraseEmptyLast⁻¹` of the marked transform at the last stage of the list** (only the order clause
is used: `markedTransformSeq_last_eraseEmpty_of_isMarkedGe`). -/
theorem markedTransformSeq_last_eraseEmpty (L : BlowUpSequence ψ₀ M)
    (I E₀ : IdealSheaf M) (m : ℕ) (hge : L.toSuccession.IsOfOrderGe I m E₀) :
    L.eraseEmpty.toSuccession.markedTransformSeq I m (Fin.last _) =
      (L.toSuccession.markedTransformSeq I m (Fin.last _)).pullback _ (Diffeomorph.toAnalyticMap
          L.eraseEmptyLast.symm).contMDiff :=
  markedTransformSeq_last_eraseEmpty_of_isMarkedGe L I m hge.isMarkedGe

/-- [Kol07, 34.1], the analogue of `strictTransformSeq_eraseEmpty_last` for schemes: **the
strict transform of a closed set `H` at the last stage of the cleaned list is the preimage under
`eraseEmptyLast⁻¹` of its strict transform at the last stage of the list** — a deleted step
transforms a closed set by preimage (`strictTransformSet_empty_of_isClosed`). Closedness is
needed: the strict transform along an empty blowing-up of a non-closed set is the preimage of its
closure. -/
theorem strictTransformSeq_last_eraseEmpty : ∀ {M : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M)
    {H : Set M}, IsClosed H →
    L.eraseEmpty.toSuccession.strictTransformSeq H (Fin.last _) =
      ⇑L.eraseEmptyLast.symm ⁻¹' (L.toSuccession.strictTransformSeq H (Fin.last _))
  | _, nil _, H, _ => (preimage_refl_symm H).symm
  | _, @cons _ _ _ _ _ _ _ _ Y _ hY rest, H, hH => by
    have e2 : (cons hY rest).toSuccession.strictTransformSeq H (Fin.last _) =
        rest.toSuccession.strictTransformSeq
          (strictTransformSet (blowUpπ ψ₀ hY) hY.idealSheaf.support H) (Fin.last _) :=
      FiniteSuccession.cons_strictTransformSeqAux_succ hY rest.toSuccession H _ (Nat.lt_succ_self _)
    have hH₁ : IsClosed (strictTransformSet (blowUpπ ψ₀ hY) hY.idealSheaf.support H) :=
      isClosed_closure
    by_cases hY₀ : Y = ∅
    · have hpre : ⇑(emptyBlowUpDiffeomorph hY hY₀) ⁻¹' H =
          strictTransformSet (blowUpπ ψ₀ hY) hY.idealSheaf.support H := by
        rw [hY.cosupport_idealSheaf]
        exact (congrArg (· ⁻¹' H) (funext (emptyBlowUpDiffeomorph_apply hY hY₀))).trans
          ((congrArg (fun Z => strictTransformSet ⇑(blowUpπ ψ₀ hY) Z H) hY₀).trans
            (strictTransformSet_empty_of_isClosed (blowUpπ ψ₀ hY).contMDiff.continuous hH)).symm
      rw [eraseEmptyLast_cons_of_eq_empty hY rest hY₀, e2]
      change _ = ⇑((rest.eraseEmptyLast.trans
        (rest.eraseEmpty.mapLast (emptyBlowUpDiffeomorph hY hY₀))).trans
          (stageOfEq (eraseEmpty_cons_of_eq_empty hY rest hY₀).symm)).symm ⁻¹' _
      rw [preimage_trans_symm, preimage_trans_symm,
        strictTransformSeq_last_stageOfEq (eraseEmpty_cons_of_eq_empty hY rest hY₀).symm H,
        strictTransformSeq_last_map, hpre, strictTransformSeq_last_eraseEmpty rest hH₁]
    · have e3 : (cons hY rest.eraseEmpty).toSuccession.strictTransformSeq H (Fin.last _) =
          rest.eraseEmpty.toSuccession.strictTransformSeq
            (strictTransformSet (blowUpπ ψ₀ hY) hY.idealSheaf.support H) (Fin.last _) :=
        FiniteSuccession.cons_strictTransformSeqAux_succ hY rest.eraseEmpty.toSuccession H _
          (Nat.lt_succ_self _)
      rw [eraseEmptyLast_cons_of_ne_empty hY rest hY₀, e2]
      exact (strictTransformSeq_last_stageOfEq (L₁ := cons hY rest.eraseEmpty)
        (eraseEmpty_cons_of_ne_empty hY rest hY₀).symm H).trans
        ((congrArg (fun S => ⇑(stageOfEq (L₁ := cons hY rest.eraseEmpty)
            (eraseEmpty_cons_of_ne_empty hY rest hY₀).symm).symm ⁻¹' S)
          (e3.trans (strictTransformSeq_last_eraseEmpty rest hH₁))).trans
          (preimage_trans_symm rest.eraseEmptyLast _ _).symm)

end EraseEmpty

end AnalyticManifold.BlowUpSequence

end
