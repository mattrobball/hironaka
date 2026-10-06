/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.RestrictBundle
public import Hironaka.Manifold.FiniteSuccession.Functor.PushforwardPullback
public import Hironaka.Resolution.Analytic.Principalization.IsoOff
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.RealizePullback
import Hironaka.Resolution.Analytic.OrderReduction.ClosedEmbeddingFam
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The push-forwards along a flag `S ⊂ Y ⊂ M`

Kollár reduces the commutation of the order-reduction functor with a closed embedding `S ⊂ M` of
codimension `s + 1` to a flag `S ⊂ Y ⊂ M` with `Y` of codimension `s` and `S` a hypersurface of `Y`
[Kol07, 108]; the push-forward of a blow-up sequence along a closed embedding is
[Kol07, Definition 30.3]. This module is the push-forward bookkeeping of that reduction:

* `IsClosedSubmanifold.exists_diffeomorph_toAnalyticManifold_of_flag`: for `S ⊆ Y` the two
  bundled structures on `S` — as a closed submanifold of `M` of codimension `s + 1`, as a
  hypersurface of the bundled `Y` — are carried by the identity of the carrier, an analytic
  isomorphism over `M`;
* `BlowUpSequence.noEmptyCenters_pushforwardRestrict'`: the per-open push-forward of a list without
  empty centres has none, at every codimension (`noEmptyCenters_pushforwardRestrict` of
  `OrderReduction/ClosedEmbeddingFam.lean` is the codimension-one case; the general one goes
  through `pushforwardAux` directly — the centres of the push-forward are the images of the
  centres under the closed embedding of each stage);
* `BlowUpSequence.pushforward_pushforward_of_flag`: pushing a list forward from the hypersurface `S`
  of `Y` to `Y` and then from `Y` to `M` is pushing it forward from `S` to `M`. The first half is
  the **nested stage** `PushforwardStage.nest`: from a stage for `Y ⊂ M` (ambient `X`, strict
  transform `Ỹ ⊆ X`) and a stage for `S ⊂ Y` on its manifold (strict transform `S̃ ⊆ T_Y`), the
  stage for `S ⊂ M` with ambient `X`, sub `j_Y(S̃)` and the composed identification. The second
  half compares the next stages: the strict transform of `j_Y(S̃)` in `Bl X` is the image of the
  strict transform of `S̃` in `Bl Ỹ` under the lifted closed embedding `Bl Ỹ ↪ Bl X`
  (`image_incl_strictTransformSet`), and the lifted inclusions agree by the uniqueness of lifts to
  a blowing-up (`incl_nestStep`; a blowing-up is unique up to an isomorphism commuting with the
  blow-down, [BM88, Definition 4.1]); this is the pull-back-stage invariant
  `isPullbackStage_nestStep` along the identity of `Bl X`, and the list induction
  `pushforwardAux_nest` follows through `pushforwardAux_pullback`;
* `BlowUpSequence.pushforward_pullback_inclusionMap_of_centersOver`, the codimension-zero case: for
  `S` clopen in `M` with `S ↪ M` a local analytic isomorphism and a list whose centres lie over `S`
  (`CentersOver`, `Principalization/IsoOff.lean`), the push-forward along `S` of the pull-back
  along the inclusion is the list itself: the pushed-forward centres are the centres (`Z ⊆ S`), the
  lifted inclusion at each stage is THE lift of the inclusion
  (`BlowUpSequence.eq_liftStep_of_comm`), and the strict transform of the open `S` contains the
  whole preimage of `S` (`IsBlowUp.dense_preimage_compl`, at every codimension).

The internals are the stage `blowUpStepOf` (the next stage with the pushed-forward centre given as
a datum `W`, so that the ambient of the next stage is `blowUp ψ hW` literally) with its
`subst`-lemmas, and `heq_pushforwardAux`. Not in the sources beyond Kollár's reduction; the proofs
are routine.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-! ### The two bundled structures on `S ⊆ Y` -/

/-- For `S ⊆ Y` with `Y` a closed submanifold of codimension `s`, `S` one of codimension `s + 1`
and `S` a hypersurface of the bundled `Y` (the flag of [Kol07, 108]), the two bundled structures
on `S` (the models `Fin (n - (s + 1)) → 𝕜` and `Fin (n - s - 1) → 𝕜` are the same type
definitionally) are carried by the identity of the carrier: an analytic isomorphism `e` with
`j_S ∘ e = j_Y ∘ j_{S,Y}`. -/
theorem IsClosedSubmanifold.exists_diffeomorph_toAnalyticManifold_of_flag {Y S : Set M} {s : ℕ}
    (hY : IsClosedSubmanifold ψ Y s) (hS : IsClosedSubmanifold ψ S (s + 1)) (hSY' : S ⊆ Y)
    (hSY : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      (⇑hY.inclusionMap ⁻¹' S) 1) :
    ∃ e : Diffeomorph 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜)
      (hSY.toAnalyticManifold : AnalyticManifold.{u} 𝕜 (Fin (n - (s + 1)) → 𝕜))
      hS.toAnalyticManifold ω,
      ∀ x, (hS.inclusionMap (e x) : M) = hY.inclusionMap (hSY.inclusionMap x) := by
  let f : hSY.toAnalyticManifold → hS.toAnalyticManifold :=
    fun x => ⟨(hY.inclusionMap (hSY.inclusionMap x) : M), x.2⟩
  let g₀ : hS.toAnalyticManifold → hY.toAnalyticManifold :=
    fun x => ⟨(hS.inclusionMap x : M), hSY' x.2⟩
  let g : hS.toAnalyticManifold → hSY.toAnalyticManifold := fun x => ⟨g₀ x, x.2⟩
  have hf : ContMDiff 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) ω f :=
    hS.contMDiff_codRestrict (hY.inclusionMap.contMDiff.comp hSY.inclusionMap.contMDiff)
      fun x => x.2
  have hg₀ : ContMDiff 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) ω g₀ :=
    hY.contMDiff_codRestrict hS.inclusionMap.contMDiff fun x => hSY' x.2
  have hg : ContMDiff 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) ω g :=
    hSY.contMDiff_codRestrict hg₀ fun x => x.2
  let e : Diffeomorph 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜)
      (hSY.toAnalyticManifold : AnalyticManifold.{u} 𝕜 (Fin (n - (s + 1)) → 𝕜))
      hS.toAnalyticManifold ω :=
    { toFun := f
      invFun := g
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun x => Subtype.ext rfl
      contMDiff_toFun := hf
      contMDiff_invFun := hg }
  exact ⟨e, fun x => rfl⟩

/-! ### No empty centres through a push-forward, at every codimension -/

section NoEmpty

variable {s : ℕ}

/-- The push-forward of a list without empty centres through any stage has none — the centres
of the push-forward are the images of the centres under the closed embedding `P.incl` of the
stage (`imageVal_image_eq`). -/
theorem _root_.AnalyticManifold.BlowUpSequence.noEmptyCenters_pushforwardAux :
    ∀ {Tᵢ : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)} (P : PushforwardStage ψ s Tᵢ)
      (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Tᵢ),
      L.NoEmptyCenters → (AnalyticManifold.BlowUpSequence.pushforwardAux P L).NoEmptyCenters
  | _, P, AnalyticManifold.BlowUpSequence.nil _, _ =>
      AnalyticManifold.BlowUpSequence.noEmptyCenters_nil
  | _, P, @AnalyticManifold.BlowUpSequence.cons _ _ _ _ _ _ _ _ Z c hZ rest, hL => by
    obtain ⟨hne, hrest⟩ := (AnalyticManifold.BlowUpSequence.noEmptyCenters_cons_iff hZ rest).mp hL
    refine (AnalyticManifold.BlowUpSequence.noEmptyCenters_cons_iff _ _).mpr
      ⟨?_, AnalyticManifold.BlowUpSequence.noEmptyCenters_pushforwardAux _ rest hrest⟩
    rw [P.imageVal_image_eq]
    intro h0
    exact hne (Set.image_eq_empty.mp h0)

/-- `BlowUpSequence.pushforward` along a closed submanifold of any codimension keeps
`NoEmptyCenters` (through the stages; the codimension-one statement elsewhere goes through
`PushforwardBridge`). -/
theorem _root_.AnalyticManifold.BlowUpSequence.noEmptyCenters_pushforward {S : Set M}
    (hS : IsClosedSubmanifold ψ S s)
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin
        (n - s) → 𝕜)) hS.toAnalyticManifold)
    (hL : L.NoEmptyCenters) : (L.pushforward hS).NoEmptyCenters :=
  AnalyticManifold.BlowUpSequence.noEmptyCenters_pushforwardAux _ L hL

end NoEmpty

/-- The per-open push-forward of a list without empty centres has none, at every codimension —
the codimension-one statement `noEmptyCenters_pushforwardRestrict`
(`OrderReduction/ClosedEmbeddingFam.lean`) generalised (the unprimed one is the case `s = 1`).
Through `pushforwardRestrict_eq` (`RestrictBundle.lean`) the per-open push-forward is a pull-back
along the bundle diffeomorphism (surjective, so `noEmptyCenters_pullback_of_surjective` applies)
followed by an ordinary push-forward. -/
theorem _root_.AnalyticManifold.BlowUpSequence.noEmptyCenters_pushforwardRestrict' {S : Set M}
    {s : ℕ}
    (hS : IsClosedSubmanifold ψ S s) (U : Opens M)
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      ((hS.toAnalyticManifold).restrict (hS.preimageOpens U)))
    (hL : L.NoEmptyCenters) : (AnalyticManifold.BlowUpSequence.pushforwardRestrict hS U
        L).NoEmptyCenters := by
  rw [AnalyticManifold.BlowUpSequence.pushforwardRestrict_eq]
  exact AnalyticManifold.BlowUpSequence.noEmptyCenters_pushforward _ _
    (AnalyticManifold.BlowUpSequence.noEmptyCenters_pullback_of_surjective L _ _
      (hS.restrictBundleDiffeomorph U).symm.surjective hL)

/-! ### The next stage with the pushed-forward centre as a datum -/

section StepOf

variable {s : ℕ} {Tᵢ T' : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)} (P : PushforwardStage ψ s Tᵢ)
  {Z : Set Tᵢ} {c : ℕ}

/-- A stage's inclusion lands in its strict transform (`range_incl`). -/
theorem PushforwardStage.incl_mem_sub (t : Tᵢ) : P.incl t ∈ P.sub := by
  rw [← P.range_incl]
  exact Set.mem_range_self t

/-- `blowUpStep` with the pushed-forward centre given as a DATUM `W` — a closed submanifold of the
ambient equal to `(j_i)_* Z` [Kol07, Definition 30.3] — so that the ambient of the next stage is
`blowUp ψ hW` literally, for a centre `W` already present in the ambient list. -/
def PushforwardStage.blowUpStepOf
    (hZ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c)
    {W : Set P.space} {c' : ℕ} (hW : IsClosedSubmanifold ψ W c')
    (hWe : W = P.isClosedSubmanifold.imageVal (P.iso '' Z)) (hc' : c' = c + s)
    {π : AnalyticMap T' Tᵢ} (hπ : IsBlowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c π) :
    PushforwardStage ψ s T' where
  space := blowUp ψ hW
  sub := strictTransformSet (blowUpπ ψ hW) W P.sub
  isClosedSubmanifold := P.isClosedSubmanifold.strictTransform hW (isBlowUp_blowUpπ ψ hW)
    (by rw [hWe]; exact P.isClosedSubmanifold.imageVal_subset _)
  iso := by
    subst hWe; subst hc'
    exact IsBlowUp.diffeomorph (hZ.image_diffeomorph P.iso) (hπ.diffeomorph_comp P.iso)
      (P.isBlowUp_restrictMap_imageVal hZ)

/-- `blowUpStepOf` IS `blowUpStep` — the datum is the pushed-forward centre. -/
theorem PushforwardStage.blowUpStepOf_eq
    (hZ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c)
    {W : Set P.space} {c' : ℕ} (hW : IsClosedSubmanifold ψ W c')
    (hWe : W = P.isClosedSubmanifold.imageVal (P.iso '' Z)) (hc' : c' = c + s)
    {π : AnalyticMap T' Tᵢ} (hπ : IsBlowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c π) :
    P.blowUpStepOf hZ hW hWe hc' hπ = P.blowUpStep hZ hπ := by
  subst hWe; subst hc'; rfl

/-- The square of `blowUpStepOf`: the blow-down of the next stage's inclusion is the inclusion
of the blow-down (`restrictMap_blowUpStep_iso`). -/
theorem PushforwardStage.blowUpπ_incl_blowUpStepOf
    (hZ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c)
    {W : Set P.space} {c' : ℕ} (hW : IsClosedSubmanifold ψ W c')
    (hWe : W = P.isClosedSubmanifold.imageVal (P.iso '' Z)) (hc' : c' = c + s)
    {π : AnalyticMap T' Tᵢ} (hπ : IsBlowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c π)
    (p : T') :
    blowUpπ ψ hW ((P.blowUpStepOf hZ hW hWe hc' hπ).incl p) = P.incl (π p) := by
  subst hWe; subst hc'
  exact congrArg Subtype.val (P.restrictMap_blowUpStep_iso hZ hπ p)

/-- The restricted blow-down of `blowUpStepOf` over the identification of the stage is the
identification of the blow-down (`restrictMap_blowUpStep_iso`). -/
theorem PushforwardStage.restrictMap_blowUpStepOf_iso
    (hZ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c)
    {W : Set P.space} {c' : ℕ} (hW : IsClosedSubmanifold ψ W c')
    (hWe : W = P.isClosedSubmanifold.imageVal (P.iso '' Z)) (hc' : c' = c + s)
    {π : AnalyticMap T' Tᵢ} (hπ : IsBlowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c π)
    (p : T') :
    (P.blowUpStepOf hZ hW hWe hc' hπ).isClosedSubmanifold.restrictMap P.isClosedSubmanifold
        (blowUpπ ψ hW) (isBlowUp_blowUpπ ψ hW).contMDiff
        (strictTransform_subset_preimage (blowUpπ ψ hW).contMDiff.continuous
          P.isClosedSubmanifold.isClosed) ((P.blowUpStepOf hZ hW hWe hc' hπ).iso p) =
      P.iso (π p) := by
  subst hWe; subst hc'
  exact P.restrictMap_blowUpStep_iso hZ hπ p

/-- The restricted blow-down of `blowUpStepOf` is a blowing-up of the stage's manifold along the
identified centre (`isBlowUp_restrictMap_imageVal`). -/
theorem PushforwardStage.isBlowUp_restrictMap_blowUpStepOf
    (hZ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c)
    {W : Set P.space} {c' : ℕ} (hW : IsClosedSubmanifold ψ W c')
    (hWe : W = P.isClosedSubmanifold.imageVal (P.iso '' Z)) (hc' : c' = c + s)
    {π : AnalyticMap T' Tᵢ} (hπ : IsBlowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c π) :
    IsBlowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) (P.iso '' Z) c
      ((P.blowUpStepOf hZ hW hWe hc' hπ).isClosedSubmanifold.restrictMap P.isClosedSubmanifold
        (blowUpπ ψ hW) (isBlowUp_blowUpπ ψ hW).contMDiff
        (strictTransform_subset_preimage (blowUpπ ψ hW).contMDiff.continuous
          P.isClosedSubmanifold.isClosed)) := by
  subst hWe; subst hc'
  exact P.isBlowUp_restrictMap_imageVal hZ

/-- `pushforwardAux` respects equality of stages and of lists (a `subst`; the two sides live on
the two `blowUp`s). -/
theorem PushforwardStage.heq_pushforwardAux {P₁ P₂ : PushforwardStage ψ s Tᵢ} (e : P₁ = P₂)
    {L₁ L₂ : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Tᵢ}
        (hL : L₁ = L₂) :
    HEq (AnalyticManifold.BlowUpSequence.pushforwardAux P₁ L₁)
        (AnalyticManifold.BlowUpSequence.pushforwardAux P₂ L₂) := by
  subst e; subst hL; rfl

end StepOf

/-! ### Uniqueness of the lift of a local isomorphism -/

section LiftUnique

variable {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {N : AnalyticManifold.{u} 𝕜 E}

/-- A continuous map over the local analytic isomorphism `h` between the blowings-up is THE lift
`liftStep h hh hY`, by `eqOn_liftPartialDiffeomorph_of_comm`
(`Hironaka/Manifold/FiniteSuccession/Lift.lean`) on the chart of `h` at each point (the uniqueness
of a blowing-up up to an isomorphism commuting with the blow-down, [BM88, Definition 4.1]; the lift
of [Kol07, Definition 30.1]). -/
theorem _root_.AnalyticManifold.BlowUpSequence.eq_liftStep_of_comm (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c)
    (G : blowUp ψ₀ (hY.preimage_of_isLocalDiffeomorph hh) → blowUp ψ₀ hY) (hG : Continuous G)
    (hGπ : ∀ q, blowUpπ ψ₀ hY (G q) = h (blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh) q)) :
    G = ⇑(AnalyticManifold.BlowUpSequence.liftStep h hh hY) := by
  funext q
  have : Nonempty (blowUp ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)) := ⟨q⟩
  have : Nonempty (blowUp ψ₀ hY) := ⟨G q⟩
  obtain ⟨Φ, hqΦ, hΦ⟩ :=
    (hh (blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh) q)).exists_partialDiffeomorph
  have e₁ := eqOn_liftPartialDiffeomorph_of_comm hY hh (isBlowUp_blowUpπ ψ₀ hY)
    (isBlowUp_blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)) hG hGπ hΦ hqΦ
  have e₂ := eqOn_liftPartialDiffeomorph_of_comm hY hh (isBlowUp_blowUpπ ψ₀ hY)
    (isBlowUp_blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh))
    (AnalyticManifold.BlowUpSequence.liftStep h hh hY).contMDiff.continuous
        (AnalyticManifold.BlowUpSequence.blowUpπ_liftStep h hh hY) hΦ hqΦ
  exact e₁.trans e₂.symm

end LiftUnique

/-! ### The nested stage `S ⊂ Y ⊂ M` -/

section Nest

variable {s : ℕ} {T_S : AnalyticManifold.{u} 𝕜 (Fin (n - s - 1) → 𝕜)}
  (P_S : PushforwardStage (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) 1 T_S)
  (P_Y : PushforwardStage ψ s P_S.space)

/-- The image `j_Y(S̃) ⊆ X` of the strict transform of `S` under the closed embedding of the
strict transform of `Y` is a closed submanifold of codimension `s + 1`
(`imageVal_isClosedSubmanifold`). -/
theorem PushforwardStage.isClosedSubmanifold_nest :
    IsClosedSubmanifold ψ (⇑P_Y.incl '' P_S.sub) (s + 1) := by
  rw [Nat.add_comm, ← P_Y.imageVal_image_eq]
  exact P_Y.isClosedSubmanifold.imageVal_isClosedSubmanifold
    (P_S.isClosedSubmanifold.image_diffeomorph P_Y.iso)

/-- A point of `j_Y(S̃)` lies in `Ỹ`. -/
theorem PushforwardStage.mem_sub_of_mem_image_incl {x : P_Y.space}
    (hx : x ∈ ⇑P_Y.incl '' P_S.sub) : x ∈ P_Y.sub := by
  rw [← P_Y.range_incl]
  obtain ⟨t, -, rfl⟩ := hx
  exact ⟨t, rfl⟩

/-- The point of `T_Y` under a point of `j_Y(S̃)` lies in `S̃`. -/
theorem PushforwardStage.iso_symm_mk_mem_sub {x : P_Y.space} (hx : x ∈ ⇑P_Y.incl '' P_S.sub) :
    P_Y.iso.symm ⟨x, PushforwardStage.mem_sub_of_mem_image_incl P_S P_Y hx⟩ ∈ P_S.sub := by
  obtain ⟨t, ht, rfl⟩ := hx
  have : (⟨P_Y.incl t, PushforwardStage.mem_sub_of_mem_image_incl P_S P_Y ⟨t, ht, rfl⟩⟩ :
      P_Y.isClosedSubmanifold.toAnalyticManifold) = P_Y.iso t := Subtype.ext rfl
  rw [this, P_Y.iso.symm_apply_apply]
  exact ht

/-- The **nested stage** `S̃ ⊆ Ỹ ⊆ X` as a stage for `S` of codimension `s + 1` — the ambient of
`Y`'s stage, the image `j_Y(S̃)` of the strict transform of `S` and the composed identification
`iso_Y ∘ iso_S` (`PushforwardStage`). -/
def PushforwardStage.nest : PushforwardStage ψ (s + 1) T_S where
  space := P_Y.space
  sub := ⇑P_Y.incl '' P_S.sub
  isClosedSubmanifold := PushforwardStage.isClosedSubmanifold_nest P_S P_Y
  iso :=
    let f : T_S → (PushforwardStage.isClosedSubmanifold_nest P_S P_Y).toAnalyticManifold :=
      fun t => ⟨P_Y.incl (P_S.incl t), ⟨P_S.incl t, P_S.incl_mem_sub t, rfl⟩⟩
    let g₁ : (PushforwardStage.isClosedSubmanifold_nest P_S P_Y).toAnalyticManifold →
        P_Y.isClosedSubmanifold.toAnalyticManifold :=
      fun x => ⟨x.1, PushforwardStage.mem_sub_of_mem_image_incl P_S P_Y x.2⟩
    let g₂ : (PushforwardStage.isClosedSubmanifold_nest P_S P_Y).toAnalyticManifold →
        P_S.isClosedSubmanifold.toAnalyticManifold :=
      fun x => ⟨P_Y.iso.symm (g₁ x), PushforwardStage.iso_symm_mk_mem_sub P_S P_Y x.2⟩
    have hf : ContMDiff 𝓘(𝕜, Fin (n - s - 1) → 𝕜) 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) ω f :=
      (PushforwardStage.isClosedSubmanifold_nest P_S P_Y).contMDiff_codRestrict
        (P_Y.incl.contMDiff.comp P_S.incl.contMDiff) _
    have hg₁ : ContMDiff 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) ω g₁ :=
      P_Y.isClosedSubmanifold.contMDiff_codRestrict
        (PushforwardStage.isClosedSubmanifold_nest P_S P_Y).inclusionMap.contMDiff _
    have hg₂ : ContMDiff 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) 𝓘(𝕜, Fin (n - s - 1) → 𝕜) ω g₂ :=
      P_S.isClosedSubmanifold.contMDiff_codRestrict (P_Y.iso.symm.contMDiff.comp hg₁) _
    { toFun := f
      invFun := fun x => P_S.iso.symm (g₂ x)
      left_inv := fun t => by
        have h1 : g₁ (f t) = P_Y.iso (P_S.incl t) := Subtype.ext rfl
        have h2 : g₂ (f t) = P_S.iso t := by
          refine Subtype.ext ?_
          change P_Y.iso.symm (g₁ (f t)) = P_S.incl t
          rw [h1, P_Y.iso.symm_apply_apply]
        change P_S.iso.symm (g₂ (f t)) = t
        rw [h2, P_S.iso.symm_apply_apply]
      right_inv := fun x => by
        obtain ⟨x, y, hy, rfl⟩ := x
        have h1 : g₁ ⟨P_Y.incl y, ⟨y, hy, rfl⟩⟩ = P_Y.iso y := Subtype.ext rfl
        have h2 : g₂ ⟨P_Y.incl y, ⟨y, hy, rfl⟩⟩ = ⟨y, hy⟩ :=
          Subtype.ext ((DFunLike.congr_arg P_Y.iso.symm h1).trans (P_Y.iso.symm_apply_apply y))
        have h3 : P_S.incl (P_S.iso.symm ⟨y, hy⟩) = y :=
          congrArg Subtype.val (P_S.iso.apply_symm_apply ⟨y, hy⟩)
        refine Subtype.ext ?_
        change P_Y.incl (P_S.incl (P_S.iso.symm (g₂ ⟨P_Y.incl y, ⟨y, hy, rfl⟩⟩))) = P_Y.incl y
        rw [h2, h3]
      contMDiff_toFun := hf
      contMDiff_invFun := P_S.iso.symm.contMDiff.comp hg₂ }

/-- The inclusion of the nested stage is the composite of the inclusions. -/
theorem PushforwardStage.incl_nest (t : T_S) :
    (PushforwardStage.nest P_S P_Y).incl t = P_Y.incl (P_S.incl t) := rfl

/-- The ambient of the nested stage. -/
theorem PushforwardStage.space_nest : (PushforwardStage.nest P_S P_Y).space = P_Y.space := rfl

/-- The strict transform of the nested stage is `j_Y(S̃)`. -/
theorem PushforwardStage.sub_nest :
    (PushforwardStage.nest P_S P_Y).sub = ⇑P_Y.incl '' P_S.sub := rfl

end Nest

/-! ### The next stage of the nested stage is the nested next stage -/

section NestStep

variable {s : ℕ} {T_S : AnalyticManifold.{u} 𝕜 (Fin (n - s - 1) → 𝕜)}
  (P_S : PushforwardStage (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) 1 T_S)
  (P_Y : PushforwardStage ψ s P_S.space) {Z : Set T_S} {c : ℕ}
  (hZ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s - 1) → 𝕜)) Z c)
  (hW₁ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
    (P_S.isClosedSubmanifold.imageVal (P_S.iso '' Z)) (c + 1))

/-- The centre pushed forward through the nested stage is the centre pushed forward through the
two stages (`imageVal_image_eq`). -/
theorem PushforwardStage.imageVal_nest_eq :
    (PushforwardStage.nest P_S P_Y).isClosedSubmanifold.imageVal
        ((PushforwardStage.nest P_S P_Y).iso '' Z) =
      P_Y.isClosedSubmanifold.imageVal
        (P_Y.iso '' (P_S.isClosedSubmanifold.imageVal (P_S.iso '' Z))) :=
  ((PushforwardStage.nest P_S P_Y).imageVal_image_eq Z).trans <|
    (Set.image_image (⇑P_Y.incl) (⇑P_S.incl) Z).symm.trans <| by
      rw [P_Y.imageVal_image_eq, P_S.imageVal_image_eq]

/-- The next stage of the nested stage, with the ambient centre `j_Y(j_S(Z))` as the datum
(`blowUpStepOf`). -/
def PushforwardStage.nestStep :
    PushforwardStage ψ (s + 1) (blowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s - 1) → 𝕜)) hZ) :=
  (PushforwardStage.nest P_S P_Y).blowUpStepOf hZ (P_Y.isClosedSubmanifold_imageVal_image hW₁)
    (PushforwardStage.imageVal_nest_eq P_S P_Y (Z := Z)).symm
    ((Nat.add_right_comm c 1 s).trans (Nat.add_assoc c s 1)) (isBlowUp_blowUpπ _ hZ)

/-- `nestStep` IS the next stage of the nested stage. -/
theorem PushforwardStage.nestStep_eq :
    PushforwardStage.nestStep P_S P_Y hZ hW₁ =
      (PushforwardStage.nest P_S P_Y).blowUpStep hZ (isBlowUp_blowUpπ _ hZ) :=
  PushforwardStage.blowUpStepOf_eq _ _ _ _ _ _

/-- The restricted blow-down of the next stage of the nested stage (`restrictMap`). -/
def PushforwardStage.nestStepπ :
    AnalyticMap (PushforwardStage.nestStep P_S P_Y hZ hW₁).isClosedSubmanifold.toAnalyticManifold
      (PushforwardStage.nest P_S P_Y).isClosedSubmanifold.toAnalyticManifold :=
  (PushforwardStage.nestStep P_S P_Y hZ hW₁).isClosedSubmanifold.restrictMap
    (PushforwardStage.nest P_S P_Y).isClosedSubmanifold
    (blowUpπ ψ (P_Y.isClosedSubmanifold_imageVal_image hW₁)) (isBlowUp_blowUpπ ψ _).contMDiff
    (strictTransform_subset_preimage (blowUpπ ψ _).contMDiff.continuous
      (PushforwardStage.nest P_S P_Y).isClosedSubmanifold.isClosed)

/-- The restricted blow-down `nestStepπ` is a blowing-up of the nested strict transform along the
identified centre ([Kol07, Definition 30.3]). -/
theorem PushforwardStage.isBlowUp_nestStepπ :
    IsBlowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - (s + 1)) → 𝕜))
      ((PushforwardStage.nest P_S P_Y).iso '' Z) c (PushforwardStage.nestStepπ P_S P_Y hZ hW₁) :=
  (PushforwardStage.nest P_S P_Y).isBlowUp_restrictMap_blowUpStepOf hZ _ _ _ _

/-- The square of `nestStepπ` with the identification of `nestStep`. -/
theorem PushforwardStage.nestStepπ_iso
    (p : blowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s - 1) → 𝕜)) hZ) :
    PushforwardStage.nestStepπ P_S P_Y hZ hW₁ ((PushforwardStage.nestStep P_S P_Y hZ hW₁).iso p) =
      (PushforwardStage.nest P_S P_Y).iso (blowUpπ _ hZ p) :=
  (PushforwardStage.nest P_S P_Y).restrictMap_blowUpStepOf_iso hZ _ _ _ _ p

/-- The comparison of the strict transforms through the two ambient blowings-up — the image under
the lifted closed embedding `Bl Ỹ ↪ Bl X` (the inclusion of `Y`'s next stage) of the strict
transform of `S̃` in `Bl Ỹ` is the strict transform of `j_Y(S̃)` in `Bl X` ([Kol07, Definition
30.3]). Both are closures: the closed embedding carries closures to closures
(`IsClosedEmbedding.closure_image_eq`), and off the centres the two preimages correspond by the
square `blowUpπ_incl_blowUpStep` and the injectivity of `j_Y`. -/
theorem PushforwardStage.image_incl_strictTransformSet :
    ⇑(P_Y.blowUpStep hW₁ (isBlowUp_blowUpπ _ hW₁)).incl ''
        strictTransformSet (blowUpπ _ hW₁) (P_S.isClosedSubmanifold.imageVal (P_S.iso '' Z))
          P_S.sub =
      strictTransformSet (blowUpπ ψ (P_Y.isClosedSubmanifold_imageVal_image hW₁))
        (P_Y.isClosedSubmanifold.imageVal
          (P_Y.iso '' (P_S.isClosedSubmanifold.imageVal (P_S.iso '' Z))))
        (⇑P_Y.incl '' P_S.sub) := by
  have hsq := P_Y.blowUpπ_incl_blowUpStep hW₁
  unfold strictTransformSet
  rw [← (P_Y.blowUpStep hW₁ (isBlowUp_blowUpπ _ hW₁)).isClosedEmbedding_incl.closure_image_eq]
  congr 1
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have h1 : blowUpπ ψ (P_Y.isClosedSubmanifold_imageVal_image hW₁)
        ((P_Y.blowUpStep hW₁ (isBlowUp_blowUpπ _ hW₁)).incl q) ∈ ⇑P_Y.incl '' P_S.sub := by
      rw [hsq]
      exact ⟨_, hq.1, rfl⟩
    have h2 : blowUpπ ψ (P_Y.isClosedSubmanifold_imageVal_image hW₁)
        ((P_Y.blowUpStep hW₁ (isBlowUp_blowUpπ _ hW₁)).incl q) ∉
          P_Y.isClosedSubmanifold.imageVal
            (P_Y.iso '' (P_S.isClosedSubmanifold.imageVal (P_S.iso '' Z))) := by
      rw [hsq, P_Y.imageVal_image_eq]
      rintro ⟨w, hw, hwq⟩
      refine hq.2 ?_
      rw [← P_Y.isClosedEmbedding_incl.injective hwq]
      exact hw
    exact ⟨h1, h2⟩
  · rintro ⟨⟨t, ht, hpt⟩, hpW⟩
    have hpY : blowUpπ ψ (P_Y.isClosedSubmanifold_imageVal_image hW₁) p ∈ P_Y.sub := by
      rw [← hpt, ← P_Y.range_incl]
      exact Set.mem_range_self t
    have hpsub : p ∈ Set.range ⇑(P_Y.blowUpStep hW₁ (isBlowUp_blowUpπ _ hW₁)).incl :=
      (congrArg (fun S => p ∈ S) (P_Y.blowUpStep hW₁ (isBlowUp_blowUpπ _ hW₁)).range_incl).mpr
        (subset_closure ⟨hpY, hpW⟩)
    obtain ⟨q, hq⟩ := hpsub
    have e1 : P_Y.incl (blowUpπ _ hW₁ q) =
        blowUpπ ψ (P_Y.isClosedSubmanifold_imageVal_image hW₁)
          ((P_Y.blowUpStep hW₁ (isBlowUp_blowUpπ _ hW₁)).incl q) := (hsq q).symm
    have e2 : blowUpπ ψ (P_Y.isClosedSubmanifold_imageVal_image hW₁)
        ((P_Y.blowUpStep hW₁ (isBlowUp_blowUpπ _ hW₁)).incl q) =
          blowUpπ ψ (P_Y.isClosedSubmanifold_imageVal_image hW₁) p :=
      congrArg (⇑(blowUpπ ψ (P_Y.isClosedSubmanifold_imageVal_image hW₁))) hq
    have hqt : blowUpπ _ hW₁ q = t :=
      P_Y.isClosedEmbedding_incl.injective (e1.trans (e2.trans hpt.symm))
    have h5 : blowUpπ _ hW₁ q ∈ P_S.sub := by
      rw [hqt]
      exact ht
    have h6 : blowUpπ _ hW₁ q ∉ P_S.isClosedSubmanifold.imageVal (P_S.iso '' Z) := by
      intro hqW
      refine hpW ?_
      rw [← e2, hsq, P_Y.imageVal_image_eq]
      exact ⟨_, hqW, rfl⟩
    exact ⟨q, ⟨h5, h6⟩, hq⟩

/-- The inclusion of the next stage of the nested stage is the inclusion of the nested next
stages, pointwise — both are lifts of the nested inclusion to the blowings-up
(`IsBlowUp.eqOn_of_comp_eq`, `BlowUp/Unique.lean`; the uniqueness of a blowing-up up to an
isomorphism commuting with the blow-down, [BM88, Definition 4.1]), the second through
`image_incl_strictTransformSet`. -/
theorem PushforwardStage.incl_nestStep
    (q : blowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s - 1) → 𝕜)) hZ) :
    (PushforwardStage.nestStep P_S P_Y hZ hW₁).incl q =
      (PushforwardStage.nest (P_S.blowUpStep hZ (isBlowUp_blowUpπ _ hZ))
        (P_Y.blowUpStep hW₁ (isBlowUp_blowUpπ _ hW₁))).incl q := by
  have hmem : ∀ q', (PushforwardStage.nest (P_S.blowUpStep hZ (isBlowUp_blowUpπ _ hZ))
      (P_Y.blowUpStep hW₁ (isBlowUp_blowUpπ _ hW₁))).incl q' ∈
        (PushforwardStage.nestStep P_S P_Y hZ hW₁).sub :=
    fun q' => (congrArg (fun S => (PushforwardStage.nest (P_S.blowUpStep hZ (isBlowUp_blowUpπ _ hZ))
      (P_Y.blowUpStep hW₁ (isBlowUp_blowUpπ _ hW₁))).incl q' ∈ S)
        (PushforwardStage.image_incl_strictTransformSet P_S P_Y hW₁)).mp
      ((PushforwardStage.nest (P_S.blowUpStep hZ (isBlowUp_blowUpπ _ hZ))
        (P_Y.blowUpStep hW₁ (isBlowUp_blowUpπ _ hW₁))).incl_mem_sub q')
  let G' : blowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s - 1) → 𝕜)) hZ →
      (PushforwardStage.nestStep P_S P_Y hZ hW₁).isClosedSubmanifold.toAnalyticManifold :=
    fun q' => ⟨(PushforwardStage.nest (P_S.blowUpStep hZ (isBlowUp_blowUpπ _ hZ))
      (P_Y.blowUpStep hW₁ (isBlowUp_blowUpπ _ hW₁))).incl q', hmem q'⟩
  have hG' : Continuous G' :=
    Continuous.subtype_mk (PushforwardStage.nest (P_S.blowUpStep hZ (isBlowUp_blowUpπ _ hZ))
      (P_Y.blowUpStep hW₁ (isBlowUp_blowUpπ _ hW₁))).incl.contMDiff.continuous _
  have hπ' : ∀ q', PushforwardStage.nestStepπ P_S P_Y hZ hW₁ (G' q') =
      (PushforwardStage.nest P_S P_Y).iso (blowUpπ _ hZ q') :=
    fun q' => Subtype.ext
      ((P_Y.blowUpπ_incl_blowUpStep hW₁ ((P_S.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)).incl q')).trans
        (DFunLike.congr_arg P_Y.incl (P_S.blowUpπ_incl_blowUpStep hZ q')))
  have heq : Set.EqOn ⇑(PushforwardStage.nestStep P_S P_Y hZ hW₁).iso G' Set.univ :=
    IsBlowUp.eqOn_of_comp_eq (hZ.image_diffeomorph (PushforwardStage.nest P_S P_Y).iso)
      ((isBlowUp_blowUpπ _ hZ).diffeomorph_comp (PushforwardStage.nest P_S P_Y).iso)
      (PushforwardStage.isBlowUp_nestStepπ P_S P_Y hZ hW₁) isOpen_univ
      (PushforwardStage.nestStep P_S P_Y hZ hW₁).iso.continuous.continuousOn hG'.continuousOn
      (fun q' _ => PushforwardStage.nestStepπ_iso P_S P_Y hZ hW₁ q') (fun q' _ => hπ' q')
  exact congrArg Subtype.val (heq (Set.mem_univ q))

/-- The next stage of the nested stage is the nested next stage — the pull-back-stage invariant
(`IsPullbackStage`, `Functor/PushforwardPullback.lean`) along the identity of the common ambient
`Bl X`. -/
theorem PushforwardStage.isPullbackStage_nestStep :
    PushforwardStage.IsPullbackStage (PushforwardStage.nestStep P_S P_Y hZ hW₁)
      (PushforwardStage.nest (P_S.blowUpStep hZ (isBlowUp_blowUpπ _ hZ))
        (P_Y.blowUpStep hW₁ (isBlowUp_blowUpπ _ hW₁)))
      ContMDiffMap.id ContMDiffMap.id where
  isLocalDiffeomorph := AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id _
  sub_eq := (PushforwardStage.image_incl_strictTransformSet P_S P_Y hW₁).trans rfl
  square := fun q => PushforwardStage.incl_nestStep P_S P_Y hZ hW₁ q

end NestStep

section NestList

variable {s : ℕ}

/-- The list induction: pushing a list forward through `S̃ ⊆ Ỹ` and then through `Ỹ ⊆ X` is
pushing it forward through the nested stage (`pushforwardAux_pullback` at the invariant
`isPullbackStage_nestStep`, the identity pull-backs removed by `pullback_id`). -/
theorem _root_.AnalyticManifold.BlowUpSequence.pushforwardAux_nest :
    ∀ {T_S : AnalyticManifold.{u} 𝕜 (Fin (n - s - 1) → 𝕜)}
      (P_S : PushforwardStage (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) 1 T_S)
      (P_Y : PushforwardStage ψ s P_S.space)
      (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin
          (n - s - 1) → 𝕜)) T_S),
      AnalyticManifold.BlowUpSequence.pushforwardAux P_Y
          (AnalyticManifold.BlowUpSequence.pushforwardAux P_S L) =
        AnalyticManifold.BlowUpSequence.pushforwardAux (PushforwardStage.nest P_S P_Y) L
  | _, P_S, P_Y, AnalyticManifold.BlowUpSequence.nil _ => rfl
  | _, P_S, P_Y, @AnalyticManifold.BlowUpSequence.cons _ _ _ _ _ _ _ _ Z c hZ rest => by
    have hIH := AnalyticManifold.BlowUpSequence.pushforwardAux_nest (P_S.blowUpStep hZ
        (isBlowUp_blowUpπ _ hZ))
      (P_Y.blowUpStep (P_S.isClosedSubmanifold_imageVal_image hZ) (isBlowUp_blowUpπ _ _)) rest
    have hpb := PushforwardStage.pushforwardAux_pullback
      (PushforwardStage.nestStep P_S P_Y hZ (P_S.isClosedSubmanifold_imageVal_image hZ))
      (PushforwardStage.nest (P_S.blowUpStep hZ (isBlowUp_blowUpπ _ hZ))
        (P_Y.blowUpStep (P_S.isClosedSubmanifold_imageVal_image hZ) (isBlowUp_blowUpπ _ _)))
      ContMDiffMap.id ContMDiffMap.id (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id _)
      (PushforwardStage.isPullbackStage_nestStep P_S P_Y hZ
        (P_S.isClosedSubmanifold_imageVal_image hZ)) rest
    have hpb' : AnalyticManifold.BlowUpSequence.pushforwardAux
        (PushforwardStage.nestStep P_S P_Y hZ (P_S.isClosedSubmanifold_imageVal_image hZ)) rest =
        AnalyticManifold.BlowUpSequence.pushforwardAux (PushforwardStage.nest (P_S.blowUpStep hZ
            (isBlowUp_blowUpπ _ hZ))
          (P_Y.blowUpStep (P_S.isClosedSubmanifold_imageVal_image hZ) (isBlowUp_blowUpπ _ _)))
          rest :=
      (AnalyticManifold.BlowUpSequence.pullback_id _).symm.trans
        (hpb.trans (congrArg (AnalyticManifold.BlowUpSequence.pushforwardAux _)
            (AnalyticManifold.BlowUpSequence.pullback_id rest)))
    refine AnalyticManifold.BlowUpSequence.cons_congr_heq_of_eq
        (PushforwardStage.imageVal_nest_eq P_S P_Y (Z := Z)).symm
      ((Nat.add_right_comm c 1 s).trans (Nat.add_assoc c s 1)) _ _ _ _ ?_
    exact HEq.trans (heq_of_eq (hIH.trans hpb'.symm))
      (PushforwardStage.heq_pushforwardAux (PushforwardStage.nestStep_eq P_S P_Y hZ _) rfl)

end NestList

/-- Pushing a list forward from the hypersurface `S` of `Y` to `Y` and then from `Y` (codimension
`s`) to `M` is pushing it forward from `S` (codimension `s + 1`) to `M`, the list read on the two
bundled structures through the isomorphism `e` of
`exists_diffeomorph_toAnalyticManifold_of_flag` — the raw form with ordinary `pushforward`s ([Kol07,
Definition 30.3] along the flag of [Kol07, 108]); the `pushforwardRestrict` form follows through
`pushforwardRestrictOf_eq`. The two stages `⟨Y-bundle, j_Y⁻¹ S, hSY, refl⟩` and `⟨M, Y, hY, refl⟩`
nest to a stage for `S` which is the pull-back stage of `⟨M, S, hS, refl⟩` along the identity of `M`
and `e` (`he` is the square), and `pushforwardAux_nest` with `pushforwardAux_pullback` finish. -/
theorem _root_.AnalyticManifold.BlowUpSequence.pushforward_pushforward_of_flag {Y S : Set M} {s : ℕ}
    (hY : IsClosedSubmanifold ψ Y s) (hS : IsClosedSubmanifold ψ S (s + 1))
    (hSY : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      (⇑hY.inclusionMap ⁻¹' S) 1)
    (e : Diffeomorph 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜)
      (hSY.toAnalyticManifold : AnalyticManifold.{u} 𝕜 (Fin (n - (s + 1)) → 𝕜))
      hS.toAnalyticManifold ω)
    (he : ∀ x : hSY.toAnalyticManifold.carrier,
      (hS.inclusionMap (e x) : M) = hY.inclusionMap (hSY.inclusionMap x))
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n -
        (s + 1)) → 𝕜)) hS.toAnalyticManifold) :
    ((L.pullback (⟨⇑e, e.contMDiff⟩ : AnalyticMap
        (hSY.toAnalyticManifold : AnalyticManifold.{u} 𝕜 (Fin (n - (s + 1)) → 𝕜))
        hS.toAnalyticManifold) e.isLocalDiffeomorph).pushforward hSY).pushforward hY =
      L.pushforward hS := by
  have hSY' : S ⊆ Y := by
    intro x hx
    have h := he (e.symm ⟨x, hx⟩)
    have h2 : (hS.inclusionMap (e (e.symm ⟨x, hx⟩)) : M) = x :=
      congrArg (fun z => (hS.inclusionMap z : M)) (e.apply_symm_apply ⟨x, hx⟩)
    rw [h2.symm.trans h]
    exact (hSY.inclusionMap (e.symm ⟨x, hx⟩)).2
  let P_S : PushforwardStage (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) 1
      hSY.toAnalyticManifold := ⟨hY.toAnalyticManifold, _, hSY, Diffeomorph.refl _ _ _⟩
  let P_Y : PushforwardStage ψ s P_S.space := ⟨M, Y, hY, Diffeomorph.refl _ _ _⟩
  have h1 := AnalyticManifold.BlowUpSequence.pushforwardAux_nest P_S P_Y
    (L.pullback (⟨⇑e, e.contMDiff⟩ : AnalyticMap
        (hSY.toAnalyticManifold : AnalyticManifold.{u} 𝕜 (Fin (n - (s + 1)) → 𝕜))
        hS.toAnalyticManifold) e.isLocalDiffeomorph)
  have hps : PushforwardStage.IsPullbackStage
      (⟨M, S, hS, Diffeomorph.refl _ _ _⟩ : PushforwardStage ψ (s + 1) hS.toAnalyticManifold)
      (PushforwardStage.nest P_S P_Y) ContMDiffMap.id
      (⟨⇑e, e.contMDiff⟩ : AnalyticMap
        (hSY.toAnalyticManifold : AnalyticManifold.{u} 𝕜 (Fin (n - (s + 1)) → 𝕜))
        hS.toAnalyticManifold) :=
    { isLocalDiffeomorph := AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id _
      sub_eq := by
        have h : ⇑hY.inclusionMap '' (⇑hY.inclusionMap ⁻¹' S) = S :=
          Set.image_preimage_eq_of_subset fun x hx => ⟨⟨x, hSY' hx⟩, rfl⟩
        exact h
      square := fun q => he q }
  have hpb := PushforwardStage.pushforwardAux_pullback
    (⟨M, S, hS, Diffeomorph.refl _ _ _⟩ : PushforwardStage ψ (s + 1) hS.toAnalyticManifold)
    (PushforwardStage.nest P_S P_Y) ContMDiffMap.id _ e.isLocalDiffeomorph hps L
  exact h1.trans ((AnalyticManifold.BlowUpSequence.pullback_id _).symm.trans hpb).symm

/-! ### The codimension-zero case -/

section Standard

variable {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-- The codimension-zero case, generalised over the stage: for a stage of codimension `0` whose
inclusion is a local analytic isomorphism and a list on its ambient with every centre over the
(clopen) image (`CentersOver`, `Principalization/IsoOff.lean`), pushing forward the pull-back along
the inclusion is the identity. Per step: the pushed-forward centre is the centre itself (it lies in
the image), the next inclusion is THE lift of the inclusion (`eq_liftStep_of_comm`), and the strict
transform of the open image contains the whole preimage of the image
(`IsBlowUp.dense_preimage_compl`), so the remaining centres lie over it. -/
theorem _root_.AnalyticManifold.BlowUpSequence.pushforwardAux_pullback_incl_of_centersOver :
    ∀ {Tᵢ : AnalyticManifold.{u} 𝕜 (Fin (n - 0) → 𝕜)}
      (P : PushforwardStage (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) 0 Tᵢ)
      (hloc : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω P.incl)
      (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) P.space),
      L.toSuccession.CentersOver P.sub →
      AnalyticManifold.BlowUpSequence.pushforwardAux P (L.pullback P.incl hloc) = L
  | _, P, hloc, AnalyticManifold.BlowUpSequence.nil _, _ => rfl
  | _, P, hloc, @AnalyticManifold.BlowUpSequence.cons _ _ _ _ _ _ _ _ Z c hZ rest, hL => by
    -- (i) the first centre lies in the image
    have hZsub : Z ⊆ P.sub := by
      intro x hx
      have h0 := hL ⟨0, Nat.succ_pos _⟩
      have hx' :
          x ∈ ((AnalyticManifold.BlowUpSequence.cons hZ rest).toSuccession.center ⟨0,
              Nat.succ_pos _⟩).support := by
        change x ∈ hZ.idealSheaf.support
        rw [hZ.cosupport_idealSheaf]
        exact hx
      exact h0 hx'
    have e : P.isClosedSubmanifold.imageVal (P.iso '' (⇑P.incl ⁻¹' Z)) = Z := by
      rw [P.imageVal_image_eq, Set.image_preimage_eq_inter_range, P.range_incl,
        Set.inter_eq_left.mpr hZsub]
    -- (ii) the next stage, with the ambient centre `Z` itself
    set hZ' := hZ.preimage_of_isLocalDiffeomorph hloc
    set P₁ := P.blowUpStepOf hZ' hZ e.symm rfl (isBlowUp_blowUpπ _ hZ')
    have hsq : ∀ q, blowUpπ _ hZ (P₁.incl q) = P.incl (blowUpπ _ hZ' q) := fun q =>
      P.blowUpπ_incl_blowUpStepOf hZ' hZ e.symm rfl (isBlowUp_blowUpπ _ hZ') q
    have hincl : ⇑P₁.incl = ⇑(AnalyticManifold.BlowUpSequence.liftStep P.incl hloc hZ) :=
      AnalyticManifold.BlowUpSequence.eq_liftStep_of_comm P.incl hloc hZ _
          P₁.incl.contMDiff.continuous hsq
    have hloc₁ : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω P₁.incl := by
      rw [hincl]
      exact AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep _ _ _
    -- (iii) the centres of the rest lie over the strict transform of the clopen image
    have hopen : IsOpen P.sub := by
      rw [← P.range_incl]
      exact hloc.isOpenMap.isOpen_range
    have hsubP₁ : ⇑(blowUpπ _ hZ) ⁻¹' P.sub ⊆ P₁.sub := by
      change ⇑(blowUpπ _ hZ) ⁻¹' P.sub ⊆ closure (⇑(blowUpπ _ hZ) ⁻¹' (P.sub \ Z))
      refine (((isBlowUp_blowUpπ _ hZ).dense_preimage_compl hZ).open_subset_closure_inter
        (hopen.preimage (blowUpπ _ hZ).contMDiff.continuous)).trans (closure_mono ?_)
      rintro r ⟨hr1, hr2⟩
      exact ⟨hr1, hr2⟩
    have hrest : rest.toSuccession.CentersOver P₁.sub := by
      intro i p hp
      have h1 : ((AnalyticManifold.BlowUpSequence.cons hZ rest).toSuccession.center
          (Fin.succ i)).support ⊆
          ⇑((AnalyticManifold.BlowUpSequence.cons hZ rest).toSuccession.stageMap
              (Fin.succ i).castSucc) ⁻¹' P.sub :=
        hL (Fin.succ i)
      have hi : i.1 + 1 < (AnalyticManifold.BlowUpSequence.cons hZ rest).toSuccession.length + 1 :=
        Nat.succ_lt_succ (Nat.lt_succ_of_lt i.2)
      have h3 : (AnalyticManifold.BlowUpSequence.cons hZ rest).toSuccession.stageMapAux
          (i.1 + 1) hi p ∈ P.sub := h1 hp
      have h4 := AnalyticManifold.BlowUpSequence.stageMapAux_cons_succ hZ rest i.1 hi p
      rw [h4] at h3
      exact hsubP₁ h3
    -- (iv) assemble
    have hIH := AnalyticManifold.BlowUpSequence.pushforwardAux_pullback_incl_of_centersOver P₁
        hloc₁ rest hrest
    have hpull : rest.pullback (AnalyticManifold.BlowUpSequence.liftStep P.incl hloc hZ)
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep _ _ _) = rest.pullback P₁.incl
            hloc₁ :=
      AnalyticManifold.BlowUpSequence.pullback_congr rest (ContMDiffMap.ext fun q =>
          (congrFun hincl q).symm) _ _
    refine AnalyticManifold.BlowUpSequence.cons_congr_heq_of_eq e rfl _ hZ _ rest ?_
    exact HEq.trans (PushforwardStage.heq_pushforwardAux
      (P.blowUpStepOf_eq hZ' hZ e.symm rfl (isBlowUp_blowUpπ _ hZ')).symm hpull) (heq_of_eq hIH)
termination_by _ _ _ L _ => L.toSuccession.length
decreasing_by exact Nat.lt_succ_self _

/-- For `S` clopen in `M` with `S ↪ M` a local analytic isomorphism and a list whose centres lie
over `S` (`CentersOver`), the push-forward along `S ↪ M` of the pull-back along the (open)
inclusion is the list itself — `pushforwardAux_pullback_incl_of_centersOver` at the stage
`⟨M, S, hS, refl⟩`. -/
theorem _root_.AnalyticManifold.BlowUpSequence.pushforward_pullback_inclusionMap_of_centersOver
    {S : Set M}
    (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) S 0)
    (hloc : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω hS.inclusionMap)
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hL : L.toSuccession.CentersOver S) :
    (L.pullback hS.inclusionMap hloc).pushforward hS = L :=
  AnalyticManifold.BlowUpSequence.pushforwardAux_pullback_incl_of_centersOver
    (⟨M, S, hS, Diffeomorph.refl _ _ _⟩ : PushforwardStage _ 0 hS.toAnalyticManifold) hloc L hL

end Standard

end Manifold

end
