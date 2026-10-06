/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.Restrict
public import Hironaka.Manifold.FiniteSuccession.Restrict.ImageVal
public import Hironaka.Manifold.BlowUp.Transform.StrictCharts
public import Hironaka.Manifold.BlowUp.Unique
public import Hironaka.Manifold.FiniteSuccession.Cons
import Hironaka.Manifold.BlowUp.Transform.Object
public import Hironaka.Manifold.FiniteSuccession.Restrict.BaseTransport
import Hironaka.Manifold.FiniteSuccession.Restrict.CongrChart
import Hironaka.Manifold.FiniteSuccession.Restrict.Lift
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The push-forward of a blow-up sequence from a closed submanifold

Given a blow-up sequence `B(S) : S_r → ⋯ → S_0 = S` with centres `Z_i^S ⊂ S_i` of a closed
subscheme `S ⊆ X`, Kollár defines its push-forward as the sequence `j_* B : X_r → ⋯ → X_0 = X`
whose centres `Z_i^X ⊂ X_i` are defined inductively as `Z_i^X := (j_i)_* Z_i^S`, where the
`j_i : S_i ↪ X_i` are the natural inclusions; if `B` is a smooth blow-up sequence, so is `j_* B`
[Kol07, Definition 30.3]. On manifolds the centres `Z_i^S ⊆ S_i ⊆ X_i` are regarded as closed
submanifolds of `X_i` (a closed submanifold of a closed submanifold is a closed submanifold,
`ImageVal.lean`), `X_{i+1} = Bl_{Z_i^S} X_i`, and `S_{i+1}` is the strict transform, identified with
`Bl_{Z_i^S} S_i` by `Lift.lean`.

The recursion carries, at each stage, the ambient manifold `X_i`, the strict transform `S_i ⊆ X_i`
(a closed submanifold of codimension `s`) and the identification `e_i : T_i ≃ S_i` of the given
stage with it (`PushforwardStage`). One step (`PushforwardStage.blowUpStep`): the centre
`Z_i^X := j_i(e_i(Z_i^T))` is a closed submanifold of `X_i` of codimension `c_i + s`
(`IsClosedSubmanifold.image_diffeomorph`, `imageVal_isClosedSubmanifold`);
`X_{i+1} := Bl_{Z_i^X} X_i` is the blowing-up `blowUp`; `S_{i+1}` is the strict transform of `S_i`,
a closed submanifold by `StrictSubmanifold.lean`; and `e_{i+1}` is the unique diffeomorphism over
`S_i` between the two blowings-up of `S_i` along `e_i(Z_i^T)` (`IsBlowUp.diffeomorph`) — the given
`T_{i+1} → T_i` composed with `e_i` (`IsBlowUp.diffeomorph_comp`) and the restricted blow-down
`S_{i+1} → S_i` (`isBlowUp_restrictMap`). The properties of the push-forward are then read off stage
by stage (a case split on the index, as for the pull-back of a succession). Not in the sources
beyond Kollár's definition; the proofs are routine.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set Manifold Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (s : ℕ)

/-! ### One stage of the push-forward -/

/-- The data of a stage of the push-forward [Kol07, Definition 30.3]: the ambient stage `X`, the
strict transform `S' ⊆ X` as a closed submanifold of codimension `s`, and the identification `e`
of the given stage `Tᵢ` with the bundled `S'`. -/
structure PushforwardStage (Tᵢ : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)) where
  /-- The ambient stage `X_i`. -/
  space : AnalyticManifold.{u} 𝕜 E
  /-- The strict transform `S_i ⊆ X_i`. -/
  sub : Set space
  /-- `S_i` is a closed submanifold of `X_i` of codimension `s`. -/
  isClosedSubmanifold : IsClosedSubmanifold ψ sub s
  /-- The identification `e_i : T_i ≃ S_i`. -/
  iso : Diffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) Tᵢ
    isClosedSubmanifold.toAnalyticManifold ω

namespace PushforwardStage

variable {ψ s} {Tᵢ T' : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)} (P : PushforwardStage ψ s Tᵢ)

/-- The natural inclusion `j_i ∘ e_i : T_i → X_i`. -/
def incl : C^ω⟮𝓘(𝕜, Fin (n - s) → 𝕜), Tᵢ; 𝓘(𝕜, E), P.space⟯ :=
  P.isClosedSubmanifold.inclusionMap.comp ⟨P.iso, P.iso.contMDiff⟩

theorem incl_apply (p : Tᵢ) : P.incl p = ((P.iso p : P.isClosedSubmanifold.toAnalyticManifold) :
    P.sub).1 :=
  rfl

/-- The inclusion is a closed embedding. -/
theorem isClosedEmbedding_incl : IsClosedEmbedding P.incl :=
  (P.isClosedSubmanifold.isClosed.isClosedEmbedding_subtypeVal).comp
    P.iso.toHomeomorph.isClosedEmbedding

/-- The image of the inclusion is the strict transform. -/
theorem range_incl : Set.range P.incl = P.sub := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    exact ((P.iso p : P.isClosedSubmanifold.toAnalyticManifold) : P.sub).2
  · intro hy
    refine ⟨P.iso.symm ⟨y, hy⟩, ?_⟩
    change ((P.iso (P.iso.symm ⟨y, hy⟩) : P.isClosedSubmanifold.toAnalyticManifold) : P.sub).1 = y
    exact congrArg Subtype.val
      (P.iso.apply_symm_apply (⟨y, hy⟩ : P.isClosedSubmanifold.toAnalyticManifold))

variable {Z : Set Tᵢ} {c : ℕ}

/-- The centre `Z_i^X := j_i(e_i(Z))` of the push-forward, a closed submanifold of `X_i` of
codimension `c + s`. -/
theorem isClosedSubmanifold_imageVal_image
    (hZ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c) :
    IsClosedSubmanifold ψ (P.isClosedSubmanifold.imageVal (P.iso '' Z)) (c + s) :=
  P.isClosedSubmanifold.imageVal_isClosedSubmanifold (hZ.image_diffeomorph P.iso)

theorem imageVal_image_eq (Z : Set Tᵢ) :
    P.isClosedSubmanifold.imageVal (P.iso '' Z) = P.incl '' Z :=
  Set.image_image _ _ Z

/-- The restricted blow-down `S_{i+1} → S_i` is a blowing-up of `S_i` along `e_i(Z)`. -/
theorem isBlowUp_restrictMap_imageVal
    (hZ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c) :
    IsBlowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) (P.iso '' Z) c
      ((P.isClosedSubmanifold.strictTransform (P.isClosedSubmanifold_imageVal_image hZ)
        (isBlowUp_blowUpπ ψ (P.isClosedSubmanifold_imageVal_image hZ))
        (P.isClosedSubmanifold.imageVal_subset _)).restrictMap P.isClosedSubmanifold
        (blowUpπ ψ (P.isClosedSubmanifold_imageVal_image hZ))
        (isBlowUp_blowUpπ ψ (P.isClosedSubmanifold_imageVal_image hZ)).contMDiff
        (strictTransform_subset_preimage (blowUpπ ψ _).contMDiff.continuous
          P.isClosedSubmanifold.isClosed)) := by
  have h1 := isBlowUp_restrictMap P.isClosedSubmanifold (P.isClosedSubmanifold_imageVal_image hZ)
    (isBlowUp_blowUpπ ψ (P.isClosedSubmanifold_imageVal_image hZ))
    (P.isClosedSubmanifold.imageVal_subset _)
  rwa [P.isClosedSubmanifold.preimageVal_imageVal, Nat.add_sub_cancel] at h1

/-- One step of the push-forward: from the stage data at `T_i` and a blowing-up `π : T' → T_i`
along `Z`, the stage data at `T'` — `X_{i+1} = Bl_{Z_i^X} X_i`, `S_{i+1}` the strict transform,
`e_{i+1}` the unique diffeomorphism over `S_i` (`IsBlowUp.diffeomorph`). -/
def blowUpStep (hZ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c)
    {π : AnalyticMap T' Tᵢ} (hπ : IsBlowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c π) :
    PushforwardStage ψ s T' where
  space := blowUp ψ (P.isClosedSubmanifold_imageVal_image hZ)
  sub := strictTransformSet (blowUpπ ψ (P.isClosedSubmanifold_imageVal_image hZ))
    (P.isClosedSubmanifold.imageVal (P.iso '' Z)) P.sub
  isClosedSubmanifold := P.isClosedSubmanifold.strictTransform
    (P.isClosedSubmanifold_imageVal_image hZ)
    (isBlowUp_blowUpπ ψ (P.isClosedSubmanifold_imageVal_image hZ))
    (P.isClosedSubmanifold.imageVal_subset _)
  iso := IsBlowUp.diffeomorph (hZ.image_diffeomorph P.iso) (hπ.diffeomorph_comp P.iso)
    (P.isBlowUp_restrictMap_imageVal hZ)

/-- The square of the step: the restricted blow-down after `e_{i+1}` is `e_i` after `π`. -/
theorem restrictMap_blowUpStep_iso
    (hZ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c)
    {π : AnalyticMap T' Tᵢ} (hπ : IsBlowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c π)
    (p : T') :
    (((P.blowUpStep hZ hπ).isClosedSubmanifold.restrictMap P.isClosedSubmanifold
        (blowUpπ ψ (P.isClosedSubmanifold_imageVal_image hZ))
        (isBlowUp_blowUpπ ψ (P.isClosedSubmanifold_imageVal_image hZ)).contMDiff
        (strictTransform_subset_preimage (blowUpπ ψ _).contMDiff.continuous
          P.isClosedSubmanifold.isClosed)) ((P.blowUpStep hZ hπ).iso p)) = P.iso (π p) :=
  blowDown_liftPoint (hZ.image_diffeomorph P.iso) (hπ.diffeomorph_comp P.iso)
    (P.isBlowUp_restrictMap_imageVal hZ) p

end PushforwardStage

end Manifold

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {S : Set M} {s : ℕ}
  (hS : IsClosedSubmanifold ψ S s) (T : FiniteSuccession hS.toAnalyticManifold)

/-! ### The recursion -/

/-- The centre `Z_i^T` of the given sequence as a closed submanifold for the identity chart. -/
theorem pushforwardCenterSub (i : ℕ) (hi : i < T.length) :
    IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      (T.center ⟨i, hi⟩).support (T.codim ⟨i, hi⟩) :=
  (T.isClosedSubmanifold_center ⟨i, hi⟩).congr_chart _

/-- The blow-down `T_{i+1} → T_i` as a blowing-up for the identity chart. -/
theorem pushforwardIsBlowUp (i : ℕ) (hi : i < T.length) :
    IsBlowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) (T.center ⟨i, hi⟩).support
      (T.codim ⟨i, hi⟩) (T.map ⟨i, hi⟩) :=
  (T.isBlowUp_map ⟨i, hi⟩).congr_chart _

/-- The stages of the push-forward, by recursion — `X_0 = X` with `S_0 = S` and the identity, then
one `blowUpStep` per step of the given sequence. -/
def pushforwardAux : ∀ (i : ℕ) (hi : i < T.length + 1),
    PushforwardStage ψ s (finStages hS.toAnalyticManifold T.later ⟨i, hi⟩)
  | 0, _ => ⟨M, S, hS, Diffeomorph.refl _ _ _⟩
  | i + 1, hi =>
    (pushforwardAux i (Nat.lt_of_succ_lt hi)).blowUpStep
      (T.pushforwardCenterSub hS i (Nat.lt_of_succ_lt_succ hi))
      (T.pushforwardIsBlowUp hS i (Nat.lt_of_succ_lt_succ hi))

/-- The later stages `X_1, …, X_r` of the push-forward. -/
def pushforwardLater (i : Fin T.length) : AnalyticManifold.{u} 𝕜 E :=
  (T.pushforwardAux hS (i.1 + 1) (Nat.succ_lt_succ i.2)).space

/-- The centre `Z_i^X` of the push-forward, as a closed submanifold of `X_i`. -/
theorem pushforwardCenterOfSub (i : ℕ) (hi : i < T.length) :
    IsClosedSubmanifold ψ
      ((T.pushforwardAux hS i (Nat.lt_succ_of_lt hi)).isClosedSubmanifold.imageVal
        ((T.pushforwardAux hS i (Nat.lt_succ_of_lt hi)).iso '' (T.center ⟨i, hi⟩).support))
      (T.codim ⟨i, hi⟩ + s) :=
  (T.pushforwardAux hS i (Nat.lt_succ_of_lt hi)).isClosedSubmanifold_imageVal_image
    (T.pushforwardCenterSub hS i hi)

/-- The centre of the push-forward at step `i`: the ideal sheaf of `Z_i^X`. -/
def pushforwardCenterOf (i : ℕ) (hi : i < T.length) :
    IdealSheaf (T.pushforwardAux hS i (Nat.lt_succ_of_lt hi)).space :=
  (T.pushforwardCenterOfSub hS i hi).idealSheaf

/-- The blow-down of the push-forward at step `i`: the blowing-up of `X_i` along `Z_i^X`. -/
def pushforwardMapOf (i : ℕ) (hi : i < T.length) :
    AnalyticMap (T.pushforwardAux hS (i + 1) (Nat.succ_lt_succ hi)).space
      (T.pushforwardAux hS i (Nat.lt_succ_of_lt hi)).space :=
  blowUpπ ψ (T.pushforwardCenterOfSub hS i hi)

/-- The support of the centre of the push-forward at step `i` is `Z_i^X`. -/
theorem support_pushforwardCenterOf (i : ℕ) (hi : i < T.length) :
    (T.pushforwardCenterOf hS i hi).support =
      (T.pushforwardAux hS i (Nat.lt_succ_of_lt hi)).isClosedSubmanifold.imageVal
        ((T.pushforwardAux hS i (Nat.lt_succ_of_lt hi)).iso '' (T.center ⟨i, hi⟩).support) :=
  (T.pushforwardCenterOfSub hS i hi).cosupport_idealSheaf

/-- The centres of the push-forward, typed on the stages `finStages`. -/
def pushforwardCenterAux :
    ∀ (i : ℕ) (hi : i < T.length),
      IdealSheaf (finStages M (T.pushforwardLater hS) ⟨i, Nat.lt_succ_of_lt hi⟩)
  | 0, hi => T.pushforwardCenterOf hS 0 hi
  | i + 1, hi => T.pushforwardCenterOf hS (i + 1) hi

/-- The blow-downs of the push-forward, typed on the stages `finStages`. -/
def pushforwardMapAux :
    ∀ (i : ℕ) (hi : i < T.length),
      AnalyticMap (finStages M (T.pushforwardLater hS) ⟨i + 1, Nat.succ_lt_succ hi⟩)
        (finStages M (T.pushforwardLater hS) ⟨i, Nat.lt_succ_of_lt hi⟩)
  | 0, hi => T.pushforwardMapOf hS 0 hi
  | i + 1, hi => T.pushforwardMapOf hS (i + 1) hi

/-- Each blow-down of the push-forward is a monoidal transformation with centre the ideal sheaf
of `Z_i^X` (`isMonoidalTransformation_blowUpπ`). -/
theorem pushforwardIsMonoidalAux :
    ∀ (i : ℕ) (hi : i < T.length),
      (T.pushforwardMapAux hS i hi).IsMonoidalTransformation (T.pushforwardCenterAux hS i hi)
  | 0, hi => isMonoidalTransformation_blowUpπ ψ (T.pushforwardCenterOfSub hS 0 hi)
  | i + 1, hi => isMonoidalTransformation_blowUpπ ψ (T.pushforwardCenterOfSub hS (i + 1) hi)

/-! ### The push-forward and the inclusions -/

/-- **The push-forward `j_* B` of a blow-up sequence of the bundled `S` to `M`**
[Kol07, Definition 30.3]: the blow-up sequence of `M` of the same length whose `i`-th stage is
`X_{i+1} = Bl_{Z_i^X} X_i` and whose `i`-th centre is (the ideal sheaf of) `Z_i^X = (j_i)_* Z_i^S`,
`j_i : S_i ↪ X_i` the natural inclusion of the strict transform, with which the given stage is
identified. -/
def pushforward : FiniteSuccession M where
  length := T.length
  later := T.pushforwardLater hS
  center i := T.pushforwardCenterAux hS i.1 i.2
  map i := T.pushforwardMapAux hS i.1 i.2
  isMonoidal i := T.pushforwardIsMonoidalAux hS i.1 i.2

/-- The natural inclusions `j_i : S_i ↪ X_i` of [Kol07, Definition 30.3]: the inclusions of the
stages of the given sequence into those of the push-forward. -/
def pushforwardIncl : ∀ i : Fin (T.length + 1),
    C^ω⟮𝓘(𝕜, Fin (n - s) → 𝕜), T.stage i; 𝓘(𝕜, E), (T.pushforward hS).stage i⟯
  | ⟨0, hi⟩ => (T.pushforwardAux hS 0 hi).incl
  | ⟨i + 1, hi⟩ => (T.pushforwardAux hS (i + 1) hi).incl

/-! ### The properties of the push-forward -/

theorem length_pushforward : (T.pushforward hS).length = T.length := rfl

/-- The strict transforms of `S` along the push-forward are the carried `S_i` (stages `≥ 1`; stage
`0` is `S` by definition). -/
theorem strictTransformSeqAux_pushforward_succ :
    ∀ (i : ℕ) (hi : i + 1 < T.length + 1),
      (T.pushforward hS).strictTransformSeqAux S (i + 1) hi =
        (T.pushforwardAux hS (i + 1) hi).sub
  | 0, hi => by
    change strictTransformSet (T.pushforwardMapOf hS 0 (Nat.lt_of_succ_lt_succ hi))
      (T.pushforwardCenterOf hS 0 (Nat.lt_of_succ_lt_succ hi)).support S = _
    rw [T.support_pushforwardCenterOf hS 0 (Nat.lt_of_succ_lt_succ hi)]
    rfl
  | i + 1, hi => by
    have ih := strictTransformSeqAux_pushforward_succ i (Nat.lt_of_succ_lt hi)
    change strictTransformSet (T.pushforwardMapOf hS (i + 1) (Nat.lt_of_succ_lt_succ hi))
      (T.pushforwardCenterOf hS (i + 1) (Nat.lt_of_succ_lt_succ hi)).support
      ((T.pushforward hS).strictTransformSeqAux S (i + 1) (Nat.lt_of_succ_lt hi)) = _
    rw [ih, T.support_pushforwardCenterOf hS (i + 1) (Nat.lt_of_succ_lt_succ hi)]
    rfl

/-- The centres of the push-forward lie in the strict transforms of `S`, so that the restriction
of [Kol07, Definition 30.2] applies to `j_* B`. -/
theorem centersIn_pushforward : (T.pushforward hS).CentersIn S := by
  intro i
  obtain ⟨i, hi⟩ := i
  have hi' : i < T.length := hi
  rcases i with _ | i
  · change (T.pushforwardCenterOf hS 0 hi').support ⊆ S
    rw [T.support_pushforwardCenterOf hS 0 hi']
    exact (T.pushforwardAux hS 0 _).isClosedSubmanifold.imageVal_subset _
  · change (T.pushforwardCenterOf hS (i + 1) hi').support ⊆
      (T.pushforward hS).strictTransformSeqAux S (i + 1) (Nat.lt_succ_of_lt hi')
    rw [T.support_pushforwardCenterOf hS (i + 1) hi',
      T.strictTransformSeqAux_pushforward_succ hS i (Nat.lt_succ_of_lt hi')]
    exact (T.pushforwardAux hS (i + 1) _).isClosedSubmanifold.imageVal_subset _

/-- The inclusions `S_i ↪ X_i` are closed embeddings. -/
theorem isClosedEmbedding_pushforwardIncl (i : Fin (T.length + 1)) :
    IsClosedEmbedding (T.pushforwardIncl hS i) := by
  obtain ⟨i, hi⟩ := i
  rcases i with _ | i
  · exact (T.pushforwardAux hS 0 hi).isClosedEmbedding_incl
  · exact (T.pushforwardAux hS (i + 1) hi).isClosedEmbedding_incl

/-- The image of the inclusion `S_i ↪ X_i` is the strict transform of `S` along the push-forward. -/
theorem range_pushforwardIncl (i : Fin (T.length + 1)) :
    Set.range (T.pushforwardIncl hS i) = (T.pushforward hS).strictTransformSeq S i := by
  obtain ⟨i, hi⟩ := i
  rcases i with _ | i
  · exact (T.pushforwardAux hS 0 hi).range_incl
  · change Set.range (T.pushforwardAux hS (i + 1) hi).incl =
      (T.pushforward hS).strictTransformSeqAux S (i + 1) hi
    rw [T.strictTransformSeqAux_pushforward_succ hS i hi]
    exact (T.pushforwardAux hS (i + 1) hi).range_incl

/-- The inclusion at stage `0` is the inclusion `S ↪ M`. -/
theorem pushforwardIncl_zero : T.pushforwardIncl hS 0 = hS.inclusionMap :=
  ContMDiffMap.ext fun _ => rfl

/-- The centre of the push-forward at step `i` is the image of the centre of the given sequence
under the inclusion (`Z_i^X := (j_i)_* Z_i^S`, [Kol07, Definition 30.3]). -/
theorem support_center_pushforward (i : Fin T.length) :
    ((T.pushforward hS).center i).support =
      T.pushforwardIncl hS i.castSucc '' (T.center i).support := by
  obtain ⟨i, hi⟩ := i
  rcases i with _ | i
  · change (T.pushforwardCenterOf hS 0 hi).support =
      (T.pushforwardAux hS 0 _).incl '' (T.center ⟨0, hi⟩).support
    rw [T.support_pushforwardCenterOf hS 0 hi]
    exact (T.pushforwardAux hS 0 _).imageVal_image_eq _
  · change (T.pushforwardCenterOf hS (i + 1) hi).support =
      (T.pushforwardAux hS (i + 1) _).incl '' (T.center ⟨i + 1, hi⟩).support
    rw [T.support_pushforwardCenterOf hS (i + 1) hi]
    exact (T.pushforwardAux hS (i + 1) _).imageVal_image_eq _

/-- The inclusions commute with the blow-downs (the squares of Kollár's diagram). -/
theorem pushforwardIncl_map (i : Fin T.length) (p : T.stage i.succ) :
    T.pushforwardIncl hS i.castSucc (T.map i p) =
      (T.pushforward hS).map i (T.pushforwardIncl hS i.succ p) := by
  obtain ⟨i, hi⟩ := i
  rcases i with _ | i
  · exact (congrArg Subtype.val
      ((T.pushforwardAux hS 0 (Nat.lt_succ_of_lt hi)).restrictMap_blowUpStep_iso
        (T.pushforwardCenterSub hS 0 hi) (T.pushforwardIsBlowUp hS 0 hi) p)).symm
  · exact (congrArg Subtype.val
      ((T.pushforwardAux hS (i + 1) (Nat.lt_succ_of_lt hi)).restrictMap_blowUpStep_iso
        (T.pushforwardCenterSub hS (i + 1) hi) (T.pushforwardIsBlowUp hS (i + 1) hi) p)).symm

/-- The centre `Z_i^X` is a closed submanifold of `X_i` of codimension `c_i + s`. -/
theorem isClosedSubmanifold_center_pushforward (i : Fin T.length) :
    IsClosedSubmanifold ψ ((T.pushforward hS).center i).support (T.codim i + s) := by
  obtain ⟨i, hi⟩ := i
  rcases i with _ | i
  · change IsClosedSubmanifold ψ (T.pushforwardCenterOf hS 0 hi).support (T.codim ⟨0, hi⟩ + s)
    rw [T.support_pushforwardCenterOf hS 0 hi]
    exact T.pushforwardCenterOfSub hS 0 hi
  · change IsClosedSubmanifold ψ (T.pushforwardCenterOf hS (i + 1) hi).support
      (T.codim ⟨i + 1, hi⟩ + s)
    rw [T.support_pushforwardCenterOf hS (i + 1) hi]
    exact T.pushforwardCenterOfSub hS (i + 1) hi

/-- Every step of the push-forward is a blowing-up of `X_i` along `Z_i^X`, of codimension
`c_i + s` (if `B` is a smooth blow-up sequence, so is `j_* B`, [Kol07, Definition 30.3]). -/
theorem isBlowUp_map_pushforward (i : Fin T.length) :
    IsBlowUp ψ ((T.pushforward hS).center i).support (T.codim i + s)
      ((T.pushforward hS).map i) := by
  obtain ⟨i, hi⟩ := i
  rcases i with _ | i
  · change IsBlowUp ψ (T.pushforwardCenterOf hS 0 hi).support (T.codim ⟨0, hi⟩ + s)
      (T.pushforwardMapOf hS 0 hi)
    rw [T.support_pushforwardCenterOf hS 0 hi]
    exact isBlowUp_blowUpπ ψ (T.pushforwardCenterOfSub hS 0 hi)
  · change IsBlowUp ψ (T.pushforwardCenterOf hS (i + 1) hi).support (T.codim ⟨i + 1, hi⟩ + s)
      (T.pushforwardMapOf hS (i + 1) hi)
    rw [T.support_pushforwardCenterOf hS (i + 1) hi]
    exact isBlowUp_blowUpπ ψ (T.pushforwardCenterOfSub hS (i + 1) hi)

end AnalyticManifold.FiniteSuccession

end
