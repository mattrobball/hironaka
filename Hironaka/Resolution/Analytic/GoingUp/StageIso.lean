/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.Pushforward
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.Restrict.GermRestrict
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Bundled
import Hironaka.Resolution.Analytic.GoingUp.Naturality
import Hironaka.Resolution.Analytic.Restrict.GoingDown
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The stage identifications `T_i ≃ S_i` between a sequence and the restriction of its push-forward

For a smooth blow-up sequence `T` of a closed submanifold `S ⊆ X`, the push-forward `Π = j_* T`
[Kol07, 30.3] carries at every stage the strict transform `S_i ⊆ X_i` and an identification
`e_i : T_i ≃ S_i`, and the restriction `Π|_S` [Kol07, 30.2] is the sequence whose stages are
these `S_i`. This module makes `e_i` a diffeomorphism onto the stages of `Π|_S`
(`pushforwardStageIso`: the identification `iso` of the push-forward's stage data, carried across
the identity of the underlying sets, `strictTransformSeqAux_pushforward_succ`) and records the two
squares it satisfies (the inclusions `j_i`, the blow-downs) and the two identities that compare
`T` with `Π|_S`: the centre `Z_i^X` pulls back along `j_i` to `Z_i`
(`center_pullback_pushforwardIncl`) and along `e_i` from the centre of `Π|_S`
(`center_pushforwardStageIso`), and the boundary of `Π|_S` started with any ideal sheaf `E₀`
pulls back along `e_i` to the boundary of `T` started with `E₀` (`boundarySeq_pushforwardStageIso`;
the boundary is Hironaka's reduced total transform [Hir64, Main Theorem II′(N), p. 156]), by
induction with the naturality of the reduced transform (`reducedTransform_pullback_of_comp_eq`).

* `IsClosedSubmanifold.diffeomorphOfEq`: two closed submanifolds with the same underlying set, as
  bundled manifolds, are identified by the identity.
* `pushforwardStageIso`, `restrictIncl_pushforwardStageIso`, `map_pushforwardStageIso`.
* `center_pullback_pushforwardIncl`, `center_pushforwardStageIso`,
  `boundarySeq_pushforwardStageIso`.

Kollár writes that "for all practical purposes, `Z_i^X = Z_i^S`" [Kol07, 30.3]; these
identifications make the phrase precise, and they carry the normal-crossings clause of `T` to the
push-forward in `GoingUp/Theorem84.lean`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Topology
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- Two closed submanifolds with the same underlying set, as bundled analytic manifolds: the
identity (`IsClosedSubmanifold` is a proposition, so the two bundles coincide). -/
def IsClosedSubmanifold.diffeomorphOfEq {Y Y' : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ Y c)
    (hY' : IsClosedSubmanifold ψ Y' c) (h : Y = Y') :
    Diffeomorph 𝓘(𝕜, Fin (n - c) → 𝕜) 𝓘(𝕜, Fin (n - c) → 𝕜) hY.toAnalyticManifold
      hY'.toAnalyticManifold ω := by
  subst h
  exact Diffeomorph.refl _ _ _

theorem IsClosedSubmanifold.diffeomorphOfEq_apply_val {Y Y' : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ Y c) (hY' : IsClosedSubmanifold ψ Y' c) (h : Y = Y')
    (p : hY.toAnalyticManifold) :
    ((hY.diffeomorphOfEq hY' h p : hY'.toAnalyticManifold) : Y').1 = (p : Y).1 := by
  subst h
  rfl

end Manifold

namespace AnalyticManifold.FiniteSuccession

open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {S : Set M} {s : ℕ}
  (hS : IsClosedSubmanifold ψ S s) (T : FiniteSuccession hS.toAnalyticManifold)

/-- The identification `e_i : T_i ≃ S_i` of the stages of `T` with the stages of the restriction
`Π|_S` of its push-forward ([Kol07, 30.2–30.3]): the identification `iso` of the push-forward's
stage data, carried across the identity of the underlying sets (`S_i` is the strict transform of
`S` along `j_* T`). -/
def pushforwardStageIso : ∀ i : Fin (T.length + 1),
    Diffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) (T.stage i)
      (((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).stage i) ω
  | ⟨0, hi⟩ => (T.pushforwardAux hS 0 hi).iso.trans
      ((T.pushforwardAux hS 0 hi).isClosedSubmanifold.diffeomorphOfEq
        ((T.pushforward hS).isClosedSubmanifold_strictTransformSeqAux _ hS
            (T.centersIn_pushforward hS) 0 hi) rfl)
  | ⟨i + 1, hi⟩ => (T.pushforwardAux hS (i + 1) hi).iso.trans
      ((T.pushforwardAux hS (i + 1) hi).isClosedSubmanifold.diffeomorphOfEq
        ((T.pushforward hS).isClosedSubmanifold_strictTransformSeqAux _ hS
            (T.centersIn_pushforward hS) (i + 1) hi)
        (T.strictTransformSeqAux_pushforward_succ hS i hi).symm)

/-- The inclusion `S_i ↪ X_i` after `e_i` is the natural inclusion `j_i : T_i → X_i`
(`pushforwardIncl`). -/
theorem restrictIncl_pushforwardStageIso (i : Fin (T.length + 1)) (p : T.stage i) :
    (T.pushforward hS).restrictIncl hS (T.centersIn_pushforward hS) i
        (T.pushforwardStageIso hS i p) = T.pushforwardIncl hS i p := by
  obtain ⟨i, hi⟩ := i
  cases i with
  | zero =>
    exact IsClosedSubmanifold.diffeomorphOfEq_apply_val _ _ rfl ((T.pushforwardAux hS 0 hi).iso p)
  | succ k =>
    exact IsClosedSubmanifold.diffeomorphOfEq_apply_val _ _
      (T.strictTransformSeqAux_pushforward_succ hS k hi).symm
      ((T.pushforwardAux hS (k + 1) hi).iso p)

/-- The square: the blow-down of `Π|_S` after `e_{i+1}` is `e_i` after the blow-down of `T` (the
squares of the restriction and of the push-forward, through the injective inclusions). -/
theorem map_pushforwardStageIso (i : Fin T.length) (p : T.stage i.succ) :
    ((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).map i
        (T.pushforwardStageIso hS i.succ p) =
      T.pushforwardStageIso hS i.castSucc (T.map i p) := by
  exact ((T.pushforward hS).isClosedEmbedding_restrictIncl hS (T.centersIn_pushforward hS)
    i.castSucc).injective
    (((T.pushforward hS).restrictIncl_map hS (T.centersIn_pushforward hS) i
      (T.pushforwardStageIso hS i.succ p)).trans
      (((congrArg ((T.pushforward hS).map i) (T.restrictIncl_pushforwardStageIso hS i.succ p)).trans
        (T.pushforwardIncl_map hS i p).symm).trans
        (T.restrictIncl_pushforwardStageIso hS i.castSucc (T.map i p)).symm))

/-- The centre `Z_i^X` of the push-forward pulls back along `j_i : T_i → X_i` to the centre `Z_i`
of `T`, at the recursion level: the ideal sheaf of `j_i(Z_i)` restricted to `S_i` is the ideal sheaf
of `e_i(Z_i)` (`idealSheaf_preimageVal_eq_pullback`), which pulls back along `e_i` to the ideal
sheaf of `Z_i` (`idealSheaf_image_diffeomorph_pullback`). -/
theorem center_pullback_pushforwardIncl_aux (k : ℕ) (hk : k < T.length) :
    (T.pushforwardCenterOf hS k hk).pullback ⇑(T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).incl
      (T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).incl.contMDiff = T.center ⟨k, hk⟩ := by
  have hZ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      (T.center ⟨k, hk⟩).support (T.codim ⟨k, hk⟩) := T.pushforwardCenterSub hS k hk
  calc (T.pushforwardCenterOf hS k hk).pullback ⇑(T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).incl
        (T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).incl.contMDiff
      = ((T.pushforwardCenterOfSub hS k hk).idealSheaf.pullback
          ⇑(T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).isClosedSubmanifold.inclusionMap
          (T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).isClosedSubmanifold.inclusionMap.contMDiff
          ).pullback ⇑(T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).iso
          (T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).iso.contMDiff := by
        rw [IdealSheaf.pullback_pullback]
        exact IdealSheaf.pullback_congr _ _ _ (funext fun _ => rfl)
    _ = (((T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).isClosedSubmanifold.preimage_val_of_subset
          (T.pushforwardCenterOfSub hS k hk)
          ((T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).isClosedSubmanifold.imageVal_subset _)
          ).idealSheaf).pullback ⇑(T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).iso
          (T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).iso.contMDiff :=
        congrArg (fun J : IdealSheaf
            (T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).isClosedSubmanifold.toAnalyticManifold =>
          J.pullback ⇑(T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).iso
            (T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).iso.contMDiff)
          (idealSheaf_preimageVal_eq_pullback
            (T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).isClosedSubmanifold
            (T.pushforwardCenterOfSub hS k hk)
            ((T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).isClosedSubmanifold.imageVal_subset
              _)).symm
    _ = ((hZ.image_diffeomorph
          (T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).iso).idealSheaf).pullback
          ⇑(T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).iso
          (T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).iso.contMDiff := by
        rw [IsClosedSubmanifold.idealSheaf_congr _
          (hZ.image_diffeomorph (T.pushforwardAux hS k (Nat.lt_succ_of_lt hk)).iso)
          ((T.pushforwardAux hS k
            (Nat.lt_succ_of_lt hk)).isClosedSubmanifold.preimageVal_imageVal _)]
    _ = hZ.idealSheaf := idealSheaf_image_diffeomorph_pullback _ hZ
    _ = T.center ⟨k, hk⟩ :=
        (IsClosedSubmanifold.idealSheaf_congr hZ (T.isClosedSubmanifold_center ⟨k, hk⟩) rfl).trans
          (T.idealSheaf_center ⟨k, hk⟩)

/-- The centre of the push-forward pulls back along `j_i` to the centre of `T` (Kollár's centres
`Z_i^X = (j_i)_* Z_i`, [Kol07, 30.3]). -/
theorem center_pullback_pushforwardIncl (i : Fin T.length) :
    ((T.pushforward hS).center i).pullback ⇑(T.pushforwardIncl hS i.castSucc)
      (T.pushforwardIncl hS i.castSucc).contMDiff = T.center i := by
  obtain ⟨k, hk⟩ := i
  cases k with
  | zero => exact T.center_pullback_pushforwardIncl_aux hS 0 hk
  | succ k => exact T.center_pullback_pushforwardIncl_aux hS (k + 1) hk

/-- The centre of `Π|_S` pulls back along `e_i` to the centre of `T` (`center_restrictSubmanifold`
composed with `restrictIncl_pushforwardStageIso`). -/
theorem center_pushforwardStageIso (i : Fin T.length) :
    (((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).center i).pullback
        ⇑(T.pushforwardStageIso hS i.castSucc) (T.pushforwardStageIso hS i.castSucc).contMDiff =
      T.center i := by
  exact (congrArg (fun J => J.pullback ⇑(T.pushforwardStageIso hS i.castSucc)
      (T.pushforwardStageIso hS i.castSucc).contMDiff)
      ((T.pushforward hS).center_restrictSubmanifold hS (T.centersIn_pushforward hS) i)).trans
    ((IdealSheaf.pullback_pullback _ _ _ _ _).trans
      ((IdealSheaf.pullback_congr _ _ (T.pushforwardIncl hS i.castSucc).contMDiff
        (funext (T.restrictIncl_pushforwardStageIso hS i.castSucc))).trans
        (T.center_pullback_pushforwardIncl hS i)))

/-- **The boundary of `Π|_S` started with `E₀` pulls back along `e_i` to the boundary of `T`
started with `E₀`** ([Kol07, 30.2] with [Kol07, 30.3]): the two sequences on `S` differ by the
stage identifications only (`e_0` is the identity of `S`), and the reduced transform is natural
along them (`reducedTransform_pullback_of_comp_eq` on the squares `map_pushforwardStageIso`). -/
theorem boundarySeq_pushforwardStageIso {E₀ : IdealSheaf hS.toAnalyticManifold}
    (i : Fin (T.length + 1)) :
    (((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).boundarySeq E₀
        i).pullback ⇑(T.pushforwardStageIso hS i) (T.pushforwardStageIso hS i).contMDiff =
      T.boundarySeq E₀ i := by
  induction i using Fin.induction with
  | zero =>
    exact (IdealSheaf.pullback_congr E₀ _ contMDiff_id (funext fun p => rfl)).trans
      (IdealSheaf.pullback_id_eq_self E₀)
  | succ i ih =>
    have hsq : ⇑(((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).map i) ∘
        ⇑(T.pushforwardStageIso hS i.succ) =
        ⇑(T.pushforwardStageIso hS i.castSucc) ∘ ⇑(T.map i) :=
      funext (T.map_pushforwardStageIso hS i)
    exact (reducedTransform_pullback_of_comp_eq (T.pushforwardStageIso hS i.castSucc) (T.map i)
      (((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).map i)
      (T.pushforwardStageIso hS i.succ) hsq
      (((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).center i)
      (((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).boundarySeq E₀
        i.castSucc)).trans
      (congrArg₂ (fun D E => IdealSheaf.reducedTransform (T.map i) E D)
        (T.center_pushforwardStageIso hS i) ih)

end AnalyticManifold.FiniteSuccession

end
