/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.Pushforward
public import Hironaka.Manifold.FiniteSuccession.Order
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Resolution.Analytic.GoingUp.Naturality
import Hironaka.Resolution.Analytic.LogDerivSequence
import Hironaka.Resolution.Analytic.MaximalContact.MarkedOneLemmas
import Hironaka.Resolution.Analytic.Restrict.LemmaSixtyTwo
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Going up: the marked transform along the push-forward

**The restriction of the push-forward is the given sequence**, read on the marked transforms. For
`Π = j_* T` the push-forward [Kol07, 30.3] of a sequence `T` on the closed submanifold `S ⊆ M`
and `J` an ideal sheaf on `M`, the marked transform of `(J, m)` along `Π`, restricted to `S_i`
through the embedding `j_i : T_i ↪ X_i` (`pushforwardIncl`), is the marked transform of
`(J|_S, m)` along `T`, as soon as the marked transforms of `Π` have order `≥ m` along the centres
of the steps before the stage (the order clause (4′) of [Kol07, Definition 66] on the prefix). The
algebraic counterpart is `pullback_pushforward`.

* `PushforwardStage.birationalTransform_pullback_incl_blowUpStep`, the step: with
  `j_{i+1} = ι_{S_{i+1}} ∘ e_{i+1}` (`blowUpStep`), the one-blowing-up Lemma 62 [Kol07, Lemma 62]
  handles `ι_{S_{i+1}}` (the marked transform restricts to the strict transform `S_{i+1}`), the
  invariance `birationalTransform_pullback_of_comp_eq` handles `e_{i+1}` (the unique
  diffeomorphism over `S_i` between the given blowing-up `e_i ∘ π_i^T` and the restricted
  blow-down), and the base change `birationalTransform_image_diffeomorph` handles `e_i`.
* `birationalTransform_pushforward_step`: the step read on the sequence's own data (the chosen
  charts, the centres `Z_i^X = j_i(Z_i)` by `support_pushforwardCenterOf`).
* `markedTransformSeq_pullback_pushforwardIncl_of_forall_lt`: the identity at a stage `i` from the
  order clause (4′) of `Π` on the steps before `i`, the form used inside the induction of Kollár's
  proof of Theorem 84 (a prefix-bounded hypothesis rather than a truncated sequence, whose stage
  types would not be definitionally those of `Π`); `markedTransformSeq_pullback_pushforwardIncl`
  is its corollary for `Π` of order `≥ m`.

The proof is an induction on the stage with the one-blowing-up Lemma 62, as for the restriction of
a sequence to a submanifold in `Hironaka/Manifold/Sequence/Restrict/`.
-/

public section

noncomputable section

open TopologicalSpace AnalyticManifold.FiniteSuccession
open scoped Manifold ContDiff Topology

universe u

namespace Manifold.PushforwardStage

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {s : ℕ} {Tᵢ T' : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)}
  (P : PushforwardStage ψ s Tᵢ) {Z : Set Tᵢ} {c : ℕ}

/-- The step of the push-forward identity at one stage ([Kol07, 30.3] with [Kol07, Lemma 62]):
for the stage data `P = (X_i, S_i, e_i)` and a blowing-up `π : T' → T_i` along `Z`, the marked
transform of `(A, m)` along the blowing-up `X_{i+1} → X_i` of `Z_i^X = j_i(e_i(Z))`, pulled back
along `j_{i+1} = ι_{S_{i+1}} ∘ e_{i+1}`, is the marked transform of `(j_i^* A, m)` along `π`:
Lemma 62 for `ι_{S_{i+1}}`, the invariance under the unique diffeomorphism `e_{i+1}` over `S_i`,
the base change along `e_i`. -/
theorem birationalTransform_pullback_incl_blowUpStep
    (hZ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c)
    {π : AnalyticMap T' Tᵢ} (hπ : IsBlowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c π)
    (A : AnalyticManifold.IdealSheaf P.space) {m : ℕ}
    (hm : ∀ a ∈ P.isClosedSubmanifold.imageVal (P.iso '' Z), (m : ℕ∞) ≤
      IdealSheaf.ordAlongIdeal (P.isClosedSubmanifold_imageVal_image hZ).idealSheaf A a) :
    (MarkedIdealSheaf.birationalTransform (P.isClosedSubmanifold_imageVal_image hZ)
        (isBlowUp_blowUpπ ψ (P.isClosedSubmanifold_imageVal_image hZ)) ⟨A, m⟩).I.pullback
        ⇑(P.blowUpStep hZ hπ).incl (P.blowUpStep hZ hπ).incl.contMDiff =
      (MarkedIdealSheaf.birationalTransform hZ hπ ⟨A.pullback ⇑P.incl P.incl.contMDiff, m⟩).I := by
  -- the data of the step, in the form the push-forward and Lemma 62 use them
  have hY₁ : IsClosedSubmanifold ψ (P.isClosedSubmanifold.imageVal (P.iso '' Z)) (c + s) :=
    P.isClosedSubmanifold_imageVal_image hZ
  have h₁ : IsBlowUp ψ (P.isClosedSubmanifold.imageVal (P.iso '' Z)) (c + s) (blowUpπ ψ hY₁) :=
    isBlowUp_blowUpπ ψ hY₁
  have hYS : P.isClosedSubmanifold.imageVal (P.iso '' Z) ⊆ P.sub :=
    P.isClosedSubmanifold.imageVal_subset _
  have hS' := P.isClosedSubmanifold.strictTransform hY₁ h₁ hYS
  have hY₂ := P.isClosedSubmanifold.preimage_val_of_subset hY₁ hYS
  have h₂ := isBlowUp_restrictMap P.isClosedSubmanifold hY₁ h₁ hYS
  have hY₃ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) (P.iso '' Z) c :=
    hZ.image_diffeomorph P.iso
  have h₁' := hπ.diffeomorph_comp P.iso
  have h₂' := P.isBlowUp_restrictMap_imageVal hZ
  -- the marking on `S_i`, read on `e_i(Z)`
  have hm₂ := le_ordAlongIdeal_pullback_inclusionMap P.isClosedSubmanifold hY₁ hYS A hm
  rw [IsClosedSubmanifold.idealSheaf_congr _ hY₃ (P.isClosedSubmanifold.preimageVal_imageVal _),
    P.isClosedSubmanifold.preimageVal_imageVal] at hm₂
  -- the four steps
  have h62 := birationalTransform_pullback_restrictMap P.isClosedSubmanifold hY₁ h₁ hYS A hm
  have hc := MarkedIdealSheaf.birationalTransform_congr hY₂ hY₃
    (P.isClosedSubmanifold.preimageVal_imageVal _) h₂ h₂'
    ⟨A.pullback ⇑P.isClosedSubmanifold.inclusionMap P.isClosedSubmanifold.inclusionMap.contMDiff, m⟩
  have hβ := birationalTransform_pullback_of_comp_eq hY₃ h₁' h₂' (P.blowUpStep hZ hπ).iso
    (funext (P.restrictMap_blowUpStep_iso hZ hπ))
    ⟨A.pullback ⇑P.isClosedSubmanifold.inclusionMap P.isClosedSubmanifold.inclusionMap.contMDiff, m⟩
    hm₂
  have hα := birationalTransform_image_diffeomorph P.iso hZ hπ
    (A.pullback ⇑P.isClosedSubmanifold.inclusionMap P.isClosedSubmanifold.inclusionMap.contMDiff) m
    hm₂
  calc (MarkedIdealSheaf.birationalTransform hY₁ h₁ ⟨A, m⟩).I.pullback ⇑(P.blowUpStep hZ hπ).incl
        (P.blowUpStep hZ hπ).incl.contMDiff
      = ((MarkedIdealSheaf.birationalTransform hY₁ h₁ ⟨A, m⟩).I.pullback ⇑hS'.inclusionMap
          hS'.inclusionMap.contMDiff).pullback ⇑(P.blowUpStep hZ hπ).iso
          (P.blowUpStep hZ hπ).iso.contMDiff :=
        ((IdealSheaf.pullback_pullback (MarkedIdealSheaf.birationalTransform hY₁ h₁ ⟨A, m⟩).I
          ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff ⇑(P.blowUpStep hZ hπ).iso
          (P.blowUpStep hZ hπ).iso.contMDiff).trans
          (IdealSheaf.pullback_congr _ _ (P.blowUpStep hZ hπ).incl.contMDiff
            (funext fun _ => rfl))).symm
    _ = (MarkedIdealSheaf.birationalTransform hY₂ h₂
          ⟨A.pullback ⇑P.isClosedSubmanifold.inclusionMap
            P.isClosedSubmanifold.inclusionMap.contMDiff, m⟩).I.pullback ⇑(P.blowUpStep hZ hπ).iso
          (P.blowUpStep hZ hπ).iso.contMDiff :=
        (congrArg (fun X : AnalyticManifold.IdealSheaf hS'.toAnalyticManifold =>
          X.pullback ⇑(P.blowUpStep hZ hπ).iso (P.blowUpStep hZ hπ).iso.contMDiff) h62).symm
    _ = (MarkedIdealSheaf.birationalTransform hY₃ h₂'
          ⟨A.pullback ⇑P.isClosedSubmanifold.inclusionMap
            P.isClosedSubmanifold.inclusionMap.contMDiff, m⟩).I.pullback ⇑(P.blowUpStep hZ hπ).iso
          (P.blowUpStep hZ hπ).iso.contMDiff :=
        congrArg (fun J : MarkedIdealSheaf _ =>
          J.I.pullback ⇑(P.blowUpStep hZ hπ).iso (P.blowUpStep hZ hπ).iso.contMDiff) hc
    _ = (MarkedIdealSheaf.birationalTransform hY₃ h₁'
          ⟨A.pullback ⇑P.isClosedSubmanifold.inclusionMap
            P.isClosedSubmanifold.inclusionMap.contMDiff, m⟩).I := hβ
    _ = (MarkedIdealSheaf.birationalTransform hZ hπ
          ⟨(A.pullback ⇑P.isClosedSubmanifold.inclusionMap
            P.isClosedSubmanifold.inclusionMap.contMDiff).pullback ⇑P.iso P.iso.contMDiff, m⟩).I :=
        hα
    _ = (MarkedIdealSheaf.birationalTransform hZ hπ
          ⟨A.pullback ⇑P.incl P.incl.contMDiff, m⟩).I :=
        congrArg (fun X : AnalyticManifold.IdealSheaf Tᵢ =>
          (MarkedIdealSheaf.birationalTransform hZ hπ ⟨X, m⟩).I)
          ((IdealSheaf.pullback_pullback A ⇑P.isClosedSubmanifold.inclusionMap
            P.isClosedSubmanifold.inclusionMap.contMDiff ⇑P.iso P.iso.contMDiff).trans
            (IdealSheaf.pullback_congr _ _ P.incl.contMDiff (funext fun _ => rfl)))

end Manifold.PushforwardStage

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

section General

variable {S : Set M} {s : ℕ} (hS : IsClosedSubmanifold ψ S s)
  (T : FiniteSuccession hS.toAnalyticManifold)

/-- The step of the push-forward identity on the sequence's own data: the marked transform of
`(K, m)` along the `i`-th blow-down of the push-forward, pulled back along `j_{i+1}`, is the marked
transform of `(j_i^* K, m)` along the `i`-th blow-down of `T`, for `K` of order `≥ m` along the
centre `Z_i^X`. The centre of the push-forward is `j_i(Z_i)` (`support_pushforwardCenterOf`) and
its blow-down the blowing-up along it; a case split on the index, as in the definition of the
push-forward. -/
theorem birationalTransform_pushforward_step (i : Fin T.length)
    (K : IdealSheaf ((T.pushforward hS).stage i.castSucc)) {m : ℕ}
    (hm : ∀ a ∈ ((T.pushforward hS).center i).support,
      (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal ((T.pushforward hS).center i) K a) :
    (MarkedIdealSheaf.birationalTransform ((T.pushforward hS).isClosedSubmanifold_center i)
        ((T.pushforward hS).isBlowUp_map i) ⟨K, m⟩).I.pullback ⇑(T.pushforwardIncl hS i.succ)
        (T.pushforwardIncl hS i.succ).contMDiff =
      (MarkedIdealSheaf.birationalTransform (T.isClosedSubmanifold_center i) (T.isBlowUp_map i)
        ⟨K.pullback ⇑(T.pushforwardIncl hS i.castSucc) (T.pushforwardIncl hS i.castSucc).contMDiff,
          m⟩).I := by
  have e1 := (T.pushforward hS).birationalTransform_step_congr_chart (ψ := ψ) i K m
  have e2 := T.birationalTransform_step_congr_chart
    (ψ := ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) i
    (K.pullback ⇑(T.pushforwardIncl hS i.castSucc) (T.pushforwardIncl hS i.castSucc).contMDiff) m
  rw [e1, e2]
  obtain ⟨i, hi⟩ := i
  cases i
  · have hc := MarkedIdealSheaf.birationalTransform_congr
      (((T.pushforward hS).isClosedSubmanifold_center (⟨0, hi⟩ : Fin T.length)).congr_chart ψ)
      (T.pushforwardCenterOfSub hS 0 hi) (T.support_pushforwardCenterOf hS 0 hi)
      (((T.pushforward hS).isBlowUp_map (⟨0, hi⟩ : Fin T.length)).congr_chart ψ)
      (isBlowUp_blowUpπ ψ (T.pushforwardCenterOfSub hS 0 hi)) ⟨K, m⟩
    rw [hc]
    exact (T.pushforwardAux hS 0 _).birationalTransform_pullback_incl_blowUpStep
      (T.pushforwardCenterSub hS 0 hi) (T.pushforwardIsBlowUp hS 0 hi) K fun a ha =>
        hm a ((congrArg (fun s => a ∈ s) (T.support_pushforwardCenterOf hS 0 hi)).mpr ha)
  · have hc := MarkedIdealSheaf.birationalTransform_congr
      (((T.pushforward hS).isClosedSubmanifold_center (⟨_ + 1, hi⟩ : Fin T.length)).congr_chart ψ)
      (T.pushforwardCenterOfSub hS (_ + 1) hi) (T.support_pushforwardCenterOf hS (_ + 1) hi)
      (((T.pushforward hS).isBlowUp_map (⟨_ + 1, hi⟩ : Fin T.length)).congr_chart ψ)
      (isBlowUp_blowUpπ ψ (T.pushforwardCenterOfSub hS (_ + 1) hi)) ⟨K, m⟩
    rw [hc]
    exact (T.pushforwardAux hS (_ + 1) _).birationalTransform_pullback_incl_blowUpStep
      (T.pushforwardCenterSub hS (_ + 1) hi) (T.pushforwardIsBlowUp hS (_ + 1) hi) K fun a ha =>
        hm a ((congrArg (fun s => a ∈ s) (T.support_pushforwardCenterOf hS (_ + 1) hi)).mpr ha)

/-- The push-forward identity in its working form: for a stage `i` such that the marked transforms
of `(J, m)` along the push-forward have order `≥ m` along the centres of the steps before `i` (the
order clause (4′) on the prefix), the marked transform of `(J, m)` along the push-forward at stage
`i`, restricted to `S_i` through `j_i`, is the marked transform of `(J|_S, m)` along `T`.
Induction on the stage with `birationalTransform_pushforward_step`. -/
theorem markedTransformSeq_pullback_pushforwardIncl_of_forall_lt (J : IdealSheaf M) {m k : ℕ}
    (h4 : ∀ i : Fin T.length, i.1 < k → ∀ a ∈ ((T.pushforward hS).center i).support,
      (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal ((T.pushforward hS).center i)
        ((T.pushforward hS).markedTransformSeq J m i.castSucc) a)
    (i : Fin (T.length + 1)) (hi : i.1 ≤ k) :
    ((T.pushforward hS).markedTransformSeq J m i).pullback ⇑(T.pushforwardIncl hS i)
        (T.pushforwardIncl hS i).contMDiff =
      T.markedTransformSeq (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) m i := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have hi' : i.1 < k := by rw [Fin.val_succ] at hi; omega
    have step := T.birationalTransform_pushforward_step hS i
      ((T.pushforward hS).markedTransformSeq J m i.castSucc) (h4 i hi')
    have e := congrArg (fun X : IdealSheaf (T.stage i.castSucc) =>
      (MarkedIdealSheaf.birationalTransform (T.isClosedSubmanifold_center i) (T.isBlowUp_map i)
        ⟨X, m⟩).I) (ih (by rw [Fin.val_castSucc]; omega))
    exact step.trans e

end General

section Hypersurface

variable [FiniteDimensional 𝕜 E] {S : Set M} (hS : IsClosedSubmanifold ψ S 1)
  (T : FiniteSuccession hS.toAnalyticManifold) {I E₀ : IdealSheaf M} {m : ℕ}

omit [FiniteDimensional 𝕜 E] in
/-- **The restriction of the push-forward is the given sequence**, read on the marked transforms
([Kol07, 30.2–30.3]; the algebraic counterpart is `pullback_pushforward`): for `Π = j_* T` of
order `≥ m` for `(J, m)`, the marked transform of `(J, m)` along `Π` restricted to `S_i` through
the embedding `j_i : T_i ↪ X_i` (`pushforwardIncl`) is the marked transform of `(J|_S, m)` along
`T`. Induction on the stage with the one-blowing-up Lemma 62 [Kol07, Lemma 62], the stage
`S_i ⊆ X_i` being identified with `T_i` by the unique diffeomorphism between two blowings-up of
one centre [BM88, Definition 4.1], along which the colon stalks correspond. The centres
correspond by `support_center_pushforward`. The order clause (4′) of `Π` is all that the induction
uses (`markedTransformSeq_pullback_pushforwardIncl_of_forall_lt`). -/
theorem markedTransformSeq_pullback_pushforwardIncl (J : IdealSheaf M)
    (hge : (T.pushforward hS).IsOfOrderGe J m E₀) (i : Fin (T.length + 1)) :
    ((T.pushforward hS).markedTransformSeq J m i).pullback ⇑(T.pushforwardIncl hS i)
        (T.pushforwardIncl hS i).contMDiff =
      T.markedTransformSeq (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) m i :=
  T.markedTransformSeq_pullback_pushforwardIncl_of_forall_lt hS J
    (fun i' _ _ ha => hge.le_ordAlong i' ha) i (Nat.lt_succ_iff.mp i.2)

end Hypersurface

end AnalyticManifold.FiniteSuccession

end
