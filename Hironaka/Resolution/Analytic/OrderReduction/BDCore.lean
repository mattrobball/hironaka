/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.LocalIsoEquiv
public import Hironaka.Resolution.Analytic.OrderReduction.BD
import Hironaka.Manifold.BlowUp.Transform.Bundled
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.Snc.Dictionary
import Hironaka.Resolution.Analytic.Functor.PullbackSequence
import Hironaka.Resolution.Analytic.Functor.PullbackTransport
import Hironaka.Resolution.Analytic.GoingUp.MaxOrder
import Hironaka.Resolution.Analytic.OrderReduction.BDCor85
import Hironaka.Resolution.Analytic.OrderReduction.BDLemmas
import Hironaka.Resolution.Analytic.OrderReduction.BDLift
import Hironaka.Resolution.Analytic.OrderReduction.TunedLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Lemma 102: the order clause

[Kol07, Lemma 102] asserts that `BD_{n,m,j}` is a smooth blow-up sequence functor of order `m`.
For the construction `BDan` of `BD.lean` this is proved here: the first blow-up, of `Z_{-1}`, has
order `s = tuningParam m` for the tuned ideal (`FirstStep.lean`); the tail is the push-forward of
the value of the input functor on the
restricted triple, of order `≥ m` for `(I_0, E)` by [Kol07, Corollary 85] with the transform of
`E^j` in the boundary (`BDCor85.lean`); and the first blow-up, when it is empty (no component of
`E^j` lies in `cosupp(I, m)`), is deleted ([Kol07, 32]).

The tail of the core is the push-forward of a list of centres, while Corollary 85 is stated for the
push-forward of a succession of blow-ups. Their identification for lists without empty centres,
`BlowUpSequence.toSuccession_pushforward`, enters here as the hypothesis `PushforwardBridge ψ₀`, so
that the clause is proved for any model; `BDBridge.lean` discharges it and states the clause
unconditionally (`BDan_isOfOrder`).

* `PushforwardBridge ψ₀` — the identification as a hypothesis.
* `BlowUpSequence.noEmptyCenters_pushforward_of_bridge`,
  `BlowUpSequence.isOfOrderGe_map_emptyBlowUp` — the push-forward of a list without empty centres
  has none ([Kol07, 32]); a sequence of order `≥ m` on the blow-up of an empty centre, transported
  along the isomorphism with the base, is of order `≥ m` there.
* `BDan.weakTransform_eq_weakTransformI`, `BDan.reducedTransform_eq_idealSheaf_append` — the weak
  transform and the boundary after the first blow-up, in the form used by the successions, are
  `I_0` and the reduced ideal sheaf of `(E - E^j)|_{X_0} + S_0`.
* `BDan.weakTransformI_eq_comap_of_eq_empty`, `BDan.idealSheaf_append_eq_comap_of_eq_empty` — when
  `Z_{-1} = ∅` the first blow-up is an isomorphism and both are pull-backs.
* `BDan.pushforward_isOfOrderGe_of_bridge`, `BDan.cons_isOfOrder_of_bridge`,
  `BDan.coreOfListOf_isOfOrderGe_of_bridge` — the order clause for the core over any sequence `L`
  on `S_0` without empty centres and of order `≥ s` for the restricted triple: its tail, the core
  before the deletion of the empty first blow-up, and the core.
* `BDan_isOfOrder_of_bridge` — **the order clause of Lemma 102**, given the identification: the
  previous item at the value of the input functor.
-/

@[expose] public section

noncomputable section

open Set Topology AnalyticManifold IsLocalRing
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

/-- The identification of the push-forward of a list of centres on a closed hypersurface `S` with
the push-forward of the corresponding succession of blow-ups ([Kol07, 30.3]), for lists without
empty centres, as a hypothesis on the model; it is `BlowUpSequence.toSuccession_pushforward`
(`BDBridge.lean`). -/
def PushforwardBridge (ψ : E ≃L[𝕜] (Fin n → 𝕜)) : Prop :=
  ∀ {M : AnalyticManifold.{u} 𝕜 E} {S : Set M} (hS : IsClosedSubmanifold ψ S 1)
    (L : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) hS.toAnalyticManifold),
    L.NoEmptyCenters → (L.pushforward hS).toSuccession = L.toSuccession.pushforward hS

end Hironaka.Manifold

namespace AnalyticManifold.BlowUpSequence

open _root_.Manifold
open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

variable {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- [Kol07, 32] for the push-forward: the centres of the push-forward are the images of the
centres, so a list without empty centres pushes forward to one without empty centres (through the
identification). -/
theorem noEmptyCenters_pushforward_of_bridge (hbr : PushforwardBridge.{u} ψ₀)
    {M : AnalyticManifold.{u} 𝕜 E} {S : Set M} (hS : IsClosedSubmanifold ψ₀ S 1)
    (L : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) hS.toAnalyticManifold)
    (hL : L.NoEmptyCenters) : (L.pushforward hS).NoEmptyCenters := by
  change (L.pushforward hS).toSuccession.NoEmptyCenters
  rw [hbr hS L hL]
  intro i hi
  have hsupp := L.toSuccession.support_center_pushforward hS i
  rw [hi] at hsupp
  change (⊤ : IdealSheaf _).support = _ at hsupp
  rw [IdealSheaf.support_top] at hsupp
  have hsupp' : (L.toSuccession.center ⟨i.1, i.2⟩).support = ∅ :=
    Set.image_eq_empty.mp hsupp.symm
  refine hL ⟨i.1, i.2⟩ ?_
  change L.toSuccession.center ⟨i.1, i.2⟩ = ⊤
  refine IdealSheaf.ext fun x => ?_
  rw [IdealSheaf.stalkIdeal_top]
  by_contra hx
  exact Set.eq_empty_iff_forall_notMem.mp hsupp' x hx

/-- Transport of [Kol07, Definition 66] along the isomorphism of an empty blow-up ([Kol07, 32]): a
list on the blow-up of the empty centre, of order `≥ m` for the pull-backs of `(I, E₀)`,
transported to `M` along the isomorphism is of order `≥ m` for `(I, E₀)`. -/
theorem isOfOrderGe_map_emptyBlowUp {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (hY₀ : Y = ∅) (P : BlowUpSequence ψ₀ (blowUp ψ₀ hY))
    {I E₀ : IdealSheaf M} {m : ℕ}
    (hP : P.toSuccession.IsOfOrderGe (I.pullback _ (blowUpπ ψ₀ hY).contMDiff) m
      (E₀.pullback _ (blowUpπ ψ₀ hY).contMDiff)) :
    (P.map (emptyBlowUpDiffeomorph hY hY₀)).toSuccession.IsOfOrderGe I m E₀ := by
  have := finiteDimensional_of_chartIso ψ₀
  set g := emptyBlowUpDiffeomorph hY hY₀ with hg
  rw [map_eq_pullback_symm]
  have hid : (Diffeomorph.toAnalyticMap g.symm).comp (Diffeomorph.toAnalyticMap g) =
      ContMDiffMap.id :=
    ContMDiffMap.ext fun x => g.symm_apply_apply x
  have hsurj : Function.Surjective (Diffeomorph.toAnalyticMap g) := g.toEquiv.surjective
  refine isOfOrderGe_of_pullback _ (Diffeomorph.toAnalyticMap g) g.isLocalDiffeomorph
    hsurj I E₀ m ?_
  rw [pullback_comp, pullback_congr _ hid _ (isLocalDiffeomorph_id _), pullback_id]
  have hgπ : ⇑(Diffeomorph.toAnalyticMap g) = ⇑(blowUpπ ψ₀ hY) :=
    funext fun p => emptyBlowUpDiffeomorph_apply hY hY₀ p
  have h1 : I.pullback _ (Diffeomorph.toAnalyticMap g).contMDiff =
      I.pullback _ (blowUpπ ψ₀ hY).contMDiff :=
    IdealSheaf.pullback_congr I _ _ hgπ
  have h2 : E₀.pullback _ (Diffeomorph.toAnalyticMap g).contMDiff =
      E₀.pullback _ (blowUpπ ψ₀ hY).contMDiff :=
    IdealSheaf.pullback_congr E₀ _ _ hgπ
  rw [h1, h2]
  exact hP

end AnalyticManifold.BlowUpSequence

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

/-- The support of `E` is the support of `E - E^j` together with `E^j`. -/
theorem _root_.Manifold.HypersurfaceFamily.support_emptyMember_union {M : AnalyticManifold.{u} 𝕜 E}
    (F : HypersurfaceFamily M) (j : F.ι) : (F.emptyMember j).support ∪ F.hyp j = F.support := by
  ext x
  simp only [HypersurfaceFamily.support, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro (⟨k, hk⟩ | hj)
    · exact ⟨k, HypersurfaceFamily.emptyMember_hyp_subset F j k hk⟩
    · exact ⟨j, hj⟩
  · rintro ⟨k, hk⟩
    by_cases hkj : k = j
    · subst hkj
      exact Or.inr hk
    · left
      refine ⟨k, ?_⟩
      rw [HypersurfaceFamily.emptyMember_hyp_of_ne F hkj]
      exact hk

namespace BDan

open _root_.Manifold

variable [FiniteDimensional 𝕜 E] {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  (T : AnalyticTriple ψ₀ M) (s : ℕ) (j : T.F.ι)

/-- The weak transform under the first blow-up, in the form used by the successions, is `I_0`. -/
theorem weakTransform_eq_weakTransformI :
    IdealSheaf.weakTransform (piMinusOne T s j) T.I (BD.isClosedSubmanifold_Zminus1 T s
        j).idealSheaf = weakTransformI T s j :=
  weakTransform_eq _ (BD.isClosedSubmanifold_Zminus1 T s j)
    (BD.isClosedSubmanifold_Zminus1 T s j).isIdealSheafOf_idealSheaf (isBlowUp_blowUpπ ψ₀ _) T.I

/-- The boundary after the first blow-up is the reduced ideal sheaf of `(E - E^j)|_{X_0} + S_0`: the
total transform of `E` and the family `(E - E^j)|_{X_0} + S_0` have the same support, since
`Z_{-1} ⊆ E^j`. -/
theorem reducedTransform_eq_idealSheaf_append :
    IdealSheaf.reducedTransform (piMinusOne T s
        j) (T.F.idealSheaf (𝕜 := 𝕜) (E := E)) (BD.isClosedSubmanifold_Zminus1 T s j).idealSheaf =
      ((boundaryMinus T s j).append (transformS T s j)).idealSheaf := by
  refine (reducedTransform_eq_idealSheaf_totalTransform (BD.isClosedSubmanifold_Zminus1 T s j)
    (isBlowUp_blowUpπ ψ₀ _) T.isSnc (BD.hasSncWith_Zminus1 T s j)).trans ?_
  apply HypersurfaceFamily.idealSheaf_eq_of_support_eq
  rw [HypersurfaceFamily.support_totalTransform _ _ _ (piMinusOne T s j).contMDiff.continuous
    (fun k => (T.isSnc.1 k).isClosed), HypersurfaceFamily.support_append, boundaryMinus,
    boundaryMinusOf, HypersurfaceFamily.support_comap,
    ← HypersurfaceFamily.support_emptyMember_union T.F j,
    Set.preimage_union, Set.union_assoc,
    Set.union_eq_left.mpr (Set.preimage_mono (BD.Zminus1_subset T s j))]
  rfl

/-- When `Z_{-1} = ∅` the weak transform `I_0` is the pull-back of `𝓘` along the isomorphism
`π_{-1}`. -/
theorem weakTransformI_eq_comap_of_eq_empty (hZ : BD.Zminus1 T.I s (T.F.hyp j) = ∅) :
    weakTransformI T s j = T.I.pullback _ (piMinusOne T s j).contMDiff := by
  refine IdealSheaf.ext fun x' => ?_
  rw [stalkIdeal_weakTransformI_of_notMem T s j
      (Set.eq_empty_iff_forall_notMem.mp hZ (piMinusOne T s j x')),
    stalkIdeal_comap_eq_map_germAlgEquiv (piMinusOne T s j) (isLocalDiffeomorph_piMinusOne T s j)
      T.I x']

/-- When `Z_{-1} = ∅` the first blow-up is an isomorphism and the boundary after it is the
pull-back of the boundary. -/
theorem idealSheaf_append_eq_comap_of_eq_empty (hZ : BD.Zminus1 T.I s (T.F.hyp j) = ∅) :
    ((boundaryMinus T s j).append (transformS T s j)).idealSheaf =
      (T.F.idealSheaf (𝕜 := 𝕜) (E := E)).pullback _ (piMinusOne T s j).contMDiff := by
  have hsurj : Function.Surjective (piMinusOne T s j) := fun y =>
    ⟨(BlowUpSequence.emptyBlowUpDiffeomorph (BD.isClosedSubmanifold_Zminus1 T s j) hZ).symm y, by
      rw [← BlowUpSequence.emptyBlowUpDiffeomorph_apply (BD.isClosedSubmanifold_Zminus1 T s j) hZ]
      exact (BlowUpSequence.emptyBlowUpDiffeomorph (BD.isClosedSubmanifold_Zminus1 T s j)
        hZ).apply_symm_apply y⟩
  rw [← HypersurfaceFamily.idealSheaf_comap_of_surjective (piMinusOne T s j)
    (isLocalDiffeomorph_piMinusOne T s j) hsurj T.F]
  apply HypersurfaceFamily.idealSheaf_eq_of_support_eq
  rw [HypersurfaceFamily.support_append, boundaryMinus, boundaryMinusOf,
    HypersurfaceFamily.support_comap, HypersurfaceFamily.support_comap,
    ← HypersurfaceFamily.support_emptyMember_union T.F j,
    Set.preimage_union]
  rfl

variable (hT : BDClass s T)
  (L : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
    (isClosedSubmanifold_transformS T s j).toAnalyticManifold)

/-- The pushed-forward tail of the core over a sequence `L` of order `≥ s` for the restricted
triple, without empty centres, is of order `≥ s` for `(I_0, E - E^j + S_0)`: the going-up property
of D-balanced ideals with `S_0` added to the boundary ([Kol07, Theorem 84], [Kol07, Corollary 85];
`pushforward_isOfOrderGe_append`), given the identification of the two push-forwards. -/
theorem pushforward_isOfOrderGe_of_bridge (hbr : PushforwardBridge.{u} ψ₀)
    (hLne : L.NoEmptyCenters)
    (hL : L.toSuccession.IsOfOrderGe (restrictedTriple T s j hT).I s
      (restrictedTriple T s j hT).F.idealSheaf) :
    (BlowUpSequence.pushforward (isClosedSubmanifold_transformS T s j) L).toSuccession.IsOfOrderGe
      (weakTransformI T s j) s ((boundaryMinus T s j).append (transformS T s j)).idealSheaf := by
  rw [hbr (isClosedSubmanifold_transformS T s j) _ hLne]
  exact FiniteSuccession.pushforward_isOfOrderGe_append (isClosedSubmanifold_transformS T s j) _
    (isDBalanced_weakTransformI T s j hT) (ord_weakTransformI_le T s j hT)
    (isSnc_boundaryMinus T s j) (hasSncWithProper_boundaryMinus T s j) hL

/-- **The core before the deletion of the empty first blow-up is of order `s`**: the first step by
`BD.isOfOrder_firstStep` and the pushed-forward tail by `pushforward_isOfOrderGe_of_bridge`. -/
theorem cons_isOfOrder_of_bridge (hbr : PushforwardBridge.{u} ψ₀) (hLne : L.NoEmptyCenters)
    (hL : L.toSuccession.IsOfOrderGe (restrictedTriple T s j hT).I s
      (restrictedTriple T s j hT).F.idealSheaf) :
    (BlowUpSequence.cons (BD.isClosedSubmanifold_Zminus1 T s j)
      (BlowUpSequence.pushforward (isClosedSubmanifold_transformS T s j) L)).toSuccession.IsOfOrder
      T.I T.F.idealSheaf s := by
  have hfirst := BD.isOfOrder_firstStep T s j hT.1.2.1 (BD.isClosedSubmanifold_Zminus1 T s j)
  rw [BlowUpSequence.toSuccession_cons, FiniteSuccession.isOfOrder_cons_iff] at hfirst
  rw [BlowUpSequence.toSuccession_cons, FiniteSuccession.isOfOrder_cons_iff]
  refine ⟨hfirst.1, ?_⟩
  convert FiniteSuccession.isOfOrder_of_isOfOrderGe_of_ord_le _
    (pushforward_isOfOrderGe_of_bridge T s j hT L hbr hLne hL) (ord_weakTransformI_le T s j hT)
    using 2
  · exact weakTransform_eq_weakTransformI _ _ _
  · exact reducedTransform_eq_idealSheaf_append _ _ _

/-- **The order clause of [Kol07, Lemma 102] for the core over a sequence**, given the
identification of the two push-forwards: if `L` has no empty centres and is a smooth blow-up
sequence of order `≥ s` for the restricted triple, the core over `L` at `Z_{-1}` and `S_0` is a
smooth blow-up sequence of order `≥ s` starting with `(M, 𝓘, s, E)` — the first blow-up has order
`s` and the tail order `≥ s` (`cons_isOfOrder_of_bridge`); when `Z_{-1}` is empty the first blow-up
is deleted and the tail is transported along the isomorphism of the empty blow-up. -/
theorem coreOfListOf_isOfOrderGe_of_bridge (hbr : PushforwardBridge.{u} ψ₀)
    (hLne : L.NoEmptyCenters)
    (hL : L.toSuccession.IsOfOrderGe (restrictedTriple T s j hT).I s
      (restrictedTriple T s j hT).F.idealSheaf) :
    (coreOfListOf (BD.isClosedSubmanifold_Zminus1 T s j) (isClosedSubmanifold_transformS T s j)
      L).toSuccession.IsOfOrderGe T.I s T.F.idealSheaf := by
  have hPne := BlowUpSequence.noEmptyCenters_pushforward_of_bridge hbr
    (isClosedSubmanifold_transformS T s j) _ hLne
  unfold coreOfListOf
  by_cases hZ0 : BD.Zminus1 T.I s (T.F.hyp j) = ∅
  · rw [BlowUpSequence.eraseEmpty_cons_of_eq_empty _ _ hZ0,
      BlowUpSequence.eraseEmpty_of_noEmptyCenters _ hPne]
    apply BlowUpSequence.isOfOrderGe_map_emptyBlowUp
    convert pushforward_isOfOrderGe_of_bridge T s j hT L hbr hLne hL using 2
    · exact (weakTransformI_eq_comap_of_eq_empty _ _ _ hZ0).symm
    · exact (idealSheaf_append_eq_comap_of_eq_empty _ _ _ hZ0).symm
  · rw [BlowUpSequence.eraseEmpty_cons_of_ne_empty _ _ hZ0,
      BlowUpSequence.eraseEmpty_of_noEmptyCenters _ hPne]
    exact (cons_isOfOrder_of_bridge T s j hT L hbr hLne hL).isOfOrderGe

end BDan

section Core

variable [FiniteDimensional 𝕜 E] {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  {m : ℕ}

/-- **The order clause of [Kol07, Lemma 102]**, given the identification of the two push-forwards:
`BD_{n,m,j}(M, 𝓘, E)` is a smooth blow-up sequence of order `m` starting with `(M, 𝓘, E)`. The
first blow-up has order `s = tuningParam m` for the tuned ideal (`BD.isOfOrder_firstStep`); the
pushed-forward
tail has order `≥ s` by [Kol07, Corollary 85] with `S_0` in the boundary
(`pushforward_isOfOrderGe_append`, the weak transform `I_0` being D-balanced of order `≤ s`);
when the first blow-up is empty it is deleted and the tail is transported along the isomorphism.
The whole is proved for the tuned triple `(M, W_s(𝓘), E)` at the mark `s` and carried back to
`(𝓘, m)` by `orderReduction_tuned_iff` (Step 1 of the proof of [Kol07, Theorem 103]). -/
theorem BDan_isOfOrder_of_bridge (hbr : PushforwardBridge.{u} ψ₀)
    (inp : BMOanData 𝕜 (n - 1) (tuningParam m)) (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BOClass m T) (j : T.F.ι) :
    (BDan m inp T hT j).toSuccession.IsOfOrder T.I T.F.idealSheaf m := by
  have hT' : BDan.BDClass (tuningParam m) (T.tuned m hT.1) :=
    ⟨AnalyticTriple.boClass_tuned hT, AnalyticTriple.isDBalanced_tuned hT⟩
  suffices h : (BDan m inp T hT j).toSuccession.IsOfOrderGe (T.tuned m hT.1).I (tuningParam m)
      (T.tuned m hT.1).F.idealSheaf from
    FiniteSuccession.isOfOrder_of_isOfOrderGe_of_ord_le _
      ((AnalyticTriple.orderReduction_tuned_iff T hT _).mp h) hT.2.1
  exact BDan.coreOfListOf_isOfOrderGe_of_bridge (T.tuned m hT.1) (tuningParam m) j hT' _ hbr
    (inp.functor.noEmptyCenters _ _) (inp.isOfOrderGe _ _)

end Core

end Hironaka.Manifold

end
