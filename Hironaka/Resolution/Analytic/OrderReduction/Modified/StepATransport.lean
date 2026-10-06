/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.NonmonomialFunctor
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.OrderReduction.FamilyIndependence
import Hironaka.Resolution.Analytic.OrderReduction.Modified.InducedValueFunctor
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The rounds on the nonmonomial part: transport of one link of the descent

The second condition of [Kol07, 34.1] and the compatibility [Wlo09, Theorem 2.0.3 (4)] for one link
of the descent of the rounds on the nonmonomial part ([Kol07, 111, Step 1]; [Wlo09, Theorem 7.4.1]):
along a local analytic isomorphism `h : N → M` carrying an open `W' ⊆ N` into `W ⊆ M`, a descent
state over `W'` for the pulled-back triple and a descent state over `W` at the same bound `d`, whose
lists agree **up to empty blow-ups after pulling back**, keep that relation through one link
(`descentLink_rel`; smaller opens `V' ⊆ W'`, `V ⊆ W` with `h(V') ⊆ V`). This is
`ChainState.link_rel` with the family read at the nonmonomial triple of the induced triple
(`nonmonomialFunctor`): the list algebra is `BlowUpSequence.shrinkAppend_eraseEmpty_pullback`
unchanged; the two appended values of the round are compared by
`AnalyticFamilyFunctor.inducedValue_rel` for that functor, whose class proofs are the invariants of
the descent (`BState.nonmonomialClass`), transported to the cleaned lists by
`nonmonomialClass_induced_eraseEmpty` (the nonmonomial part is indifferent to empty members and
commutes with pull-back: `NonmonomialIndiff.lean`, `NonmonomialComap`).

The relation is the inductive step of the compatibility of the values and of the independence of
the value from the chain and the outer open; the alignment of two descents of different lengths
(the empty links above the smaller bound) is `StepAAlign.lean`.
-/

public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

open Hironaka.Manifold.BMO

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))

/-! ### The class of the induced triple of the cleaned list -/

section Class

variable {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (TW : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X) (m : ℕ)
  (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
  (hL : L.toSuccession.IsOfOrderGe TW.I m TW.F.idealSheaf)
  (hLe : L.eraseEmpty.toSuccession.IsOfOrderGe TW.I m TW.F.idealSheaf) {d : ℕ}

include hcomp in
/-- **The invariant of the descent passes to the cleaned list** ([Kol07, 32] and its counterpart for
boundary members): the
induced triple of the list is the induced triple of the cleaned list pulled back along
`eraseEmptyLast`, up to empty boundary members (`induced_eq_pullback_induced_eraseEmpty`); the
nonmonomial triple ignores the empty members (`nonmonomialClass_of_isEmptyExtension`) and commutes
with the pull-back (`NonmonomialComap`); and the order bound and the finiteness of the nonempty
members transport along the diffeomorphism (`ord_pullback_of_isLocalDiffeomorphAt`). -/
theorem nonmonomialClass_induced_eraseEmpty (hD : NonmonomialClass d (TW.induced m L hL)) :
    NonmonomialClass d (TW.induced m L.eraseEmpty hLe) := by
  have htriple := AnalyticTriple.induced_eq_pullback_induced_eraseEmpty TW m L hL hLe
  have hext := AnalyticTriple.isEmptyExtension_eraseEmptyIdx_induced TW m L hL hLe
  have h1 := nonmonomialClass_of_isEmptyExtension hD
    ((TW.induced m L.eraseEmpty hLe).F.comap ⇑(Diffeomorph.toAnalyticMap L.eraseEmptyLast))
    (HypersurfaceFamily.isSnc_comap (TW.induced m L.eraseEmpty hLe).isSnc _
      L.eraseEmptyLast.isLocalDiffeomorph) hext
  rw [htriple] at h1
  unfold NonmonomialClass at h1 ⊢
  rw [hcomp] at h1
  refine ⟨h1.1, fun y => ?_, ?_⟩
  · have h := h1.2.1 (L.eraseEmptyLast.symm y)
    change ((nonmonomialTriple (TW.induced m L.eraseEmpty hLe)).I.pullback ⇑L.eraseEmptyLast
      _).ord _ ≤ _ at h
    rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
      (L.eraseEmptyLast.isLocalDiffeomorph _), Diffeomorph.apply_symm_apply] at h
    exact h
  · have h := h1.2.2
    change Finite {j // ⇑L.eraseEmptyLast ⁻¹'
      (nonmonomialTriple (TW.induced m L.eraseEmpty hLe)).F.hyp j ≠ ∅} at h
    refine Finite.of_injective
      (fun j : {j // (nonmonomialTriple (TW.induced m L.eraseEmpty hLe)).F.hyp j ≠ ∅} =>
        (⟨j.1, fun he => j.2 ?_⟩ : {j // ⇑L.eraseEmptyLast ⁻¹'
          (nonmonomialTriple (TW.induced m L.eraseEmpty hLe)).F.hyp j ≠ ∅}))
      fun _ _ hj => Subtype.ext (Subtype.mk.inj hj)
    refine Set.eq_empty_iff_forall_notMem.mpr fun y hy =>
      Set.eq_empty_iff_forall_notMem.mp he (L.eraseEmptyLast.symm y) (Set.mem_preimage.mpr ?_)
    rw [Diffeomorph.apply_symm_apply]
    exact hy

end Class

/-! ### One link -/

section Link

variable {M N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  {T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M} {m : ℕ}
  (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hT : AnalyticTriple.BMOClass m T) (hm : 1 ≤ m)

/-- One link is the shrink-and-append step with the value of the round. -/
theorem BState.descentLink_L {W : Opens M} {d : ℕ} (st : BState T m W d) {V : Opens M}
    (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W) (hmd : m ≤ d) :
    (st.descentLink hcomp bo hid hV hVW hT hm hmd).L =
      st.L.shrinkAppend (M.restrictLE (ChainState.le_of_closure_subset hVW))
        (isLocalDiffeomorph_restrictLE _) (st.roundValue bo hV hVW hT (hm.trans hmd)) := rfl

/-- The second condition of [Kol07, 34.1] for one link of the descent: **the relation "the cleaned
list over `W'` is the cleaned pull-back of the list over `W`" along a local analytic isomorphism
`h` with `h(W') ⊆ W`, between two states at the same bound `d`, is kept by one link**, for smaller
opens `V ⊆ W`, `V' ⊆ W'` with `h(V') ⊆ V`. The list algebra is `shrinkAppend_eraseEmpty_pullback`;
the two values of the round are compared by `inducedValue_rel` for the family read at the
nonmonomial triple (`nonmonomialFunctor`; the class proofs from the invariants,
`nonmonomialClass_induced_eraseEmpty` for the cleaned list). The triple over `N` is any triple equal
to the pull-back (`hT'eq`, substituted), so the case of one manifold reads with `h` the identity. -/
theorem descentLink_rel (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω h)
    {T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) N}
    (hT'eq : T' = T.pullback h hh) (hT' : AnalyticTriple.BMOClass m T') {W : Opens M}
    {W' : Opens N} (hWW' : ⇑h '' (W' : Set N) ⊆ W) {d : ℕ} (st : BState T m W d)
    (st' : BState T' m W' d)
    (hrel : st'.L.eraseEmpty = (st.L.pullback (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).eraseEmpty)
    {V : Opens M} (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W)
    {V' : Opens N} (hV' : IsCompact (closure (V' : Set N))) (hV'W' : closure (V' : Set N) ⊆ W')
    (hVV' : ⇑h '' (V' : Set N) ⊆ V) (hmd : m ≤ d) :
    (st'.descentLink hcomp bo hid hV' hV'W' hT' hm hmd).L.eraseEmpty =
      ((st.descentLink hcomp bo hid hV hVW hT hm hmd).L.pullback
        (AnalyticMap.restrictMap h V' V hVV')
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV')).eraseEmpty := by
  subst hT'eq
  have hd : 1 ≤ d := hm.trans hmd
  -- the square of restrictions
  have hsq : (M.restrictLE (ChainState.le_of_closure_subset hVW)).comp
      (AnalyticMap.restrictMap h V' V hVV') =
      (AnalyticMap.restrictMap h W' W hWW').comp
        (N.restrictLE (ChainState.le_of_closure_subset hV'W')) :=
    ContMDiffMap.ext fun _ => Subtype.ext rfl
  have hc₁ : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      ((M.restrictLE (ChainState.le_of_closure_subset hVW)).comp
        (AnalyticMap.restrictMap h V' V hVV')) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp (isLocalDiffeomorph_restrictLE _)
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV')
  have hc₂ : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      ((AnalyticMap.restrictMap h W' W hWW').comp
        (N.restrictLE (ChainState.le_of_closure_subset hV'W'))) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')
      (isLocalDiffeomorph_restrictLE _)
  have e₀ : (st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
      (isLocalDiffeomorph_restrictLE _)).pullback (AnalyticMap.restrictMap h V' V hVV')
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV') =
      (st.L.pullback (AnalyticMap.restrictMap h W' W hWW')
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).pullback
        (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
        (isLocalDiffeomorph_restrictLE _) := by
    rw [AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _,
        AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _]
    exact AnalyticManifold.BlowUpSequence.pullback_congr _ hsq hc₁ hc₂
  have hA : (st'.L.pullback (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
      (isLocalDiffeomorph_restrictLE _)).eraseEmpty =
      ((st.L.pullback (AnalyticMap.restrictMap h W' W hWW')
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).pullback
        (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
        (isLocalDiffeomorph_restrictLE _)).eraseEmpty := by
    rw [← AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty st'.L _
        (isLocalDiffeomorph_restrictLE _), hrel,
      AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty]
  -- the triple over `W'` is the pull-back of the triple over `W` along `h|_{W'}`
  have hmap : (M.inclusion W).comp (AnalyticMap.restrictMap h W' W hWW') =
      h.comp (N.inclusion W') := ContMDiffMap.ext fun _ => rfl
  have hTWeq : (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).pullback
      (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW') =
      (T.pullback h hh).pullback (N.inclusion W') (isLocalDiffeomorph_inclusion N W') := by
    rw [AnalyticTriple.pullback_pullback _ _ _ _ _,
      AnalyticTriple.pullback_pullback _ _ _ _ _]
    exact AnalyticTriple.pullback_eq_of_eq T hmap _ _
  have hL₂ : st'.L.toSuccession.IsOfOrderGe ((T.pullback (M.inclusion W)
      (isLocalDiffeomorph_inclusion M W)).pullback (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).I m
      ((T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).pullback
        (AnalyticMap.restrictMap h W' W hWW')
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).F.idealSheaf := by
    rw [hTWeq]
    exact st'.hge
  -- the class proofs: the invariants of the two states, the one over `W'` read at the pulled-back
  -- triple, and its transport to the erased list
  have hD₁ : NonmonomialClass d (ChainState.inducedTriple T m st.toChainState) :=
    st.nonmonomialClass hT hd
  have hD₂ : NonmonomialClass d (((T.pullback (M.inclusion W)
      (isLocalDiffeomorph_inclusion M W)).pullback
      (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).induced m st'.L hL₂) := by
    rw [AnalyticTriple.induced_congr hTWeq m st'.L hL₂ st'.hge]
    exact st'.nonmonomialClass hT' hd
  have hDe₂ := nonmonomialClass_induced_eraseEmpty hcomp _ m st'.L hL₂
    (AnalyticManifold.BlowUpSequence.isOfOrderGe_eraseEmpty st'.L _ m ((T.pullback (M.inclusion W)
      (isLocalDiffeomorph_inclusion M W)).pullback (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).isSnc hL₂) hD₂
  -- the two values of the round as values of the functor read at the nonmonomial triple
  have hF₁ := st.roundValue_eq_nonmonomialFunctor hT bo hV hVW hd
  have hF₂ : st'.roundValue bo hV' hV'W' hT' hd =
      ((nonmonomialFunctor (bo d)).fam (((T.pullback (M.inclusion W)
        (isLocalDiffeomorph_inclusion M W)).pullback (AnalyticMap.restrictMap h W' W hWW')
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).induced m st'.L hL₂) hD₂).seqOn
        (st'.liftOpen hV'W') (st'.isCompact_closure_liftOpen hV' hV'W') := by
    rw [st'.roundValue_eq_nonmonomialFunctor hT' bo hV' hV'W' hd]
    exact AnalyticFamilyFunctor.fam_seqOn_congr_triple _
      (AnalyticTriple.induced_congr hTWeq.symm m st'.L st'.hge hL₂) _ _ _ _
  -- the maps to the common erased last stage
  have hκ₂ : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      ((st'.L.liftCorestrict (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
        (isLocalDiffeomorph_restrictLE _)).comp (Diffeomorph.toAnalyticMap
        (st'.L.pullback (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
          (isLocalDiffeomorph_restrictLE _)).eraseEmptyLast.symm)) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftCorestrict _ _ _)
      (Diffeomorph.isLocalDiffeomorph _)
  have hκ₁ : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      (((st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _)).comp
        ((st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _)).pullbackLiftLast (AnalyticMap.restrictMap h V' V hVV')
          (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV'))).comp
        (Diffeomorph.toAnalyticMap ((AnalyticManifold.BlowUpSequence.stageOfEq e₀).trans
          (((st.L.pullback (AnalyticMap.restrictMap h W' W hWW')
            (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).pullback
            (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
            (isLocalDiffeomorph_restrictLE _)).eraseEmptyLast.trans
            (AnalyticManifold.BlowUpSequence.stageOfEq hA.symm))).symm)) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftCorestrict _ _ _)
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _))
      (Diffeomorph.isLocalDiffeomorph _)
  -- the comparison of the two round values
  have hF := (congrArg (fun X : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜
      (Fin n → 𝕜))
      ((st'.L.stage (Fin.last _)).restrict (st'.liftOpen hV'W')) => (X.pullback
        ((st'.L.liftCorestrict (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
          (isLocalDiffeomorph_restrictLE _)).comp (Diffeomorph.toAnalyticMap
          (st'.L.pullback (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
            (isLocalDiffeomorph_restrictLE _)).eraseEmptyLast.symm)) hκ₂).eraseEmpty) hF₂).trans
    (((nonmonomialFunctor (bo d)).inducedValue_rel
      (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)) m
      (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')
      st.L st.hge hD₁ (M.restrictLE (ChainState.le_of_closure_subset hVW))
      (isLocalDiffeomorph_restrictLE _) (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
      (isLocalDiffeomorph_restrictLE _) (AnalyticMap.restrictMap h V' V hVV')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV') hsq
      (nonmonomialFunctor_commutesWithLocalIsos (bo d) hcomp)
      (nonmonomialFunctor_indifferentToEmptyMembers (bo d))
      (fun T g hg hT => nonmonomialClass_pullback hcomp hT g hg) st'.L hL₂ hD₂ hDe₂ hrel
      (st.isCompact_closure_liftOpen hV hVW) (st'.isCompact_closure_liftOpen hV' hV'W')
      (isCompact_closure_range_restrictLE (ChainState.le_of_closure_subset hV'W') hV' hV'W')
      e₀ hA hκ₂ hκ₁).trans
    (congrArg (fun X : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      ((st.L.stage (Fin.last _)).restrict (st.liftOpen hVW)) => (X.pullback
        (((st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _)).comp
          ((st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
            (isLocalDiffeomorph_restrictLE _)).pullbackLiftLast
            (AnalyticMap.restrictMap h V' V hVV')
            (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV'))).comp
          (Diffeomorph.toAnalyticMap ((AnalyticManifold.BlowUpSequence.stageOfEq e₀).trans
            (((st.L.pullback (AnalyticMap.restrictMap h W' W hWW')
              (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).pullback
              (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
              (isLocalDiffeomorph_restrictLE _)).eraseEmptyLast.trans
              (AnalyticManifold.BlowUpSequence.stageOfEq hA.symm))).symm)) hκ₁).eraseEmpty)
                  hF₁).symm)
  exact (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty (st'.descentLink_L hcomp bo hid hT' hm
      hV' hV'W' hmd)).trans
    ((AnalyticManifold.BlowUpSequence.shrinkAppend_eraseEmpty_pullback st.L st'.L _ _ _ _ _ _ _ _
      (st.roundValue bo hV hVW hT hd) (st'.roundValue bo hV' hV'W' hT' hd) e₀ hA hκ₂ hκ₁ hF).trans
      (congrArg (fun X : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          (M.restrict V) =>
        (X.pullback (AnalyticMap.restrictMap h V' V hVV')
          (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV')).eraseEmpty)
        (st.descentLink_L hcomp bo hid hT hm hV hVW hmd)).symm)

end Link

end Hironaka.Manifold.BMOmod

end
