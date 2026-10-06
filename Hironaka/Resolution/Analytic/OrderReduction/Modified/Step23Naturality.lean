/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step3Link
public import Hironaka.Resolution.Analytic.OrderReduction.BDIndiff
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.OrderReduction.FamilyIndependence
import Hironaka.Resolution.Analytic.OrderReduction.Modified.InducedValueFunctor
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepAIndiff
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The separation and monomial steps: naturality of the links and of the continuation

Clause (2) of the marked order reduction theorem [Kol07, Theorem 107] and the compatibility of the
sequences over different relatively compact opens [Wlo09, Theorem 2.0.3 (4)] require the runs of
the three steps over two opens, or across a local analytic isomorphism, to agree up to the
deletion of empty blow-ups [Kol07, 34.1]. For the first step this is proved by aligning two chains
link by link (`descentStateAux_rel`, `descentStateAux_L_indiff`); this module continues the
alignment through the links of the separation step and of the monomial step. Each fact is the
corresponding fact for a link of the first step with the family of the round replaced,
`sepFunctor` for the separation step and the functor of `MonomialStep3Fam` for the monomial step:

* **commutation with local analytic isomorphisms for one link** (`SState.sepLink_rel`,
  `SState.step3Link_rel`), the second condition of [Kol07, 34.1]: the relation "the list over `W'`
  with empty blow-ups deleted is the pull-back of the list over `W` with empty blow-ups deleted",
  along a local analytic isomorphism `h` with `h(W') ⊆ W`, is kept by one link, for `V ⊆ W`,
  `V' ⊆ W'` with `h(V') ⊆ V`. The list algebra is `BlowUpSequence.shrinkAppend_eraseEmpty_pullback`;
  the two values of the round are compared by `AnalyticFamilyFunctor.inducedValue_rel` for the
  family of the round (its two naturality properties and the closure of its class under
  pull-back), and the class of the induced triple of the cleaned list is
  `sepClass_induced_eraseEmpty`;
* **indifference to empty boundary members for one link** (`SState.sepLink_L_indiff`,
  `SState.step3Link_L_indiff`; the counterpart, for boundary members, of [Kol07, 32]): two states
  with the same list, for `T` and for `T`
  with its boundary replaced by an empty extension, link to the same list, since the family of
  the round is indifferent to empty members;
* **the continuation** `step23Aux`: both facts link by link, `sepDescentAux_rel` and
  `sepDescentAux_L_indiff` by induction along the descent, then `step23Aux_rel` and
  `step23Aux_L_indiff` through the link of the monomial step. Both continuations run the same
  number of links, so no offset of bounds is needed.

These are the inputs of `bmoSeqOn_compat`, `bmoSeqOn_pullback` and `bmoSeqOn_indiff`.
-/

public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO

open _root_.Manifold

open Hironaka.Manifold.BMOmod

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

/-! ### The class of the induced triple of the cleaned list -/

section Class

variable (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (TW : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X) (m : ℕ)
  (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
  (hL : L.toSuccession.IsOfOrderGe TW.I m TW.F.idealSheaf)
  (hLe : L.eraseEmpty.toSuccession.IsOfOrderGe TW.I m TW.F.idealSheaf) {s : ℕ}

include hcomp in
/-- **The class of the round of the separation step passes to the cleaned list**: the induced
triple of a list is, up to empty boundary members, the induced triple of the list with empty
blow-ups deleted, pulled back along the diffeomorphism `eraseEmptyLast` of the last stages
(`AnalyticTriple.induced_eq_pullback_induced_eraseEmpty`); the separating triple ignores empty
members (`sepClass_of_isEmptyExtension`) and commutes with pull-back (`sepTripleAt_pullback`), and
the order bound and the finiteness of the nonempty members transport along the diffeomorphism. -/
theorem sepClass_induced_eraseEmpty (hD : SepClass m s (TW.induced m L hL)) :
    SepClass m s (TW.induced m L.eraseEmpty hLe) := by
  have htriple := AnalyticTriple.induced_eq_pullback_induced_eraseEmpty TW m L hL hLe
  have hext := AnalyticTriple.isEmptyExtension_eraseEmptyIdx_induced TW m L hL hLe
  have h1 := sepClass_of_isEmptyExtension hD
    ((TW.induced m L.eraseEmpty hLe).F.comap ⇑(Diffeomorph.toAnalyticMap L.eraseEmptyLast))
    (HypersurfaceFamily.isSnc_comap (TW.induced m L.eraseEmpty hLe).isSnc _
      L.eraseEmptyLast.isLocalDiffeomorph) hext
  rw [htriple] at h1
  unfold SepClass at h1 ⊢
  rw [sepTripleAt_pullback hcomp] at h1
  refine ⟨h1.1, fun y => ?_, ?_⟩
  · have h := h1.2.1 (L.eraseEmptyLast.symm y)
    change ((sepTripleAt (TW.induced m L.eraseEmpty hLe) m s).I.pullback ⇑L.eraseEmptyLast
      _).ord _ ≤ _ at h
    rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
      (L.eraseEmptyLast.isLocalDiffeomorph _), Diffeomorph.apply_symm_apply] at h
    exact h
  · have h := h1.2.2
    change Finite {j // ⇑L.eraseEmptyLast ⁻¹'
      (sepTripleAt (TW.induced m L.eraseEmpty hLe) m s).F.hyp j ≠ ∅} at h
    refine Finite.of_injective
      (fun j : {j // (sepTripleAt (TW.induced m L.eraseEmpty hLe) m s).F.hyp j ≠ ∅} =>
        (⟨j.1, fun he => j.2 ?_⟩ : {j // ⇑L.eraseEmptyLast ⁻¹'
          (sepTripleAt (TW.induced m L.eraseEmpty hLe) m s).F.hyp j ≠ ∅}))
      fun _ _ hj => Subtype.ext (Subtype.mk.inj hj)
    refine Set.eq_empty_iff_forall_notMem.mpr fun y hy =>
      Set.eq_empty_iff_forall_notMem.mp he (L.eraseEmptyLast.symm y) (Set.mem_preimage.mpr ?_)
    rw [Diffeomorph.apply_symm_apply]
    exact hy

variable {m} in
/-- The induced triple of a triple of the marked class is in the marked class (the mark, and the
finiteness of the nonempty members). -/
theorem bmoClass_induced_of_bmoClass {T₀ : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n →
    𝕜)) X}
    (hT₀ : AnalyticTriple.BMOClass m T₀) (L' : AnalyticManifold.BlowUpSequence
        (ContinuousLinearEquiv.refl 𝕜 (Fin n →
        𝕜)) X)
    (hL' : L'.toSuccession.IsOfOrderGe T₀.I m T₀.F.idealSheaf) :
    AnalyticTriple.BMOClass m (T₀.induced m L' hL') :=
  ⟨hT₀.1, finite_nonempty_totalTransformSeqFrom L'.toSuccession _ hT₀.2 (Fin.last _)⟩

variable {m} in
/-- The marked class is closed under pull-back along local analytic isomorphisms. -/
theorem bmoClass_pullback_of_isLocalDiffeomorph {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    {T₀ : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X}
    (hT₀ : AnalyticTriple.BMOClass m T₀) (g : AnalyticMap N X)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g) :
    AnalyticTriple.BMOClass m (T₀.pullback g hg) :=
  ⟨hT₀.1, finite_nonempty_hyp_comap T₀.F g hT₀.2⟩

end Class

/-! ### One link: commutation with local analytic isomorphisms -/

section Link

variable {M N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  {T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M} {m : ℕ}
  (hT : AnalyticTriple.BMOClass m T) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hidN : NonmonomialTransformIdentityMod.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (st3 : MonomialStep3Fam.{u} 𝕜 n m) (hm : 1 ≤ m)

include hT bo hcomp hidN hm in
/-- **Commutation with local analytic isomorphisms for one link of the separation step** (the
second condition of [Kol07, 34.1]): the relation "the list over `W'` with empty blow-ups deleted is
the pull-back along `h|_{W'}` of the list over `W` with empty blow-ups deleted", between two states
at the same separation bound `s`, for `T` and for a triple equal to the pull-back of `T` along `h`,
is kept by one link, for `V ⊆ W`, `V' ⊆ W'` with `h(V') ⊆ V`. The list algebra is
`BlowUpSequence.shrinkAppend_eraseEmpty_pullback`; the two values of the round are compared by
`inducedValue_rel` for `sepFunctor` (its two naturality properties, the closure of the class under
pull-back, and `sepClass_induced_eraseEmpty` for the cleaned list). -/
theorem SState.sepLink_rel (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω h)
    {T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) N}
    (hT'eq : T' = T.pullback h hh) (hT' : AnalyticTriple.BMOClass m T') {W : Opens M}
    {W' : Opens N} (hWW' : ⇑h '' (W' : Set N) ⊆ W) {s : ℕ} (st : SState T m W s)
    (st' : SState T' m W' s)
    (hrel : st'.L.eraseEmpty = (st.L.pullback (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).eraseEmpty)
    {V : Opens M} (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W)
    {V' : Opens N} (hV' : IsCompact (closure (V' : Set N))) (hV'W' : closure (V' : Set N) ⊆ W')
    (hVV' : ⇑h '' (V' : Set N) ⊆ V) (hs : 1 ≤ s) :
    (st'.sepLink hT' bo hcomp hidN hV' hV'W' hm hs).L.eraseEmpty =
      ((st.sepLink hT bo hcomp hidN hV hVW hm hs).L.pullback
        (AnalyticMap.restrictMap h V' V hVV')
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV')).eraseEmpty := by
  subst hT'eq
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
  -- the class proofs
  have hD₁ : SepClass m s (ChainState.inducedTriple T m st.toChainState) := st.sepClass hT hs
  have hD₂ : SepClass m s (((T.pullback (M.inclusion W)
      (isLocalDiffeomorph_inclusion M W)).pullback
      (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).induced m st'.L hL₂) := by
    rw [AnalyticTriple.induced_congr hTWeq m st'.L hL₂ st'.hge]
    exact st'.sepClass hT' hs
  have hDe₂ := sepClass_induced_eraseEmpty hcomp _ m st'.L hL₂
    (AnalyticManifold.BlowUpSequence.isOfOrderGe_eraseEmpty st'.L _ m ((T.pullback (M.inclusion W)
      (isLocalDiffeomorph_inclusion M W)).pullback (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).isSnc hL₂) hD₂
  -- the two round values as values of the functor
  have hF₁ : st.roundValue hT bo hV hVW hs =
      ((sepFunctor (bo (m * s))).fam (ChainState.inducedTriple T m st.toChainState) hD₁).seqOn
        (ChainState.readOpen T m st.toChainState hVW)
        (ChainState.isCompact_closure_readOpen T m st.toChainState hV hVW) := rfl
  have hF₂ : st'.roundValue hT' bo hV' hV'W' hs =
      ((sepFunctor (bo (m * s))).fam (((T.pullback (M.inclusion W)
        (isLocalDiffeomorph_inclusion M W)).pullback (AnalyticMap.restrictMap h W' W hWW')
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).induced m st'.L hL₂) hD₂).seqOn
        (ChainState.readOpen (T.pullback h hh) m st'.toChainState hV'W')
        (ChainState.isCompact_closure_readOpen (T.pullback h hh) m st'.toChainState hV' hV'W') :=
    AnalyticFamilyFunctor.fam_seqOn_congr_triple _
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
      ((st'.L.stage (Fin.last _)).restrict
        (ChainState.readOpen (T.pullback h hh) m st'.toChainState hV'W')) => (X.pullback
        ((st'.L.liftCorestrict (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
          (isLocalDiffeomorph_restrictLE _)).comp (Diffeomorph.toAnalyticMap
          (st'.L.pullback (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
            (isLocalDiffeomorph_restrictLE _)).eraseEmptyLast.symm)) hκ₂).eraseEmpty) hF₂).trans
    (((sepFunctor (bo (m * s))).inducedValue_rel
      (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)) m
      (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')
      st.L st.hge hD₁ (M.restrictLE (ChainState.le_of_closure_subset hVW))
      (isLocalDiffeomorph_restrictLE _) (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
      (isLocalDiffeomorph_restrictLE _) (AnalyticMap.restrictMap h V' V hVV')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV') hsq
      (sepFunctor_commutesWithLocalIsos (bo (m * s)) hcomp)
      (sepFunctor_indifferentToEmptyMembers (bo (m * s)))
      (fun T g hg hT => sepClass_pullback hcomp hT g hg) st'.L hL₂ hD₂ hDe₂ hrel
      (ChainState.isCompact_closure_readOpen T m st.toChainState hV hVW)
      (ChainState.isCompact_closure_readOpen (T.pullback h hh) m st'.toChainState hV' hV'W')
      (isCompact_closure_range_restrictLE (ChainState.le_of_closure_subset hV'W') hV' hV'W')
      e₀ hA hκ₂ hκ₁).trans
    (congrArg (fun X : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      ((st.L.stage (Fin.last _)).restrict (ChainState.readOpen T m st.toChainState hVW)) =>
        (X.pullback
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
  exact (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty (st'.sepLink_L hT' bo hcomp hidN hV'
      hV'W' hm hs)).trans
    ((AnalyticManifold.BlowUpSequence.shrinkAppend_eraseEmpty_pullback st.L st'.L _ _ _ _ _ _ _ _
      (st.roundValue hT bo hV hVW hs) (st'.roundValue hT' bo hV' hV'W' hs) e₀ hA hκ₂ hκ₁ hF).trans
      (congrArg (fun X : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          (M.restrict V) =>
        (X.pullback (AnalyticMap.restrictMap h V' V hVV')
          (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV')).eraseEmpty)
        (st.sepLink_L hT bo hcomp hidN hV hVW hm hs)).symm)

include hT st3 in
/-- The same for the link of the monomial step, with the functor of the procedure `st3.functor` in
place of `sepFunctor` (`inducedValue_rel` with `st3.commutesWithLocalIsos` and
`st3.indifferentToEmptyMembers`). -/
theorem SState.step3Link_rel (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω h)
    {T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) N}
    (hT'eq : T' = T.pullback h hh) (hT' : AnalyticTriple.BMOClass m T') {W : Opens M}
    {W' : Opens N} (hWW' : ⇑h '' (W' : Set N) ⊆ W) (st : SState T m W 0) (st' : SState T' m W' 0)
    (hrel : st'.L.eraseEmpty = (st.L.pullback (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).eraseEmpty)
    {V : Opens M} (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W)
    {V' : Opens N} (hV' : IsCompact (closure (V' : Set N))) (hV'W' : closure (V' : Set N) ⊆ W')
    (hVV' : ⇑h '' (V' : Set N) ⊆ V) :
    (st'.step3Link hT' st3 hV' hV'W').L.eraseEmpty =
      ((st.step3Link hT st3 hV hVW).L.pullback (AnalyticMap.restrictMap h V' V hVV')
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV')).eraseEmpty := by
  subst hT'eq
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
  have hD₁ : AnalyticTriple.BMOClass m (ChainState.inducedTriple T m st.toChainState) :=
    bmoClass_inducedTriple T m hT st.toChainState
  have hTW : AnalyticTriple.BMOClass m ((T.pullback (M.inclusion W)
      (isLocalDiffeomorph_inclusion M W)).pullback (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')) :=
    bmoClass_pullback_of_isLocalDiffeomorph
      (bmoClass_pullback_of_isLocalDiffeomorph hT (M.inclusion W) (isLocalDiffeomorph_inclusion M
          W))
      _ _
  have hD₂ := bmoClass_induced_of_bmoClass hTW st'.L hL₂
  have hDe₂ := bmoClass_induced_of_bmoClass hTW st'.L.eraseEmpty
    (AnalyticManifold.BlowUpSequence.isOfOrderGe_eraseEmpty st'.L _ m ((T.pullback (M.inclusion W)
      (isLocalDiffeomorph_inclusion M W)).pullback (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).isSnc hL₂)
  have hF₁ : st.step3Value hT st3 hV hVW =
      (st3.functor.fam (ChainState.inducedTriple T m st.toChainState) hD₁).seqOn
        (ChainState.readOpen T m st.toChainState hVW)
        (ChainState.isCompact_closure_readOpen T m st.toChainState hV hVW) := rfl
  have hF₂ : st'.step3Value hT' st3 hV' hV'W' =
      (st3.functor.fam (((T.pullback (M.inclusion W)
        (isLocalDiffeomorph_inclusion M W)).pullback (AnalyticMap.restrictMap h W' W hWW')
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).induced m st'.L hL₂) hD₂).seqOn
        (ChainState.readOpen (T.pullback h hh) m st'.toChainState hV'W')
        (ChainState.isCompact_closure_readOpen (T.pullback h hh) m st'.toChainState hV' hV'W') :=
    AnalyticFamilyFunctor.fam_seqOn_congr_triple _
      (AnalyticTriple.induced_congr hTWeq.symm m st'.L st'.hge hL₂) _ _ _ _
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
  have hF := (congrArg (fun X : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜
      (Fin n → 𝕜))
      ((st'.L.stage (Fin.last _)).restrict
        (ChainState.readOpen (T.pullback h hh) m st'.toChainState hV'W')) => (X.pullback
        ((st'.L.liftCorestrict (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
          (isLocalDiffeomorph_restrictLE _)).comp (Diffeomorph.toAnalyticMap
          (st'.L.pullback (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
            (isLocalDiffeomorph_restrictLE _)).eraseEmptyLast.symm)) hκ₂).eraseEmpty) hF₂).trans
    ((st3.functor.inducedValue_rel
      (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)) m
      (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')
      st.L st.hge hD₁ (M.restrictLE (ChainState.le_of_closure_subset hVW))
      (isLocalDiffeomorph_restrictLE _) (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
      (isLocalDiffeomorph_restrictLE _) (AnalyticMap.restrictMap h V' V hVV')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV') hsq
      st3.commutesWithLocalIsos st3.indifferentToEmptyMembers
      (fun T g hg hT => bmoClass_pullback_of_isLocalDiffeomorph hT g hg) st'.L hL₂ hD₂ hDe₂ hrel
      (ChainState.isCompact_closure_readOpen T m st.toChainState hV hVW)
      (ChainState.isCompact_closure_readOpen (T.pullback h hh) m st'.toChainState hV' hV'W')
      (isCompact_closure_range_restrictLE (ChainState.le_of_closure_subset hV'W') hV' hV'W')
      e₀ hA hκ₂ hκ₁).trans
    (congrArg (fun X : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      ((st.L.stage (Fin.last _)).restrict (ChainState.readOpen T m st.toChainState hVW)) =>
        (X.pullback
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
  exact (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty (st'.step3Link_L hT' st3 hV'
      hV'W')).trans
    ((AnalyticManifold.BlowUpSequence.shrinkAppend_eraseEmpty_pullback st.L st'.L _ _ _ _ _ _ _ _
      (st.step3Value hT st3 hV hVW) (st'.step3Value hT' st3 hV' hV'W') e₀ hA hκ₂ hκ₁ hF).trans
      (congrArg (fun X : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          (M.restrict V) =>
        (X.pullback (AnalyticMap.restrictMap h V' V hVV')
          (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV')).eraseEmpty)
        (st.step3Link_L hT st3 hV hVW)).symm)

end Link

/-! ### One link: indifference to empty boundary members -/

section Indiff

variable {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  {T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M} {m : ℕ}
  (hT : AnalyticTriple.BMOClass m T) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hidN : NonmonomialTransformIdentityMod.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (st3 : MonomialStep3Fam.{u} 𝕜 n m) (hm : 1 ≤ m)
  (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (e : F'.ι ↪o T.F.ι) (he : ∀ i, T.F.hyp (e i) = F'.hyp i)
  (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅)
  (hT' : AnalyticTriple.BMOClass m (BDan.withBoundary T F' hsnc'))

include hT bo hcomp hidN hm he he' hT' in
/-- **Indifference to empty boundary members for one link of the separation step** (the
counterpart, for boundary members, of [Kol07, 32]):
two states with the same list, for `T` and for `T` with its boundary replaced by an empty
extension `F'`, link to the same list. The restricted triples over `W` are again related by a
boundary change along `e`, and the value of the round is the value of `sepFunctor` at the induced
triples (`IndifferentToEmptyMembers.seqOn_induced_indiff` with
`sepFunctor_indifferentToEmptyMembers`). -/
theorem SState.sepLink_L_indiff {W : Opens M} {s : ℕ} (st : SState T m W s)
    (st' : SState (BDan.withBoundary T F' hsnc') m W s) (hL : st.L = st'.L) {V : Opens M}
    (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W) (hs : 1 ≤ s) :
    (st.sepLink hT bo hcomp hidN hV hVW hm hs).L =
      (st'.sepLink hT' bo hcomp hidN hV hVW hm hs).L := by
  obtain ⟨⟨L, hge⟩, sep⟩ := st
  obtain ⟨⟨L', hge'⟩, sep'⟩ := st'
  change L = L' at hL
  subst hL
  rw [SState.sepLink_L, SState.sepLink_L]
  refine congrArg (L.shrinkAppend _ _) ?_
  -- the pulled-back triples over `W`: the same boundary change along `e`
  have hTWeq : BDan.withBoundary (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W))
      ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
        (isLocalDiffeomorph_inclusion M W)).F
      ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
        (isLocalDiffeomorph_inclusion M W)).isSnc =
      (BDan.withBoundary T F' hsnc').pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W) :=
    AnalyticTriple.ext' rfl rfl
  have hge'' : L.toSuccession.IsOfOrderGe
      (BDan.withBoundary (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W))
        ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
          (isLocalDiffeomorph_inclusion M W)).F
        ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
          (isLocalDiffeomorph_inclusion M W)).isSnc).I m
      (BDan.withBoundary (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W))
        ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
          (isLocalDiffeomorph_inclusion M W)).F
        ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
          (isLocalDiffeomorph_inclusion M W)).isSnc).F.idealSheaf := by
    rw [hTWeq]
    exact hge'
  have hDw : SepClass m s
      ((BDan.withBoundary (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W))
        ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
          (isLocalDiffeomorph_inclusion M W)).F
        ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
          (isLocalDiffeomorph_inclusion M W)).isSnc).induced m L hge'') := by
    rw [AnalyticTriple.induced_congr hTWeq m L hge'' hge']
    exact SState.sepClass hT' ⟨⟨L, hge'⟩, sep'⟩ hs
  have heW : ∀ k, (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).F.hyp (e k) =
      ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
        (isLocalDiffeomorph_inclusion M W)).F.hyp k :=
    fun k => congrArg (fun S => ⇑(M.inclusion W) ⁻¹' S) (he k)
  have heW' : ∀ b, b ∉ Set.range e →
      (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).F.hyp b = ∅ :=
    fun b hb => (congrArg (fun S => ⇑(M.inclusion W) ⁻¹' S) (he' b hb)).trans Set.preimage_empty
  exact (AnalyticFamilyFunctor.IndifferentToEmptyMembers.seqOn_induced_indiff
    (sepFunctor_indifferentToEmptyMembers (bo (m * s)))
    (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W))
    ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).F
    ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
      (isLocalDiffeomorph_inclusion M W)).isSnc e heW heW' m L hge hge'' _ hDw _ _).trans
    ((sepFunctor (bo (m * s))).fam_seqOn_congr_triple
      (AnalyticTriple.induced_congr hTWeq m L hge'' hge') hDw _ _ _)

include hT st3 he he' hT' in
/-- The same for the link of the monomial step (`seqOn_induced_indiff` with
`st3.indifferentToEmptyMembers`). -/
theorem SState.step3Link_L_indiff {W : Opens M} (st : SState T m W 0)
    (st' : SState (BDan.withBoundary T F' hsnc') m W 0) (hL : st.L = st'.L) {V : Opens M}
    (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W) :
    (st.step3Link hT st3 hV hVW).L = (st'.step3Link hT' st3 hV hVW).L := by
  obtain ⟨⟨L, hge⟩, sep⟩ := st
  obtain ⟨⟨L', hge'⟩, sep'⟩ := st'
  change L = L' at hL
  subst hL
  rw [SState.step3Link_L, SState.step3Link_L]
  refine congrArg (L.shrinkAppend _ _) ?_
  have hTWeq : BDan.withBoundary (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W))
      ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
        (isLocalDiffeomorph_inclusion M W)).F
      ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
        (isLocalDiffeomorph_inclusion M W)).isSnc =
      (BDan.withBoundary T F' hsnc').pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W) :=
    AnalyticTriple.ext' rfl rfl
  have hge'' : L.toSuccession.IsOfOrderGe
      (BDan.withBoundary (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W))
        ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
          (isLocalDiffeomorph_inclusion M W)).F
        ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
          (isLocalDiffeomorph_inclusion M W)).isSnc).I m
      (BDan.withBoundary (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W))
        ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
          (isLocalDiffeomorph_inclusion M W)).F
        ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
          (isLocalDiffeomorph_inclusion M W)).isSnc).F.idealSheaf := by
    rw [hTWeq]
    exact hge'
  have hDw : AnalyticTriple.BMOClass m
      ((BDan.withBoundary (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W))
        ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
          (isLocalDiffeomorph_inclusion M W)).F
        ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
          (isLocalDiffeomorph_inclusion M W)).isSnc).induced m L hge'') := by
    rw [AnalyticTriple.induced_congr hTWeq m L hge'' hge']
    exact bmoClass_induced_of_bmoClass
      (bmoClass_pullback_of_isLocalDiffeomorph hT' (M.inclusion W)
        (isLocalDiffeomorph_inclusion M W)) L hge'
  have heW : ∀ k, (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).F.hyp (e k) =
      ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
        (isLocalDiffeomorph_inclusion M W)).F.hyp k :=
    fun k => congrArg (fun S => ⇑(M.inclusion W) ⁻¹' S) (he k)
  have heW' : ∀ b, b ∉ Set.range e →
      (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).F.hyp b = ∅ :=
    fun b hb => (congrArg (fun S => ⇑(M.inclusion W) ⁻¹' S) (he' b hb)).trans Set.preimage_empty
  exact (AnalyticFamilyFunctor.IndifferentToEmptyMembers.seqOn_induced_indiff
    st3.indifferentToEmptyMembers
    (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W))
    ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).F
    ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
      (isLocalDiffeomorph_inclusion M W)).isSnc e heW heW' m L hge hge'' _ hDw _ _).trans
    (st3.functor.fam_seqOn_congr_triple
      (AnalyticTriple.induced_congr hTWeq m L hge'' hge') hDw _ _ _)

end Indiff

/-! ### The continuation along a chain: both facts link by link -/

section Chain

variable {M N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  {T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M} {m : ℕ}
  (hT : AnalyticTriple.BMOClass m T) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hidN : NonmonomialTransformIdentityMod.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (st3 : MonomialStep3Fam.{u} 𝕜 n m) (hm : 1 ≤ m)

include hT bo hcomp hidN hm in
/-- The descent of the separation step keeps the relation of `SState.sepLink_rel` link by link. -/
theorem sepDescentAux_rel (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω h)
    {T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) N}
    (hT'eq : T' = T.pullback h hh) (hT' : AnalyticTriple.BMOClass m T') (W : ℕ → Opens M)
    (hW : ∀ k, IsCompact (closure (W k : Set M))) (r : ℕ)
    (hWsub : ∀ k, k < r → closure (W (k + 1) : Set M) ⊆ W k) (X : ℕ → Opens N)
    (hX : ∀ k, IsCompact (closure (X k : Set N)))
    (hXsub : ∀ k, k < r → closure (X (k + 1) : Set N) ⊆ X k)
    (hXW : ∀ j, ⇑h '' (X j : Set N) ⊆ W j) (S₀ : ℕ) (st₀ : SState T m (W 0) S₀)
    (st₀' : SState T' m (X 0) S₀)
    (hrel : st₀'.L.eraseEmpty = (st₀.L.pullback (AnalyticMap.restrictMap h (X 0) (W 0) (hXW 0))
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh (X 0) (W 0) (hXW 0))).eraseEmpty) :
    ∀ j (hj : j ≤ r) (hjS : j ≤ S₀),
      (sepDescentAux hT' bo hcomp hidN hm X hX r hXsub S₀ st₀' j hj hjS).L.eraseEmpty =
        ((sepDescentAux hT bo hcomp hidN hm W hW r hWsub S₀ st₀ j hj hjS).L.pullback
          (AnalyticMap.restrictMap h (X j) (W j) (hXW j))
          (AnalyticMap.isLocalDiffeomorph_restrictMap hh (X j) (W j) (hXW j))).eraseEmpty
  | 0, _, _ => hrel
  | j + 1, hj, hjS =>
    SState.sepLink_rel hT bo hcomp hidN hm h hh hT'eq hT' (hXW j)
      (sepDescentAux hT bo hcomp hidN hm W hW r hWsub S₀ st₀ j (Nat.le_of_succ_le hj)
        (Nat.le_of_succ_le hjS))
      (sepDescentAux hT' bo hcomp hidN hm X hX r hXsub S₀ st₀' j (Nat.le_of_succ_le hj)
        (Nat.le_of_succ_le hjS))
      (sepDescentAux_rel h hh hT'eq hT' W hW r hWsub X hX hXsub hXW S₀ st₀ st₀' hrel j
        (Nat.le_of_succ_le hj) (Nat.le_of_succ_le hjS))
      (hW (j + 1)) (hWsub j hj) (hX (j + 1)) (hXsub j hj) (hXW (j + 1)) (by omega)

include hT bo hcomp hidN st3 hm in
/-- **Commutation with local analytic isomorphisms for the continuation**: two continuations by the
separation and monomial steps, over `N` and over `M`, along a local analytic isomorphism `h` with
`h(X j) ⊆ W j`, from states of the first step whose lists with empty blow-ups deleted are related
by pull-back along `h`, end in states whose lists are so related. Both continuations run the same
number `t` of links, so no offset of bounds is needed. -/
theorem step23Aux_rel (t : ℕ) (ht : 1 ≤ t) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω h)
    {T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) N}
    (hT'eq : T' = T.pullback h hh) (hT' : AnalyticTriple.BMOClass m T') (W : ℕ → Opens M)
    (hW : ∀ k, IsCompact (closure (W k : Set M)))
    (hWsub : ∀ k, k < t → closure (W (k + 1) : Set M) ⊆ W k) (X : ℕ → Opens N)
    (hX : ∀ k, IsCompact (closure (X k : Set N)))
    (hXsub : ∀ k, k < t → closure (X (k + 1) : Set N) ⊆ X k)
    (hXW : ∀ j, ⇑h '' (X j : Set N) ⊆ W j) (st₀ : BState T m (W 0) (t - 1))
    (st₀' : BState T' m (X 0) (t - 1))
    (hrel : st₀'.L.eraseEmpty = (st₀.L.pullback (AnalyticMap.restrictMap h (X 0) (W 0) (hXW 0))
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh (X 0) (W 0) (hXW 0))).eraseEmpty) :
    (step23Aux hT' bo hcomp hidN st3 hm t ht X hX hXsub st₀').L.eraseEmpty =
      ((step23Aux hT bo hcomp hidN st3 hm t ht W hW hWsub st₀).L.pullback
        (AnalyticMap.restrictMap h (X t) (W t) (hXW t))
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh (X t) (W t) (hXW t))).eraseEmpty :=
  SState.step3Link_rel hT st3 h hh hT'eq hT' (hXW (t - 1))
    (sepDescentState hT bo hcomp hidN hm W hW t (fun k hk => hWsub k hk) (t - 1)
      (SState.ofBState T m st₀) (Nat.sub_le t 1))
    (sepDescentState hT' bo hcomp hidN hm X hX t (fun k hk => hXsub k hk) (t - 1)
      (SState.ofBState T' m st₀') (Nat.sub_le t 1))
    (sepDescentAux_rel hT bo hcomp hidN hm h hh hT'eq hT' W hW t (fun k hk => hWsub k hk) X hX
      (fun k hk => hXsub k hk) hXW (t - 1) (SState.ofBState T m st₀) (SState.ofBState T' m st₀')
      hrel (t - 1) (Nat.sub_le t 1) le_rfl)
    (hW t) (by have h := hWsub (t - 1) (by omega); rwa [Nat.sub_add_cancel ht] at h) (hX t)
    (by have h := hXsub (t - 1) (by omega); rwa [Nat.sub_add_cancel ht] at h) (hXW t)

variable (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (e : F'.ι ↪o T.F.ι) (he : ∀ i, T.F.hyp (e i) = F'.hyp i)
  (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅)
  (hT' : AnalyticTriple.BMOClass m (BDan.withBoundary T F' hsnc'))

include hT bo hcomp hidN hm he he' hT' in
/-- The descent of the separation step is indifferent to empty boundary members link by link. -/
theorem sepDescentAux_L_indiff (W : ℕ → Opens M) (hW : ∀ k, IsCompact (closure (W k : Set M)))
    (r : ℕ) (hWsub : ∀ k, k < r → closure (W (k + 1) : Set M) ⊆ W k) (S₀ : ℕ)
    (st₀ : SState T m (W 0) S₀) (st₀' : SState (BDan.withBoundary T F' hsnc') m (W 0) S₀)
    (hL : st₀.L = st₀'.L) :
    ∀ j (hj : j ≤ r) (hjS : j ≤ S₀),
      (sepDescentAux hT bo hcomp hidN hm W hW r hWsub S₀ st₀ j hj hjS).L =
        (sepDescentAux hT' bo hcomp hidN hm W hW r hWsub S₀ st₀' j hj hjS).L
  | 0, _, _ => hL
  | j + 1, hj, hjS =>
    SState.sepLink_L_indiff hT bo hcomp hidN hm F' hsnc' e he he' hT'
      (sepDescentAux hT bo hcomp hidN hm W hW r hWsub S₀ st₀ j (Nat.le_of_succ_le hj)
        (Nat.le_of_succ_le hjS))
      (sepDescentAux hT' bo hcomp hidN hm W hW r hWsub S₀ st₀' j (Nat.le_of_succ_le hj)
        (Nat.le_of_succ_le hjS))
      (sepDescentAux_L_indiff W hW r hWsub S₀ st₀ st₀' hL j (Nat.le_of_succ_le hj)
        (Nat.le_of_succ_le hjS))
      (hW (j + 1)) (hWsub j hj) (by omega)

include hT bo hcomp hidN st3 hm he he' hT' in
/-- **Indifference to empty boundary members for the continuation**: two continuations along the
same chain from states with the same list, for `T` and for `T` with its boundary replaced by an
empty extension, have the same list. -/
theorem step23Aux_L_indiff (t : ℕ) (ht : 1 ≤ t) (W : ℕ → Opens M)
    (hW : ∀ k, IsCompact (closure (W k : Set M)))
    (hWsub : ∀ k, k < t → closure (W (k + 1) : Set M) ⊆ W k) (st₀ : BState T m (W 0) (t - 1))
    (st₀' : BState (BDan.withBoundary T F' hsnc') m (W 0) (t - 1)) (hL : st₀.L = st₀'.L) :
    (step23Aux hT bo hcomp hidN st3 hm t ht W hW hWsub st₀).L =
      (step23Aux hT' bo hcomp hidN st3 hm t ht W hW hWsub st₀').L :=
  SState.step3Link_L_indiff hT st3 F' hsnc' e he he' hT'
    (sepDescentState hT bo hcomp hidN hm W hW t (fun k hk => hWsub k hk) (t - 1)
      (SState.ofBState T m st₀) (Nat.sub_le t 1))
    (sepDescentState hT' bo hcomp hidN hm W hW t (fun k hk => hWsub k hk) (t - 1)
      (SState.ofBState (BDan.withBoundary T F' hsnc') m st₀') (Nat.sub_le t 1))
    (sepDescentAux_L_indiff hT bo hcomp hidN hm F' hsnc' e he he' hT' W hW t
      (fun k hk => hWsub k hk) (t - 1) (SState.ofBState T m st₀)
      (SState.ofBState (BDan.withBoundary T F' hsnc') m st₀') hL (t - 1) (Nat.sub_le t 1) le_rfl)
    (hW t) (by have h := hWsub (t - 1) (by omega); rwa [Nat.sub_add_cancel ht] at h)

end Chain

end Hironaka.Manifold.BMO

end
