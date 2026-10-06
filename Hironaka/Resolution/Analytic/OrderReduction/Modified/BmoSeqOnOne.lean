/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.BmoSeqOn
public import Hironaka.Resolution.Analytic.OrderReduction.Stage.AllNFam
public import Hironaka.Resolution.Analytic.OrderReduction.Stage.Concrete
public import Hironaka.Resolution.Analytic.Functor.ChainClosedEmbeddingZero
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1Comap
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1Measure
import Hironaka.Resolution.Analytic.OrderReduction.ClosedEmbeddingPrep
import Hironaka.Resolution.Analytic.OrderReduction.FamilyIndependence
import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClauseClosedEmbedding
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bFunctor
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepAAlign
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepATransport
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepCExit
import Hironaka.Resolution.Analytic.OrderReduction.Step21ErasePrep
import Hironaka.Resolution.Analytic.OrderReduction.Step21Functoriality
import Hironaka.Resolution.Analytic.Principalization.ShrinkAppendLemmas
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Theorem 107 (3) at the mark `1`: the marked order reduction of an ideal of order `≤ 1`

Clause (3) of [Kol07, Theorem 107] says that the marked order reduction `BMO_{n,m}(X, I, m, ∅)`
is the order reduction `BO_{n,m}(X, I, ∅)` when `m` is the maximal order of `I`. This module
proves it for the library's three-step construction of `BMO_{n,m}` (`bmoSeqOn`, the chain of
[Kol07, 111]) at the mark `1` and for an ideal sheaf of order `≤ 1` with the empty boundary, the
case the commutation with closed embeddings uses ([Kol07, 108]: every local equation of the
submanifold lies in `I`, so the maximal order is `1`):

* with the empty boundary the nonmonomial part of the ideal is the ideal itself
  (`nonmonomialTriple_eq_self_of_isEmpty`), so the bound of the rounds on the nonmonomial part is
  `D ≤ 1`, and at the threshold `t = m = 1` the first step runs `D` links: none when `D = 0`, one
  round of `BO_{n,1}` when `D = 1`;
* after the first step the controlled transform of `(I, 1)` has order `< 1` at every point of the
  last stage (`descentState_ord_lt_one`): with no link it is the restriction of `I`, of order `0`;
  with one link it is the last marked transform of the round, of order `< 1` by
  [Kol07, Theorem 103 (1)], carried along the corestricted lift (`induced_pullback`);
* the separation step has `t − 1 = 0` links, and the monomial step is idle: the monomial part of
  an ideal of order `< 1` has order `< 1` (`le_monomialPart`, `ord_anti`), the value of the
  procedure is a sequence of order `≥ 1` for it without empty centres, hence empty
  (`MonomialStep3Fam.seqOn_eq_nil`), and a link with the empty value restricts the list
  (`SState.step3Link_L_of_ord_lt`);
* the value of `BMO_{n,1}` on `U` is therefore the value of the first step on `U`
  (`bmoSeqOn_one_eq_stepAFamOn`), which is the value of `BO_{n,1}` on `U`
  (`descentState_eraseEmpty_pullback_eq_bo_one`: with no link both are empty; with one link the
  round read on the second chain open and restricted to `U` is the value on `U` by the commutation
  of `BO_{n,1}` with the inclusion of the outer open and its compatibility under restriction, the
  argument of `composeOn_eq_of_firstList_eq_nil`) — `bmoSeqOn_one_eq_bo_one`.

Consequence: the marked family of the library's tower at the mark `1` commutes with closed
embeddings of hypersurfaces of empty divisor through the marked family one dimension down
(`concreteBMOanFam_commutesWithClosedEmbeddings_one`, [Kol07, Claim 71.2] for hypersurfaces as
in [Kol07, 108]: Theorem 103 (3), `BOanFamAllOf_commutesWithClosedEmbeddingsOfEmptyDivisorFam`,
and Theorem 107 (3) above), and, by the chaining along flags
(`BMOanFam_commutesWithClosedEmbeddingsOfEmptyDivisorFam_all`), in every codimension
(`concreteBMOanFam_commutesWithClosedEmbeddings`).
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace Hironaka.Manifold Hironaka.Local
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

open Hironaka.Manifold.BMO Hironaka.Manifold.BMOmod

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-! ### The empty boundary -/

/-- With the empty boundary the nonmonomial triple is the triple itself: the monomial part of the
ideal is the unit ideal (`monomialPart_eq_top_of_activeMembers_eq_empty`, no member), so the
nonmonomial part is the ideal (`nonmonomialTriple_I_eq_of_monomialPart_eq_top`). -/
theorem nonmonomialTriple_eq_self_of_isEmpty
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) [hε : IsEmpty T.F.ι] :
    nonmonomialTriple T = T :=
  AnalyticTriple.ext'
    (nonmonomialTriple_I_eq_of_monomialPart_eq_top T
      (monomialPart_eq_top_of_activeMembers_eq_empty T
        (Set.eq_empty_of_forall_notMem fun j _ => (hε.false j).elim))) rfl

/-- The order of the ideal of the nonmonomial triple of a triple with empty boundary is the order
of the ideal. -/
theorem nonmonomialTriple_I_ord_of_isEmpty
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) [IsEmpty T.F.ι] (x : M) :
    (nonmonomialTriple T).I.ord x = T.I.ord x := by
  rw [nonmonomialTriple_eq_self_of_isEmpty T]

/-! ### The monomial step is idle on an ideal of order `< 1` -/

/-- **The empty-value lemma for the monomial procedure** ([Kol07, Definition 66 (4′)] with
[Kol07, 32]): on an open where the monomial part of the ideal has order `< m` everywhere the value
of the procedure is the empty list, since a first centre would lie where that order is `≥ m` and
be nonempty. The counterpart of `BOanFam.seqOn_eq_nil`. -/
theorem BMO.MonomialStep3Fam.seqOn_eq_nil {m : ℕ} (st3 : MonomialStep3Fam.{u} 𝕜 n m)
    (S : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hS : AnalyticTriple.BMOClass m S) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (hlt : ∀ x ∈ (U : Set M), (monomialPart S.F S.isSnc S.I).ord x < (m : ℕ∞)) :
    (st3.functor.fam S hS).seqOn U hU = AnalyticManifold.BlowUpSequence.nil _ := by
  have hord := st3.isOfOrderGe S hS U hU
  have hne := (st3.functor.fam S hS).noEmptyCenters U hU
  generalize (st3.functor.fam S hS).seqOn U hU = L at hord hne ⊢
  cases L with
  | nil => rfl
  | cons hY rest =>
    exfalso
    obtain ⟨hYne, -⟩ := (AnalyticManifold.BlowUpSequence.noEmptyCenters_cons_iff hY rest).mp hne
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hYne
    have hmem : y ∈
        ((AnalyticManifold.BlowUpSequence.cons hY rest).toSuccession.center ⟨0,
            Nat.succ_pos _⟩).support := by
      change y ∈ hY.idealSheaf.support
      rw [hY.cosupport_idealSheaf]
      exact hy
    have h := (hord ⟨0, Nat.succ_pos _⟩).2 y hmem
    have h2 := ordAlongIdeal_le_ord_of_mem_support _
      (monomialPart (S.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F
        (S.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc
        (S.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I) hmem
    have h3 : (monomialPart (S.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F
        (S.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc
        (S.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I).ord y < (m : ℕ∞) := by
      change (monomialPart (S.F.comap (M.inclusion U))
        (HypersurfaceFamily.isSnc_comap S.isSnc (M.inclusion U) (isLocalDiffeomorph_inclusion M U))
        (S.I.pullback (M.inclusion U) (M.inclusion U).contMDiff)).ord y < _
      rw [monomialPart_comap (M.inclusion U) (isLocalDiffeomorph_inclusion M U) S.F S.isSnc S.I]
      change ((monomialPart S.F S.isSnc S.I).pullback _ _).ord y < _
      rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
        (isLocalDiffeomorph_inclusion _ _ y)]
      exact hlt y.1 y.2
    exact absurd (h.trans h2) (not_le.mpr h3)


/-! ### The monomial link with an empty value restricts the list -/

section Step3Idle

variable {T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M}
  (hT : AnalyticTriple.BMOClass 1 T) (st3 : MonomialStep3Fam.{u} 𝕜 n 1)
  {W : Opens M} (st : SState T 1 W 0) {V : Opens M} (hV : IsCompact (closure (V : Set M)))
  (hVW : closure (V : Set M) ⊆ W)

/-- When the controlled transform of `(𝓘, 1)` at the exit state has order `< 1` at every point, the
value of the monomial procedure is empty: the monomial part of the induced ideal contains it
(`le_monomialPart`), so has order `< 1` too (`ord_anti`), and `MonomialStep3Fam.seqOn_eq_nil`. -/
theorem BMO.SState.step3Value_eq_nil_of_ord_lt
    (hlt : ∀ x, (ChainState.inducedTriple T 1 st.toChainState).I.ord x < (1 : ℕ∞)) :
    st.step3Value hT st3 hV hVW = AnalyticManifold.BlowUpSequence.nil _ :=
  BMO.MonomialStep3Fam.seqOn_eq_nil st3 (ChainState.inducedTriple T 1 st.toChainState)
    (bmoClass_inducedTriple T 1 hT st.toChainState) (ChainState.readOpen T 1 st.toChainState hVW)
    (ChainState.isCompact_closure_readOpen T 1 st.toChainState hV hVW) fun x _ =>
      lt_of_le_of_lt (IdealSheaf.ord_anti (BMO.le_monomialPart
        (ChainState.inducedTriple T 1 st.toChainState).F
        (ChainState.inducedTriple T 1 st.toChainState).isSnc
        (ChainState.inducedTriple T 1 st.toChainState).I) x) (hlt x)

/-- A monomial link with an empty value restricts the list to `V` (`shrinkAppend` with the empty
list: `pullback_nil`, `concat_nil_right`). -/
theorem BMO.SState.step3Link_L_of_ord_lt
    (hlt : ∀ x, (ChainState.inducedTriple T 1 st.toChainState).I.ord x < (1 : ℕ∞)) :
    (st.step3Link hT st3 hV hVW).L =
      st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
        (isLocalDiffeomorph_restrictLE _) := by
  rw [st.step3Link_L hT st3 hV hVW, st.step3Value_eq_nil_of_ord_lt hT st3 hV hVW hlt]
  unfold AnalyticManifold.BlowUpSequence.shrinkAppend
  rw [AnalyticManifold.BlowUpSequence.pullback_nil,
    AnalyticManifold.BlowUpSequence.concat_nil_right]

end Step3Idle

/-! ### The first step at the threshold `1` on an ideal of order `≤ 1`: no link or one round -/

section Descent

variable (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) [hε : IsEmpty T.F.ι]
  (hT : AnalyticTriple.BMOClass 1 T)

section OneLink

variable {W₀ : Opens M}

/-- With the empty boundary, the nonmonomial triple of the induced triple of the initial state (the
triple restricted to the first chain open) is that triple itself. -/
theorem nonmonomialTriple_inducedTriple_initialOf {D : ℕ}
    (hD : ∀ x ∈ (W₀ : Set M), (nonmonomialTriple T).I.ord x ≤ (D : ℕ∞)) :
    nonmonomialTriple
        (ChainState.inducedTriple T 1 (BState.initialOf T 1 hcomp D hD).toChainState) =
      ChainState.inducedTriple T 1 (BState.initialOf T 1 hcomp D hD).toChainState := by
  have e : ChainState.inducedTriple T 1 (BState.initialOf T 1 hcomp D hD).toChainState =
      T.pullback (M.inclusion W₀) (isLocalDiffeomorph_inclusion M W₀) :=
    AnalyticTriple.induced_nil _ 1 _
  rw [e]
  have : IsEmpty (T.pullback (M.inclusion W₀) (isLocalDiffeomorph_inclusion M W₀)).F.ι := hε
  exact nonmonomialTriple_eq_self_of_isEmpty _

variable {V : Opens M} (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W₀)

include hid in
/-- **After one round of `BO_{n,1}` from the initial state the controlled transform of `(𝓘, 1)` has
order `< 1` at every point of the last stage**: Theorem 103 (1) for the round (`ord_lt`), on the
triple restricted to the reading open, carried along the corestricted lift (`induced_pullback`)
and through the concatenation (`pred_induced_concat`), as in `SState.step3Link_ord_lt`. -/
theorem inducedTriple_descentLink_initialOf_ord_lt
    (hD : ∀ x ∈ (W₀ : Set M), (nonmonomialTriple T).I.ord x ≤ ((1 : ℕ) : ℕ∞)) :
    ∀ y, (ChainState.inducedTriple T 1
      ((BState.initialOf T 1 hcomp 1 hD).descentLink hcomp bo hid hV hVW hT le_rfl
        le_rfl).toChainState).I.ord y < (1 : ℕ∞) := by
  set st := BState.initialOf T 1 hcomp 1 hD with hst
  have hL₀' := st.roundValue_isOfOrderGe hcomp bo hid hV hVW hT le_rfl le_rfl
  have hL₁ := st.shrink_hge hVW
  have h₂ := AnalyticTriple.isOfOrderGe_pullback _ 1 (st.roundValue bo hV hVW hT le_rfl) hL₀'
    (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
      (isLocalDiffeomorph_restrictLE _)) (st.L.isLocalDiffeomorph_liftCorestrict _ _)
  have e := st.inducedTriple_pullback_liftCorestrict hVW
  have hL₂ : ((st.roundValue bo hV hVW hT le_rfl).pullback
      (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
        (isLocalDiffeomorph_restrictLE _))
      (st.L.isLocalDiffeomorph_liftCorestrict _ _)).toSuccession.IsOfOrderGe
      ((T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).induced 1
        (st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _)) hL₁).I 1
      ((T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).induced 1
        (st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _)) hL₁).F.idealSheaf := by
    rw [← e]; exact h₂
  have hmain : ∀ z, ((((T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).induced 1
      (st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
        (isLocalDiffeomorph_restrictLE _)) hL₁).induced 1
      ((st.roundValue bo hV hVW hT le_rfl).pullback
        (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _))
        (st.L.isLocalDiffeomorph_liftCorestrict _ _)) hL₂).I).ord z < (1 : ℕ∞) := by
    rw [← AnalyticTriple.induced_congr e 1 _ h₂ hL₂,
      ← AnalyticTriple.induced_pullback _ 1 (st.roundValue bo hV hVW hT le_rfl) hL₀'
        (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _)) (st.L.isLocalDiffeomorph_liftCorestrict _ _) h₂]
    intro z
    change (((((ChainState.inducedTriple T 1 st.toChainState).pullback
      ((st.L.stage (Fin.last _)).inclusion (st.liftOpen hVW))
      (isLocalDiffeomorph_inclusion _ _)).induced 1 (st.roundValue bo hV hVW hT le_rfl)
      hL₀')).I.pullback _ _).ord z < _
    rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _ z)]
    have hlt := (bo 1).ord_lt (nonmonomialTriple (ChainState.inducedTriple T 1 st.toChainState))
      (st.boClass_nonmonomial hT le_rfl) (st.liftOpen hVW) (st.isCompact_closure_liftOpen hV hVW)
      ((st.roundValue bo hV hVW hT le_rfl).pullbackLiftLast _ _ z)
    have hN := congrArg AnalyticTriple.I (nonmonomialTriple_inducedTriple_initialOf hcomp T hD)
    change ((st.roundValue bo hV hVW hT le_rfl).toSuccession.markedTransformSeq
      ((nonmonomialTriple (ChainState.inducedTriple T 1 st.toChainState)).I.pullback _ _) 1
      (Fin.last _)).ord _ < _ at hlt
    rw [hN] at hlt
    exact hlt
  change ∀ z, ((T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).induced 1
      ((st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
        (isLocalDiffeomorph_restrictLE _)).concat ((st.roundValue bo hV hVW hT le_rfl).pullback
          (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
            (isLocalDiffeomorph_restrictLE _)) (st.L.isLocalDiffeomorph_liftCorestrict _ _)))
      _).I.ord z < (1 : ℕ∞)
  exact AnalyticTriple.pred_induced_concat (fun S => ∀ z, S.I.ord z < (1 : ℕ∞)) _ _ _ 1 hL₁ hL₂ _
    hmain

include hid in
/-- **The value of one round of `BO_{n,1}` from the initial state, restricted to `U ⊆ V` and
cleaned, is the value of `BO_{n,1}` on `U`**: the round is the value of `BO_{n,1}` on the triple
restricted to `W₀`, read on the reading open, whose image under the inclusion of `W₀` is `V`
(`CommutesWithLocalIsos.seqOn_eq_of_image_eq`); the pull-backs compose to the inclusion `U ⊆ V`,
and the compatibility of the family of `BO_{n,1}` closes (the argument of
`composeOn_eq_of_firstList_eq_nil`). -/
theorem descentLink_initialOf_eraseEmpty_pullback_eq (hT₁ : AnalyticTriple.BOClass 1 T)
    (hD : ∀ x ∈ (W₀ : Set M), (nonmonomialTriple T).I.ord x ≤ ((1 : ℕ) : ℕ∞))
    {U : Opens M} (hU : IsCompact (closure (U : Set M))) (hUV : U ≤ V) :
    (((BState.initialOf T 1 hcomp 1 hD).descentLink hcomp bo hid hV hVW hT le_rfl le_rfl).L.pullback
      (M.restrictLE hUV) (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty =
      ((bo 1).functor.fam T hT₁).seqOn U hU := by
  set st := BState.initialOf T 1 hcomp 1 hD with hst
  have hVW₀ : V ≤ W₀ := ChainState.le_of_closure_subset hVW
  have hg₀ : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (M.inclusion W₀) :=
    isLocalDiffeomorph_inclusion M W₀
  have hT₁W : AnalyticTriple.BOClass 1 (T.pullback (M.inclusion W₀) hg₀) :=
    AnalyticTriple.boClass_pullback_of_isLocalDiffeomorph T _ hg₀ hT₁
  rw [st.descentLink_L hcomp bo hid hT le_rfl hV hVW le_rfl]
  unfold BState.roundValue
  -- the list of the initial state is empty: generalize it, then substitute
  have key : ∀ (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (M.restrict W₀))
      (hL : L.toSuccession.IsOfOrderGe (T.pullback (M.inclusion W₀) hg₀).I 1
        (T.pullback (M.inclusion W₀) hg₀).F.idealSheaf)
      (hD' : AnalyticTriple.BOClass 1
        (nonmonomialTriple ((T.pullback (M.inclusion W₀) hg₀).induced 1 L hL)))
      (hOc : IsCompact (closure (L.liftRange (M.restrictLE hVW₀) (isLocalDiffeomorph_restrictLE _) :
        Set (L.stage (Fin.last _))))),
      L = AnalyticManifold.BlowUpSequence.nil _ →
      ((L.shrinkAppend (M.restrictLE hVW₀) (isLocalDiffeomorph_restrictLE _)
        (((bo 1).functor.fam (nonmonomialTriple ((T.pullback (M.inclusion W₀) hg₀).induced 1 L hL))
          hD').seqOn (L.liftRange (M.restrictLE hVW₀) (isLocalDiffeomorph_restrictLE _))
            hOc)).pullback (M.restrictLE hUV) (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty =
      ((bo 1).functor.fam T hT₁).seqOn U hU := by
    intro L hL hD' hOc hnil
    subst hnil
    rw [AnalyticManifold.BlowUpSequence.shrinkAppend_nil]
    -- the functor at the induced triple of the empty list is the functor at the restricted triple
    have etri : nonmonomialTriple ((T.pullback (M.inclusion W₀) hg₀).induced 1
        (AnalyticManifold.BlowUpSequence.nil _) hL) = T.pullback (M.inclusion W₀) hg₀ := by
      rw [AnalyticTriple.induced_nil]
      have : IsEmpty (T.pullback (M.inclusion W₀) hg₀).F.ι := hε
      exact nonmonomialTriple_eq_self_of_isEmpty _
    rw [AnalyticFamilyFunctor.fam_seqOn_congr_triple (bo 1).functor etri hD' hT₁W]
    -- the reading open and its image `V`
    set O : Opens (M.restrict W₀) :=
      (AnalyticManifold.BlowUpSequence.nil (ψ₀ := ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (M.restrict W₀)).liftRange (M.restrictLE hVW₀) (isLocalDiffeomorph_restrictLE _) with hO
    have hOc' : IsCompact (closure (O : Set (M.restrict W₀))) := hOc
    have himg : ⇑(M.inclusion W₀) '' (O : Set (M.restrict W₀)) = (V : Set M) :=
      (congrArg (fun s : Set (M.restrict W₀) => (Subtype.val : M.restrict W₀ → M) '' s)
        (range_restrictLE hVW₀)).trans
        (Set.image_preimage_eq_of_subset fun x hx => ⟨⟨x, hVW₀ hx⟩, rfl⟩)
    set c : AnalyticMap (M.restrict V) ((M.restrict W₀).restrict O) :=
      (AnalyticManifold.BlowUpSequence.nil (ψ₀ := ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (M.restrict W₀)).liftCorestrict (M.restrictLE hVW₀) (isLocalDiffeomorph_restrictLE _)
      with hcdef
    have hc : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω c :=
      AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftCorestrict _ _ _
    set rm := AnalyticMap.restrictMap (M.inclusion W₀) O V himg.le with hrmdef
    have hrm : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω rm :=
      AnalyticMap.isLocalDiffeomorph_restrictMap hg₀ O V himg.le
    change (((((bo 1).functor.fam (T.pullback (M.inclusion W₀) hg₀) hT₁W).seqOn O hOc').pullback c
      hc).pullback (M.restrictLE hUV) (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty = _
    rw [AnalyticFamilyFunctor.CommutesWithLocalIsos.seqOn_eq_of_image_eq
      (bo 1).commutesWithLocalIsos hg₀ (AnalyticTriple.isPullbackOf_pullback T _ hg₀) hT₁ hT₁W hOc'
      hV himg]
    have hcr : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
        (c.comp (M.restrictLE hUV)) :=
      AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hc (isLocalDiffeomorph_restrictLE _)
    have hcomp' : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
        (rm.comp (c.comp (M.restrictLE hUV))) :=
      AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hrm hcr
    have hmap : rm.comp (c.comp (M.restrictLE hUV)) = M.restrictLE hUV :=
      ContMDiffMap.ext fun x => Subtype.ext rfl
    rw [AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _,
      AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty _ _ hcr,
      AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _,
      AnalyticManifold.BlowUpSequence.pullback_congr _ hmap hcomp'
        (isLocalDiffeomorph_restrictLE hUV),
      ((bo 1).functor.fam T hT₁).compat U V hU hV hUV]
  exact key st.L st.hge (st.boClass_nonmonomial hT le_rfl) (st.isCompact_closure_liftOpen hV hVW)
    rfl

end OneLink

section Chain

variable (W : ℕ → Opens M) (hW : ∀ k, IsCompact (closure (W k : Set M))) (r : ℕ)
  (hWsub : ∀ k, k < r → closure (W (k + 1) : Set M) ⊆ W k) (D : ℕ)
  (hD : ∀ x ∈ (W 0 : Set M), (nonmonomialTriple T).I.ord x ≤ (D : ℕ∞)) (hD1 : D ≤ 1)
  (hr : descentLength 1 D ≤ r)

include hid hD1 in
/-- **At the threshold `1` with a bound `D ≤ 1`, the controlled transform at the exit of the first
step has order `< 1` everywhere**: with `D = 0` there is no link and the induced ideal is the
restriction of `𝓘`, of order `0`; with `D = 1` there is one link,
`inducedTriple_descentLink_initialOf_ord_lt`. -/
theorem descentState_ord_lt_one :
    ∀ y, (ChainState.inducedTriple T 1
      (descentState T 1 hT bo hcomp hid 1 le_rfl le_rfl W hW r hWsub D hD hr).toChainState).I.ord
        y <
        (1 : ℕ∞) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hD1 with rfl | rfl
  · have e : ChainState.inducedTriple T 1 (BState.initialOf T 1 hcomp 0 hD).toChainState =
        T.pullback (M.inclusion (W 0)) (isLocalDiffeomorph_inclusion M (W 0)) :=
      AnalyticTriple.induced_nil _ 1 _
    have key : ∀ y : M.restrict (W 0),
        (T.pullback (M.inclusion (W 0)) (isLocalDiffeomorph_inclusion M (W 0))).I.ord y <
          (1 : ℕ∞) := by
      intro y
      change (T.I.pullback (M.inclusion (W 0)) _).ord y < _
      rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt (M.inclusion (W 0)) _ T.I
        (isLocalDiffeomorph_inclusion M (W 0) y)]
      have h := hD y.1 y.2
      rw [nonmonomialTriple_I_ord_of_isEmpty] at h
      exact lt_of_le_of_lt h (by exact_mod_cast zero_lt_one)
    intro y
    exact (congrArg (fun S : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (M.restrict (W 0)) => S.I.ord y) e).trans_lt (key y)
  · exact inducedTriple_descentLink_initialOf_ord_lt bo hcomp hid T hT (hW 1)
      (hWsub 0 (by unfold descentLength at hr; omega)) hD

include hid hD1 in
/-- **At the threshold `1` with a bound `D ≤ 1`, the value of the first step on `U` is the value of
`BO_{n,1}` on `U`**: with `D = 0` both are empty (`BOanFam.seqOn_eq_nil`: `ord 𝓘 = 0` on `U`); with
`D = 1`, `descentLink_initialOf_eraseEmpty_pullback_eq`. -/
theorem descentState_eraseEmpty_pullback_eq_bo_one (hT₁ : AnalyticTriple.BOClass 1 T) {U : Opens M}
    (hU : IsCompact (closure (U : Set M))) (hUW : U ≤ W (descentLength 1 D)) :
    ((descentState T 1 hT bo hcomp hid 1 le_rfl le_rfl W hW r hWsub D hD hr).L.pullback
      (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE hUW)).eraseEmpty =
      ((bo 1).functor.fam T hT₁).seqOn U hU := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hD1 with rfl | rfl
  · change ((AnalyticManifold.BlowUpSequence.nil _).pullback _ _).eraseEmpty = _
    rw [AnalyticManifold.BlowUpSequence.pullback_nil,
      AnalyticManifold.BlowUpSequence.eraseEmpty_nil]
    symm
    refine (bo 1).seqOn_eq_nil T hT₁ U hU fun x hx => ?_
    have h := hD x (hUW hx)
    rw [nonmonomialTriple_I_ord_of_isEmpty] at h
    exact lt_of_le_of_lt h (by exact_mod_cast zero_lt_one)
  · exact descentLink_initialOf_eraseEmpty_pullback_eq bo hcomp hid T hT (hW 1)
      (hWsub 0 (by unfold descentLength at hr; omega)) hT₁ hD hU hUW

end Chain

end Descent

/-! ### Theorem 107 (3) at the mark `1` for the three-step construction -/

section Main

variable (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hidN : NonmonomialTransformIdentityMod.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (st3 : MonomialStep3Fam.{u} 𝕜 n 1)
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) [hε : IsEmpty T.F.ι]
  (hT : AnalyticTriple.BMOClass 1 T) (hord : ∀ x, T.I.ord x ≤ (1 : ℕ∞))
  (U : Opens M) (hU : IsCompact (closure (U : Set M)))

include hord in
/-- With the empty boundary and `ord 𝓘 ≤ 1`, the bound of the rounds is at most `1`. -/
theorem stepABound_le_one : stepABound T U hU ≤ 1 := by
  have h : (roundOrderOn T (stepAOuter U hU) : ℕ∞) ≤ ((1 : ℕ) : ℕ∞) := by
    rw [coe_roundOrderOn T _ (isCompact_closure_stepAOuter U hU)]
    exact iSup_le fun x => by
      have hx := nonmonomialTriple_I_ord_of_isEmpty T x.1
      rw [nonmonomialTriple_I] at hx
      rw [hx]
      exact hord x.1
  exact_mod_cast h

include hid hord in
/-- After the first step at the threshold `1` the controlled transform of `(𝓘, 1)` has order `< 1`
at every point of the last stage. -/
theorem stepAChainState_ord_lt_one :
    ∀ y, (ChainState.inducedTriple T 1
      (stepAChainState T 1 hT bo hcomp hid 1 hT.1 le_rfl U hU).toChainState).I.ord y < (1 : ℕ∞) :=
  descentState_ord_lt_one bo hcomp hid T hT _ _ _ _ _ _ (stepABound_le_one T hord U hU) _

include hid hord in
/-- **The value of the first step on `U` at the threshold `1` is the value of `BO_{n,1}` on
`U`.** -/
theorem stepAFamOn_one_eq_bo_one (hT₁ : AnalyticTriple.BOClass 1 T) :
    stepAFamOn T 1 hT bo hcomp hid 1 hT.1 le_rfl U hU = ((bo 1).functor.fam T hT₁).seqOn U hU :=
  descentState_eraseEmpty_pullback_eq_bo_one bo hcomp hid T hT _ _ _ _ _ _
    (stepABound_le_one T hord U hU) _ hT₁ hU _

include hid hord in
/-- **Theorem 107 (3) at the mark `1`** ([Kol07, Theorem 107 (3)]: `BMO_{n,m}(X, I, m, ∅) =
BO_{n,m}(X, I, ∅)` when `m = max-ord I`), for the three-step construction: on a triple with the
empty boundary and `ord 𝓘 ≤ 1`, the value of `BMO_{n,1}` on `U` is the value of `BO_{n,1}` on `U`.
The separation step has `1 − 1 = 0` links; the monomial link is idle since the controlled transform
already has order `< 1` (`stepAChainState_ord_lt_one`, `SState.step3Link_L_of_ord_lt`); the terminal
list is the first step's list restricted, so the value is the first step's value
(`stepAFamOn_one_eq_bo_one`). -/
theorem bmoSeqOn_one_eq_bo_one (hT₁ : AnalyticTriple.BOClass 1 T) :
    bmoSeqOn T 1 hT bo hcomp hid hidN st3 U hU = ((bo 1).functor.fam T hT₁).seqOn U hU := by
  have hlt := stepAChainState_ord_lt_one bo hcomp hid T hT hord U hU
  have hVW₁ : closure (step2ChainOpens T 1 U hU 1 : Set M) ⊆ step2ChainOpens T 1 U hU 0 :=
    closure_step2ChainOpens_succ_subset T 1 U hU 0
  have hL : (step23ChainState T 1 hT bo hcomp hid hidN st3 1 hT.1 le_rfl U hU).L =
      (stepAChainState T 1 hT bo hcomp hid 1 hT.1 le_rfl U hU).L.pullback
        (M.restrictLE (ChainState.le_of_closure_subset hVW₁)) (isLocalDiffeomorph_restrictLE _) :=
    SState.step3Link_L_of_ord_lt hT st3
      (sepDescentState hT bo hcomp hidN hT.1 (step2ChainOpens T 1 U hU)
        (isCompact_closure_step2ChainOpens T 1 U hU) 1
        (fun k _ => closure_step2ChainOpens_succ_subset T 1 U hU k) (1 - 1)
        (SState.ofBState T 1 (stepAExitState T 1 hT bo hcomp hid 1 hT.1 le_rfl U hU))
        (Nat.sub_le 1 1))
      (isCompact_closure_step2ChainOpens T 1 U hU 1) hVW₁ hlt
  change ((step23ChainState T 1 hT bo hcomp hid hidN st3 1 hT.1 le_rfl U hU).L.pullback
    (M.restrictLE (le_step23ChainOpen T 1 U hU)) (isLocalDiffeomorph_restrictLE _)).eraseEmpty = _
  rw [hL]
  have hcomp' : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      ((M.restrictLE (ChainState.le_of_closure_subset hVW₁)).comp
        (M.restrictLE (le_step23ChainOpen T 1 U hU))) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp (isLocalDiffeomorph_restrictLE _)
      (isLocalDiffeomorph_restrictLE _)
  have hmap : (M.restrictLE (ChainState.le_of_closure_subset hVW₁)).comp
        (M.restrictLE (le_step23ChainOpen T 1 U hU)) =
      M.restrictLE (le_stepAChainOpens U hU (stepALinks T 1 U hU)) :=
    ContMDiffMap.ext fun x => Subtype.ext rfl
  refine (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
    (AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _)).trans ?_
  refine (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
    (AnalyticManifold.BlowUpSequence.pullback_congr _ hmap hcomp'
      (isLocalDiffeomorph_restrictLE _))).trans ?_
  exact stepAFamOn_one_eq_bo_one bo hcomp hid T hT hord U hU hT₁

end Main

/-! ### The concrete marked tower commutes with closed embeddings of empty divisor -/

section Concrete

variable (𝕜 : Type) [RCLike 𝕜]

/-- Theorem 107 (3) at the mark `1` for the library's tower: on a triple with the empty boundary and
`ord 𝓘 ≤ 1`, the value of `concreteBMOanFam 𝕜 n` is the value of `concreteBOanFam 𝕜 n 1`. In
dimension `0` both are the trivial functor. -/
theorem concreteBMOanFam_seqOn_eq_concreteBOanFam_one (n : ℕ)
    {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) [IsEmpty T.F.ι]
    (hT : AnalyticTriple.BMOClass 1 T) (hT₁ : AnalyticTriple.BOClass 1 T)
    (hord : ∀ x, T.I.ord x ≤ (1 : ℕ∞)) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (((concreteBMOanFam.{u} 𝕜 n).functor.fam T hT).seqOn U hU) =
      ((concreteBOanFam.{u} 𝕜 n 1).functor.fam T hT₁).seqOn U hU := by
  cases n with
  | zero => rfl
  | succ n =>
    exact bmoSeqOn_one_eq_bo_one (BOanFamAllOf 𝕜 (concreteTheorem107FamStar 𝕜) (n + 1))
      BMOmod.nonmonomialComap_inhabitant
      (BMOmod.nonmonomialTransformIdentity_inhabitant (ContinuousLinearEquiv.refl 𝕜 _))
      (BMOmod.nonmonomialTransformIdentityMod_inhabitant (ContinuousLinearEquiv.refl 𝕜 _))
      (BMO.monomialStep3Fam 𝕜 (n + 1) 1) T hT hord U hU hT₁

/-- **[Kol07, Claim 71.2] for hypersurfaces** ([Kol07, 108]): the marked family of the tower in
dimension `n + 1` at the mark `1` commutes with closed embeddings of hypersurfaces of empty divisor
through the marked family in dimension `n`: the ideal `𝓘 ⊇ I_S` has order `≤ 1`
(`ord_le_one_of_idealSheaf_le`), so `BMO_{n+1,1}` agrees with `BO_{n+1,1}` on it
(`concreteBMOanFam_seqOn_eq_concreteBOanFam_one`, Theorem 107 (3)), and `BO_{n+1,1}` is the
push-forward of `BMO_{n,1}` (`BOanFamAllOf_commutesWithClosedEmbeddingsOfEmptyDivisorFam`,
Theorem 103 (3)). -/
theorem concreteBMOanFam_commutesWithClosedEmbeddings_one (n : ℕ) :
    (concreteBMOanFam.{u} 𝕜 (n + 1)).functor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := 1)
      (concreteBMOanFam.{u} 𝕜 n).functor := by
  intro M S hS I hI J hJ hle hJI hT hT' U hU
  subst hJI
  have hT₁ := AnalyticTriple.boClass_one_of_idealSheaf_le hS I hI hle
  have h103 := BOanFamAllOf_commutesWithClosedEmbeddingsOfEmptyDivisorFam 𝕜
    (concreteTheorem107FamStar 𝕜) n hS I hI _ hJ hle rfl hT₁ hT' U hU
  have : IsEmpty (⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩ :
      AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n + 1) → 𝕜)) M).F.ι :=
    inferInstanceAs (IsEmpty PEmpty)
  rw [concreteBMOanFam_seqOn_eq_concreteBOanFam_one 𝕜 (n + 1) _ hT hT₁
    (hS.ord_le_one_of_idealSheaf_le I hle) U hU]
  exact h103

/-- **[Kol07, Claim 71.2], [Kol07, Theorem 35 (5)] for the concrete marked tower**: the marked order
reduction at the mark `1` in dimension `n` commutes with closed embeddings of empty divisor in every
codimension `s`, through the one in dimension `n − s`: the hypersurface case
(`concreteBMOanFam_commutesWithClosedEmbeddings_one`) chained along flags
(`BMOanFam_commutesWithClosedEmbeddingsOfEmptyDivisorFam_all`, [Kol07, 108]). -/
theorem concreteBMOanFam_commutesWithClosedEmbeddings (n s : ℕ) :
    (concreteBMOanFam.{u} 𝕜 n).functor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s)
      (concreteBMOanFam.{u} 𝕜 (n - s)).functor :=
  BMOanFam_commutesWithClosedEmbeddingsOfEmptyDivisorFam_all (concreteBMOanFam.{u} 𝕜)
    (fun m hm => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
      exact concreteBMOanFam_commutesWithClosedEmbeddings_one 𝕜 k) n s

end Concrete

end Hironaka.Manifold

end

end
