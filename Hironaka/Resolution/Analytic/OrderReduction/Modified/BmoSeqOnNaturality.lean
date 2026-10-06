/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.BmoSeqOn
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepAComm
public import Hironaka.Resolution.Analytic.OrderReduction.BDIndiff
public import Hironaka.Resolution.Analytic.OrderReduction.ChainIndep
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step23Naturality
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepAAlign
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepAIndiff
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The naturality of the sequence over an open: compatibility, local isomorphisms, indifference

Beyond the order and erasure facts, the structure `BMOanFam` reads three properties of the
sequence `bmoSeqOn` over a relatively compact open:

* **compatibility** (`CompatibleFamily.compat`): the sequence over `U ≤ V` is the sequence over `V`
  restricted to `U` and cleaned of empty blow-ups ([Wlo09, Theorem 2.0.3 (4)],
  [Wlo09, Definition 3.2.6]);
* **commutation with local analytic isomorphisms** (`CommutesWithLocalIsos`): for a pull-back `T'`
  of the triple along a local analytic isomorphism `g`, the sequence over `U'` is the sequence over
  `g(U')` pulled back along `g|_{U'}` and cleaned ([Kol07, Theorem 107 (2)], [Kol07, 34.1]);
* **indifference to empty boundary members** (`IndifferentToEmptyMembers`): replacing the boundary
  by an empty extension does not change the sequence (the counterpart, for boundary members, of
  [Kol07, 32]).

The substance is the alignment of two runs of the three steps, the argument behind the second
condition of [Kol07, 34.1]. For the first step it is made by a **virtual descent** over a pair of
opens: a chain which maps into the canonical chains of both opens link by link, on which a third
run is aligned with each of the two real runs (`descentStateAux_rel`). Here the virtual run is
continued through the separation and monomial steps (`step23Aux_rel`, `step23Aux_L_indiff`):

* **compatibility.** For `U ≤ V` the virtual descent of the first step runs over the join chain
  `stepAJoin U hU V hV` from the larger of the two bounds. It is continued along `bmoJoinCont`: the
  exit open of the join descent, then the shrinkings of `closure U` inside it met with both
  canonical continuation chains, so that it maps into each of them link by link; `step23Aux_rel`
  along the identity carries the alignment to the terminal states (`bmoJoinTerminal_rel_left`,
  `bmoJoinTerminal_rel_right`). Both real sequences are then read off the one virtual terminal
  state on `U` (`valueOn_eq_of_rel_id`), and `valueOn_restrict`, the compatibility for one
  terminal state, closes.
* **local isomorphisms.** The same over the source manifold, with the pre-join chain `preJoin` of
  the pair `U' ⊆ N`, `g(U') ⊆ M` for the pulled-back triple, continued along `bmoPreJoinCont` (met
  with the canonical continuation of `U'` and the `g`-preimage of that of `g(U')`); the alignments
  along the identity (`bmoPreJoinTerminal_rel_left`) and along `g` (`bmoPreJoinTerminal_rel_right`,
  the triple of the virtual run being the pulled-back triple by `IsPullbackOf.eq`), then
  `valueOn_eq_of_rel_id` and `valueOn_pullback_of_rel'`.
* **indifference.** The canonical chains of `T` and of the boundary-extended triple coincide, the
  bound being read on the nonmonomial ideal, which does not see the empty members
  (`step2ChainOpens_withBoundary`, from `roundOrderOn_withBoundary`); along the common chain from
  the common bound the two descents have the same lists (`descentStateAux_L_indiff`), and so do the
  two continuations (`step23Aux_L_indiff`). `bmoTerminal_L_indiff` states this as a heterogeneous
  equality across the propositionally equal chains, which the value discharges by substituting the
  terminal open.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-! ### Three more transports of the value -/

namespace TerminalState

open _root_.Manifold

variable {T : AnalyticTriple ψ₀ M} {m : ℕ}

/-- The value on a smaller open is the value on the larger open restricted and cleaned: the
compatibility for one terminal state (`pullback_comp`, `eraseEmpty_pullback_eraseEmpty`). -/
theorem valueOn_restrict {W V U : Opens M} (st : TerminalState T m W) (hVW : V ≤ W) (hUV : U ≤ V) :
    st.valueOn (hUV.trans hVW) =
      ((st.valueOn hVW).pullback (M.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty := by
  unfold valueOn
  have hc : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ((M.restrictLE hVW).comp (M.restrictLE hUV)) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp (isLocalDiffeomorph_restrictLE hVW)
      (isLocalDiffeomorph_restrictLE hUV)
  rw [AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
      AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _]
  exact congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
    (AnalyticManifold.BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ =>
        Subtype.ext rfl) _ _)

/-- The identity form of `valueOn_pullback_of_rel`: a terminal state for the triple pulled back
along the identity, whose cleaned list is the cleaned pull-back of the list of a terminal state
along the inclusion `W' ⊆ W`, has the same value on every `U' ≤ W'`: the inclusion composed with
the restriction to `U'` is the restriction to `U'` (`pullback_comp`, `pullback_congr`,
`eraseEmpty_pullback_eraseEmpty`). -/
theorem valueOn_eq_of_rel_id {W W' : Opens M} (st : TerminalState T m W)
    (st' : TerminalState (T.pullback ContMDiffMap.id
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)) m W')
    (hW'W : ⇑(ContMDiffMap.id : AnalyticMap M M) '' (W' : Set M) ⊆ W)
    (hrel : st'.L.eraseEmpty = (st.L.pullback (AnalyticMap.restrictMap ContMDiffMap.id W' W hW'W)
      (AnalyticMap.isLocalDiffeomorph_restrictMap
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) W' W
        hW'W)).eraseEmpty)
    {U' : Opens M} (hU'W' : U' ≤ W') (hU'W : U' ≤ W) : st'.valueOn hU'W' = st.valueOn hU'W := by
  unfold valueOn
  have hc : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      ((AnalyticMap.restrictMap ContMDiffMap.id W' W hW'W).comp (M.restrictLE hU'W')) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
      (AnalyticMap.isLocalDiffeomorph_restrictMap
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) W' W hW'W)
      (isLocalDiffeomorph_restrictLE hU'W')
  rw [← AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty st'.L, hrel,
    AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
        AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _]
  exact congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
    (AnalyticManifold.BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ =>
        Subtype.ext rfl) _ _)

/-- `valueOn_pullback_of_rel` for any triple equal to the pull-back, the form in which the alignment
facts `descentStateAux_rel` and `step23Aux_rel` are stated. -/
theorem valueOn_pullback_of_rel' {N : AnalyticManifold.{u} 𝕜 E} (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) {T' : AnalyticTriple ψ₀ N}
    (hT'eq : T' = T.pullback g hg) {W : Opens M} {W' : Opens N}
    (hWW' : ⇑g '' (W' : Set N) ⊆ W) (st : TerminalState T m W) (st' : TerminalState T' m W')
    (hrel : st'.L.eraseEmpty = (st.L.pullback (AnalyticMap.restrictMap g W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hg W' W hWW')).eraseEmpty)
    {U' : Opens N} (hU'W' : U' ≤ W') (hU'W : AnalyticMap.imageOpens g hg U' ≤ W) :
    st'.valueOn hU'W' =
      ((st.valueOn hU'W).pullback
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
          Set.Subset.rfl)).eraseEmpty := by
  subst hT'eq
  exact valueOn_pullback_of_rel g hg hWW' st st' hrel hU'W' hU'W

end TerminalState

/-! ### The three naturality exports of the sequence

Every export is the corresponding proof for the first step (`stepAFamOn_compat`,
`stepAFamOn_pullback`, `stepAFamOn_indiff`) with the continuation appended: the virtual descent of
the pair (over the join chain `stepAJoin`, over the pre-join chain `preJoin`) is continued through
the separation and monomial steps along a virtual continuation chain which maps into both real
continuation chains link by link, the alignment of the first step (`descentStateAux_rel`) feeds
that of the continuation (`step23Aux_rel`), and the transports of `valueOn` read the two real
sequences off the one virtual terminal state. -/

namespace BMO

open _root_.Manifold

open Hironaka.Manifold.BMOmod

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (m : ℕ)
  (hT : AnalyticTriple.BMOClass m T) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hidN : NonmonomialTransformIdentityMod.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (st3 : MonomialStep3Fam.{u} 𝕜 n m) (U : Opens M) (hU : IsCompact (closure (U : Set M)))

/-! #### The canonical terminal state, named -/

/-- The canonical terminal state of the three steps over `U` at the threshold `m`
(`step23ChainState` with its terminal bound); `bmoSeqOn` is its value on `U`. -/
def bmoTerminal : TerminalState T m (step23ChainOpen T m U hU) :=
  ⟨step23ChainState T m hT bo hcomp hid hidN st3 m hT.1 le_rfl U hU,
    step23ChainState_ord_lt T m hT bo hcomp hid hidN st3 m hT.1 le_rfl U hU⟩

theorem bmoSeqOn_eq_valueOn :
    bmoSeqOn T m hT bo hcomp hid hidN st3 U hU =
      (bmoTerminal T m hT bo hcomp hid hidN st3 U hU).valueOn (le_step23ChainOpen T m U hU) := rfl

/-! #### Compatibility: the virtual join chain of the pair `U ≤ V`, continued -/

section Join

variable (V : Opens M) (hV : IsCompact (closure (V : Set M))) (hUV : U ≤ V)

/-- The number of links of the virtual descent of the first step on the join chain, its bound the
larger of the two. -/
abbrev bmoJoinLinks : ℕ := stepAJoinBound T U hU V hV + 1 - m

include hUV in
theorem closure_subset_stepAJoin (j : ℕ) : closure (U : Set M) ⊆ stepAJoin U hU V hV j := by
  intro x hx
  exact ⟨subset_shrinkChain hU (closure_subset_stepAOuter U hU) j hx,
    subset_shrinkChain hV (closure_subset_stepAOuter V hV) j
      (closure_mono (SetLike.coe_subset_coe.mpr hUV) hx)⟩

include T m U hU V hV hUV in
/-- The virtual continuation chain: the exit open of the join descent, then the shrinkings of
`closure U` inside it met with both real continuation chains, so that it maps into each of them
link by link. -/
def bmoJoinCont : ℕ → Opens M
  | 0 => stepAJoin U hU V hV (bmoJoinLinks T m U hU V hV)
  | k + 1 => shrinkChain (closure (U : Set M)) (stepAJoin U hU V hV (bmoJoinLinks T m U hU V hV))
        hU (closure_subset_stepAJoin U hU V hV hUV _) k ⊓
      (step2ChainOpens T m U hU (k + 1) ⊓ step2ChainOpens T m V hV (k + 1))

theorem isCompact_closure_bmoJoinCont (k : ℕ) :
    IsCompact (closure (bmoJoinCont T m U hU V hV hUV k : Set M)) := by
  cases k with
  | zero => exact isCompact_closure_stepAJoin U hU V hV _
  | succ k =>
    exact (isCompact_closure_shrinkChain hU (closure_subset_stepAJoin U hU V hV hUV _)
      k).of_isClosed_subset isClosed_closure (closure_mono (SetLike.coe_subset_coe.mpr inf_le_left))

theorem closure_bmoJoinCont_succ_subset (k : ℕ) :
    closure (bmoJoinCont T m U hU V hV hUV (k + 1) : Set M) ⊆ bmoJoinCont T m U hU V hV hUV k := by
  cases k with
  | zero =>
    exact (closure_mono (SetLike.coe_subset_coe.mpr inf_le_left)).trans
      (closure_shrinkChain_zero_subset hU (closure_subset_stepAJoin U hU V hV hUV _))
  | succ k =>
    refine (closure_inter_subset_inter_closure _ _).trans (Set.inter_subset_inter
      (closure_shrinkChain_succ_subset hU (closure_subset_stepAJoin U hU V hV hUV _) k) ?_)
    exact (closure_inter_subset_inter_closure _ _).trans (Set.inter_subset_inter
      (closure_step2ChainOpens_succ_subset T m U hU (k + 1))
      (closure_step2ChainOpens_succ_subset T m V hV (k + 1)))

theorem le_bmoJoinCont (k : ℕ) : U ≤ bmoJoinCont T m U hU V hV hUV k := by
  cases k with
  | zero => exact fun x hx => closure_subset_stepAJoin U hU V hV hUV _ (subset_closure hx)
  | succ k =>
    exact le_inf (fun x hx => subset_shrinkChain hU (closure_subset_stepAJoin U hU V hV hUV _) k
      (subset_closure hx))
      (le_inf (le_step2ChainOpens T m U hU (k + 1))
        (hUV.trans (le_step2ChainOpens T m V hV (k + 1))))

theorem bmoJoinCont_le_left (k : ℕ) :
    bmoJoinCont T m U hU V hV hUV k ≤ step2ChainOpens T m U hU k := by
  cases k with
  | zero =>
    exact stepAJoin_le_left U hU V hV _ _
      (Nat.sub_le_sub_right (Nat.add_le_add_right (le_max_left _ _) 1) m)
  | succ k => exact inf_le_right.trans inf_le_left

theorem bmoJoinCont_le_right (k : ℕ) :
    bmoJoinCont T m U hU V hV hUV k ≤ step2ChainOpens T m V hV k := by
  cases k with
  | zero =>
    exact stepAJoin_le_right U hU V hV _ _
      (Nat.sub_le_sub_right (Nat.add_le_add_right (le_max_right _ _) 1) m)
  | succ k => exact inf_le_right.trans inf_le_right

/-- The virtual descent of the first step for the pair (for `T` pulled back along the identity, on
the join chain from the larger bound), read at its exit bound `m − 1`. -/
def bmoJoinExitState :
    BState (T.pullback ContMDiffMap.id (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)) m
      (bmoJoinCont T m U hU V hV hUV 0) (m - 1) :=
  ⟨(descentState (T.pullback ContMDiffMap.id (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id
      M)) m
      (bmoClass_pullback_id T m hT) bo hcomp hid m hT.1 le_rfl (stepAJoin U hU V hV)
      (isCompact_closure_stepAJoin U hU V hV) (bmoJoinLinks T m U hU V hV)
      (fun j _ => closure_stepAJoin_succ_subset U hU V hV j) (stepAJoinBound T U hU V hV)
      (stepAJoin_bound T hcomp U hU V hV) le_rfl).toChainState,
    descentState_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩

/-- The virtual terminal state of the pair: the separation and monomial steps along the virtual
continuation chain. -/
def bmoJoinTerminal :
    TerminalState (T.pullback ContMDiffMap.id
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)) m
      (bmoJoinCont T m U hU V hV hUV m) :=
  ⟨step23Aux (bmoClass_pullback_id T m hT) bo hcomp hidN st3 hT.1 m hT.1
      (bmoJoinCont T m U hU V hV hUV) (isCompact_closure_bmoJoinCont T m U hU V hV hUV)
      (fun k _ => closure_bmoJoinCont_succ_subset T m U hU V hV hUV k)
      (bmoJoinExitState T m hT bo hcomp hid U hU V hV hUV),
    step23Aux_ord_lt _ _ _ _ _ _ _ _ _ _ _ _⟩

/-- The alignment of the first step along the identity (`descentStateAux_rel` at the offset of
bounds `stepAJoinBound − stepABound`, then `alignRHS_congr` to the number of links of `U`): the
cleaned list of the virtual exit state is the cleaned pull-back of that of the real exit state of
`U`. -/
theorem bmoJoinExitState_rel_left :
    (bmoJoinExitState T m hT bo hcomp hid U hU V hV hUV).L.eraseEmpty =
      ((stepAExitState T m hT bo hcomp hid m hT.1 le_rfl U hU).L.pullback
        (AnalyticMap.restrictMap ContMDiffMap.id (bmoJoinCont T m U hU V hV hUV 0)
          (step2ChainOpens T m U hU 0)
          (ChainState.image_id_subset (bmoJoinCont_le_left T m U hU V hV hUV 0)))
        (AnalyticMap.isLocalDiffeomorph_restrictMap
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) _ _
          _)).eraseEmpty := by
  have hle : stepABound T U hU ≤ stepAJoinBound T U hU V hV := le_max_left _ _
  have hal := descentStateAux_rel T m hT bo hcomp hid m hT.1 le_rfl ContMDiffMap.id
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) (bmoClass_pullback_id T m hT)
        (stepAChainOpens U hU)
    (fun k => isCompact_closure_shrinkChain hU (closure_subset_stepAOuter U hU) k)
    (stepALinks T m U hU)
    (fun k _ => closure_shrinkChain_succ_subset hU (closure_subset_stepAOuter U hU) k)
    (stepABound T U hU) (stepABound_bound T U hU) (stepAJoin U hU V hV)
    (isCompact_closure_stepAJoin U hU V hV) (bmoJoinLinks T m U hU V hV)
    (fun j _ => closure_stepAJoin_succ_subset U hU V hV j) (stepAJoinBound T U hU V hV)
    (stepAJoin_bound T hcomp U hU V hV) hle (links_le_sub_add (t := m) hle)
    (fun j => ChainState.image_id_subset (stepAJoin_le_left U hU V hV j _ (Nat.sub_le _ _)))
    (bmoJoinLinks T m U hU V hV) le_rfl le_rfl
  have e : bmoJoinLinks T m U hU V hV - (stepAJoinBound T U hU V hV - stepABound T U hU) =
      stepALinks T m U hU := (sub_links_eq (t := m) hle).symm
  rw [alignRHS_congr T m hT bo hcomp hid m hT.1 le_rfl ContMDiffMap.id
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) (stepAChainOpens U hU) _
        (stepALinks T m U hU) _
    (stepABound T U hU) (stepABound_bound T U hU) (stepAJoin U hU V hV) e _ _ _ le_rfl le_rfl
    (ChainState.image_id_subset (stepAJoin_le_left U hU V hV _ _
      (Nat.sub_le_sub_right (Nat.add_le_add_right (le_max_left _ _) 1) m)))] at hal
  unfold alignRHS at hal
  exact hal

theorem bmoJoinExitState_rel_right :
    (bmoJoinExitState T m hT bo hcomp hid U hU V hV hUV).L.eraseEmpty =
      ((stepAExitState T m hT bo hcomp hid m hT.1 le_rfl V hV).L.pullback
        (AnalyticMap.restrictMap ContMDiffMap.id (bmoJoinCont T m U hU V hV hUV 0)
          (step2ChainOpens T m V hV 0)
          (ChainState.image_id_subset (bmoJoinCont_le_right T m U hU V hV hUV 0)))
        (AnalyticMap.isLocalDiffeomorph_restrictMap
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) _ _
          _)).eraseEmpty := by
  have hle : stepABound T V hV ≤ stepAJoinBound T U hU V hV := le_max_right _ _
  have hal := descentStateAux_rel T m hT bo hcomp hid m hT.1 le_rfl ContMDiffMap.id
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) (bmoClass_pullback_id T m hT)
        (stepAChainOpens V hV)
    (fun k => isCompact_closure_shrinkChain hV (closure_subset_stepAOuter V hV) k)
    (stepALinks T m V hV)
    (fun k _ => closure_shrinkChain_succ_subset hV (closure_subset_stepAOuter V hV) k)
    (stepABound T V hV) (stepABound_bound T V hV) (stepAJoin U hU V hV)
    (isCompact_closure_stepAJoin U hU V hV) (bmoJoinLinks T m U hU V hV)
    (fun j _ => closure_stepAJoin_succ_subset U hU V hV j) (stepAJoinBound T U hU V hV)
    (stepAJoin_bound T hcomp U hU V hV) hle (links_le_sub_add (t := m) hle)
    (fun j => ChainState.image_id_subset (stepAJoin_le_right U hU V hV j _ (Nat.sub_le _ _)))
    (bmoJoinLinks T m U hU V hV) le_rfl le_rfl
  have e : bmoJoinLinks T m U hU V hV - (stepAJoinBound T U hU V hV - stepABound T V hV) =
      stepALinks T m V hV := (sub_links_eq (t := m) hle).symm
  rw [alignRHS_congr T m hT bo hcomp hid m hT.1 le_rfl ContMDiffMap.id
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) (stepAChainOpens V hV) _
        (stepALinks T m V hV) _
    (stepABound T V hV) (stepABound_bound T V hV) (stepAJoin U hU V hV) e _ _ _ le_rfl le_rfl
    (ChainState.image_id_subset (stepAJoin_le_right U hU V hV _ _
      (Nat.sub_le_sub_right (Nat.add_le_add_right (le_max_right _ _) 1) m)))] at hal
  unfold alignRHS at hal
  exact hal

/-- The relation carried through the separation and monomial steps (`step23Aux_rel` along the
identity). -/
theorem bmoJoinTerminal_rel_left :
    (bmoJoinTerminal T m hT bo hcomp hid hidN st3 U hU V hV hUV).L.eraseEmpty =
      ((bmoTerminal T m hT bo hcomp hid hidN st3 U hU).L.pullback
        (AnalyticMap.restrictMap ContMDiffMap.id (bmoJoinCont T m U hU V hV hUV m)
          (step23ChainOpen T m U hU)
          (ChainState.image_id_subset (bmoJoinCont_le_left T m U hU V hV hUV m)))
        (AnalyticMap.isLocalDiffeomorph_restrictMap
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) _ _
          _)).eraseEmpty :=
  step23Aux_rel hT bo hcomp hidN st3 hT.1 m hT.1 ContMDiffMap.id
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) rfl (bmoClass_pullback_id T m hT)
    (step2ChainOpens T m U hU) (isCompact_closure_step2ChainOpens T m U hU)
    (fun k _ => closure_step2ChainOpens_succ_subset T m U hU k) (bmoJoinCont T m U hU V hV hUV)
    (isCompact_closure_bmoJoinCont T m U hU V hV hUV)
    (fun k _ => closure_bmoJoinCont_succ_subset T m U hU V hV hUV k)
    (fun j => ChainState.image_id_subset (bmoJoinCont_le_left T m U hU V hV hUV j))
    (stepAExitState T m hT bo hcomp hid m hT.1 le_rfl U hU)
    (bmoJoinExitState T m hT bo hcomp hid U hU V hV hUV)
    (bmoJoinExitState_rel_left T m hT bo hcomp hid U hU V hV hUV)

theorem bmoJoinTerminal_rel_right :
    (bmoJoinTerminal T m hT bo hcomp hid hidN st3 U hU V hV hUV).L.eraseEmpty =
      ((bmoTerminal T m hT bo hcomp hid hidN st3 V hV).L.pullback
        (AnalyticMap.restrictMap ContMDiffMap.id (bmoJoinCont T m U hU V hV hUV m)
          (step23ChainOpen T m V hV)
          (ChainState.image_id_subset (bmoJoinCont_le_right T m U hU V hV hUV m)))
        (AnalyticMap.isLocalDiffeomorph_restrictMap
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) _ _
          _)).eraseEmpty :=
  step23Aux_rel hT bo hcomp hidN st3 hT.1 m hT.1 ContMDiffMap.id
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) rfl (bmoClass_pullback_id T m hT)
    (step2ChainOpens T m V hV) (isCompact_closure_step2ChainOpens T m V hV)
    (fun k _ => closure_step2ChainOpens_succ_subset T m V hV k) (bmoJoinCont T m U hU V hV hUV)
    (isCompact_closure_bmoJoinCont T m U hU V hV hUV)
    (fun k _ => closure_bmoJoinCont_succ_subset T m U hU V hV hUV k)
    (fun j => ChainState.image_id_subset (bmoJoinCont_le_right T m U hU V hV hUV j))
    (stepAExitState T m hT bo hcomp hid m hT.1 le_rfl V hV)
    (bmoJoinExitState T m hT bo hcomp hid U hU V hV hUV)
    (bmoJoinExitState_rel_right T m hT bo hcomp hid U hU V hV hUV)

/-- The compatibility `CompatibleFamily.compat` on the values ([Wlo09, Theorem 2.0.3 (4)],
[Wlo09, Definition 3.2.6]; [Kol07, 34.1]): the sequence over `U ≤ V` is the sequence over `V`
restricted to `U` and cleaned. Both are the virtual terminal state of the pair read on `U`
(`valueOn_eq_of_rel_id` twice, then `valueOn_restrict`). -/
theorem bmoSeqOn_compat :
    bmoSeqOn T m hT bo hcomp hid hidN st3 U hU =
      ((bmoSeqOn T m hT bo hcomp hid hidN st3 V hV).pullback (M.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty := by
  rw [bmoSeqOn_eq_valueOn, bmoSeqOn_eq_valueOn]
  have h1 := TerminalState.valueOn_eq_of_rel_id (bmoTerminal T m hT bo hcomp hid hidN st3 U hU)
    (bmoJoinTerminal T m hT bo hcomp hid hidN st3 U hU V hV hUV)
    (ChainState.image_id_subset (bmoJoinCont_le_left T m U hU V hV hUV m))
    (bmoJoinTerminal_rel_left T m hT bo hcomp hid hidN st3 U hU V hV hUV)
    (le_bmoJoinCont T m U hU V hV hUV m) (le_step23ChainOpen T m U hU)
  have h2 := TerminalState.valueOn_eq_of_rel_id (bmoTerminal T m hT bo hcomp hid hidN st3 V hV)
    (bmoJoinTerminal T m hT bo hcomp hid hidN st3 U hU V hV hUV)
    (ChainState.image_id_subset (bmoJoinCont_le_right T m U hU V hV hUV m))
    (bmoJoinTerminal_rel_right T m hT bo hcomp hid hidN st3 U hU V hV hUV)
    (le_bmoJoinCont T m U hU V hV hUV m) (hUV.trans (le_step23ChainOpen T m V hV))
  rw [← h1, h2]
  exact (bmoTerminal T m hT bo hcomp hid hidN st3 V hV).valueOn_restrict
    (le_step23ChainOpen T m V hV) hUV

end Join

/-! #### Local isomorphisms: the virtual pre-join chain of `U' ⊆ N` and `g(U') ⊆ M`, continued -/

section PreJoin

variable {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (g : AnalyticMap N M)
  (hg : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g)
  (hT' : AnalyticTriple.BMOClass m (T.pullback g hg)) (U' : Opens N)
  (hU' : IsCompact (closure (U' : Set N)))

/-- The number of links of the virtual descent on the pre-join chain. -/
abbrev bmoPreJoinLinks : ℕ :=
  preJoinBound T g hg U' hU' (AnalyticMap.imageOpens g hg U')
    (AnalyticMap.isCompact_closure_image g hU') + 1 - m

theorem closure_subset_preJoin (j : ℕ) :
    closure (U' : Set N) ⊆
      preJoin g U' hU' (AnalyticMap.imageOpens g hg U') (AnalyticMap.isCompact_closure_image g hU')
        j := by
  intro x hx
  refine ⟨subset_shrinkChain hU' (closure_subset_stepAOuter U' hU') j hx, ?_⟩
  exact subset_shrinkChain (AnalyticMap.isCompact_closure_image g hU')
    (closure_subset_stepAOuter (AnalyticMap.imageOpens g hg U') _) j
    (image_closure_subset_closure_image g.contMDiff.continuous ⟨x, hx, rfl⟩)

include T m g hg U' hU' in
/-- The virtual continuation chain over `N`: the exit open of the pre-join descent, then the
shrinkings of `closure U'` met with the real continuation of `U'` and the `g`-preimage of the real
continuation of `g(U')`. -/
def bmoPreJoinCont : ℕ → Opens N
  | 0 => preJoin g U' hU' (AnalyticMap.imageOpens g hg U')
      (AnalyticMap.isCompact_closure_image g hU') (bmoPreJoinLinks T m g hg U' hU')
  | k + 1 => shrinkChain (closure (U' : Set N))
        (preJoin g U' hU' (AnalyticMap.imageOpens g hg U')
          (AnalyticMap.isCompact_closure_image g hU') (bmoPreJoinLinks T m g hg U' hU'))
        hU' (closure_subset_preJoin g hg U' hU' _) k ⊓
      (step2ChainOpens (T.pullback g hg) m U' hU' (k + 1) ⊓
        preimageOpens ⇑g g.contMDiff
          (step2ChainOpens T m (AnalyticMap.imageOpens g hg U')
            (AnalyticMap.isCompact_closure_image g hU') (k + 1)))

theorem isCompact_closure_bmoPreJoinCont (k : ℕ) :
    IsCompact (closure (bmoPreJoinCont T m g hg U' hU' k : Set N)) := by
  cases k with
  | zero => exact isCompact_closure_preJoin g U' hU' _ _ _
  | succ k =>
    exact (isCompact_closure_shrinkChain hU' (closure_subset_preJoin g hg U' hU' _)
      k).of_isClosed_subset isClosed_closure (closure_mono (SetLike.coe_subset_coe.mpr inf_le_left))

theorem closure_bmoPreJoinCont_succ_subset (k : ℕ) :
    closure (bmoPreJoinCont T m g hg U' hU' (k + 1) : Set N) ⊆
      bmoPreJoinCont T m g hg U' hU' k := by
  cases k with
  | zero =>
    exact (closure_mono (SetLike.coe_subset_coe.mpr inf_le_left)).trans
      (closure_shrinkChain_zero_subset hU' (closure_subset_preJoin g hg U' hU' _))
  | succ k =>
    refine (closure_inter_subset_inter_closure _ _).trans (Set.inter_subset_inter
      (closure_shrinkChain_succ_subset hU' (closure_subset_preJoin g hg U' hU' _) k) ?_)
    refine (closure_inter_subset_inter_closure _ _).trans (Set.inter_subset_inter
      (closure_step2ChainOpens_succ_subset (T.pullback g hg) m U' hU' (k + 1)) ?_)
    have h1 : closure (⇑g ⁻¹' (step2ChainOpens T m (AnalyticMap.imageOpens g hg U')
        (AnalyticMap.isCompact_closure_image g hU') (k + 2) : Set M)) ⊆
        ⇑g ⁻¹' closure (step2ChainOpens T m (AnalyticMap.imageOpens g hg U')
          (AnalyticMap.isCompact_closure_image g hU') (k + 2) : Set M) :=
      closure_minimal (Set.preimage_mono subset_closure)
        (isClosed_closure.preimage g.contMDiff.continuous)
    exact h1.trans (Set.preimage_mono (closure_step2ChainOpens_succ_subset T m _ _ (k + 1)))

theorem le_bmoPreJoinCont (k : ℕ) : U' ≤ bmoPreJoinCont T m g hg U' hU' k := by
  cases k with
  | zero => exact fun x hx => closure_subset_preJoin g hg U' hU' _ (subset_closure hx)
  | succ k =>
    exact le_inf (fun x hx => subset_shrinkChain hU' (closure_subset_preJoin g hg U' hU' _) k
      (subset_closure hx))
      (le_inf (le_step2ChainOpens (T.pullback g hg) m U' hU' (k + 1))
        (fun x hx => le_step2ChainOpens T m _ _ (k + 1) (Set.mem_image_of_mem g hx)))

theorem bmoPreJoinCont_le_left (k : ℕ) :
    bmoPreJoinCont T m g hg U' hU' k ≤ step2ChainOpens (T.pullback g hg) m U' hU' k := by
  cases k with
  | zero =>
    exact preJoin_le_left g U' hU' _ _ _ _
      (Nat.sub_le_sub_right (Nat.add_le_add_right (le_max_left _ _) 1) m)
  | succ k => exact inf_le_right.trans inf_le_left

theorem image_bmoPreJoinCont_subset (k : ℕ) :
    ⇑g '' (bmoPreJoinCont T m g hg U' hU' k : Set N) ⊆
      step2ChainOpens T m (AnalyticMap.imageOpens g hg U')
        (AnalyticMap.isCompact_closure_image g hU') k := by
  cases k with
  | zero =>
    exact image_preJoin_subset g U' hU' _ _ _ _
      (Nat.sub_le_sub_right (Nat.add_le_add_right (le_max_right _ _) 1) m)
  | succ k =>
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2.2

/-- The virtual descent of the first step for the pair (for the pulled-back triple pulled back once
more along the identity, on the pre-join chain from the larger bound), read at its exit bound
`m − 1`. -/
def bmoPreJoinExitState :
    BState ((T.pullback g hg).pullback ContMDiffMap.id
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N)) m
      (bmoPreJoinCont T m g hg U' hU' 0) (m - 1) :=
  ⟨(descentState ((T.pullback g hg).pullback ContMDiffMap.id
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N))
      m (bmoClass_pullback_id (T.pullback g hg) m hT') bo hcomp hid m hT.1 le_rfl
      (preJoin g U' hU' (AnalyticMap.imageOpens g hg U')
        (AnalyticMap.isCompact_closure_image g hU'))
      (isCompact_closure_preJoin g U' hU' _ _) (bmoPreJoinLinks T m g hg U' hU')
      (fun j _ => closure_preJoin_succ_subset g U' hU' _ _ j)
      (preJoinBound T g hg U' hU' _ _) (preJoin_bound T hcomp g hg U' hU' _ _) le_rfl).toChainState,
    descentState_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩

/-- The virtual terminal state of the pair over `N`. -/
def bmoPreJoinTerminal :
    TerminalState ((T.pullback g hg).pullback ContMDiffMap.id
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N))
      m (bmoPreJoinCont T m g hg U' hU' m) :=
  ⟨step23Aux (bmoClass_pullback_id (T.pullback g hg) m hT') bo hcomp hidN st3 hT.1 m hT.1
      (bmoPreJoinCont T m g hg U' hU') (isCompact_closure_bmoPreJoinCont T m g hg U' hU')
      (fun k _ => closure_bmoPreJoinCont_succ_subset T m g hg U' hU' k)
      (bmoPreJoinExitState T m hT bo hcomp hid g hg hT' U' hU'),
    step23Aux_ord_lt _ _ _ _ _ _ _ _ _ _ _ _⟩

/-- The virtual terminal state aligned with the real terminal state of `U'` (for the pulled-back
triple), along the identity of `N` (`descentStateAux_rel` and `step23Aux_rel` along the
identity). -/
theorem bmoPreJoinTerminal_rel_left :
    (bmoPreJoinTerminal T m hT bo hcomp hid hidN st3 g hg hT' U' hU').L.eraseEmpty =
      ((bmoTerminal (T.pullback g hg) m hT' bo hcomp hid hidN st3 U' hU').L.pullback
        (AnalyticMap.restrictMap ContMDiffMap.id (bmoPreJoinCont T m g hg U' hU' m)
          (step23ChainOpen (T.pullback g hg) m U' hU')
          (ChainState.image_id_subset (bmoPreJoinCont_le_left T m g hg U' hU' m)))
        (AnalyticMap.isLocalDiffeomorph_restrictMap
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N) _ _
          _)).eraseEmpty := by
  have hle : stepABound (T.pullback g hg) U' hU' ≤
      preJoinBound T g hg U' hU' (AnalyticMap.imageOpens g hg U')
        (AnalyticMap.isCompact_closure_image g hU') := le_max_left _ _
  have hal := descentStateAux_rel (T.pullback g hg) m hT' bo hcomp hid m hT.1 le_rfl ContMDiffMap.id
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N) (bmoClass_pullback_id
        (T.pullback g hg) m hT')
    (stepAChainOpens U' hU')
    (fun k => isCompact_closure_shrinkChain hU' (closure_subset_stepAOuter U' hU') k)
    (stepALinks (T.pullback g hg) m U' hU')
    (fun k _ => closure_shrinkChain_succ_subset hU' (closure_subset_stepAOuter U' hU') k)
    (stepABound (T.pullback g hg) U' hU') (stepABound_bound (T.pullback g hg) U' hU')
    (preJoin g U' hU' _ _) (isCompact_closure_preJoin g U' hU' _ _)
    (bmoPreJoinLinks T m g hg U' hU') (fun j _ => closure_preJoin_succ_subset g U' hU' _ _ j)
    (preJoinBound T g hg U' hU' _ _) (preJoin_bound T hcomp g hg U' hU' _ _) hle
    (links_le_sub_add (t := m) hle)
    (fun j => ChainState.image_id_subset (preJoin_le_left g U' hU' _ _ j _ (Nat.sub_le _ _)))
    (bmoPreJoinLinks T m g hg U' hU') le_rfl le_rfl
  have e : bmoPreJoinLinks T m g hg U' hU' -
      (preJoinBound T g hg U' hU' (AnalyticMap.imageOpens g hg U')
        (AnalyticMap.isCompact_closure_image g hU') - stepABound (T.pullback g hg) U' hU') =
      stepALinks (T.pullback g hg) m U' hU' := (sub_links_eq (t := m) hle).symm
  have hal' := hal.trans (alignRHS_congr (T.pullback g hg) m hT' bo hcomp hid m hT.1 le_rfl
    ContMDiffMap.id (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N)
        (stepAChainOpens U' hU') _
    (stepALinks (T.pullback g hg) m U' hU') _ (stepABound (T.pullback g hg) U' hU')
    (stepABound_bound (T.pullback g hg) U' hU')
    (preJoin g U' hU' (AnalyticMap.imageOpens g hg U') (AnalyticMap.isCompact_closure_image g hU'))
    e _ _ _ le_rfl le_rfl
    (ChainState.image_id_subset (preJoin_le_left g U' hU' _ _ _ _
      (Nat.sub_le_sub_right (Nat.add_le_add_right (le_max_left _ _) 1) m))))
  unfold alignRHS at hal'
  exact step23Aux_rel hT' bo hcomp hidN st3 hT.1 m hT.1 ContMDiffMap.id
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N) rfl (bmoClass_pullback_id
        (T.pullback g hg) m hT')
    (step2ChainOpens (T.pullback g hg) m U' hU')
    (isCompact_closure_step2ChainOpens (T.pullback g hg) m U' hU')
    (fun k _ => closure_step2ChainOpens_succ_subset (T.pullback g hg) m U' hU' k)
    (bmoPreJoinCont T m g hg U' hU') (isCompact_closure_bmoPreJoinCont T m g hg U' hU')
    (fun k _ => closure_bmoPreJoinCont_succ_subset T m g hg U' hU' k)
    (fun j => ChainState.image_id_subset (bmoPreJoinCont_le_left T m g hg U' hU' j))
    (stepAExitState (T.pullback g hg) m hT' bo hcomp hid m hT.1 le_rfl U' hU')
    (bmoPreJoinExitState T m hT bo hcomp hid g hg hT' U' hU') hal'

/-- The virtual terminal state aligned with the real terminal state of `g(U')` (for `T`), along `g`
(`descentStateAux_rel` and `step23Aux_rel` along `g`; the triple of the virtual descent is the
pulled-back triple by `IsPullbackOf.eq`, which is substituted inside). -/
theorem bmoPreJoinTerminal_rel_right :
    (bmoPreJoinTerminal T m hT bo hcomp hid hidN st3 g hg hT' U' hU').L.eraseEmpty =
      ((bmoTerminal T m hT bo hcomp hid hidN st3 (AnalyticMap.imageOpens g hg U')
          (AnalyticMap.isCompact_closure_image g hU')).L.pullback
        (AnalyticMap.restrictMap g (bmoPreJoinCont T m g hg U' hU' m)
          (step23ChainOpen T m (AnalyticMap.imageOpens g hg U')
            (AnalyticMap.isCompact_closure_image g hU'))
          (image_bmoPreJoinCont_subset T m g hg U' hU' m))
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg _ _ _)).eraseEmpty := by
  have hle : stepABound T (AnalyticMap.imageOpens g hg U')
      (AnalyticMap.isCompact_closure_image g hU') ≤
      preJoinBound T g hg U' hU' (AnalyticMap.imageOpens g hg U')
        (AnalyticMap.isCompact_closure_image g hU') := le_max_right _ _
  have e₀ : (T.pullback g hg).pullback ContMDiffMap.id
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N) =
      T.pullback g hg :=
    AnalyticTriple.IsPullbackOf.eq
      ((T.isPullbackOf_pullback g hg).comp ((T.pullback g hg).isPullbackOf_pullback
        ContMDiffMap.id (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N)))
      (T.isPullbackOf_pullback g hg)
  -- the exit alignment along `g`, for ANY triple equal to the pulled-back one (a `subst`)
  have key : ∀ (T₂ : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) N),
      T₂ = T.pullback g hg → ∀ (hT₂ : AnalyticTriple.BMOClass m T₂)
      (hDX : ∀ x ∈ (preJoin g U' hU' (AnalyticMap.imageOpens g hg U')
        (AnalyticMap.isCompact_closure_image g hU') 0 : Set N),
        (nonmonomialTriple T₂).I.ord x ≤
          (preJoinBound T g hg U' hU' (AnalyticMap.imageOpens g hg U')
            (AnalyticMap.isCompact_closure_image g hU') : ℕ∞)),
      (descentStateAux T₂ m hT₂ bo hcomp hid m hT.1 le_rfl (preJoin g U' hU' _ _)
        (isCompact_closure_preJoin g U' hU' _ _) (bmoPreJoinLinks T m g hg U' hU')
        (fun j _ => closure_preJoin_succ_subset g U' hU' _ _ j) (preJoinBound T g hg U' hU' _ _)
        hDX (bmoPreJoinLinks T m g hg U' hU') le_rfl le_rfl).L.eraseEmpty =
      alignRHS T m hT bo hcomp hid m hT.1 le_rfl g hg
        (stepAChainOpens (AnalyticMap.imageOpens g hg U')
          (AnalyticMap.isCompact_closure_image g hU'))
        (fun k => isCompact_closure_shrinkChain _ (closure_subset_stepAOuter _ _) k)
        (stepALinks T m (AnalyticMap.imageOpens g hg U')
          (AnalyticMap.isCompact_closure_image g hU'))
        (fun k _ => closure_shrinkChain_succ_subset _ (closure_subset_stepAOuter _ _) k)
        (stepABound T (AnalyticMap.imageOpens g hg U') (AnalyticMap.isCompact_closure_image g hU'))
        (stepABound_bound T _ _) (preJoin g U' hU' _ _) (bmoPreJoinLinks T m g hg U' hU')
        (bmoPreJoinLinks T m g hg U' hU' - (preJoinBound T g hg U' hU' _ _ - stepABound T _ _))
        (sub_links_eq (t := m) hle).symm.le (sub_links_eq (t := m) hle).symm.le
        (image_preJoin_subset g U' hU' _ _ _ _ (Nat.sub_le _ _)) := by
    intro T₂ e₂ hT₂ hDX
    subst e₂
    exact descentStateAux_rel T m hT bo hcomp hid m hT.1 le_rfl g hg hT₂
      (stepAChainOpens (AnalyticMap.imageOpens g hg U') (AnalyticMap.isCompact_closure_image g hU'))
      (fun k => isCompact_closure_shrinkChain _ (closure_subset_stepAOuter _ _) k)
      (stepALinks T m (AnalyticMap.imageOpens g hg U') (AnalyticMap.isCompact_closure_image g hU'))
      (fun k _ => closure_shrinkChain_succ_subset _ (closure_subset_stepAOuter _ _) k)
      (stepABound T _ _) (stepABound_bound T _ _) (preJoin g U' hU' _ _)
      (isCompact_closure_preJoin g U' hU' _ _) (bmoPreJoinLinks T m g hg U' hU')
      (fun j _ => closure_preJoin_succ_subset g U' hU' _ _ j) (preJoinBound T g hg U' hU' _ _) hDX
      hle (links_le_sub_add (t := m) hle)
      (fun j => image_preJoin_subset g U' hU' _ _ j _ (Nat.sub_le _ _))
      (bmoPreJoinLinks T m g hg U' hU') le_rfl le_rfl
  have hal := key _ e₀ (bmoClass_pullback_id (T.pullback g hg) m hT')
    (preJoin_bound T hcomp g hg U' hU' _ _)
  have e : bmoPreJoinLinks T m g hg U' hU' -
      (preJoinBound T g hg U' hU' (AnalyticMap.imageOpens g hg U')
        (AnalyticMap.isCompact_closure_image g hU') -
        stepABound T (AnalyticMap.imageOpens g hg U') (AnalyticMap.isCompact_closure_image g hU')) =
      stepALinks T m (AnalyticMap.imageOpens g hg U') (AnalyticMap.isCompact_closure_image g hU') :=
    (sub_links_eq (t := m) hle).symm
  rw [alignRHS_congr T m hT bo hcomp hid m hT.1 le_rfl g hg
    (stepAChainOpens (AnalyticMap.imageOpens g hg U') (AnalyticMap.isCompact_closure_image g hU')) _
    (stepALinks T m (AnalyticMap.imageOpens g hg U') (AnalyticMap.isCompact_closure_image g hU')) _
    (stepABound T _ _) (stepABound_bound T _ _) (preJoin g U' hU' _ _) e _ _ _ le_rfl le_rfl
    (image_preJoin_subset g U' hU' _ _ _ _
      (Nat.sub_le_sub_right (Nat.add_le_add_right (le_max_right _ _) 1) m))] at hal
  unfold alignRHS at hal
  exact step23Aux_rel hT bo hcomp hidN st3 hT.1 m hT.1 g hg e₀
    (bmoClass_pullback_id (T.pullback g hg) m hT')
    (step2ChainOpens T m (AnalyticMap.imageOpens g hg U')
      (AnalyticMap.isCompact_closure_image g hU'))
    (isCompact_closure_step2ChainOpens T m _ _)
    (fun k _ => closure_step2ChainOpens_succ_subset T m _ _ k)
    (bmoPreJoinCont T m g hg U' hU') (isCompact_closure_bmoPreJoinCont T m g hg U' hU')
    (fun k _ => closure_bmoPreJoinCont_succ_subset T m g hg U' hU' k)
    (image_bmoPreJoinCont_subset T m g hg U' hU')
    (stepAExitState T m hT bo hcomp hid m hT.1 le_rfl _ _)
    (bmoPreJoinExitState T m hT bo hcomp hid g hg hT' U' hU') hal

end PreJoin

/-- The commutation with local analytic isomorphisms ([Kol07, Theorem 107 (2)], [Kol07, 34.1]) in
the form `CommutesWithLocalIsos` requires: for `T'` a pull-back of `T` along a local analytic
isomorphism `g`, the sequence over `U'` is the sequence over `g(U')` pulled back along `g|_{U'}`
and cleaned. Both are the virtual terminal state of the pair read on `U'` (`valueOn_eq_of_rel_id`
along the identity of `N`, `valueOn_pullback_of_rel'` along `g`). -/
theorem bmoSeqOn_pullback {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g)
    {T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) N} (hpull : T'.IsPullbackOf T g)
    (hT' : AnalyticTriple.BMOClass m T') (U' : Opens N)
    (hU' : IsCompact (closure (U' : Set N))) :
    bmoSeqOn T' m hT' bo hcomp hid hidN st3 U' hU' =
      ((bmoSeqOn T m hT bo hcomp hid hidN st3 (AnalyticMap.imageOpens g hg U')
          (AnalyticMap.isCompact_closure_image g hU')).pullback
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
          Set.Subset.rfl)).eraseEmpty := by
  obtain rfl := hpull.eq (T.isPullbackOf_pullback g hg)
  have e₀ : (T.pullback g hg).pullback ContMDiffMap.id
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N) =
      T.pullback g hg :=
    AnalyticTriple.IsPullbackOf.eq
      ((T.isPullbackOf_pullback g hg).comp ((T.pullback g hg).isPullbackOf_pullback
        ContMDiffMap.id (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N)))
      (T.isPullbackOf_pullback g hg)
  have h1 := TerminalState.valueOn_eq_of_rel_id
    (bmoTerminal (T.pullback g hg) m hT' bo hcomp hid hidN st3 U' hU')
    (bmoPreJoinTerminal T m hT bo hcomp hid hidN st3 g hg hT' U' hU')
    (ChainState.image_id_subset (bmoPreJoinCont_le_left T m g hg U' hU' m))
    (bmoPreJoinTerminal_rel_left T m hT bo hcomp hid hidN st3 g hg hT' U' hU')
    (le_bmoPreJoinCont T m g hg U' hU' m) (le_step23ChainOpen (T.pullback g hg) m U' hU')
  have h2 := TerminalState.valueOn_pullback_of_rel' g hg e₀
    (image_bmoPreJoinCont_subset T m g hg U' hU' m) (bmoTerminal T m hT bo hcomp hid hidN st3 _ _)
    (bmoPreJoinTerminal T m hT bo hcomp hid hidN st3 g hg hT' U' hU')
    (bmoPreJoinTerminal_rel_right T m hT bo hcomp hid hidN st3 g hg hT' U' hU')
    (le_bmoPreJoinCont T m g hg U' hU' m) (le_step23ChainOpen T m _ _)
  exact (bmoSeqOn_eq_valueOn (T.pullback g hg) m hT' bo hcomp hid hidN st3 U' hU').trans
    (h1.symm.trans h2)

/-! #### Indifference: the same chain from the same bound for the boundary-extended triple -/

section Indiff

variable (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (e : F'.ι ↪o T.F.ι) (he : ∀ i, T.F.hyp (e i) = F'.hyp i)
  (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅)
  (hT' : AnalyticTriple.BMOClass m (BDan.withBoundary T F' hsnc'))

include e he he' in
/-- The canonical chains of `T` and of the boundary-extended triple coincide: the bound is read on
the nonmonomial ideal, which does not see the empty members (`roundOrderOn_withBoundary`), and the
chain is the shrink chain from it (substituting through the dependent inclusion proof). -/
theorem step2ChainOpens_withBoundary :
    step2ChainOpens (BDan.withBoundary T F' hsnc') m U hU = step2ChainOpens T m U hU := by
  have eD : stepABound (BDan.withBoundary T F' hsnc') U hU = stepABound T U hU :=
    roundOrderOn_withBoundary T F' hsnc' e he he' (stepAOuter U hU)
  have eO : step2Outer (BDan.withBoundary T F' hsnc') m U hU = step2Outer T m U hU := by
    unfold step2Outer stepALinks
    rw [eD]
  have key : ∀ (O₁ O₂ : Opens M) (h : O₁ = O₂) (h₁ : closure (U : Set M) ⊆ O₁)
      (h₂ : closure (U : Set M) ⊆ O₂) (k : ℕ),
      shrinkChain (closure (U : Set M)) O₁ hU h₁ k =
        shrinkChain (closure (U : Set M)) O₂ hU h₂ k := by
    intro O₁ O₂ h h₁ h₂ k
    subst h
    rfl
  funext k
  cases k with
  | zero => exact eO
  | succ k => exact key _ _ eO _ _ k

include e he he' in
/-- **The terminal lists agree** across the propositionally equal canonical chains: the descents
of the first step from the equal bounds have the same lists (`descentStateAux_L_indiff`, after
substituting the bound and the number of links), and the continuations along the same chain from
states with the same list have the same list (`step23Aux_L_indiff`, after substituting the
chain). -/
theorem bmoTerminal_L_indiff :
    HEq (bmoTerminal T m hT bo hcomp hid hidN st3 U hU).L
      (bmoTerminal (BDan.withBoundary T F' hsnc') m hT' bo hcomp hid hidN st3 U hU).L := by
  have eD : stepABound (BDan.withBoundary T F' hsnc') U hU = stepABound T U hU :=
    roundOrderOn_withBoundary T F' hsnc' e he he' (stepAOuter U hU)
  have eW := step2ChainOpens_withBoundary T m U hU F' hsnc' e he he'
  -- the exit states: the descents from the two (equal) bounds, with the link counts generalised
  have keyA : ∀ (D' r' j' : ℕ), D' = stepABound T U hU → r' = stepALinks T m U hU →
      j' = stepALinks T m U hU →
      ∀ (hWsub' : ∀ k, k < r' →
          closure (stepAChainOpens U hU (k + 1) : Set M) ⊆ stepAChainOpens U hU k)
        (hD' : ∀ x ∈ (stepAChainOpens U hU 0 : Set M),
          (nonmonomialTriple (BDan.withBoundary T F' hsnc')).I.ord x ≤ (D' : ℕ∞))
        (hj : j' ≤ r') (hjt : j' ≤ D' + 1 - m),
      HEq (descentStateAux T m hT bo hcomp hid m hT.1 le_rfl (stepAChainOpens U hU)
          (fun k => isCompact_closure_shrinkChain hU (closure_subset_stepAOuter U hU) k)
          (stepALinks T m U hU)
          (fun k _ => closure_shrinkChain_succ_subset hU (closure_subset_stepAOuter U hU) k)
          (stepABound T U hU) (stepABound_bound T U hU) (stepALinks T m U hU) le_rfl le_rfl).L
        (descentStateAux (BDan.withBoundary T F' hsnc') m hT' bo hcomp hid m hT'.1 le_rfl
          (stepAChainOpens U hU)
          (fun k => isCompact_closure_shrinkChain hU (closure_subset_stepAOuter U hU) k) r' hWsub'
          D' hD' j' hj hjt).L := by
    intro D' r' j' eD' er ej hWsub' hD' hj hjt
    subst eD' er ej
    exact heq_of_eq (descentStateAux_L_indiff T m hT bo hcomp hid m hT.1 le_rfl F' hsnc' e he he'
      hT' (stepAChainOpens U hU) _ (stepALinks T m U hU) _ (stepABound T U hU) _ hD' _ le_rfl
      le_rfl)
  have hexit : HEq (stepAExitState T m hT bo hcomp hid m hT.1 le_rfl U hU).L
      (stepAExitState (BDan.withBoundary T F' hsnc') m hT' bo hcomp hid m hT'.1 le_rfl U hU).L :=
    keyA (stepABound (BDan.withBoundary T F' hsnc') U hU)
      (stepALinks (BDan.withBoundary T F' hsnc') m U hU)
      (descentLength m (stepABound (BDan.withBoundary T F' hsnc') U hU)) eD
      (by simp only [stepALinks, eD]) (by simp only [stepALinks, descentLength, eD])
      _ _ le_rfl le_rfl
  -- the continuations along the same chain from states with the same list
  have key : ∀ (W' : ℕ → Opens M), W' = step2ChainOpens T m U hU →
      ∀ (hW' : ∀ k, IsCompact (closure (W' k : Set M)))
        (hWsub' : ∀ k, k < m → closure (W' (k + 1) : Set M) ⊆ W' k)
        (st₀' : BState (BDan.withBoundary T F' hsnc') m (W' 0) (m - 1)),
      HEq (stepAExitState T m hT bo hcomp hid m hT.1 le_rfl U hU).L st₀'.L →
      HEq (step23Aux hT bo hcomp hidN st3 hT.1 m hT.1 (step2ChainOpens T m U hU)
          (isCompact_closure_step2ChainOpens T m U hU)
          (fun k _ => closure_step2ChainOpens_succ_subset T m U hU k)
          (stepAExitState T m hT bo hcomp hid m hT.1 le_rfl U hU)).L
        (step23Aux hT' bo hcomp hidN st3 hT'.1 m hT'.1 W' hW' hWsub' st₀').L := by
    intro W' eW' hW' hWsub' st₀' hL
    subst eW'
    exact heq_of_eq (step23Aux_L_indiff hT bo hcomp hidN st3 hT.1 F' hsnc' e he he' hT' m hT.1 _
      _ _ _ _ (eq_of_heq hL))
  exact key (step2ChainOpens (BDan.withBoundary T F' hsnc') m U hU) eW _ _ _ hexit

end Indiff

/-- The indifference to empty boundary members (the counterpart, for boundary members, of
[Kol07, 32]) on each open, for the triple with the
boundary replaced by `F'`: the canonical chain and bound do not see the empty members, and the two
runs along them have the same lists (`bmoTerminal_L_indiff`), so the values on `U` agree (the
heterogeneous equality is discharged by substituting the terminal open). -/
theorem bmoSeqOn_indiff (F' : HypersurfaceFamily M)
    (hsnc' : F'.IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))) (e : F'.ι ↪o T.F.ι)
    (he : ∀ i, T.F.hyp (e i) = F'.hyp i) (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅)
    (hT' : AnalyticTriple.BMOClass m ⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩) :
    bmoSeqOn T m hT bo hcomp hid hidN st3 U hU =
      bmoSeqOn ⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ m hT' bo hcomp hid hidN st3 U hU := by
  rw [bmoSeqOn_eq_valueOn, bmoSeqOn_eq_valueOn]
  have eW : step23ChainOpen (BDan.withBoundary T F' hsnc') m U hU = step23ChainOpen T m U hU :=
    congrFun (step2ChainOpens_withBoundary T m U hU F' hsnc' e he he') m
  have aux : ∀ (W' : Opens M), W' = step23ChainOpen T m U hU →
      ∀ (st' : TerminalState (BDan.withBoundary T F' hsnc') m W'),
      HEq (bmoTerminal T m hT bo hcomp hid hidN st3 U hU).L st'.L → ∀ (hUW' : U ≤ W'),
      (bmoTerminal T m hT bo hcomp hid hidN st3 U hU).valueOn (le_step23ChainOpen T m U hU) =
        st'.valueOn hUW' := by
    intro W' eW' st' hL hUW'
    subst eW'
    unfold TerminalState.valueOn
    rw [eq_of_heq hL]
  exact aux _ eW _ (bmoTerminal_L_indiff T m hT bo hcomp hid hidN st3 U hU F' hsnc' e he he' hT') _

end BMO

end Hironaka.Manifold

end
