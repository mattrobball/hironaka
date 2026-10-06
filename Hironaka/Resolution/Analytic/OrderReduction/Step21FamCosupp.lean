/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Step21Fam
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Hironaka.Resolution.Analytic.OrderReduction.ChainTransport
import Hironaka.Resolution.Analytic.OrderReduction.Step21Cosupp
import Hironaka.Resolution.Analytic.OrderReduction.Step22Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Step 2.1 on an open: the cosupport misses the transforms of the members

At the end of Step 2.1 of the proof of [Kol07, Theorem 103], "`cosupp(I_r, m)` is disjoint from
`Π^{-1}_* E`" (the conclusion of [Kol07, 104, Step 2.1.j] for every member `i ≤ j`). In the
compatible-family form (`Step21Fam.lean`): at the end of Step 2.1 on a relatively compact open `U`,
the cosupport of the controlled transform of `𝓘|_U` misses the strict transform of every member of
`E|_U` (`step21FamOn_cosupp_disjoint`). Along the chain:

* `BlowUpSequence.disjoint_setOf_le_ord_strictTransformSeq_pullback`, `…_eraseEmpty` — the clause
  "the cosupport of the last controlled transform misses the last strict transform of `H`" is
  carried along a pull-back (the last stage of the pulled-back sequence maps to the last stage by
  a local analytic isomorphism, `markedTransformSeq_last_pullbackLiftLast`,
  `strictTransformSeq_last_pullbackLiftLast`) and along the deletion of the empty blow-ups
  (`markedTransformSeq_last_eraseEmpty`, `strictTransformSeq_last_eraseEmpty`);
* `ChainState.step21FamAux_cosupp_disjoint` — along the chain, once a member has been processed the
  clause holds for it: Lemma 102 (1) of the family at that link (`bd.cosupp_disjoint`, the weak
  transform being the controlled one by `bd.isOfOrder`), pulled back to the link's open and carried
  through the concatenation (`disjoint_concat_of_disjoint`); the clauses of the members processed
  before persist along a sequence of order `≥ s`
  (`disjoint_setOf_le_ord_markedTransformSeq_strictTransformSeq`);
* `step21FamOn_cosupp_disjoint` — the chain's clause restricted to `U` with the empty blow-ups
  deleted; an empty member has empty strict transform.

This is the clause of Step 2.1 that Step 2.2 in the compatible-family form needs
(`Step22Fam.lean`).
-/

public section

universe u

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

namespace AnalyticManifold.BlowUpSequence

open _root_.Manifold
open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

/-- **The clause of Lemma 102 (1) pulls back** (the local nature of [Kol07, 34.1]): if along `L` the
cosupport of the last controlled transform of `J` misses the last strict transform of `H`, then
along `h^* L` the cosupport of the last controlled transform of `h^* J` misses the last strict
transform of `h⁻¹(H)`. Both are read at the lift of the point to the last stage of `L`
(`markedTransformSeq_last_pullbackLiftLast`, `strictTransformSeq_last_pullbackLiftLast`,
`ord_pullback_of_isLocalDiffeomorphAt`). -/
theorem disjoint_setOf_le_ord_strictTransformSeq_pullback (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (J E₀ : IdealSheaf M) (m : ℕ) (hge : L.toSuccession.IsOfOrderGe J m E₀)
        (H : Set M)
    (hL : Disjoint {y | (m : ℕ∞) ≤ (L.toSuccession.markedTransformSeq J m (Fin.last _)).ord y}
      (L.toSuccession.strictTransformSeq H (Fin.last _))) :
    Disjoint
      {x | (m : ℕ∞) ≤ ((L.pullback h hh).toSuccession.markedTransformSeq
        (J.pullback h h.contMDiff) m (Fin.last _)).ord x}
      ((L.pullback h hh).toSuccession.strictTransformSeq (⇑h ⁻¹' H) (Fin.last _)) := by
  rw [markedTransformSeq_last_pullbackLiftLast L h hh J E₀ m hge,
    strictTransformSeq_last_pullbackLiftLast L h hh H]
  refine Set.disjoint_left.mpr fun x hx hxH => ?_
  exact Set.disjoint_left.mp hL (hx.trans_eq (IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
    (isLocalDiffeomorph_pullbackLiftLast L h hh x))) hxH

/-- **The clause of Lemma 102 (1) survives the deletion of the empty blow-ups**: the last stage of
the cleaned sequence is the last stage of the sequence through the isomorphism `eraseEmptyLast`
(`markedTransformSeq_last_eraseEmpty`, `strictTransformSeq_last_eraseEmpty`). -/
theorem disjoint_setOf_le_ord_strictTransformSeq_eraseEmpty (L : BlowUpSequence ψ₀ M)
    (J E₀ : IdealSheaf M) (m : ℕ) (hge : L.toSuccession.IsOfOrderGe J m E₀)
        {H : Set M}
    (hH : IsClosed H)
    (hL : Disjoint {y | (m : ℕ∞) ≤ (L.toSuccession.markedTransformSeq J m (Fin.last _)).ord y}
      (L.toSuccession.strictTransformSeq H (Fin.last _))) :
    Disjoint {x | (m : ℕ∞) ≤ (L.eraseEmpty.toSuccession.markedTransformSeq J m (Fin.last _)).ord x}
      (L.eraseEmpty.toSuccession.strictTransformSeq H (Fin.last _)) := by
  rw [markedTransformSeq_last_eraseEmpty L J E₀ m hge, strictTransformSeq_last_eraseEmpty L hH]
  refine Set.disjoint_left.mpr fun x hx hxH => ?_
  exact Set.disjoint_left.mp hL (hx.trans_eq (IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
    (Diffeomorph.isLocalDiffeomorph L.eraseEmptyLast.symm x))) hxH

end AnalyticManifold.BlowUpSequence

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

variable {s : ℕ} (bd : BDanFamData ψ₀ s) (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BOClass s T)

/-- Step 2.1 of the proof of [Kol07, Theorem 103] along the processed members, per open
([Kol07, 104, Step 2.1.j]: "`Π^{-1}_{r(j)*}(E^i) ∩ cosupp(I_{r(j)}, m) = ∅` for `i ≤ j`"): **after a
member has been processed, the cosupport of the controlled transform misses its strict transform,
at every later state of the chain**. For the member processed last, this is Lemma 102 (1) of the
family at that link (`bd.cosupp_disjoint`; its weak transform is the controlled one by
`bd.isOfOrder`), read on the link's open through the lift of the restriction and carried through
the concatenation (`disjoint_concat_of_disjoint`); for a member processed before, the clause at the
previous state restricted to the smaller open persists along the appended sequence of order `≥ s`
(`disjoint_setOf_le_ord_markedTransformSeq_strictTransformSeq`). -/
theorem ChainState.step21FamAux_cosupp_disjoint (W : ℕ → Opens M) (r : ℕ)
    (hW : ∀ k, IsCompact (closure (W k : Set M)))
    (hWsub : ∀ k, k < r → closure (W (k + 1) : Set M) ⊆ W k) :
    ∀ (l : List T.F.ι) (hl : l.length ≤ r) (j : T.F.ι), j ∈ l →
    Disjoint
      {x | (s : ℕ∞) ≤ ((step21FamAux T s bd hT W r hW hWsub l hl).L.toSuccession.markedTransformSeq
        (T.pullback (M.inclusion (W l.length)) (isLocalDiffeomorph_inclusion M _)).I s
        (Fin.last _)).ord x}
      ((step21FamAux T s bd hT W r hW hWsub l hl).L.toSuccession.strictTransformSeq
        ((T.pullback (M.inclusion (W l.length)) (isLocalDiffeomorph_inclusion M _)).F.hyp j)
        (Fin.last _))
  | [], _, _, hj => absurd hj List.not_mem_nil
  | k :: l, hl, j, hj => by
    have hlm : l.length ≤ r := Nat.le_of_succ_le hl
    have hVW : closure (W (l.length + 1) : Set M) ⊆ W l.length := hWsub l.length hl
    -- the state so far and the link's data
    set st := step21FamAux T s bd hT W r hW hWsub l hlm with hst
    have hTW : AnalyticTriple.BOClass s
        (T.pullback (M.inclusion (W l.length)) (isLocalDiffeomorph_inclusion M _)) :=
      boClass_pullback_inclusion_of_boClass T (W l.length) hT
    have hI' : ((T.pullback (M.inclusion (W l.length)) (isLocalDiffeomorph_inclusion M _)).pullback
        (M.restrictLE (ChainState.le_of_closure_subset hVW))
        (isLocalDiffeomorph_restrictLE _)).I =
        (T.pullback (M.inclusion (W (l.length + 1))) (isLocalDiffeomorph_inclusion M _)).I :=
      congrArg AnalyticTriple.I
        (AnalyticTriple.pullback_inclusion_restrictLE T (ChainState.le_of_closure_subset hVW))
    change Disjoint
      {x | (s : ℕ∞) ≤ ((st.link T s bd hT k (hW _) hVW).L.toSuccession.markedTransformSeq
        (T.pullback (M.inclusion (W (l.length + 1))) (isLocalDiffeomorph_inclusion M _)).I s
        (Fin.last _)).ord x}
      ((st.link T s bd hT k (hW _) hVW).L.toSuccession.strictTransformSeq
        ((T.pullback (M.inclusion (W (l.length + 1))) (isLocalDiffeomorph_inclusion M _)).F.hyp j)
        (Fin.last _))
    rw [ChainState.link_L, ← hI']
    unfold BlowUpSequence.shrinkAppend
    apply BlowUpSequence.disjoint_concat_of_disjoint
    -- Lemma 102's data at the link: the induced triple, the member, the open, the value
    have hord := bd.isOfOrder
      ((T.pullback (M.inclusion (W l.length)) (isLocalDiffeomorph_inclusion M _)).induced s st.L
        st.hge)
      (AnalyticTriple.boClass_induced _ s st.L st.hge hTW)
      (st.L.toSuccession.originalIdx
        (T.pullback (M.inclusion (W l.length)) (isLocalDiffeomorph_inclusion M _)).F (Fin.last _) k)
      (st.L.liftRange (M.restrictLE (ChainState.le_of_closure_subset hVW))
        (isLocalDiffeomorph_restrictLE _))
      (st.L.isCompact_closure_liftRange (M.restrictLE (ChainState.le_of_closure_subset hVW))
        (isLocalDiffeomorph_restrictLE _)
        (isCompact_closure_range_restrictLE (ChainState.le_of_closure_subset hVW) (hW _) hVW))
    -- the ideal and the member of the induced triple restricted to the range, pulled back along
    -- the corestricted lift, are the controlled transform and the strict transform along `P`
    have hideal : Manifold.IdealSheaf.pullback _ (st.L.liftCorestrict (M.restrictLE
        (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _)).contMDiff
        (((T.pullback (M.inclusion (W l.length)) (isLocalDiffeomorph_inclusion M _)).induced s st.L
          st.hge).pullback
          ((st.L.stage (Fin.last _)).inclusion (st.L.liftRange
            (M.restrictLE (ChainState.le_of_closure_subset hVW)) (isLocalDiffeomorph_restrictLE _)))
          (isLocalDiffeomorph_inclusion _ _)).I =
        (st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _)).toSuccession.markedTransformSeq
          ((T.pullback (M.inclusion (W l.length)) (isLocalDiffeomorph_inclusion M _)).pullback
            (M.restrictLE (ChainState.le_of_closure_subset hVW))
            (isLocalDiffeomorph_restrictLE _)).I s (Fin.last _) :=
      (IdealSheaf.pullback_comp _ _ _).trans
        (BlowUpSequence.markedTransformSeq_last_pullbackLiftLast st.L
          (M.restrictLE (ChainState.le_of_closure_subset hVW)) (isLocalDiffeomorph_restrictLE _)
          _ _ s st.hge).symm
    have hset : ⇑(st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _)) ⁻¹'
        (((T.pullback (M.inclusion (W l.length)) (isLocalDiffeomorph_inclusion M _)).induced s st.L
          st.hge).pullback
          ((st.L.stage (Fin.last _)).inclusion (st.L.liftRange
            (M.restrictLE (ChainState.le_of_closure_subset hVW)) (isLocalDiffeomorph_restrictLE _)))
          (isLocalDiffeomorph_inclusion _ _)).F.hyp
          (st.L.toSuccession.originalIdx
            (T.pullback (M.inclusion (W l.length)) (isLocalDiffeomorph_inclusion M _)).F
            (Fin.last _) k) =
        (st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _)).toSuccession.strictTransformSeq
          (((T.pullback (M.inclusion (W l.length)) (isLocalDiffeomorph_inclusion M _)).pullback
            (M.restrictLE (ChainState.le_of_closure_subset hVW))
            (isLocalDiffeomorph_restrictLE _)).F.hyp k) (Fin.last _) :=
      (congrArg (fun S => ⇑(st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _)) ⁻¹'
          (⇑((st.L.stage (Fin.last _)).inclusion (st.L.liftRange
            (M.restrictLE (ChainState.le_of_closure_subset hVW))
            (isLocalDiffeomorph_restrictLE _))) ⁻¹' S))
        (st.L.toSuccession.hyp_originalIdx
          (T.pullback (M.inclusion (W l.length)) (isLocalDiffeomorph_inclusion M _)).F
          (Fin.last _) k)).trans
        (BlowUpSequence.strictTransformSeq_last_pullbackLiftLast st.L
          (M.restrictLE (ChainState.le_of_closure_subset hVW)) (isLocalDiffeomorph_restrictLE _)
          _).symm
    rcases List.mem_cons.mp hj with rfl | hjl
    · -- the member just processed: Lemma 102 (1) of the family at the link, pulled back
      have hc := bd.cosupp_disjoint
        ((T.pullback (M.inclusion (W l.length)) (isLocalDiffeomorph_inclusion M _)).induced s st.L
          st.hge)
        (AnalyticTriple.boClass_induced _ s st.L st.hge hTW)
        (st.L.toSuccession.originalIdx
          (T.pullback (M.inclusion (W l.length)) (isLocalDiffeomorph_inclusion M _)).F (Fin.last _)
          j)
        (st.L.liftRange (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _))
        (st.L.isCompact_closure_liftRange (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _)
          (isCompact_closure_range_restrictLE (ChainState.le_of_closure_subset hVW) (hW _) hVW))
      rw [← hord.markedTransformSeq_eq_weakTransformSeq] at hc
      have hc' := BlowUpSequence.disjoint_setOf_le_ord_strictTransformSeq_pullback _
        (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _))
        (st.L.isLocalDiffeomorph_liftCorestrict _ _) _ _ s hord.isOfOrderGe _ hc
      rw [hideal, hset] at hc'
      exact hc'
    · -- a member processed before: its clause persists along a sequence of order `≥ s`
      have hdis := BlowUpSequence.disjoint_setOf_le_ord_strictTransformSeq_pullback st.L
        (M.restrictLE (ChainState.le_of_closure_subset hVW)) (isLocalDiffeomorph_restrictLE _)
        _ _ s st.hge _ (step21FamAux_cosupp_disjoint W r hW hWsub l hlm j hjl)
      have hQ : ((bd.fam _ _ _).seqOn _ _).pullback
          (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
            (isLocalDiffeomorph_restrictLE _))
          (st.L.isLocalDiffeomorph_liftCorestrict _ _) |>.toSuccession.IsOfOrderGe
          (Manifold.IdealSheaf.pullback _ (st.L.liftCorestrict (M.restrictLE
              (ChainState.le_of_closure_subset hVW))
              (isLocalDiffeomorph_restrictLE _)).contMDiff
            (((T.pullback (M.inclusion (W l.length)) (isLocalDiffeomorph_inclusion M _)).induced s
              st.L st.hge).pullback
              ((st.L.stage (Fin.last _)).inclusion (st.L.liftRange
                (M.restrictLE (ChainState.le_of_closure_subset hVW))
                (isLocalDiffeomorph_restrictLE _)))
              (isLocalDiffeomorph_inclusion _ _)).I) s
          ((((T.pullback (M.inclusion (W l.length)) (isLocalDiffeomorph_inclusion M _)).induced s
              st.L st.hge).pullback
              ((st.L.stage (Fin.last _)).inclusion (st.L.liftRange
                (M.restrictLE (ChainState.le_of_closure_subset hVW))
                (isLocalDiffeomorph_restrictLE _)))
              (isLocalDiffeomorph_inclusion _ _)).pullback
            (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
              (isLocalDiffeomorph_restrictLE _))
            (st.L.isLocalDiffeomorph_liftCorestrict _ _)).F.idealSheaf :=
        AnalyticTriple.isOfOrderGe_pullback _ s _ hord.isOfOrderGe _ _
      rw [hideal] at hQ
      exact FiniteSuccession.disjoint_setOf_le_ord_markedTransformSeq_strictTransformSeq _ hQ
        ((st.L.pullback _ _).toSuccession.isClosed_strictTransformSeq _
          (((T.pullback (M.inclusion (W l.length)) (isLocalDiffeomorph_inclusion M _)).pullback
            (M.restrictLE (ChainState.le_of_closure_subset hVW))
            (isLocalDiffeomorph_restrictLE _)).isSnc.1 j).isClosed _)
        hdis _

/-- At the end of Step 2.1 the cosupport `cosupp(I_r, m)` "is disjoint from `Π^{-1}_* E`" (Step 2.1
of the proof of [Kol07, Theorem 103]; [Kol07, 104, Step 2.1.j]), per
relatively compact open: **at the end of Step 2.1 on `U` the cosupport of the controlled transform
misses the strict transform of every member of `E|_U`**. The chain's clause
(`step21FamAux_cosupp_disjoint`) for a nonempty member, restricted to `U` with the empty blow-ups
deleted; an empty member has empty strict transform. -/
theorem step21FamOn_cosupp_disjoint (bd : BDanFamData ψ₀ s) (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BOClass s T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (j : T.F.ι) :
    Disjoint
      {x | (s : ℕ∞) ≤
        ((step21FamOn T s bd hT U hU).toSuccession.markedTransformSeq
          (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I s (Fin.last _)).ord x}
      ((step21FamOn T s bd hT U hU).toSuccession.strictTransformSeq
        ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.hyp j)
        (Fin.last _)) := by
  by_cases hj : T.F.hyp j = ∅
  · have h0 : (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.hyp j = ∅ := by
      change ⇑(M.inclusion U) ⁻¹' T.F.hyp j = ∅
      rw [hj, Set.preimage_empty]
    rw [h0, FiniteSuccession.strictTransformSeq_empty]
    exact Set.disjoint_empty _
  · have hmem : j ∈ (T.F.nonemptyList hT.2.2).reverse :=
      List.mem_reverse.mpr ((T.F.mem_nonemptyList hT.2.2 j).mpr hj)
    have hUW := le_chainOpens_last (exhaustion M) hU (memberCount T s hT)
    have hchain := ChainState.step21FamAux_cosupp_disjoint bd T hT
      (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) (memberCount T s hT))
      (memberCount T s hT) (isCompact_closure_chainOpens (exhaustion M) _ _)
      (fun _ hk => closure_chainOpens_succ_subset (exhaustion M) _ _ hk)
      (T.F.nonemptyList hT.2.2).reverse le_rfl j hmem
    have hres := BlowUpSequence.disjoint_setOf_le_ord_strictTransformSeq_pullback _
        (M.restrictLE hUW)
      (isLocalDiffeomorph_restrictLE hUW) _ _ s (step21FamChain T s bd hT U hU).hge _ hchain
    have hI' : ((T.pullback (M.inclusion _) (isLocalDiffeomorph_inclusion M _)).pullback
        (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE hUW)).I =
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I :=
      congrArg AnalyticTriple.I (AnalyticTriple.pullback_inclusion_restrictLE T hUW)
    unfold step21FamOn
    rw [← hI']
    exact BlowUpSequence.disjoint_setOf_le_ord_strictTransformSeq_eraseEmpty _ _ _ s
      (AnalyticTriple.isOfOrderGe_pullback _ s _ (step21FamChain T s bd hT U hU).hge _ _)
      (((T.pullback (M.inclusion _) (isLocalDiffeomorph_inclusion M _)).pullback
        (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE hUW)).isSnc.1 j).isClosed hres

end Hironaka.Manifold
