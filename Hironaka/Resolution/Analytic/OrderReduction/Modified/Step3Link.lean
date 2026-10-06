/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2Chain
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.MonomialStep3Fam
import Hironaka.Manifold.BlowUp.Transform.DerivTransform
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1Measure
import Hironaka.Resolution.Analytic.OrderReduction.ChainTransportPrep
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bFunctor
import Hironaka.Resolution.Analytic.OrderReduction.Step21Functoriality
import Hironaka.Resolution.Analytic.Tuning
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The monomial step of the marked order reduction as one link, and clause (1) of the theorem

The last step of Kollár's proof of the marked order reduction theorem [Kol07, Theorem 107] runs
the monomial procedure on the monomial part `M(I)`, once the separation step has made the
cosupports of `(I, m)` and of `N(I)` disjoint [Kol07, 111, Step 3]. Here the procedure enters
through the structure `MonomialStep3Fam` (a family functor for `(M(𝓘), m)` whose last marked
transform of `(M(𝓘), m)` has order `< m`), read at the induced triple of the exit state of the
separation step on the reading open and appended by `ChainState.linkWith` (`SState.step3Link`);
the order clause `≥ m` for `𝓘` follows from the one for `M(𝓘)` and `𝓘 ⊆ M(𝓘)`.

**Clause (1) of the theorem**, `max-ord I_r < m`, for `𝓘` itself. Kollár replaces `X` by
`X ∖ cosupp N(I)` and assumes `I = M(I)` [Kol07, 111, Step 2]. Here the procedure runs on
`(M(𝓘), m, E)` on the whole last stage of the separation step, and the clause for `𝓘` is proved
pointwise (`ord_markedTransformSeq_lt_of_sepOrdLe_zero`):

* at a point of the last stage over `cosupp N(𝓘)`: by the exit of the separation step,
  `ord 𝓘 < m` there, so `ord M(𝓘) < m`; no centre of the procedure meets the fibre over such a
  point, since the centres lie where the marked transform of `(M(𝓘), m)` has order `≥ m`, while
  over the point that order is the order of `M(𝓘)` (off the centres a blow-up is a local analytic
  isomorphism and the marked transform is the pull-back, `IsBlowUp.isLocalDiffeomorphOn_compl`,
  `birationalTransform_stalkIdeal_of_notMem`); so the marked transform of `(𝓘, m)` over the point
  is the pull-back of `𝓘`, of order `< m` (`IsOfOrderGe.forall_notMem_center_of_ord_lt`,
  `ord_markedTransformSeq_eq_of_forall_notMem`);
* at a point off it: `𝓘 = M(𝓘)` on the open complement of `cosupp N(𝓘)`
  (`stalkIdeal_eq_monomialPart_of_notMem_cosupport`), so the marked transforms of `(𝓘, m)` and of
  `(M(𝓘), m)` agree over that open (`BlowUpSequence.markedTransformSeq_last_pullbackLiftLast`), and
  the exit property of the procedure bounds the latter.

Transported along the lift and through the concatenation this gives `SState.step3Link_ord_lt`.
The module ends with **the terminal state of the three steps**, `step23ChainState`, on the open
`step23ChainOpen ⊇ closure U`, with `step23ChainState_ord_lt`; the sequence over `U` (`bmoSeqOn`)
is its restriction to `U` with the empty blow-ups deleted. The scheme-theoretic counterpart of
the clause is `Hironaka.BMO.maxOrd_markedTransformSeq_step3Seq_lt`.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace AnalyticManifold Filter
open scoped Manifold ContDiff

universe u

/-! ### The iso-locus: off the centres, the marked transform is the pull-back -/

namespace AnalyticManifold.FiniteSuccession

open Manifold Hironaka.Manifold.BMOmod

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} {S : FiniteSuccession M} {I J E₀ : IdealSheaf M} {m : ℕ}

/-- One step of the iso-locus: at a point of stage `i + 1` whose image is not in the centre `Z_i`,
the order of the marked transform is the order of the previous marked transform at the image —
the blow-up is a local analytic isomorphism there (`IsBlowUp.isLocalDiffeomorphOn_compl`) and the
marked transform's stalk is the pull-back's (`birationalTransform_stalkIdeal_of_notMem`). -/
theorem ord_markedTransformSeq_succ_of_notMem (hS : S.IsOfOrderGe I m E₀) (i : Fin S.length)
    (y : S.stage i.succ) (hnot : S.map i y ∉ (S.center i).support) :
    (S.markedTransformSeq I m i.succ).ord y =
      (S.markedTransformSeq I m i.castSucc).ord (S.map i y) := by
  have hloc : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω (S.map i) y :=
    (S.isBlowUp_map i).isLocalDiffeomorphOn_compl ⟨y, hnot⟩
  have e : (S.markedTransformSeq I m i.succ).ord y =
      ((S.markedTransformSeq I m i.castSucc).pullback (S.map i)
        (S.isBlowUp_map i).contMDiff).ord y := by
    rw [markedTransformSeq_succ]
    exact congrArg IsLocalRing.ord (birationalTransform_stalkIdeal_of_notMem
      (S.isClosedSubmanifold_center i) (S.isBlowUp_map i) (hS.le_ordAlong_center i) hnot)
  rw [e, IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _ hloc]

/-- If no centre of the list meets the fibre over `x`, the marked transform at any point of stage
`i` over `x` has the order of the ideal at `x`: `ord_markedTransformSeq_succ_of_notMem` along the
stages. -/
theorem ord_markedTransformSeq_eq_of_forall_notMem (hS : S.IsOfOrderGe I m E₀) {x : M}
    (hx : ∀ (i : Fin S.length) (y : S.stage i.castSucc),
      S.stageMap i.castSucc y = x → y ∉ (S.center i).support)
    (i : Fin (S.length + 1)) (y : S.stage i) (hy : S.stageMap i y = x) :
    (S.markedTransformSeq I m i).ord y = I.ord x := by
  induction i using Fin.induction with
  | zero => exact congrArg I.ord hy
  | succ i ih =>
    have hy' : S.stageMap i.castSucc (S.map i y) = x := hy
    rw [ord_markedTransformSeq_succ_of_notMem hS i y (hx i (S.map i y) hy')]
    exact ih (S.map i y) hy'

/-- Along a list of order `≥ m` for `(J, m)`, no centre meets the fibre over a point `x` with
`ord_x J < m`: by induction along the stages the marked transform keeps the order `ord_x J < m`
over `x` (the iso-locus step), while a centre through a point has order `≥ m` there
(`ordAlongIdeal_le_ord_of_mem_support`). This is "the center of any further blow-up is contained
in `cosupp(I, m)`" [Kol07, 111, Step 2]. -/
theorem IsOfOrderGe.forall_notMem_center_of_ord_lt (hS : S.IsOfOrderGe J m E₀) {x : M}
    (hlt : J.ord x < (m : ℕ∞)) :
    ∀ (i : Fin S.length) (y : S.stage i.castSucc),
      S.stageMap i.castSucc y = x → y ∉ (S.center i).support := by
  suffices key : ∀ (i : Fin (S.length + 1)) (y : S.stage i), S.stageMap i y = x →
      (S.markedTransformSeq J m i).ord y = J.ord x by
    intro i y hy hmem
    have h1 := hS.le_ordAlong i hmem
    have h2 := ordAlongIdeal_le_ord_of_mem_support (S.center i)
      (S.markedTransformSeq J m i.castSucc) hmem
    rw [key i.castSucc y hy] at h2
    exact absurd (h1.trans h2) (not_le.mpr hlt)
  intro i
  induction i using Fin.induction with
  | zero => intro y hy; exact congrArg J.ord hy
  | succ i ih =>
    intro y hy
    have hy' : S.stageMap i.castSucc (S.map i y) = x := hy
    have hnot : S.map i y ∉ (S.center i).support := by
      intro hmem
      have h1 := hS.le_ordAlong i hmem
      have h2 := ordAlongIdeal_le_ord_of_mem_support (S.center i)
        (S.markedTransformSeq J m i.castSucc) hmem
      rw [ih (S.map i y) hy'] at h2
      exact absurd (h1.trans h2) (not_le.mpr hlt)
    rw [ord_markedTransformSeq_succ_of_notMem hS i y hnot]
    exact ih (S.map i y) hy'

end AnalyticManifold.FiniteSuccession

namespace Hironaka.Manifold.BMO

open _root_.Manifold

open Hironaka.Manifold.BMOmod

/-! ### Clause (1) of the theorem for `𝓘` from the exit property of the monomial procedure -/

section ClauseOne

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- The separation invariant restricts along a local analytic isomorphism (pointwise;
`NonmonomialComap` for the nonmonomial part, `ord_pullback_of_isLocalDiffeomorphAt`). -/
theorem sepOrdLe_pullback (hcomp : NonmonomialComap.{u} ψ₀) {S : AnalyticTriple ψ₀ M} {m s : ℕ}
    (h : SepOrdLe S m s) {N : AnalyticManifold.{u} 𝕜 E} (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) : SepOrdLe (S.pullback g hg) m s := by
  intro y hy
  rw [hcomp S g hg]
  change ((nonmonomialTriple S).I.pullback _ _).ord y ≤ _
  change (m : ℕ∞) ≤ (S.I.pullback _ g.contMDiff).ord y at hy
  rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _ (hg y)] at hy ⊢
  exact h _ hy

/-- **Clause (1) of [Kol07, Theorem 107] from the exit property of the monomial procedure**: for a
triple `(M, 𝓘, E)` at the exit of the separation step (`SepOrdLe … m 0`) and a list `L` of order
`≥ m` for `(M(𝓘), m)` whose last marked transform of `(M(𝓘), m)` has order `< m` everywhere, the
last marked transform of `(𝓘, m)` has order `< m` at every point. Over `cosupp N(𝓘)` no centre
meets the fibre and the marked transform is the pull-back of `𝓘`, of order `ord 𝓘 < m`; off it,
`𝓘 = M(𝓘)` on the open complement, so the two marked transforms agree there. -/
theorem ord_markedTransformSeq_lt_of_sepOrdLe_zero {S' : AnalyticTriple ψ₀ M} {m : ℕ}
    (hsep : SepOrdLe S' m 0) (L : BlowUpSequence ψ₀ M)
    (hL : L.toSuccession.IsOfOrderGe S'.I m S'.F.idealSheaf)
    (hM : L.toSuccession.IsOfOrderGe (monomialPart S'.F S'.isSnc S'.I) m S'.F.idealSheaf)
    (hMlt : ∀ z, (L.toSuccession.markedTransformSeq (monomialPart S'.F S'.isSnc S'.I) m
      (Fin.last _)).ord z < (m : ℕ∞))
    (z : L.stage (Fin.last _)) :
    (L.toSuccession.markedTransformSeq S'.I m (Fin.last _)).ord z < (m : ℕ∞) := by
  by_cases hxN : L.toSuccession.stageMap (Fin.last _) z ∈ (nonmonomialTriple S').I.support
  · -- over `cosupp N(𝓘)`: the pull-back of `𝓘`, of order `< m`
    have hlt := hsep.ord_lt_of_mem_cosupport hxN
    have hMlt' : (monomialPart S'.F S'.isSnc S'.I).ord (L.toSuccession.stageMap (Fin.last _) z) <
        (m : ℕ∞) :=
      lt_of_le_of_lt (IdealSheaf.ord_anti (le_monomialPart S'.F S'.isSnc S'.I) _) hlt
    rw [FiniteSuccession.ord_markedTransformSeq_eq_of_forall_notMem hL
      (hM.forall_notMem_center_of_ord_lt hMlt') (Fin.last _) z rfl]
    exact hlt
  · -- off it: `𝓘 = M(𝓘)` on the open complement, the marked transforms agree over it
    let V₀ : Opens M := ⟨((nonmonomialTriple S').I.support)ᶜ,
      (nonmonomialTriple S').I.isOpen_compl_support⟩
    have hIM : S'.I.pullback _ (M.inclusion V₀).contMDiff =
        (monomialPart S'.F S'.isSnc S'.I).pullback _ (M.inclusion V₀).contMDiff := by
      refine IdealSheaf.ext fun b => ?_
      rw [IdealSheaf.stalkIdeal_pullback, IdealSheaf.stalkIdeal_pullback]
      exact congrArg _ (stalkIdeal_eq_monomialPart_of_notMem_cosupport S' b.2)
    have hz : z ∈ Set.range (L.pullbackLiftLast (M.inclusion V₀)
        (isLocalDiffeomorph_inclusion M V₀)) := by
      rw [BlowUpSequence.range_pullbackLiftLast, Manifold.range_inclusion]
      exact hxN
    obtain ⟨z', hz'⟩ := hz
    have e1 := BlowUpSequence.markedTransformSeq_last_pullbackLiftLast L (M.inclusion V₀)
      (isLocalDiffeomorph_inclusion M V₀) S'.I S'.F.idealSheaf m hL
    have e2 := BlowUpSequence.markedTransformSeq_last_pullbackLiftLast L (M.inclusion V₀)
      (isLocalDiffeomorph_inclusion M V₀) (monomialPart S'.F S'.isSnc S'.I) S'.F.idealSheaf m hM
    rw [hIM] at e1
    have e3 := e1.symm.trans e2
    have h1 := IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _
      (L.pullbackLiftLast (M.inclusion V₀) (isLocalDiffeomorph_inclusion M V₀)).contMDiff
      (L.toSuccession.markedTransformSeq S'.I m (Fin.last _))
      (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L (M.inclusion V₀)
        (isLocalDiffeomorph_inclusion M V₀) z')
    have h2 := IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _
      (L.pullbackLiftLast (M.inclusion V₀) (isLocalDiffeomorph_inclusion M V₀)).contMDiff
      (L.toSuccession.markedTransformSeq (monomialPart S'.F S'.isSnc S'.I) m (Fin.last _))
      (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L (M.inclusion V₀)
        (isLocalDiffeomorph_inclusion M V₀) z')
    rw [← hz']
    calc (L.toSuccession.markedTransformSeq S'.I m (Fin.last _)).ord
          (L.pullbackLiftLast (M.inclusion V₀) (isLocalDiffeomorph_inclusion M V₀) z')
        = ((L.toSuccession.markedTransformSeq S'.I m (Fin.last _)).pullback
            (L.pullbackLiftLast (M.inclusion V₀) (isLocalDiffeomorph_inclusion M V₀))
            (L.pullbackLiftLast (M.inclusion V₀) (isLocalDiffeomorph_inclusion M V₀)).contMDiff).ord
            z' := h1.symm
      _ = ((L.toSuccession.markedTransformSeq (monomialPart S'.F S'.isSnc S'.I) m
            (Fin.last _)).pullback
            (L.pullbackLiftLast (M.inclusion V₀) (isLocalDiffeomorph_inclusion M V₀))
            (L.pullbackLiftLast (M.inclusion V₀) (isLocalDiffeomorph_inclusion M V₀)).contMDiff).ord
            z' :=
          congrArg (fun J : AnalyticManifold.IdealSheaf ((L.pullback (M.inclusion V₀)
            (isLocalDiffeomorph_inclusion M V₀)).stage (Fin.last _)) => J.ord z') e3
      _ = (L.toSuccession.markedTransformSeq (monomialPart S'.F S'.isSnc S'.I) m
            (Fin.last _)).ord
            (L.pullbackLiftLast (M.inclusion V₀) (isLocalDiffeomorph_inclusion M V₀) z') := h2
      _ < (m : ℕ∞) := hMlt _

end ClauseOne

/-! ### The monomial procedure as one link on the exit state of the separation step -/

section Step3

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  {T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M} {m : ℕ}
  (hT : AnalyticTriple.BMOClass m T) (st3 : MonomialStep3Fam.{u} 𝕜 n m)
  {W : Opens M} (st : SState T m W 0) {V : Opens M} (hV : IsCompact (closure (V : Set M)))
  (hVW : closure (V : Set M) ⊆ W)

/-- **The value of the monomial step**: the procedure `st3` at the induced triple of the exit state
of the separation step, read on the reading open (the lifted range of `V ⊆ W`). -/
def SState.step3Value :
    BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      ((st.L.stage (Fin.last _)).restrict (ChainState.readOpen T m st.toChainState hVW)) :=
  (st3.functor.fam (ChainState.inducedTriple T m st.toChainState)
    (bmoClass_inducedTriple T m hT st.toChainState)).seqOn
    (ChainState.readOpen T m st.toChainState hVW)
    (ChainState.isCompact_closure_readOpen T m st.toChainState hV hVW)

/-- The value is of order `≥ m` for `(M(𝓘), m)` (`st3.isOfOrderGe`), hence for `(𝓘, m)` since
`𝓘 ⊆ M(𝓘)` (`IsOfOrderGe.of_le`); this is the order clause `ChainState.linkWith` requires. -/
theorem SState.step3Value_isOfOrderGe :
    (st.step3Value hT st3 hV hVW).toSuccession.IsOfOrderGe
      ((ChainState.inducedTriple T m st.toChainState).pullback
        ((st.L.stage (Fin.last _)).inclusion (ChainState.readOpen T m st.toChainState hVW))
        (isLocalDiffeomorph_inclusion _ _)).I m
      (((ChainState.inducedTriple T m st.toChainState).pullback
        ((st.L.stage (Fin.last _)).inclusion (ChainState.readOpen T m st.toChainState hVW))
        (isLocalDiffeomorph_inclusion _ _)).F.idealSheaf) :=
  (st3.isOfOrderGe (ChainState.inducedTriple T m st.toChainState)
    (bmoClass_inducedTriple T m hT st.toChainState) _ _).of_le (le_monomialPart _ _ _)

/-- **The monomial procedure as one link** on the exit state of the separation step
[Kol07, 111, Step 3]: its value appended to the list restricted to `V`. -/
def SState.step3Link : ChainState T m V :=
  ChainState.linkWith T m st.toChainState hV hVW
    (st3.functor.fam (ChainState.inducedTriple T m st.toChainState)
      (bmoClass_inducedTriple T m hT st.toChainState))
    (st.step3Value_isOfOrderGe hT st3 hV hVW)

/-- The link is the shrink-and-append step with the value of the monomial step. -/
theorem SState.step3Link_L :
    (st.step3Link hT st3 hV hVW).L =
      st.L.shrinkAppend (M.restrictLE (ChainState.le_of_closure_subset hVW))
        (isLocalDiffeomorph_restrictLE _) (st.step3Value hT st3 hV hVW) := rfl

/-- **After the monomial step the marked transform of `(𝓘, m)` has order `< m` at every point of
the last stage** (clause (1) of [Kol07, Theorem 107]): `ord_markedTransformSeq_lt_of_sepOrdLe_zero`
at the restricted induced triple (the exit invariant of the separation step restricted to the
reading open, and the two properties of `st3`), pulled back along the corestricted lift and passed
through the concatenation (`pred_induced_concat`). -/
theorem SState.step3Link_ord_lt
    (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))) :
    ∀ x, (ChainState.inducedTriple T m (st.step3Link hT st3 hV hVW)).I.ord x < (m : ℕ∞) := by
  have hL₀' := st.step3Value_isOfOrderGe hT st3 hV hVW
  have hL₁ := st.toChainState.pullback_restrictLE_isOfOrderGe hVW
  have h₂ := AnalyticTriple.isOfOrderGe_pullback _ m (st.step3Value hT st3 hV hVW) hL₀'
    (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
      (isLocalDiffeomorph_restrictLE _)) (st.L.isLocalDiffeomorph_liftCorestrict _ _)
  have e := st.toChainState.inducedTriple_pullback_liftCorestrict_eq hVW
  have hL₂ : ((st.step3Value hT st3 hV hVW).pullback
      (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
        (isLocalDiffeomorph_restrictLE _))
      (st.L.isLocalDiffeomorph_liftCorestrict _ _)).toSuccession.IsOfOrderGe
      ((T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).induced m
        (st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _)) hL₁).I m
      ((T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).induced m
        (st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _)) hL₁).F.idealSheaf := by
    rw [← e]; exact h₂
  have hmain : ∀ y, ((((T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).induced m
      (st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
        (isLocalDiffeomorph_restrictLE _)) hL₁).induced m
      ((st.step3Value hT st3 hV hVW).pullback
        (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _))
        (st.L.isLocalDiffeomorph_liftCorestrict _ _)) hL₂).I).ord y < (m : ℕ∞) := by
    rw [← AnalyticTriple.induced_congr e m _ h₂ hL₂,
      ← AnalyticTriple.induced_pullback _ m (st.step3Value hT st3 hV hVW) hL₀'
        (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _)) (st.L.isLocalDiffeomorph_liftCorestrict _ _) h₂]
    intro y
    change (((((ChainState.inducedTriple T m st.toChainState).pullback
      ((st.L.stage (Fin.last _)).inclusion (ChainState.readOpen T m st.toChainState hVW))
      (isLocalDiffeomorph_inclusion _ _)).induced m (st.step3Value hT st3 hV hVW)
      hL₀')).I.pullback _ _).ord y < _
    rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
      (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _ y)]
    exact ord_markedTransformSeq_lt_of_sepOrdLe_zero
      (sepOrdLe_pullback hcomp st.sep _ (isLocalDiffeomorph_inclusion _ _))
      (st.step3Value hT st3 hV hVW) hL₀'
      (st3.isOfOrderGe (ChainState.inducedTriple T m st.toChainState)
        (bmoClass_inducedTriple T m hT st.toChainState) _ _)
      (st3.ord_lt (ChainState.inducedTriple T m st.toChainState)
        (bmoClass_inducedTriple T m hT st.toChainState) _ _) _
  change ∀ y, ((T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).induced m
      ((st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
      (isLocalDiffeomorph_restrictLE _)).concat ((st.step3Value hT st3 hV
      hVW).pullback (st.L.liftCorestrict (M.restrictLE
      (ChainState.le_of_closure_subset
      hVW)) (isLocalDiffeomorph_restrictLE _)) (st.L.isLocalDiffeomorph_liftCorestrict _ _)))
      _).I.ord
      y < (m : ℕ∞)
  exact AnalyticTriple.pred_induced_concat (fun S => ∀ y, S.I.ord y < (m : ℕ∞)) _ _ _ m hL₁ hL₂ _
    hmain

end Step3

/-! ### The last two steps along an arbitrary shrinking chain, and the terminal state -/

section Continuation

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  {T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M} {m : ℕ}
  (hT : AnalyticTriple.BMOClass m T) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hidN : NonmonomialTransformIdentityMod.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (st3 : MonomialStep3Fam.{u} 𝕜 n m) (hm : 1 ≤ m) (t : ℕ) (ht : 1 ≤ t) (W : ℕ → Opens M)
  (hW : ∀ k, IsCompact (closure (W k : Set M)))
  (hWsub : ∀ k, k < t → closure (W (k + 1) : Set M) ⊆ W k) (st₀ : BState T m (W 0) (t - 1))

/-- **The continuation of the first step by the separation and monomial steps along an arbitrary
shrinking chain** `W 0 ⊇ closure (W 1) ⊇ ⋯ ⊇ W t`: from a state of the first step at the exit
bound `t − 1` on `W 0`, the `t − 1` links of the descent of the separation step (to `W (t − 1)`),
then the link of the monomial step (to `W t`). The number of links is fixed, so two continuations
over different opens align link by link. The canonical instance is `step23ChainState`; the
alignment facts `step23Aux_rel` and `step23Aux_L_indiff` are stated on this general form. -/
def step23Aux : ChainState T m (W t) :=
  (sepDescentState hT bo hcomp hidN hm W hW t (fun k hk => hWsub k hk) (t - 1)
    (SState.ofBState T m st₀) (Nat.sub_le t 1)).step3Link hT st3 (hW t)
    (by have h := hWsub (t - 1) (by omega); rwa [Nat.sub_add_cancel ht] at h)

/-- Clause (1) of [Kol07, Theorem 107] along an arbitrary chain: the last marked transform of the
continuation has order `< m` at every point. -/
theorem step23Aux_ord_lt :
    ∀ x, (ChainState.inducedTriple T m
        (step23Aux hT bo hcomp hidN st3 hm t ht W hW hWsub st₀)).I.ord x < (m : ℕ∞) :=
  (sepDescentState hT bo hcomp hidN hm W hW t (fun k hk => hWsub k hk) (t - 1)
    (SState.ofBState T m st₀) (Nat.sub_le t 1)).step3Link_ord_lt hT st3 (hW t)
    (by have h := hWsub (t - 1) (by omega); rwa [Nat.sub_add_cancel ht] at h) hcomp

end Continuation

section Terminal

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (m : ℕ)
  (hT : AnalyticTriple.BMOClass m T) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hidN : NonmonomialTransformIdentityMod.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (st3 : MonomialStep3Fam.{u} 𝕜 n m) (t : ℕ) (hm : 1 ≤ m) (hmt : m ≤ t) (U : Opens M)
  (hU : IsCompact (closure (U : Set M)))

/-- The open of the terminal state: the `t`-th member of the canonical chain of the separation
step, which contains `closure U`. -/
abbrev step23ChainOpen : Opens M := step2ChainOpens T t U hU t

theorem le_step23ChainOpen : U ≤ step23ChainOpen T t U hU := le_step2ChainOpens T t U hU t

/-- The final state of the first step, read at its exit bound `t − 1` (`stepAChainState_bound`). -/
def stepAExitState : BState T m (step2ChainOpens T t U hU 0) (t - 1) :=
  ⟨(stepAChainState T m hT bo hcomp hid t hm hmt U hU).toChainState,
    stepAChainState_bound T m hT bo hcomp hid t hm hmt U hU⟩

/-- **The terminal chain state of the three steps** [Kol07, 111] on the open
`step23ChainOpen ⊇ closure U`: the state of the first step, the descent of the separation step and
the link of the monomial step along the canonical chain (`step23Aux` at `step2ChainOpens`). The
sequence over `U`, `bmoSeqOn`, is its restriction to `U` with the empty blow-ups deleted. The
scheme-theoretic counterpart is `Hironaka.BMO.bmoSeq` before the restriction. -/
def step23ChainState : ChainState T m (step23ChainOpen T t U hU) :=
  step23Aux hT bo hcomp hidN st3 hm t (hm.trans hmt) (step2ChainOpens T t U hU)
    (isCompact_closure_step2ChainOpens T t U hU)
    (fun k _ => closure_step2ChainOpens_succ_subset T t U hU k)
    (stepAExitState T m hT bo hcomp hid t hm hmt U hU)

/-- Clause (1) of [Kol07, Theorem 107] at the terminal state: the marked transform of `(𝓘, m)` has
order `< m` at every point of the last stage. -/
theorem step23ChainState_ord_lt :
    ∀ x, (ChainState.inducedTriple T m
        (step23ChainState T m hT bo hcomp hid hidN st3 t hm hmt U hU)).I.ord x < (m : ℕ∞) :=
  step23Aux_ord_lt hT bo hcomp hidN st3 hm t (hm.trans hmt) (step2ChainOpens T t U hU)
    (isCompact_closure_step2ChainOpens T t U hU)
    (fun k _ => closure_step2ChainOpens_succ_subset T t U hU k)
    (stepAExitState T m hT bo hcomp hid t hm hmt U hU)

end Terminal

end Hironaka.Manifold.BMO

end
