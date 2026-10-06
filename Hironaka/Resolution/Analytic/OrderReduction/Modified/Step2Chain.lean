/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2Sep
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepAFamily
import Hironaka.Manifold.BlowUp.Transform.MarkedAlgebra
import Hironaka.Manifold.BlowUp.Transform.TuningTransform
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.GoingUp.BoundaryDrop
import Hironaka.Resolution.Analytic.GoingUp.Tools
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Round
import Hironaka.Resolution.Analytic.OrderReduction.BMO.SupPow
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.OrderReduction.Step21Functoriality
import Hironaka.Resolution.Analytic.Tuning
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The separation step of the marked order reduction: the chain state, the link and the descent

The second step of Kollár's proof of the marked order reduction theorem [Kol07, Theorem 107]
lowers the maximal order `s` of the nonmonomial part `N(I)` along `cosupp(I, m)` to `0`, by
applying the order reduction `BO_{n, ms}` to `N(I)^m + I^s` and continuing with `s − 1`
[Kol07, 111, Step 2]. On an analytic manifold each application is a link of the chain of
relatively compact opens on which the sequence is built (`ChainState`), following the links of
the first step (the rounds of order reduction on `N(𝓘)`, `stepAChainState`, with their states
`BState`). This module provides:

* **the facts along a succession**: along a list of order `≥ ms` for `J₁^m + J₂^s` the marked
  transforms of `(J₁^m + J₂^s, ms)` are `mt(J₁, s)^m + mt(J₂, m)^s` at every stage
  (`markedTransformSeq_pow_add_pow`), and such a list is of order `≥ s` for `(J₁, s)` and of order
  `≥ m` for `(J₂, m)` (`IsOfOrderGe.left_of_pow_add_pow`, `IsOfOrderGe.right_of_pow_add_pow`),
  Kollár's remark in [Kol07, 111, Step 2] that a sequence of order `ms` for the sum of powers is one
  of order `s` for the first ideal and of order `m` for the second; the order clause is antitone in
  the ideal
  (`IsOfOrderGe.of_le`); a pointwise predicate on the induced triple passes through a
  concatenation of lists (`AnalyticTriple.pred_induced_concat`);
* **the state** `SState T m W s`: a chain state whose induced triple satisfies the separation
  invariant `SepOrdLe … m s`, entered from the exit bound of the first step
  (`SState.ofNonmonomialOrdLe`);
* **the link** `SState.sepLink` at a bound `s ≥ 1`: the value of `BO_{n, ms}` at the separating
  triple of the induced triple (`sepFunctor`), read on the reading open and appended by
  `ChainState.linkWith`; the order clause `≥ m` for `𝓘` holds by the observation above, and the
  invariant descends to `s − 1`: at the last stage the transform of the separating ideal has
  order `< ms`, i.e. `min(m · ord N_r, s · ord 𝓘_r) < ms`, so `ord N_r < s` on `cosupp(𝓘_r, m)`, and
  the transform identity modulo `N` gives `N(𝓘_r) = N(N_r) ⊇ N_r`, hence `ord N(𝓘_r) ≤ ord N_r`;
* **the descent** `sepDescentAux` and `sepDescentState` over `s = S₀, …, 1`, and its canonical
  instance after the first step, `step2ChainState`, along the chain `step2ChainOpens`: the exit
  open of the first step, then the iterated shrinkings of `closure U` inside it; after `t − 1`
  links the separation bound is `0`, the disjointness of the cosupports (`step2ChainState_sep`).

The scheme-theoretic counterparts are `Hironaka.BMO.step2Round` and `Hironaka.BMO.afterStep2`
with `Hironaka.BMO.sepOrder_afterStep2_eq_zero`.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace AnalyticManifold Filter
open scoped Manifold ContDiff

universe u

/-! ### Facts along a succession -/

namespace AnalyticManifold.FiniteSuccession

open Manifold Hironaka.Manifold.BMOmod

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E} {S : FiniteSuccession M}
  {I J J₁ J₂ E₀ : IdealSheaf M} {m s : ℕ}

/-- Along a list of order `≥ ms` for `J₁^m + J₂^s` (`m, s ≥ 1`), the marked transforms of
`(J₁^m + J₂^s, ms)` are `mt(J₁, s)^m + mt(J₂, m)^s` at every stage: at each centre the observation
of [Kol07, 111, Step 2] gives `ord_Z mt(J₁) ≥ s` and `ord_Z mt(J₂) ≥ m`, and the transform of a
sum of powers is the sum of the powers of the transforms (`birationalTransform_add`,
`birationalTransform_pow`). The scheme-theoretic counterpart is
`Hironaka.Sequence.weakTransformSeq_pow_sup_pow`. -/
theorem markedTransformSeq_pow_add_pow (hm : 1 ≤ m) (hs : 1 ≤ s)
    (h : S.IsOfOrderGe (J₁ ^ m + J₂ ^ s) (m * s) E₀) (i : Fin (S.length + 1)) :
    S.markedTransformSeq (J₁ ^ m + J₂ ^ s) (m * s) i =
      S.markedTransformSeq J₁ s i ^ m + S.markedTransformSeq J₂ m i ^ s := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have hY := S.isClosedSubmanifold_center i
    have hsum : ∀ a ∈ (S.center i).support, ((m * s : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
        hY.idealSheaf (S.markedTransformSeq J₁ s i.castSucc ^ m +
          S.markedTransformSeq J₂ m i.castSucc ^ s) a := by
      intro a ha
      have := h.le_ordAlong_center i a ha
      rwa [ih] at this
    have h1 : ∀ a ∈ (S.center i).support, (s : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf
        (S.markedTransformSeq J₁ s i.castSucc) a := fun a ha =>
      ((IdealSheaf.le_ordAlongIdeal_pow_add_pow_iff hY _ _ hm hs ha).mp (hsum a ha)).1
    have h2 : ∀ a ∈ (S.center i).support, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf
        (S.markedTransformSeq J₂ m i.castSucc) a := fun a ha =>
      ((IdealSheaf.le_ordAlongIdeal_pow_add_pow_iff hY _ _ hm hs ha).mp (hsum a ha)).2
    have h1' : ∀ a ∈ (S.center i).support, ((m * s : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
        hY.idealSheaf (S.markedTransformSeq J₁ s i.castSucc ^ m) a := fun a ha => by
      have := le_ordAlongIdeal_pow hY.idealSheaf (h1 a ha) m
      rwa [mul_comm s m] at this
    have h2' : ∀ a ∈ (S.center i).support, ((m * s : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
        hY.idealSheaf (S.markedTransformSeq J₂ m i.castSucc ^ s) a := fun a ha =>
      le_ordAlongIdeal_pow hY.idealSheaf (h2 a ha) s
    rw [markedTransformSeq_succ, markedTransformSeq_succ, markedTransformSeq_succ, ih,
      birationalTransform_add hY (S.isBlowUp_map i) _ _ (m * s) h1' h2']
    congr 1
    · have e := birationalTransform_pow hY (S.isBlowUp_map i)
        (S.markedTransformSeq J₁ s i.castSucc) s m h1
      rw [mul_comm s m] at e
      exact e
    · exact birationalTransform_pow hY (S.isBlowUp_map i) (S.markedTransformSeq J₂ m i.castSucc)
        m s h2

/-- A list of order `≥ ms` for `J₁^m + J₂^s` is of order `≥ s` for `(J₁, s)`: the same centres and
boundaries, the order clause at every centre by the observation of [Kol07, 111, Step 2] ("also a
smooth blow-up sequence of order `s` starting with `N(I)`"). -/
theorem IsOfOrderGe.left_of_pow_add_pow (hm : 1 ≤ m) (hs : 1 ≤ s)
    (h : S.IsOfOrderGe (J₁ ^ m + J₂ ^ s) (m * s) E₀) : S.IsOfOrderGe J₁ s E₀ := by
  intro i
  refine ⟨(h i).1, fun a ha => ?_⟩
  have hsum := h.le_ordAlong_center i a ha
  rw [markedTransformSeq_pow_add_pow hm hs h i.castSucc] at hsum
  have := ((IdealSheaf.le_ordAlongIdeal_pow_add_pow_iff (S.isClosedSubmanifold_center i) _ _ hm hs
    ha).mp hsum).1
  rwa [S.idealSheaf_center i] at this

/-- A list of order `≥ ms` for `J₁^m + J₂^s` is of order `≥ m` for `(J₂, m)` ("and a smooth blow-up
sequence of order `m` starting with `I`" [Kol07, 111, Step 2]). -/
theorem IsOfOrderGe.right_of_pow_add_pow (hm : 1 ≤ m) (hs : 1 ≤ s)
    (h : S.IsOfOrderGe (J₁ ^ m + J₂ ^ s) (m * s) E₀) : S.IsOfOrderGe J₂ m E₀ := by
  intro i
  refine ⟨(h i).1, fun a ha => ?_⟩
  have hsum := h.le_ordAlong_center i a ha
  rw [markedTransformSeq_pow_add_pow hm hs h i.castSucc] at hsum
  have := ((IdealSheaf.le_ordAlongIdeal_pow_add_pow_iff (S.isClosedSubmanifold_center i) _ _ hm hs
    ha).mp hsum).2
  rwa [S.idealSheaf_center i] at this

omit [FiniteDimensional 𝕜 E] in
/-- The order clause is antitone in the ideal at a fixed mark: a list of order `≥ m` for `(J, m)` is
of order `≥ m` for `(I, m)` when `I ≤ J`, since `mt(I, m) ≤ mt(J, m)` at every stage
(`markedTransformSeq_le_of_le`) and the order along the centre is antitone (`ordAlongIdeal_anti`).
-/
theorem IsOfOrderGe.of_le (hIJ : I ≤ J) (h : S.IsOfOrderGe J m E₀) : S.IsOfOrderGe I m E₀ := by
  intro i
  refine ⟨(h i).1, fun a ha => ?_⟩
  exact (h.le_ordAlong i ha).trans
    (ordAlongIdeal_anti _ (h.markedTransformSeq_le_of_le _ hIJ i.castSucc) a)

end AnalyticManifold.FiniteSuccession

/-! ### A pointwise predicate on the induced triple transports through a concatenation -/

namespace Manifold.AnalyticTriple

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- A predicate on triples which holds at the triple induced by `L'` from the triple induced by `L`
holds at the triple induced by the concatenation `L.concat L'`. Induction on `L`; the induced
triple is definitional at the constructors (`induced_congr`, `induced_cons`), so no cast across
`stage_last_concat` is needed. The separation invariant and the terminal bound of the monomial
step are its two instances. -/
theorem pred_induced_concat (P : ∀ {N : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ N → Prop) :
    ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (L : BlowUpSequence ψ₀ M)
      (L' : BlowUpSequence ψ₀ (L.stage (Fin.last _))) (m : ℕ)
      (hL : L.toSuccession.IsOfOrderGe T.I m T.F.idealSheaf)
      (hL' : L'.toSuccession.IsOfOrderGe (T.induced m L hL).I m (T.induced m L hL).F.idealSheaf)
      (hC : (L.concat L').toSuccession.IsOfOrderGe T.I m T.F.idealSheaf),
      P ((T.induced m L hL).induced m L' hL') → P (T.induced m (L.concat L') hC)
  | _, T, BlowUpSequence.nil _, L', m, hL, hL', hC, h => by
    rw [induced_congr (induced_nil T m hL) m L' hL' hC] at h
    exact h
  | _, T, BlowUpSequence.cons hY rest, L', m, hL, hL', hC, h => by
    have e₁ := induced_cons T m hY hL
    have hL'' : L'.toSuccession.IsOfOrderGe
        ((T.headTriple m hY (T.isOfOrderGe_head_of_cons m hY hL)).induced m rest
          (T.isOfOrderGe_tail_of_cons m hY hL)).I m
        ((T.headTriple m hY (T.isOfOrderGe_head_of_cons m hY hL)).induced m rest
          (T.isOfOrderGe_tail_of_cons m hY hL)).F.idealSheaf := by
      rw [← e₁]; exact hL'
    rw [induced_congr e₁ m L' hL' hL''] at h
    have ih := pred_induced_concat P (T.headTriple m hY (T.isOfOrderGe_head_of_cons m hY hL)) rest
      L' m (T.isOfOrderGe_tail_of_cons m hY hL) hL'' (T.isOfOrderGe_tail_of_cons m hY hC) h
    change P (T.induced m (BlowUpSequence.cons hY (rest.concat L')) hC)
    rw [induced_cons T m hY hC]
    exact ih

end Manifold.AnalyticTriple

namespace Hironaka.Manifold.BMO

open _root_.Manifold

open Hironaka.Manifold.BMOmod

/-! ### Two facts about chain states -/

section ChainStateTools

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  {T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M} {m : ℕ} {W V : Opens M}
  (st : ChainState T m W) (hVW : closure (V : Set M) ⊆ W)

/-- The list of a chain state over `W`, restricted to `V` with `closure V ⊆ W`, is of order `≥ m`
for `(𝓘|V, m)`. -/
theorem _root_.Hironaka.Manifold.ChainState.pullback_restrictLE_isOfOrderGe :
    (st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
      (isLocalDiffeomorph_restrictLE _)).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).I m
      (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).F.idealSheaf := by
  have h := AnalyticTriple.isOfOrderGe_pullback _ m st.L st.hge
    (M.restrictLE (ChainState.le_of_closure_subset hVW)) (isLocalDiffeomorph_restrictLE _)
  rwa [AnalyticTriple.pullback_inclusion_restrictLE T (ChainState.le_of_closure_subset hVW)] at h

/-- The induced triple of a chain state, restricted to the reading open and pulled back along the
corestricted lift, is the induced triple of the restricted list (`pullback_pullback`,
`inclusion_comp_liftCorestrict`, `induced_pullback`, `pullback_inclusion_restrictLE`). -/
theorem _root_.Hironaka.Manifold.ChainState.inducedTriple_pullback_liftCorestrict_eq :
    ((ChainState.inducedTriple T m st).pullback
        ((st.L.stage (Fin.last _)).inclusion (ChainState.readOpen T m st hVW))
        (isLocalDiffeomorph_inclusion _ _)).pullback
        (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _))
        (st.L.isLocalDiffeomorph_liftCorestrict _ _) =
      (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).induced m
        (st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _)) (st.pullback_restrictLE_isOfOrderGe hVW) := by
  have hL₁ := AnalyticTriple.isOfOrderGe_pullback _ m st.L st.hge
    (M.restrictLE (ChainState.le_of_closure_subset hVW)) (isLocalDiffeomorph_restrictLE _)
  rw [AnalyticTriple.pullback_pullback,
    AnalyticTriple.pullback_eq_of_eq _ (BlowUpSequence.inclusion_comp_liftCorestrict st.L _ _) _
      (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast st.L _ _)]
  exact (AnalyticTriple.induced_pullback _ m st.L st.hge _ _ hL₁).trans
    (AnalyticTriple.induced_congr
      (AnalyticTriple.pullback_inclusion_restrictLE T (ChainState.le_of_closure_subset hVW)) m _
      hL₁ (st.pullback_restrictLE_isOfOrderGe hVW))

end ChainStateTools

/-! ### The chain state of the separation step -/

section Chain

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (m : ℕ)

/-- **The state of the descent of the separation step at the separation bound `s`** over the open
`W`: a chain state (a list on `M.restrict W` of order `≥ m` for `(𝓘|W, m)`) whose induced triple
satisfies `SepOrdLe … m s` on its last stage, Kollár's `s` [Kol07, 111, Step 2] as an
invariant. -/
structure SState (W : Opens M) (s : ℕ) extends ChainState T m W where
  /-- The invariant: `ord N(𝓘_ind) ≤ s` on `cosupp(𝓘_ind, m)`, globally on the last stage. -/
  sep : SepOrdLe (ChainState.inducedTriple T m toChainState) m s

/-- A chain state whose induced triple satisfies `ord N(𝓘_ind) ≤ d` everywhere (the exit bound of
the first step) is a state of the separation step at the separation bound `d`: the separation
step starts from the bound the first step exits with (`stepAChainState_bound`), with no new
supremum. -/
def SState.ofNonmonomialOrdLe {W : Opens M} (st : ChainState T m W) {d : ℕ}
    (h : NonmonomialOrdLe (ChainState.inducedTriple T m st) d) : SState T m W d :=
  ⟨st, h.sepOrdLe m⟩

@[simp] theorem SState.ofNonmonomialOrdLe_L {W : Opens M} (st : ChainState T m W) {d : ℕ}
    (h : NonmonomialOrdLe (ChainState.inducedTriple T m st) d) :
    (SState.ofNonmonomialOrdLe T m st h).L = st.L := rfl

/-- A state of the first step at the bound `d` (a `BState`) is a state of the separation step at
the separation bound `d`. -/
def SState.ofBState {W : Opens M} {d : ℕ} (st : BState T m W d) : SState T m W d :=
  ⟨st.toChainState, st.bound.sepOrdLe m⟩

@[simp] theorem SState.ofBState_L {W : Opens M} {d : ℕ} (st : BState T m W d) :
    (SState.ofBState T m st).L = st.L := rfl

/-- The state at a weaker bound. -/
def SState.weaken {W : Opens M} {s s' : ℕ} (st : SState T m W s) (h : s ≤ s') : SState T m W s' :=
  ⟨st.toChainState, st.sep.weaken h⟩

/-- The induced triple of any chain state of a triple of the marked class `BMOClass m` is again in
the class: the mark is unchanged, and finitely many members of the induced boundary are nonempty
(`finite_nonempty_totalTransformSeqFrom`). -/
theorem bmoClass_inducedTriple (hT : AnalyticTriple.BMOClass m T) {W : Opens M}
    (st : ChainState T m W) : AnalyticTriple.BMOClass m (ChainState.inducedTriple T m st) :=
  ⟨hT.1, finite_nonempty_totalTransformSeqFrom st.L.toSuccession _
    (finite_nonempty_hyp_comap T.F (M.inclusion W) hT.2) (Fin.last _)⟩

variable {T} {m} (hT : AnalyticTriple.BMOClass m T) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hidN : NonmonomialTransformIdentityMod.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))

section Link

variable {W : Opens M} {s : ℕ} (st : SState T m W s)

include hT in
/-- The invariant puts the induced triple in the class of the round, `SepClass m s`, for `s ≥ 1`
(`sepClass_of_sepOrdLe`). -/
theorem SState.sepClass (hs : 1 ≤ s) :
    SepClass m s (ChainState.inducedTriple T m st.toChainState) :=
  sepClass_of_sepOrdLe (bmoClass_inducedTriple T m hT st.toChainState) hs st.sep

section Round

variable {V : Opens M} (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W)

/-- **The value of the round of the separation step**: `BO_{n, ms}` read at the separating triple
of the induced triple (`sepFunctor`), on the reading open, the lifted range of `V ⊆ W` ("we apply
order reduction to the ideal `N(I)^m + I^s`" [Kol07, 111, Step 2]). -/
def SState.roundValue (hs : 1 ≤ s) :
    BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      ((st.L.stage (Fin.last _)).restrict (ChainState.readOpen T m st.toChainState hVW)) :=
  ((sepFunctor (bo (m * s))).fam (ChainState.inducedTriple T m st.toChainState)
    (st.sepClass hT hs)).seqOn (ChainState.readOpen T m st.toChainState hVW)
    (ChainState.isCompact_closure_readOpen T m st.toChainState hV hVW)

include hcomp in
/-- The value is of order `≥ ms` for the separating ideal of the restricted induced triple
(`bo.isOfOrderGe`; the separating triple commutes with the restriction). -/
theorem SState.roundValue_isOfOrderGe_sepIdealAt (hs : 1 ≤ s) :
    (st.roundValue hT bo hV hVW hs).toSuccession.IsOfOrderGe
      (sepIdealAt ((ChainState.inducedTriple T m st.toChainState).pullback
        ((st.L.stage (Fin.last _)).inclusion (ChainState.readOpen T m st.toChainState hVW))
        (isLocalDiffeomorph_inclusion _ _)) m s) (m * s)
      (((ChainState.inducedTriple T m st.toChainState).pullback
        ((st.L.stage (Fin.last _)).inclusion (ChainState.readOpen T m st.toChainState hVW))
        (isLocalDiffeomorph_inclusion _ _)).F.idealSheaf) := by
  have h := (bo (m * s)).isOfOrderGe
    (sepTripleAt (ChainState.inducedTriple T m st.toChainState) m s) (st.sepClass hT hs)
        (ChainState.readOpen T m st.toChainState hVW)
    (ChainState.isCompact_closure_readOpen T m st.toChainState hV hVW)
  rw [← sepTripleAt_pullback hcomp (ChainState.inducedTriple T m st.toChainState) m s _ _,
    sepTripleAt_I, sepTripleAt_F] at h
  exact h

include hcomp in
/-- The value is of order `≥ s` for `(N(𝓘'), s)`, where `(M', 𝓘', E')` is the restricted induced
triple ("also a smooth blow-up sequence of order `s` starting with `N(I)`" [Kol07, 111, Step 2]). -/
theorem SState.roundValue_isOfOrderGe_nonmonomial (hm : 1 ≤ m) (hs : 1 ≤ s) :
    (st.roundValue hT bo hV hVW hs).toSuccession.IsOfOrderGe
      (nonmonomialTriple ((ChainState.inducedTriple T m st.toChainState).pullback
        ((st.L.stage (Fin.last _)).inclusion (ChainState.readOpen T m st.toChainState hVW))
        (isLocalDiffeomorph_inclusion _ _))).I s
      (((ChainState.inducedTriple T m st.toChainState).pullback
        ((st.L.stage (Fin.last _)).inclusion (ChainState.readOpen T m st.toChainState hVW))
        (isLocalDiffeomorph_inclusion _ _)).F.idealSheaf) :=
  (st.roundValue_isOfOrderGe_sepIdealAt hT bo hcomp hV hVW hs).left_of_pow_add_pow hm hs

include hcomp in
/-- The value is of order `≥ m` for the restricted induced triple itself ("and a smooth blow-up
sequence of order `m` starting with `I`" [Kol07, 111, Step 2]); this is the order clause
`ChainState.linkWith` requires. -/
theorem SState.roundValue_isOfOrderGe (hm : 1 ≤ m) (hs : 1 ≤ s) :
    (st.roundValue hT bo hV hVW hs).toSuccession.IsOfOrderGe
      ((ChainState.inducedTriple T m st.toChainState).pullback
        ((st.L.stage (Fin.last _)).inclusion (ChainState.readOpen T m st.toChainState hVW))
        (isLocalDiffeomorph_inclusion _ _)).I m
      (((ChainState.inducedTriple T m st.toChainState).pullback
        ((st.L.stage (Fin.last _)).inclusion (ChainState.readOpen T m st.toChainState hVW))
        (isLocalDiffeomorph_inclusion _ _)).F.idealSheaf) :=
  (st.roundValue_isOfOrderGe_sepIdealAt hT bo hcomp hV hVW hs).right_of_pow_add_pow hm hs

include hcomp hidN in
/-- **One link of the descent of the separation step** at the bound `s ≥ 1` [Kol07, 111, Step 2]:
the value of the round appended to the list restricted to `V` (`ChainState.linkWith`, with the
order clause `≥ m` for `𝓘` from the observation of the separation step), and the invariant
descends to `s − 1`. At the last stage of the value the transform of the separating ideal has
order `< ms` (`bo.ord_lt` at the mark `ms`) and equals `mt(N', s)^m + mt(𝓘', m)^s`
(`markedTransformSeq_pow_add_pow`), so `min(m · ord N_r, s · ord 𝓘_r) < ms` and hence
`ord N_r < s` wherever `ord 𝓘_r ≥ m`; the transform identity modulo `N` gives
`N(𝓘_r) = N(N_r) ⊇ N_r`, so `ord N(𝓘_r) ≤ ord N_r < s`. The bound is pulled back along the
corestricted lift (`induced_pullback`, `ord_pullback_of_isLocalDiffeomorphAt`) and passed through
the concatenation (`pred_induced_concat`). This is Kollár's "we stop … when
`cosupp(I_r, m) ∩ cosupp(N(I_r), s) = ∅`; we can continue with `s − 1`". -/
def SState.sepLink (hm : 1 ≤ m) (hs : 1 ≤ s) : SState T m V (s - 1) where
  toChainState := ChainState.linkWith T m st.toChainState hV hVW
    ((sepFunctor (bo (m * s))).fam (ChainState.inducedTriple T m st.toChainState)
      (st.sepClass hT hs))
    (st.roundValue_isOfOrderGe hT bo hcomp hV hVW hm hs)
  sep := by
    have hL₀' := st.roundValue_isOfOrderGe hT bo hcomp hV hVW hm hs
    have hN' := st.roundValue_isOfOrderGe_nonmonomial hT bo hcomp hV hVW hm hs
    have hsep' := st.roundValue_isOfOrderGe_sepIdealAt hT bo hcomp hV hVW hs
    have hL₁ := st.toChainState.pullback_restrictLE_isOfOrderGe hVW
    -- the value pulled back along the corestricted lift, of order ≥ m for the induced triple of the
    -- restricted list
    have h₂ := AnalyticTriple.isOfOrderGe_pullback _ m (st.roundValue hT bo hV hVW hs) hL₀'
      (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
        (isLocalDiffeomorph_restrictLE _)) (st.L.isLocalDiffeomorph_liftCorestrict _ _)
    have e := st.toChainState.inducedTriple_pullback_liftCorestrict_eq hVW
    have hL₂ : ((st.roundValue hT bo hV hVW hs).pullback
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
    -- the invariant at the last stage of the pulled-back value
    have hmain : SepOrdLe
        (((T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).induced m
          (st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
            (isLocalDiffeomorph_restrictLE _)) hL₁).induced m
          ((st.roundValue hT bo hV hVW hs).pullback
            (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
              (isLocalDiffeomorph_restrictLE _))
            (st.L.isLocalDiffeomorph_liftCorestrict _ _)) hL₂) m (s - 1) := by
      rw [← AnalyticTriple.induced_congr e m _ h₂ hL₂,
        ← AnalyticTriple.induced_pullback _ m (st.roundValue hT bo hV hVW hs) hL₀'
          (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
            (isLocalDiffeomorph_restrictLE _)) (st.L.isLocalDiffeomorph_liftCorestrict _ _) h₂]
      intro y hy
      rw [hcomp (((ChainState.inducedTriple T m st.toChainState).pullback
          ((st.L.stage (Fin.last _)).inclusion (ChainState.readOpen T m st.toChainState hVW))
          (isLocalDiffeomorph_inclusion _ _)).induced m (st.roundValue hT bo hV hVW hs) hL₀')
        ((st.roundValue hT bo hV hVW hs).pullbackLiftLast
          (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
            (isLocalDiffeomorph_restrictLE _)) (st.L.isLocalDiffeomorph_liftCorestrict _ _))
        (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)]
      change ((nonmonomialTriple (((ChainState.inducedTriple T m st.toChainState).pullback
        ((st.L.stage (Fin.last _)).inclusion (ChainState.readOpen T m st.toChainState hVW))
        (isLocalDiffeomorph_inclusion _ _)).induced m (st.roundValue hT bo hV hVW hs)
        hL₀')).I.pullback _ _).ord y ≤ _
      change (m : ℕ∞) ≤ (((((ChainState.inducedTriple T m st.toChainState).pullback
        ((st.L.stage (Fin.last _)).inclusion (ChainState.readOpen T m st.toChainState hVW))
        (isLocalDiffeomorph_inclusion _ _)).induced m (st.roundValue hT bo hV hVW hs)
        hL₀')).I.pullback _ _).ord y at hy
      rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
        (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _ y)] at hy ⊢
      -- the modulo-N identity at the last stage: N(mt(𝓘', m)) = N(mt(N(𝓘'), s))
      have eN : (nonmonomialTriple (((ChainState.inducedTriple T m st.toChainState).pullback
            ((st.L.stage (Fin.last _)).inclusion (ChainState.readOpen T m st.toChainState hVW))
            (isLocalDiffeomorph_inclusion _ _)).induced m (st.roundValue hT bo hV hVW hs)
            hL₀')).I =
          nonmonomialPart ((st.roundValue hT bo hV hVW hs).toSuccession.totalTransformSeqFrom
              ((ChainState.inducedTriple T m st.toChainState).pullback
                ((st.L.stage (Fin.last _)).inclusion
                  (ChainState.readOpen T m st.toChainState hVW))
                (isLocalDiffeomorph_inclusion _ _)).F (Fin.last _))
            ((st.roundValue hT bo hV hVW
              hs).toSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq
              ((ChainState.inducedTriple T m st.toChainState).pullback
                ((st.L.stage (Fin.last _)).inclusion
                  (ChainState.readOpen T m st.toChainState hVW))
                (isLocalDiffeomorph_inclusion _ _)).isSnc
              (fun j => hL₀'.hasOnlyNormalCrossingsWith j) (Fin.last _)).1
            ((st.roundValue hT bo hV hVW hs).toSuccession.markedTransformSeq
              (nonmonomialTriple ((ChainState.inducedTriple T m st.toChainState).pullback
                ((st.L.stage (Fin.last _)).inclusion
                  (ChainState.readOpen T m st.toChainState hVW))
                (isLocalDiffeomorph_inclusion _ _))).I s (Fin.last _)) :=
        (nonmonomialTriple_I _).trans (hidN _ (st.roundValue hT bo hV hVW hs) m s hm hL₀' hN'
          (Fin.last _))
      rw [eN]
      -- ord N(mt(N', s)) ≤ ord mt(N', s) < s
      refine (IdealSheaf.ord_anti (le_nonmonomialPart _ _ _) _).trans ?_
      have hlt := (bo (m * s)).ord_lt (sepTripleAt (ChainState.inducedTriple T m st.toChainState)
        m s) (st.sepClass hT hs) (ChainState.readOpen T m st.toChainState hVW)
        (ChainState.isCompact_closure_readOpen T m st.toChainState hV hVW)
        ((st.roundValue hT bo hV hVW hs).pullbackLiftLast
          (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
            (isLocalDiffeomorph_restrictLE _)) (st.L.isLocalDiffeomorph_liftCorestrict _ _) y)
      rw [← sepTripleAt_pullback hcomp (ChainState.inducedTriple T m st.toChainState) m s _ _,
        sepTripleAt_I] at hlt
      change ((st.roundValue hT bo hV hVW hs).toSuccession.markedTransformSeq
        ((nonmonomialTriple ((ChainState.inducedTriple T m st.toChainState).pullback
          ((st.L.stage (Fin.last _)).inclusion (ChainState.readOpen T m st.toChainState hVW))
          (isLocalDiffeomorph_inclusion _ _))).I ^ m +
        ((ChainState.inducedTriple T m st.toChainState).pullback
          ((st.L.stage (Fin.last _)).inclusion (ChainState.readOpen T m st.toChainState hVW))
          (isLocalDiffeomorph_inclusion _ _)).I ^ s) (m * s) (Fin.last _)).ord _ < _ at hlt
      rw [FiniteSuccession.markedTransformSeq_pow_add_pow hm hs hsep' (Fin.last _)] at hlt
      have h1 := IdealSheaf.ord_add_eq_min
        ((st.roundValue hT bo hV hVW hs).toSuccession.markedTransformSeq
          (nonmonomialTriple ((ChainState.inducedTriple T m st.toChainState).pullback
            ((st.L.stage (Fin.last _)).inclusion (ChainState.readOpen T m st.toChainState hVW))
            (isLocalDiffeomorph_inclusion _ _))).I s (Fin.last _) ^ m)
        ((st.roundValue hT bo hV hVW hs).toSuccession.markedTransformSeq
          ((ChainState.inducedTriple T m st.toChainState).pullback
            ((st.L.stage (Fin.last _)).inclusion (ChainState.readOpen T m st.toChainState hVW))
            (isLocalDiffeomorph_inclusion _ _)).I m (Fin.last _) ^ s)
        ((st.roundValue hT bo hV hVW hs).pullbackLiftLast
          (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
            (isLocalDiffeomorph_restrictLE _)) (st.L.isLocalDiffeomorph_liftCorestrict _ _) y)
      rw [IdealSheaf.ord_pow _ hm, IdealSheaf.ord_pow _ hs] at h1
      have hlt' := lt_of_eq_of_lt h1.symm hlt
      have hA : ((st.roundValue hT bo hV hVW hs).toSuccession.markedTransformSeq
          (nonmonomialTriple ((ChainState.inducedTriple T m st.toChainState).pullback
            ((st.L.stage (Fin.last _)).inclusion (ChainState.readOpen T m st.toChainState hVW))
            (isLocalDiffeomorph_inclusion _ _))).I s (Fin.last _)).ord
          ((st.roundValue hT bo hV hVW hs).pullbackLiftLast
              (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
                (isLocalDiffeomorph_restrictLE _)) (st.L.isLocalDiffeomorph_liftCorestrict _ _) y)
                  < (s : ℕ∞) := by
        by_contra hge
        rw [not_lt] at hge
        have h1 : ((m * s : ℕ) : ℕ∞) ≤ (m : ℕ∞) *
            ((st.roundValue hT bo hV hVW hs).toSuccession.markedTransformSeq
              (nonmonomialTriple ((ChainState.inducedTriple T m st.toChainState).pullback
                ((st.L.stage (Fin.last _)).inclusion
                  (ChainState.readOpen T m st.toChainState hVW))
                (isLocalDiffeomorph_inclusion _ _))).I s (Fin.last _)).ord
              ((st.roundValue hT bo hV hVW hs).pullbackLiftLast
              (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
                (isLocalDiffeomorph_restrictLE _)) (st.L.isLocalDiffeomorph_liftCorestrict _ _) y)
                  := by
          rw [Nat.cast_mul]
          exact mul_le_mul_of_nonneg_left hge zero_le
        have h2 : ((m * s : ℕ) : ℕ∞) ≤ (s : ℕ∞) *
            ((st.roundValue hT bo hV hVW hs).toSuccession.markedTransformSeq
              ((ChainState.inducedTriple T m st.toChainState).pullback
                ((st.L.stage (Fin.last _)).inclusion
                  (ChainState.readOpen T m st.toChainState hVW))
                (isLocalDiffeomorph_inclusion _ _)).I m (Fin.last _)).ord
              ((st.roundValue hT bo hV hVW hs).pullbackLiftLast
              (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
                (isLocalDiffeomorph_restrictLE _)) (st.L.isLocalDiffeomorph_liftCorestrict _ _) y)
                  := by
          rw [Nat.cast_mul, mul_comm]
          exact mul_le_mul_of_nonneg_left hy zero_le
        exact absurd (le_min h1 h2) (not_le.mpr hlt')
      have hs1 : (s : ℕ∞) = ((s - 1 : ℕ) : ℕ∞) + 1 := by
        norm_cast
        omega
      rw [hs1] at hA
      exact (ENat.lt_add_one_iff (ENat.natCast_ne_top _)).mp hA
    -- transport through the concatenation
    change SepOrdLe
      ((T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).induced m
        ((st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _)).concat
          ((st.roundValue hT bo hV hVW hs).pullback
            (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
              (isLocalDiffeomorph_restrictLE _)) (st.L.isLocalDiffeomorph_liftCorestrict _ _))) _)
      m (s - 1)
    exact AnalyticTriple.pred_induced_concat (fun S => SepOrdLe S m (s - 1)) _ _ _ m hL₁ hL₂ _ hmain

/-- One link is the shrink-and-append step with the round's value. -/
theorem SState.sepLink_L (hm : 1 ≤ m) (hs : 1 ≤ s) :
    (st.sepLink hT bo hcomp hidN hV hVW hm hs).L =
      st.L.shrinkAppend (M.restrictLE (ChainState.le_of_closure_subset hVW))
        (isLocalDiffeomorph_restrictLE _) (st.roundValue hT bo hV hVW hs) := rfl

end Round

end Link

section Descent

variable (hm : 1 ≤ m) (W : ℕ → Opens M) (hW : ∀ k, IsCompact (closure (W k : Set M))) (r : ℕ)
  (hWsub : ∀ k, k < r → closure (W (k + 1) : Set M) ⊆ W k) (S₀ : ℕ) (st₀ : SState T m (W 0) S₀)

/-- **The descent of the separation step**: `j` links from the state `st₀` at the bound `S₀` on
`W 0`, giving the state on `W j` at the bound `S₀ − j` ("we can continue with `s − 1` and so on"
[Kol07, 111, Step 2]). The descent runs through every bound `S₀, S₀ − 1, …, 1`; a round at a bound
above the actual separation order is empty up to the deletion of empty blow-ups. -/
def sepDescentAux : ∀ j : ℕ, j ≤ r → j ≤ S₀ → SState T m (W j) (S₀ - j)
  | 0, _, _ => st₀
  | j + 1, hj, hjS =>
    (sepDescentAux j (Nat.le_of_succ_le hj) (Nat.le_of_succ_le hjS)).sepLink hT bo hcomp hidN
      (hW (j + 1)) (hWsub j hj) hm (by omega)

/-- **The final state of the descent**, after `S₀` links, at the separation bound `0`
("eventually we achieve a situation where the cosupports of `N(I)` and of `(I, m)` are disjoint"
[Kol07, 111, Step 2]). -/
def sepDescentState (hr : S₀ ≤ r) : SState T m (W S₀) 0 :=
  ⟨(sepDescentAux hT bo hcomp hidN hm W hW r hWsub S₀ st₀ S₀ hr le_rfl).toChainState,
    (sepDescentAux hT bo hcomp hidN hm W hW r hWsub S₀ st₀ S₀ hr le_rfl).sep.weaken
      (Nat.sub_self S₀).le⟩

theorem sepDescentState_L (hr : S₀ ≤ r) :
    (sepDescentState hT bo hcomp hidN hm W hW r hWsub S₀ st₀ hr).L =
      (sepDescentAux hT bo hcomp hidN hm W hW r hWsub S₀ st₀ S₀ hr le_rfl).L := rfl

end Descent

end Chain

/-! ### The canonical separation step: the chain inside the exit open of the first step -/

section Canonical

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (m : ℕ)
  (hT : AnalyticTriple.BMOClass m T) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hidN : NonmonomialTransformIdentityMod.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (t : ℕ) (hm : 1 ≤ m) (hmt : m ≤ t) (U : Opens M) (hU : IsCompact (closure (U : Set M)))

/-- The exit open of the first step, which contains `closure U` (the open of `stepAChainState`). -/
abbrev step2Outer : Opens M := stepAChainOpens U hU (stepALinks T t U hU)

theorem closure_subset_step2Outer : closure (U : Set M) ⊆ step2Outer T t U hU :=
  subset_shrinkChain hU (closure_subset_stepAOuter U hU) _

theorem isCompact_closure_step2Outer : IsCompact (closure (step2Outer T t U hU : Set M)) :=
  isCompact_closure_shrinkChain hU (closure_subset_stepAOuter U hU) _

/-- The canonical chain of the separation step: the exit open of the first step, then the iterated
shrinkings of `closure U` inside it (`shrinkChain`). -/
def step2ChainOpens : ℕ → Opens M
  | 0 => step2Outer T t U hU
  | k + 1 => shrinkChain (closure (U : Set M)) (step2Outer T t U hU) hU
      (closure_subset_step2Outer T t U hU) k

theorem isCompact_closure_step2ChainOpens (k : ℕ) :
    IsCompact (closure (step2ChainOpens T t U hU k : Set M)) := by
  cases k with
  | zero => exact isCompact_closure_step2Outer T t U hU
  | succ k => exact isCompact_closure_shrinkChain hU (closure_subset_step2Outer T t U hU) k

theorem closure_step2ChainOpens_succ_subset (k : ℕ) :
    closure (step2ChainOpens T t U hU (k + 1) : Set M) ⊆ step2ChainOpens T t U hU k := by
  cases k with
  | zero => exact closure_shrinkChain_zero_subset hU (closure_subset_step2Outer T t U hU)
  | succ k => exact closure_shrinkChain_succ_subset hU (closure_subset_step2Outer T t U hU) k

theorem le_step2ChainOpens (k : ℕ) : U ≤ step2ChainOpens T t U hU k := by
  cases k with
  | zero => exact fun x hx => closure_subset_step2Outer T t U hU (subset_closure hx)
  | succ k => exact fun x hx =>
      subset_shrinkChain hU (closure_subset_step2Outer T t U hU) k (subset_closure hx)

/-- **The state after the separation step**: the descent from the final state of the first step
(`stepAChainState`, whose exit bound `t − 1` is the initial separation bound) along the canonical
chain, `t − 1` links; at the exit the separation bound is `0`, i.e.
`cosupp(𝓘, m) ∩ cosupp N(𝓘) = ∅` [Kol07, 111, Step 2]. The scheme-theoretic counterpart is
`Hironaka.BMO.afterStep2`. -/
def step2ChainState : SState T m (step2ChainOpens T t U hU (t - 1)) 0 :=
  sepDescentState hT bo hcomp hidN hm (step2ChainOpens T t U hU)
    (isCompact_closure_step2ChainOpens T t U hU) (t - 1)
    (fun k _ => closure_step2ChainOpens_succ_subset T t U hU k) (t - 1)
    (SState.ofNonmonomialOrdLe T m (stepAChainState T m hT bo hcomp hid t hm hmt U hU).toChainState
      (stepAChainState_bound T m hT bo hcomp hid t hm hmt U hU))
    le_rfl

/-- At the exit of the separation step the cosupports of `(𝓘, m)` and of `N(𝓘)` are disjoint
[Kol07, 111, Step 2]. -/
theorem step2ChainState_sep :
    SepOrdLe (ChainState.inducedTriple T m
      (step2ChainState T m hT bo hcomp hid hidN t hm hmt U hU).toChainState) m 0 :=
  (step2ChainState T m hT bo hcomp hid hidN t hm hmt U hU).sep

end Canonical

end Hironaka.Manifold.BMO

end
