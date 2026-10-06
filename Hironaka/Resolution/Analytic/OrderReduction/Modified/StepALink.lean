/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepARound
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.InducedConcat
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1RoundOrder
public import Hironaka.Resolution.Analytic.OrderReduction.Step21Fam
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.OrderReduction.Step21Functoriality
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The rounds on the nonmonomial part: one link of the descent

One round of order reduction on the nonmonomial part `N(𝓘)` at the bound `d` ([Kol07, 111, Step 1];
the first phase of the modified algorithm of [Wlo09, Theorem 7.4.1]), as **one link of a shrinking
chain** `W ⊇ closure V` of relatively compact opens (the shape of `ChainState.link`): the state
carries, besides the list and its order clause, the invariant that the nonmonomial part of the
induced ideal has order `≤ d` everywhere on the last stage (`BState`). So the nonmonomial triple of
the induced triple lies in the domain of `BO_{n,d}` globally (`BState.boClass_nonmonomial`), the
order reduction `bo d` is read on the lifted range of the inclusion `V ⊆ W` (`liftRange`, relatively
compact), the list is restricted to `V` and the value appended (`shrinkAppend`), and

* the order clause `≥ m` for `(𝓘|V, m)` holds by the order transfer (`isOfOrderGe_of_nonmonomial`:
  the value is of order `≥ d` for `(N, d)`, hence of order `≥ m` for `(𝓘, m)`, the transform
  identity and the invariant supplying its hypotheses) and `isOfOrderGe_shrinkAppend`;
* the invariant descends to `d − 1`: at the last stage of the value, `bo.ord_lt` bounds the marked
  transform of `(N, d)` by `< d`; the transform identity at the last stage turns this into the bound
  on the nonmonomial part of the marked transform of `(𝓘, m)`, which is pulled back along the
  corestricted lift (`induced_pullback`, `ord_pullback_of_isLocalDiffeomorphAt`) and passed through
  the concatenation (`nonmonomialOrdLe_induced_concat`).

The descent `d = D, D − 1, …, t` (`StepAChain.lean`) visits every `d`; at a `d` above the current
maximal order of `N(𝓘)` the order clause and the absence of empty centres force the value to be the
empty list (`BOanFam.seqOn_eq_nil`), so the nonempty links are the rounds of the sources at
`d = max-ord N(𝓘)`, in their order.

The nonmonomial part commutes with pull-back along a local analytic isomorphism
(`NonmonomialComap`, a parameter here, proved in `nonmonomialComap_inhabitant`). Every
identification of `(nonmonomialTriple X).F` with `X.F` goes through the projection lemma
`nonmonomialTriple_F` by `congrArg` before any `exact`: otherwise the elaborator unfolds
`nonmonomialTriple X` against `X` through the structures, and elaboration becomes very slow.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

open Hironaka.Manifold.BMO

section Comap

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ}

/-- **The nonmonomial part commutes with pull-back along a local analytic isomorphism**: the
nonmonomial triple of a pulled-back triple is the pull-back of the nonmonomial triple (the
decomposition of [Kol07, Definition–Lemma 110] is local). The rounds take the predicate as a
parameter; `nonmonomialComap_inhabitant` proves it at the standard model. -/
def NonmonomialComap (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)) : Prop :=
  ∀ {M N : AnalyticManifold.{u} 𝕜 E} (S : AnalyticTriple ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h),
    nonmonomialTriple (S.pullback h hh) = (nonmonomialTriple S).pullback h hh

variable {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

omit [FiniteDimensional 𝕜 E] in
/-- The boundary of a pulled-back nonmonomial triple is the boundary of the pulled-back triple: the
nonmonomial part keeps the boundary (`nonmonomialTriple_F`), transported by `congrArg` rather than
by `rfl`, which would unfold the triple against its nonmonomial triple through the structures. -/
theorem nonmonomialTriple_pullback_F (S : AnalyticTriple ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) :
    ((nonmonomialTriple S).pullback h hh).F = (S.pullback h hh).F :=
  congrArg (fun G : HypersurfaceFamily M => G.comap h) (nonmonomialTriple_F S)

omit [FiniteDimensional 𝕜 E] in
/-- A member of the pulled-back family is nonempty only if the member is, so finitely many nonempty
members pull back to finitely many (the boundary clause of `BOClass` pulls back). -/
theorem finite_nonempty_hyp_comap (F : HypersurfaceFamily M) (h : AnalyticMap N M)
    (hF : Finite {j // F.hyp j ≠ ∅}) : Finite {j // (F.comap h).hyp j ≠ ∅} := by
  refine Finite.of_injective
    (fun j : {j // (F.comap h).hyp j ≠ ∅} => (⟨j.1, fun he => j.2 ?_⟩ : {j // F.hyp j ≠ ∅}))
    fun j₁ j₂ hj => Subtype.ext (Subtype.mk.inj hj)
  change ⇑h ⁻¹' F.hyp j.1 = ∅
  rw [he, Set.preimage_empty]

end Comap

section Link

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  {T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M} {m : ℕ}

variable (T) (m) in
/-- **The state of the descent at the bound `d`** over the open `W`: a chain state (the list built
so far on `M.restrict W`, of order `≥ m` for `(𝓘|W, m)`) whose induced triple has nonmonomial part
of order `≤ d` at every point of the last stage. -/
structure BState (W : Opens M) (d : ℕ) extends ChainState T m W where
  /-- The invariant: `max-ord N(𝓘_ind) ≤ d` globally on the last stage. -/
  bound : NonmonomialOrdLe (ChainState.inducedTriple T m toChainState) d

variable (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))

variable (T) (m) in
/-- The initial state on `W ⊆ U₀`: the empty list, the bound `roundOrderOn T U₀` (the maximum of
`ord N(𝓘)` on the closure of `U₀`, `ord_le_roundOrderOn`). -/
def BState.initial {W U₀ : Opens M} (hU₀ : IsCompact (closure (U₀ : Set M))) (hWU : W ≤ U₀) :
    BState T m W (roundOrderOn T U₀) where
  toChainState := ChainState.init T m W
  bound := fun x => by
    have h : ∀ x' : M.restrict W, ((nonmonomialTriple T).pullback (M.inclusion W)
        (isLocalDiffeomorph_inclusion M W)).I.ord x' ≤ (roundOrderOn T U₀ : ℕ∞) := fun x' => by
      change ((nonmonomialTriple T).I.pullback _ _).ord x' ≤ _
      rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
        (isLocalDiffeomorph_inclusion _ _ x'), nonmonomialTriple_I]
      exact ord_le_roundOrderOn T U₀ hU₀ (hWU x'.2)
    have e : nonmonomialTriple (ChainState.inducedTriple T m (ChainState.init T m W)) =
        (nonmonomialTriple T).pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W) :=
      (congrArg nonmonomialTriple (AnalyticTriple.induced_nil _ m _)).trans
        (hcomp T (M.inclusion W) (isLocalDiffeomorph_inclusion M W))
    rw [e]
    exact h x

variable (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  {W : Opens M} {d : ℕ} (st : BState T m W d)

/-- The invariant puts the nonmonomial triple of the induced triple in the domain of `BO_{n,d}`
globally on the last stage (the boundary clause from the marked class `BMOClass`, through
`finite_nonempty_totalTransformSeqFrom`). -/
theorem BState.boClass_nonmonomial (hT : AnalyticTriple.BMOClass m T) (hd : 1 ≤ d) :
    AnalyticTriple.BOClass d (nonmonomialTriple (ChainState.inducedTriple T m st.toChainState)) :=
  ⟨hd, st.bound, finite_nonempty_totalTransformSeqFrom st.L.toSuccession _
    (finite_nonempty_hyp_comap T.F (M.inclusion W) hT.2) (Fin.last _)⟩

section Round

variable {V : Opens M} (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W)

/-- The reading open of the link: the lifted range of the inclusion `V ⊆ W` at the last stage. -/
abbrev BState.liftOpen : Opens (st.L.stage (Fin.last _)) :=
  st.L.liftRange (M.restrictLE (ChainState.le_of_closure_subset hVW))
    (isLocalDiffeomorph_restrictLE _)

include hV in
theorem BState.isCompact_closure_liftOpen :
    IsCompact (closure (st.liftOpen hVW : Set (st.L.stage (Fin.last _)))) :=
  st.L.isCompact_closure_liftRange _ _
    (isCompact_closure_range_restrictLE (ChainState.le_of_closure_subset hVW) hV hVW)

include hcomp in
/-- The invariant restricted to the reading open (the maximal-order hypothesis of the transform
identity). -/
theorem BState.nonmonomialOrdLe_restrict :
    NonmonomialOrdLe ((ChainState.inducedTriple T m st.toChainState).pullback
      ((st.L.stage (Fin.last _)).inclusion (st.liftOpen hVW))
      (isLocalDiffeomorph_inclusion _ _)) d := by
  intro x
  rw [hcomp (ChainState.inducedTriple T m st.toChainState)
    ((st.L.stage (Fin.last _)).inclusion (st.liftOpen hVW)) (isLocalDiffeomorph_inclusion _ _)]
  change ((nonmonomialTriple
    (ChainState.inducedTriple T m st.toChainState)).I.pullback _ _).ord x ≤ _
  rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _ (isLocalDiffeomorph_inclusion _ _ x)]
  exact st.bound _

include bo hV in
/-- **The value of the round**: the order reduction `BO_{n,d}` of the nonmonomial triple of the
induced triple, read on the reading open ("apply order reduction (68) to `N(I)`",
[Kol07, 111, Step 1]). -/
def BState.roundValue (hT : AnalyticTriple.BMOClass m T) (hd : 1 ≤ d) :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      ((st.L.stage (Fin.last _)).restrict (st.liftOpen hVW)) :=
  ((bo d).functor.fam (nonmonomialTriple (ChainState.inducedTriple T m st.toChainState))
    (st.boClass_nonmonomial hT hd)).seqOn (st.liftOpen hVW)
    (st.isCompact_closure_liftOpen hV hVW)

include hcomp bo hV in
/-- The value is of order `≥ d` for the nonmonomial triple of the restricted induced triple
(`bo.isOfOrderGe`; the identifications of ideal and boundary rewritten by their lemmas before the
`exact`). -/
theorem BState.roundValue_isOfOrderGe_nonmonomial (hT : AnalyticTriple.BMOClass m T) (hd : 1 ≤ d) :
    (st.roundValue bo hV hVW hT hd).toSuccession.IsOfOrderGe
      (nonmonomialTriple ((ChainState.inducedTriple T m st.toChainState).pullback
        ((st.L.stage (Fin.last _)).inclusion (st.liftOpen hVW))
        (isLocalDiffeomorph_inclusion _ _))).I d
      (((ChainState.inducedTriple T m st.toChainState).pullback
        ((st.L.stage (Fin.last _)).inclusion (st.liftOpen hVW))
        (isLocalDiffeomorph_inclusion _ _)).F.idealSheaf (𝕜 := 𝕜) (E := Fin n → 𝕜)) := by
  rw [congrArg AnalyticTriple.I (hcomp (ChainState.inducedTriple T m st.toChainState)
      ((st.L.stage (Fin.last _)).inclusion (st.liftOpen hVW)) (isLocalDiffeomorph_inclusion _ _)),
    ← nonmonomialTriple_pullback_F (ChainState.inducedTriple T m st.toChainState)
      ((st.L.stage (Fin.last _)).inclusion (st.liftOpen hVW)) (isLocalDiffeomorph_inclusion _ _)]
  exact (bo d).isOfOrderGe _ (st.boClass_nonmonomial hT hd) (st.liftOpen hVW)
    (st.isCompact_closure_liftOpen hV hVW)

include hcomp bo hid hV in
/-- The order transfer at the round: the value is of order `≥ m` for the restricted induced triple
itself (`isOfOrderGe_of_nonmonomial`, with `m ≤ d`). -/
theorem BState.roundValue_isOfOrderGe (hT : AnalyticTriple.BMOClass m T) (hm : 1 ≤ m)
    (hmd : m ≤ d) :
    (st.roundValue bo hV hVW hT (hm.trans hmd)).toSuccession.IsOfOrderGe
      ((ChainState.inducedTriple T m st.toChainState).pullback
        ((st.L.stage (Fin.last _)).inclusion (st.liftOpen hVW))
        (isLocalDiffeomorph_inclusion _ _)).I m
      (((ChainState.inducedTriple T m st.toChainState).pullback
        ((st.L.stage (Fin.last _)).inclusion (st.liftOpen hVW))
        (isLocalDiffeomorph_inclusion _ _)).F.idealSheaf (𝕜 := 𝕜) (E := Fin n → 𝕜)) :=
  isOfOrderGe_of_nonmonomial hid _ _ hm hmd (st.nonmonomialOrdLe_restrict hcomp hVW)
    (st.roundValue_isOfOrderGe_nonmonomial hcomp bo hV hVW hT (hm.trans hmd))

/-- The list restricted to `V` is of order `≥ m` for `(𝓘|V, m)` (the input of
`induced_pullback`). -/
theorem BState.shrink_hge :
    (st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
      (isLocalDiffeomorph_restrictLE _)).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).I m
      (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).F.idealSheaf := by
  have h := AnalyticTriple.isOfOrderGe_pullback _ m st.L st.hge
    (M.restrictLE (ChainState.le_of_closure_subset hVW)) (isLocalDiffeomorph_restrictLE _)
  rwa [AnalyticTriple.pullback_inclusion_restrictLE T (ChainState.le_of_closure_subset hVW)] at h

/-- The restricted induced triple pulled back along the corestricted lift is the induced triple of
the restricted list (`pullback_pullback`, `inclusion_comp_liftCorestrict`, `induced_pullback`,
`pullback_inclusion_restrictLE`). -/
theorem BState.inducedTriple_pullback_liftCorestrict :
    ((ChainState.inducedTriple T m st.toChainState).pullback
        ((st.L.stage (Fin.last _)).inclusion (st.liftOpen hVW))
        (isLocalDiffeomorph_inclusion _ _)).pullback
        (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _))
        (st.L.isLocalDiffeomorph_liftCorestrict _ _) =
      (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).induced m
        (st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _)) (st.shrink_hge hVW) := by
  have hL₁ := AnalyticTriple.isOfOrderGe_pullback _ m st.L st.hge
    (M.restrictLE (ChainState.le_of_closure_subset hVW)) (isLocalDiffeomorph_restrictLE _)
  rw [AnalyticTriple.pullback_pullback,
    AnalyticTriple.pullback_eq_of_eq _
        (AnalyticManifold.BlowUpSequence.inclusion_comp_liftCorestrict st.L _ _) _
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast st.L _ _)]
  exact (AnalyticTriple.induced_pullback _ m st.L st.hge _ _ hL₁).trans
    (AnalyticTriple.induced_congr
      (AnalyticTriple.pullback_inclusion_restrictLE T (ChainState.le_of_closure_subset hVW)) m _
      hL₁ (st.shrink_hge hVW))

include hcomp bo hid hV in
/-- **One link of the descent** at the bound `d ≥ m` ([Kol07, 111, Step 1];
[Wlo09, Theorem 7.4.1]): the value of the round, read on the lifted range of `V ⊆ W`, is appended
to the list restricted to `V` (`shrinkAppend`); the order clause by the order transfer and
`isOfOrderGe_shrinkAppend`; the invariant descends to `d − 1` (`bo.ord_lt` at the last stage, the
transform identity, the transport along the lift and through the concatenation). -/
def BState.descentLink (hT : AnalyticTriple.BMOClass m T) (hm : 1 ≤ m) (hmd : m ≤ d) :
    BState T m V (d - 1) where
  L := st.L.shrinkAppend (M.restrictLE (ChainState.le_of_closure_subset hVW))
    (isLocalDiffeomorph_restrictLE _) (st.roundValue bo hV hVW hT (hm.trans hmd))
  hge := by
    have h := st.L.isOfOrderGe_shrinkAppend (M.restrictLE (ChainState.le_of_closure_subset hVW))
      (isLocalDiffeomorph_restrictLE _)
      (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W))
      m st.hge (st.roundValue bo hV hVW hT (hm.trans hmd))
      (st.roundValue_isOfOrderGe hcomp bo hid hV hVW hT hm hmd)
    rwa [AnalyticTriple.pullback_inclusion_restrictLE T (ChainState.le_of_closure_subset hVW)] at h
  bound := by
    have hL₀' := st.roundValue_isOfOrderGe hcomp bo hid hV hVW hT hm hmd
    have hL₁ := st.shrink_hge hVW
    -- the value pulled back along the corestricted lift, of order ≥ m for the induced triple of the
    -- restricted list
    have h₂ := AnalyticTriple.isOfOrderGe_pullback _ m (st.roundValue bo hV hVW hT (hm.trans hmd))
      hL₀' (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
        (isLocalDiffeomorph_restrictLE _)) (st.L.isLocalDiffeomorph_liftCorestrict _ _)
    have e := st.inducedTriple_pullback_liftCorestrict hVW
    have hL₂ : ((st.roundValue bo hV hVW hT (hm.trans hmd)).pullback
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
    -- the bound at the last stage of the pulled-back value
    have hmain : NonmonomialOrdLe
        (((T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).induced m
          (st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
            (isLocalDiffeomorph_restrictLE _)) hL₁).induced m
          ((st.roundValue bo hV hVW hT (hm.trans hmd)).pullback
            (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
              (isLocalDiffeomorph_restrictLE _))
            (st.L.isLocalDiffeomorph_liftCorestrict _ _)) hL₂) (d - 1) := by
      rw [← AnalyticTriple.induced_congr e m _ h₂ hL₂,
        ← AnalyticTriple.induced_pullback _ m (st.roundValue bo hV hVW hT (hm.trans hmd)) hL₀'
          (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
            (isLocalDiffeomorph_restrictLE _)) (st.L.isLocalDiffeomorph_liftCorestrict _ _) h₂]
      intro y
      rw [hcomp (((ChainState.inducedTriple T m st.toChainState).pullback
          ((st.L.stage (Fin.last _)).inclusion (st.liftOpen hVW))
          (isLocalDiffeomorph_inclusion _ _)).induced m (st.roundValue bo hV hVW hT (hm.trans hmd))
          hL₀')
        ((st.roundValue bo hV hVW hT (hm.trans hmd)).pullbackLiftLast
          (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
            (isLocalDiffeomorph_restrictLE _)) (st.L.isLocalDiffeomorph_liftCorestrict _ _))
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)]
      change ((nonmonomialTriple (((ChainState.inducedTriple T m st.toChainState).pullback
        ((st.L.stage (Fin.last _)).inclusion (st.liftOpen hVW))
        (isLocalDiffeomorph_inclusion _ _)).induced m (st.roundValue bo hV hVW hT (hm.trans hmd))
        hL₀')).I.pullback _ _).ord y ≤ _
      rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _ y)]
        -- the transform identity at the last stage:
      -- N(marked transform of 𝓘) = marked transform of N(𝓘)
      have eN : (nonmonomialTriple (((ChainState.inducedTriple T m st.toChainState).pullback
            ((st.L.stage (Fin.last _)).inclusion (st.liftOpen hVW))
            (isLocalDiffeomorph_inclusion _ _)).induced m
            (st.roundValue bo hV hVW hT (hm.trans hmd)) hL₀')).I =
          (st.roundValue bo hV hVW hT (hm.trans hmd)).toSuccession.markedTransformSeq
            ((nonmonomialTriple (ChainState.inducedTriple T m st.toChainState)).pullback
              ((st.L.stage (Fin.last _)).inclusion (st.liftOpen hVW))
              (isLocalDiffeomorph_inclusion _ _)).I d (Fin.last _) :=
        (nonmonomialTriple_I _).trans
          ((hid ((ChainState.inducedTriple T m st.toChainState).pullback
              ((st.L.stage (Fin.last _)).inclusion (st.liftOpen hVW))
              (isLocalDiffeomorph_inclusion _ _)) (st.roundValue bo hV hVW hT (hm.trans hmd)) m d
              hm hmd (st.nonmonomialOrdLe_restrict hcomp hVW)
              (st.roundValue_isOfOrderGe_nonmonomial hcomp bo hV hVW hT (hm.trans hmd))
              (Fin.last _)).trans
            (congrArg (fun J =>
                (st.roundValue bo hV hVW hT (hm.trans hmd)).toSuccession.markedTransformSeq J d
                  (Fin.last _))
              (congrArg AnalyticTriple.I (hcomp (ChainState.inducedTriple T m st.toChainState)
                ((st.L.stage (Fin.last _)).inclusion (st.liftOpen hVW))
                (isLocalDiffeomorph_inclusion _ _)))))
      rw [eN]
      have hlt := (bo d).ord_lt (nonmonomialTriple (ChainState.inducedTriple T m st.toChainState))
        (st.boClass_nonmonomial hT (hm.trans hmd)) (st.liftOpen hVW)
        (st.isCompact_closure_liftOpen hV hVW)
        ((st.roundValue bo hV hVW hT (hm.trans hmd)).pullbackLiftLast
          (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
            (isLocalDiffeomorph_restrictLE _)) (st.L.isLocalDiffeomorph_liftCorestrict _ _) y)
      have hd1 : (d : ℕ∞) = ((d - 1 : ℕ) : ℕ∞) + 1 := by
        norm_cast
        omega
      rw [hd1] at hlt
      exact (ENat.lt_add_one_iff (ENat.natCast_ne_top _)).mp hlt
    -- transport through the concatenation
    change NonmonomialOrdLe
      ((T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).induced m
        ((st.L.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
          (isLocalDiffeomorph_restrictLE _)).concat
          ((st.roundValue bo hV hVW hT (hm.trans hmd)).pullback
            (st.L.liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
              (isLocalDiffeomorph_restrictLE _)) (st.L.isLocalDiffeomorph_liftCorestrict _ _))) _)
      (d - 1)
    exact nonmonomialOrdLe_induced_concat _ _ _ m (d - 1) hL₁ hL₂ _ hmain

end Round

end Link

end Hironaka.Manifold.BMOmod

end
