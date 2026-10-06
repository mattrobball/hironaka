/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step3Link
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Hironaka.Resolution.Analytic.Functor.EraseEmptyOrder
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.OrderReduction.Step21Functoriality
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The sequence over a relatively compact open: the terminal chain state and its value

Kollár's proof of the marked order reduction theorem [Kol07, Theorem 107] runs three steps on the
marked triple `(X, I, m, E)` [Kol07, 111]: the first lowers the order of the nonmonomial part
`N(I)` below `m`, the second separates `cosupp(I, m)` from `cosupp N(I)`, the third lowers the
order of the monomial part; each runs on the triple obtained at the end of the previous one, and
the proof ends with `max-ord I_r < m`, clause (1) of the theorem. On an analytic manifold the
value of the functor is read on each relatively compact open `U` [Wlo09, Theorem 2.0.3], and the
three steps cannot be composed as values on `M.restrict U`: a round of an order reduction functor
is read on a relatively compact open of the manifold at hand, which the last stage of a sequence
over `M.restrict U` is not. The steps are therefore composed as links of a chain (`ChainState`):
the list is built on a shrinking chain of relatively compact opens of `M` containing `closure U`,
every round is read on the lifted range of an inclusion, and the restriction to `U` with the
deletion of empty blow-ups [Kol07, 32] comes last.

This module joins the chain to the structure `BMOanFam`. **The terminal chain state**
`TerminalState T m W` is a `ChainState` whose induced triple has order `< m` at every point of the
last stage, the state the monomial step exits with; **its value on `U ≤ W`**,
`TerminalState.valueOn`, is the list of the state pulled back along the open inclusion and cleaned
of empty blow-ups. Its four exports are the facts `BMOanFam` reads on each open: no empty centres,
order `≥ m` for the restricted triple (`valueOn_isOfOrderGe`), stability under the deletion of
empty blow-ups, and clause (1) pointwise (`ord_lt_valueOn`: the marked transform at the last stage
of the value has order `< m` at every point over `U`). The last is the terminal bound transported
along the pull-back (`induced_pullback`, `pullback_inclusion_restrictLE`,
`ord_pullback_of_isLocalDiffeomorphAt`) and through the deletion of empty blow-ups
(`BlowUpSequence.markedTransformSeq_last_eraseEmpty`: the marked transform of the cleaned list is
the pull-back of that of the list along the diffeomorphism `eraseEmptyLast` of the last stages).

Three further lemmas transport the naturality properties from the states to the values: if the
lists of two terminal states agree on `U` up to empty blow-ups, the values satisfy the
compatibility `CompatibleFamily.compat`; if a terminal state for a pulled-back triple has, up to
empty blow-ups, the pulled-back list, the values satisfy the commutation with local analytic
isomorphisms; equal cleaned lists give equal values. The alignment of two chains, the substance of
[Kol07, 34.1] and of [Wlo09, Theorem 2.0.3 (4)] for the composite of the three steps, is proved
for the first step by a virtual descent over a pair of opens and continued through the other two
in `bmoSeqOn_compat`, `bmoSeqOn_pullback` and `bmoSeqOn_indiff`.

The sequence `bmoSeqOn` is the value of the terminal state of the three steps along the canonical
chain of `U` (`step23ChainState`). The scheme-theoretic counterpart is `Hironaka.BMO.bmoSeq`.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-! ### The terminal chain state -/

/-- **A terminal chain state**: a chain state over the open `W` (a list on `M.restrict W` of order
`≥ m` for the restricted triple) whose induced triple at the last stage has order `< m` at every
point, clause (1) of [Kol07, Theorem 107] on the state. It is the state the three steps exit with,
before the restriction to the relatively compact open and the deletion of empty blow-ups. -/
structure TerminalState (T : Manifold.AnalyticTriple ψ₀ M) (m : ℕ) (W : Opens M)
    extends ChainState T m W where
  /-- Clause (1) of [Kol07, Theorem 107] on the state: the marked transform at the last stage has
  order `< m` everywhere. -/
  ord_lt : ∀ x, (ChainState.inducedTriple T m toChainState).I.ord x < (m : ℕ∞)

namespace ChainState

open _root_.Manifold

variable {T : AnalyticTriple ψ₀ M} {m : ℕ}

/-- The list of a chain state over `W`, pulled back to an open `U ≤ W`, is of order `≥ m` for the
triple restricted to `U` (`isOfOrderGe_pullback` along the open inclusion,
`pullback_inclusion_restrictLE`). -/
theorem hge_pullback_restrictLE {W U : Opens M} (st : ChainState T m W)
    (hUW : U ≤ W) :
    (st.L.pullback (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE hUW)).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I m
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf := by
  have := finiteDimensional_of_chartIso ψ₀
  have h := AnalyticTriple.isOfOrderGe_pullback _ m _ st.hge (M.restrictLE hUW)
    (isLocalDiffeomorph_restrictLE hUW)
  rwa [AnalyticTriple.pullback_inclusion_restrictLE] at h

end ChainState

namespace TerminalState

open _root_.Manifold

variable {T : AnalyticTriple ψ₀ M} {m : ℕ}

/-! ### The value on a relatively compact open -/

/-- **The value of a terminal state on an open `U ≤ W`**: its list pulled back along the open
inclusion and cleaned of empty blow-ups [Kol07, 32]. The sequence of the functor over `U` is this
value at the state the three steps exit with. -/
def valueOn {W U : Opens M} (st : TerminalState T m W) (hUW : U ≤ W) :
    AnalyticManifold.BlowUpSequence ψ₀ (M.restrict U) :=
  (st.L.pullback (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE hUW)).eraseEmpty

/-- The value has no empty blow-ups [Kol07, 32]. -/
theorem valueOn_noEmptyCenters {W U : Opens M} (st : TerminalState T m W) (hUW : U ≤ W) :
    (st.valueOn hUW).NoEmptyCenters :=
  AnalyticManifold.BlowUpSequence.noEmptyCenters_eraseEmpty _

/-- The deletion of empty blow-ups is the identity on the value (`eraseEmpty_eraseEmpty`). -/
theorem eraseEmpty_valueOn {W U : Opens M} (st : TerminalState T m W) (hUW : U ≤ W) :
    (st.valueOn hUW).eraseEmpty = st.valueOn hUW :=
  AnalyticManifold.BlowUpSequence.eraseEmpty_eraseEmpty _

/-- The value is a smooth blow-up sequence of order `≥ m` for the triple restricted to `U`
[Kol07, Definition 66 (2′)–(4′)]: the invariant of the chain along the inclusion, kept by the
deletion of empty blow-ups. -/
theorem valueOn_isOfOrderGe {W U : Opens M} (st : TerminalState T m W)
    (hUW : U ≤ W) :
    (st.valueOn hUW).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I m
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf :=
  have := finiteDimensional_of_chartIso ψ₀
  AnalyticManifold.BlowUpSequence.isOfOrderGe_eraseEmpty _ _ _
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc
    (st.hge_pullback_restrictLE hUW)

/-- Clause (1) of [Kol07, Theorem 107] on the value, pointwise: the marked transform at the last
stage of the value has order `< m` at every point over `U`. The terminal bound of the state is
transported along the pull-back (`induced_pullback`: the induced triple of the pulled-back list is
the pull-back of the induced triple along the lift of the last stages;
`ord_pullback_of_isLocalDiffeomorphAt`) and through the deletion of empty blow-ups
(`BlowUpSequence.markedTransformSeq_last_eraseEmpty`). -/
theorem ord_lt_valueOn {W U : Opens M} (st : TerminalState T m W)
    (hUW : U ≤ W) (x : (st.valueOn hUW).toSuccession.stage (Fin.last _)) :
    ((st.valueOn hUW).toSuccession.markedTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I m (Fin.last _)).ord x
      < (m : ℕ∞) := by
  have := finiteDimensional_of_chartIso ψ₀
  have h0 := AnalyticTriple.isOfOrderGe_pullback _ m _ st.hge (M.restrictLE hUW)
    (isLocalDiffeomorph_restrictLE hUW)
  have hL' := st.hge_pullback_restrictLE hUW
  unfold valueOn at x ⊢
  rw [AnalyticManifold.BlowUpSequence.markedTransformSeq_last_eraseEmpty _ _ _ m hL']
  change (((st.L.pullback (M.restrictLE hUW)
        (isLocalDiffeomorph_restrictLE hUW)).toSuccession.markedTransformSeq
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I m (Fin.last _)).pullback
      ⇑(st.L.pullback (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE hUW)).eraseEmptyLast.symm
      _).ord x < _
  rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
    ((st.L.pullback (M.restrictLE hUW)
      (isLocalDiffeomorph_restrictLE hUW)).eraseEmptyLast.symm.isLocalDiffeomorph x)]
  have e1 : (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).induced m
      (st.L.pullback (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE hUW)) hL' =
      ((T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).pullback (M.restrictLE hUW)
        (isLocalDiffeomorph_restrictLE hUW)).induced m
        (st.L.pullback (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE hUW)) h0 :=
    AnalyticTriple.induced_congr (AnalyticTriple.pullback_inclusion_restrictLE T hUW).symm m _ hL'
      h0
  have e2 := AnalyticTriple.induced_pullback
    (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)) m st.L st.hge
    (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE hUW) h0
  have eI := congrArg AnalyticTriple.I (e1.trans e2.symm)
  rw [AnalyticTriple.induced_I] at eI
  rw [eI]
  change ((((T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).induced m st.L
      st.hge).I).pullback
      ⇑(st.L.pullbackLiftLast (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE hUW))
      _).ord _ < _
  rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast st.L (M.restrictLE hUW)
      (isLocalDiffeomorph_restrictLE hUW) _)]
  exact st.ord_lt _

/-! ### The three naturality transports, from the states to the values -/

/-- The compatibility `CompatibleFamily.compat` on the values ([Wlo09, Theorem 2.0.3 (4)],
[Wlo09, Definition 3.2.6]; [Kol07, 34.1]): two terminal states whose lists agree on `U ≤ V` up to
empty blow-ups have compatible values (`eraseEmpty_pullback_eraseEmpty`). -/
theorem valueOn_eq_pullback_eraseEmpty_of_rel {W₁ W₂ U V : Opens M} (st₁ : TerminalState T m W₁)
    (st₂ : TerminalState T m W₂) (hUW₁ : U ≤ W₁) (hVW₂ : V ≤ W₂) (hUV : U ≤ V)
    (hrel : (st₁.L.pullback (M.restrictLE hUW₁) (isLocalDiffeomorph_restrictLE hUW₁)).eraseEmpty =
      ((st₂.L.pullback (M.restrictLE hVW₂) (isLocalDiffeomorph_restrictLE hVW₂)).pullback
        (M.restrictLE hUV) (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty) :
    st₁.valueOn hUW₁ =
      ((st₂.valueOn hVW₂).pullback (M.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty := by
  unfold valueOn
  rw [AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty]
  exact hrel

/-- The commutation with local analytic isomorphisms on the values [Kol07, 34.1]: a terminal state
for the triple pulled back along a local analytic isomorphism `g`, whose cleaned list is the
cleaned pull-back of the list of a terminal state along `g|_{W'}`, has on `U' ≤ W'` the value on
`g(U')` pulled back along `g|_{U'}` and cleaned (`eraseEmpty_pullback_eraseEmpty`, `pullback_comp`:
both sides are the list pulled back along the same map `U' → W`). -/
theorem valueOn_pullback_of_rel {N : AnalyticManifold.{u} 𝕜 E} (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) {W : Opens M} {W' : Opens N}
    (hWW' : ⇑g '' (W' : Set N) ⊆ W) (st : TerminalState T m W)
    (st' : TerminalState (T.pullback g hg) m W')
    (hrel : st'.L.eraseEmpty = (st.L.pullback (AnalyticMap.restrictMap g W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hg W' W hWW')).eraseEmpty)
    {U' : Opens N} (hU'W' : U' ≤ W') (hU'W : AnalyticMap.imageOpens g hg U' ≤ W) :
    st'.valueOn hU'W' =
      ((st.valueOn hU'W).pullback
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
          Set.Subset.rfl)).eraseEmpty := by
  unfold valueOn
  rw [← AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty st'.L, hrel,
    AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
        AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
    AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _,
        AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _]
  exact congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
    (AnalyticManifold.BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ =>
        Subtype.ext rfl) _ _)

/-- The indifference to empty boundary members on the values (the counterpart, for boundary
members, of [Kol07, 32]): two terminal states, for
two triples on `M`, with the same cleaned list have the same value on every `U`. -/
theorem valueOn_eq_of_eraseEmpty_eq {T' : AnalyticTriple ψ₀ M} {W U : Opens M}
    (st : TerminalState T m W) (st' : TerminalState T' m W) (hUW : U ≤ W)
    (hL : st'.L.eraseEmpty = st.L.eraseEmpty) : st'.valueOn hUW = st.valueOn hUW := by
  unfold valueOn
  rw [← AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty st'.L, hL,
    AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty]

end TerminalState

/-! ### The sequence over a relatively compact open: the value and its four order/erase exports -/

namespace BMO

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (m : ℕ)
  (hT : AnalyticTriple.BMOClass m T) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : BMOmod.NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hid : BMOmod.NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hidN : NonmonomialTransformIdentityMod.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (st3 : MonomialStep3Fam.{u} 𝕜 n m) (U : Opens M) (hU : IsCompact (closure (U : Set M)))

/-- **The sequence `BMO_{n,m}(M, 𝓘, m, E)` over the relatively compact open `U`**
[Kol07, Theorem 107]: the three steps run as one chain of links on shrinking opens containing
`closure U` (the descent of the first step, `stepAChainState`, continued by the descent of the
separation step and the link of the monomial step, `step23ChainState`, at the threshold `t = m`),
and the terminal state, whose induced triple has order `< m` (`step23ChainState_ord_lt`), is
restricted to `U` and cleaned of empty blow-ups (`TerminalState.valueOn`). The order reductions
`bo`, the pull-back property of the nonmonomial part `hcomp`, the two transform identities `hid`
and `hidN`, and the monomial procedure `st3` are parameters. The scheme-theoretic counterpart is
`Hironaka.BMO.bmoSeq`. -/
def bmoSeqOn : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    (M.restrict U) :=
  (⟨step23ChainState T m hT bo hcomp hid hidN st3 m hT.1 le_rfl U hU,
    step23ChainState_ord_lt T m hT bo hcomp hid hidN st3 m hT.1 le_rfl U hU⟩ :
      TerminalState T m (step23ChainOpen T m U hU)).valueOn (le_step23ChainOpen T m U hU)

/-- The sequence over `U` is a smooth blow-up sequence of order `≥ m` for the triple restricted to
`U` [Kol07, Definition 66 (2′)–(4′)] (`TerminalState.valueOn_isOfOrderGe`). -/
theorem bmoSeqOn_isOfOrderGe :
    (bmoSeqOn T m hT bo hcomp hid hidN st3 U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I m
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf :=
  TerminalState.valueOn_isOfOrderGe
    (⟨step23ChainState T m hT bo hcomp hid hidN st3 m hT.1 le_rfl U hU,
      step23ChainState_ord_lt T m hT bo hcomp hid hidN st3 m hT.1 le_rfl U hU⟩ :
        TerminalState T m (step23ChainOpen T m U hU)) (le_step23ChainOpen T m U hU)

/-- The sequence has no empty blow-ups [Kol07, 32]. -/
theorem bmoSeqOn_noEmptyCenters : (bmoSeqOn T m hT bo hcomp hid hidN st3 U hU).NoEmptyCenters :=
  TerminalState.valueOn_noEmptyCenters
    (⟨step23ChainState T m hT bo hcomp hid hidN st3 m hT.1 le_rfl U hU,
      step23ChainState_ord_lt T m hT bo hcomp hid hidN st3 m hT.1 le_rfl U hU⟩ :
        TerminalState T m (step23ChainOpen T m U hU)) (le_step23ChainOpen T m U hU)

/-- The deletion of empty blow-ups is the identity on the sequence. -/
theorem eraseEmpty_bmoSeqOn :
    (bmoSeqOn T m hT bo hcomp hid hidN st3 U hU).eraseEmpty =
      bmoSeqOn T m hT bo hcomp hid hidN st3 U hU :=
  TerminalState.eraseEmpty_valueOn
    (⟨step23ChainState T m hT bo hcomp hid hidN st3 m hT.1 le_rfl U hU,
      step23ChainState_ord_lt T m hT bo hcomp hid hidN st3 m hT.1 le_rfl U hU⟩ :
        TerminalState T m (step23ChainOpen T m U hU)) (le_step23ChainOpen T m U hU)

/-- Clause (1) of [Kol07, Theorem 107] on the sequence over `U`, pointwise: the marked transform at
the last stage has order `< m` at every point (`TerminalState.ord_lt_valueOn`). -/
theorem ord_lt_bmoSeqOn
    (x : (bmoSeqOn T m hT bo hcomp hid hidN st3 U hU).toSuccession.stage (Fin.last _)) :
    ((bmoSeqOn T m hT bo hcomp hid hidN st3 U hU).toSuccession.markedTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I m (Fin.last _)).ord x
      < (m : ℕ∞) :=
  TerminalState.ord_lt_valueOn
    (⟨step23ChainState T m hT bo hcomp hid hidN st3 m hT.1 le_rfl U hU,
      step23ChainState_ord_lt T m hT bo hcomp hid hidN st3 m hT.1 le_rfl U hU⟩ :
        TerminalState T m (step23ChainOpen T m U hU)) (le_step23ChainOpen T m U hU) x

end BMO

end Hironaka.Manifold

end
