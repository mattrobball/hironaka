/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepAChain
public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
public import Hironaka.Resolution.Analytic.Functor.EraseEmptyConcat
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.OrderReduction.Modified.InducedValueFunctor
import Hironaka.Resolution.Analytic.OrderReduction.Modified.NonmonomialIndiff
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bFunctor
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepATransport
import Hironaka.Resolution.Analytic.OrderReduction.Step21ErasePrep
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The rounds on the nonmonomial part: the empty-link lemma and the alignment of two descents

**The empty-link lemma**: the value of the order reduction `BO_{n,d}` on an open where the ideal has
order `< d` everywhere is the empty list, since its centres lie where the order is `≥ d`
([Kol07, Definition 66 (4′)], the order clause of the family) and none of them is empty
([Kol07, 32], the absence of empty centres), so there is no first centre (`BOanFam.seqOn_eq_nil`,
`BState.roundValue_eq_nil`). Hence a link of the descent at a bound `d` above the maximal order of
`N(𝓘)` appends nothing: the list of the state is only restricted
(`BState.descentLink_eraseEmpty_of_roundValue_nil`).

**The alignment of two descents** (`descentStateAux_rel`): along a local analytic isomorphism
`h : N → M`, a descent over `N` for the pulled-back triple from a bound `DX` along a chain `X`, and
a descent over `M` from a bound `D ≤ DX` along a chain `W` with `h(X j) ⊆ W (j − (DX − D))`,
produce lists which agree up to empty blow-ups after pulling back: the first `DX − D` links over
`N` are empty (the bound `D` holds on `X j` through `h`), and from then on the two descents run at
the same bound and `descentLink_rel` carries the relation link by link (the bounds identified by
`BState.castBound`). This is the inductive engine of the compatibility of the values, of the
independence of the value from the outer open and the chain, and of the commutation with local
isomorphisms (the second condition of [Kol07, 34.1]); the applications are in `StepACompat.lean`,
`StepAIndep.lean` and `StepAComm.lean`.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

open Hironaka.Manifold.BMO

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

/-! ### The empty-link lemma -/

/-- **The empty-link lemma** ([Kol07, Definition 66 (4′)] with [Kol07, 32]): the value of `BO_{n,d}`
on an open where `ord 𝓘 < d` everywhere is the empty list, since a first centre would lie where the
order is `≥ d` (`isOfOrderGe`, `ordAlongIdeal_le_ord_of_mem_support`) and be nonempty
(`noEmptyCenters`). -/
theorem _root_.Hironaka.Manifold.BOanFam.seqOn_eq_nil {d : ℕ} (bo : BOanFam.{u} 𝕜 n d)
    {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (S : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    (hS : AnalyticTriple.BOClass d S) (U : Opens X) (hU : IsCompact (closure (U : Set X)))
    (hlt : ∀ x ∈ (U : Set X), S.I.ord x < (d : ℕ∞)) :
    (bo.functor.fam S hS).seqOn U hU = AnalyticManifold.BlowUpSequence.nil _ := by
  have hord := bo.isOfOrderGe S hS U hU
  have hne := (bo.functor.fam S hS).noEmptyCenters U hU
  generalize (bo.functor.fam S hS).seqOn U hU = L at hord hne ⊢
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
      (S.pullback (X.inclusion U) (isLocalDiffeomorph_inclusion X U)).I hmem
    have h3 : ((S.pullback (X.inclusion U) (isLocalDiffeomorph_inclusion X U)).I).ord y <
        (d : ℕ∞) := by
      change ((S.I).pullback _ _).ord y < _
      rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
        (isLocalDiffeomorph_inclusion _ _ y)]
      exact hlt y.1 y.2
    exact absurd (h.trans h2) (not_le.mpr h3)

section Round

variable {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  {T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M} {m : ℕ}
  (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hT : AnalyticTriple.BMOClass m T) {W : Opens M} {d : ℕ} (st : BState T m W d) {V : Opens M}
  (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W)

/-- The empty-link lemma at a link of the descent: when the invariant holds at a bound `D < d`, the
value of the round is the empty list. -/
theorem BState.roundValue_eq_nil (hd : 1 ≤ d) {D : ℕ}
    (hb : NonmonomialOrdLe (ChainState.inducedTriple T m st.toChainState) D) (hDd : D < d) :
    st.roundValue bo hV hVW hT hd = AnalyticManifold.BlowUpSequence.nil _ :=
  (bo d).seqOn_eq_nil (nonmonomialTriple (ChainState.inducedTriple T m st.toChainState))
    (st.boClass_nonmonomial hT hd) (st.liftOpen hVW) (st.isCompact_closure_liftOpen hV hVW)
    fun x _ => (hb x).trans_lt (by exact_mod_cast hDd)

/-- A link whose round has the empty value restricts the list (`shrinkAppend` with the empty list,
`concat_nil_right`); up to empty blow-ups it is the cleaned list restricted. -/
theorem BState.descentLink_eraseEmpty_of_roundValue_nil (hm : 1 ≤ m) (hmd : m ≤ d)
    (hnil : st.roundValue bo hV hVW hT (hm.trans hmd) = AnalyticManifold.BlowUpSequence.nil _) :
    (st.descentLink hcomp bo hid hV hVW hT hm hmd).L.eraseEmpty =
      (st.L.eraseEmpty.pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
        (isLocalDiffeomorph_restrictLE _)).eraseEmpty := by
  rw [st.descentLink_L hcomp bo hid hT hm hV hVW hmd, hnil,
    AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty]
  unfold AnalyticManifold.BlowUpSequence.shrinkAppend
  rw [AnalyticManifold.BlowUpSequence.pullback_nil,
      AnalyticManifold.BlowUpSequence.concat_nil_right]

/-! ### The invariant through `eraseEmpty` and along pull-backs -/

variable {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

include hcomp in
/-- The order bound on `N(𝓘)` pulls back along local analytic isomorphisms (`NonmonomialComap`,
`ord_pullback_of_isLocalDiffeomorphAt`). -/
theorem nonmonomialOrdLe_pullback {S : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M}
    {D : ℕ} (hb : NonmonomialOrdLe S D) (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g) :
    NonmonomialOrdLe (S.pullback g hg) D := by
  intro x
  rw [hcomp S g hg]
  change ((nonmonomialTriple S).I.pullback _ _).ord x ≤ _
  rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _ (hg x)]
  exact hb _

/-- The bound transports along an equality of lists (a `subst`). -/
theorem NonmonomialOrdLe.of_induced_eq {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    {TW : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X} {s : ℕ}
    {L₁ L₂ : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X}
        (e : L₁ = L₂)
    (hL₁ : L₁.toSuccession.IsOfOrderGe TW.I s TW.F.idealSheaf)
    (hL₂ : L₂.toSuccession.IsOfOrderGe TW.I s TW.F.idealSheaf) {D : ℕ}
    (hb : NonmonomialOrdLe (TW.induced s L₁ hL₁) D) : NonmonomialOrdLe (TW.induced s L₂ hL₂) D := by
  subst e
  exact hb

/-- The bound at the induced triple of the empty list is the bound on the triple
(`induced_nil`). -/
theorem nonmonomialOrdLe_induced_nil_iff {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (TW : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X) (s : ℕ)
    (hL : (AnalyticManifold.BlowUpSequence.nil X).toSuccession.IsOfOrderGe TW.I s TW.F.idealSheaf)
        (D : ℕ) :
    NonmonomialOrdLe (TW.induced s (AnalyticManifold.BlowUpSequence.nil X) hL) D ↔ NonmonomialOrdLe
        TW D :=
  Iff.of_eq (by rw [AnalyticTriple.induced_nil]; rfl)

include hcomp in
/-- **The ideal `N` of the induced triple is the pull-back of the ideal `N` of the induced triple of
the cleaned list along `eraseEmptyLast`** ([Kol07, 32] and its counterpart for boundary members):
the induced triple is that
pull-back up to empty boundary members (`induced_eq_pullback_induced_eraseEmpty`), `N` ignores them
(`nonmonomialTriple_eq_of_isEmptyExtension`) and commutes with the pull-back (`NonmonomialComap`).
Every identification goes through the projection lemmas by `congrArg`. -/
theorem nonmonomialTriple_induced_I_eq_pullback_eraseEmpty
    {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (TW : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X) (s : ℕ)
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    (hL : L.toSuccession.IsOfOrderGe TW.I s TW.F.idealSheaf)
    (hLe : L.eraseEmpty.toSuccession.IsOfOrderGe TW.I s TW.F.idealSheaf) :
    (nonmonomialTriple (TW.induced s L hL)).I =
      ((nonmonomialTriple (TW.induced s L.eraseEmpty hLe)).pullback
        (Diffeomorph.toAnalyticMap L.eraseEmptyLast) L.eraseEmptyLast.isLocalDiffeomorph).I := by
  have htriple := AnalyticTriple.induced_eq_pullback_induced_eraseEmpty TW s L hL hLe
  have hext := AnalyticTriple.isEmptyExtension_eraseEmptyIdx_induced TW s L hL hLe
  have hI := congrArg AnalyticTriple.I (nonmonomialTriple_eq_of_isEmptyExtension
    (TW.induced s L hL)
    ((TW.induced s L.eraseEmpty hLe).F.comap ⇑(Diffeomorph.toAnalyticMap L.eraseEmptyLast))
    (HypersurfaceFamily.isSnc_comap (TW.induced s L.eraseEmpty hLe).isSnc _
      L.eraseEmptyLast.isLocalDiffeomorph) hext)
  dsimp only at hI
  have hI' := congrArg AnalyticTriple.I (hcomp (TW.induced s L.eraseEmpty hLe)
    (Diffeomorph.toAnalyticMap L.eraseEmptyLast) L.eraseEmptyLast.isLocalDiffeomorph)
  rw [← hI, htriple, hI']

include hcomp in
/-- The bound at the induced triple of the cleaned list gives the bound at the induced triple of the
list (`nonmonomialTriple_induced_I_eq_pullback_eraseEmpty`,
`ord_pullback_of_isLocalDiffeomorphAt`). -/
theorem NonmonomialOrdLe.of_induced_eraseEmpty {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (TW : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X) (s : ℕ)
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    (hL : L.toSuccession.IsOfOrderGe TW.I s TW.F.idealSheaf)
    (hLe : L.eraseEmpty.toSuccession.IsOfOrderGe TW.I s TW.F.idealSheaf) {D : ℕ}
    (hb : NonmonomialOrdLe (TW.induced s L.eraseEmpty hLe) D) :
    NonmonomialOrdLe (TW.induced s L hL) D := by
  intro x
  rw [nonmonomialTriple_induced_I_eq_pullback_eraseEmpty hcomp TW s L hL hLe]
  change ((nonmonomialTriple (TW.induced s L.eraseEmpty hLe)).I.pullback ⇑L.eraseEmptyLast
    _).ord x ≤ _
  rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _ (L.eraseEmptyLast.isLocalDiffeomorph x)]
  exact hb _

include hcomp in
/-- The converse: the bound at the induced triple of the list gives the bound at the induced triple
of the cleaned list (`eraseEmptyLast` is onto). -/
theorem NonmonomialOrdLe.induced_eraseEmpty {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (TW : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X) (s : ℕ)
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    (hL : L.toSuccession.IsOfOrderGe TW.I s TW.F.idealSheaf)
    (hLe : L.eraseEmpty.toSuccession.IsOfOrderGe TW.I s TW.F.idealSheaf) {D : ℕ}
    (hb : NonmonomialOrdLe (TW.induced s L hL) D) :
    NonmonomialOrdLe (TW.induced s L.eraseEmpty hLe) D := by
  intro y
  have h := hb (L.eraseEmptyLast.symm y)
  rw [nonmonomialTriple_induced_I_eq_pullback_eraseEmpty hcomp TW s L hL hLe] at h
  change ((nonmonomialTriple (TW.induced s L.eraseEmpty hLe)).I.pullback ⇑L.eraseEmptyLast
    _).ord _ ≤ _ at h
  rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
    (L.eraseEmptyLast.isLocalDiffeomorph _), Diffeomorph.apply_symm_apply] at h
  exact h

/-! ### Re-typing a state at an equal bound -/

variable (T) (m) in
/-- The same state at a propositionally equal bound (the bounds of two aligned descents are equal
natural numbers, not the same terms). -/
def BState.castBound {W : Opens M} {d d' : ℕ} (e : d = d') (st : BState T m W d) :
    BState T m W d' :=
  ⟨st.toChainState, e ▸ st.bound⟩

theorem BState.castBound_L {W : Opens M} {d d' : ℕ} (e : d = d') (st : BState T m W d) :
    (BState.castBound T m e st).L = st.L := rfl

/-- The link of a re-typed state is the re-typed link (a substitution). -/
theorem BState.castBound_descentLink {W : Opens M} {d d' : ℕ} (e : d = d') (st : BState T m W d)
    {V : Opens M} (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W)
    (hm : 1 ≤ m) (hmd : m ≤ d') :
    (BState.castBound T m e st).descentLink hcomp bo hid hV hVW hT hm hmd =
      BState.castBound T m (by omega)
        (st.descentLink hcomp bo hid hV hVW hT hm (by omega)) := by
  subst e
  rfl

end Round

/-! ### The alignment of two descents -/

section Align

variable {M N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (m : ℕ)
  (hT : AnalyticTriple.BMOClass m T) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (t : ℕ) (hm : 1 ≤ m) (hmt : m ≤ t)
  (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω h)
  (hT' : AnalyticTriple.BMOClass m (T.pullback h hh))
  (W : ℕ → Opens M) (hW : ∀ k, IsCompact (closure (W k : Set M))) (r : ℕ)
  (hWsub : ∀ k, k < r → closure (W (k + 1) : Set M) ⊆ W k) (D : ℕ)
  (hD : ∀ x ∈ (W 0 : Set M), (nonmonomialTriple T).I.ord x ≤ (D : ℕ∞))
  (X : ℕ → Opens N) (hX : ∀ j, IsCompact (closure (X j : Set N))) (rX : ℕ)
  (hXsub : ∀ j, j < rX → closure (X (j + 1) : Set N) ⊆ X j) (DX : ℕ)
  (hDX : ∀ x ∈ (X 0 : Set N), (nonmonomialTriple (T.pullback h hh)).I.ord x ≤ (DX : ℕ∞))
  (hDD : D ≤ DX) (hrr : rX ≤ (DX - D) + r) (hXW : ∀ j, ⇑h '' (X j : Set N) ⊆ W (j - (DX - D)))

/-- The right-hand side of the alignment: the `k`-th state of the descent over `M`, pulled back
along `h` to the `j`-th open of the chain over `N` and cleaned of empty blow-ups (its type does not
depend on `k`). -/
def alignRHS (j k : ℕ) (hk : k ≤ r) (hkt : k ≤ D + 1 - t) (hXWk : ⇑h '' (X j : Set N) ⊆ W k) :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (N.restrict (X j)) :=
  ((descentStateAux T m hT bo hcomp hid t hm hmt W hW r hWsub D hD k hk hkt).L.pullback
    (AnalyticMap.restrictMap h (X j) (W k) hXWk)
    (AnalyticMap.isLocalDiffeomorph_restrictMap hh _ _ hXWk)).eraseEmpty

/-- `alignRHS` depends on the index `k` only through its value (a substitution). -/
theorem alignRHS_congr {j k k' : ℕ} (e : k = k') (hk : k ≤ r) (hkt : k ≤ D + 1 - t)
    (hXWk : ⇑h '' (X j : Set N) ⊆ W k) (hk' : k' ≤ r) (hkt' : k' ≤ D + 1 - t)
    (hXWk' : ⇑h '' (X j : Set N) ⊆ W k') :
    alignRHS T m hT bo hcomp hid t hm hmt h hh W hW r hWsub D hD X j k hk hkt hXWk =
      alignRHS T m hT bo hcomp hid t hm hmt h hh W hW r hWsub D hD X j k' hk' hkt' hXWk' := by
  subst e
  rfl

/-- At `k = 0` the right-hand side is `nil` (the initial state has no blow-ups). -/
theorem alignRHS_zero (j : ℕ) (hkt : 0 ≤ D + 1 - t) (hXWk : ⇑h '' (X j : Set N) ⊆ W 0) :
    alignRHS T m hT bo hcomp hid t hm hmt h hh W hW r hWsub D hD X j 0 (Nat.zero_le _) hkt hXWk =
      AnalyticManifold.BlowUpSequence.nil _ := rfl

include hDD hrr hXW hT' hX hXsub hDX in
/-- **The alignment of two descents** (the inductive engine of the compatibility of the values and
of the second condition of [Kol07, 34.1] for the rounds): the `j`-th state of the descent over `N`
(bound `DX`, chain `X`) and the `(j − (DX − D))`-th state of the descent over `M` (bound `D ≤ DX`,
chain `W`), pulled back along `h`, agree up to empty blow-ups. For `j < DX − D` the link over `N`
runs at a bound above `D`, which bounds `ord N` on `X j` through `h`, so its value is the empty list
(the empty-link lemma) and both sides stay empty; from `j = DX − D` on the two descents run at the
same bound and `descentLink_rel` carries the relation. -/
theorem descentStateAux_rel : ∀ j (hj : j ≤ rX) (hjt : j ≤ DX + 1 - t),
    (descentStateAux (T.pullback h hh) m hT' bo hcomp hid t hm hmt X hX rX hXsub DX hDX j hj
      hjt).L.eraseEmpty =
      alignRHS T m hT bo hcomp hid t hm hmt h hh W hW r hWsub D hD X j (j - (DX - D)) (by omega)
        (by omega) (hXW j)
  | 0, _, _ => by
    rw [alignRHS_congr T m hT bo hcomp hid t hm hmt h hh W hW r hWsub D hD X
      (show 0 - (DX - D) = 0 by omega) _ _ _ (Nat.zero_le _) (by omega) (by
        have := hXW 0
        rwa [show 0 - (DX - D) = 0 by omega] at this),
      alignRHS_zero]
    rfl
  | j + 1, hj, hjt => by
    have ih := descentStateAux_rel j (Nat.le_of_succ_le hj) (Nat.le_of_succ_le hjt)
    by_cases hcase : j + 1 ≤ DX - D
    · -- the link over `N` runs at a bound above `D`: the empty list
      have hXW0 : ⇑h '' (X j : Set N) ⊆ W 0 := by
        have := hXW j
        rwa [show j - (DX - D) = 0 by omega] at this
      have hXW0' : ⇑h '' (X (j + 1) : Set N) ⊆ W 0 := by
        have := hXW (j + 1)
        rwa [show j + 1 - (DX - D) = 0 by omega] at this
      rw [alignRHS_congr T m hT bo hcomp hid t hm hmt h hh W hW r hWsub D hD X
        (show j - (DX - D) = 0 by omega) _ _ _ (Nat.zero_le _) (by omega) hXW0,
        alignRHS_zero] at ih
      rw [alignRHS_congr T m hT bo hcomp hid t hm hmt h hh W hW r hWsub D hD X
        (show j + 1 - (DX - D) = 0 by omega) _ _ _ (Nat.zero_le _) (by omega) hXW0',
        alignRHS_zero]
      -- the bound `D` holds on the induced triple of the state over `X j`
      have hb0 : ∀ y ∈ (X j : Set N), (nonmonomialTriple (T.pullback h hh)).I.ord y ≤ (D : ℕ∞) := by
        intro y hy
        rw [hcomp T h hh]
        change ((nonmonomialTriple T).I.pullback _ _).ord y ≤ _
        rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _ (hh y)]
        exact hD _ (hXW0 ⟨y, hy, rfl⟩)
      have hb1 : NonmonomialOrdLe ((T.pullback h hh).pullback (N.inclusion (X j))
          (isLocalDiffeomorph_inclusion N (X j))) D := by
        intro z
        rw [hcomp]
        change ((nonmonomialTriple (T.pullback h hh)).I.pullback _ _).ord z ≤ _
        rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
          (isLocalDiffeomorph_inclusion _ _ z)]
        exact hb0 z.1 z.2
      have hb : NonmonomialOrdLe (ChainState.inducedTriple (T.pullback h hh) m
          (descentStateAux (T.pullback h hh) m hT' bo hcomp hid t hm hmt X hX rX hXsub DX hDX j
            (Nat.le_of_succ_le hj) (Nat.le_of_succ_le hjt)).toChainState) D := by
        have hLe := AnalyticManifold.BlowUpSequence.isOfOrderGe_eraseEmpty _ _ m
          ((T.pullback h hh).pullback (N.inclusion (X j))
            (isLocalDiffeomorph_inclusion N (X j))).isSnc
          (descentStateAux (T.pullback h hh) m hT' bo hcomp hid t hm hmt X hX rX hXsub DX hDX j
            (Nat.le_of_succ_le hj) (Nat.le_of_succ_le hjt)).hge
        refine NonmonomialOrdLe.of_induced_eraseEmpty hcomp _ m _ _ hLe ?_
        refine NonmonomialOrdLe.of_induced_eq ih.symm (by rw [← ih]; exact hLe) hLe ?_
        exact (nonmonomialOrdLe_induced_nil_iff _ m _ D).mpr hb1
      have hnil := (descentStateAux (T.pullback h hh) m hT' bo hcomp hid t hm hmt X hX rX hXsub DX
        hDX j (Nat.le_of_succ_le hj) (Nat.le_of_succ_le hjt)).roundValue_eq_nil bo hT'
        (hX (j + 1)) (hXsub j hj) (hm.trans (by omega)) hb (by omega)
      change ((descentStateAux (T.pullback h hh) m hT' bo hcomp hid t hm hmt X hX rX hXsub DX hDX j
        (Nat.le_of_succ_le hj) (Nat.le_of_succ_le hjt)).descentLink hcomp bo hid (hX (j + 1))
        (hXsub j hj) hT' hm (by omega)).L.eraseEmpty = _
      rw [BState.descentLink_eraseEmpty_of_roundValue_nil bo hcomp hid hT' _ (hX (j + 1))
        (hXsub j hj) hm (by omega) hnil, ih, AnalyticManifold.BlowUpSequence.pullback_nil,
            AnalyticManifold.BlowUpSequence.eraseEmpty_nil]
    · -- the two descents run at the same bound: `descentLink_rel`
      have hj₀ : DX - D ≤ j := by omega
      have hXW' : ⇑h '' (X (j + 1) : Set N) ⊆ W (j - (DX - D) + 1) := by
        have := hXW (j + 1)
        rwa [show j + 1 - (DX - D) = j - (DX - D) + 1 by omega] at this
      rw [alignRHS_congr T m hT bo hcomp hid t hm hmt h hh W hW r hWsub D hD X
        (show j + 1 - (DX - D) = j - (DX - D) + 1 by omega) _ _ _ (by omega) (by omega) hXW']
      have e : DX - j = D - (j - (DX - D)) := by omega
      have hrel := descentLink_rel hcomp bo hid hT hm h hh rfl hT' (hXW j)
        (descentStateAux T m hT bo hcomp hid t hm hmt W hW r hWsub D hD (j - (DX - D)) (by omega)
          (by omega))
        (BState.castBound (T.pullback h hh) m e (descentStateAux (T.pullback h hh) m hT' bo hcomp
          hid t hm hmt X hX rX hXsub DX hDX j (Nat.le_of_succ_le hj) (Nat.le_of_succ_le hjt)))
        ih (hW (j - (DX - D) + 1)) (hWsub _ (by omega)) (hX (j + 1)) (hXsub j hj) hXW' (by omega)
      rw [BState.castBound_descentLink] at hrel
      exact hrel

end Align

end Hironaka.Manifold.BMOmod

end
