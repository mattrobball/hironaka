/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepALink
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The rounds on the nonmonomial part: the descent along a shrinking chain

The rounds of order reduction on the nonmonomial part ([Kol07, 111, Step 1]; the first phase of
the modified algorithm of [Wlo09, Theorem 7.4.1], "until we drop `max ord N(I)` to 1") are run as
a **descent through the bounds** `d = D, D − 1, …, t`: `D` is a bound of `ord N(𝓘)` on the first
open of a shrinking chain `W 0 ⊇ closure (W 1) ⊇ W 1 ⊇ ⋯ ⊇ W r` of relatively compact opens
(canonically `D = roundOrderOn T U₀`, the maximum of `ord N(𝓘)` on the closure of an outer open
`U₀ ⊇ W 0`, see `StepAFamily.lean`), and at every `d` one link (`BState.descentLink`) runs on the
next two opens of the chain, `r = D + 1 − t` links in all (`descentStateAux`, `descentState`). At a
bound `d` above the current maximal order of `N(𝓘)` the value of the round is the empty list (the
centres of a sequence of order `≥ d` lie where the order is `≥ d`, and none is empty; see
`BOanFam.seqOn_eq_nil`), so the nonempty links are the rounds at `d = max-ord N(𝓘)` in the order
of the sources. The state after the last link satisfies `max-ord N(𝓘_ind) ≤ t − 1` on its last
stage (`descentState_bound`): the exit condition of the sources at `t = m`, respectively `t = 2`.

The bound is a parameter of the descent (any `D` with `ord N(𝓘) ≤ D` on `W 0`, `BState.initialOf`):
the alignment of two descents (the compatibility of the values, their independence from the outer
open and the chain, the commutation with local isomorphisms) runs a third descent from the larger
of two bounds on the intersections of two chains, whose first links are empty.

The chain: since `r` depends on `D`, which is read on `U₀`, the opens are the iterated shrinkings
of the compact `closure U` inside `U₀` (`shrinkChain`, from Mathlib's
`exists_open_between_and_isCompact_closure`): `closure (W (k + 1)) ⊆ W k`, every `W k` relatively
compact and containing `closure U`, `closure (W 0) ⊆ U₀`. The descent is stated for any such chain
and any bound; the canonical ones are chosen in `StepAFamily.lean`.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

open Hironaka.Manifold.BMO

section Descent

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (m : ℕ)
  (hT : AnalyticTriple.BMOClass m T) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))

include hcomp in
/-- **The initial state at a bound `D`**: no blow-ups yet (`ChainState.init`), the invariant from
the pointwise bound `ord N(𝓘) ≤ D` on `W`, transported along the inclusion (`NonmonomialComap`,
`ord_pullback_of_isLocalDiffeomorphAt`). `BState.initial` is the case `D = roundOrderOn T U₀`. -/
def BState.initialOf {W : Opens M} (D : ℕ)
    (hD : ∀ x ∈ (W : Set M), (nonmonomialTriple T).I.ord x ≤ (D : ℕ∞)) :
    BState T m W D where
  toChainState := ChainState.init T m W
  bound := fun x => by
    have h : ∀ x' : M.restrict W, ((nonmonomialTriple T).pullback (M.inclusion W)
        (isLocalDiffeomorph_inclusion M W)).I.ord x' ≤ (D : ℕ∞) := fun x' => by
      change ((nonmonomialTriple T).I.pullback _ _).ord x' ≤ _
      rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
        (isLocalDiffeomorph_inclusion _ _ x')]
      exact hD x'.1 x'.2
    have e : nonmonomialTriple (ChainState.inducedTriple T m (ChainState.init T m W)) =
        (nonmonomialTriple T).pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W) :=
      (congrArg nonmonomialTriple (AnalyticTriple.induced_nil _ m _)).trans
        (hcomp T (M.inclusion W) (isLocalDiffeomorph_inclusion M W))
    rw [e]
    exact h x

/-- The initial state has no blow-ups. -/
theorem BState.initialOf_L {W : Opens M} (D : ℕ)
    (hD : ∀ x ∈ (W : Set M), (nonmonomialTriple T).I.ord x ≤ (D : ℕ∞)) :
    (BState.initialOf T m hcomp D hD).L = AnalyticManifold.BlowUpSequence.nil _ := rfl

variable (t : ℕ) (hm : 1 ≤ m) (hmt : m ≤ t)
  (W : ℕ → Opens M) (hW : ∀ k, IsCompact (closure (W k : Set M))) (r : ℕ)
  (hWsub : ∀ k, k < r → closure (W (k + 1) : Set M) ⊆ W k) (D : ℕ)
  (hD : ∀ x ∈ (W 0 : Set M), (nonmonomialTriple T).I.ord x ≤ (D : ℕ∞))

/-- **The descent**: `j` links from the initial state on `W 0` at the bound `D`, giving the state on
`W j` at the bound `D − j` (for `j ≤ r` and `j ≤ D + 1 − t`: every link so far ran at a bound
`d ≥ t`). -/
def descentStateAux : ∀ j : ℕ, j ≤ r → j ≤ D + 1 - t → BState T m (W j) (D - j)
  | 0, _, _ => BState.initialOf T m hcomp D hD
  | j + 1, hj, hjt =>
    (descentStateAux j (Nat.le_of_succ_le hj) (Nat.le_of_succ_le hjt)).descentLink hcomp bo hid
      (hW (j + 1)) (hWsub j hj) hT hm (by omega)

/-- The number of links of the descent: `D + 1 − t` (zero when `D < t`: nothing to do). -/
abbrev descentLength : ℕ := D + 1 - t

/-- **The final state of the descent**, after `D + 1 − t` links, on `W (D + 1 − t)`
([Kol07, 111, Step 1]; [Wlo09, Theorem 7.4.1], the modified algorithm). -/
def descentState (hr : descentLength t D ≤ r) :
    BState T m (W (descentLength t D)) (D - descentLength t D) :=
  descentStateAux T m hT bo hcomp hid t hm hmt W hW r hWsub D hD (descentLength t D) hr le_rfl

/-- The terminal bound: at the final state, `max-ord N(𝓘_ind) ≤ t − 1` everywhere on the last stage
("until we drop `max ord N(I)` to 1" at `t = 2`, [Wlo09, Theorem 7.4.1]; "until its order drops
below `m`" at `t = m`, [Kol07, 111, Step 1]). -/
theorem descentState_bound (hr : descentLength t D ≤ r) :
    NonmonomialOrdLe (ChainState.inducedTriple T m
      (descentState T m hT bo hcomp hid t hm hmt W hW r hWsub D hD hr).toChainState) (t - 1) :=
  (descentState T m hT bo hcomp hid t hm hmt W hW r hWsub D hD hr).bound.weaken
    (by unfold descentLength; omega)

end Descent

end Hironaka.Manifold.BMOmod

end
