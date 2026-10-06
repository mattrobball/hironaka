/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepAChain
public import Hironaka.Resolution.Analytic.Wlo09.Rounds
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Resolution.Analytic.Functor.EraseEmptyOrder
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The rounds on the nonmonomial part: the value on a relatively compact open

**The value of the rounds on the nonmonomial part on a relatively compact open `U`**
([Kol07, 111, Step 1]; the first phase of the modified algorithm of [Wlo09, Theorem 7.4.1]), read
per open as every family of the library is [Wlo09, Theorem 2.0.3 (1)]: the canonical exhaustion of
the manifold (`exhaustion`, `exhaustionIdx`) gives an outer open `U₀ ⊇ closure U` on which the bound
`D = roundOrderOn T U₀` is read; the descent of `StepAChain.lean` runs its `D + 1 − t` links along
the canonical chain of iterated shrinkings of `closure U` inside `U₀` (`shrinkChain`); its final
state, on an open containing `closure U`, is restricted to `U` and its empty blow-ups are deleted
[Kol07, 32]. This is `stepAFamOn T m hT bo hcomp hid t hm hmt U hU`: a smooth blow-up sequence of
order `≥ m` for `(𝓘|U, m)` (`stepAFamOn_isOfOrderGe`) with no empty centre
(`stepAFamOn_noEmptyCenters`). The terminal bound `max-ord N(𝓘_ind) ≤ t − 1` is read on the chain
state before the deletion (`stepAChainState_bound`); the later steps of both algorithms continue
from that state.

The index of the exhaustion is a choice; the independence of the value from it, up to empty
blow-ups, is `stepAFamOn_eq_of_outer`, and the compatibility of the values is `stepAFamOn_compat`.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

open Hironaka.Manifold.BMO

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (m : ℕ)
  (hT : AnalyticTriple.BMOClass m T) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (t : ℕ) (hm : 1 ≤ m) (hmt : m ≤ t) (U : Opens M) (hU : IsCompact (closure (U : Set M)))

/-! ### The canonical opens -/

/-- The outer open `U₀` of the canonical exhaustion, containing `closure U`; the bound `D` is read
on it. -/
abbrev stepAOuter : Opens M := relCompactOpen (exhaustion M) (exhaustionIdx (exhaustion M) hU)

theorem isCompact_closure_stepAOuter : IsCompact (closure (stepAOuter U hU : Set M)) :=
  isCompact_closure_relCompactOpen _ _

theorem closure_subset_stepAOuter : closure (U : Set M) ⊆ stepAOuter U hU :=
  closure_subset_relCompactOpen_exhaustionIdx _ hU

/-- The bound `D = roundOrderOn T U₀`, the maximum of `ord N(𝓘)` on the closure of `U₀`. -/
abbrev stepABound : ℕ := roundOrderOn T (stepAOuter U hU)

/-- The number of links, `D + 1 − t`. -/
abbrev stepALinks : ℕ := stepABound T U hU + 1 - t

/-- The canonical chain: the iterated shrinkings of `closure U` inside `U₀` (`shrinkChain`). -/
abbrev stepAChainOpens (k : ℕ) : Opens M :=
  shrinkChain (closure (U : Set M)) (stepAOuter U hU) hU (closure_subset_stepAOuter U hU) k

theorem le_stepAChainOpens (k : ℕ) : U ≤ stepAChainOpens U hU k := fun _ hx =>
  subset_shrinkChain hU (closure_subset_stepAOuter U hU) k (subset_closure hx)

/-- The bound `stepABound T U hU` holds on the first open of the canonical chain of `U`: the bound
hypothesis of the descent along it. -/
theorem stepABound_bound (x : M) (hx : x ∈ (stepAChainOpens U hU 0 : Set M)) :
    (nonmonomialTriple T).I.ord x ≤ (stepABound T U hU : ℕ∞) := by
  rw [nonmonomialTriple_I]
  exact ord_le_roundOrderOn T (stepAOuter U hU) (isCompact_closure_stepAOuter U hU)
    (closure_shrinkChain_zero_subset hU (closure_subset_stepAOuter U hU) (subset_closure hx))

/-! ### The chain state and the value -/

/-- **The final chain state over the inner open of `U`**: the `D + 1 − t` links of the descent along
the canonical chain. -/
def stepAChainState :
    BState T m (stepAChainOpens U hU (stepALinks T t U hU))
      (stepABound T U hU - stepALinks T t U hU) :=
  descentState T m hT bo hcomp hid t hm hmt (stepAChainOpens U hU)
    (fun k => isCompact_closure_shrinkChain hU (closure_subset_stepAOuter U hU) k)
    (stepALinks T t U hU)
    (fun k _ => closure_shrinkChain_succ_subset hU (closure_subset_stepAOuter U hU) k)
    (stepABound T U hU) (stepABound_bound T U hU) le_rfl

/-- The terminal bound of the chain state: `max-ord N(𝓘_ind) ≤ t − 1` on its last stage (the exit
condition of the rounds; the input of the later steps). -/
theorem stepAChainState_bound :
    NonmonomialOrdLe (ChainState.inducedTriple T m
      (stepAChainState T m hT bo hcomp hid t hm hmt U hU).toChainState) (t - 1) :=
  descentState_bound T m hT bo hcomp hid t hm hmt _ _ _ _ _ _ le_rfl

/-- **The value of the rounds on the nonmonomial part on `U`** ([Kol07, 111, Step 1];
[Wlo09, Theorem 7.4.1]): the list of the final chain state restricted to `U`, its empty blow-ups
deleted [Kol07, 32]. -/
def stepAFamOn : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    (M.restrict U) :=
  ((stepAChainState T m hT bo hcomp hid t hm hmt U hU).L.pullback
    (M.restrictLE (le_stepAChainOpens U hU _)) (isLocalDiffeomorph_restrictLE _)).eraseEmpty

/-- The value has no empty blow-ups [Kol07, 32]. -/
theorem stepAFamOn_noEmptyCenters : (stepAFamOn T m hT bo hcomp hid t hm hmt U hU).NoEmptyCenters :=
  AnalyticManifold.BlowUpSequence.noEmptyCenters_eraseEmpty _

/-- The value is a smooth blow-up sequence of order `≥ m` starting with `(𝓘|U, m, E|U)`: the
invariant of the chain restricted along the last inclusion, kept by the deletion of empty
blow-ups. -/
theorem stepAFamOn_isOfOrderGe :
    (stepAFamOn T m hT bo hcomp hid t hm hmt U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I m
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf := by
  have h := AnalyticTriple.isOfOrderGe_pullback _ m _
    (stepAChainState T m hT bo hcomp hid t hm hmt U hU).hge
    (M.restrictLE (le_stepAChainOpens U hU _)) (isLocalDiffeomorph_restrictLE _)
  rw [AnalyticTriple.pullback_inclusion_restrictLE] at h
  exact AnalyticManifold.BlowUpSequence.isOfOrderGe_eraseEmpty _ _ _
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc h

end Hironaka.Manifold.BMOmod

end
