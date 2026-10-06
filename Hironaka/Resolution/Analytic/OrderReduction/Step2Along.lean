/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Step22Fam
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Step 2 of Theorem 103 along an arbitrary chain of relatively compact opens

The value of Step 2 on a relatively compact open `U` (`step2SeqFamOn`, `Step22Fam.lean`) is
computed along one fixed chain of relatively compact opens, taken from the compact exhaustion of
the manifold (`chainOpens`, `Step21Fam.lean`). To show that the value does not depend on this
choice, this module defines Step 2 along an arbitrary admissible chain `W : ℕ → Opens M` of `r + 1`
links (`r` the number of nonempty boundary members): relatively compact opens, each containing the
closure of the next, the last containing `U`. The construction repeats that of `step2SeqFamOn`
with `W` in place of the exhaustion chain (`hfStep2FamChainAlong`; `hfStep22FamOnAlong`, the value
`hfStep22ValueOf` of Step 2.2 over a state of the chain read at the lifted range of the last
restriction; `hfStep2SeqFamAlong`), and `hfStep2SeqFamOn_eq_along` identifies the canonical value as
the value along the exhaustion chain, by definition.

The `hf…` declarations are the general forms over data `d : HFData ψ₀ s` of Step 2
(`HFamData.lean`); the plain forms are their instances at Lemma 102's data. The independence of
the chain, and with it the compatibility of Step 2 under restriction ([Wlo09, Theorem 2.0.3 (4)]),
is proved in `Step2Assembly.lean`.
-/

@[expose] public section

universe u

open Set Topology TopologicalSpace Hironaka.Local
open scoped Manifold ContDiff

namespace Hironaka.Manifold.BO

open _root_.Manifold

section ValueOf

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {s : ℕ}
  (bd : ∀ s : ℕ, BDanFamData ψ₀ s) (d : HFData ψ₀ s) {M : AnalyticManifold.{u} 𝕜 E}
  (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BOClass s T) {H : Set M}
  (hH : IsClosedSubmanifold ψ₀ H 1) (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1))

/-- The value of Step 2.2 over a state of the chain (over data `d`): the family functor of Step 2.2
at the triple of Step 2.2 over the state's sequence, for the triple restricted to the state's open
with the restricted hypersurface of maximal contact, read on the lifted range of the restriction
to `V`. -/
noncomputable def hfStep22ValueOf {W : Opens M} (st : ChainState T s W) {V : Opens M}
    (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W) :
    AnalyticManifold.BlowUpSequence ψ₀ ((st.L.stage (Fin.last _)).restrict
      (st.L.liftRange (M.restrictLE (ChainState.le_of_closure_subset hVW))
        (isLocalDiffeomorph_restrictLE _))) :=
  ((hfStep22Functor d.hf).fam
    (step22TripleOf (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)) st.L st.hge
      (isSnc_step22BoundaryOf _ s st.L (boClass_pullback_inclusion_of_boClass T W hT) st.hge
        (hH.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion M W))
        (idealSheaf_preimage_le_iteratedDeriv_inclusion T s hH hle W)))
    (stepHClass_step22TripleOf _ s st.L (boClass_pullback_inclusion_of_boClass T W hT) st.hge
      _)).seqOn
    (st.L.liftRange (M.restrictLE (ChainState.le_of_closure_subset hVW))
      (isLocalDiffeomorph_restrictLE _))
    (st.L.isCompact_closure_liftRange (M.restrictLE (ChainState.le_of_closure_subset hVW))
      (isLocalDiffeomorph_restrictLE _)
      (isCompact_closure_range_restrictLE (ChainState.le_of_closure_subset hVW) hV hVW))

end ValueOf

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (s : ℕ)
  (hT : AnalyticTriple.BOClass s T) (W : ℕ → Opens M)
  (hWsub : ∀ k, k < memberCount T s hT + 1 → closure (W (k + 1) : Set M) ⊆ W k)

include hWsub in
/-- The next-to-last open of an admissible chain of `r + 1` links contains the closure of the last
one. -/
theorem closure_chainLast_subset :
    closure (W (memberCount T s hT + 1) : Set M) ⊆ W (memberCount T s hT) :=
  hWsub _ (Nat.lt_succ_self _)

include hWsub in
/-- The last open of an admissible chain lies in the next-to-last one. -/
theorem chainLast_le : W (memberCount T s hT + 1) ≤ W (memberCount T s hT) :=
  fun _ hx => closure_chainLast_subset T s hT W hWsub (subset_closure hx)

variable [FiniteDimensional 𝕜 E] (bd : ∀ s : ℕ, BDanFamData ψ₀ s) (d : HFData ψ₀ s)
  (hW : ∀ k, IsCompact (closure (W k : Set M)))

/-- The chain of Step 2.1 along `W`, over data `d`: its state at the next-to-last open `W r`. -/
noncomputable def hfStep2FamChainAlong : ChainState T s (W (memberCount T s hT)) :=
  step21FamAux T s d.bd₁ hT W (memberCount T s hT + 1) hW hWsub (T.F.nonemptyList hT.2.2).reverse
    (Nat.le_succ _)

variable {H : Set M} (hH : IsClosedSubmanifold ψ₀ H 1)
  (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1))

/-- The value of Step 2.2 along `W` (over data `d`): the value over the chain's state at `W r`,
read at the lifted range of `W (r + 1) ⊆ W r` (`hfStep22ValueOf`). -/
noncomputable def hfStep22FamOnAlong :=
  hfStep22ValueOf d T hT hH hle (hfStep2FamChainAlong T s hT W hWsub d hW) (hW _)
    (closure_chainLast_subset T s hT W hWsub)

/-- The value of Step 2 on `U` along the admissible chain `W`, over data `d`: the chain of Step 2.1
along `W` with Step 2.2 appended at the last link, restricted to `U ⊆ W (r + 1)`, with its empty
blow-ups deleted. -/
noncomputable def hfStep2SeqFamAlong (U : Opens M) (hUW : U ≤ W (memberCount T s hT + 1)) :
    AnalyticManifold.BlowUpSequence ψ₀ (M.restrict U) :=
  (((hfStep2FamChainAlong T s hT W hWsub d hW).L.shrinkAppend
      (M.restrictLE (chainLast_le T s hT W hWsub)) (isLocalDiffeomorph_restrictLE _)
      (hfStep22FamOnAlong T s hT W hWsub d hW hH hle)).pullback
    (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE _)).eraseEmpty

/-- The value of Step 2 on `U` (`hfStep2SeqFamOn`) is Step 2 along the chain of exhaustion opens, by
definition. -/
theorem hfStep2SeqFamOn_eq_along (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    hfStep2SeqFamOn T s d hT U hU hH hle =
      hfStep2SeqFamAlong T s hT
        (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) (memberCount T s hT + 1))
        (fun _ hk => closure_chainOpens_succ_subset _ _ _ hk) d
        (isCompact_closure_chainOpens _ _ _) hH hle U (le_step2OpenV T s hT U hU) :=
  rfl

end Hironaka.Manifold.BO
