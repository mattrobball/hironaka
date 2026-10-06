/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.FamilyData
public import Hironaka.Resolution.Analytic.OrderReduction.FamilyChain
public import Hironaka.Resolution.Analytic.OrderReduction.Step21Defs
public import Hironaka.Manifold.Exhaustion
public import Hironaka.Resolution.Analytic.OrderReduction.Induced
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Resolution.Analytic.Functor.EraseEmptyOrder
import Hironaka.Resolution.Analytic.GoingUp.MaxOrder
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Step 2.1 of Theorem 103 as a compatible family

Step 2.1 of the proof of [Kol07, Theorem 103] applies Lemma 102 to the nonempty boundary members in
turn, each application on the triple induced at the end of the previous one. In the
compatible-family form the data of Lemma 102 are compatible families
(`BDanFamData ψ₀ s`, `FamilyData.lean`), whose values can only be read on relatively compact
opens; the value `step21FamOn bd T hT U hU` of Step 2.1 on a relatively compact open `U` is
therefore computed along a finite shrinking chain of the opens `M_{n₀+r} ⋑ ⋯ ⋑ M_{n₀} ⊇ closure U`
of a compact exhaustion of `M`, `r` the number of nonempty members: the `k`-th member's family is
read on the last stage of the sequence built so far, at the range of the lift of the inclusion
`M_{n₀+r-k-1} ⊆ M_{n₀+r-k}` (relatively compact by the properness of the blow-downs,
`FamilyChain.lean`), the sequence built so far is restricted to the smaller open and the value
appended (`shrinkAppend`); at the end the sequence is restricted to `U` and its empty blow-ups
deleted ([Kol07, 32]). The triple carried along the chain is the pull-back along the lifts of the
induced triples (`AnalyticTriple.induced`), a member of the class by `boClass_induced` and the
stability of the class under pull-back; it equals the induced triple of the restricted sequence
(`induced_pullback`), which the proofs of the clauses use.

Conventions. The compact exhaustion of `M` is chosen once (`exhaustion M`), and the value uses one
fixed chain; `step21FamOn_chain_indep` (`Step21FamIndep.lean`) shows that the value does not depend
on the chain up to empty blow-ups.

* `isCompact_closure_preimage_val_of_closure_subset`, `isCompact_closure_range_restrictLE` —
  relatively compact opens inside an open restriction;
* `exhaustion`, `exhaustionIdx`, `chainOpens` — the compact exhaustion, an index `n₀` with
  `closure U ⊆ M_{n₀}`, and the chain `W k := M_{n₀ + (r − k)}`;
* `ChainState T s W` — the state of the chain over `W`: the sequence built so far on `M.restrict W`
  with its order clause; `ChainState.init`; `ChainState.linkWith` (the generic link: a compatible
  family `C` on the induced triple at the last stage, with the order clause of its value on the
  reading open `readOpen`, restricts the sequence so far to the smaller open and appends the value,
  `shrinkAppend`, keeping the order clause); `ChainState.link` (one step of Step 2.1, at one
  member: `linkWith` at Lemma 102's family);
* `step21FamAux`, `memberCount`, `step21FamChain`, `step21FamOn` — the recursion over a list of
  members, the number of nonempty members, the chain over them, and the value on `U`;
* `step21FamOn_isOfOrderGe`, `step21FamOn_isOfOrder`, `step21FamOn_noEmptyCenters` — the value on
  `U` is a smooth blow-up sequence of order `≥ s`, indeed of order exactly `s`, starting with the
  triple restricted to `U`, without empty blow-ups.

The remaining clauses are proved in `Step21FamCosupp.lean` (the cosupport misses the transforms of
the members), `Step21FamIndep.lean` (independence of the chain, compatibility under restriction,
commutation with local analytic isomorphisms) and `Step21FamIndiff.lean` (indifference to empty
boundary members); the compatible family of Step 2.1 and Step 2.2 in this form are assembled in
`Step22Fam.lean`.
-/

@[expose] public section

universe u

open Set TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-! ### Relatively compact opens inside an open restriction -/

/-- For `closure V ⊆ W` with `closure V` compact, the preimage of `V` in `M.restrict W` has compact
closure: its closure lies in the preimage of `closure V`, which is compact as the preimage of a
compact subset of the open `W` under the inclusion. -/
theorem isCompact_closure_preimage_val_of_closure_subset {V W : Opens M}
    (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W) :
    IsCompact (closure (Subtype.val ⁻¹' (V : Set M) : Set (M.restrict W))) := by
  have hr : Set.range (Subtype.val : M.restrict W → M) = (W : Set M) := Subtype.range_coe
  have h1 : IsCompact (Subtype.val ⁻¹' (closure (V : Set M)) : Set (M.restrict W)) := by
    have hsub : closure (V : Set M) ⊆ Set.range (Subtype.val : M.restrict W → M) := by
      rw [hr]; exact hVW
    have heq : (Subtype.val : M.restrict W → M) '' (Subtype.val ⁻¹' closure (V : Set M)) =
        closure (V : Set M) := Set.image_preimage_eq_of_subset hsub
    exact Subtype.isCompact_iff.mpr ((congrArg IsCompact heq).mpr hV)
  exact h1.of_isClosed_subset isClosed_closure (continuous_subtype_val.closure_preimage_subset _)

/-- The open inclusion `M.restrict V → M.restrict W` of a relatively compact `V ⋐ W` has relatively
compact range. -/
theorem isCompact_closure_range_restrictLE {V W : Opens M} (hVW : V ≤ W)
    (hV : IsCompact (closure (V : Set M))) (hcl : closure (V : Set M) ⊆ W) :
    IsCompact (closure (Set.range (M.restrictLE hVW))) := by
  rw [range_restrictLE]
  exact isCompact_closure_preimage_val_of_closure_subset hV hcl

/-! ### The chain of exhaustion opens -/

/-- A compact exhaustion of `M`, fixed once and for all (a choice; `nonempty_compactExhaustion`). -/
noncomputable def exhaustion (M : AnalyticManifold.{u} 𝕜 E) [FiniteDimensional 𝕜 E] :
    CompactExhaustion M :=
  haveI : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  Classical.choice (nonempty_compactExhaustion (E := E) (M := M))

/-- An index `n₀` with `closure U ⊆ M_{n₀}` for a relatively compact open `U`. -/
noncomputable def exhaustionIdx (K : CompactExhaustion M) {U : Opens M}
    (hU : IsCompact (closure (U : Set M))) : ℕ :=
  Classical.choose (K.exists_superset_of_isCompact hU)

theorem closure_subset_relCompactOpen_exhaustionIdx (K : CompactExhaustion M) {U : Opens M}
    (hU : IsCompact (closure (U : Set M))) :
    closure (U : Set M) ⊆ relCompactOpen K (exhaustionIdx K hU) :=
  (Classical.choose_spec (K.exists_superset_of_isCompact hU)).trans (K.subset_interior_succ _)

/-- The shrinking chain `W k := M_{n₀ + (r − k)}`, `k = 0, …, r`: `W 0 = M_{n₀+r}` is the largest,
`W r = M_{n₀}` the smallest. -/
noncomputable def chainOpens (K : CompactExhaustion M) (n₀ r : ℕ) (k : ℕ) : Opens M :=
  relCompactOpen K (n₀ + (r - k))

theorem isCompact_closure_chainOpens (K : CompactExhaustion M) (n₀ r k : ℕ) :
    IsCompact (closure (chainOpens K n₀ r k : Set M)) :=
  isCompact_closure_relCompactOpen K _

theorem closure_chainOpens_succ_subset (K : CompactExhaustion M) (n₀ r : ℕ) {k : ℕ} (hk : k < r) :
    closure (chainOpens K n₀ r (k + 1) : Set M) ⊆ chainOpens K n₀ r k := by
  have h : n₀ + (r - k) = n₀ + (r - (k + 1)) + 1 := by omega
  unfold chainOpens
  rw [h]
  exact closure_relCompactOpen_subset_succ K _

theorem le_chainOpens_last (K : CompactExhaustion M) {U : Opens M}
    (hU : IsCompact (closure (U : Set M))) (r : ℕ) : U ≤ chainOpens K (exhaustionIdx K hU) r r := by
  intro x hx
  have h : exhaustionIdx K hU + (r - r) = exhaustionIdx K hU := by omega
  change x ∈ (relCompactOpen K (exhaustionIdx K hU + (r - r)) : Set M)
  rw [h]
  exact closure_subset_relCompactOpen_exhaustionIdx K hU (subset_closure hx)

/-! ### The chain state -/

variable (T : AnalyticTriple ψ₀ M) (s : ℕ)

/-- The state of the chain over the open `W`: the sequence of centres built so far on
`M.restrict W`, of order `≥ s` for the triple restricted to `W` (the invariant of the recursion). -/
structure ChainState (W : Opens M) where
  /-- The sequence built so far. -/
  L : BlowUpSequence ψ₀ (M.restrict W)
  /-- It is of order `≥ s` for the restricted triple. -/
  hge : L.toSuccession.IsOfOrderGe
    (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).I s
    (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).F.idealSheaf

/-- The initial state: the empty sequence on `M.restrict W`. -/
noncomputable def ChainState.init (W : Opens M) : ChainState T s W where
  L := BlowUpSequence.nil (M.restrict W)
  hge := FiniteSuccession.isOfOrderGe_nil _ _ s

namespace ChainState

open _root_.Manifold

variable {W V : Opens M} (st : ChainState T s W)

/-- The opens of a link: `V ≤ W`. -/
theorem le_of_closure_subset (hVW : closure (V : Set M) ⊆ W) : V ≤ W :=
  fun _ hx => hVW (subset_closure hx)

/-- The induced triple at the last stage of the sequence so far (from the state's order clause). -/
noncomputable abbrev inducedTriple : AnalyticTriple ψ₀ (st.L.stage (Fin.last _)) :=
  (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).induced s st.L st.hge

/-- The link's reading open: the range of the lift of the inclusion `V ⊆ W` at the last stage. -/
noncomputable abbrev readOpen (hVW : closure (V : Set M) ⊆ W) : Opens (st.L.stage (Fin.last _)) :=
  st.L.liftRange (M.restrictLE (le_of_closure_subset hVW)) (isLocalDiffeomorph_restrictLE _)

theorem isCompact_closure_readOpen (hV : IsCompact (closure (V : Set M)))
    (hVW : closure (V : Set M) ⊆ W) :
    IsCompact (closure (readOpen T s st hVW : Set (st.L.stage (Fin.last _)))) :=
  st.L.isCompact_closure_liftRange _ _
    (isCompact_closure_range_restrictLE (le_of_closure_subset hVW) hV hVW)

variable [FiniteDimensional 𝕜 E]

/-- **The generic link**: given a compatible family `C` on the induced triple at the last stage and
the order clause of its value on the reading open (for the induced triple restricted there),
restrict the sequence so far to `V` and append the value (`shrinkAppend`); the order clause for the
triple restricted to `V` is kept. -/
noncomputable def linkWith (hV : IsCompact (closure (V : Set M)))
    (hVW : closure (V : Set M) ⊆ W) (C : CompatibleFamily (inducedTriple T s st))
    (hC : (C.seqOn (readOpen T s st hVW)
        (isCompact_closure_readOpen T s st hV hVW)).toSuccession.IsOfOrderGe
      ((inducedTriple T s st).pullback ((st.L.stage (Fin.last _)).inclusion (readOpen T s st hVW))
        (isLocalDiffeomorph_inclusion _ _)).I s
      ((inducedTriple T s st).pullback ((st.L.stage (Fin.last _)).inclusion (readOpen T s st hVW))
        (isLocalDiffeomorph_inclusion _ _)).F.idealSheaf) :
    ChainState T s V where
  L := st.L.shrinkAppend (M.restrictLE (le_of_closure_subset hVW)) (isLocalDiffeomorph_restrictLE _)
    (C.seqOn (readOpen T s st hVW) (isCompact_closure_readOpen T s st hV hVW))
  hge := by
    have h := st.L.isOfOrderGe_shrinkAppend (M.restrictLE (le_of_closure_subset hVW))
      (isLocalDiffeomorph_restrictLE _)
      (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)) s st.hge _ hC
    rwa [AnalyticTriple.pullback_inclusion_restrictLE T (le_of_closure_subset hVW)] at h

end ChainState

variable [FiniteDimensional 𝕜 E]

/-- **One step of the chain**: the generic link `linkWith` at the member `j`'s family, read on the
induced triple at the last stage of the sequence built so far (`AnalyticTriple.induced`, in the
class by `boClass_induced`) at the member's index in the induced boundary (`originalIdx`), with its
order clause (`BDanFamData.isOfOrder`). -/
noncomputable def ChainState.link (bd : BDanFamData ψ₀ s) (hT : AnalyticTriple.BOClass s T)
    {W : Opens M} (st : ChainState T s W) (j : T.F.ι) {V : Opens M}
    (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W) : ChainState T s V :=
  st.linkWith T s hV hVW
    (bd.fam _ (AnalyticTriple.boClass_induced _ s st.L st.hge
        (boClass_pullback_inclusion_of_boClass T W hT))
      (st.L.toSuccession.originalIdx
        (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).F (Fin.last _) j))
    (bd.isOfOrder _ _ _ _ _).isOfOrderGe

/-- The chain over the members `l` (processed from the last), from the state at `W 0` down to the
state at `W l.length`. -/
noncomputable def step21FamAux (bd : BDanFamData ψ₀ s) (hT : AnalyticTriple.BOClass s T)
    (W : ℕ → Opens M) (r : ℕ) (hW : ∀ k, IsCompact (closure (W k : Set M)))
    (hWsub : ∀ k, k < r → closure (W (k + 1) : Set M) ⊆ W k) :
    ∀ (l : List T.F.ι), l.length ≤ r → ChainState T s (W l.length)
  | [], _ => ChainState.init T s (W 0)
  | j :: l, hl =>
    (step21FamAux bd hT W r hW hWsub l (Nat.le_of_succ_le hl)).link T s bd hT j (hW _)
      (hWsub l.length hl)

/-- The number of nonempty boundary members (the length of the chain). -/
noncomputable def memberCount (hT : AnalyticTriple.BOClass s T) : ℕ :=
  (T.F.nonemptyList hT.2.2).reverse.length

/-- **The chain of Step 2.1 on `U`**: over the nonempty members (in the order of the index set,
from the last) along the exhaustion opens `M_{n₀+r} ⋑ ⋯ ⋑ M_{n₀} ⊇ closure U`
(`chainOpens (exhaustion M) n₀ r`, `r` the number of nonempty members, `n₀ = exhaustionIdx`); its
state at the smallest open `M_{n₀}`. -/
noncomputable def step21FamChain (bd : BDanFamData ψ₀ s) (hT : AnalyticTriple.BOClass s T)
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    ChainState T s (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU)
      (memberCount T s hT) (memberCount T s hT)) :=
  step21FamAux T s bd hT (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU)
      (memberCount T s hT)) (memberCount T s hT)
    (isCompact_closure_chainOpens (exhaustion M) _ _)
    (fun _ hk => closure_chainOpens_succ_subset (exhaustion M) _ _ hk)
    (T.F.nonemptyList hT.2.2).reverse le_rfl

/-- **The value of Step 2.1 on `U`** (Step 2.1 of the proof of [Kol07, Theorem 103] per relatively
compact open): the chain's sequence at `M_{n₀}`, restricted to `U`, with the empty blow-ups deleted
([Kol07, 32]). -/
noncomputable def step21FamOn (bd : BDanFamData ψ₀ s) (hT : AnalyticTriple.BOClass s T)
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) : BlowUpSequence ψ₀ (M.restrict U) :=
  ((step21FamChain T s bd hT U hU).L.pullback
    (M.restrictLE (le_chainOpens_last (exhaustion M) hU (memberCount T s hT)))
    (isLocalDiffeomorph_restrictLE _)).eraseEmpty

variable (bd : BDanFamData ψ₀ s) (hT : AnalyticTriple.BOClass s T) (U : Opens M)
  (hU : IsCompact (closure (U : Set M)))

/-- The value of Step 2.1 on `U` is a smooth blow-up sequence of order `≥ s` starting with the
triple restricted to `U` (the chain's invariant, restricted along the last inclusion by
`isOfOrderGe_pullback`, kept under the deletion of empty blow-ups). -/
theorem step21FamOn_isOfOrderGe :
    (step21FamOn T s bd hT U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I s
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf := by
  have h := AnalyticTriple.isOfOrderGe_pullback _ s _ (step21FamChain T s bd hT U hU).hge
    (M.restrictLE (le_chainOpens_last (exhaustion M) hU (memberCount T s hT)))
    (isLocalDiffeomorph_restrictLE _)
  rw [AnalyticTriple.pullback_inclusion_restrictLE] at h
  exact BlowUpSequence.isOfOrderGe_eraseEmpty _ _ _
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc h

/-- The value of Step 2.1 on `U` is of order exactly `s`: on the class every centre of a sequence
of order `≥ s` has order exactly `s`, as [Kol07, Remark 67] notes
(`isOfOrder_of_isOfOrderGe_of_ord_le`). -/
theorem step21FamOn_isOfOrder :
    (step21FamOn T s bd hT U hU).toSuccession.IsOfOrder
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf s :=
  FiniteSuccession.isOfOrder_of_isOfOrderGe_of_ord_le _ (step21FamOn_isOfOrderGe T s bd hT U hU)
    (boClass_pullback_inclusion_of_boClass T U hT).2.1

/-- The value has no empty blow-ups ([Kol07, 32]). -/
theorem step21FamOn_noEmptyCenters : (step21FamOn T s bd hT U hU).NoEmptyCenters :=
  BlowUpSequence.noEmptyCenters_eraseEmpty _

end Hironaka.Manifold
