/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.FamilyChain
public import Hironaka.Resolution.Analytic.OrderReduction.Induced
public import Hironaka.Resolution.Analytic.Functor.Family
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
public import Hironaka.Manifold.IdealSheaf.CosupportDeriv
import Hironaka.Manifold.IdealSheaf.Pullback
public import Hironaka.Resolution.Analytic.OrderReduction.Finiteness
import Hironaka.Resolution.Analytic.OrderReduction.Step21Fam
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Compactness.Paracompact

/-!
# The rounds of order reduction along a shrinking chain: the resolution family

Hironaka's Main Theorem II(N) [Hir64, p. 176] iterates order reduction with the maximal order
`d = max ord` decreasing: run the order reduction of `(𝓘, d)` at the maximal order `d`, then again
on the weak transform (whose order is `< d`), down to `d = 1`. Here each round is the value of the
order-reduction family `BO_{n,d}` of [Kol07, Theorem 68] (`BOanFam 𝕜 n d`, the binder `bo d`) on the
current derived triple, a `CompatibleFamily` whose sequences exist only on relatively compact opens;
so the rounds are read along a shrinking chain of relatively compact opens: round `d + 1` is read at
`Ω d`, the derived triple is the induced triple at mark `d + 1` (`AnalyticTriple.induced`, in the
class of `BO_{n,d}` by the round's `ord_lt`), the chain is lifted to the round's last stage as the
preimages under the proper composite blow-down, and the rounds from `d` are concatenated after the
round's list pulled back to the open whose value is wanted. The recursion is one recursion on `d`
over the current manifold (`resolveFrom`): the concatenation's second factor lives on the first
factor's last stage by construction, so no stage transport is needed. The value on a relatively
compact open `U` (`resolveSeqOn`) is the recursion along the canonical chain, `d_U + 1` iterated
shrinks of `closure U` inside the open `{ord 𝓘 ≤ d_U}` (upper semicontinuity of the order,
`isOpen_setOf_ord_le`; `d_U` the least bound of `ord 𝓘` on `closure U`, `bddAbove_ord_on_compact`),
so that the triple restricted to the outermost open lies in the class of `BO_{n,d_U}` when `d_U ≥ 1`
(`boClass_pullback_inclusion`), with the empty blow-ups erased (the empty blow-up convention
[Kol07, 32]). The opens of a fixed exhaustion alone would make the round count circular (the bound
on the outermost open depends on the open chosen); the rounds above the order bound of an open are
empty on it (the remark after [Kol07, Theorem 68]), which enters canonicity
(`Hironaka/Resolution/Analytic/Wlo09/Canonicity.lean`), not the definition. The value along an
arbitrary admissible chain (`ResolveChain`, `resolveSeqOnAlong`) is what canonicity compares.

This is Włodarczyk's locally finite principalization [Wlo09, Theorem 2.0.3 (1)], with the
neighbourhoods `U` of the compact sets read as relatively compact opens, and the reduction of the
maximal order of [Wlo09, §6, Step 2a]; Bierstone and Milman treat the non-compact case by relatively
compact opens (the remark after [BM97, Theorem 1.6]).
`Hironaka/Resolution/Analytic/Wlo09/Canonicity.lean` proves that the value does not depend on the
chain and bundles the values into `resolveFam`.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

/-! ### Shrinking a compact inside an open (the chain's opens) -/

section Shrink

variable {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-- A manifold modelled on `𝕜ⁿ` is locally compact. -/
theorem locallyCompactSpace_std (M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)) :
    LocallyCompactSpace M :=
  haveI : ProperSpace (Fin n → 𝕜) := FiniteDimensional.proper_rclike 𝕜 _
  ChartedSpace.locallyCompactSpace (Fin n → 𝕜) M

/-- Between a compact `K` and an open `V ⊇ K` there is a relatively compact open `W` with `K ⊆ W`
and `closure W ⊆ V` (Mathlib's `exists_open_between_and_isCompact_closure`, the manifold being
locally compact and Hausdorff, hence regular). -/
theorem exists_shrinkBetween {K : Set M} {V : Opens M} (hK : IsCompact K) (hKV : K ⊆ V) :
    ∃ W : Opens M, K ⊆ W ∧ closure (W : Set M) ⊆ V ∧ IsCompact (closure (W : Set M)) := by
  have : LocallyCompactSpace M := locallyCompactSpace_std M
  obtain ⟨W, hWo, hKW, hWV, hWc⟩ := exists_open_between_and_isCompact_closure hK V.isOpen hKV
  exact ⟨⟨W, hWo⟩, hKW, hWV, hWc⟩

/-- A chosen open between a compact and an open containing it (`Classical.choose` of
`exists_shrinkBetween`). -/
def shrinkBetween (K : Set M) (V : Opens M) (hK : IsCompact K) (hKV : K ⊆ V) : Opens M :=
  Classical.choose (exists_shrinkBetween hK hKV)

theorem subset_shrinkBetween {K : Set M} {V : Opens M} (hK : IsCompact K) (hKV : K ⊆ V) :
    K ⊆ shrinkBetween K V hK hKV :=
  (Classical.choose_spec (exists_shrinkBetween hK hKV)).1

theorem closure_shrinkBetween_subset {K : Set M} {V : Opens M} (hK : IsCompact K) (hKV : K ⊆ V) :
    closure (shrinkBetween K V hK hKV : Set M) ⊆ V :=
  (Classical.choose_spec (exists_shrinkBetween hK hKV)).2.1

theorem isCompact_closure_shrinkBetween {K : Set M} {V : Opens M} (hK : IsCompact K)
    (hKV : K ⊆ V) : IsCompact (closure (shrinkBetween K V hK hKV : Set M)) :=
  (Classical.choose_spec (exists_shrinkBetween hK hKV)).2.2

/-- The iterated shrinks of `K` inside `V`, each carrying `K ⊆ W`. -/
def shrinkChainAux (K : Set M) (V : Opens M) (hK : IsCompact K) (hKV : K ⊆ V) :
    ℕ → {W : Opens M // K ⊆ W}
  | 0 => ⟨shrinkBetween K V hK hKV, subset_shrinkBetween hK hKV⟩
  | j + 1 => ⟨shrinkBetween K (shrinkChainAux K V hK hKV j).1 hK (shrinkChainAux K V hK hKV j).2,
      subset_shrinkBetween hK (shrinkChainAux K V hK hKV j).2⟩

/-- **The iterated shrinks** of a compact `K` inside an open `V`: `shrinkChain K V hK hKV 0 ⋐ V`,
`shrinkChain K V hK hKV (j + 1) ⋐ shrinkChain K V hK hKV j`, every one relatively compact and
containing `K`. The canonical chain of the resolution family is made of them. -/
def shrinkChain (K : Set M) (V : Opens M) (hK : IsCompact K) (hKV : K ⊆ V) (j : ℕ) : Opens M :=
  (shrinkChainAux K V hK hKV j).1

theorem subset_shrinkChain {K : Set M} {V : Opens M} (hK : IsCompact K) (hKV : K ⊆ V) (j : ℕ) :
    K ⊆ shrinkChain K V hK hKV j :=
  (shrinkChainAux K V hK hKV j).2

theorem shrinkChain_zero {K : Set M} {V : Opens M} (hK : IsCompact K) (hKV : K ⊆ V) :
    shrinkChain K V hK hKV 0 = shrinkBetween K V hK hKV := rfl

theorem shrinkChain_succ {K : Set M} {V : Opens M} (hK : IsCompact K) (hKV : K ⊆ V) (j : ℕ) :
    shrinkChain K V hK hKV (j + 1) =
      shrinkBetween K (shrinkChain K V hK hKV j) hK (subset_shrinkChain hK hKV j) := rfl

theorem closure_shrinkChain_zero_subset {K : Set M} {V : Opens M} (hK : IsCompact K)
    (hKV : K ⊆ V) : closure (shrinkChain K V hK hKV 0 : Set M) ⊆ V :=
  closure_shrinkBetween_subset hK hKV

theorem closure_shrinkChain_succ_subset {K : Set M} {V : Opens M} (hK : IsCompact K) (hKV : K ⊆ V)
    (j : ℕ) : closure (shrinkChain K V hK hKV (j + 1) : Set M) ⊆ shrinkChain K V hK hKV j := by
  rw [shrinkChain_succ]
  exact closure_shrinkBetween_subset hK (subset_shrinkChain hK hKV j)

theorem isCompact_closure_shrinkChain {K : Set M} {V : Opens M} (hK : IsCompact K) (hKV : K ⊆ V)
    (j : ℕ) : IsCompact (closure (shrinkChain K V hK hKV j : Set M)) := by
  cases j with
  | zero => exact isCompact_closure_shrinkBetween hK hKV
  | succ j =>
    rw [shrinkChain_succ]
    exact isCompact_closure_shrinkBetween hK (subset_shrinkChain hK hKV j)

theorem shrinkChain_succ_le {K : Set M} {V : Opens M} (hK : IsCompact K) (hKV : K ⊆ V) (j : ℕ) :
    shrinkChain K V hK hKV (j + 1) ≤ shrinkChain K V hK hKV j :=
  fun _ hx => closure_shrinkChain_succ_subset hK hKV j (subset_closure hx)

theorem shrinkChain_antitone {K : Set M} {V : Opens M} (hK : IsCompact K) (hKV : K ⊆ V) :
    Antitone (shrinkChain K V hK hKV) :=
  antitone_nat_of_succ_le (shrinkChain_succ_le hK hKV)

theorem closure_shrinkChain_subset_of_lt {K : Set M} {V : Opens M} (hK : IsCompact K) (hKV : K ⊆ V)
    {i j : ℕ} (h : i < j) :
    closure (shrinkChain K V hK hKV j : Set M) ⊆ shrinkChain K V hK hKV i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  exact (closure_shrinkChain_succ_subset hK hKV (i + k)).trans
    (shrinkChain_antitone hK hKV (Nat.le_add_right i k))

end Shrink

/-! ### The least order bound on a compact closure, and the open where it holds -/

section OrderBound

variable {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

open Classical in
/-- **`d_U`**, the least bound of `ord 𝓘` on the compact `closure U` (`bddAbove_ord_on_compact`):
the maximal order of `𝓘` on `closure U` when `U` is nonempty, `0` when `U` is empty. Hironaka's
`d_i`, the maximal integer attained by the order [Hir64, Main Theorem II(N), p. 176]. -/
def maxOrdOn (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) : ℕ :=
  Nat.find (IdealSheaf.bddAbove_ord_on_compact T.isNonzeroEverywhere hU)

open Classical in
theorem ord_le_maxOrdOn (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    ∀ x ∈ closure (U : Set M), T.I.ord x ≤ (maxOrdOn T U hU : ℕ∞) :=
  Nat.find_spec (IdealSheaf.bddAbove_ord_on_compact T.isNonzeroEverywhere hU)

/-- The open `{ord 𝓘 ≤ D}` (upper semicontinuity of the order, `isOpen_setOf_ord_le`), on which the
rounds from `D` may start. -/
def orderOpen (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (D : ℕ) :
    Opens M :=
  ⟨{x | T.I.ord x ≤ (D : ℕ∞)}, T.I.isOpen_setOf_ord_le D⟩

theorem closure_subset_orderOpen (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    closure (U : Set M) ⊆ orderOpen T (maxOrdOn T U hU) :=
  fun x hx => ord_le_maxOrdOn T U hU x hx

end OrderBound

/-! ### Chains of opens -/

section Chain

variable {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-- A chain with `closure (Ω k) ⊆ Ω (k + 1)` below `D` is monotone below `D`. -/
theorem chain_le_of_le {Ω : ℕ → Opens X} {D : ℕ}
    (hΩsub : ∀ k, k + 1 < D → closure (Ω k : Set X) ⊆ Ω (k + 1)) {k j : ℕ} (hkj : k ≤ j)
    (hj : j < D) : Ω k ≤ Ω j := by
  induction j, hkj using Nat.le_induction with
  | base => exact le_rfl
  | succ j hkj ih =>
    exact (ih (Nat.lt_of_succ_lt hj)).trans (fun _ hx => hΩsub j hj (subset_closure hx))

theorem chain_closure_subset_of_lt {Ω : ℕ → Opens X} {D : ℕ}
    (hΩsub : ∀ k, k + 1 < D → closure (Ω k : Set X) ⊆ Ω (k + 1)) {k j : ℕ} (hkj : k < j)
    (hj : j < D) : closure (Ω k : Set X) ⊆ Ω j :=
  (hΩsub k (lt_of_le_of_lt hkj hj)).trans (chain_le_of_le hΩsub hkj hj)

/-- The trace of an open `V` of `X` on the open submanifold `X.restrict O`. -/
def traceOn (O V : Opens X) : Opens (X.restrict O) :=
  ⟨Subtype.val ⁻¹' (V : Set X), V.isOpen.preimage continuous_subtype_val⟩

end Chain

/-! ### One round: the list, the derived triple -/

section Round

variable (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d) {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-- A triple of order `≤ d + 1` everywhere with finitely many nonempty boundary members lies in the
class of `BO_{n,d+1}` (the hypothesis `max-ord I ≤ m` of [Kol07, Theorem 68]). -/
theorem boClass_succ_of_ord_le {d : ℕ}
    (cur : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    (hord : ∀ x, cur.I.ord x ≤ ((d + 1 : ℕ) : ℕ∞)) (hfin : Finite {j // cur.F.hyp j ≠ ∅}) :
    AnalyticTriple.BOClass (d + 1) cur :=
  ⟨Nat.succ_le_succ (Nat.zero_le d), hord, hfin⟩

/-- **The round's list**: the value of the family `BO_{n,d+1}` on the current triple `cur` at the
reading open `O` (one round of [Hir64, Main Theorem II(N), p. 176]; [Kol07, Theorem 68]). -/
def roundList {d : ℕ} (cur : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    (hcls : AnalyticTriple.BOClass (d + 1) cur) (O : Opens X)
    (hO : IsCompact (closure (O : Set X))) :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (X.restrict O) :=
  ((bo (d + 1)).functor.fam cur hcls).seqOn O hO

/-- **The derived triple** at the last stage of the round: the induced triple at mark `d + 1`
(`AnalyticTriple.induced`), whose ideal is Hironaka's weak transform `J_{i+1}` of `J_i`
[Hir64, Main Theorem II(N), p. 176], Kollár's marked transform at the current mark
(`Hironaka/Resolution/Analytic/Wlo09/HironakaClauses.lean`). -/
def derivedTriple {d : ℕ} (cur : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    (hcls : AnalyticTriple.BOClass (d + 1) cur) (O : Opens X)
    (hO : IsCompact (closure (O : Set X))) :
    AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      ((roundList bo cur hcls O hO).stage (Fin.last _)) :=
  (cur.pullback (X.inclusion O) (isLocalDiffeomorph_inclusion X O)).induced (d + 1)
    (roundList bo cur hcls O hO) ((bo (d + 1)).isOfOrderGe cur hcls O hO)

/-- The derived triple has order `≤ d` everywhere (clause (1) of [Kol07, Theorem 68],
`max-ord I_r < m`, the round's `ord_lt`): the next round applies to it on its whole manifold. -/
theorem derivedTriple_ord_le {d : ℕ}
    (cur : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    (hcls : AnalyticTriple.BOClass (d + 1) cur) (O : Opens X) (hO : IsCompact (closure (O : Set X)))
    (x : (roundList bo cur hcls O hO).stage (Fin.last _)) :
    (derivedTriple bo cur hcls O hO).I.ord x ≤ (d : ℕ∞) := by
  have h := (bo (d + 1)).ord_lt cur hcls O hO x
  rw [Nat.cast_succ] at h
  exact (ENat.lt_add_one_iff (ENat.natCast_ne_top d)).mp h

/-- The derived triple has finitely many nonempty boundary members
(`finite_nonempty_totalTransformSeqFrom`). -/
theorem derivedTriple_finite {d : ℕ}
    (cur : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    (hcls : AnalyticTriple.BOClass (d + 1) cur) (O : Opens X)
    (hO : IsCompact (closure (O : Set X))) :
    Finite {j // (derivedTriple bo cur hcls O hO).F.hyp j ≠ ∅} :=
  finite_nonempty_totalTransformSeqFrom _ _ (finite_nonempty_pullback_inclusion cur O hcls.2.2) _

end Round

/-! ### The chain lifted to a round's last stage -/

section Lift

variable {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} {O : Opens X}
  (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (X.restrict O))

/-- **The lift of an open** `V` of `X` to the last stage of a list on `X.restrict O`: its preimage
under the composite blow-down (Włodarczyk's `Ũ = prin⁻¹(U)`, [Wlo09, Theorem 2.0.3 (1)]). -/
def liftOpens (V : Opens X) : Opens (L.stage (Fin.last _)) :=
  ⟨L.toSuccession.stageMap (Fin.last _) ⁻¹' (Subtype.val ⁻¹' (V : Set X)),
    (V.isOpen.preimage continuous_subtype_val).preimage
      (L.toSuccession.stageMap (Fin.last _)).contMDiff.continuous⟩

/-- The lift of `V` as a set: the preimage of `V` under the composite blow-down. -/
theorem coe_liftOpens (V : Opens X) :
    (liftOpens L V : Set (L.stage (Fin.last _))) =
      L.toSuccession.stageMap (Fin.last _) ⁻¹' (Subtype.val ⁻¹' (V : Set X)) := rfl

/-- The lift of a relatively compact open with closure inside `O` is relatively compact (the
composite blow-down is proper, `isProperMap_stageMap`). -/
theorem isCompact_closure_liftOpens {V : Opens X} (hV : IsCompact (closure (V : Set X)))
    (hVO : closure (V : Set X) ⊆ O) :
    IsCompact (closure (liftOpens L V : Set (L.stage (Fin.last _)))) := by
  have h1 := isCompact_closure_preimage_val_of_closure_subset hV hVO
  have hprop := L.toSuccession.isProperMap_stageMap (Fin.last _)
  rw [coe_liftOpens]
  exact (hprop.isCompact_preimage h1).of_isClosed_subset isClosed_closure
    (hprop.continuous.closure_preimage_subset _)

/-- The lift preserves shrinking with closures. -/
theorem closure_liftOpens_subset {V W : Opens X} (hVW : closure (V : Set X) ⊆ W) :
    closure (liftOpens L V : Set (L.stage (Fin.last _))) ⊆ liftOpens L W := by
  rw [coe_liftOpens, coe_liftOpens]
  refine ((L.toSuccession.stageMap (Fin.last _)).contMDiff.continuous.closure_preimage_subset
    _).trans (Set.preimage_mono ?_)
  exact (continuous_subtype_val.closure_preimage_subset _).trans (Set.preimage_mono hVW)

/-- The last-stage lift of a map into `V ⊆ O` lands in the lift of `V`
(`range_pullbackLiftLast_subset`). -/
theorem range_pullbackLiftLast_subset_liftOpens {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (ι : AnalyticMap N X) (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι)
    (V : Opens X) (hV : Set.range ι ⊆ V) (h : Set.range ι ⊆ O) :
    Set.range (L.pullbackLiftLast (AnalyticMap.corestrict ι O h)
      (isLocalDiffeomorph_corestrict ι O hι h)) ⊆ liftOpens L V := by
  rw [coe_liftOpens]
  refine (L.range_pullbackLiftLast_subset _ _).trans (Set.preimage_mono ?_)
  rintro _ ⟨y, rfl⟩
  exact hV ⟨y, rfl⟩

/-- **The chain lifted** to the last stage of `L`. -/
def liftChain (Ω : ℕ → Opens X) (k : ℕ) : Opens (L.stage (Fin.last _)) := liftOpens L (Ω k)

theorem liftChain_isCompact {Ω : ℕ → Opens X} {d : ℕ}
    (hΩ : ∀ k, k < d + 1 → IsCompact (closure (Ω k : Set X)))
    (hΩsub : ∀ k, k + 1 < d + 1 → closure (Ω k : Set X) ⊆ Ω (k + 1)) (hO : O = Ω d) :
    ∀ k, k < d → IsCompact (closure (liftChain L Ω k : Set (L.stage (Fin.last _)))) := by
  intro k hk
  subst hO
  exact isCompact_closure_liftOpens L (hΩ k (Nat.lt_succ_of_lt hk))
    (chain_closure_subset_of_lt hΩsub hk (Nat.lt_succ_self d))

theorem liftChain_closure_subset {Ω : ℕ → Opens X} {d : ℕ}
    (hΩsub : ∀ k, k + 1 < d + 1 → closure (Ω k : Set X) ⊆ Ω (k + 1)) :
    ∀ k, k + 1 < d →
      closure (liftChain L Ω k : Set (L.stage (Fin.last _))) ⊆ liftChain L Ω (k + 1) :=
  fun k hk => closure_liftOpens_subset L (hΩsub k (Nat.lt_succ_of_lt hk))

end Lift

/-! ### The rounds `d ↓` along a chain, as one recursion over the current manifold -/

section Rounds

variable (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)

/-- The range of the reading map lies in every open of the chain below `d + 1`. -/
theorem range_subset_chain {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} {Ω : ℕ → Opens X} {d : ℕ}
    (hΩsub : ∀ k, k + 1 < d + 1 → closure (Ω k : Set X) ⊆ Ω (k + 1))
    {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} {ι : AnalyticMap N X} (hrange : Set.range ι ⊆ Ω 0) :
    Set.range ι ⊆ Ω d :=
  hrange.trans (chain_le_of_le hΩsub (Nat.zero_le d) (Nat.lt_succ_self d))

/-- **The rounds `d, d − 1, …, 1`** of the families `bo` on the current derived triple `cur` (of
order `≤ d` everywhere, with finitely many nonempty boundary members) along the chain `Ω` of
relatively compact opens of the current manifold (`closure (Ω k) ⊆ Ω (k + 1)` below `d`), read on
the manifold `N` of a local analytic isomorphism `ι` into `Ω 0`: the iteration of [Hir64, Main
Theorem II(N), p. 176] at decreasing maximal order, [Wlo09, Theorem 2.0.3 (1)]. Round `d + 1` is the
family's value at `Ω d`; the derived triple is the induced triple at mark `d + 1` on the round's
last stage; the chain and `ι` are lifted to that stage; the value is the round's list pulled back
along `ι` followed by the rounds from `d`, pulled back along the last-stage lift of `ι`; the second
factor lives on the first factor's last stage by construction. -/
def resolveFrom :
    ∀ (d : ℕ) {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
      (cur : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
      (_hord : ∀ x, cur.I.ord x ≤ (d : ℕ∞)) (_hfin : Finite {j // cur.F.hyp j ≠ ∅})
      (Ω : ℕ → Opens X) (_hΩ : ∀ k, k < d → IsCompact (closure (Ω k : Set X)))
      (_hΩsub : ∀ k, k + 1 < d → closure (Ω k : Set X) ⊆ Ω (k + 1))
      {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (ι : AnalyticMap N X)
      (_hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι)
      (_hrange : Set.range ι ⊆ Ω 0), AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜
          (Fin n → 𝕜)) N
  | 0, _, _, _, _, _, _, _, N, _, _, _ => AnalyticManifold.BlowUpSequence.nil N
  | d + 1, _, cur, hord, hfin, Ω, hΩ, hΩsub, _, ι, hι, hrange =>
    ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d))).pullback
        (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
        (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange))).concat
      (resolveFrom d
        (derivedTriple bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
          (hΩ d (Nat.lt_succ_self d)))
        (derivedTriple_ord_le bo cur _ (Ω d) _) (derivedTriple_finite bo cur _ (Ω d) _)
        (liftChain (roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
          (hΩ d (Nat.lt_succ_self d))) Ω)
        (liftChain_isCompact _ hΩ hΩsub rfl) (liftChain_closure_subset _ hΩsub)
        ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
          (hΩ d (Nat.lt_succ_self d))).pullbackLiftLast
          (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
          (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange)))
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)
        (range_pullbackLiftLast_subset_liftOpens _ ι hι (Ω 0) hrange
          (range_subset_chain hΩsub hrange)))

end Rounds

/-! ### Admissible chains and the value along one; the canonical chain; the value on an open -/

section Top

variable {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-- **An admissible shrinking chain** for `(T, U)`: `D` rounds, opens `W 0 ⊆ ⋯ ⊆ W D` with compact
closures, `closure (W k) ⊆ W (k + 1)`, `U ≤ W 0`, and `ord 𝓘 ≤ D` on the outermost open (so the
triple restricted to it lies in the class of `BO_{n,D}` when `D ≥ 1`). Włodarczyk's open
neighbourhood `U ⊃ Z` of [Wlo09, Theorem 2.0.3 (1)], read `D` times. -/
structure ResolveChain (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (U : Opens M) where
  /-- The number of rounds. -/
  D : ℕ
  /-- The opens, `W 0` the innermost, `W D` the outermost. -/
  W : ℕ → Opens M
  /-- Compact closures. -/
  isCompact_closure : ∀ k, k ≤ D → IsCompact (closure (W k : Set M))
  /-- Shrinking with closures. -/
  closure_subset : ∀ k, k < D → closure (W k : Set M) ⊆ W (k + 1)
  /-- `U` lies in the innermost open. -/
  le_zero : U ≤ W 0
  /-- The order bound on the outermost open. -/
  ord_le : ∀ x ∈ W D, T.I.ord x ≤ (D : ℕ∞)

variable (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (U : Opens M)

namespace ResolveChain

open _root_.Manifold

variable {T U} (c : ResolveChain T U)

theorem le_of_le {k j : ℕ} (hkj : k ≤ j) (hj : j ≤ c.D) : c.W k ≤ c.W j := by
  induction j, hkj using Nat.le_induction with
  | base => exact le_rfl
  | succ j hkj ih =>
    exact (ih (Nat.le_of_succ_le hj)).trans (fun _ hx => c.closure_subset j hj (subset_closure hx))

theorem le_outer (k : ℕ) (hk : k ≤ c.D) : c.W k ≤ c.W c.D := c.le_of_le hk le_rfl

theorem closure_subset_of_lt {k j : ℕ} (hkj : k < j) (hj : j ≤ c.D) :
    closure (c.W k : Set M) ⊆ c.W j :=
  (c.closure_subset k (lt_of_lt_of_le hkj hj)).trans (c.le_of_le hkj hj)

/-- The triple restricted to the outermost open. -/
def outerTriple :
    AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (M.restrict (c.W c.D)) :=
  T.pullback (M.inclusion (c.W c.D)) (isLocalDiffeomorph_inclusion M _)

/-- The order bound restricts to the outermost open. -/
theorem outerTriple_ord_le (x : M.restrict (c.W c.D)) :
    (c.outerTriple.I).ord x ≤ (c.D : ℕ∞) := by
  change (T.I.pullback ⇑(M.inclusion (c.W c.D)) (M.inclusion (c.W c.D)).contMDiff).ord x ≤ _
  rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ T.I
    (isLocalDiffeomorph_inclusion M (c.W c.D) x)]
  exact c.ord_le _ x.2

/-- Finitely many boundary members meet the relatively compact outermost open
(`boClass_pullback_inclusion`). -/
theorem outerTriple_finite : Finite {j // (c.outerTriple).F.hyp j ≠ ∅} :=
  (boClass_pullback_inclusion T (Nat.succ_pos c.D) _ (c.isCompact_closure c.D le_rfl)
    (fun _ hx => (c.ord_le _ hx).trans (by exact_mod_cast Nat.le_succ _))).2.2

/-- The chain as opens of the outermost open. -/
def trace (k : ℕ) : Opens (M.restrict (c.W c.D)) := traceOn (c.W c.D) (c.W k)

theorem isCompact_closure_trace (k : ℕ) (hk : k < c.D) :
    IsCompact (closure (c.trace k : Set (M.restrict (c.W c.D)))) :=
  isCompact_closure_preimage_val_of_closure_subset (c.isCompact_closure k hk.le)
    (c.closure_subset_of_lt hk le_rfl)

theorem closure_trace_subset (k : ℕ) (hk : k + 1 < c.D) :
    closure (c.trace k : Set (M.restrict (c.W c.D))) ⊆ c.trace (k + 1) :=
  (continuous_subtype_val.closure_preimage_subset _).trans
    (Set.preimage_mono (c.closure_subset k (Nat.lt_of_succ_lt hk)))

theorem le_outerOpen : U ≤ c.W c.D := c.le_zero.trans (c.le_outer 0 (Nat.zero_le _))

theorem range_restrictLE_subset_trace :
    Set.range (M.restrictLE c.le_outerOpen) ⊆ c.trace 0 := by
  rw [range_restrictLE]
  exact Set.preimage_mono c.le_zero

end ResolveChain

/-- **The value along an admissible chain**: the rounds `c.D, …, 1` on the triple restricted to the
outermost open, along the chain, read on `U`, the empty blow-ups erased ([Wlo09, Theorem 2.0.3 (1)];
the empty blow-up convention [Kol07, 32]). Canonicity
(`Hironaka/Resolution/Analytic/Wlo09/Canonicity.lean`) shows that it does not depend on the chain.
-/
def resolveSeqOnAlong (c : ResolveChain T U) :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (M.restrict U) :=
  (resolveFrom bo c.D c.outerTriple c.outerTriple_ord_le c.outerTriple_finite c.trace
    c.isCompact_closure_trace c.closure_trace_subset (M.restrictLE c.le_outerOpen)
    (isLocalDiffeomorph_restrictLE _) c.range_restrictLE_subset_trace).eraseEmpty

theorem noEmptyCenters_resolveSeqOnAlong (c : ResolveChain T U) :
    (resolveSeqOnAlong bo T U c).NoEmptyCenters :=
  AnalyticManifold.BlowUpSequence.noEmptyCenters_eraseEmpty _

/-- **The canonical chain**: `d_U + 1` iterated shrinks of `closure U` inside `{ord 𝓘 ≤ d_U}`, the
`k`-th open being the `(d_U − k)`-th shrink, so the innermost is the last shrink and the outermost
the first. -/
def canonicalResolveChain (hU : IsCompact (closure (U : Set M))) : ResolveChain T U where
  D := maxOrdOn T U hU
  W k := shrinkChain (closure (U : Set M)) (orderOpen T (maxOrdOn T U hU)) hU
    (closure_subset_orderOpen T U hU) (maxOrdOn T U hU - k)
  isCompact_closure k _ := isCompact_closure_shrinkChain hU _ _
  closure_subset k hk := by
    have h : maxOrdOn T U hU - k = (maxOrdOn T U hU - (k + 1)) + 1 := by omega
    rw [h]
    exact closure_shrinkChain_succ_subset hU _ _
  le_zero := fun _ hx => subset_shrinkChain hU _ _ (subset_closure hx)
  ord_le := fun x hx => by
    have h : maxOrdOn T U hU - maxOrdOn T U hU = 0 := Nat.sub_self _
    rw [h] at hx
    exact closure_shrinkChain_zero_subset hU _ (subset_closure hx)

/-- **The value of the resolution family** on the relatively compact open `U`: the rounds `d_U, …,
1` along the canonical chain, read on `U`, the empty blow-ups erased ([Hir64, Main Theorem II(N), p.
176]; [Wlo09, Theorem 2.0.3 (1)]). `Hironaka/Resolution/Analytic/Wlo09/Canonicity.lean` proves its
compatibility under restriction and bundles it into `resolveFam`. -/
def resolveSeqOn (hU : IsCompact (closure (U : Set M))) :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (M.restrict U) :=
  resolveSeqOnAlong bo T U (canonicalResolveChain T U hU)

/-- The value has no empty blow-ups (the empty blow-up convention [Kol07, 32]). -/
theorem noEmptyCenters_resolveSeqOn (hU : IsCompact (closure (U : Set M))) :
    (resolveSeqOn bo T U hU).NoEmptyCenters :=
  AnalyticManifold.BlowUpSequence.noEmptyCenters_eraseEmpty _

end Top

end Hironaka.Manifold

end
