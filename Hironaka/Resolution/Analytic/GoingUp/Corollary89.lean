/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Order
public import Hironaka.Manifold.FiniteSuccession.Restrict.Pushforward
public import Hironaka.Manifold.IdealSheaf.LogDeriv
public import Hironaka.Manifold.IdealSheaf.Tuning
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.FiniteSuccession.DerivTransform
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.LogDerivRestrict
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.GoingUp.PushforwardTransform
import Hironaka.Resolution.Analytic.GoingUp.Tools
import Hironaka.Resolution.Analytic.LogDerivSequence
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Going up: Corollary 89 on the push-forward and the order clause of Theorem 84

Kollár's Corollary 89 [Kol07, Corollary 89] for the push-forward `Π = j_* T` of a sequence `T` on
the smooth hypersurface `S`, read on the stages of `T` through the embeddings `j_i : T_i ↪ X_i`,
and the induction of Kollár's proof of the going-up theorem [Kol07, 90]: **the order clause (4′)
of the push-forward**.

* `PushforwardStage.logDerivIter_pullback_incl`, `logDerivIter_pullback_pushforwardIncl`: the
  restriction identity (87.1) of [Kol07, 87] along `j_i`: the restriction to `T_i` of
  `D^r(−log S_i)(J)` is the `r`-th derivative of the restriction
  (`logDerivIter_pullback_inclusionMap` along `ι_{S_i}`, then the locality of `D` along the
  diffeomorphism `e_i`).
* `le_ordAlong_markedTransformSeq_iteratedDeriv_of_forall_lt`: the order clause of
  [Kol07, Corollary 77] on a prefix (the prefix-bounded form of
  `IsOfOrderGe.isOfOrderGe_iteratedDeriv`).
* `setOf_le_ord_markedTransformSeq_pushforward_inter_eq_iInter_of_forall_lt`: **Corollary 89 on the
  push-forward at a stage `i`**, from the order clause (4′) of `Π` on the steps before `i`:
  `{y ∈ T_i | ord_{j_i y} Π_*^{-1}(I, m) ≥ m} = ⋂_{j<m} cosupp T_*^{-1}((D^j I)|_S, m − j)`. The
  prefix-bounded Theorem 88 on `Π`, restricted to `T_i` summand by summand with (87.1) and the
  push-forward identity, then `cosupp(I, m) = cosupp(D^{m−1}(I), 1)` [Kol07, Lemma 74 (3)] and the
  cosupport of a sum [Kol07, Definition 59], as for Corollary 89 itself in
  `Hironaka/Resolution/Analytic/LogDerivSequence.lean`;
  `setOf_le_ord_markedTransformSeq_pushforward_inter_eq_iInter` is its form for `Π` of order `≥ m`.
* `le_ordAlong_pushforward` (the order half of [Kol07, Theorem 84], Kollár's item 90): for `I`
  D-balanced with `ord I ≤ m` everywhere and `T` of order `≥ m` for `(I|_S, m)` (any boundary),
  `Π` has order `≥ m` for `(I, m)` along every centre. Induction on the stage: Corollary 89 for
  the prefix, the D-balanced inclusion (`setOf_le_ord_markedTransformSeq_subset_iInter`) and the
  order along the pushed-forward centre (`le_ordAlong_pushforward_center_of_setOf_le_ord_subset`).

The normal-crossings clause of the push-forward and the assembly of Theorem 84 are in
`GoingUp/Theorem84.lean`.
-/

public section

noncomputable section

open TopologicalSpace AnalyticManifold.FiniteSuccession
open scoped Manifold ContDiff Topology

universe u

namespace Manifold.PushforwardStage

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} [FiniteDimensional 𝕜 E] {Tᵢ : AnalyticManifold.{u} 𝕜 (Fin (n - 1) → 𝕜)}
  (P : PushforwardStage ψ 1 Tᵢ)

omit [FiniteDimensional 𝕜 E] in
/-- The restriction identity (87.1) of [Kol07, 87] along `j_i = ι_{S_i} ∘ e_i` at one stage of the
push-forward: for the hypersurface `S' = S_i` of `X_i`, the restriction to `T_i` of
`D^r(−log S')(J)` is the `r`-th derivative of the restriction
(`logDerivIter_pullback_inclusionMap` along `ι_{S_i}` and
`iteratedDeriv_pullback_of_isLocalDiffeomorph` along the diffeomorphism `e_i`). -/
theorem logDerivIter_pullback_incl {S' : Set P.space} (hS' : IsClosedSubmanifold ψ S' 1)
    (hset : S' = P.sub) (r : ℕ) (J : AnalyticManifold.IdealSheaf P.space) :
    (IdealSheaf.logDerivIter E ψ hS' r J).pullback ⇑P.incl P.incl.contMDiff =
      (J.pullback ⇑P.incl P.incl.contMDiff).iteratedDeriv r := by
  subst hset
  have h1 : (IdealSheaf.logDerivIter E ψ hS' r J).pullback ⇑P.incl P.incl.contMDiff =
      ((IdealSheaf.logDerivIter E ψ hS' r J).pullback ⇑hS'.inclusionMap
        hS'.inclusionMap.contMDiff).pullback ⇑P.iso P.iso.contMDiff :=
    ((IdealSheaf.pullback_pullback _ ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff ⇑P.iso
      P.iso.contMDiff).trans (IdealSheaf.pullback_congr _ _ P.incl.contMDiff
        (funext fun _ => rfl))).symm
  have h2 : (J.pullback ⇑P.incl P.incl.contMDiff) =
      (J.pullback ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff).pullback ⇑P.iso P.iso.contMDiff :=
    ((IdealSheaf.pullback_pullback J ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff ⇑P.iso
      P.iso.contMDiff).trans (IdealSheaf.pullback_congr _ _ P.incl.contMDiff
        (funext fun _ => rfl))).symm
  rw [h1, h2, logDerivIter_pullback_inclusionMap hS' r J,
    iteratedDeriv_pullback_of_isLocalDiffeomorph ⇑P.iso P.iso.contMDiff _ P.iso.isLocalDiffeomorph]

end Manifold.PushforwardStage

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} [FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E}

/-! ### Corollary 77's order clause on a prefix -/

section Prefix

variable (B : FiniteSuccession M) {I : IdealSheaf M} {m j : ℕ}

/-- [Kol07, Corollary 77] on a prefix: the order clause of `IsOfOrderGe.isOfOrderGe_iteratedDeriv`
from the order clause (4′) alone. If the marked transforms of `(I, m)` have order `≥ m` along the
centres of the steps before `k`, the marked transforms of `(D^j I, m − j)` have order `≥ m − j`
along those centres. -/
theorem le_ordAlong_markedTransformSeq_iteratedDeriv_of_forall_lt (hj : j ≤ m) (k : ℕ)
    (h4 : ∀ i : Fin B.length, i.1 < k → ∀ a ∈ (B.center i).support,
      (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (B.center i) (B.markedTransformSeq I m i.castSucc) a) :
    ∀ i : Fin B.length, i.1 < k → ∀ a ∈ (B.center i).support, ((m - j : ℕ) : ℕ∞) ≤
      IdealSheaf.ordAlongIdeal (B.center i)
        (B.markedTransformSeq (I.iteratedDeriv j) (m - j) i.castSucc) a := fun i hi =>
  le_ordAlong_iteratedDeriv_of_le_of_le_ordAlong hj i (h4 i hi)
    (markedTransformSeq_iteratedDeriv_le_of_forall_lt hj i.castSucc fun i' hi' =>
      h4 i' (by rw [Fin.val_castSucc] at hi'; omega))

end Prefix

/-! ### Corollary 89 on the push-forward -/

section Hypersurface

variable {S : Set M} (hS : IsClosedSubmanifold ψ S 1) (T : FiniteSuccession hS.toAnalyticManifold)
  {I E₀ : IdealSheaf M} {m : ℕ}

omit [FiniteDimensional 𝕜 E] in
/-- The restriction identity (87.1) of [Kol07, 87] along the inclusions `j_i : T_i ↪ X_i` of the
push-forward: the restriction to `T_i` of `D^r(−log S_i)(J)` is the `r`-th derivative of the
restriction; the strict transform `S_i` of the push-forward is the stage data's `S_i`
(`strictTransformSeqAux_pushforward_succ`). -/
theorem logDerivIter_pullback_pushforwardIncl (i : Fin (T.length + 1)) (r : ℕ)
    (J : IdealSheaf ((T.pushforward hS).stage i)) :
    (IdealSheaf.logDerivIter E ψ ((T.pushforward hS).isClosedSubmanifold_strictTransformSeq S hS
        (T.centersIn_pushforward hS) i) r J).pullback ⇑(T.pushforwardIncl hS i)
        (T.pushforwardIncl hS i).contMDiff =
      (J.pullback ⇑(T.pushforwardIncl hS i) (T.pushforwardIncl hS i).contMDiff).iteratedDeriv
        r := by
  obtain ⟨i, hi⟩ := i
  cases i
  · exact (T.pushforwardAux hS 0 hi).logDerivIter_pullback_incl _ rfl r J
  · exact (T.pushforwardAux hS (_ + 1) hi).logDerivIter_pullback_incl _
      (T.strictTransformSeqAux_pushforward_succ hS _ hi) r J

/-- **Corollary 89 on the push-forward** [Kol07, Corollary 89], at a stage `i` from the order
clause (4′) of `Π = j_* T` on the steps before `i` (the working form inside the induction of
Kollár's proof of Theorem 84): on `T_i`, the points where the marked transform of `(I, m)` along `Π`
has order `≥ m` are those where every marked transform of `((D^j I)|_S, m − j)` along `T` has order
`≥ m − j`. The prefix-bounded Theorem 88 on `Π` at the stage `i`, its summands restricted to `T_i`
by (87.1) along `j_i` and the push-forward identity for `(D^j I, m − j)` (Corollary 77's order
clause on the prefix), then `cosupp(I, m) = cosupp(D^{m−1}(I), 1)` [Kol07, Lemma 74 (3)] and the
cosupport of a sum: the proof of Corollary 89 in
`Hironaka/Resolution/Analytic/LogDerivSequence.lean` read through `j_i`. -/
theorem setOf_le_ord_markedTransformSeq_pushforward_inter_eq_iInter_of_forall_lt (hm : 1 ≤ m)
    (i : Fin (T.length + 1))
    (h4 : ∀ i' : Fin T.length, i'.1 < i.1 → ∀ a ∈ ((T.pushforward hS).center i').support,
      (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal ((T.pushforward hS).center i')
        ((T.pushforward hS).markedTransformSeq I m i'.castSucc) a) :
    {y : T.stage i | (m : ℕ∞) ≤
        ((T.pushforward hS).markedTransformSeq I m i).ord (T.pushforwardIncl hS i y)} =
      ⋂ j, ⋂ (_ : j < m), {y | ((m - j : ℕ) : ℕ∞) ≤ (T.markedTransformSeq
        ((I.iteratedDeriv j).pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) (m - j)
          i).ord y} := by
  have h88 := (T.pushforward hS).iteratedDeriv_markedTransformSeq_eq_sum_of_forall_lt hS
    (T.centersIn_pushforward hS) (Nat.sub_le m 1) i h4
  -- the summands, restricted to `T_i`: (87.1) along `j_i`, the push-forward identity for
  -- `(D^j I, m − j)`
  have hsummand : ∀ j, j < m →
      ((IdealSheaf.logDerivIter E ψ ((T.pushforward hS).isClosedSubmanifold_strictTransformSeq S hS
        (T.centersIn_pushforward hS) i) (m - 1 - j)
        ((T.pushforward hS).markedTransformSeq (I.iteratedDeriv j) (m - j) i)).pullback
          ⇑(T.pushforwardIncl hS i) (T.pushforwardIncl hS i).contMDiff) =
      (T.markedTransformSeq
        ((I.iteratedDeriv j).pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) (m - j)
        i).iteratedDeriv (m - 1 - j) := fun j hj => by
    rw [T.logDerivIter_pullback_pushforwardIncl hS i]
    exact congrArg (fun X : IdealSheaf (T.stage i) => X.iteratedDeriv (m - 1 - j))
      (T.markedTransformSeq_pullback_pushforwardIncl_of_forall_lt hS (I.iteratedDeriv j)
        (le_ordAlong_markedTransformSeq_iteratedDeriv_of_forall_lt (T.pushforward hS) hj.le i.1 h4)
        i le_rfl)
  ext y
  rw [Set.mem_ofPred_eq, Set.mem_iInter₂]
  simp only [Set.mem_ofPred_eq]
  rw [IdealSheaf.le_ord_iff_one_le_ord_iteratedDeriv _ hm, IdealSheaf.one_le_ord_iff_mem_support,
    ← Set.mem_preimage,
    ← IdealSheaf.support_pullback ⇑(T.pushforwardIncl hS i) (T.pushforwardIncl hS i).contMDiff,
    h88, Nat.sub_add_cancel hm,
    IdealSheaf.pullback_finset_sum, IdealSheaf.mem_support_finset_sum_iff]
  refine forall_congr' fun j => ?_
  rw [Finset.mem_range]
  refine imp_congr_right fun hj => ?_
  rw [hsummand j hj, ← IdealSheaf.one_le_ord_iff_mem_support,
    show m - 1 - j = m - j - 1 by omega,
    ← IdealSheaf.le_ord_iff_one_le_ord_iteratedDeriv _ (Nat.sub_pos_of_lt hj)]

/-- **Corollary 89 on the push-forward** [Kol07, Corollary 89], read on the stages of `T`: for
`Π = j_* T` of order `≥ m` for `(I, m)`, `1 ≤ m`, at every stage `i`, the points of `T_i` whose
image in `X_i` lies in `cosupp Π_*^{-1}(I, m)` are the points of
`⋂_{j<m} cosupp T_*^{-1}((D^j I)|_S, m − j)`: Corollary 89 on `Π`, its right side carried to the
stages of `T` by the push-forward identity stage by stage (the order clause (4′) of `hge` is all
that is used: `setOf_le_ord_markedTransformSeq_pushforward_inter_eq_iInter_of_forall_lt`). The
algebraic counterpart is `cosupp_markedTransformSeq_pushforward_inter_eq_iInter`. -/
theorem setOf_le_ord_markedTransformSeq_pushforward_inter_eq_iInter
    (hge : (T.pushforward hS).IsOfOrderGe I m E₀) (hm : 1 ≤ m) (i : Fin (T.length + 1)) :
    {y : T.stage i | (m : ℕ∞) ≤
        ((T.pushforward hS).markedTransformSeq I m i).ord (T.pushforwardIncl hS i y)} =
      ⋂ j, ⋂ (_ : j < m), {y | ((m - j : ℕ) : ℕ∞) ≤ (T.markedTransformSeq
        ((I.iteratedDeriv j).pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) (m - j)
          i).ord y} :=
  T.setOf_le_ord_markedTransformSeq_pushforward_inter_eq_iInter_of_forall_lt hS hm i
    fun i' _ _ ha => hge.le_ordAlong i' ha

/-! ### The order clause of the push-forward -/

/-- The order half of the going-up theorem [Kol07, Theorem 84], Kollár's induction [Kol07, 90]:
for `I` D-balanced with `ord I ≤ m` everywhere, `S` a smooth hypersurface and `T` a sequence of
order `≥ m` for `(I|_S, m)` (any boundary), the pushed-forward sequence `j_* T` has order `≥ m` for
`(I, m)` along every centre, i.e. clause (4′) of [Kol07, Definition 66] at every stage. Induction
on the stage: Corollary 89 for the prefix of `j_* T` read on the stages of `T`, then the D-balanced
property and the order along the pushed-forward centre. The hypothesis `_hmax : ∀ y, I.ord y ≤ m`
is Kollár's `m = max-ord I` of Theorem 84 and is kept so that this half carries the hypotheses of
the theorem it serves; the proof does not need it, because Kollár's induction uses only the
D-balanced property, the bound entering only in the passage from order `≥ m` to order exactly `m`
([Kol07, Remark 67], `pushforward_isOfOrder`). The algebraic counterpart is
`IsDBalanced.isOrderSeq_pushforward`. -/
theorem le_ordAlong_pushforward (hI : I.IsDBalanced m) (_hmax : ∀ y, I.ord y ≤ m)
    {E' : IdealSheaf hS.toAnalyticManifold}
    (hT : T.IsOfOrderGe (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) m E') :
    ∀ i : Fin T.length, ∀ a ∈ ((T.pushforward hS).center i).support,
      (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal ((T.pushforward hS).center i)
        ((T.pushforward hS).markedTransformSeq I m i.castSucc) a := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · intro i a _
    simp
  suffices h : ∀ k, ∀ i : Fin T.length, i.1 < k → ∀ a ∈ ((T.pushforward hS).center i).support,
      (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal ((T.pushforward hS).center i)
        ((T.pushforward hS).markedTransformSeq I m i.castSucc) a from
    fun i => h (i.1 + 1) i (Nat.lt_succ_self _)
  intro k
  induction k with
  | zero => exact fun i hi => absurd hi (Nat.not_lt_zero _)
  | succ k ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact ih i hlt
    -- the step `i = k`: Corollary 89 for the prefix, the D-balanced inclusion, the pushed centre
    have hcor := T.setOf_le_ord_markedTransformSeq_pushforward_inter_eq_iInter_of_forall_lt hS hm
      i.castSucc fun i' hi' => ih i' (by rw [Fin.val_castSucc] at hi'; omega)
    refine T.le_ordAlong_pushforward_center_of_setOf_le_ord_subset hS i
      (J := T.markedTransformSeq (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) m
        i.castSucc) (fun _ ha => hT.le_ordAlong i ha) fun y hy => ?_
    have hy' : y ∈ ⋂ j, ⋂ (_ : j < m), {y : T.stage i.castSucc | ((m - j : ℕ) : ℕ∞) ≤
        (T.markedTransformSeq
          ((I.iteratedDeriv j).pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) (m - j)
          i.castSucc).ord y} :=
      T.setOf_le_ord_markedTransformSeq_subset_iInter hS hI hT i.castSucc hy
    rw [← hcor] at hy'
    exact hy'

end Hypersurface

end AnalyticManifold.FiniteSuccession

end
