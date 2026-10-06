/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedState
import Hironaka.Resolution.Algebraic.Kol07.Thm36.SncPreimageSingular
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedBridge
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Remaining
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP2Entry
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP5
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Loop
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedMain
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Hironaka.Resolution.Algebraic.Snc.SncOnTransport
import Hironaka.Scheme.BlowUpSequence.ConcatApi

/-!
# The bridge from the CP loop to the clauses of the theorem

`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedEndBridge` derives the clauses of [Wlo05, Theorem
1.0.2] for `BED` from the end data `EmbeddedEnd ⟨TX, 1⟩ (componentIdeals TX) ∅ (BED TX)` as a
hypothesis: the final strict transform of `Y` is the product of the final strict transforms of its
components, snc with the boundary, hence smooth. This module obtains the end data from the
statements CP1–CP6 (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) instead of the
hypotheses `ClaimKC`, `StratumBlowUp` and `CentersInNonmonomialSupportOrStratum`. The CP side of the
end data: the snc clause for every member (`hasSncWith_strictTransformSeq_bedAux_last_of_invCE`) —
Włodarczyk's "the strict transforms `Ỹᵢ` of `Yᵢ` are smooth and disjoint" and clause (c) of
[Wlo05, Theorem 1.0.2], from the loop theorem of CP5 at the round where the member is absorbed —
and the remaining clauses, the final strict transforms of the members pairwise disjoint and the
marked transform of the ideal their product, which are the end identity of CP6
(`markedTransformSeq_bedAux_last_eq_prod`, `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Loop`).
The assembly `embeddedEnd_bedAux_of_invCE` and its instance `embeddedEnd_BED_of_invCE` at the entry
`(X, I_Y, ∅)` feed the clauses through `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedEndBridge`
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFunctorClauses`). The conclusions are those of
[Wlo05, Theorem 4.7.1]; the route through CP1–CP6 is not in the literature.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.Snc

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

open Classical in
/-- Every member of a state satisfying `InvCE` is absorbed in some round of the loop; from that
round on its strict transform is protected (the entry `protectedState_isolatedTriple_of_absorbed`,
then the loop theorem `protected_bedAux`), so at the end of the loop it has simple normal
crossings with the final boundary ([Wlo05, Theorem 4.7.1]). Strong induction on the number of
members along `bedAux`: a member still live at the absorbing stage of the round is a remaining
member of the isolated state (`invCE_isolatedTriple`), and no member survives a round without
absorption (`exists_centerContains_bmoOneRun_of_invCE`). -/
theorem hasSncWith_strictTransformSeq_bedAux_last_of_invCE (N : ℕ) : ∀ (T : MarkedTriple k)
    (hm : T.m = 1) (C : Finset T.X.left.IdealSheafData), C.card = N → InvCE T.I T.E C →
    ∀ c ∈ C, ((bedAux T hm C).totalTransformSeq T.E (Fin.last _)).HasSncWith
      ((bedAux T hm C).strictTransformSeq c (Fin.last _)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro T hm C hcard hinv c hc
  by_cases h : ∃ n, HasAbsorptionAt T hm C n
  · rw [bedAux_of_exists T hm C h]
    set n₀ := Nat.find h with hn₀
    have hlt : (remainingComponents T hm C n₀).card < N := by
      rw [← hcard]
      exact card_remainingComponents_lt T hm C h
    set R := bedAux (isolatedTriple T hm C n₀) hm (remainingComponents T hm C n₀) with hR
    have e := last_concat ((bmoOneRun T hm).take n₀) R
    have key : (R.totalTransformSeq (isolatedTriple T hm C n₀).E (Fin.last _)).HasSncWith
        (R.strictTransformSeq (((bmoOneRun T hm).take n₀).strictTransformSeq c (Fin.last _))
          (Fin.last _)) := by
      by_cases habs : CenterContains (bmoOneRun T hm) c n₀
      · -- absorbed at `n₀`: the entry, then the loop theorem on the isolated state
        exact (protected_bedAux _ (isolatedTriple T hm C n₀) hm (remainingComponents T hm C n₀) _
          rfl (protectedState_isolatedTriple_of_absorbed T hm C hinv h hc habs)).2.1
      · -- still live at `n₀`: a remaining member, the induction hypothesis
        exact ih _ hlt (isolatedTriple T hm C n₀) hm (remainingComponents T hm C n₀) rfl
          (invCE_isolatedTriple T hm C hinv h) _
          (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hc, habs⟩))
    exact hasSncWith_of_heq e.symm (totalTransformSeq_concat_last_heq _ R T.E).symm
      (strictTransformSeq_concat_last_heq _ R c).symm key
  · rw [bedAux_of_not_exists T hm C h]
    exfalso
    obtain ⟨η, -, rfl, -, -⟩ := hinv.mem c hc
    have := isIntegral_subscheme_vanishingIdeal_closure η
    obtain ⟨n, hn⟩ := exists_centerContains_bmoOneRun_of_invCE T hm hinv hc
    exact h ⟨n, _, hc, hn⟩

/-- **The end result of the loop from CP1–CP6** ([Wlo05, Theorem 4.7.1]): on a state satisfying
`InvCE` the loop ends with the final strict transforms of the members pairwise disjoint and the
marked transform of the ideal their product (the end identity of CP6,
`markedTransformSeq_bedAux_last_eq_prod`), each final strict transform snc with the final
boundary (`hasSncWith_strictTransformSeq_bedAux_last_of_invCE`, CP5), and nothing protected. -/
theorem embeddedEnd_bedAux_of_invCE (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) (hinv : InvCE T.I T.E C) :
    EmbeddedEnd T C ∅ (bedAux T hm C) := by
  classical
  obtain ⟨hpair, hprod⟩ := markedTransformSeq_bedAux_last_eq_prod T hm C hinv
  refine ⟨hprod, fun γ hγ => (Finset.notMem_empty γ hγ).elim, fun z hz => ?_, ?_⟩
  · rw [Finset.union_empty] at hz
    exact hasSncWith_strictTransformSeq_bedAux_last_of_invCE _ T hm C rfl hinv z hz
  · rw [Finset.union_empty]
    exact hpair

/-- **The end result of the loop for `BED`** at the entry `(X, I_Y, ∅)` with the irreducible
components of the reduced `Y` as members (`embeddedStateData_componentIdeals`): the end data of
`BED TX` from CP1–CP6. Clause (c) of [Wlo05, Theorem 1.0.2] follows through
`BED_strictTransform_last_smooth_of_embeddedEnd` and
`BED_hasSncWith_strictTransform_last_of_embeddedEnd`. -/
theorem embeddedEnd_BED_of_invCE (TX : Triple k) (hE : IsEmpty TX.E.ι)
    [IsReduced TX.I.subscheme] : EmbeddedEnd ⟨TX, 1⟩ (componentIdeals TX) ∅ (BED TX) :=
  embeddedEnd_bedAux_of_invCE ⟨TX, 1⟩ rfl (componentIdeals TX)
    (embeddedStateData_componentIdeals TX hE).invCE

end Hironaka.Resolution
