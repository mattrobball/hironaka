/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimAt
public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedGenericLift
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedDisjoint
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedGenericOrder
import Hironaka.Scheme.BlowUp.FlatColon
import Hironaka.Scheme.BlowUpSequence.MarkedLeWeak
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Włodarczyk's Claim along Step 1: the rounds of order `≥ 2` and the end of Step 1

Włodarczyk's proof of his Claim in the proof of [Wlo05, Theorem 4.7.1] passes through the purely
nonmonomial stage ("At this stage `I = N(I)` is purely nonmonomial") before restricting to a
hypersurface of maximal contact. In Kollár's order (Step 1 of the proof of [Kol07, Theorem 107],
item 111) the run of `BMO_{n,1}` on `(X, I, 1, E)` is `step1 ++ step2 ++ step3`, and Step 1 is the
sequence of rounds `BO_{n,d}(X, N(I), E)` for `d = max-ord N(I)` decreasing to below `1`
(`Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step1NonmonomialPart`). For the member `c =
I_{closure η}` of Włodarczyk's Claim, with `η ∉ E` and `I = c` at `η`:

* a round of order `d ≥ 2` never blows up a centre containing the strict transform `c̃`: the
  nonmonomial part has order `1` at the generic point `η̃` of `c̃` (`GenericLift.ord_eq_one`), while
  the centres of the round carry order `d ≥ 2` for the weak transform of `N(I)`, which contains the
  marked transform (`markedTransformSeq_le_weakTransformSeq_of_le`); upper semicontinuity of the
  order (`not_centerContains_of_leOrdAlong_two`) excludes `η̃` from every centre;
* the round of order `1` is `BO_{n,1}(X, N(I), E)`, where the conclusion of Włodarczyk's Claim for
  `BO_{n,1}` (`ClaimBOFor`) concerns the purely nonmonomial triple `(X, N(I), E)`, which satisfies
  the hypotheses of the Claim at `η`;
* after Step 1 the nonmonomial part has maximal order `< 1` (`maxOrd_nonmonomialPart_step1_lt`),
  so no lift of `η` survives: the first containing centre lies in Step 1.

`ClaimBOFor` is the conclusion `ClaimFor` (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimAt`)
for `BO_{n,1}`; since `ClaimKC` is false for the transcribed order
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses`), it is not available at every stage of
the tower, and the module is used only through its lemmas on the rounds of order `≥ 2` and on the
end of Step 1, which `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step1` uses for the induction
on the loop variable `d`, mirroring the recursion of `step1`, with the chain-relative conclusion of
CP1.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData IsLocalRing Hironaka.BMO Hironaka.Stage

namespace Hironaka.Resolution

/-! ### The nonmonomial part off the boundary -/

/-- Off every member of the boundary the nonmonomial part is the ideal itself, stalkwise. -/
theorem stalkIdeal_nonmonomialPart_of_forall_notMem {X : Scheme.{u}} [IsLocallyNoetherian X]
    [NoetherianSpace X] (I : X.IdealSheafData) (E : DivisorFamily X) {x : X}
    (hx : ∀ i, x ∉ (E.component i).support) :
    (nonmonomialPart I E).stalkIdeal x = I.stalkIdeal x := by
  unfold nonmonomialPart
  rw [IdealSheafData.stalkIdeal_colon_of_isLocallyNoetherian,
    stalkIdeal_monomialPart_eq_top_of_forall_notMem _ _ hx, Submodule.top_coe,
    Submodule.colon_univ]

/-- The conclusion of Włodarczyk's Claim for the run of `BO_{n,1}` of a family `bo` of
order-reduction data over the field `k`, stated for every triple of `BOClass n 1` (the hypothesis
of the reduction from `BMO_{n,1}`). -/
def ClaimBOFor (k : Type u) [Field k] [CharZero k] {n : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d) : Prop :=
  ∀ (T : Triple k) (hT : T.BOClass n 1) (η : T.X.left), η ∈ T.I.support.genericPoints →
    (∀ i, η ∉ (T.E.component i).support) →
    T.I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η →
    ClaimFor (((bo 1).functor k).seq T hT) T.I T.E 1 η

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d)

/-! ### The hypotheses of Włodarczyk's Claim for the purely nonmonomial triple -/

section Triple

variable (T : MarkedTriple k) {η : T.X.left} (hη : η ∈ T.I.support.genericPoints)
  (hηE : ∀ i, η ∉ (T.E.component i).support)
  (hIc : T.I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η)

omit [CharZero k] in
include hηE in
/-- At `η ∉ E` the nonmonomial part agrees with `I`. -/
theorem stalkIdeal_nonmonomialPart_triple_eq :
    (nonmonomialPart T.I T.E).stalkIdeal η = T.I.stalkIdeal η := by
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have : NoetherianSpace T.X.left := Hironaka.BD.noetherianSpace_triple T.toTriple
  exact stalkIdeal_nonmonomialPart_of_forall_notMem T.I T.E hηE

omit [CharZero k] in
include hη hηE in
/-- `η` is a generic point of the support of `N(I)`: it lies there (`N(I) = I` at `η`) and the
support of `N(I)` lies in that of `I`. -/
theorem mem_genericPoints_nonmonomialPart_support :
    η ∈ (nonmonomialPart T.I T.E).support.genericPoints := by
  refine ⟨?_, ?_⟩
  · rw [IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal,
      stalkIdeal_nonmonomialPart_triple_eq T hηE]
    exact (IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp hη.1
  · intro ζ hζ hsp
    exact hη.2 (IdealSheafData.support_antitone (IdealSheafData.le_colon_self _ _) hζ) hsp

omit [CharZero k] in
include hηE hIc in
/-- `N(I)` agrees with `c` at `η`. -/
theorem stalkIdeal_nonmonomialPart_triple_eq_closure :
    (nonmonomialPart T.I T.E).stalkIdeal η =
      (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η := by
  rw [stalkIdeal_nonmonomialPart_triple_eq T hηE, hIc]

omit [CharZero k] in
include hηE in
/-- `N(I)` is nonzero at `η`. -/
theorem stalkIdeal_nonmonomialPart_triple_ne_bot : (nonmonomialPart T.I T.E).stalkIdeal η ≠ ⊥ := by
  rw [stalkIdeal_nonmonomialPart_triple_eq T hηE]
  exact T.isNonzeroEverywhere η

end Triple

/-! ### A round of order `≥ 2` never contains the strict transform -/

/-- No centre of a round `BO_{n,d}(X, N(I), E)` with `d ≥ 2` contains the strict transform of
`c = I_{closure η}` (Step 1 of the proof of [Kol07, Theorem 107], the rounds of order `d ≥ 2`): at
the generic point of the strict transform at the first such stage the weak transform of `N(I)` has
order `≤ 1`, while the centre carries order `d ≥ 2`. -/
theorem not_centerContains_step1Round_of_two_le {m : ℕ} (T : MarkedTriple k)
    (hT : MarkedTriple.BMOClass n m T) (hd : m ≤ roundOrder T) (h2 : 2 ≤ roundOrder T)
    {η : T.X.left}
    (hη : η ∈ T.I.support.genericPoints) (hηE : ∀ i, η ∉ (T.E.component i).support)
    (hIc : T.I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η)
        (l : ℕ) :
    ¬ CenterContains (step1Round bo T hT hd) (IdealSheafData.vanishingIdeal (Closeds.closure
        {η})) l := by
  intro hl
  have hex : ∃ l, CenterContains (step1Round bo T hT hd) (IdealSheafData.vanishingIdeal
      (Closeds.closure {η})) l :=
    ⟨l, hl⟩
  have hcont := firstCenterIndex_of_exists hex
  obtain ⟨hi₀, -⟩ := id hcont
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  have hsmn : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
  have hround := step1Round_isOrderSeq bo T hT hd
  obtain ⟨η', hlift⟩ := exists_genericLift (step1Round bo T hT hd) T.I T.E T.m hη hηE hIc
    ⟨firstCenterIndex _ _, Nat.lt_succ_of_lt hi₀⟩ fun l' hl' =>
      not_centerContains_of_lt_firstCenterIndex hex hl'
  have hlN : IsLocallyNoetherian ((step1Round bo T hT hd).stage
      ⟨firstCenterIndex _ _, Nat.lt_succ_of_lt hi₀⟩) :=
    ((T.induced (step1Round bo T hT hd) (step1Round_isOrderGeSeq bo T hT hd) _).X.left ↘
      Spec (.of k)).isLocallyNoetherian_of_field
  have hle : (step1Round bo T hT hd).markedTransformSeq (nonmonomialPart T.I T.E) (roundOrder T)
      ⟨firstCenterIndex _ _, Nat.lt_succ_of_lt hi₀⟩ ≤
      (step1Round bo T hT hd).weakTransformSeq (nonmonomialPart T.I T.E)
        ⟨firstCenterIndex _ _, Nat.lt_succ_of_lt hi₀⟩ :=
    markedTransformSeq_le_weakTransformSeq_of_le (T.X.left ↘ Spec (.of k)) n' le_rfl hround le_rfl _
  have hone : ((step1Round bo T hT hd).markedTransformSeq (nonmonomialPart T.I T.E) (roundOrder T)
      ⟨firstCenterIndex _ _, Nat.lt_succ_of_lt hi₀⟩).ord η' = 1 :=
    ord_markedTransformSeq_eq_one _ _ _ (stalkIdeal_nonmonomialPart_triple_eq_closure T hηE hIc)
      (stalkIdeal_nonmonomialPart_triple_ne_bot T hηE) _ hlift.map hlift.avoid
  have hord : ((step1Round bo T hT hd).weakTransformSeq (nonmonomialPart T.I T.E)
      ⟨firstCenterIndex _ _, Nat.lt_succ_of_lt hi₀⟩).ord η' ≤ 1 :=
    (IdealSheafData.ord_anti hle η').trans hone.le
  have hN : ((step1Round bo T hT hd).weakTransformSeq (nonmonomialPart T.I T.E)
      ⟨firstCenterIndex _ _, Nat.lt_succ_of_lt hi₀⟩).LeOrdAlong
      ((step1Round bo T hT hd).center ⟨firstCenterIndex _ _, hi₀⟩).support ((2 : ℕ) : ℕ∞) := by
    intro ζ hζ
    exact le_of_le_of_eq (by exact_mod_cast h2) ((hround.2 ⟨firstCenterIndex _ _, hi₀⟩).2 ζ hζ).symm
  exact not_centerContains_of_leOrdAlong_two (T.X.left ↘ Spec (.of k)) n' (step1Round bo T hT hd)
    hround.1 (IdealSheafData.vanishingIdeal (Closeds.closure {η})) ⟨firstCenterIndex _ _, hi₀⟩ _ hN
    hlift.mem_support hord hcont

/-! ### After Step 1 no lift survives -/

/-- The lift of `η` cannot reach the end of Step 1 (Step 1 of the proof of [Kol07, Theorem 107]
ends with `max-ord N(I) < m`): there the nonmonomial part has maximal order `< 1`, while at a lift
its stalk is the maximal ideal. So the first centre containing `c̃` lies in Step 1. -/
theorem not_genericLift_step1_last (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n 1 T)
    {η : T.X.left} (hηE : ∀ i, η ∉ (T.E.component i).support)
    (hIc : T.I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η)
    (η' : (step1 bo T hT).1.stage (Fin.last _))
    (hlift : GenericLift (step1 bo T hT).1 T.I T.E 1 η (Fin.last _) η') : False := by
  obtain ⟨T, m⟩ := T
  obtain rfl : m = 1 := hT.2.2
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hlN : IsLocallyNoetherian ((step1 bo ⟨T, 1⟩ hT).1.stage (Fin.last _)) :=
    ((MarkedTriple.induced ⟨T, 1⟩ (step1 bo ⟨T, 1⟩ hT).1 (step1_isOrderGeSeq bo _ hT)
      (Fin.last _)).X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hNS : NoetherianSpace ((step1 bo ⟨T, 1⟩ hT).1.stage (Fin.last _)) :=
    Hironaka.BD.noetherianSpace_triple (MarkedTriple.induced ⟨T, 1⟩ (step1 bo ⟨T, 1⟩ hT).1
      (step1_isOrderGeSeq bo _ hT) (Fin.last _)).toTriple
  have hst := stalkIdeal_nonmonomialPart_markedTransformSeq_eq_maximalIdeal (step1 bo ⟨T, 1⟩ hT).1
    T.I T.E hηE hIc (Fin.last _) hlift.map hlift.avoid
  have hmem : η' ∈ (nonmonomialPart ((step1 bo ⟨T, 1⟩ hT).1.markedTransformSeq T.I 1 (Fin.last _))
      ((step1 bo ⟨T, 1⟩ hT).1.totalTransformSeq T.E (Fin.last _))).support := by
    rw [IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal, hst]
  have hlt := maxOrd_nonmonomialPart_step1_lt bo ⟨T, 1⟩ hT
  rw [Nat.cast_one] at hlt
  exact absurd (lt_of_le_of_lt (((IdealSheafData.one_le_ord_iff _ _).mpr hmem).trans
      (IdealSheafData.le_maxOrd _ _)) hlt)
    (lt_irrefl _)

end Hironaka.Resolution
