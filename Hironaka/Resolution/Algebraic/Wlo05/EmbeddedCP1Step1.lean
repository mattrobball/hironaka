/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1At
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.MaximalContact.Sequence
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainMonomial
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimStep1
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP1 through Step 1

Step 1 of the proof of [Kol07, Theorem 107] (item 111) runs `BMO_{n,1}` on `(X, I, 1, E)` as rounds
of `BO_{n,d}` on the nonmonomial part `N(I)` for `d = max-ord N(I)` descending to `1`, followed by
Steps 2 and 3. `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimStep1` proved, for the conclusion
of Włodarczyk's Claim, that the first stage whose centre contains the strict transform of a
component lies in the round of order `1` (`not_centerContains_step1Round_of_two_le`) and that no
lift survives Step 1
(`not_genericLift_step1_last`). This module runs the same induction for the statement CP1 of the
embedded desingularization (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`; `CP1For` in
place of `ClaimFor`). The one new step: at the absorbing stage the chain form of the marked
transform of `N(I)`, given by CP1 for `BO_{n,1}` on the nonmonomial triple, gives the chain form of
the marked transform of `I = N(I) · M(I)` by `chainRelativeAt_markedTransformSeq_mul_monomial`
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainMonomial`; the monomial part is
`E.monomial (fun η => (I.ord η).toNat)`, `monomialPart_eq_monomial`). The tower induction is that
of [Kol07, 70]. Used in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Tower`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData Hironaka.BMO Hironaka.Stage Hironaka.Sequence

namespace Hironaka.Resolution

/-- CP1 for the run of `BO_{n,1}` of a family `bo` of order-reduction data over `k`, stated for
every triple of `BOClass n 1` (the hypothesis of the reduction from `BMO_{n,1}`; `ClaimBOFor` with
`CP1For` in place of `ClaimFor`). -/
def CP1BOFor (k : Type u) [Field k] [CharZero k] {n : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d) : Prop :=
  ∀ (T : Triple k) (hT : T.BOClass n 1) (η : T.X.left), η ∈ T.I.support.genericPoints →
    (∀ i, η ∉ (T.E.component i).support) →
    T.I.stalkIdeal η = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η →
    CP1For (((bo 1).functor k).seq T hT) T.I T.E η

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d)

/-- CP1 for the round of order `1`, `BO_{n,1}(X, N(I), E)`, from CP1 for `BO_{n,1}` on the triple
`(X, N(I), E)` (Step 1 of the proof of [Kol07, Theorem 107] at `d = 1`): the chain form of the
marked transform of `N(I)` at the absorbing stage gives that of `I = N(I) · M(I)` by
`chainRelativeAt_markedTransformSeq_mul_monomial`. -/
theorem cp1For_step1Round_of_roundOrder_eq_one (hbo : CP1BOFor k bo) (T : MarkedTriple k)
    (hT : MarkedTriple.BMOClass n 1 T) (hd : 1 ≤ roundOrder T) (h1 : roundOrder T = 1)
    {η : T.X.left}
    (hη : η ∈ T.I.support.genericPoints) (hηE : ∀ i, η ∉ (T.E.component i).support)
    (hIc : T.I.stalkIdeal η = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        {η})).stalkIdeal η) :
    CP1For (step1Round bo T hT hd) T.I T.E η := by
  obtain ⟨T, m⟩ := T
  obtain rfl : m = 1 := hT.2.2
  have key : ∀ (d : ℕ), d = 1 →
      ∀ (hcls : Triple.BOClass n d (nonmonomialTriple (⟨T, 1⟩ : MarkedTriple k)))
        (_ : (((bo d).functor k).seq (nonmonomialTriple (⟨T, 1⟩ : MarkedTriple k))
          hcls).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I 1 T.E),
        CP1For (((bo d).functor k).seq (nonmonomialTriple (⟨T, 1⟩ : MarkedTriple k)) hcls) T.I
          T.E η := by
    intro d e hcls _
    subst e
    have hR := hbo (nonmonomialTriple (⟨T, 1⟩ : MarkedTriple k)) hcls η
      (mem_genericPoints_nonmonomialPart_support ⟨T, 1⟩ hη hηE) hηE
      (stalkIdeal_nonmonomialPart_triple_eq_closure ⟨T, 1⟩ hηE hIc)
    obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
    have hsmn : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
    have hS : (((bo 1).functor k).seq (nonmonomialTriple (⟨T, 1⟩ : MarkedTriple k))
        hcls).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) (nonmonomialPart T.I T.E) 1 T.E :=
      Hironaka.Sequence.IsOrderSeq.isOrderGeSeq (T.X.left ↘ Spec (.of k)) n'
        (((bo 1).functor k).isOrderSeq (nonmonomialTriple (⟨T, 1⟩ : MarkedTriple k)) hcls)
    have hLN : IsLocallyNoetherian T.X.left :=
      (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
    have hNS : NoetherianSpace T.X.left := Hironaka.BD.noetherianSpace_triple T
    have hN : IsNoetherian T.X.left :=
      { toIsLocallyNoetherian := hLN, toCompactSpace := inferInstance }
    -- `I = N(I) · M(I)` with the monomial part a monomial of `E`
    have hsplit : T.I = nonmonomialPart T.I T.E * T.E.monomial (fun η => (T.I.ord η).toNat) := by
      rw [← monomialPart_eq_monomial, mul_comm]
      exact (monomialPart_mul_nonmonomialPart T).symm
    intro i hi hmin p hp
    have hloc := hR i hi hmin p hp
    rw [hsplit]
    exact chainRelativeAt_markedTransformSeq_mul_monomial (T.X.left ↘ Spec (.of k)) n' hS T.isSnc
      (fun η => (T.I.ord η).toNat) i.castSucc hloc
  exact key (roundOrder (⟨T, 1⟩ : MarkedTriple k)) h1 (boClass_nonmonomialTriple ⟨T, 1⟩ hT hd)
    (step1Round_isOrderGeSeq bo ⟨T, 1⟩ hT hd)

/-- CP1 for Step 1 on a marked triple of mark `1` (Step 1 of the proof of [Kol07, Theorem 107], the
loop on `d = max-ord N(I)`), by induction on a bound for the loop variable: a round of order `≥ 2`
contains no centre with `c̃` (`not_centerContains_step1Round_of_two_le`), the round of order `1`
has CP1 from `BO_{n,1}` (`cp1For_step1Round_of_roundOrder_eq_one`), and the rest of Step 1 has it by
induction on the induced marked triple with the lifted member (`cp1For_concat`, `GenericLift`). -/
theorem cp1For_step1_aux (hbo : CP1BOFor k bo) (l : ℕ) :
    ∀ (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n 1 T), roundOrder T ≤ l →
      ∀ (η : T.X.left), η ∈ T.I.support.genericPoints → (∀ i, η ∉ (T.E.component i).support) →
        T.I.stalkIdeal η = (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure {η})).stalkIdeal η →
        CP1For (step1 bo T hT).1 T.I T.E η := by
  induction l with
  | zero =>
    intro T hT hl η _ _ _
    have hlt : roundOrder T < 1 := lt_of_le_of_lt hl Nat.zero_lt_one
    rw [step1_of_lt bo T hT hlt]
    intro i
    exact i.elim0
  | succ l ih =>
    intro T hT hl η hη hηE hIc
    obtain ⟨T, m⟩ := T
    obtain rfl : m = 1 := hT.2.2
    have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
    by_cases hd : 1 ≤ roundOrder (⟨T, 1⟩ : MarkedTriple k)
    · rw [step1_of_le bo _ hT hd]
      refine cp1For_concat _ _ T.I T.E hη hηE hIc ?_ ?_
      · by_cases h2 : 2 ≤ roundOrder (⟨T, 1⟩ : MarkedTriple k)
        · intro i hi _
          exact absurd hi (not_centerContains_step1Round_of_two_le bo ⟨T, 1⟩ hT hd h2 hη hηE hIc i)
        · exact cp1For_step1Round_of_roundOrder_eq_one bo hbo ⟨T, 1⟩ hT hd (by omega) hη hηE hIc
      · intro η' hlift
        exact ih (roundTriple bo ⟨T, 1⟩ hT hd) (bmoClass_roundTriple bo ⟨T, 1⟩ hT hd)
          (Nat.lt_succ_iff.mp (lt_of_lt_of_le (roundOrder_roundTriple_lt bo ⟨T, 1⟩ hT hd) hl)) η'
          hlift.mem_genericPoints hlift.notMem hlift.stalk_eq
    · rw [step1_of_lt bo _ hT (not_le.mp hd)]
      intro i
      exact i.elim0

/-- CP1 for the run of `BMO_{n,1}` from CP1 for `BO_{n,1}` (the proof of [Kol07, Theorem 107],
item 111): the run is `step1 ++ (step2 ++ step3)`, Step 1 has CP1 by the induction on the loop
variable, and no lift of `η` reaches the end of Step 1 (`not_genericLift_step1_last`). -/
theorem cp1For_bmoSeq (hbo : CP1BOFor k bo) (T : MarkedTriple k)
    (hT : MarkedTriple.BMOClass n 1 T) {η : T.X.left} (hη : η ∈ T.I.support.genericPoints)
    (hηE : ∀ i, η ∉ (T.E.component i).support)
    (hIc : T.I.stalkIdeal η = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        {η})).stalkIdeal η) :
    CP1For (bmoSeq bo T hT) T.I T.E η := by
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  unfold bmoSeq
  refine cp1For_concat _ _ T.I T.E hη hηE hIc
    (cp1For_step1_aux bo hbo (roundOrder T) T hT le_rfl η hη hηE hIc) ?_
  intro η' hlift
  exact (not_genericLift_step1_last bo T hT hηE hIc η' hlift).elim

/-- **The Step 1 reduction along the tower** ([Kol07, 70, (70.2)]: (68) in dimension `n` gives
(69) in dimension `n`): CP1 for `BMO_{n+1,1}` from CP1 for `BO_{n+1,1}`. -/
theorem cp1BMOAt_succ_of_cp1BOAt (n : ℕ) (hbo : CP1BOAt k (n + 1)) : CP1BMOAt k (n + 1) := by
  intro T hT η hη hηE hIc
  have hbo' : CP1BOFor k (boOfBMO (tower stage0 n).bmo) := fun T' hT' η' h1 h2 h3 =>
    hbo T' hT' η' h1 h2 h3
  exact cp1For_bmoSeq _ hbo' T hT hη hηE hIc

end Hironaka.Resolution
