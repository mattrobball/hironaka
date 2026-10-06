/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.BmoSeqOn
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.BmoSeqOnNaturality
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The marked order-reduction record `BMO^{an}_{n,m}` from the input family

The packaging of [Kol07, Theorem 107] on manifolds in the family form: the marked order-reduction
functor `BMO_{n,m}` on the class `BMOClass m` at the standard model `𝕜ⁿ`, from the input family
`bo : ∀ d, BOanFam 𝕜 n d` (the order-reduction records at every order), as the structure
`BMOanFam 𝕜 n m` (`Hironaka.Resolution.Analytic.Functor.Family`). The per-open value is
`bmoSeqOn` (`Hironaka.Resolution.Analytic.OrderReduction.Modified.BmoSeqOn`: the chain of the
three steps of the proof, [Kol07, 111], over a relatively compact open, restricted to it and
with its empty blow-ups erased), and the fields of the structure are its exports read one each, as
for `stepAFunctor` (`Hironaka.Resolution.Analytic.OrderReduction.Modified.StepAComm`):

* `bmoFunctor`: the family functor, `bmoSeqOn` on every relatively compact open, without empty
  centres (`bmoSeqOn_noEmptyCenters`), compatible under restriction up to empty blow-ups
  (`bmoSeqOn_compat`; [Wlo09, Theorem 2.0.3, (4)], [Wlo09, Definition 3.2.6]);
* `bmoFunctor_commutesWithLocalIsos` ([Kol07, Theorem 107, (2)]; [Kol07, 34.1] per open) from
  `bmoSeqOn_pullback`, and `bmoFunctor_indifferentToEmptyMembers` from `bmoSeqOn_indiff`;
* `BMOanFamOfInput_of_hid`: the structure, with the order clause `bmoSeqOn_isOfOrderGe`
  ([Kol07, Definition 66, (2′)–(4′)]), the output clause `ord_lt_bmoSeqOn`
  ([Kol07, Theorem 107, (1)]) and the two clauses above.

The four interfaces of the assembly, `hcomp : NonmonomialComap` (the non-monomial part commutes
with pull-back), `hid : NonmonomialTransformIdentity`, `hidN : NonmonomialTransformIdentityMod`
(the identity modulo `N`) and `st3 : MonomialStep3Fam 𝕜 n m` (the third step as a datum), are
binders here, at the fixed `n`; nothing in this module depends on their inhabitants.
`theorem107FamStarOf` (`Hironaka.Resolution.Analytic.OrderReduction.Stage.InstancesFamTheorem107`)
and `concreteTheorem107FamStar` (`Hironaka.Resolution.Analytic.OrderReduction.Stage.Concrete`)
discharge them.
-/

@[expose] public section

universe u

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.Manifold.BMO

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
  (hcomp : BMOmod.NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hid : BMOmod.NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hidN : NonmonomialTransformIdentityMod.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (m : ℕ) (st3 : MonomialStep3Fam.{u} 𝕜 n m) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)

/-- **The family functor of `BMO_{n,m}`** on the marked class at the standard model — `bmoSeqOn` on
every relatively compact open, without empty centres, compatible under restriction up to empty
blow-ups (as `stepAFunctor`, `Hironaka.Resolution.Analytic.OrderReduction.Modified.StepAComm`). -/
noncomputable def bmoFunctor :
    AnalyticFamilyFunctor.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (AnalyticTriple.BMOClass m) where
  fam T hT :=
    ⟨fun U hU => bmoSeqOn T m hT bo hcomp hid hidN st3 U hU,
      fun U hU => bmoSeqOn_noEmptyCenters T m hT bo hcomp hid hidN st3 U hU,
      fun U V hU hV hUV => bmoSeqOn_compat T m hT bo hcomp hid hidN st3 U hU V hV hUV⟩

/-- The value of the family functor on an open is `bmoSeqOn`. -/
@[simp] theorem bmoFunctor_fam_seqOn {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BMOClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    ((bmoFunctor hcomp hid hidN m st3 bo).fam T hT).seqOn U hU =
      bmoSeqOn T m hT bo hcomp hid hidN st3 U hU := rfl

/-- The
family functor commutes with local analytic isomorphisms — `bmoSeqOn_pullback` at the functor's
value (as `stepAFunctor_commutesWithLocalIsos`). -/
theorem bmoFunctor_commutesWithLocalIsos :
    (bmoFunctor hcomp hid hidN m st3 bo).CommutesWithLocalIsos := by
  intro M N T T' g hg hpull hT hT' U' hU'
  exact bmoSeqOn_pullback T m hT bo hcomp hid hidN st3 g hg hpull hT' U' hU'

/-- The family functor is indifferent to empty
boundary members — `bmoSeqOn_indiff` at the functor's value (as
`stepAFunctor_indifferentToEmptyMembers`). -/
theorem bmoFunctor_indifferentToEmptyMembers :
    (bmoFunctor hcomp hid hidN m st3 bo).IndifferentToEmptyMembers := by
  intro M T F' hsnc' e he he' hT hT' U hU
  exact bmoSeqOn_indiff T m hT bo hcomp hid hidN st3 U hU F' hsnc' e he he' hT'

/-- **The structure
`BMO^{an}_{n,m}` from the input family**, the four interfaces of the assembly as binders: the
family functor `bmoFunctor` with the clauses of [Kol07, Theorem 107] read per
relatively compact open: order `≥ m` (`bmoSeqOn_isOfOrderGe`), the last marked transform of order
`< m` pointwise (`ord_lt_bmoSeqOn`, [Kol07, Theorem 107, (1)]), commutation with local analytic
isomorphisms ([Kol07, Theorem 107, (2)]) and indifference to empty members.
`theorem107FamStarOf` and `concreteTheorem107FamStar` (`Stage/InstancesFamTheorem107.lean`,
`Stage/Concrete.lean`) discharge the binders. -/
noncomputable def BMOanFamOfInput_of_hid : BMOanFam.{u} 𝕜 n m where
  functor := bmoFunctor hcomp hid hidN m st3 bo
  isOfOrderGe T hT U hU := bmoSeqOn_isOfOrderGe T m hT bo hcomp hid hidN st3 U hU
  ord_lt T hT U hU x := ord_lt_bmoSeqOn T m hT bo hcomp hid hidN st3 U hU x
  commutesWithLocalIsos := bmoFunctor_commutesWithLocalIsos hcomp hid hidN m st3 bo
  indifferentToEmptyMembers := bmoFunctor_indifferentToEmptyMembers hcomp hid hidN m st3 bo

/-- The functor of the structure is `bmoFunctor`. -/
theorem BMOanFamOfInput_of_hid_functor :
    (BMOanFamOfInput_of_hid hcomp hid hidN m st3 bo).functor = bmoFunctor hcomp hid hidN m st3 bo :=
  rfl

end Hironaka.Manifold.BMO
