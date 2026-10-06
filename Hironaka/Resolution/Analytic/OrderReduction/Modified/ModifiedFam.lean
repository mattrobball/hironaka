/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepCExit
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepBGlobal
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.NonmonomialComapInhabit
public import Hironaka.Resolution.Analytic.Functor.FamilyNil
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepAIndiff
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic


/-!
# The modified marked resolution: the functor at dimension `n` and the tower

The modified marked resolution of [Wlo09, Theorem 7.4.1] runs, on each relatively compact open,
three phases in succession, the rounds on the nonmonomial part (`stepAFunctor`), the monomial phase
(`step2bFunctor`) and the modified first step with the stop rule (`stepBFunctor`), and recurses on
the dimension inside the last (the restriction to the hypersurface `H⁺`). This module assembles the
functor and the tower over the dimension, in the form which carries all the properties of the
structure `BMOmodFam` except the two about the stop predicate (the output is locally the ideal of a
smooth submanifold transversal to the boundary, and a point at which this holds off the boundary is
never blown up again), which are proved of the tower afterwards:

* `stepACFunctor_commutesWithLocalIsos`, `stepACFunctor_indifferentToEmptyMembers`: the two
  naturality properties of the composite of the rounds with the monomial phase (`stepACFunctor` of
  `StepCExit.lean`), from those of the generic composite (`composeInduced_commutesWithLocalIsos`,
  `composeInduced_indifferentToEmptyMembers` with `stepAFunctor_indifferentToEmptyMembers`);
* `modFunctor R hRo hRc hRi bmo₁ bo hcomp hid : AnalyticFamilyFunctor (refl 𝕜 (Fin n → 𝕜))
  (BMOClass 1)`, **the modified functor at dimension `n`**: the `composeInduced` of
  `stepACFunctor bo hcomp hid` (on `BMOClass 1`) with `stepBFunctor R hRo hRc hRi bmo₁` (on
  `BOClass 1`), the class transport being `boClass_one_induced_stepACFunctor` of `StepCExit.lean`;
  `R` is the modified functor one dimension down with its order clause and two naturality
  properties, `bmo₁` the unmodified marked order reduction one dimension down, `bo` the order
  reductions at dimension `n`, `hcomp` and `hid` the two facts about the nonmonomial part which the
  rounds use. Its properties: `modFunctor_isOfOrderGe` (from `composeInduced_isOfOrderGe` and
  `stepBFunctor_isOfOrderGe`), `modFunctor_center_mem_support` (the support clause, from the order
  clause at the mark `1`, `center_support_subset_of_isOfOrderGe`),
  `modFunctor_commutesWithLocalIsos`, `modFunctor_indifferentToEmptyMembers`;
* `BMOmodPre 𝕜 n`, **the structure without the two clauses about the stop predicate**: the fields of
  `BMOmodFam 𝕜 n` other than `output_isSmoothSubmanifoldIdeal` and `stopped_never_blownUp`, with the
  same types; `BMOmodPre.ofModFunctor` packages the functor with its four properties;
  `BMOmodPre.zero 𝕜 : BMOmodPre 𝕜 0` is the level `0`, `𝕜⁰` a point and the value the empty sequence
  on every open ("if `M` is 0-dimensional … all resolutions are trivial", the proof of [Wlo09,
  Theorem 6.0.6]): `nilFamilyFunctor` with its properties, the support clause with no centre to
  check;
* `modTower bo bmo hid : ∀ n, BMOmodPre 𝕜 n`, **the tower** by recursion on `n` (as `towerOf`):
  level `0` is `BMOmodPre.zero`, level `n + 1` is `BMOmodPre.ofModFunctor` at dimension `n + 1`
  with `R` the functor of level `n` and its properties, `bmo n`, `bo (n + 1)`,
  `nonmonomialComap_inhabitant` as `hcomp` and `hid (n + 1)`; `modTower_zero` and `modTower_succ`
  are its two defining equations, which the inductions for the two remaining clauses unfold.

The transform identity `hid : ∀ n, NonmonomialTransformIdentity (refl 𝕜 (Fin n → 𝕜))` is a
parameter of the tower, discharged by `nonmonomialTransformIdentity_inhabitant` when the structure
`BMOmodFam` is assembled. The marked order reduction `bmo` enters only
through the modified first step, the order reductions `bo` only through the rounds.
-/

@[expose] public section


noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

/-- **The structure of the modified marked resolution without the two clauses about the stop
predicate**: the fields of `BMOmodFam 𝕜 n` other than `output_isSmoothSubmanifoldIdeal` and
`stopped_never_blownUp`, i.e. the functor on `BMOClass 1` with its order clause, the support clause
and the two naturality properties, with the same types. The tower `modTower` is built in it level by
level; the two remaining clauses are proved of the tower afterwards, and the structure `BMOmodFam`
assembles both. -/
structure BMOmodPre (𝕜 : Type) [RCLike 𝕜] (n : ℕ) where
  /-- The family functor on the marked class of mark `1` at the standard model `𝕜ⁿ`. -/
  functor : AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    (AnalyticTriple.BMOClass 1)
  /-- The value on `U` is a smooth blow-up sequence of order `≥ 1` starting with the
  restricted `(M, 𝓘, 1, E)`. -/
  isOfOrderGe : ∀ {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BMOClass 1 T) (U : Opens M) (hU : IsCompact (closure (U : Set M))),
    ((functor.fam T hT).seqOn U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf
  /-- Every centre lies in the support of the current controlled transform. -/
  center_mem_support : ∀ {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BMOClass 1 T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (i : Fin ((functor.fam T hT).seqOn U hU).toSuccession.length),
    (((functor.fam T hT).seqOn U hU).toSuccession.center i).support ⊆
      {x | (1 : ℕ∞) ≤ (((functor.fam T hT).seqOn U hU).toSuccession.markedTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1 i.castSucc).ord x}
  /-- The functor commutes with local analytic isomorphisms. -/
  commutesWithLocalIsos : functor.CommutesWithLocalIsos
  /-- The functor is indifferent to empty boundary members. -/
  indifferentToEmptyMembers : functor.IndifferentToEmptyMembers

namespace BMOmod

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
  (R : AnalyticFamilyFunctor.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
    (AnalyticTriple.BMOClass 1))
  (hRo : ∀ {N : AnalyticManifold.{u} 𝕜 (Fin (n - 1) → 𝕜)}
    (T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) N)
    (hT' : AnalyticTriple.BMOClass 1 T') (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))),
    ((R.fam T' hT').seqOn U' hU').toSuccession.IsOfOrderGe
      (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).I 1
      (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).F.idealSheaf)
  (hRc : R.CommutesWithLocalIsos) (hRi : R.IndifferentToEmptyMembers)
  (bmo₁ : BMOanFam.{u} 𝕜 (n - 1) 1) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))

/-- The composite of the rounds with the monomial phase commutes with local analytic isomorphisms
(`composeInduced_commutesWithLocalIsos`). -/
theorem stepACFunctor_commutesWithLocalIsos : (stepACFunctor bo hcomp hid).CommutesWithLocalIsos :=
  AnalyticFamilyFunctor.composeInduced_commutesWithLocalIsos
    (stepAFunctor 1 bo hcomp hid 2 le_rfl one_le_two)
    (step2bFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))) 1
    (fun T hT U hU => stepAFamOn_isOfOrderGe T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU)
    (fun T hT U hU => AnalyticTriple.bmoClass_inducedTriple _ (bmoClass_restrict T hT U) 1 _
      (stepAFamOn_isOfOrderGe T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU))
    (stepAFunctor_commutesWithLocalIsos 1 bo hcomp hid 2 le_rfl one_le_two)
    step2bFunctor_commutesWithLocalIsos step2bFunctor_indifferentToEmptyMembers
    (AnalyticFamilyFunctor.bmoClass_classPullbackClosed 1)
    (AnalyticFamilyFunctor.bmoClass_classInducedEraseEmptyClosed 1 1)
    (AnalyticFamilyFunctor.bmoClass_classPullbackClosed 1)

/-- The composite of the rounds with the monomial phase is indifferent to empty boundary members
(`composeInduced_indifferentToEmptyMembers` with `stepAFunctor_indifferentToEmptyMembers`). -/
theorem stepACFunctor_indifferentToEmptyMembers :
    (stepACFunctor bo hcomp hid).IndifferentToEmptyMembers :=
  AnalyticFamilyFunctor.composeInduced_indifferentToEmptyMembers
    (stepAFunctor 1 bo hcomp hid 2 le_rfl one_le_two)
    (step2bFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))) 1
    (fun T hT U hU => stepAFamOn_isOfOrderGe T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU)
    (fun T hT U hU => AnalyticTriple.bmoClass_inducedTriple _ (bmoClass_restrict T hT U) 1 _
      (stepAFamOn_isOfOrderGe T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU))
    (stepAFunctor_commutesWithLocalIsos 1 bo hcomp hid 2 le_rfl one_le_two)
    step2bFunctor_commutesWithLocalIsos step2bFunctor_indifferentToEmptyMembers
    (AnalyticFamilyFunctor.bmoClass_classPullbackClosed 1)
    (AnalyticFamilyFunctor.bmoClass_classInducedEraseEmptyClosed 1 1)
    (AnalyticFamilyFunctor.bmoClass_classPullbackClosed 1)
    (stepAFunctor_indifferentToEmptyMembers 1 bo hcomp hid 2 le_rfl one_le_two)

/-- **The modified functor at dimension `n`** ([Wlo09, Theorem 7.4.1]: the three phases in
succession on each open): the composite along induced triples of the rounds with the monomial phase
(`stepACFunctor`, on `BMOClass 1`) and of the modified first step
(`stepBFunctor R hRo hRc hRi bmo₁`, on `BOClass 1`), the class transport being
`boClass_one_induced_stepACFunctor`. `R` is the modified functor one dimension down (the recursion
on the dimension of the modified first step), `bo` the order reductions at dimension `n` (the
rounds), `bmo₁` the unmodified marked order reduction one dimension down (the resolution of `Z_{-1}`
in the modified first step). -/
def modFunctor :
    AnalyticFamilyFunctor.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (AnalyticTriple.BMOClass 1) :=
  AnalyticFamilyFunctor.composeInduced (stepACFunctor bo hcomp hid)
    (stepBFunctor R hRo hRc hRi bmo₁) 1
    (fun T hT U hU => stepACFunctor_isOfOrderGe T hT bo hcomp hid U hU)
    (fun T hT U hU => boClass_one_induced_stepACFunctor T hT bo hcomp hid U hU)
    (stepACFunctor_commutesWithLocalIsos bo hcomp hid)
    (stepBFunctor_commutesWithLocalIsos R hRo hRc hRi bmo₁)
    (stepBFunctor_indifferentToEmptyMembers R hRo hRc hRi bmo₁)
    (AnalyticFamilyFunctor.boClass_classPullbackClosed 1)
    (AnalyticFamilyFunctor.boClass_classInducedEraseEmptyClosed 1 1)
    (AnalyticFamilyFunctor.bmoClass_classPullbackClosed 1)

/-- The order clause of the modified functor: `composeInduced_isOfOrderGe` with
`stepBFunctor_isOfOrderGe`. -/
theorem modFunctor_isOfOrderGe {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BMOClass 1 T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (((modFunctor R hRo hRc hRi bmo₁ bo hcomp hid).fam T hT).seqOn U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf :=
  AnalyticFamilyFunctor.composeInduced_isOfOrderGe (stepACFunctor bo hcomp hid)
    (stepBFunctor R hRo hRc hRi bmo₁) 1
    (fun T hT U hU => stepACFunctor_isOfOrderGe T hT bo hcomp hid U hU)
    (fun T hT U hU => boClass_one_induced_stepACFunctor T hT bo hcomp hid U hU)
    (stepACFunctor_commutesWithLocalIsos bo hcomp hid)
    (stepBFunctor_commutesWithLocalIsos R hRo hRc hRi bmo₁)
    (stepBFunctor_indifferentToEmptyMembers R hRo hRc hRi bmo₁)
    (AnalyticFamilyFunctor.boClass_classPullbackClosed 1)
    (AnalyticFamilyFunctor.boClass_classInducedEraseEmptyClosed 1 1)
    (AnalyticFamilyFunctor.bmoClass_classPullbackClosed 1)
    (fun T' hT' U' hU' => stepBFunctor_isOfOrderGe R hRo hRc hRi bmo₁ T' hT' U' hU') T hT U hU

/-- The support clause of the modified functor, from the order clause at the mark `1`
(`center_support_subset_of_isOfOrderGe`). -/
theorem modFunctor_center_mem_support {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BMOClass 1 T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (i : Fin (((modFunctor R hRo hRc hRi bmo₁ bo hcomp hid).fam T hT).seqOn U
      hU).toSuccession.length) :
    ((((modFunctor R hRo hRc hRi bmo₁ bo hcomp hid).fam T hT).seqOn U hU).toSuccession.center
        i).support ⊆
      {x | (1 : ℕ∞) ≤ ((((modFunctor R hRo hRc hRi bmo₁ bo hcomp hid).fam T hT).seqOn U
        hU).toSuccession.markedTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1 i.castSucc).ord x} :=
  center_support_subset_of_isOfOrderGe _
    (modFunctor_isOfOrderGe R hRo hRc hRi bmo₁ bo hcomp hid T hT U hU) le_rfl i

/-- The modified functor commutes with local analytic isomorphisms
(`composeInduced_commutesWithLocalIsos`). -/
theorem modFunctor_commutesWithLocalIsos :
    (modFunctor R hRo hRc hRi bmo₁ bo hcomp hid).CommutesWithLocalIsos :=
  AnalyticFamilyFunctor.composeInduced_commutesWithLocalIsos (stepACFunctor bo hcomp hid)
    (stepBFunctor R hRo hRc hRi bmo₁) 1
    (fun T hT U hU => stepACFunctor_isOfOrderGe T hT bo hcomp hid U hU)
    (fun T hT U hU => boClass_one_induced_stepACFunctor T hT bo hcomp hid U hU)
    (stepACFunctor_commutesWithLocalIsos bo hcomp hid)
    (stepBFunctor_commutesWithLocalIsos R hRo hRc hRi bmo₁)
    (stepBFunctor_indifferentToEmptyMembers R hRo hRc hRi bmo₁)
    (AnalyticFamilyFunctor.boClass_classPullbackClosed 1)
    (AnalyticFamilyFunctor.boClass_classInducedEraseEmptyClosed 1 1)
    (AnalyticFamilyFunctor.bmoClass_classPullbackClosed 1)

/-- The modified functor is indifferent to empty boundary members
(`composeInduced_indifferentToEmptyMembers` with `stepACFunctor_indifferentToEmptyMembers`). -/
theorem modFunctor_indifferentToEmptyMembers :
    (modFunctor R hRo hRc hRi bmo₁ bo hcomp hid).IndifferentToEmptyMembers :=
  AnalyticFamilyFunctor.composeInduced_indifferentToEmptyMembers (stepACFunctor bo hcomp hid)
    (stepBFunctor R hRo hRc hRi bmo₁) 1
    (fun T hT U hU => stepACFunctor_isOfOrderGe T hT bo hcomp hid U hU)
    (fun T hT U hU => boClass_one_induced_stepACFunctor T hT bo hcomp hid U hU)
    (stepACFunctor_commutesWithLocalIsos bo hcomp hid)
    (stepBFunctor_commutesWithLocalIsos R hRo hRc hRi bmo₁)
    (stepBFunctor_indifferentToEmptyMembers R hRo hRc hRi bmo₁)
    (AnalyticFamilyFunctor.boClass_classPullbackClosed 1)
    (AnalyticFamilyFunctor.boClass_classInducedEraseEmptyClosed 1 1)
    (AnalyticFamilyFunctor.bmoClass_classPullbackClosed 1)
    (stepACFunctor_indifferentToEmptyMembers bo hcomp hid)

/-- The structure at dimension `n` from the modified functor and its four properties. -/
def BMOmodPre.ofModFunctor : BMOmodPre.{u} 𝕜 n :=
  ⟨modFunctor R hRo hRc hRi bmo₁ bo hcomp hid,
    modFunctor_isOfOrderGe R hRo hRc hRi bmo₁ bo hcomp hid,
    modFunctor_center_mem_support R hRo hRc hRi bmo₁ bo hcomp hid,
    modFunctor_commutesWithLocalIsos R hRo hRc hRi bmo₁ bo hcomp hid,
    modFunctor_indifferentToEmptyMembers R hRo hRc hRi bmo₁ bo hcomp hid⟩

end BMOmod

namespace BMOmod

variable (𝕜 : Type) [RCLike 𝕜]

/-- **The level `0`**: `𝕜⁰` is a point, the recursion bottoms out ("if `M` is 0-dimensional … all
resolutions are trivial", the proof of [Wlo09, Theorem 6.0.6]), and the value is the empty sequence
on every open: the trivial functor `nilFamilyFunctor` with its properties
(`nilFamilyFunctor_isOfOrderGe`, no centres for the support clause,
`nilFamilyFunctor_commutesWithLocalIsos`, `nilFamilyFunctor_indifferentToEmptyMembers`). -/
def BMOmodPre.zero : BMOmodPre.{u} 𝕜 0 :=
  ⟨AnalyticFamilyFunctor.nilFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin 0 → 𝕜))
      (AnalyticTriple.BMOClass 1),
    fun T hT U hU => AnalyticFamilyFunctor.nilFamilyFunctor_isOfOrderGe T hT U hU 1,
    fun _ _ _ _ i => Fin.elim0 i,
    AnalyticFamilyFunctor.nilFamilyFunctor_commutesWithLocalIsos,
    AnalyticFamilyFunctor.nilFamilyFunctor_indifferentToEmptyMembers⟩

variable {𝕜}

/-- **The tower** `n ↦ BMOmodPre 𝕜 n` (the recursion on the dimension of [Wlo09, Theorem 7.4.1]; as
`towerOf`): level `0` is `BMOmodPre.zero`, level `n + 1` is the modified functor at dimension
`n + 1` with `R` the functor of level `n` (and its properties), `bmo n` and `bo (n + 1)`; `hcomp`
is `nonmonomialComap_inhabitant`, `hid` a parameter at each level. -/
def modTower (bo : ∀ n d : ℕ, BOanFam.{u} 𝕜 n d) (bmo : ∀ n : ℕ, BMOanFam.{u} 𝕜 n 1)
    (hid : ∀ n : ℕ, NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))) :
    ∀ n : ℕ, BMOmodPre.{u} 𝕜 n
  | 0 => BMOmodPre.zero 𝕜
  | n + 1 =>
    BMOmodPre.ofModFunctor (modTower bo bmo hid n).functor (modTower bo bmo hid n).isOfOrderGe
      (modTower bo bmo hid n).commutesWithLocalIsos
      (modTower bo bmo hid n).indifferentToEmptyMembers
      (bmo n) (bo (n + 1)) nonmonomialComap_inhabitant (hid (n + 1))

variable (bo : ∀ n d : ℕ, BOanFam.{u} 𝕜 n d) (bmo : ∀ n : ℕ, BMOanFam.{u} 𝕜 n 1)
  (hid : ∀ n : ℕ, NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))

/-- The level `0` of the tower. -/
theorem modTower_zero : modTower bo bmo hid 0 = BMOmodPre.zero 𝕜 := rfl

/-- The level `n + 1` of the tower (the equation which the inductions for the two remaining clauses
unfold). -/
theorem modTower_succ (n : ℕ) :
    modTower bo bmo hid (n + 1) =
      BMOmodPre.ofModFunctor (modTower bo bmo hid n).functor (modTower bo bmo hid n).isOfOrderGe
        (modTower bo bmo hid n).commutesWithLocalIsos
        (modTower bo bmo hid n).indifferentToEmptyMembers
        (bmo n) (bo (n + 1)) nonmonomialComap_inhabitant (hid (n + 1)) := rfl

end BMOmod

end Hironaka.Manifold

end
