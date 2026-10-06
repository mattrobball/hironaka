/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepBLocal
import Hironaka.Resolution.Analytic.OrderReduction.GlobalizeFamClauses
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The modified first step: the functor on `BOClass 1`

The third step of [Kol07, Theorem 103] at the level of families ("argue as in (37)", the descent
along a finite shrunk cover by hypersurfaces of maximal contact, `globalizeFam`) extends the local
functor of the modified first step (`stepBLocalFunctorFam`, `StepBLocal.lean`) from the local
maximal-contact class to the whole of `BOClass 1`, exactly as `BOanFamOfInputOf` extends Kollár's
local functor, with the same three properties descended on each open: the commutation with local
analytic isomorphisms of the descent (`globalizeFam_commutesWithLocalIsos`), the order clause
(`isOfOrderGe_of_agreeFam`) and the indifference to empty boundary members
(`indifferentToEmptyMembers_of_agreeFam`). There is no clause bounding the order at the end: on the
stopped components the modified run keeps the order at `1` ("the algorithm is stopped",
[Wlo09, Theorem 7.4.1]); the output of the modified algorithm is described instead by the clause
that the controlled transform is locally the ideal of a smooth submanifold transversal to the
boundary.

* `stepBFunctor R hRo hRc hRi bmo₁ : AnalyticFamilyFunctor (refl) (BOClass 1)`;
* `stepBFunctor_commutesWithLocalIsos`, `stepBFunctor_isOfOrderGe`,
  `stepBFunctor_indifferentToEmptyMembers`; `stepBFunctor_fam_eq` (the descent agrees with the local
  functor on the local class).

The composite on each open with the rounds and the monomial phase, the tower over `n` and the
assembled structure are in `ModifiedFam.lean`.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace Hironaka.Local
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

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
  (bmo₁ : BMOanFam.{u} 𝕜 (n - 1) 1)

/-- **The functor of the modified first step on the class of `BO_{n,1}`** ([Wlo09, Theorem 7.4.1];
[Kol07, Theorem 103, Step 3]): the descent of the local functor along a finite shrunk cover by
hypersurfaces of maximal contact, on each open. -/
def stepBFunctor :
    AnalyticFamilyFunctor.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (AnalyticTriple.BOClass 1) :=
  AnalyticFamilyFunctor.globalizeFam (stepBLocalFunctorFam R hRo hRc hRi bmo₁)
    (stepBLocalFunctorFam_commutesWithLocalIsos R hRo hRc hRi bmo₁)

/-- The descent agrees with the local functor on the local maximal-contact class
(`globalizeFam_fam_eq`). -/
theorem stepBFunctor_fam_eq {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) N)
    (hL : AnalyticTriple.LocalMCClass 1 T) :
    (stepBFunctor R hRo hRc hRi bmo₁).fam T hL.1 =
      (stepBLocalFunctorFam R hRo hRc hRi bmo₁).fam T hL :=
  AnalyticFamilyFunctor.globalizeFam_fam_eq (stepBLocalFunctorFam R hRo hRc hRi bmo₁)
    (stepBLocalFunctorFam_commutesWithLocalIsos R hRo hRc hRi bmo₁) T hL

/-- [Kol07, Theorem 103 (2)] for the functor of the modified first step: the descent commutes with
local analytic isomorphisms (`globalizeFam_commutesWithLocalIsos`). -/
theorem stepBFunctor_commutesWithLocalIsos :
    (stepBFunctor R hRo hRc hRi bmo₁).CommutesWithLocalIsos :=
  AnalyticFamilyFunctor.globalizeFam_commutesWithLocalIsos (stepBLocalFunctorFam R hRo hRc hRi bmo₁)
    (stepBLocalFunctorFam_commutesWithLocalIsos R hRo hRc hRi bmo₁)

/-- [Kol07, Definition 66 (2′)–(4′)] at the mark `1` on each open for the functor of the modified
first step: the local clause `stepBLocalFunctorFamOn_isOfOrderGe` descended
(`isOfOrderGe_of_agreeFam`). -/
theorem stepBFunctor_isOfOrderGe {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) N)
    (hT : AnalyticTriple.BOClass 1 T) (U : Opens N) (hU : IsCompact (closure (U : Set N))) :
    (((stepBFunctor R hRo hRc hRi bmo₁).fam T hT).seqOn U hU).toSuccession.IsOfOrderGe
      (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).I 1
      (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).F.idealSheaf :=
  AnalyticFamilyFunctor.isOfOrderGe_of_agreeFam (stepBLocalFunctorFam R hRo hRc hRi bmo₁)
    (stepBFunctor R hRo hRc hRi bmo₁) (stepBFunctor_fam_eq R hRo hRc hRi bmo₁)
    (stepBFunctor_commutesWithLocalIsos R hRo hRc hRi bmo₁)
    (stepBLocalFunctorFamOn_isOfOrderGe R hRo hRc hRi bmo₁) T hT U hU

/-- The counterpart, for boundary members, of the empty blow-up convention [Kol07, 32], for the
functor of the modified first step: the descended indifference to empty boundary members
(`indifferentToEmptyMembers_of_agreeFam`). -/
theorem stepBFunctor_indifferentToEmptyMembers :
    (stepBFunctor R hRo hRc hRi bmo₁).IndifferentToEmptyMembers :=
  AnalyticFamilyFunctor.indifferentToEmptyMembers_of_agreeFam
    (stepBLocalFunctorFam R hRo hRc hRi bmo₁) (stepBFunctor R hRo hRc hRi bmo₁)
    (stepBFunctor_fam_eq R hRo hRc hRi bmo₁) (stepBFunctor_commutesWithLocalIsos R hRo hRc hRi bmo₁)
    (stepBLocalFunctorFam_indifferentToEmptyMembers R hRo hRc hRi bmo₁)

end Hironaka.Manifold.BMOmod

end
