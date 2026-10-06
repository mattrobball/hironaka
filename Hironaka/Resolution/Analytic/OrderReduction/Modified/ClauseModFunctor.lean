/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.ModifiedFam
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClauseTools
import Hironaka.Resolution.Analytic.OrderReduction.BaseCases
import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClauseCompose
import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClausePhaseA
import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClausePhaseB
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic


/-!
# The two stop clauses of the modified functor and of the tower; the structure `BMOmodFam`

The modified marked resolution of [Wlo09, Theorem 7.4.1] at dimension `n` is the composite of the
three phases along induced triples: the rounds on the nonmonomial part and the monomial phase, then
the modified first step (`modFunctor`, `ModifiedFam.lean`); the tower `modTower` over all dimensions
recurses on `n`, the recursion of the modified first step on the hypersurface of maximal contact,
level `0` being the trivial functor (`𝕜⁰` is a point; the case of dimension `0` in [Kol07, 70]).
This module proves the two remaining fields of the structure `BMOmodFam 𝕜 n`, the stopped clause
`stopped_never_blownUp` (the stop rule of the modified first step) and the output clause
`output_isSmoothSubmanifoldIdeal` (the form of the output of [Wlo09, Theorem 7.4.1]), for the
composite and for every level of the tower, and assembles the structure: `BMOmodFamOfInput_of_hid`,
the modified marked resolution at every dimension, with the transform identity of the nonmonomial
part `hid` (`NonmonomialTransformIdentity`, `StepARound.lean`) as a parameter at every level;
`concreteBMOmodFam` (`Hironaka/Resolution/Analytic/Wlo09/Concrete.lean`) supplies it as
`nonmonomialTransformIdentity_refl`.

* `nilFamilyFunctor_stoppedClauseFam`, `nilFamilyFunctor_outputClauseFam`: the two clauses of the
  trivial family functor. The stopped clause holds with nothing to check (the empty sequence has no
  centre); the output clause holds with nothing to check at dimension `0`, where the order of every
  ideal sheaf of a triple is `0` (`ord_lt_of_dim_zero`). General facts beside
  `nilFamilyFunctor_isOfOrderGe`.
* `BMOmodFam.ofPre`: the structure from a pre-structure `BMOmodPre` (the order and support clauses
  of the centres and the two naturality clauses) and the two clauses of its functor
  (`OutputClauseFam`, `StoppedClauseFam`, which are the fields definitionally,
  `ClauseTools.lean`).
* `modFunctor_stoppedClauseFam`, `modFunctor_outputClauseFam`: the composite's clauses from the
  stopped clause of the rounds and the monomial phase (`stepACFunctor_stoppedClauseFam`) and the
  two clauses of the modified first step (`stepBFunctor_stoppedClauseFam`,
  `stepBFunctor_outputClauseFam`, from the clauses of the functor one dimension down), by the
  composition lemmas `composeInduced_stoppedClauseFam` and `composeInduced_outputClauseFam`
  (`ClauseCompose.lean`); the output clause needs the modified first step's only, the last stage of
  the composite being its.
* `modTower_stoppedClauseFam`, `modTower_outputClauseFam`: every level, by induction on `n`.
* `BMOmodFamOfInput_of_hid`, `BMOmodFamOfInput_of_hid_functor`: the structure at every level and its
  functor (the tower's, by definition).

Sources: the proof of [Wlo09, Theorem 7.4.1] (the modified algorithm, its stop rule, the form of
its output and the recursion on the dimension); [Kol07, 70] for dimension `0`. The statements
themselves are not in the sources.
-/

@[expose] public section


noncomputable section

open Set Topology TopologicalSpace Hironaka.Manifold Hironaka.Local
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace AnalyticFamilyFunctor

open _root_.Manifold

section Nil

variable {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}
  {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}

/-- **The stopped clause of the trivial family functor** `nilFamilyFunctor` ("everything is
resolved without blow-ups", the case of dimension `0` in [Kol07, 70]): the empty sequence has no
centre, so there is nothing to check: the stage bound of the clause reads `i + k < 0`. -/
theorem nilFamilyFunctor_stoppedClauseFam : (nilFamilyFunctor ψ₀ Dom).StoppedClauseFam ψ₀ := by
  intro M T hT U hU i k h
  exact absurd h (Nat.not_lt_zero _)

end Nil

section NilZero

variable [FiniteDimensional 𝕜 E] {ψ₀ : E ≃L[𝕜] (Fin 0 → 𝕜)}
  {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}

/-- **The output clause of the trivial family functor at dimension `0`** (the case `dim X = 0`,
`I = 𝒪_X`, of [Kol07, 70]): on a manifold modelled on `𝕜⁰` the order of the ideal sheaf is `0` at
every point (`ord_lt_of_dim_zero`), so no point of the last stage (the manifold itself) has order
`≥ 1` and the clause has nothing to check. -/
theorem nilFamilyFunctor_outputClauseFam : (nilFamilyFunctor ψ₀ Dom).OutputClauseFam ψ₀ := by
  intro M T hT U hU x hx
  exfalso
  have h1 := AnalyticTriple.ord_lt_of_dim_zero
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) (le_refl 1) x
  rw [Nat.cast_one] at h1
  exact absurd hx (not_le.mpr h1)

end NilZero

end AnalyticFamilyFunctor

/-- **The structure from a pre-structure and the two clauses**: `BMOmodFam 𝕜 n`
(`ModifiedMarkedFam.lean`) from `BMOmodPre 𝕜 n` (the order and support clauses of the centres and
the two naturality clauses) and the output clause `OutputClauseFam` and stopped clause
`StoppedClauseFam` of its functor, which are the fields `output_isSmoothSubmanifoldIdeal` and
`stopped_never_blownUp` definitionally. -/
def BMOmodFam.ofPre {n : ℕ} (P : BMOmodPre.{u} 𝕜 n)
    (h1 : P.functor.OutputClauseFam (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
    (h8 : P.functor.StoppedClauseFam (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))) :
    BMOmodFam.{u} 𝕜 n :=
  ⟨P.functor, P.isOfOrderGe, P.center_mem_support, h1, h8, P.commutesWithLocalIsos,
    P.indifferentToEmptyMembers⟩

namespace BMOmod

open _root_.Manifold

variable {n : ℕ}
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

/-- **The stopped clause of the modified functor at dimension `n`** (the stop rule of the modified
first step of [Wlo09, Theorem 7.4.1], along the three phases): `composeInduced_stoppedClauseFam` on
the composite of `modFunctor` from the clause of the rounds and the monomial phase
(`stepACFunctor_stoppedClauseFam`) and that of the modified first step
(`stepBFunctor_stoppedClauseFam`, from the clause `hR8` of the functor one dimension down), with
the order clause `stepBFunctor_isOfOrderGe`. -/
theorem modFunctor_stoppedClauseFam
    (hR8 : R.StoppedClauseFam (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))) :
    (modFunctor R hRo hRc hRi bmo₁ bo hcomp hid).StoppedClauseFam
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) := by
  exact AnalyticFamilyFunctor.composeInduced_stoppedClauseFam (stepACFunctor bo hcomp hid)
    (stepBFunctor R hRo hRc hRi bmo₁)
    (fun T hT U hU => stepACFunctor_isOfOrderGe T hT bo hcomp hid U hU)
    (fun T hT U hU => boClass_one_induced_stepACFunctor T hT bo hcomp hid U hU)
    (stepACFunctor_commutesWithLocalIsos bo hcomp hid)
    (stepBFunctor_commutesWithLocalIsos R hRo hRc hRi bmo₁)
    (stepBFunctor_indifferentToEmptyMembers R hRo hRc hRi bmo₁)
    (AnalyticFamilyFunctor.boClass_classPullbackClosed 1)
    (AnalyticFamilyFunctor.boClass_classInducedEraseEmptyClosed 1 1)
    (AnalyticFamilyFunctor.bmoClass_classPullbackClosed 1)
    (fun T' hT' U' hU' => stepBFunctor_isOfOrderGe R hRo hRc hRi bmo₁ T' hT' U' hU')
    (stepACFunctor_stoppedClauseFam bo hcomp hid)
    (stepBFunctor_stoppedClauseFam R hRo hRc hRi bmo₁ hR8)

/-- **The output clause of the modified functor at dimension `n`** (the form of the output of
[Wlo09, Theorem 7.4.1]): `composeInduced_outputClauseFam`. The last stage of the composite is the
last stage of the run of the modified first step on the induced triple, so only its clause
(`stepBFunctor_outputClauseFam`, from the clause `hR1` of the functor one dimension down) enters,
with its order clause. -/
theorem modFunctor_outputClauseFam
    (hR1 : R.OutputClauseFam (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))) :
    (modFunctor R hRo hRc hRi bmo₁ bo hcomp hid).OutputClauseFam
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) := by
  exact AnalyticFamilyFunctor.composeInduced_outputClauseFam (stepACFunctor bo hcomp hid)
    (stepBFunctor R hRo hRc hRi bmo₁)
    (fun T hT U hU => stepACFunctor_isOfOrderGe T hT bo hcomp hid U hU)
    (fun T hT U hU => boClass_one_induced_stepACFunctor T hT bo hcomp hid U hU)
    (stepACFunctor_commutesWithLocalIsos bo hcomp hid)
    (stepBFunctor_commutesWithLocalIsos R hRo hRc hRi bmo₁)
    (stepBFunctor_indifferentToEmptyMembers R hRo hRc hRi bmo₁)
    (AnalyticFamilyFunctor.boClass_classPullbackClosed 1)
    (AnalyticFamilyFunctor.boClass_classInducedEraseEmptyClosed 1 1)
    (AnalyticFamilyFunctor.bmoClass_classPullbackClosed 1)
    (fun T' hT' U' hU' => stepBFunctor_isOfOrderGe R hRo hRc hRi bmo₁ T' hT' U' hU')
    (stepBFunctor_outputClauseFam R hRo hRc hRi bmo₁ hR1)

end BMOmod

namespace BMOmod

variable (𝕜) (bo : ∀ n d : ℕ, BOanFam.{u} 𝕜 n d) (bmo : ∀ n : ℕ, BMOanFam.{u} 𝕜 n 1)
  (hid : ∀ n : ℕ, NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))

variable {𝕜}

/-- **The stopped clause of every level of the tower** (the recursion on the dimension of
[Wlo09, Theorem 7.4.1]): by induction on `n`; level `0` is the trivial functor
(`nilFamilyFunctor_stoppedClauseFam`), level `n + 1` is `modFunctor_stoppedClauseFam` with the
level-`n` clause as `hR8`. -/
theorem modTower_stoppedClauseFam (n : ℕ) :
    (modTower bo bmo hid n).functor.StoppedClauseFam
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) := by
  induction n with
  | zero =>
    exact (AnalyticFamilyFunctor.nilFamilyFunctor_stoppedClauseFam :
      (BMOmodPre.zero 𝕜).functor.StoppedClauseFam _)
  | succ n ih =>
    exact modFunctor_stoppedClauseFam (modTower bo bmo hid n).functor
      (modTower bo bmo hid n).isOfOrderGe (modTower bo bmo hid n).commutesWithLocalIsos
      (modTower bo bmo hid n).indifferentToEmptyMembers (bmo n) (bo (n + 1))
      nonmonomialComap_inhabitant (hid (n + 1)) ih

/-- **The output clause of every level of the tower**: by induction on `n`; level `0` is the
trivial functor at dimension `0` (`nilFamilyFunctor_outputClauseFam`), level `n + 1` is
`modFunctor_outputClauseFam` with the level-`n` clause as `hR1`. -/
theorem modTower_outputClauseFam (n : ℕ) :
    (modTower bo bmo hid n).functor.OutputClauseFam
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) := by
  induction n with
  | zero =>
    exact (AnalyticFamilyFunctor.nilFamilyFunctor_outputClauseFam :
      (BMOmodPre.zero 𝕜).functor.OutputClauseFam _)
  | succ n ih =>
    exact modFunctor_outputClauseFam (modTower bo bmo hid n).functor
      (modTower bo bmo hid n).isOfOrderGe (modTower bo bmo hid n).commutesWithLocalIsos
      (modTower bo bmo hid n).indifferentToEmptyMembers (bmo n) (bo (n + 1))
      nonmonomialComap_inhabitant (hid (n + 1)) ih

variable (𝕜)

/-- **The modified marked resolution at every dimension, with the transform identity as a
parameter** (the proof of [Wlo09, Theorem 7.4.1]): the tower `modTower` with its two clauses
(`modTower_outputClauseFam`, `modTower_stoppedClauseFam`) at every level. The parameter `hid` is the
transform identity of the nonmonomial part at every dimension (`NonmonomialTransformIdentity`);
`concreteBMOmodFam` in `Hironaka/Resolution/Analytic/Wlo09/Concrete.lean` supplies it as
`nonmonomialTransformIdentity_refl`. -/
def BMOmodFamOfInput_of_hid : ∀ n : ℕ, BMOmodFam.{u} 𝕜 n :=
  fun n => BMOmodFam.ofPre (modTower bo bmo hid n) (modTower_outputClauseFam bo bmo hid n)
    (modTower_stoppedClauseFam bo bmo hid n)

variable {𝕜}

/-- The functor of the structure at level `n` is the tower's (by definition). -/
theorem BMOmodFamOfInput_of_hid_functor (n : ℕ) :
    (BMOmodFamOfInput_of_hid 𝕜 bo bmo hid n).functor = (modTower bo bmo hid n).functor := by
  rfl

end BMOmod

end Hironaka.Manifold

end
