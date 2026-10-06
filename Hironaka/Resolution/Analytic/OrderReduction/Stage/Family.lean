/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Stage.Generic
public import Hironaka.Resolution.Analytic.Functor.FamilyNil
public import Hironaka.Resolution.Analytic.OrderReduction.BaseCases
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The order-reduction tower on the compatible-family structures

The recursion on the dimension of [Kol07, 70], stated over arbitrary families of structures in
`Stage/Generic.lean`, instantiated at the compatible-family structures `BOanFam 𝕜 n m` and
`BMOanFam 𝕜 n m` of `Functor/Family.lean`. These are the order-reduction functors of
[Kol07, Theorem 103] and [Kol07, Theorem 107] in the form suited to non-compact analytic
manifolds ([Wlo09, Theorem 2.0.3 (1), (4)]): the value on a triple is a finite blow-up sequence on
every relatively compact open subset, the sequence on a smaller open being the restriction of the
sequence on a larger one once empty blow-ups are deleted.

* `OrderReductionStageAnFam 𝕜 n`, `BOanFamStep 𝕜`, `BMOanFamStep 𝕜` — the stage and the two
  reduction steps at the compatible-family structures (abbreviations of the generic ones);
* `boZeroAnFam m`, `bmoZeroAnFam m`, `stage0AnFam` — the base stage in dimension `0`
  ([Kol07, 70]: everything is resolved without blow-ups), on the trivial family functor
  (`Functor/FamilyNil.lean`): the order clause holds on every relatively compact open because
  the restricted triple lives on a manifold modelled on `𝕜⁰`, where the ideal sheaf is the unit
  ideal sheaf (`AnalyticTriple.ord_lt_of_dim_zero`); the unfolding lemmas are `stage0AnFam_bo`,
  `stage0AnFam_bmo`, `boZeroAnFam_seqOn`, `bmoZeroAnFam_seqOn`;
* `succOfBMOanFam`, `succAnFam` — the successor stage ([Kol07, 70.1] then [Kol07, 70.2]), with
  `succAnFam_eq_succOfBMOanFam`, `succAnFam_bo`, `succAnFam_bmo`, `succAnFam_congr`,
  `exists_succAnFam`;
* `orderReductionTowerAnFam h103 h107` — the recursion, with `orderReductionTowerAnFam_zero`,
  `orderReductionTowerAnFam_succ`, `orderReductionTowerAnFam_succ_bo`,
  `orderReductionTowerAnFam_succ_bmo`, `exists_orderReductionTowerAnFam`, `nonempty_boanFam`,
  `nonempty_bmoanFam` — each the generic statement at the compatible-family structures.

The two steps are constructed in `Stage/InstancesFam.lean` (Theorem 103) and
`Stage/InstancesFamTheorem107.lean` (Theorem 107); the tower at those steps, `Stage/Concrete.lean`,
provides the order-reduction functors used by the analytic main theorems.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜]

/-- A stage of the recursion on the dimension at the compatible-family structures: order reduction
for ideals (`BOanFam`) and for marked ideals (`BMOanFam`) at every mark. -/
abbrev OrderReductionStageAnFam (𝕜 : Type) [RCLike 𝕜] (n : ℕ) : Type (u + 1) :=
  StageOf (BOanFam.{u} 𝕜) (BMOanFam.{u} 𝕜) n

/-- The first reduction step of [Kol07, 70] at the compatible-family structures: order reduction for
ideals in dimension `n + 1` from order reduction for marked ideals in dimension `n`
([Kol07, Theorem 103]). -/
abbrev BOanFamStep (𝕜 : Type) [RCLike 𝕜] : Type (u + 1) :=
  StepBOOf (BOanFam.{u} 𝕜) (BMOanFam.{u} 𝕜)

/-- The second reduction step of [Kol07, 70] at the compatible-family structures: order reduction
for marked ideals in dimension `n` from order reduction for ideals in dimension `n`
([Kol07, Theorem 107]). -/
abbrev BMOanFamStep (𝕜 : Type) [RCLike 𝕜] : Type (u + 1) :=
  StepBMOOf (BOanFam.{u} 𝕜) (BMOanFam.{u} 𝕜)

/-! ### The base stage -/

/-- The standard model in dimension zero. -/
local notation "ψ₀⁰" => ContinuousLinearEquiv.refl 𝕜 (Fin 0 → 𝕜)

/-- Order reduction for ideals in dimension zero at the compatible-family structures ([Kol07, 70]):
the trivial family functor on the class `BOClass m`. On every relatively compact open `U` the
restricted triple lives on a manifold modelled on `𝕜⁰`, where the ideal sheaf is the unit ideal
sheaf and has order `0 < m` (`AnalyticTriple.ord_lt_of_dim_zero`, with `1 ≤ m` from the class);
the other clauses are those of the trivial family functor (`Functor/FamilyNil.lean`). -/
def boZeroAnFam (m : ℕ) : BOanFam.{u} 𝕜 0 m where
  functor := AnalyticFamilyFunctor.nilFamilyFunctor ψ₀⁰ (AnalyticTriple.BOClass m)
  isOfOrderGe T hT U hU := AnalyticFamilyFunctor.nilFamilyFunctor_isOfOrderGe T hT U hU m
  ord_lt := fun {M} T hT U _ x =>
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).ord_lt_of_dim_zero hT.1 x
  commutesWithLocalIsos := AnalyticFamilyFunctor.nilFamilyFunctor_commutesWithLocalIsos
  indifferentToEmptyMembers := AnalyticFamilyFunctor.nilFamilyFunctor_indifferentToEmptyMembers

/-- Order reduction for marked ideals in dimension zero at the compatible-family structures
([Kol07, 70]): the trivial family functor on the class `BMOClass m`, with the same clauses as
`boZeroAnFam`. -/
def bmoZeroAnFam (m : ℕ) : BMOanFam.{u} 𝕜 0 m where
  functor := AnalyticFamilyFunctor.nilFamilyFunctor ψ₀⁰ (AnalyticTriple.BMOClass m)
  isOfOrderGe T hT U hU := AnalyticFamilyFunctor.nilFamilyFunctor_isOfOrderGe T hT U hU m
  ord_lt := fun {M} T hT U _ x =>
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).ord_lt_of_dim_zero hT.1 x
  commutesWithLocalIsos := AnalyticFamilyFunctor.nilFamilyFunctor_commutesWithLocalIsos
  indifferentToEmptyMembers := AnalyticFamilyFunctor.nilFamilyFunctor_indifferentToEmptyMembers

/-- The base stage of the tower on the compatible-family structures, in dimension zero. -/
def stage0AnFam : OrderReductionStageAnFam.{u} 𝕜 0 where
  bo := boZeroAnFam
  bmo := bmoZeroAnFam

variable (𝕜)

theorem stage0AnFam_bo (m : ℕ) : (stage0AnFam.{u} (𝕜 := 𝕜)).bo m = boZeroAnFam m := rfl

theorem stage0AnFam_bmo (m : ℕ) : (stage0AnFam.{u} (𝕜 := 𝕜)).bmo m = bmoZeroAnFam m := rfl

variable {𝕜}

/-- The value of `boZeroAnFam` on every triple and every relatively compact open is the empty
sequence of centres. -/
theorem boZeroAnFam_seqOn (m : ℕ) {M : AnalyticManifold.{u} 𝕜 (Fin 0 → 𝕜)}
    (T : AnalyticTriple ψ₀⁰ M) (hT : AnalyticTriple.BOClass m T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    ((boZeroAnFam m).functor.fam T hT).seqOn U hU = AnalyticManifold.BlowUpSequence.nil
        (M.restrict U) := rfl

/-- The value of `bmoZeroAnFam` on every triple and every relatively compact open is the empty
sequence of centres. -/
theorem bmoZeroAnFam_seqOn (m : ℕ) {M : AnalyticManifold.{u} 𝕜 (Fin 0 → 𝕜)}
    (T : AnalyticTriple ψ₀⁰ M) (hT : AnalyticTriple.BMOClass m T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    ((bmoZeroAnFam m).functor.fam T hT).seqOn U hU = AnalyticManifold.BlowUpSequence.nil
        (M.restrict U) := rfl

/-! ### The successor stage -/

variable (h103 : BOanFamStep.{u} 𝕜) (h107 : BMOanFamStep.{u} 𝕜) {n : ℕ}

/-- The stage `n + 1` from the marked families of the stage `n` ([Kol07, 70]): the first reduction
step applied to the marked families, then the second applied to the result. -/
def succOfBMOanFam (bmo : ∀ s : ℕ, BMOanFam.{u} 𝕜 n s) : OrderReductionStageAnFam.{u} 𝕜 (n + 1) :=
  succOfBMOOf h103 h107 bmo

/-- The successor stage: `succOfBMOanFam` at the marked families of the given stage. -/
def succAnFam (S : OrderReductionStageAnFam.{u} 𝕜 n) : OrderReductionStageAnFam.{u} 𝕜 (n + 1) :=
  succOf h103 h107 S

theorem succAnFam_eq_succOfBMOanFam (S : OrderReductionStageAnFam.{u} 𝕜 n) :
    succAnFam h103 h107 S = succOfBMOanFam h103 h107 S.bmo := rfl

theorem succAnFam_bo (S : OrderReductionStageAnFam.{u} 𝕜 n) :
    (succAnFam h103 h107 S).bo = h103.bo n S.bmo := rfl

theorem succAnFam_bmo (S : OrderReductionStageAnFam.{u} 𝕜 n) :
    (succAnFam h103 h107 S).bmo = h107.bmo (n + 1) (succAnFam h103 h107 S).bo := rfl

/-- The successor stage depends on the stage below only through its marked families, as in the
hypothesis "assume that (69) holds in dimensions `< n`" of [Kol07, Theorem 103]. -/
theorem succAnFam_congr (S S' : OrderReductionStageAnFam.{u} 𝕜 n) (h : S.bmo = S'.bmo) :
    succAnFam h103 h107 S = succAnFam h103 h107 S' :=
  succOf_congr h103 h107 S S' h

theorem exists_succAnFam (S : OrderReductionStageAnFam.{u} 𝕜 n) :
    ∃ S' : OrderReductionStageAnFam.{u} 𝕜 (n + 1),
      S'.bo = h103.bo n S.bmo ∧ S'.bmo = h107.bmo (n + 1) S'.bo :=
  exists_succOf h103 h107 S

/-! ### The recursion -/

/-- The order-reduction tower on the compatible-family structures ([Kol07, 70]): the stage in
every dimension, by recursion from `stage0AnFam` along the two reduction steps. -/
def orderReductionTowerAnFam : ∀ n : ℕ, OrderReductionStageAnFam.{u} 𝕜 n :=
  towerOf stage0AnFam h103 h107

theorem orderReductionTowerAnFam_zero : orderReductionTowerAnFam.{u} h103 h107 0 = stage0AnFam :=
  rfl

theorem orderReductionTowerAnFam_succ (n : ℕ) :
    orderReductionTowerAnFam.{u} h103 h107 (n + 1) =
      succAnFam h103 h107 (orderReductionTowerAnFam h103 h107 n) := rfl

theorem orderReductionTowerAnFam_succ_bo (n m : ℕ) :
    (orderReductionTowerAnFam.{u} h103 h107 (n + 1)).bo m =
      h103.bo n (orderReductionTowerAnFam h103 h107 n).bmo m := rfl

theorem orderReductionTowerAnFam_succ_bmo (n m : ℕ) :
    (orderReductionTowerAnFam.{u} h103 h107 (n + 1)).bmo m =
      h107.bmo (n + 1) (orderReductionTowerAnFam h103 h107 (n + 1)).bo m := rfl

theorem exists_orderReductionTowerAnFam :
    ∃ st : ∀ n : ℕ, OrderReductionStageAnFam.{u} 𝕜 n,
      st 0 = stage0AnFam ∧ ∀ n : ℕ, st (n + 1) = succAnFam h103 h107 (st n) :=
  ⟨orderReductionTowerAnFam h103 h107, rfl, fun _ => rfl⟩

include h103 h107 in
/-- Given the two reduction steps, order reduction for ideals exists in every dimension and at
every mark, in the compatible-family form. -/
theorem nonempty_boanFam (n m : ℕ) : Nonempty (BOanFam.{u} 𝕜 n m) :=
  ⟨(orderReductionTowerAnFam h103 h107 n).bo m⟩

include h103 h107 in
/-- Given the two reduction steps, order reduction for marked ideals exists in every dimension and
at every mark, in the compatible-family form. -/
theorem nonempty_bmoanFam (n m : ℕ) : Nonempty (BMOanFam.{u} 𝕜 n m) :=
  ⟨(orderReductionTowerAnFam h103 h107 n).bmo m⟩

end Hironaka.Manifold

end
