/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.Family
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The trivial compatible-family functor

Kollár starts the induction with `dim X = 0`, where everything is resolved without blow-ups
[Kol07, 70]. On the family layer the functor that resolves without blow-ups is the constant
family functor whose value on every triple is the trivial compatible family
(`CompatibleFamily.nil`: the empty list on every relatively compact open, compatibility by
`pullback_nil` and `eraseEmpty_nil`), cut once for every class and model:

* `AnalyticFamilyFunctor.nilFamilyFunctor ψ₀ Dom`, the family functor `T ↦ CompatibleFamily.nil T`
  on the class `Dom`, with `nilFamilyFunctor_fam` and `nilFamilyFunctor_seqOn` (`rfl`);
* `nilFamilyFunctor_isOfOrderGe`: its value on every relatively compact open is (vacuously) a
  smooth blow-up sequence of order `≥ m` at the restricted triple (`isOfOrderGe_nil`);
* `nilFamilyFunctor_commutesWithLocalIsos`, `nilFamilyFunctor_indifferentToEmptyMembers`: the
  two predicates of a family functor, by `pullback_nil` and `eraseEmpty_nil` (the pull-back of the
  empty list is the empty list, its `eraseEmpty` too) and by the value's independence of the
  triple.

The order clause "`ord I_r < m` at the end" is not general: it is the dimension-zero content of
[Kol07, 70] (`ord_lt_of_dim_zero`) and lives with the base stage of the family tower
(`Hironaka.Resolution.Analytic.OrderReduction.Stage.Family`).
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

namespace AnalyticFamilyFunctor

open _root_.Manifold

/-- **The trivial family functor** on a class `Dom` of
triples at the model `ψ₀` — every triple is sent to the trivial compatible family
(`CompatibleFamily.nil`). -/
def nilFamilyFunctor (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜))
    (Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop) :
    AnalyticFamilyFunctor ψ₀ Dom where
  fam {_M} T _ := CompatibleFamily.nil T

variable {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}
  {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}

@[simp]
theorem nilFamilyFunctor_fam {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : Dom T) :
    (nilFamilyFunctor ψ₀ Dom).fam T hT = CompatibleFamily.nil T := rfl

@[simp]
theorem nilFamilyFunctor_seqOn {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (hT : Dom T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    ((nilFamilyFunctor ψ₀ Dom).fam T hT).seqOn U hU = BlowUpSequence.nil (M.restrict U) := rfl

/-- [Kol07, Definition 66] (2′)–(4′) for the trivial family functor, per relatively compact
open: the empty sequence is (vacuously) a smooth blow-up sequence of order `≥ m` starting with the
restricted triple. -/
theorem nilFamilyFunctor_isOfOrderGe {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (hT : Dom T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) (m : ℕ) :
    (((nilFamilyFunctor ψ₀ Dom).fam T hT).seqOn U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I m
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf :=
  FiniteSuccession.isOfOrderGe_nil _ _ m

/-- [Kol07, 34.1], both bullets, for the trivial family functor, per relatively
compact open: the pull-back of the empty list is the empty list (`pullback_nil`), and so is its
`eraseEmpty` (`eraseEmpty_nil`). -/
theorem nilFamilyFunctor_commutesWithLocalIsos :
    (nilFamilyFunctor ψ₀ Dom).CommutesWithLocalIsos := by
  intro M N T T' g hg _ hT hT' U' hU'
  change BlowUpSequence.nil (N.restrict U') = ((BlowUpSequence.nil _).pullback _ _).eraseEmpty
  simp

/-- Indifference to empty boundary members (not in the source) for the trivial family functor: its
value does not depend on the boundary. -/
theorem nilFamilyFunctor_indifferentToEmptyMembers :
    (nilFamilyFunctor ψ₀ Dom).IndifferentToEmptyMembers := by
  intro M T F' hsnc' e _ _ hT hT' U hU
  rfl

end AnalyticFamilyFunctor

end Hironaka.Manifold

end
