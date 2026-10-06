/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BDCore
import Hironaka.Manifold.FiniteSuccession.Functor.ToSuccessionPushforward
import Hironaka.Resolution.Analytic.OrderReduction.BDCosupp
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Lemma 102: the order clause and clause (1), unconditionally

The order clause of [Kol07, Lemma 102] (`BDCore.lean`) and its clause (1) (`BDCosupp.lean`) were
proved for the construction `BDan` under the hypothesis `PushforwardBridge ψ₀`: the push-forward of
a list of centres without empty centres on a closed hypersurface has, as succession of blow-ups, the
push-forward of the succession of the list ([Kol07, 30.3]). This identification is
`BlowUpSequence.toSuccession_pushforward`
(`Hironaka/Manifold/FiniteSuccession/Functor/ToSuccessionPushforward.lean`), so both clauses hold
outright.

* `pushforwardBridge ψ` — the identification for every model.
* `BDan_isOfOrder`, `BDan_cosupp_disjoint` — the two clauses of Lemma 102 for `BDan`.
-/

public section

noncomputable section

open Set Topology IsLocalRing
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

omit [FiniteDimensional 𝕜 E] in
/-- The push-forward of a list of centres without empty centres along a closed hypersurface has,
as succession of blow-ups, the push-forward of the succession of the list:
`BlowUpSequence.toSuccession_pushforward` at codimension one. -/
theorem pushforwardBridge {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜)) : PushforwardBridge.{u} ψ :=
  fun hS L hL => AnalyticManifold.BlowUpSequence.toSuccession_pushforward hS L hL

variable {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {m : ℕ}

/-- **`BD_{n,m,j}(M, 𝓘, E)` is a smooth blow-up sequence of order `m` starting with `(M, 𝓘, E)`**
([Kol07, Lemma 102]; the going-up statement [Kol07, Corollary 85] for the tail): the order clause
`BDan_isOfOrder_of_bridge` with the identification of the two push-forwards supplied. -/
theorem BDan_isOfOrder (inp : BMOanData 𝕜 (n - 1) (tuningParam m)) (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BOClass m T) (j : T.F.ι) :
    (BDan m inp T hT j).toSuccession.IsOfOrder T.I T.F.idealSheaf m :=
  BDan_isOfOrder_of_bridge (pushforwardBridge ψ₀) inp T hT j

/-- **The birational transform of `E^j` at the end of `BD_{n,m,j}(M, 𝓘, E)` misses the cosupport
`{ord I_r ≥ m}`** ([Kol07, Lemma 102 (1)]): `BDan_cosupp_disjoint_of_bridge` with the
identification of the two push-forwards supplied. -/
theorem BDan_cosupp_disjoint (inp : BMOanData 𝕜 (n - 1) (tuningParam m))
    (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BOClass m T) (j : T.F.ι) :
    Disjoint
      {x | (m : ℕ∞) ≤ ((BDan m inp T hT j).toSuccession.weakTransformSeq T.I (Fin.last _)).ord x}
      ((BDan m inp T hT j).toSuccession.strictTransformSeq (T.F.hyp j) (Fin.last _)) :=
  BDan_cosupp_disjoint_of_bridge (pushforwardBridge ψ₀) inp T hT j

end Hironaka.Manifold

end
