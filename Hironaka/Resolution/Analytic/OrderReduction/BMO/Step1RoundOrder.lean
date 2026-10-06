/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BMO.NonmonomialTriple
public import Hironaka.Manifold.FiniteSuccession.Functor.LocalCover
public import Hironaka.Resolution.Analytic.OrderReduction.Basic
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Round
import Hironaka.Resolution.Analytic.OrderReduction.Finiteness
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The round order of Step 1 on a relatively compact open set

Step 1 of the proof of [Kol07, Theorem 107] (item 111) applies order reduction to the nonmonomial
part `N(𝓘)` at its maximal order `d = max-ord N(𝓘)` and repeats until that order drops below `m`.
On a scheme the maximal order is a single number; on a manifold the order of `N(𝓘)` need not be
bounded, so the **round order** is read on a relatively compact open `U`: `d_U` is the supremum of
`ord_x N(𝓘)` over `closure U`, finite because `N(𝓘)` is nonzero at every point and the order of such
an ideal sheaf is bounded on a compact set (`IdealSheaf.bddAbove_ord_on_compact`). This is the
locally finite reading of [Wlo09, Theorem 2.0.3 (1)], in which the resolution is constructed on a
neighbourhood of a compact set. The file supplies the round order, its finiteness, and the fact
that the restriction of the nonmonomial triple `(M, N(𝓘), E)` to `U` lies in the class of
`BO_{n,d_U}` (the domain of the order reduction functor of [Kol07, Theorem 68]) when `d_U ≥ 1`. The
analytic counterpart of `Hironaka.BMO.roundOrder`.
-/

@[expose] public section

open TopologicalSpace Set Topology
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- The **round order** `d_U` of a triple on a relatively compact open `U`: the supremum over
`closure U` of the order of the nonmonomial part `N(𝓘)`, as a natural number. Kollár's
`d = max-ord N(I)` of [Kol07, 111, Step 1], read on a neighbourhood of a compact set. The
supremum is finite when `closure U` is compact (`coe_roundOrderOn`). -/
noncomputable def roundOrderOn (T : AnalyticTriple ψ₀ M) (U : Opens M) : ℕ :=
  (⨆ x : closure (U : Set M), (nonmonomialPart T.F T.isSnc T.I).ord (x : M)).toNat

/-- The round order is the genuine supremum: `(d_U : ℕ∞) = sup_{x ∈ closure U} ord_x N(𝓘)`. The
supremum is finite because `N(𝓘)` is nonzero at every point and the order of such an ideal sheaf is
bounded on the compact set `closure U`. -/
theorem coe_roundOrderOn (T : AnalyticTriple ψ₀ M) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    (roundOrderOn T U : ℕ∞) =
      ⨆ x : closure (U : Set M), (nonmonomialPart T.F T.isSnc T.I).ord (x : M) := by
  have := finiteDimensional_of_chartIso ψ₀
  obtain ⟨m, hm⟩ := IdealSheaf.bddAbove_ord_on_compact
    (nonmonomialPart_isNonzeroEverywhere T.F T.isSnc T.I T.isNonzeroEverywhere) hU
  exact ENat.natCast_toNat
    (ne_top_of_le_ne_top (ENat.natCast_ne_top m) (iSup_le fun x => hm x.1 x.2))

/-- The order of `N(𝓘)` at any point of `U` is at most the round order `d_U`. -/
theorem ord_le_roundOrderOn (T : AnalyticTriple ψ₀ M) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) {x : M} (hx : x ∈ (U : Set M)) :
    (nonmonomialPart T.F T.isSnc T.I).ord x ≤ (roundOrderOn T U : ℕ∞) := by
  rw [coe_roundOrderOn T U hU]
  exact le_iSup (fun y : closure (U : Set M) => (nonmonomialPart T.F T.isSnc T.I).ord (y : M))
    ⟨x, subset_closure hx⟩

/-- For `d_U ≥ 1`, the restriction of the nonmonomial triple `(M, N(𝓘), E)` to a relatively compact
open `U` lies in the class `BOClass d_U` of the order reduction functor `BO_{n,d_U}` of [Kol07,
Theorem 68], defined on triples whose ideal has order at most `d`: the order of `N(𝓘)` on `U` is at
most `d_U`, and only finitely many boundary members meet `closure U`. This is the input of a round
of [Kol07, 111, Step 1]. -/
theorem boClass_nonmonomialTriple_pullback (T : AnalyticTriple ψ₀ M) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) (hpos : 1 ≤ roundOrderOn T U) :
    AnalyticTriple.BOClass (roundOrderOn T U)
      ((nonmonomialTriple T).pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) := by
  have := finiteDimensional_of_chartIso ψ₀
  exact boClass_pullback_inclusion (nonmonomialTriple T) hpos U hU fun x hx => by
    rw [nonmonomialTriple_I]; exact ord_le_roundOrderOn T U hU hx

end Hironaka.Manifold.BMO
