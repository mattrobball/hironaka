/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Deriv
public import Hironaka.Algebra.Local.Tuning
public import Hironaka.Manifold.IdealSheaf.Basic
import Hironaka.Algebra.Local.TuningFinite
import Hironaka.Manifold.IdealSheaf.Monoid
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Maximal coefficient ideal sheaves, D-balanced and MC-invariant ideal sheaves

The analytic forms of three notions of Kollár's proof, for a locally finitely generated ideal
sheaf `J` on an analytic manifold, with the derivative ideal sheaves `D^j J` of
`Hironaka/Manifold/IdealSheaf/Deriv.lean`:

* `IdealSheaf.tuning J m s` is Kollár's maximal coefficient ideal
  `W_s(I) = ∑_{wt(e) ≥ s} ∏_j (D^j I)^{e_j}` [Kol07, Definition 98], the ideal sheaf with that
  stalk at every point (`ofStalks`). It is locally finitely generated because the sum is finite:
  `∑_{e ∈ tuningExponents m s}` suffices (`IsLocalRing.iSup_wt_eq_sum_tuningExponents`), and a
  finite sum of finite products of powers of locally finitely generated ideal sheaves is locally
  finitely generated (the monoid structures of `Hironaka/Manifold/IdealSheaf/Monoid.lean`).
  Kollár's `m = max-ord I` is an explicit parameter.
* `IdealSheaf.IsDBalanced J m`: `(D^i J)^m ⊆ J^{m−i}` for `i < m` [Kol07, Definition 83] (the
  analytic form of the `Hironaka` library's `IsDBalanced`).
* `IdealSheaf.IsMCInvariant J m`: `MC(J) · D(J) ⊆ J` with `MC(J) = D^{m−1} J`
  [Kol07, Definition 79; 53, (53.1)] (the analytic form of the `Hironaka` library's
  `IsMCInvariant`).

The properties of `W_s(J)` — Kollár's Proposition 99, its orders and cosupports — are read off the
`Hironaka` library's coefficient ideals `RegularCoords.W` at the stalks in
`Hironaka/Manifold/IdealSheaf/TuningLemmas.lean`; the tuned ideal sheaves are the input of the
order-reduction algorithm (`Hironaka/Resolution/Analytic/OrderReduction/`).
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory IsLocalRing
open scoped Manifold ContDiff

universe u

namespace Manifold

namespace IdealSheaf

/-! ### The maximal coefficient ideal sheaf (Kollár Definition 98) -/

section Tuning

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(𝕜, E) ω M]
  [FiniteDimensional 𝕜 E] (J : IdealSheaf (structureSheaf 𝕜 E M))

/-- Kollár's `W_s` as a finite sum of finite products [Kol07, Definition 98]: the stalks
`W_s(J)_x = ∑_{wt(e) ≥ s} ∏_j ((D^j J)_x)^{e_j}` have local generators, the sum being the finite
one over `tuningExponents m s`. -/
theorem hasLocalGenerators_tuning (m s : ℕ) :
    HasLocalGenerators fun x =>
      ⨆ (e : Fin (m + 1) → ℕ) (_ : s ≤ wt m e),
        ∏ j : Fin (m + 1), (J.iteratedDeriv (j : ℕ)).stalkIdeal x ^ e j := by
  have h : (fun x => ⨆ (e : Fin (m + 1) → ℕ) (_ : s ≤ wt m e),
        ∏ j : Fin (m + 1), (J.iteratedDeriv (j : ℕ)).stalkIdeal x ^ e j) =
      (∑ e ∈ tuningExponents m s, ∏ j : Fin (m + 1), J.iteratedDeriv (j : ℕ) ^ e j).stalkIdeal := by
    funext x
    rw [stalkIdeal_finset_sum, iSup_wt_eq_sum_tuningExponents m s
      (fun j : Fin (m + 1) => (J.iteratedDeriv (j : ℕ)).stalkIdeal x)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [stalkIdeal_finset_prod]
    exact Finset.prod_congr rfl fun j _ => (stalkIdeal_pow _ _ _).symm
  rw [h]
  exact hasLocalGenerators_stalkIdeal _

/-- The **maximal coefficient ideal sheaf** `W_s(J) = ∑_{wt(e) ≥ s} ∏_j (D^j J)^{e_j}` of order
`s` [Kol07, Definition 98], with the parameter `m` (Kollár's `max-ord I`) explicit — the ideal
sheaf with Kollár's sum as its stalk at every point. -/
def tuning (m s : ℕ) : IdealSheaf (structureSheaf 𝕜 E M) :=
  ofStalks _ _ (J.hasLocalGenerators_tuning m s)

/-- `J` is **D-balanced** with respect to `m` if `(D^i J)^m ⊆ J^{m−i}` for every `i < m`
[Kol07, Definition 83], with `D` the derivative ideal sheaf (the analytic form of the `Hironaka`
library's `IsDBalanced`). -/
def IsDBalanced (m : ℕ) : Prop := ∀ i < m, J.iteratedDeriv i ^ m ≤ J ^ (m - i)

/-- Every ideal sheaf is D-balanced with respect to `1`: the only clause is `J ≤ J`. -/
theorem isDBalanced_one : J.IsDBalanced 1 := fun i hi => by
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  simp only [Nat.sub_zero, pow_one]
  exact le_rfl

/-- `J` is **MC-invariant** with respect to `m` if `MC(J) · D(J) ⊆ J`, `MC(J) = D^{m−1} J`
[Kol07, Definition 79; 53, (53.1)] (the analytic form of the `Hironaka` library's `IsMCInvariant`,
the maximal contact ideal written as `iteratedDeriv (m - 1)`). -/
def IsMCInvariant (m : ℕ) : Prop := J.iteratedDeriv (m - 1) * J.deriv ≤ J

end Tuning

end IdealSheaf

end Manifold

end
