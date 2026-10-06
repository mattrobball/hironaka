/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Basic
public import Hironaka.Manifold.StructureSheaf
import Hironaka.Manifold.BlowUp.Transform.TuningTransform
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The order of a sum of powers of ideal sheaves

Step 2 of the proof of [Kol07, Theorem 107] (item 111) reduces order reduction for the pair of
marked ideals `(N(I), s)`, `(I, m)` to order reduction for the single ideal `N(I)^m + I^s` at the
mark `ms`, by the observation that a centre `Z` satisfies `ord_Z N(I) ≥ s` and `ord_Z I ≥ m` if and
only if `ord_Z (N(I)^m + I^s) ≥ ms`. This file proves the pointwise form of that equivalence on an
analytic manifold: the order of a sum of ideal sheaves is the minimum of the orders and the order
of a power is the multiple of the order (the cosupport identities
`cosupp(I₁ + I₂, m) = cosupp(I₁, m) ∩ cosupp(I₂, m)` and `cosupp(I, m) = cosupp(I^c, mc)` of
[Kol07, Definition 59 (4), (3)], read on orders; `IdealSheaf.ord_pow`), and the factors `m`, `s`
cancel in `ℕ∞`. The sum of ideal sheaves is the join of the stalks.
-/

public section

open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(𝕜, E) ω M]

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The order of a sum of ideal sheaves at a point is the minimum of the two orders
([Kol07, Definition 59 (4)], read on orders): the stalk of the sum is the join of the stalks, and
the order of a join of ideals in a local ring is the minimum (`IsLocalRing.ord_sup`). -/
theorem IdealSheaf.ord_add_eq_min (I J : IdealSheaf (structureSheaf 𝕜 E M)) (x : M) :
    (I + J).ord x = min (I.ord x) (J.ord x) := by
  unfold IdealSheaf.ord
  rw [stalkIdeal_add]
  exact IsLocalRing.ord_sup _ _

/-- For `m, s ≥ 1`, the order of `J₁^m + J₂^s` at `x` is at least `ms` if and only if the order of
`J₁` is at least `s` and the order of `J₂` is at least `m`: the observation of
[Kol07, 111, Step 2] that reduces the pair `(N(I), s)`, `(I, m)` to the single ideal `N(I)^m + I^s`,
here at a point. The order of the sum is the minimum, the order of a power is the multiple, and the
factors cancel in `ℕ∞`. -/
theorem IdealSheaf.le_ord_pow_add_pow_iff [FiniteDimensional 𝕜 E]
    (J₁ J₂ : IdealSheaf (structureSheaf 𝕜 E M)) {m s : ℕ} (hm : 1 ≤ m) (hs : 1 ≤ s) (x : M) :
    ((m * s : ℕ) : ℕ∞) ≤ (J₁ ^ m + J₂ ^ s).ord x ↔
      (s : ℕ∞) ≤ J₁.ord x ∧ (m : ℕ∞) ≤ J₂.ord x := by
  rw [IdealSheaf.ord_add_eq_min, IdealSheaf.ord_pow J₁ hm x, IdealSheaf.ord_pow J₂ hs x,
    le_min_iff, Nat.cast_mul]
  have hm0 : (m : ℕ∞) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hm
  have hs0 : (s : ℕ∞) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hs
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(ENat.mul_le_mul_left_iff hm0 (ENat.natCast_ne_top m)).mp h1, ?_⟩
    rw [mul_comm (m : ℕ∞) (s : ℕ∞)] at h2
    exact (ENat.mul_le_mul_left_iff hs0 (ENat.natCast_ne_top s)).mp h2
  · rintro ⟨h1, h2⟩
    refine ⟨mul_le_mul_of_nonneg_left h1 zero_le, ?_⟩
    rw [mul_comm (m : ℕ∞) (s : ℕ∞)]
    exact mul_le_mul_of_nonneg_left h2 zero_le

end Manifold
