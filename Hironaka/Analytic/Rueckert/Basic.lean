/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Germ.Coordinate
public import Hironaka.Analytic.Weierstrass.Basic
import Hironaka.Analytic.ConvSeries.Order
import Hironaka.Analytic.ConvSeries.Units
public import Hironaka.Analytic.Weierstrass.Tail
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.Tactic.Positivity.Finset

/-!
# The ring `Conv K m`: domain, local ring, the tail embedding and polynomial evaluation

The definitions and instances that Rückert's theorems on the ring of convergent power series
(Noetherianity, unique factorization, the Nullstellensatz) use throughout, in the classical
setting of [GR65, Chapter II, §B]:

* `Conv K m` is a domain (`instIsDomainConv`): orders add (`order_mul`), so a product of nonzero
  series is nonzero; and a local ring (`instIsLocalRingConv`): the units are the series with
  nonzero constant coefficient (`isUnit_iff_constantCoeff_ne_zero`), whose complement is closed
  under addition. This is the local ring `𝒪_a` of germs of [BM88, p. 23].
* `convTail : Conv K m →ₐ[K] Conv K (m+1)`, the embedding of the tail series (`liftTail`). No
  global `Algebra (Conv K m) (Conv K (m+1))` instance is declared (instance search for
  `SMul (Conv K m) (Conv K (m+1))` through the subalgebra coercions does not terminate in
  reasonable time); module structures over `Conv K m` are introduced locally where the Noetherian
  argument needs them.
* `convPolyEval : (Conv K m)[X] →+* Conv K (m+1)`, evaluation at `x_0` with coefficients embedded
  by `convTail` (`Polynomial.eval₂RingHom`), sending `weierstrassPolynomial d c` to the series
  `weierstrassPoly d c`.

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

@[expose] public section

open MvPowerSeries Polynomial

namespace Analytic

variable {K : Type*} [RCLike K]

variable {m : ℕ}

section Instances

variable (K) in
/-- `Conv K m` has no zero divisors: orders add. -/
instance instNoZeroDivisorsConv : NoZeroDivisors (Conv K m) where
  eq_zero_or_eq_zero_of_mul_eq_zero {u v} h := by
    have h' : (u : MvPowerSeries (Fin m) K) * v = 0 := by
      have := congrArg Subtype.val h
      simpa using this
    have hord := MvPowerSeries.order_eq_top_iff.mpr h'
    rw [order_mul, ENat.add_eq_top] at hord
    rcases hord with hu | hv
    · exact Or.inl (Subtype.ext (MvPowerSeries.order_eq_top_iff.mp hu))
    · exact Or.inr (Subtype.ext (MvPowerSeries.order_eq_top_iff.mp hv))

variable (K) in
/-- `Conv K m` is a domain. -/
instance instIsDomainConv : IsDomain (Conv K m) :=
  NoZeroDivisors.to_isDomain _

variable (K) in
/-- `Conv K m` is a local ring: the nonunits are the series vanishing at `0`, closed under
addition [GR65, Chapter II, §B]. -/
instance instIsLocalRingConv : IsLocalRing (Conv K m) := by
  refine IsLocalRing.of_nonunits_add fun a b ha hb => ?_
  rw [mem_nonunits_iff] at ha hb ⊢
  rw [← Subtype.coe_eta a a.2, isUnit_iff_constantCoeff_ne_zero, not_not] at ha
  rw [← Subtype.coe_eta b b.2, isUnit_iff_constantCoeff_ne_zero, not_not] at hb
  rw [← Subtype.coe_eta (a + b) (a + b).2, isUnit_iff_constantCoeff_ne_zero, not_not,
    Subalgebra.coe_add, map_add, ha, hb, add_zero]

end Instances

section Tail

variable (K) in
/-- The tail embedding `Conv K m → Conv K (m+1)` (the series in `x_1, …, x_m` as series in all
variables, `liftTail`), as a `K`-algebra map. -/
noncomputable def convTail : Conv K m →ₐ[K] Conv K (m + 1) :=
  AlgHom.codRestrict ((MvPowerSeries.rename Fin.succ).comp (Conv K m).val) (Conv K (m + 1))
    fun c => liftTail_mem_conv c.2

@[simp] theorem coe_convTail (c : Conv K m) :
    (convTail K c : MvPowerSeries (Fin (m + 1)) K) = liftTail c :=
  rfl

variable (K) in
/-- Evaluation of a polynomial over `Conv K m` at `x_0`, as a ring map
`(Conv K m)[X] → Conv K (m+1)` (coefficients embedded by `convTail`). -/
noncomputable def convPolyEval : Polynomial (Conv K m) →+* Conv K (m + 1) :=
  Polynomial.eval₂RingHom (convTail K).toRingHom (convX K 0)

@[simp] theorem convPolyEval_C (c : Conv K m) : convPolyEval K (Polynomial.C c) = convTail K c :=
  Polynomial.eval₂_C _ _

variable (K) in
@[simp] theorem convPolyEval_X :
    convPolyEval K (Polynomial.X : Polynomial (Conv K m)) = convX K 0 :=
  Polynomial.eval₂_X _ _

end Tail

end Analytic
