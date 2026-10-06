/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import HironakaExamples.Space.CircleSpace
public import Hironaka.Manifold.Germ.StalkNoetherian
public import Hironaka.Analytic.Germ.Coordinate
import Hironaka.Algebra.Local.PowerSeriesRegular
import Hironaka.Algebra.Local.Regular
import Hironaka.Analytic.ConvSeries.Units
import Hironaka.Analytic.Rueckert.UFD
import Hironaka.Manifold.Germ.TaylorIdeal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init

/-!
# `V(x² + y²) ⊆ ℝ²` is reduced

The real-analytic space `X = V(x² + y²) ⊆ ℝ²` is reduced although its simple locus is empty: the
example behind Hironaka's remark that the simple locus of a reduced real-analytic space need not
be dense [Hir64, Introduction]. Reducedness: the only point of `X` is the origin, where the local
ring is `ℝ{x, y}/(x² + y²)`; `x² + y²` is irreducible in the unique factorisation domain
`ℝ{x, y}` (`Hironaka/Analytic/Rueckert/UFD.lean`), hence prime, so the quotient is a
domain.

* `sumSquares = X₀² + X₁² ∈ Conv ℝ 2` and `irreducible_sumSquares`: if `X₀² + X₁² = a b` with
  `a(0) = b(0) = 0`, the coefficients of `x²`, `y²` and `xy` give `a₁ b₁ = 1`, `a₂ b₂ = 1`,
  `a₁ b₂ + a₂ b₁ = 0` for the linear coefficients, whence `a₁² + a₂² = 0` — impossible over `ℝ`;
  so one factor has a nonzero constant term and is a unit (`isUnit_iff_constantCoeff_ne_zero`).
  Hence `prime_sumSquares` (`irreducible_iff_prime` in a unique factorisation monoid) and the
  prime ideal `(x² + y²)`.
* The stalk of `X` at its point is `𝒜_{⊤,0}/𝓘_0` (`stalkEquiv`), `𝓘_0` the image of the ambient
  ideal `(germ (x² + y²))` of `𝒜_{ℝ²,0}` (`stalkIdeal_modelIdeal_eq_map`), which the Taylor
  isomorphism `𝒜_{ℝ²,0} ≅ ℝ{x, y}` (`taylorEquivConv`) carries to `(X₀² + X₁²)` (the coordinate
  germs at `0` go to `X_i`); prime ideals correspond, the quotient is a domain, and reducedness
  passes back along the isomorphisms.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold Analytic MvPowerSeries
open scoped Manifold ContDiff

universe u

namespace Hironaka.Space

open AnalyticSpace

/-! ### `x² + y²` is irreducible in `ℝ{x, y}` -/

section Irreducible

/-- `X₀² + X₁² ∈ ℝ{x, y}`. -/
def sumSquares : Analytic.Conv ℝ 2 := convX ℝ 0 ^ 2 + convX ℝ 1 ^ 2

theorem coe_sumSquares : (sumSquares : MvPowerSeries (Fin 2) ℝ) = X 0 ^ 2 + X 1 ^ 2 := by
  simp [sumSquares]

theorem single_zero_two_ne_single_one_two :
    (Finsupp.single (0 : Fin 2) 2 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 2 := by
  intro h
  have := DFunLike.congr_fun h 0
  simp at this

theorem single_add_single_ne_single_zero :
    (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 2 := by
  intro h
  have := DFunLike.congr_fun h 1
  simp at this

theorem single_add_single_ne_single_one :
    (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 2 := by
  intro h
  have := DFunLike.congr_fun h 0
  simp at this

theorem coeff_single_two_sumSquares (s : Fin 2) :
    coeff (Finsupp.single s 2) (sumSquares : MvPowerSeries (Fin 2) ℝ) = 1 := by
  rw [coe_sumSquares, map_add, coeff_X_pow, coeff_X_pow]
  fin_cases s
  · simp [single_zero_two_ne_single_one_two]
  · simp [single_zero_two_ne_single_one_two.symm]

theorem coeff_single_add_single_sumSquares :
    coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)
      (sumSquares : MvPowerSeries (Fin 2) ℝ) = 0 := by
  rw [coe_sumSquares, map_add, coeff_X_pow, coeff_X_pow]
  simp [single_add_single_ne_single_zero, single_add_single_ne_single_one]

theorem sumSquares_ne_zero : sumSquares ≠ 0 := by
  intro h
  have := coeff_single_two_sumSquares 0
  rw [h] at this
  simp at this

theorem constantCoeff_sumSquares : constantCoeff (sumSquares : MvPowerSeries (Fin 2) ℝ) = 0 := by
  rw [coe_sumSquares]
  simp

/-- The antidiagonal of `2` in `ℕ`. -/
theorem nat_antidiagonal_two :
    Finset.HasAntidiagonal.antidiagonal (2 : ℕ) = {(0, 2), (1, 1), (2, 0)} := by
  decide

/-- The `x_s²`-coefficient of a product of two series without constant term. -/
theorem coeff_single_two_mul {a b : MvPowerSeries (Fin 2) ℝ} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) (s : Fin 2) :
    coeff (Finsupp.single s 2) (a * b) =
      coeff (Finsupp.single s 1) a * coeff (Finsupp.single s 1) b := by
  classical
  rw [coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map, nat_antidiagonal_two,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map_apply,
    Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply, ha, hb, zero_mul, mul_zero, zero_add,
    add_zero]

/-- The antidiagonal of `e₀ + e₁` in `Fin 2 →₀ ℕ`. -/
theorem antidiagonal_single_add_single :
    Finset.HasAntidiagonal.antidiagonal (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1) =
      {((0 : Fin 2 →₀ ℕ), Finsupp.single 0 1 + Finsupp.single 1 1),
        (Finsupp.single 0 1, Finsupp.single 1 1), (Finsupp.single 1 1, Finsupp.single 0 1),
        (Finsupp.single 0 1 + Finsupp.single 1 1, 0)} := by
  ext ⟨a, b⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  rw [Finset.HasAntidiagonal.mem_antidiagonal]
  constructor
  · intro hab
    have h0 := DFunLike.congr_fun hab 0
    have h1 := DFunLike.congr_fun hab 1
    simp only [Finsupp.add_apply, Finsupp.single_apply, Fin.isValue, Fin.zero_eq_one_iff,
      OfNat.ofNat_ne_one, ↓reduceIte, one_ne_zero, add_zero, zero_add] at h0 h1
    have ea : a = Finsupp.single 0 (a 0) + Finsupp.single 1 (a 1) := by
      ext i; fin_cases i <;> simp
    have eb : b = Finsupp.single 0 (b 0) + Finsupp.single 1 (b 1) := by
      ext i; fin_cases i <;> simp
    have ha0 : a 0 = 0 ∨ a 0 = 1 := by omega
    have ha1 : a 1 = 0 ∨ a 1 = 1 := by omega
    have hb0 : b 0 = 1 - a 0 := by omega
    have hb1 : b 1 = 1 - a 1 := by omega
    rw [ea, eb, hb0, hb1]
    rcases ha0 with ha0 | ha0 <;> rcases ha1 with ha1 | ha1 <;> rw [ha0, ha1] <;> simp
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [add_comm]

/-- The `xy`-coefficient of a product of two series without constant term. -/
theorem coeff_single_add_single_mul {a b : MvPowerSeries (Fin 2) ℝ} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) :
    coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1) (a * b) =
      coeff (Finsupp.single 0 1) a * coeff (Finsupp.single 1 1) b +
        coeff (Finsupp.single 1 1) a * coeff (Finsupp.single 0 1) b := by
  classical
  have h1 : ((0 : Fin 2 →₀ ℕ), Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1) ∉
      ({(Finsupp.single 0 1, Finsupp.single 1 1), (Finsupp.single 1 1, Finsupp.single 0 1),
        (Finsupp.single 0 1 + Finsupp.single 1 1, 0)} : Finset ((Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ))) := by
    simp [eq_comm, Finsupp.single_eq_zero]
  have h2 : (Finsupp.single (0 : Fin 2) 1, Finsupp.single (1 : Fin 2) 1) ∉
      ({(Finsupp.single 1 1, Finsupp.single 0 1),
        (Finsupp.single 0 1 + Finsupp.single 1 1, 0)} : Finset ((Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ))) := by
    simp [Finsupp.single_eq_single_iff, Finsupp.single_eq_zero]
  have h3 : (Finsupp.single (1 : Fin 2) 1, Finsupp.single (0 : Fin 2) 1) ∉
      ({(Finsupp.single 0 1 + Finsupp.single 1 1, 0)} : Finset ((Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ))) := by
    simp [Finsupp.single_eq_zero]
  rw [coeff_mul, antidiagonal_single_add_single, Finset.sum_insert h1, Finset.sum_insert h2,
    Finset.sum_insert h3, Finset.sum_singleton]
  simp only [coeff_zero_eq_constantCoeff_apply, ha, hb, zero_mul, mul_zero, zero_add, add_zero]

/-- `x² + y²` is irreducible in `ℝ{x, y}`: a factorisation `x² + y² = a b` with `a(0) = b(0) = 0`
would give `a₁ b₁ = a₂ b₂ = 1` and `a₁ b₂ + a₂ b₁ = 0` for the linear coefficients, i.e.
`a₁² + a₂² = 0`, impossible over `ℝ`. -/
theorem irreducible_sumSquares : Irreducible sumSquares := by
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · exact (isUnit_iff_constantCoeff_ne_zero sumSquares.2).mp hu constantCoeff_sumSquares
  · have h : (sumSquares : MvPowerSeries (Fin 2) ℝ) = (a : MvPowerSeries (Fin 2) ℝ) * b :=
      congrArg Subtype.val hab
    by_cases ha0 : constantCoeff (a : MvPowerSeries (Fin 2) ℝ) = 0
    · by_cases hb0 : constantCoeff (b : MvPowerSeries (Fin 2) ℝ) = 0
      · exfalso
        have e1 := congrArg (coeff (Finsupp.single (0 : Fin 2) 2)) h
        have e2 := congrArg (coeff (Finsupp.single (1 : Fin 2) 2)) h
        have e3 := congrArg (coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)) h
        rw [coeff_single_two_sumSquares, coeff_single_two_mul ha0 hb0] at e1 e2
        rw [coeff_single_add_single_sumSquares, coeff_single_add_single_mul ha0 hb0] at e3
        set x₁ := coeff (Finsupp.single (0 : Fin 2) 1) (a : MvPowerSeries (Fin 2) ℝ)
        set x₂ := coeff (Finsupp.single (1 : Fin 2) 1) (a : MvPowerSeries (Fin 2) ℝ)
        set y₁ := coeff (Finsupp.single (0 : Fin 2) 1) (b : MvPowerSeries (Fin 2) ℝ)
        set y₂ := coeff (Finsupp.single (1 : Fin 2) 1) (b : MvPowerSeries (Fin 2) ℝ)
        have h4 : x₁ * x₁ + x₂ * x₂ = 0 := by
          linear_combination (x₁ * x₂) * e3.symm - x₁ * x₁ * e2.symm - x₂ * x₂ * e1.symm
        obtain ⟨hx1, -⟩ := mul_self_add_mul_self_eq_zero.mp h4
        rw [hx1, zero_mul] at e1
        exact one_ne_zero e1
      · exact Or.inr ((isUnit_iff_constantCoeff_ne_zero b.2).mpr hb0)
    · exact Or.inl ((isUnit_iff_constantCoeff_ne_zero a.2).mpr ha0)

theorem prime_sumSquares : Prime sumSquares := irreducible_iff_prime.mp irreducible_sumSquares

theorem isPrime_span_sumSquares : (Ideal.span {sumSquares}).IsPrime :=
  (Ideal.span_singleton_prime sumSquares_ne_zero).mpr prime_sumSquares

end Irreducible

/-! ### The stalk of `V(x² + y²)` at the origin -/

/-- The Taylor isomorphism `𝒜_{ℝ²,0} ≃ ℝ{x, y}` in the identity chart. -/
def taylorOrigin :
    (affine.{u} ℝ 2).toLocallyRingedSpace.presheaf.stalk (ULift.up 0) ≃+* Analytic.Conv ℝ 2 :=
  taylorEquivConv (Kn.{u} ℝ 2) ContinuousLinearEquiv.ulift (chartAt (Kn.{u} ℝ 2) (ULift.up 0))
    (mem_chart_source _ _) (IsManifold.chart_mem_maximalAtlas _)

/-- The Taylor series of `x² + y²` at the origin is `X₀² + X₁²`. -/
theorem taylorOrigin_germTop_circleEq :
    taylorOrigin (germTop (circleEq.{u} 0) (ULift.up 0)) = sumSquares := by
  apply Subtype.ext
  change (taylorEquivConv (Kn.{u} ℝ 2) ContinuousLinearEquiv.ulift
    (chartAt (Kn.{u} ℝ 2) (ULift.up 0)) (mem_chart_source _ _) (IsManifold.chart_mem_maximalAtlas _)
      (germTop (circleEq.{u} 0) (ULift.up 0)) : MvPowerSeries (Fin 2) ℝ) = _
  rw [taylorEquivConv_apply_coe, circleEq_germ, map_add, map_mul, map_mul, coe_sumSquares]
  change taylorHom _ _ _ _ _ (coord _ _ _ _ _ 0) * taylorHom _ _ _ _ _ (coord _ _ _ _ _ 0) +
    taylorHom _ _ _ _ _ (coord _ _ _ _ _ 1) * taylorHom _ _ _ _ _ (coord _ _ _ _ _ 1) = _
  rw [taylorHom_coord, taylorHom_coord]
  have h0 : ∀ i : Fin 2, ((ContinuousLinearEquiv.ulift : Kn.{u} ℝ 2 ≃L[ℝ] (Fin 2 → ℝ))
      (chartAt (Kn.{u} ℝ 2) (ULift.up 0) (ULift.up (0 : Fin 2 → ℝ)))) i = 0 := by
    intro i
    rw [chartAt_self_eq]
    rfl
  simp only [h0, map_zero, add_zero]
  ring

/-- The ambient ideal `(x² + y²)` of `𝒜_{ℝ²,0}` is prime. -/
theorem isPrime_ambientIdeal_circleEq :
    (ambientIdeal ℝ 2 ⊤ circleEq.{u} (ULift.up 0)).IsPrime := by
  rw [ambientIdeal_of_mem ℝ 2 ⊤ circleEq (Opens.mem_top _)]
  have hr : (Set.range fun i : Fin 1 =>
      (affine ℝ 2).toLocallyRingedSpace.presheaf.germ ⊤ (ULift.up 0) (Opens.mem_top _)
        (circleEq.{u} i)) = {germTop (circleEq.{u} 0) (ULift.up 0)} := by
    rw [Set.range_unique]
    rfl
  rw [hr]
  have hx : taylorOrigin.{u}.symm sumSquares = germTop (circleEq.{u} 0) (ULift.up 0) := by
    rw [← taylorOrigin_germTop_circleEq, RingEquiv.symm_apply_apply]
  have hmap : (Ideal.map taylorOrigin.{u}.symm (Ideal.span {sumSquares})).IsPrime := by
    have := isPrime_span_sumSquares
    infer_instance
  convert hmap using 1
  rw [Ideal.map_span, Set.image_singleton, hx]

theorem isPrime_ambientIdeal_circleEq_of_eq (q : Kn.{u} ℝ 2) (hq : q = ULift.up 0) :
    (ambientIdeal ℝ 2 ⊤ circleEq.{u} q).IsPrime := by
  subst hq
  exact isPrime_ambientIdeal_circleEq

/-- The stalk ideal of `V(x² + y²)` at its point is prime. -/
theorem isPrime_stalkIdeal_circleEq (z : circleSpace.{u}) :
    (QuotientSpace.stalkIdeal (analyticSpaceOfOpen ℝ 2 ⊤).toLocallyRingedSpace
      (modelIdeal ℝ 2 ⊤ circleEq.{u}) z.1).IsPrime := by
  rw [stalkIdeal_modelIdeal_eq_map]
  have hiso := KLocallyRingedSpace.isIso_ofRestrict_stalkMap (affine.{u} ℝ 2) ⊤ z.1
  have hbij := ConcreteCategory.bijective_of_isIso
    ((KLocallyRingedSpace.ofRestrict (affine.{u} ℝ 2) ⊤).1.stalkMap z.1)
  have hp := isPrime_ambientIdeal_circleEq_of_eq z.1.1 (circleSpace_eq_zero z)
  refine Ideal.map_isPrime_of_surjective (H := hp) hbij.2 ?_
  rw [(RingHom.injective_iff_ker_eq_bot _).mp hbij.1]
  exact bot_le

/-- `V(x² + y²) ⊆ ℝ²` is reduced: the standard example of a reduced real-analytic space whose
simple locus is empty (the phenomenon Hironaka remarks on in [Hir64, Introduction]). -/
theorem circleSpace_isReduced : AnalyticSpace.IsReduced (circleSpace.{u}) := by
  intro z
  have e := QuotientSpace.stalkEquiv (analyticSpaceOfOpen ℝ 2 ⊤).toLocallyRingedSpace
    (modelIdeal ℝ 2 ⊤ circleEq.{u}) z
  have hprime := isPrime_stalkIdeal_circleEq z
  have hdom : IsDomain (QuotientSpace.fiber (analyticSpaceOfOpen ℝ 2 ⊤).toLocallyRingedSpace
      (modelIdeal ℝ 2 ⊤ circleEq.{u}) z) :=
    Ideal.Quotient.isDomain_iff_prime _ |>.mpr hprime
  exact isReduced_of_injective e e.injective

end Hironaka.Space
