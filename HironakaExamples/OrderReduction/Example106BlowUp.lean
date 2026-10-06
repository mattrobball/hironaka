/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import HironakaExamples.BlowUp.Glue.SpecIso
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
public import Hironaka.Scheme.Smooth.Graph
public import HironakaExamples.Balanced.Example106
import Hironaka.Scheme.BlowUp.Composite.Transition
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUp.Transform.TransformIso
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.Remark33Iso
import Hironaka.Scheme.IdealSheaf.Order.AffineSpace
import Hironaka.Scheme.IdealSheaf.Order.Invariance
import Hironaka.Scheme.Smooth.Origin
import HironakaExamples.MaximalContact.Example106Charts
import HironakaExamples.OrderReduction.Example106
import HironakaExamples.Sequence.CosuppForcing
import HironakaExamples.Sequence.Remark33Warning63
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Kollár's Example 106 for the order-reduction functor: the first blow-up

[Kol07, Example 106] continues in the chart `x₁ = x, y₁ = y/x, z₁ = z/x, w₁ = w/x` of the blow-up of
the origin, where the transform is `I₁ = (x₁ − y₁², x₁(x₁ + z₁² − w₁³))` with exceptional divisor
`E₁ = (x₁ = 0)`, and states that "the order has dropped to 1", continuing with `(I₁, 1, E₁)`. That
holds on the `x`-chart Kollár displays but not on the whole blow-up: on the chart `x = x₁z₁`,
`y = y₁z₁`, `z = z₁`, `w = w₁z₁` the transform is `I₁ = (x₁³z₁ − y₁², z₁(x₁⁴z₁ + x₁ − w₁³))`, and
at the origin `q = [0:0:1:0]` of that chart, a point of the exceptional divisor `E₁`, the marked
transform
`(I₁, 2)` still has order exactly `2`. The order-`2` run of `BO_{4,2}(𝔸⁴_ℚ, I, ∅)` therefore does
not stop after the first blow-up. This module computes the order-`2` locus of `I₁` at every scheme
point of the blow-up and derives the second centre by the cosupport forcing of
`HironakaExamples/Sequence/CosuppForcing.lean`: the tail of the sequence after the blow-up of the
origin is an order-`2` sequence for the weak transform `I₁ = π_*^{-1}(I, 2)`, so its first centre is
supported at the order-`2` locus of `I₁`, the single point `q`.

* The blow-up `blowUp 𝔸⁴ (ofIdealTop 𝔪₀)` is identified with the affine model of the blow-up of
  the origin (`HironakaExamples/BlowUp/Glue/SpecIso.lean`), whose four charts `U_a`,
  `a ∈ {x, y, z, w}`, are copies of `Spec ℚ[x, y, z, w]` with the substitutions `σ_a` of
  `HironakaExamples/MaximalContact/Example106Charts.lean` (`chartSubst`; the charts of [Hau14,
  Definition 4.12]).
* On the chart of `a`, `I₁` is the ideal sheaf of the colon `(σ_a I : a²)`, the controlled
  transform of [Kol07, Definition 60] on an affine chart; the identities `σ_a g = a² g'` make it
  Kollár's `I₁` on the `x`-chart and give the `y`-, `z`- and `w`-chart ideals (`chartIdeal_zero`
  to `chartIdeal_three`).
* By the derivative criterion at primes ([Kol07, Lemma 74 (3)]; `le_ord_specIdealSheaf_iff`), the
  order-`2` locus is empty on the `x`-, `y`- and `w`-charts (`D(I₁) = (1)`) and is the origin of
  the `z`-chart (a prime containing `D(I₁)` contains `y₁`, `x₁³`, then `z₁` and `w₁³`), where
  `ord_q I₁ = 2` exactly (`D²(I₁) ∋ ∂²_{y₁}(x₁³z₁ − y₁²) = −2`).
* `q` is the intersection of `E₁` with the strict transform of the `z`-axis `(x = y = w = 0)`, a
  closed point (`mem_modelST_and_EA_iff`, `isClosed_singleton_qA`), and everything is transported
  to the blow-up of `𝔸⁴_ℚ` along the identification (`qB`, `two_le_ord_weakTransform_iff`,
  `ord_weakTransform_qB`).
* `secondCenter_of_axioms`: for any order-`2` sequence with the three properties of the functor's
  values that begins with the blow-up of the origin, the continuation is a blow-up of a centre
  supported at `q`, at which `(I₁, 2)` has order exactly `2`.

The same facts at the `ℚ`-points of the charts are in `Example106Charts.lean`; the order is a
notion at scheme points, so they are proved here at primes, reusing the chart identities. The
later stages are in `HironakaExamples/OrderReduction/Example106Length.lean`.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
  Scheme.IdealSheafData Scheme BlowUpSequence Hironaka.BlowUp IdealSheafData CoordinateSubspace
  affineBlowUpAlgebra Hironaka.Sequence AlgebraicGeometry.Remark33 Hironaka.Examples.Example106
  Hironaka.Examples.Example106Charts

namespace Hironaka.Examples.Example106BO

/-! ### A general helper -/

/-- In a domain, the colon of `(a g₁, a g₂)` by `a ≠ 0` is `(g₁, g₂)`: the controlled transform
of [Kol07, Definition 60] on an affine chart. -/
theorem colon_span_pair_mul {R : Type*} [CommRing R] [IsDomain R] {a g₁ g₂ : R} (ha : a ≠ 0) :
    (Ideal.span {a * g₁, a * g₂}).colon ((Ideal.span {a} : Ideal R) : Set R) =
      Ideal.span {g₁, g₂} := by
  ext f
  rw [Submodule.mem_colon]
  constructor
  · intro h
    have := h a (Ideal.mem_span_singleton_self a)
    rw [smul_eq_mul, Ideal.mem_span_pair] at this
    obtain ⟨u, v, huv⟩ := this
    rw [Ideal.mem_span_pair]
    refine ⟨u, v, mul_left_cancel₀ ha ?_⟩
    linear_combination huv
  · intro h p hp
    rw [SetLike.mem_coe, Ideal.mem_span_singleton] at hp
    obtain ⟨c, rfl⟩ := hp
    rw [Ideal.mem_span_pair] at h
    obtain ⟨u, v, rfl⟩ := h
    rw [smul_eq_mul, Ideal.mem_span_pair]
    exact ⟨u * c, v * c, by ring⟩

/-! ### The model blow-up of the origin of `𝔸⁴_ℚ` -/

/-- `x = X 0` in `ℚ[x, y, z, w]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 4) ℚ)
/-- `y = X 1` in `ℚ[x, y, z, w]`. -/
local notation "y" => (X 1 : MvPolynomial (Fin 4) ℚ)
/-- `z = X 2` in `ℚ[x, y, z, w]`. -/
local notation "z" => (X 2 : MvPolynomial (Fin 4) ℚ)
/-- `w = X 3` in `ℚ[x, y, z, w]`. -/
local notation "w" => (X 3 : MvPolynomial (Fin 4) ℚ)
/-- The coordinate ring `ℚ[x, y, z, w]`. -/
local notation "R4" => MvPolynomial (Fin 4) ℚ
/-- The centre `(x_0, …, x_3)` of the model blow-up of the origin. -/
local notation "c44" => centerIdeal ℚ 4 4
/-- The chart of `x_j` of the model blow-up. -/
local notation "chart" j => modelChart ℚ 4 4 j (Fin.isLt j)
/-- The substitution of the chart of `x_j` (`chartSubst`). -/
local notation "σ" j => chartSubst ℚ (CoordinateSubspace.center 4 4) j

/-- The partial derivative `∂/∂x_i` as a `ℚ`-derivation of `ℚ[x, y, z, w]`. -/
noncomputable abbrev pd (i : Fin 4) : Derivation ℚ R4 R4 := pderiv i

/-- The centre `(x_0, …, x_3)` of the model blow-up is `𝔪₀ = (x, y, z, w)`. -/
theorem centerIdeal_eq_m0 : centerIdeal ℚ 4 4 = m0 := by
  unfold centerIdeal coordinateIdeal
  congr 1
  ext p
  constructor
  · rintro ⟨i, -, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, by simp [CoordinateSubspace.center], rfl⟩
    · exact ⟨1, by simp [CoordinateSubspace.center], rfl⟩
    · exact ⟨2, by simp [CoordinateSubspace.center], rfl⟩
    · exact ⟨3, by simp [CoordinateSubspace.center], rfl⟩

/-- The chart substitution of `x`: `(x, y, z, w) ↦ (x, yx, zx, wx)`. -/
theorem chartSubst_zero_eq :
    (σ 0) = (aeval ![x, y * x, z * x, w * x] : R4 →ₐ[ℚ] R4) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [chartSubst, CoordinateSubspace.center]

/-- The chart substitution of `y`: `(x, y, z, w) ↦ (xy, y, zy, wy)`. -/
theorem chartSubst_one_eq :
    (σ 1) = (aeval ![x * y, y, z * y, w * y] : R4 →ₐ[ℚ] R4) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [chartSubst, CoordinateSubspace.center]

/-- The chart substitution of `z`: `(x, y, z, w) ↦ (xz, yz, z, wz)`. -/
theorem chartSubst_two_eq :
    (σ 2) = (aeval ![x * z, y * z, z, w * z] : R4 →ₐ[ℚ] R4) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [chartSubst, CoordinateSubspace.center]

/-- The chart substitution of `w`: `(x, y, z, w) ↦ (xw, yw, zw, w)`. -/
theorem chartSubst_three_eq :
    (σ 3) = (aeval ![x * w, y * w, z * w, w] : R4 →ₐ[ℚ] R4) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [chartSubst, CoordinateSubspace.center]

/-- On the chart of `x_j` the total transform of `V(P)` is the ideal sheaf of `σ_j P`. -/
theorem comap_comap_modelChart (P : Ideal R4) (j : Fin 4) :
    ((specIdealSheaf P).comap (affineBlowUp.π c44)).comap (chart j) =
      specIdealSheaf (P.map (σ j).toRingHom) := by
  rw [← comap_comp, modelChart_π, comap_specIdealSheaf_Spec_map]

/-- On the chart of `x_j` the exceptional ideal is `(x_j)`. -/
theorem comap_exceptionalIdeal_modelChart' (j : Fin 4) :
    (affineBlowUp.exceptionalIdeal c44).comap (chart j) = specIdealSheaf (Ideal.span {X j}) :=
  comap_exceptionalIdeal_modelChart ℚ 4 4 j j.isLt

/-- The weak transform of `I` on the model blow-up, as the controlled transform of control `2`
([Kol07, Definition 60]; `weakTransform_eq_markedTransform_of_smooth` identifies it with the weak
transform of the blow-up sequences). -/
noncomputable abbrev modelW : (affineBlowUp c44).IdealSheafData :=
  ((specIdealSheaf I106).comap (affineBlowUp.π c44)).colon
    (affineBlowUp.exceptionalIdeal c44 ^ 2)

/-- The controlled transform on the chart of `x_j` is the ideal sheaf of the colon `(σ_j I : x_j²)`
([Kol07, Definition 60] on the chart). -/
theorem comap_modelW_modelChart (j : Fin 4) :
    modelW.comap (chart j) =
      specIdealSheaf ((I106.map (σ j).toRingHom).colon
        ((Ideal.span {(X j : R4)} ^ 2 : Ideal R4) : Set R4)) := by
  have hX : (X j : R4) ∈ nonZeroDivisors R4 := mem_nonZeroDivisors_of_ne_zero (X_ne_zero j)
  have hinv : (specIdealSheaf (Ideal.span {(X j : R4)} ^ 2)).IsInvertible := by
    rw [specIdealSheaf_pow]
    exact isInvertible_pow (isInvertible_specIdealSheaf_span_singleton hX) 2
  rw [modelW, colon_comap_of_flat _ _
      (isInvertible_pow (affineBlowUp.isInvertible_exceptionalIdeal _) 2),
    comap_pow, comap_comap_modelChart, comap_exceptionalIdeal_modelChart', ← specIdealSheaf_pow,
    specIdealSheaf_colon _ _ hinv]

/-! ### The chart ideals of Kollár's `I₁` -/

/-- The image of `I` under a chart substitution `σ`, with the generators rewritten. -/
theorem map_I106_eq (σ' : R4 →ₐ[ℚ] R4) :
    I106.map σ'.toRingHom =
      Ideal.span {σ' (x ^ 3 - y ^ 2), σ' (x ^ 4 + x * z ^ 2 - w ^ 3)} := by
  rw [I106, Ideal.map_span, Set.image_pair]
  rfl

/-- On the `x`-chart, `I₁ = (x₁ − y₁², x₁(x₁ + z₁² − w₁³))`, as printed in [Kol07, Example 106]. -/
theorem chartIdeal_zero :
    (I106.map (σ 0).toRingHom).colon ((Ideal.span {x} ^ 2 : Ideal R4) : Set R4) =
      Ideal.span {x - y ^ 2, x * (x + z ^ 2 - w ^ 3)} := by
  rw [map_I106_eq, chartSubst_zero_eq, transform_example106_x.1, transform_example106_x.2.1,
    Ideal.span_singleton_pow]
  exact colon_span_pair_mul (pow_ne_zero 2 (X_ne_zero 0))

/-- On the `y`-chart, `I₁ = (x₁³y₁ − 1, y₁(x₁⁴y₁ + x₁z₁² − w₁³))`. -/
theorem chartIdeal_one :
    (I106.map (σ 1).toRingHom).colon ((Ideal.span {y} ^ 2 : Ideal R4) : Set R4) =
      Ideal.span {x ^ 3 * y - 1, y * (x ^ 4 * y + x * z ^ 2 - w ^ 3)} := by
  rw [map_I106_eq, chartSubst_one_eq, transform_example106_y.1, transform_example106_y.2,
    Ideal.span_singleton_pow]
  exact colon_span_pair_mul (pow_ne_zero 2 (X_ne_zero 1))

/-- On the `z`-chart, `I₁ = (x₁³z₁ − y₁², z₁(x₁⁴z₁ + x₁ − w₁³))`, the chart not displayed in
[Kol07, Example 106]. -/
theorem chartIdeal_two :
    (I106.map (σ 2).toRingHom).colon ((Ideal.span {z} ^ 2 : Ideal R4) : Set R4) =
      Ideal.span {x ^ 3 * z - y ^ 2, z * (x ^ 4 * z + x - w ^ 3)} := by
  rw [map_I106_eq, chartSubst_two_eq, transform_example106_z.1, transform_example106_z.2.1,
    Ideal.span_singleton_pow]
  exact colon_span_pair_mul (pow_ne_zero 2 (X_ne_zero 2))

/-- On the `w`-chart, `I₁ = (x₁³w₁ − y₁², w₁(x₁⁴w₁ + x₁z₁² − 1))`. -/
theorem chartIdeal_three :
    (I106.map (σ 3).toRingHom).colon ((Ideal.span {w} ^ 2 : Ideal R4) : Set R4) =
      Ideal.span {x ^ 3 * w - y ^ 2, w * (x ^ 4 * w + x * z ^ 2 - 1)} := by
  rw [map_I106_eq, chartSubst_three_eq, transform_example106_w.1, transform_example106_w.2,
    Ideal.span_singleton_pow]
  exact colon_span_pair_mul (pow_ne_zero 2 (X_ne_zero 3))

/-! ### The order-2 locus on each chart, at every prime -/

/-- On the `x`-chart the order has dropped to `1` at every point, as [Kol07, Example 106] says:
`D(I₁) ∋ ∂_{x₁}(x₁ − y₁²) = 1`, so no prime contains `D(I₁)`. -/
theorem not_le_derivative_zero (p : Ideal R4) [hp : p.IsPrime] :
    ¬ Ideal.derivative ℚ (Ideal.span {x - y ^ 2, x * (x + z ^ 2 - w ^ 3)}) ≤ p := by
  intro h
  have e : pd 0 (x - y ^ 2) = 1 := by simp
  have h1 := Ideal.derivation_apply_mem_derivative (pd 0)
    (Ideal.subset_span (by simp) : x - y ^ 2 ∈ Ideal.span {x - y ^ 2, x * (x + z ^ 2 - w ^ 3)})
  rw [e] at h1
  exact hp.ne_top ((Ideal.eq_top_iff_one _).mpr (h h1))

/-- The `y`-chart has no point of order `2`: `x₁³y₁ − 1 ∈ I₁` and `∂_{y₁}(x₁³y₁ − 1) = x₁³ ∈ D(I₁)`,
so `1 ∈ D(I₁)`. -/
theorem not_le_derivative_one (p : Ideal R4) [hp : p.IsPrime] :
    ¬ Ideal.derivative ℚ (Ideal.span {x ^ 3 * y - 1, y * (x ^ 4 * y + x * z ^ 2 - w ^ 3)}) ≤ p := by
  intro h
  set K := Ideal.span {x ^ 3 * y - 1, y * (x ^ 4 * y + x * z ^ 2 - w ^ 3)} with hK
  have hg : x ^ 3 * y - 1 ∈ Ideal.derivative ℚ K :=
    Ideal.le_derivative K (Ideal.subset_span (by simp))
  have e : pd 1 (x ^ 3 * y - 1) = x ^ 3 := by simp
  have h1 := Ideal.derivation_apply_mem_derivative (pd 1)
    (Ideal.subset_span (by simp) : x ^ 3 * y - 1 ∈ K)
  rw [e] at h1
  have hone : (1 : R4) ∈ Ideal.derivative ℚ K := by
    have : (1 : R4) = x ^ 3 * y - (x ^ 3 * y - 1) := by ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ h1) hg
  exact hp.ne_top ((Ideal.eq_top_iff_one _).mpr (h hone))

/-- The `w`-chart has no point of order `2`: a prime containing `D(I₁)` contains
`∂_{w₁}(x₁³w₁ − y₁²) = x₁³`, hence `x₁`, and `∂_{w₁}(w₁(x₁⁴w₁ + x₁z₁² − 1)) = 2x₁⁴w₁ + x₁z₁² − 1`,
hence `1`. -/
theorem not_le_derivative_three (p : Ideal R4) [hp : p.IsPrime] :
    ¬ Ideal.derivative ℚ (Ideal.span {x ^ 3 * w - y ^ 2, w * (x ^ 4 * w + x * z ^ 2 - 1)}) ≤ p := by
  intro h
  set K := Ideal.span {x ^ 3 * w - y ^ 2, w * (x ^ 4 * w + x * z ^ 2 - 1)} with hK
  have e1 : pd 3 (x ^ 3 * w - y ^ 2) = x ^ 3 := by simp
  have e2 : pd 3 (w * (x ^ 4 * w + x * z ^ 2 - 1)) = 2 * x ^ 4 * w + x * z ^ 2 - 1 := by
    simp
    ring
  have h1 := Ideal.derivation_apply_mem_derivative (pd 3)
    (Ideal.subset_span (by simp) : x ^ 3 * w - y ^ 2 ∈ K)
  have h2 := Ideal.derivation_apply_mem_derivative (pd 3)
    (Ideal.subset_span (by simp) : w * (x ^ 4 * w + x * z ^ 2 - 1) ∈ K)
  rw [e1] at h1
  rw [e2] at h2
  have hx : x ∈ p := hp.mem_of_pow_mem 3 (h h1)
  have hone : (1 : R4) ∈ p := by
    have : (1 : R4) = x * (2 * x ^ 3 * w + z ^ 2) - (2 * x ^ 4 * w + x * z ^ 2 - 1) := by ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hx) (h h2)
  exact hp.ne_top ((Ideal.eq_top_iff_one _).mpr hone)

/-- On the `z`-chart a prime contains `D(I₁)` iff it is the origin `q = [0:0:1:0]`: from
`∂_{y₁}(x₁³z₁ − y₁²) = −2y₁`, `∂_{z₁}(x₁³z₁ − y₁²) = x₁³`,
`∂_{x₁}(z₁(x₁⁴z₁ + x₁ − w₁³)) = 4x₁³z₁² + z₁` and `∂_{z₁}(z₁(x₁⁴z₁ + x₁ − w₁³)) = 2x₁⁴z₁ + x₁ − w₁³`
a prime containing `D(I₁)` contains `y₁, x₁, z₁, w₁`; conversely `I₁ ⊆ 𝔪_q²`
(`ord_zero_example106_z`) gives `D(I₁) ⊆ 𝔪_q`. -/
theorem le_derivative_two_iff (p : Spec (CommRingCat.of R4)) :
    Ideal.derivative ℚ (Ideal.span {x ^ 3 * z - y ^ 2, z * (x ^ 4 * z + x - w ^ 3)}) ≤ p.asIdeal ↔
      p = origin ℚ 4 := by
  set K := Ideal.span {x ^ 3 * z - y ^ 2, z * (x ^ 4 * z + x - w ^ 3)} with hK
  have hp : p.asIdeal.IsPrime := p.isPrime
  constructor
  · intro h
    have e1 : pd 1 (x ^ 3 * z - y ^ 2) = -(C 2 * y) := by simp [map_ofNat]
    have e2 : pd 2 (x ^ 3 * z - y ^ 2) = x ^ 3 := by simp
    have e3 : pd 0 (z * (x ^ 4 * z + x - w ^ 3)) = 4 * x ^ 3 * z ^ 2 + z := by
      simp
      ring
    have e4 : pd 2 (z * (x ^ 4 * z + x - w ^ 3)) = 2 * x ^ 4 * z + x - w ^ 3 := by
      simp
      ring
    have hg1 : x ^ 3 * z - y ^ 2 ∈ K := Ideal.subset_span (by simp)
    have hg2 : z * (x ^ 4 * z + x - w ^ 3) ∈ K := Ideal.subset_span (by simp)
    have h1 := h (Ideal.derivation_apply_mem_derivative (pd 1) hg1)
    have h2 := h (Ideal.derivation_apply_mem_derivative (pd 2) hg1)
    have h3 := h (Ideal.derivation_apply_mem_derivative (pd 0) hg2)
    have h4 := h (Ideal.derivation_apply_mem_derivative (pd 2) hg2)
    rw [e1] at h1
    rw [e2] at h2
    rw [e3] at h3
    rw [e4] at h4
    have hy : y ∈ p.asIdeal := by
      have : y = C (1 / 2 : ℚ) * -(-(C 2 * y)) := by
        rw [neg_neg, ← mul_assoc, ← C_mul]; norm_num
      rw [this]
      exact Ideal.mul_mem_left _ _ ((Ideal.neg_mem_iff _).mpr h1)
    have hx : x ∈ p.asIdeal := hp.mem_of_pow_mem 3 h2
    have hz : z ∈ p.asIdeal := by
      have : z = (4 * x ^ 3 * z ^ 2 + z) - x * (4 * x ^ 2 * z ^ 2) := by ring
      rw [this]
      exact Ideal.sub_mem _ h3 (Ideal.mul_mem_right _ _ hx)
    have hw : w ∈ p.asIdeal := by
      have : w ^ 3 = x * (2 * x ^ 3 * z + 1) - (2 * x ^ 4 * z + x - w ^ 3) := by ring
      exact hp.mem_of_pow_mem 3 (this ▸ Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hx) h4)
    rw [eq_origin_iff_forall_X_mem]
    intro i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
    · exact hw
  · rintro rfl
    have hle : K ≤ m0 ^ (1 + 1) := ord_zero_example106_z.1
    have := Ideal.derivative_le_pow (k := ℚ) hle
    rwa [pow_one, m0_eq_origin_asIdeal] at this

/-- `ord_q I₁` is not more than `2`: `1 ∈ D²(I₁)` on the `z`-chart, from
`∂²_{y₁}(x₁³z₁ − y₁²) = −2`. -/
theorem one_mem_derivativeIter_two_chart_two :
    (1 : R4) ∈ Ideal.derivativeIter ℚ 2
      (Ideal.span {x ^ 3 * z - y ^ 2, z * (x ^ 4 * z + x - w ^ 3)}) := by
  set K := Ideal.span {x ^ 3 * z - y ^ 2, z * (x ^ 4 * z + x - w ^ 3)} with hK
  have e1 : pd 1 (x ^ 3 * z - y ^ 2) = -(C 2 * y) := by simp [map_ofNat]
  have e2 : pd 1 (-(C 2 * y)) = -(C 2) := by simp
  have h1 := Ideal.derivation_apply_mem_derivative (pd 1)
    (Ideal.subset_span (by simp) : x ^ 3 * z - y ^ 2 ∈ K)
  rw [e1] at h1
  have h2 := Ideal.derivation_apply_mem_derivative (pd 1) h1
  rw [e2] at h2
  have : (1 : R4) = C (-1 / 2 : ℚ) * -(C 2) := by
    rw [← C_neg, ← C_mul]; norm_num
  rw [show (2 : ℕ) = 1 + 1 from rfl, Ideal.derivativeIter_succ, Ideal.derivativeIter_succ,
    Ideal.derivativeIter_zero, this]
  exact Ideal.mul_mem_left _ _ h2

/-! ### The order-2 locus of `I₁` on the model blow-up -/

/-- The four cases of an index of `Fin 4`. -/
theorem fin4_cases (j : Fin 4) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide +revert

/-- `D^{2−1} = D` at the ring level, for the derivative criterion. -/
theorem derivativeIter_two_sub_one (K : Ideal R4) :
    Ideal.derivativeIter ℚ (2 - 1) K = Ideal.derivative ℚ K := by
  rw [show (2 : ℕ) - 1 = 0 + 1 from rfl, Ideal.derivativeIter_succ, Ideal.derivativeIter_zero]

/-- Off the `z`-chart no scheme point of the blow-up has `ord I₁ ≥ 2`. -/
theorem not_two_le_ord_modelW_chart (j : Fin 4) (hj : j ≠ 2) (p : Spec (CommRingCat.of R4)) :
    ¬ ((2 : ℕ) : ℕ∞) ≤ (modelW.comap (chart j)).ord p := by
  rw [comap_modelW_modelChart, le_ord_specIdealSheaf_iff _ p one_le_two, derivativeIter_two_sub_one]
  have hp : p.asIdeal.IsPrime := p.isPrime
  rcases fin4_cases j with rfl | rfl | rfl | rfl
  · rw [chartIdeal_zero]
    exact not_le_derivative_zero p.asIdeal
  · rw [chartIdeal_one]
    exact not_le_derivative_one p.asIdeal
  · exact absurd rfl hj
  · rw [chartIdeal_three]
    exact not_le_derivative_three p.asIdeal

/-- On the `z`-chart the order-`2` locus of `I₁` is the origin `q = [0:0:1:0]`, at every scheme
point. -/
theorem two_le_ord_modelW_chart_two_iff (p : Spec (CommRingCat.of R4)) :
    ((2 : ℕ) : ℕ∞) ≤ (modelW.comap (chart 2)).ord p ↔ p = origin ℚ 4 := by
  rw [comap_modelW_modelChart, le_ord_specIdealSheaf_iff _ p one_le_two,
    derivativeIter_two_sub_one, chartIdeal_two, le_derivative_two_iff]

/-- The order of `I₁` at `q` is not `≥ 3`. -/
theorem not_three_le_ord_modelW_chart_two :
    ¬ ((3 : ℕ) : ℕ∞) ≤ (modelW.comap (chart 2)).ord (origin ℚ 4) := by
  rw [comap_modelW_modelChart, le_ord_specIdealSheaf_iff _ _ (by norm_num), chartIdeal_two]
  intro h
  exact (origin ℚ 4).isPrime.ne_top
    ((Ideal.eq_top_iff_one _).mpr (h one_mem_derivativeIter_two_chart_two))

/-- Every point of the model blow-up lies on one of the four charts. -/
theorem exists_modelChart_eq (b : affineBlowUp c44) :
    ∃ (j : Fin 4) (p : Spec (CommRingCat.of R4)), (chart j) p = b := by
  have hb : b ∈ (⊤ : (affineBlowUp c44).Opens) := trivial
  rw [← iSup_opensRange_modelChart ℚ 4 4] at hb
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hb
  obtain ⟨hj', hp⟩ := Opens.mem_iSup.mp hj
  obtain ⟨p, hp⟩ := Scheme.Hom.mem_opensRange.mp hp
  exact ⟨j, p, hp⟩

/-- Kollár's point `q = [0:0:1:0] ∈ E₁`, the origin of the `z`-chart, on the model blow-up. -/
noncomputable abbrev qA : affineBlowUp c44 := (chart 2) (origin ℚ 4)

/-- `ord_q I₁ ≥ 2` on the model blow-up. -/
theorem two_le_ord_modelW_qA : ((2 : ℕ) : ℕ∞) ≤ modelW.ord qA := by
  rw [qA, ← ord_comap_of_isOpenImmersion modelW (chart 2) (origin ℚ 4)]
  exact (two_le_ord_modelW_chart_two_iff _).mpr rfl

/-- `ord_q I₁ = 2` on the model blow-up. -/
theorem ord_modelW_qA : modelW.ord qA = ((2 : ℕ) : ℕ∞) := by
  refine le_antisymm ?_ two_le_ord_modelW_qA
  have h3 : ¬ ((3 : ℕ) : ℕ∞) ≤ modelW.ord qA := by
    rw [qA, ← ord_comap_of_isOpenImmersion modelW (chart 2) (origin ℚ 4)]
    exact not_three_le_ord_modelW_chart_two
  have h3' : modelW.ord qA < ((2 : ℕ) : ℕ∞) + 1 := by exact_mod_cast not_le.mp h3
  exact (ENat.lt_add_one_iff (by simp)).mp h3'

/-- On the model blow-up the order-`2` locus of `I₁` is the single point `q`, at every scheme
point. -/
theorem two_le_ord_modelW_iff (b : affineBlowUp c44) :
    ((2 : ℕ) : ℕ∞) ≤ modelW.ord b ↔ b = qA := by
  constructor
  · intro h
    obtain ⟨j, p, rfl⟩ := exists_modelChart_eq b
    rw [← ord_comap_of_isOpenImmersion modelW (chart j) p] at h
    rcases fin4_cases j with rfl | rfl | rfl | rfl
    · exact absurd h (not_two_le_ord_modelW_chart 0 (by decide) p)
    · exact absurd h (not_two_le_ord_modelW_chart 1 (by decide) p)
    · rw [(two_le_ord_modelW_chart_two_iff p).mp h]
    · exact absurd h (not_two_le_ord_modelW_chart 3 (by decide) p)
  · rintro rfl
    exact two_le_ord_modelW_qA

/-! ### The strict transform of the `z`-axis meets `E₁` at `q` -/

/-- The exceptional divisor of the model blow-up. -/
local notation "EA" => affineBlowUp.exceptionalIdeal (centerIdeal ℚ 4 4)

/-- The `z`-axis `(x = y = w = 0) ⊆ 𝔸⁴`. -/
noncomputable abbrev zAxisIdeal : Ideal R4 := Ideal.span {x, y, w}

/-- The strict transform of the `z`-axis `(x = y = w = 0)` on the model blow-up. -/
noncomputable abbrev modelST : (affineBlowUp c44).IdealSheafData :=
  ((specIdealSheaf zAxisIdeal).comap (affineBlowUp.π c44)).saturate EA

/-- The strict transform of the `z`-axis on the chart of `x_j`. -/
theorem comap_modelST_modelChart (j : Fin 4) :
    modelST.comap (chart j) =
      (specIdealSheaf (zAxisIdeal.map (σ j).toRingHom)).saturate
        (specIdealSheaf (Ideal.span {(X j : R4)})) := by
  rw [modelST, saturate_comap_of_flat _ _ (affineBlowUp.isInvertible_exceptionalIdeal _),
    comap_comap_modelChart, comap_exceptionalIdeal_modelChart']

/-- The `z`-axis is prime: `ℚ[x, y, z, w]/(x, y, w) ≅ ℚ[z]`. -/
theorem isPrime_span_xyw : (Ideal.span {x, y, w} : Ideal R4).IsPrime := by
  have heq : (Ideal.span {x, y, w} : Ideal R4) = coordinateIdeal ℚ {i : Fin 4 | ¬ i = 2} := by
    unfold coordinateIdeal
    congr 1
    ext p
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by decide, rfl⟩
      · exact ⟨1, by decide, rfl⟩
      · exact ⟨3, by decide, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all
  rw [heq, ← Ideal.Quotient.isDomain_iff_prime]
  exact MulEquiv.isDomain _
    (quotientCoordinateIdealAlgEquiv ℚ (fun i : Fin 4 => i = 2)).toRingEquiv.toMulEquiv

/-- `z ∉ (x, y, w)`: evaluate at `(0, 0, 1, 0)`. -/
theorem z_notMem_span_xyw : z ∉ (Ideal.span {x, y, w} : Ideal R4) := by
  intro hz
  have hle : (Ideal.span {x, y, w} : Ideal R4) ≤
      RingHom.ker (aeval (fun i : Fin 4 => if i = 2 then (1 : ℚ) else 0) : R4 →ₐ[ℚ] ℚ) := by
    rw [Ideal.span_le]
    rintro g (rfl | rfl | rfl) <;> simp [RingHom.mem_ker]
  have := hle hz
  simp [RingHom.mem_ker] at this

/-- `σ_z` on the generators of the `z`-axis: `σ_z x = xz`. -/
theorem chartSubst_two_X_zero : (σ 2) x = x * z :=
  chartSubst_X_of_mem ℚ _ _ (by decide) (by decide)
/-- `σ_z y = yz`. -/
theorem chartSubst_two_X_one : (σ 2) y = y * z :=
  chartSubst_X_of_mem ℚ _ _ (by decide) (by decide)
/-- `σ_z w = wz`. -/
theorem chartSubst_two_X_three : (σ 2) w = w * z :=
  chartSubst_X_of_mem ℚ _ _ (by decide) (by decide)

/-- On the `z`-chart the total transform of the `z`-axis is contained in `(x₁, y₁, w₁)`. -/
theorem map_zAxis_two_le : zAxisIdeal.map (σ 2).toRingHom ≤ Ideal.span {x, y, w} := by
  rw [Ideal.map_le_iff_le_comap, zAxisIdeal, Ideal.span_le]
  rintro g (rfl | rfl | rfl)
  · rw [SetLike.mem_coe, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      chartSubst_two_X_zero]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · rw [SetLike.mem_coe, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      chartSubst_two_X_one]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · rw [SetLike.mem_coe, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      chartSubst_two_X_three]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

/-- On the `z`-chart, `x₁z₁`, `y₁z₁` and `w₁z₁` lie in the total transform of the `z`-axis. -/
theorem mul_X_two_mem_map_zAxis (i : Fin 4) (hi : i ≠ 2) :
    (X i : R4) * z ∈ zAxisIdeal.map (σ 2).toRingHom := by
  have hmem : (X i : R4) ∈ zAxisIdeal := by
    rcases fin4_cases i with rfl | rfl | rfl | rfl
    · exact Ideal.subset_span (by simp)
    · exact Ideal.subset_span (by simp)
    · exact absurd rfl hi
    · exact Ideal.subset_span (by simp)
  have := Ideal.mem_map_of_mem (σ 2).toRingHom hmem
  rwa [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    chartSubst_X_of_mem ℚ _ _ (by exact i.isLt) hi] at this

/-- Off the `z`-chart the total transform of the `z`-axis contains the exceptional generator. -/
theorem X_mem_map_zAxis (j : Fin 4) (hj : j ≠ 2) : (X j : R4) ∈ zAxisIdeal.map (σ j).toRingHom := by
  have hmem : (X j : R4) ∈ zAxisIdeal := by
    rcases fin4_cases j with rfl | rfl | rfl | rfl
    · exact Ideal.subset_span (by simp)
    · exact Ideal.subset_span (by simp)
    · exact absurd rfl hj
    · exact Ideal.subset_span (by simp)
  have := Ideal.mem_map_of_mem (σ j).toRingHom hmem
  rwa [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, chartSubst_X_self] at this

/-- Kollár's `q = [0:0:1:0]` is the intersection of `E₁` with the strict transform of the `z`-axis,
at every scheme point of the model blow-up: a point lies on both iff it is `q`. -/
theorem mem_modelST_and_EA_iff (b : affineBlowUp c44) :
    b ∈ modelST.support ∧ b ∈ (EA).support ↔ b = qA := by
  have hXz : (specIdealSheaf (Ideal.span {z})).IsInvertible :=
    isInvertible_specIdealSheaf_span_singleton (mem_nonZeroDivisors_of_ne_zero (X_ne_zero 2))
  constructor
  · rintro ⟨hS, hE⟩
    obtain ⟨j, p, rfl⟩ := exists_modelChart_eq b
    rw [← mem_support_comap_iff_apply, comap_exceptionalIdeal_modelChart',
      mem_support_specIdealSheaf_iff] at hE
    rw [← mem_support_comap_iff_apply, comap_modelST_modelChart] at hS
    have hXj : (specIdealSheaf (Ideal.span {(X j : R4)})).IsInvertible :=
      isInvertible_specIdealSheaf_span_singleton (mem_nonZeroDivisors_of_ne_zero (X_ne_zero j))
    have hcol : p ∈ ((specIdealSheaf (zAxisIdeal.map (σ j).toRingHom)).colon
        (specIdealSheaf (Ideal.span {(X j : R4)}))).support := by
      have hle := colon_pow_le_saturate (specIdealSheaf (zAxisIdeal.map (σ j).toRingHom))
        (specIdealSheaf (Ideal.span {(X j : R4)})) 1
      rw [pow_one] at hle
      exact support_antitone hle hS
    rw [specIdealSheaf_colon _ _ hXj, mem_support_specIdealSheaf_iff] at hcol
    have hp : p.asIdeal.IsPrime := p.isPrime
    rcases fin4_cases j with rfl | rfl | rfl | rfl
    · exfalso
      refine hp.ne_top ((Ideal.eq_top_iff_one _).mpr (hcol ?_))
      rw [Submodule.mem_colon]
      intro g hg
      rw [SetLike.mem_coe, Ideal.mem_span_singleton] at hg
      obtain ⟨c, rfl⟩ := hg
      rw [one_smul]
      exact Ideal.mul_mem_right _ _ (X_mem_map_zAxis 0 (by decide))
    · exfalso
      refine hp.ne_top ((Ideal.eq_top_iff_one _).mpr (hcol ?_))
      rw [Submodule.mem_colon]
      intro g hg
      rw [SetLike.mem_coe, Ideal.mem_span_singleton] at hg
      obtain ⟨c, rfl⟩ := hg
      rw [one_smul]
      exact Ideal.mul_mem_right _ _ (X_mem_map_zAxis 1 (by decide))
    · have hmem : ∀ i : Fin 4, i ≠ 2 → (X i : R4) ∈ p.asIdeal := by
        intro i hi
        refine hcol ?_
        rw [Submodule.mem_colon]
        intro g hg
        rw [SetLike.mem_coe, Ideal.mem_span_singleton] at hg
        obtain ⟨c, rfl⟩ := hg
        rw [smul_eq_mul, ← mul_assoc]
        exact Ideal.mul_mem_right _ _ (mul_X_two_mem_map_zAxis i hi)
      have hz : z ∈ p.asIdeal := hE (Ideal.mem_span_singleton_self _)
      have hp0 : p = origin ℚ 4 := by
        rw [eq_origin_iff_forall_X_mem]
        intro i
        by_cases hi : i = 2
        · rw [hi]; exact hz
        · exact hmem i hi
      rw [hp0]
    · exfalso
      refine hp.ne_top ((Ideal.eq_top_iff_one _).mpr (hcol ?_))
      rw [Submodule.mem_colon]
      intro g hg
      rw [SetLike.mem_coe, Ideal.mem_span_singleton] at hg
      obtain ⟨c, rfl⟩ := hg
      rw [one_smul]
      exact Ideal.mul_mem_right _ _ (X_mem_map_zAxis 3 (by decide))
  · rintro rfl
    constructor
    · rw [qA, ← mem_support_comap_iff_apply, comap_modelST_modelChart,
        Scheme.IdealSheafData.saturate, support_iSup, Closeds.mem_iInf]
      intro i
      have hinv : (specIdealSheaf (Ideal.span {z} ^ i)).IsInvertible := by
        rw [specIdealSheaf_pow]
        exact isInvertible_pow hXz i
      rw [← specIdealSheaf_pow, specIdealSheaf_colon _ _ hinv, mem_support_specIdealSheaf_iff]
      intro f hf
      rw [Submodule.mem_colon] at hf
      have hzi : z ^ i ∈ ((Ideal.span {z} ^ i : Ideal R4) : Set R4) :=
        Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) i
      have hfz : f * z ^ i ∈ Ideal.span {x, y, w} :=
        map_zAxis_two_le (by simpa [smul_eq_mul] using hf (z ^ i) hzi)
      have hf' : f ∈ Ideal.span {x, y, w} := by
        rcases isPrime_span_xyw.mem_or_mem hfz with h | h
        · exact h
        · exact absurd (isPrime_span_xyw.mem_of_pow_mem i h) z_notMem_span_xyw
      refine (Ideal.span_le.mpr ?_) hf'
      rintro g (rfl | rfl | rfl) <;> exact X_mem_origin_asIdeal ℚ 4 _
    · rw [qA, ← mem_support_comap_iff_apply, comap_exceptionalIdeal_modelChart',
        mem_support_specIdealSheaf_iff, Ideal.span_le]
      rintro g rfl
      exact X_mem_origin_asIdeal ℚ 4 _

/-- `q` is a closed point of the model blow-up: the intersection of two closed sets. -/
theorem isClosed_singleton_qA : IsClosed ({qA} : Set (affineBlowUp c44)) := by
  have : ({qA} : Set (affineBlowUp c44)) =
      ((modelST.support ⊓ (EA).support : Closeds _) : Set _) := by
    ext b
    rw [Set.mem_singleton_iff, Closeds.coe_inf, Set.mem_inter_iff, SetLike.mem_coe,
      SetLike.mem_coe]
    exact (mem_modelST_and_EA_iff b).symm
  rw [this]
  exact Closeds.isClosed _

/-! ### Transport to the blow-up of record -/

/-- The identification of the blow-up of `𝔸⁴_ℚ` at the origin with the model blow-up. -/
local notation "Φ" => blowUpSpecIso (centerIdeal ℚ 4 4)
/-- The blow-up of `𝔸⁴_ℚ` along `ofIdealTop 𝔪₀` (as `centerIdeal ℚ 4 4`). -/
local notation "𝔹ᵣ" => Scheme.IdealSheafData.blowUp (specIdealSheaf (centerIdeal ℚ 4 4))

/-- The identification `Φ` is a bijection on points (inverse then hom). -/
theorem inv_hom_apply (b : 𝔹ᵣ) : (Φ).inv ((Φ).hom b) = b := by
  rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

/-- The identification `Φ` is a bijection on points (hom then inverse). -/
theorem hom_inv_apply (a : affineBlowUp c44) : (Φ).hom ((Φ).inv a) = a := by
  rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  rfl

/-- The exceptional divisor of the blow-up transports to the model's. -/
theorem comap_exceptionalDivisor_inv :
    (specIdealSheaf c44).exceptionalDivisor.comap (Φ).inv = EA :=
  comap_comap_blowUpSpecIso_inv _ _

/-- The weak transform of `I`, which is its marked transform `π_*^{-1}(I, 2)` since `ord_0 I = 2`
([Kol07, 58] against [Kol07, Definition 60]; `weakTransform_eq_markedTransform_of_smooth`),
transports to `modelW`. -/
theorem comap_weakTransform_inv
    [Smooth ((specIdealSheaf c44).subschemeι ≫ affineSpaceToSpec ℚ 4)]
    (hord : (specIdealSheaf I106).OrdAlongEq (specIdealSheaf c44).support ((2 : ℕ) : ℕ∞)) :
    ((specIdealSheaf I106).weakTransform (specIdealSheaf c44)).comap (Φ).inv = modelW := by
  have := smoothOfRelativeDimension_affineSpaceToSpec
  rw [weakTransform_eq_markedTransform_of_smooth (affineSpaceToSpec ℚ 4) 4 (specIdealSheaf c44)
      (specIdealSheaf I106) hord, markedTransform_eq_colon, comap_colon_of_isIso, comap_pow,
    comap_comap_blowUpSpecIso_inv, comap_exceptionalDivisor_inv]

/-- The strict transform of the `z`-axis transports to the model's. -/
theorem comap_strictTransform_inv :
    ((specIdealSheaf zAxisIdeal).strictTransform (specIdealSheaf c44)).comap (Φ).inv = modelST := by
  change (((specIdealSheaf zAxisIdeal).strictTransformAlong (specIdealSheaf c44).blowUpπ
      (specIdealSheaf c44).exceptionalDivisor)).comap (Φ).inv = _
  rw [strictTransformAlong, comap_saturate_of_isIso, comap_comap_blowUpSpecIso_inv,
    comap_exceptionalDivisor_inv]

/-- Kollár's point `q` on the blow-up of `𝔸⁴_ℚ`. -/
noncomputable abbrev qB : 𝔹ᵣ := (Φ).inv qA

/-- The order of `I₁` at a point of the blow-up is the order of `modelW` at its image under `Φ`. -/
theorem ord_weakTransform_eq
    [Smooth ((specIdealSheaf c44).subschemeι ≫ affineSpaceToSpec ℚ 4)]
    (hord : (specIdealSheaf I106).OrdAlongEq (specIdealSheaf c44).support ((2 : ℕ) : ℕ∞))
    (b : 𝔹ᵣ) :
    ((specIdealSheaf I106).weakTransform (specIdealSheaf c44)).ord b = modelW.ord ((Φ).hom b) := by
  rw [← comap_weakTransform_inv hord, ord_comap_of_isIso, inv_hom_apply]

/-- On the blow-up of `𝔸⁴_ℚ` the order-`2` locus of `I₁` is the single point `q`, at every scheme
point; it lies off the `x`-chart displayed in [Kol07, Example 106]. -/
theorem two_le_ord_weakTransform_iff
    [Smooth ((specIdealSheaf c44).subschemeι ≫ affineSpaceToSpec ℚ 4)]
    (hord : (specIdealSheaf I106).OrdAlongEq (specIdealSheaf c44).support ((2 : ℕ) : ℕ∞))
    (b : 𝔹ᵣ) :
    ((2 : ℕ) : ℕ∞) ≤ ((specIdealSheaf I106).weakTransform (specIdealSheaf c44)).ord b ↔ b = qB := by
  rw [ord_weakTransform_eq hord, two_le_ord_modelW_iff]
  constructor
  · intro h
    rw [← inv_hom_apply b, h]
  · intro h
    rw [h, qB, hom_inv_apply]

/-- `ord_q I₁ = 2` on the blow-up of `𝔸⁴_ℚ`. -/
theorem ord_weakTransform_qB
    [Smooth ((specIdealSheaf c44).subschemeι ≫ affineSpaceToSpec ℚ 4)]
    (hord : (specIdealSheaf I106).OrdAlongEq (specIdealSheaf c44).support ((2 : ℕ) : ℕ∞)) :
    ((specIdealSheaf I106).weakTransform (specIdealSheaf c44)).ord qB = ((2 : ℕ) : ℕ∞) := by
  rw [ord_weakTransform_eq hord, qB, hom_inv_apply, ord_modelW_qA]

/-- Membership in a support on the blow-up, read on the model through `Φ`. -/
theorem mem_support_iff_hom (K : (𝔹ᵣ).IdealSheafData) (b : 𝔹ᵣ) :
    b ∈ K.support ↔ (Φ).hom b ∈ (K.comap (Φ).inv).support := by
  rw [mem_support_comap_iff_apply, inv_hom_apply]

/-- On the blow-up of `𝔸⁴_ℚ`, `q` is the intersection of `E₁` with the strict transform of the
`z`-axis, at every scheme point. -/
theorem mem_strictTransform_and_exceptional_iff (b : 𝔹ᵣ) :
    b ∈ ((specIdealSheaf zAxisIdeal).strictTransform (specIdealSheaf c44)).support ∧
      b ∈ (specIdealSheaf c44).exceptionalDivisor.support ↔
        b = qB := by
  rw [mem_support_iff_hom, mem_support_iff_hom, comap_strictTransform_inv,
    comap_exceptionalDivisor_inv, mem_modelST_and_EA_iff]
  constructor
  · intro h
    rw [← inv_hom_apply b, h]
  · intro h
    rw [h, qB, hom_inv_apply]

/-- `q` is a closed point of the blow-up. -/
theorem isClosed_singleton_qB : IsClosed ({qB} : Set 𝔹ᵣ) := by
  have : ({qB} : Set 𝔹ᵣ) =
      ((((specIdealSheaf zAxisIdeal).strictTransform (specIdealSheaf c44)).support ⊓
        (specIdealSheaf c44).exceptionalDivisor.support : Closeds _) :
          Set _) := by
    ext b
    rw [Set.mem_singleton_iff, Closeds.coe_inf, Set.mem_inter_iff, SetLike.mem_coe,
      SetLike.mem_coe]
    exact (mem_strictTransform_and_exceptional_iff b).symm
  rw [this]
  exact Closeds.isClosed _

/-! ### The second centre -/

/-- **The second centre** ([Kol07, Example 106], continued beyond the displayed chart): for a
smooth blow-up sequence of order `2` for `(𝔸⁴_ℚ, I, E)` that begins with the blow-up of the origin,
has no empty centre and ends with maximal order `< 2`, the continuation after the first blow-up is
again a blow-up, of a centre supported at the single point `q = [0:0:1:0] ∈ E₁`, the intersection
of `E₁` with the strict transform of the `z`-axis, at which the marked transform
`I₁ = π_*^{-1}(I, 2)` has order exactly `2`. The centre `J` of the first blow-up is passed with
`hJ : J = 𝔪₀` (as `centerIdeal ℚ 4 4`) so that the statement applies to `ofIdealTop 𝔪₀`. -/
theorem secondCenter_of_axioms (J : Ideal R4) (hJ : J = centerIdeal ℚ 4 4)
    (E : DivisorFamily (Spec (CommRingCat.of R4)))
    (rest : BlowUpSequence (specIdealSheaf J).blowUp)
    (hS : (cons _ (specIdealSheaf J) rest).IsOrderSeq (affineSpaceToSpec ℚ 4)
      (specIdealSheaf I106) E 2)
    (hne : (cons _ (specIdealSheaf J) rest).NoEmptyCenters)
    (hend : ((cons _ (specIdealSheaf J) rest).weakTransformSeq (specIdealSheaf I106)
      (Fin.last _)).maxOrd < ((2 : ℕ) : ℕ∞)) :
    ∃ (Z₁ : (specIdealSheaf J).blowUp.IdealSheafData)
      (rest' : BlowUpSequence Z₁.blowUp),
      rest = cons _ Z₁ rest' ∧
      Z₁.support = ((specIdealSheaf zAxisIdeal).strictTransform (specIdealSheaf J)).support ⊓
        (specIdealSheaf J).exceptionalDivisor.support ∧
      ∀ q ∈ Z₁.support,
        ((specIdealSheaf I106).weakTransform (specIdealSheaf J)).ord q = ((2 : ℕ) : ℕ∞) := by
  subst hJ
  obtain ⟨⟨hsm, -, hord⟩, hrest⟩ := (isOrderSeq_cons_iff (f := affineSpaceToSpec ℚ 4)
    (I := specIdealSheaf I106) (E := E) (m := 2) _ _).mp hS
  have hne' := ((noEmptyCenters_cons_iff _ _).mp hne).2
  have hend' : (rest.weakTransformSeq ((specIdealSheaf I106).weakTransform (specIdealSheaf c44))
      (Fin.last _)).maxOrd < ((2 : ℕ) : ℕ∞) := hend
  have hsm' : Smooth ((specIdealSheaf c44).subschemeι ≫ affineSpaceToSpec ℚ 4) := hsm
  obtain ⟨Z₁, rest', hcons, hsupp⟩ := exists_eq_cons_of_ord_le_iff rest
    ((specIdealSheaf c44).blowUpπ ≫ affineSpaceToSpec ℚ 4) _ _ 2 hrest hne' hend'
    isClosed_singleton_qB (two_le_ord_weakTransform_iff hord)
  refine ⟨Z₁, rest', hcons, ?_, ?_⟩
  · rw [hsupp]
    ext b
    rw [Closeds.coe_mk, Set.mem_singleton_iff, Closeds.coe_inf, Set.mem_inter_iff, SetLike.mem_coe,
      SetLike.mem_coe]
    exact (mem_strictTransform_and_exceptional_iff b).symm
  · intro q hq
    rw [hsupp] at hq
    have hq' : q = qB := by simpa using hq
    rw [hq']
    exact ord_weakTransform_qB hord

end Hironaka.Examples.Example106BO
