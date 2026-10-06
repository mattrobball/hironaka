/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import HironakaExamples.OrderReduction.Example106BlowUp
import Hironaka.Resolution.Algebraic.Kol07.CosuppTransport
import Hironaka.Scheme.BlowUp.BlowUpMap
public import Hironaka.Scheme.BlowUp.Composite.ChartIdeal
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUp.Transform.TransformIso
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.Remark33Exceptional
import Hironaka.Scheme.BlowUpSequence.Remark33Iso
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.AffineSpace
public import Hironaka.Scheme.IdealSheaf.Order.Invariance
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.Smooth.Origin
import HironakaExamples.MaximalContact.Example106Stages
import HironakaExamples.OrderReduction.Example106
import HironakaExamples.Sequence.CosuppForcing
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Hironaka.Scheme.BlowUp.Model
import Mathlib.AlgebraicGeometry.Scheme
import Hironaka.Scheme.Smooth.CoordinateSystem
import Mathlib.AlgebraicGeometry.OpenImmersion
import Std.Time.Format.Modifier
import Mathlib.Algebra.MvPolynomial.Basic
import Hironaka.Scheme.BlowUp.Defs
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Admissible
import HironakaExamples.BlowUp.Glue.SpecIso
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.EqToHom
public import HironakaExamples.MaximalContact.Example106Charts
import Hironaka.Scheme.Snc.Defs
import Hironaka.Scheme.BlowUp.BlowUpMap.Defs
import Hironaka.Scheme.BlowUp.AffineBlowUp.Defs
import Hironaka.Scheme.BlowUpSequence.Defs
import Hironaka.Scheme.BlowUp.CoordinateSubspace.Charts

/-!
# Kollár's Example 106 for the order-reduction functor: at least four blow-ups of order two

After the blow-up of the origin, the point `q ∈ E₁` of the `z`-chart has order `2` for the
transform `(I₁, 2)` (`HironakaExamples/OrderReduction/Example106BlowUp.lean`); blowing it up, the
origin `q'` of the `w₂`-chart is again of order `2`, and after that blow-up the origin `q''` of the
`w₃`-chart is again of order `2` (the chart identities of
`HironakaExamples/MaximalContact/Example106Stages.lean`). For the order-reduction functor of [Kol07,
Theorem 103] this means that the order-`2` run of `BO_{4,2}(𝔸⁴_ℚ, I, ∅)` has at least four blow-ups
(`four_le_length_of_axioms`), whereas the text of [Kol07, Example 106] passes to the mark `1` after
the first: the sequence cannot end while a point of order `2` exists (clause (1) of Theorem 103),
and its centres are forced one stage at a time by the cosupport forcing of
`HironakaExamples/Sequence/CosuppForcing.lean`.

The mechanism is one **stage step**, run twice. On a `ℚ`-scheme `Y` with a centre `Z` and an
ideal `I` whose order-`2` locus is `{ι 0}`, for an open chart `ι : 𝔸⁴_ℚ ⟶ Y` on which `Z` is the
reduced origin and `I` is `V(P)`, the blow-up of `Y` at `Z` receives the model blow-up of the
origin of `𝔸⁴` as an open piece (`stepMap`: the identification of
`HironakaExamples/BlowUp/Glue/SpecIso.lean` and the map of blow-ups along `ι`, a cartesian square),
on which the weak transform is the controlled transform `(σ_j P : x_j²)` chart by chart
(`weakTransform_comap_stepMap`); off the piece the weak transform has the order of `I` at the image
(`ord_weakTransform_of_notMem`), which is `< 2`. So the order-`2` locus of the new weak transform is
read on the four charts of the model, the same computation as at stage 1 with the chart ideals
`K_z = (x³z − y², z(x⁴z + x − w³))` (stage 2) and `K_zw = (x³zw² − y², z(x⁴zw⁴ + x − w²))` (stage 3)
in place of `I`, and it is a single closed point (the cosupport is closed, `isClosed_setOf_le_ord`),
at which the forcing pins the next centre. That centre is the reduced point (the centres of an order
sequence are smooth, read on the pulled-back sequence: `comap_eq_specIdealSheaf_centerIdeal`), so
its chart form is again the origin and the step repeats. At stage 3 only the existence of the
order-`2` point `q''` is needed (`two_le_ord_weakTransform_stepMap` with `ord_zero_example106_zww`):
the final maximal order `< 2` then forces a fourth blow-up (`one_le_length_of_le_ord`).

Every order-`2` locus is computed at every scheme point, through the derivative criterion
`ord_p ≥ 2 ↔ D(K) ⊆ p` ([Kol07, Lemma 74 (3)]) on each chart. The three lemmas
`comap_markedTransform_eqToHom`, `exists_eqToHom_apply_eq` and `map_span_pair` are the
`Scheme.{0}` and `ℚ[x, y, z, w]` instances of their general forms in
`Hironaka/Scheme/BlowUpSequence/InducedData.lean`, `Hironaka/Scheme/BlowUp/BlowUpMap.lean` and
`Hironaka/Scheme/BlowUp/Composite/ChartIdeal.lean`; `mem_of_two_mul_mem` is specific to `ℚ`. The
result is applied to the functor's own sequence in `HironakaExamples/KollarExample106Run.lean`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
  Scheme.IdealSheafData Scheme BlowUpSequence Hironaka.BlowUp IdealSheafData CoordinateSubspace
  affineBlowUpAlgebra Hironaka.Sequence AlgebraicGeometry.Remark33 Hironaka.Examples.Example106
  Hironaka.Examples.Example106Charts Hironaka.Examples.Example106Stages

namespace Hironaka.Examples.Example106BO

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
/-- The affine space `𝔸⁴_ℚ`. -/
local notation "𝔸⁴" => Spec (CommRingCat.of (MvPolynomial (Fin 4) ℚ))
/-- The centre `(x_0, …, x_3)` of the model blow-up of the origin. -/
local notation "c44" => centerIdeal ℚ 4 4
/-- The chart of `x_j` of the model blow-up. -/
local notation "chart" j => modelChart ℚ 4 4 j (Fin.isLt j)
/-- The substitution of the chart of `x_j` (`chartSubst`). -/
local notation "σ" j => chartSubst ℚ (CoordinateSubspace.center 4 4) j
/-- The identification of the blow-up of record with the model blow-up. -/
local notation "Φ" => blowUpSpecIso (centerIdeal ℚ 4 4)
/-- The blow-up of `𝔸⁴_ℚ` at the origin. -/
local notation "𝔹ᵣ" => Scheme.IdealSheafData.blowUp (specIdealSheaf (centerIdeal ℚ 4 4))

/-! ### The model computation for an arbitrary ideal -/

/-- The controlled transform of control `2` of `V(P)` on the model blow-up of the origin of `𝔸⁴`
([Kol07, Definition 60]): the shape of `modelW` for an arbitrary ideal `P`. -/
noncomputable abbrev modelWP (P : Ideal R4) : (affineBlowUp c44).IdealSheafData :=
  ((specIdealSheaf P).comap (affineBlowUp.π c44)).colon (affineBlowUp.exceptionalIdeal c44 ^ 2)

/-- Kollár's chart ideal `(σ_j P : x_j²)` on the chart of `x_j`. -/
noncomputable abbrev chartColon (P : Ideal R4) (j : Fin 4) : Ideal R4 :=
  (P.map (σ j).toRingHom).colon ((Ideal.span {(X j : R4)} ^ 2 : Ideal R4) : Set R4)

/-- The controlled transform on the chart of `x_j` is the ideal sheaf of the chart ideal
`(σ_j P : x_j²)` ([Kol07, Definition 60] on the chart, for any `P`; `comap_modelW_modelChart` is
the case `P = I`). -/
theorem comap_modelWP_modelChart (P : Ideal R4) (j : Fin 4) :
    (modelWP P).comap (chart j) = specIdealSheaf (chartColon P j) := by
  have hX : (X j : R4) ∈ nonZeroDivisors R4 := mem_nonZeroDivisors_of_ne_zero (X_ne_zero j)
  have hinv : (specIdealSheaf (Ideal.span {(X j : R4)} ^ 2)).IsInvertible := by
    rw [specIdealSheaf_pow]
    exact isInvertible_pow (isInvertible_specIdealSheaf_span_singleton hX) 2
  rw [modelWP, colon_comap_of_flat _ _
      (isInvertible_pow (affineBlowUp.isInvertible_exceptionalIdeal _) 2),
    comap_pow, comap_comap_modelChart, comap_exceptionalIdeal_modelChart', ← specIdealSheaf_pow,
    specIdealSheaf_colon _ _ hinv]

/-- The image of a two-generator ideal under a chart substitution: the `ℚ[x, y, z, w]` instance of
`Ideal.map_span_pair`. -/
theorem map_span_pair (σ' : R4 →ₐ[ℚ] R4) (g₁ g₂ : R4) :
    (Ideal.span {g₁, g₂}).map σ'.toRingHom = Ideal.span {σ' g₁, σ' g₂} :=
  Ideal.map_span_pair σ'.toRingHom g₁ g₂

/-- The chart ideal of a two-generator ideal whose generators transform with the factor `x_j²`
([Kol07, Definition 60]; the chart identities of `Example106Charts.lean`). -/
theorem chartColon_span_pair (j : Fin 4) {g₁ g₂ h₁ h₂ : R4} (e₁ : (σ j) g₁ = X j ^ 2 * h₁)
    (e₂ : (σ j) g₂ = X j ^ 2 * h₂) :
    chartColon (Ideal.span {g₁, g₂}) j = Ideal.span {h₁, h₂} := by
  rw [chartColon, map_span_pair, e₁, e₂, Ideal.span_singleton_pow]
  exact colon_span_pair_mul (pow_ne_zero 2 (X_ne_zero j))

/-- The derivative criterion on the chart of `x_j`: `ord ≥ 2` at a point of the chart iff its
prime contains `D(σ_j P : x_j²)`. -/
theorem two_le_ord_modelWP_chart_iff (P : Ideal R4) (j : Fin 4) (p : Spec (CommRingCat.of R4)) :
    ((2 : ℕ) : ℕ∞) ≤ ((modelWP P).comap (chart j)).ord p ↔
      Ideal.derivative ℚ (chartColon P j) ≤ p.asIdeal := by
  rw [comap_modelWP_modelChart, le_ord_specIdealSheaf_iff _ p one_le_two,
    derivativeIter_two_sub_one]

/-- If no prime of a chart other than `j₀` contains `D(σ_j P : x_j²)`, and on the chart `j₀` only
the origin does, then the order-`2` locus of the controlled transform of `V(P)` on the model
blow-up is the origin of the chart `j₀`, at every scheme point (`two_le_ord_modelW_iff` for any
`P`). -/
theorem two_le_ord_modelWP_iff (P : Ideal R4) (j₀ : Fin 4)
    (H1 : ∀ j : Fin 4, j ≠ j₀ → ∀ p : Spec (CommRingCat.of R4),
      ¬ Ideal.derivative ℚ (chartColon P j) ≤ p.asIdeal)
    (H2 : ∀ p : Spec (CommRingCat.of R4),
      Ideal.derivative ℚ (chartColon P j₀) ≤ p.asIdeal ↔ p = origin ℚ 4)
    (b : affineBlowUp c44) :
    ((2 : ℕ) : ℕ∞) ≤ (modelWP P).ord b ↔ b = (chart j₀) (origin ℚ 4) := by
  constructor
  · intro h
    obtain ⟨j, p, rfl⟩ := exists_modelChart_eq b
    rw [← ord_comap_of_isOpenImmersion (modelWP P) (chart j) p, two_le_ord_modelWP_chart_iff] at h
    by_cases hj : j = j₀
    · subst hj
      rw [(H2 p).mp h]
    · exact absurd h (H1 j hj p)
  · rintro rfl
    rw [← ord_comap_of_isOpenImmersion (modelWP P) (chart j₀) (origin ℚ 4),
      two_le_ord_modelWP_chart_iff]
    exact (H2 _).mpr rfl

/-! ### The stage step: the blow-up at a chart origin receives the model blow-up as an open piece -/

section Step

variable {Y : Scheme.{0}} (ZY IY : Y.IdealSheafData) (ι : 𝔸⁴ ⟶ Y) [IsOpenImmersion ι]

/-- Transport of the marked transform along an equality of centres (the `eqToHom` of
`eqToHom_comp_blowUpπ`): the `Scheme.{0}` instance of
`AlgebraicGeometry.comap_markedTransform_eqToHom`. -/
theorem comap_markedTransform_eqToHom {X : Scheme.{0}} {I J : X.IdealSheafData} (e : I = J)
    (K : X.IdealSheafData) (m : ℕ) :
    (K.markedTransform J m).comap (eqToHom (congrArg IdealSheafData.blowUp e)) =
      K.markedTransform I m :=
  AlgebraicGeometry.comap_markedTransform_eqToHom e K m

/-- The model blow-up of the origin of `𝔸⁴` as an open piece of the blow-up of `Y` at a centre `ZY`
that is the origin on the chart `ι` ([Kol07, 30.1], the pull-back of a blow-up along an open
immersion): `blowUpMap ι ZY` preceded by the transport of the centre and by `blowUpSpecIso`. -/
noncomputable def stepMap (hZ : ZY.comap ι = specIdealSheaf c44) :
    affineBlowUp c44 ⟶ IdealSheafData.blowUp ZY :=
  (Φ).inv ≫ eqToHom (congrArg IdealSheafData.blowUp hZ.symm) ≫ Hom.blowUpMap ι ZY

/-- The open piece is an open immersion (`isOpenImmersion_blowUpMap`). -/
instance isOpenImmersion_stepMap (hZ : ZY.comap ι = specIdealSheaf c44) :
    IsOpenImmersion (stepMap ZY ι hZ) := by
  unfold stepMap
  infer_instance

omit [IsOpenImmersion ι] in
/-- The open piece lies over the chart: `stepMap ≫ π = π_model ≫ ι`. -/
theorem stepMap_π (hZ : ZY.comap ι = specIdealSheaf c44) :
    stepMap ZY ι hZ ≫ ZY.blowUpπ = affineBlowUp.π c44 ≫ ι := by
  rw [stepMap, Category.assoc, Category.assoc, blowUpMap_π, ← Category.assoc (eqToHom _),
    eqToHom_comp_blowUpπ hZ.symm, ← Category.assoc, blowUpSpecIso_inv_π]

/-- Points of a blow-up transport along an equality of centres: the `Scheme.{0}` instance of
`AlgebraicGeometry.exists_eqToHom_apply_eq`. -/
theorem exists_eqToHom_apply_eq {X : Scheme.{0}} {I J : X.IdealSheafData} (e : I = J)
    (t : IdealSheafData.blowUp J) : ∃ s, eqToHom (congrArg IdealSheafData.blowUp e) s = t :=
  AlgebraicGeometry.exists_eqToHom_apply_eq e t

/-- Every point of `blowUp Y ZY` over the chart lies on the open piece (the cartesian square of
`blowUpMap`, `exists_blowUpMap_eq`). -/
theorem exists_stepMap_eq (hZ : ZY.comap ι = specIdealSheaf c44) (b : IdealSheafData.blowUp ZY)
    (p : 𝔸⁴) (hb : ZY.blowUpπ b = ι p) : ∃ a, stepMap ZY ι hZ a = b := by
  obtain ⟨t, rfl⟩ := exists_blowUpMap_eq ι ZY b p hb
  obtain ⟨s, rfl⟩ := exists_eqToHom_apply_eq hZ.symm t
  refine ⟨(Φ).hom s, ?_⟩
  -- the composite is unfolded by a term-mode `comp_apply` (a `rw` through the coercion of the
  -- three-fold composite makes Lean's kernel time out)
  have h1 : stepMap ZY ι hZ ((Φ).hom s) =
      (eqToHom (congrArg IdealSheafData.blowUp hZ.symm) ≫ Hom.blowUpMap ι ZY)
        ((Φ).inv ((Φ).hom s)) := Scheme.Hom.comp_apply _ _ _
  rw [h1, inv_hom_apply, Scheme.Hom.comp_apply]

/-- On the open piece the weak transform of `IY` is the model's controlled transform of `V(P)`
([Kol07, 58] against [Kol07, Definition 60]; `weakTransform_eq_markedTransform_of_smooth` and the
flat pull-back of colon ideals). -/
theorem weakTransform_comap_stepMap (f : Y ⟶ Spec (.of ℚ)) (n : ℕ) [SmoothOfRelativeDimension n f]
    [Smooth (ZY.subschemeι ≫ f)] (hZ : ZY.comap ι = specIdealSheaf c44) (P : Ideal R4)
    (hI : IY.comap ι = specIdealSheaf P) (hord : IY.OrdAlongEq ZY.support ((2 : ℕ) : ℕ∞)) :
    (IY.weakTransform ZY).comap (stepMap ZY ι hZ) = modelWP P := by
  have hE : ZY.exceptionalDivisor.IsInvertible := blowUp.isInvertible_comap_π ZY
  have h1 : (IY.markedTransform ZY 2).comap (Hom.blowUpMap ι ZY) =
      (IY.comap ι).markedTransform (ZY.comap ι) 2 := by
    rw [markedTransform_eq_colon, markedTransform_eq_colon,
      colon_comap_of_flat _ _ (isInvertible_pow hE 2), comap_pow,
      ← comap_comp IY (Hom.blowUpMap ι ZY) ZY.blowUpπ, blowUpMap_π, comap_comp,
      exceptionalDivisor_comap]
  rw [weakTransform_eq_markedTransform_of_smooth f n ZY IY hord, stepMap, comap_comp, comap_comp,
    h1, comap_markedTransform_eqToHom hZ.symm, hI, markedTransform_eq_colon,
    comap_colon_of_isIso,
    comap_pow, comap_comap_blowUpSpecIso_inv, comap_exceptionalDivisor_inv]

/-- If the order-`2` locus of `IY` is the chart origin `ι 0`, the centre is supported there, and
the chart hypotheses on `V(P)` hold (no prime of a chart other than `j₀` contains the derivative of
its chart ideal, and on the chart `j₀` only the origin does), then the order-`2` locus of the weak
transform is the single point `stepMap (chart j₀ 0)`, at every scheme point: on the open piece by
the model computation, off it by `ord_weakTransform_of_notMem` (the point lies off the exceptional
divisor and its image has order `< 2`). -/
theorem two_le_ord_weakTransform_iff_step (f : Y ⟶ Spec (.of ℚ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [Smooth (ZY.subschemeι ≫ f)]
    (hZ : ZY.comap ι = specIdealSheaf c44) (P : Ideal R4) (hI : IY.comap ι = specIdealSheaf P)
    (hord : IY.OrdAlongEq ZY.support ((2 : ℕ) : ℕ∞))
    (hsupp : ∀ q ∈ ZY.support, q = ι (origin ℚ 4))
    (hcos : ∀ q : Y, ((2 : ℕ) : ℕ∞) ≤ IY.ord q ↔ q = ι (origin ℚ 4)) (j₀ : Fin 4)
    (H1 : ∀ j : Fin 4, j ≠ j₀ → ∀ p : Spec (CommRingCat.of R4),
      ¬ Ideal.derivative ℚ (chartColon P j) ≤ p.asIdeal)
    (H2 : ∀ p : Spec (CommRingCat.of R4),
      Ideal.derivative ℚ (chartColon P j₀) ≤ p.asIdeal ↔ p = origin ℚ 4)
    (b : IdealSheafData.blowUp ZY) :
    ((2 : ℕ) : ℕ∞) ≤ (IY.weakTransform ZY).ord b ↔
      b = stepMap ZY ι hZ ((chart j₀) (origin ℚ 4)) := by
  have key : ∀ a, (IY.weakTransform ZY).ord (stepMap ZY ι hZ a) = (modelWP P).ord a := fun a => by
    rw [← ord_comap_of_isOpenImmersion (IY.weakTransform ZY) (stepMap ZY ι hZ) a,
      weakTransform_comap_stepMap ZY IY ι f n hZ P hI hord]
  constructor
  · intro h
    by_cases hb : ∃ p, ι p = ZY.blowUpπ b
    · obtain ⟨p, hp⟩ := hb
      obtain ⟨a, rfl⟩ := exists_stepMap_eq ZY ι hZ b p hp.symm
      rw [key] at h
      rw [(two_le_ord_modelWP_iff P j₀ H1 H2 a).mp h]
    · exfalso
      have hbE : b ∉ ZY.exceptionalDivisor.support := fun hbE =>
        hb ⟨origin ℚ 4,
          (hsupp _ ((mem_support_comap_iff_apply ZY ZY.blowUpπ b).mp hbE)).symm⟩
      rw [ord_weakTransform_of_notMem ZY IY hbE, hcos] at h
      exact hb ⟨origin ℚ 4, h.symm⟩
  · rintro rfl
    rw [key]
    exact (two_le_ord_modelWP_iff P j₀ H1 H2 _).mpr rfl

/-- The order-`2` point of the new weak transform is a closed point: the closed cosupport
`{ord ≥ 2}` (`isClosed_setOf_le_ord`) is that single point. -/
theorem isClosed_singleton_stepMap_origin (f : Y ⟶ Spec (.of ℚ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [Smooth (ZY.subschemeι ≫ f)]
    (hZ : ZY.comap ι = specIdealSheaf c44) (P : Ideal R4) (hI : IY.comap ι = specIdealSheaf P)
    (hord : IY.OrdAlongEq ZY.support ((2 : ℕ) : ℕ∞))
    (hsupp : ∀ q ∈ ZY.support, q = ι (origin ℚ 4))
    (hcos : ∀ q : Y, ((2 : ℕ) : ℕ∞) ≤ IY.ord q ↔ q = ι (origin ℚ 4)) (j₀ : Fin 4)
    (H1 : ∀ j : Fin 4, j ≠ j₀ → ∀ p : Spec (CommRingCat.of R4),
      ¬ Ideal.derivative ℚ (chartColon P j) ≤ p.asIdeal)
    (H2 : ∀ p : Spec (CommRingCat.of R4),
      Ideal.derivative ℚ (chartColon P j₀) ≤ p.asIdeal ↔ p = origin ℚ 4) :
    IsClosed ({stepMap ZY ι hZ ((chart j₀) (origin ℚ 4))} : Set (IdealSheafData.blowUp ZY)) := by
  have := smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n ZY
  have hcl := isClosed_setOf_le_ord (ZY.blowUpπ ≫ f) n (IY.weakTransform ZY) 2
  convert hcl using 1
  ext b
  rw [Set.mem_singleton_iff]
  exact (two_le_ord_weakTransform_iff_step ZY IY ι f n hZ P hI hord hsupp hcos j₀ H1 H2 b).symm

/-- The next centre of the order sequence is forced (clause (1) of [Kol07, Theorem 103] through the
cosupport forcing `exists_eq_cons_of_ord_le_iff`): it is supported exactly at the order-`2` point
`stepMap (chart j₀ 0)`. -/
theorem exists_eq_cons_step (f : Y ⟶ Spec (.of ℚ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [Smooth (ZY.subschemeι ≫ f)]
    (hZ : ZY.comap ι = specIdealSheaf c44) (P : Ideal R4) (hI : IY.comap ι = specIdealSheaf P)
    (hord : IY.OrdAlongEq ZY.support ((2 : ℕ) : ℕ∞))
    (hsupp : ∀ q ∈ ZY.support, q = ι (origin ℚ 4))
    (hcos : ∀ q : Y, ((2 : ℕ) : ℕ∞) ≤ IY.ord q ↔ q = ι (origin ℚ 4)) (j₀ : Fin 4)
    (H1 : ∀ j : Fin 4, j ≠ j₀ → ∀ p : Spec (CommRingCat.of R4),
      ¬ Ideal.derivative ℚ (chartColon P j) ≤ p.asIdeal)
    (H2 : ∀ p : Spec (CommRingCat.of R4),
      Ideal.derivative ℚ (chartColon P j₀) ≤ p.asIdeal ↔ p = origin ℚ 4)
    {E' : DivisorFamily (IdealSheafData.blowUp ZY)}
    (rest : BlowUpSequence (IdealSheafData.blowUp ZY))
    (hS : rest.IsOrderSeq (ZY.blowUpπ ≫ f) (IY.weakTransform ZY) E' 2)
    (hne : rest.NoEmptyCenters)
    (hend : (rest.weakTransformSeq (IY.weakTransform ZY) (Fin.last _)).maxOrd <
      ((2 : ℕ) : ℕ∞)) :
    ∃ (Z' : (IdealSheafData.blowUp ZY).IdealSheafData)
      (rest' : BlowUpSequence (IdealSheafData.blowUp Z')),
      rest = cons _ Z' rest' ∧
        ∀ q, q ∈ Z'.support ↔ q = stepMap ZY ι hZ ((chart j₀) (origin ℚ 4)) := by
  obtain ⟨Z', rest', hcons, hsupp'⟩ := exists_eq_cons_of_ord_le_iff rest
      (ZY.blowUpπ ≫ f) _ _ 2
    hS hne hend (isClosed_singleton_stepMap_origin ZY IY ι f n hZ P hI hord hsupp hcos j₀ H1 H2)
    (two_le_ord_weakTransform_iff_step ZY IY ι f n hZ P hI hord hsupp hcos j₀ H1 H2)
  refine ⟨Z', rest', hcons, fun q => ?_⟩
  rw [hsupp']
  exact Set.mem_singleton_iff

/-- A centre of an order sequence supported at the chart origin `ι 0` is, on the chart, the reduced
origin `(x, y, z, w)` (`centerIdeal`): the centres are smooth ([Kol07, Definition 65 (1)]), hence
regular, hence reduced, hence the vanishing ideal of their support, read on the sequence pulled
back along the chart ([Kol07, 30.1]). -/
theorem comap_eq_specIdealSheaf_centerIdeal (f : Y ⟶ Spec (.of ℚ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (Z I : Y.IdealSheafData) (E : DivisorFamily Y)
    (rest : BlowUpSequence (IdealSheafData.blowUp Z)) (hS : (cons Y Z rest).IsOrderSeq f I E 2)
    (hsupp : ∀ q, q ∈ Z.support ↔ q = ι (origin ℚ 4)) :
    Z.comap ι = specIdealSheaf c44 := by
  have hf : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hpull := IsOrderSeq.pullback f n ι (d := 0) hS
  rw [pullback_cons] at hpull
  have hZι := center_eq_vanishingIdeal_support_of_isOrderSeq (ι ≫ f) (I.comap ι) (E.comap ι) 2
    (Z.comap ι) _ hpull
  have hsup : (Z.comap ι).support = ⟨{origin ℚ 4}, isClosed_singleton_origin⟩ := by
    ext q
    simp only [SetLike.mem_coe, Closeds.coe_mk, Set.mem_singleton_iff]
    rw [mem_support_comap_iff_apply, hsupp]
    exact ι.isOpenEmbedding.injective.eq_iff
  rw [hZι, hsup, vanishingIdeal_singleton_origin, centerIdeal_eq_m0]

/-- The origin of the chart `j₀` on the open piece has `ord ≥ 2` for the new weak transform as soon
as `D(σ_{j₀} P : x_{j₀}²) ⊆ (x, y, z, w)`: the third stage. -/
theorem two_le_ord_weakTransform_stepMap (f : Y ⟶ Spec (.of ℚ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [Smooth (ZY.subschemeι ≫ f)]
    (hZ : ZY.comap ι = specIdealSheaf c44) (P : Ideal R4) (hI : IY.comap ι = specIdealSheaf P)
    (hord : IY.OrdAlongEq ZY.support ((2 : ℕ) : ℕ∞)) (j₀ : Fin 4)
    (H : Ideal.derivative ℚ (chartColon P j₀) ≤ (origin ℚ 4).asIdeal) :
    ((2 : ℕ) : ℕ∞) ≤ (IY.weakTransform ZY).ord (stepMap ZY ι hZ ((chart j₀) (origin ℚ 4))) := by
  rw [← ord_comap_of_isOpenImmersion (IY.weakTransform ZY) (stepMap ZY ι hZ),
    weakTransform_comap_stepMap ZY IY ι f n hZ P hI hord,
    ← ord_comap_of_isOpenImmersion (modelWP P) (chart j₀), two_le_ord_modelWP_chart_iff]
  exact H

end Step

/-- Clause (1) of [Kol07, Theorem 103] at the end of a sequence: if a point of order `≥ m` remains
while the final maximal order is `< m`, the sequence is not empty. -/
theorem one_le_length_of_le_ord {X : Scheme.{0}} (S : BlowUpSequence X) (I : X.IdealSheafData)
    (m : ℕ) (hend : (S.weakTransformSeq I (Fin.last _)).maxOrd < (m : ℕ∞)) {pt : X}
    (hpt : (m : ℕ∞) ≤ I.ord pt) : 1 ≤ S.length := by
  cases S with
  | nil _ =>
    exfalso
    change I.maxOrd < (m : ℕ∞) at hend
    exact absurd (hpt.trans (le_maxOrdAlong I (Set.mem_univ pt))) (not_le.mpr hend)
  | cons _ Z rest => exact Nat.le_add_left 1 rest.length

/-! ### Stages 2 and 3: the chart ideals `K_z` and `K_zw` and their order-2 loci -/

/-- Kollár's `I₁` on the `z`-chart: `K_z = (x³z − y², z(x⁴z + x − w³))`. -/
noncomputable abbrev Kz : Ideal R4 := Ideal.span {x ^ 3 * z - y ^ 2, z * (x ^ 4 * z + x - w ^ 3)}

/-- The transform `I₂` on the `w₂`-chart of the blow-up of `q`:
`K_zw = (x³zw² − y², z(x⁴zw⁴ + x − w²))`. -/
noncomputable abbrev Kzw : Ideal R4 :=
  Ideal.span {x ^ 3 * z * w ^ 2 - y ^ 2, z * (x ^ 4 * z * w ^ 4 + x - w ^ 2)}

/-- The `x₂`-chart: `(σ_x K_z : x²) = (x²z − y², z(x⁴z + 1 − w³x²))`. -/
theorem chartColon_Kz_zero :
    chartColon Kz 0 = Ideal.span {x ^ 2 * z - y ^ 2, z * (x ^ 4 * z + 1 - w ^ 3 * x ^ 2)} :=
  chartColon_span_pair 0 (by rw [chartSubst_zero_eq]; exact transform_example106_zx.1)
    (by rw [chartSubst_zero_eq]; exact transform_example106_zx.2)

/-- The `y₂`-chart: `(σ_y K_z : y²) = (x³y²z − 1, z(x⁴y⁴z + x − w³y²))`. -/
theorem chartColon_Kz_one :
    chartColon Kz 1 =
      Ideal.span {x ^ 3 * y ^ 2 * z - 1, z * (x ^ 4 * y ^ 4 * z + x - w ^ 3 * y ^ 2)} :=
  chartColon_span_pair 1 (by rw [chartSubst_one_eq]; exact transform_example106_zy.1)
    (by rw [chartSubst_one_eq]; exact transform_example106_zy.2)

/-- The `z₂`-chart: `(σ_z K_z : z²) = (x³z² − y², x⁴z⁴ + x − w³z²)`. -/
theorem chartColon_Kz_two :
    chartColon Kz 2 = Ideal.span {x ^ 3 * z ^ 2 - y ^ 2, x ^ 4 * z ^ 4 + x - w ^ 3 * z ^ 2} :=
  chartColon_span_pair 2 (by rw [chartSubst_two_eq]; exact transform_example106_zz.1)
    (by rw [chartSubst_two_eq]; exact transform_example106_zz.2)

/-- The `w₂`-chart: `(σ_w K_z : w²) = K_zw`. -/
theorem chartColon_Kz_three : chartColon Kz 3 = Kzw :=
  chartColon_span_pair 3 (by rw [chartSubst_three_eq]; exact transform_example106_zw.1)
    (by rw [chartSubst_three_eq]; exact transform_example106_zw.2.1)

/-- The `w₃`-chart: `(σ_w K_zw : w²) = (x³zw⁴ − y², z(x⁴zw⁸ + x − w))`. -/
theorem chartColon_Kzw_three :
    chartColon Kzw 3 = Ideal.span {x ^ 3 * z * w ^ 4 - y ^ 2, z * (x ^ 4 * z * w ^ 8 + x - w)} :=
  chartColon_span_pair 3 (by rw [chartSubst_three_eq]; exact transform_example106_zww.1)
    (by rw [chartSubst_three_eq]; exact transform_example106_zww.2.1)

/-- `2a ∈ p ⇒ a ∈ p` in `ℚ[x, y, z, w]`, `2` being a unit. -/
theorem mem_of_two_mul_mem (p : Ideal R4) {a : R4} (h : 2 * a ∈ p) : a ∈ p := by
  have : a = C (1 / 2 : ℚ) * (2 * a) := by
    rw [(by simp [map_ofNat] : (2 : R4) = C 2), ← mul_assoc, ← C_mul]
    norm_num
  rw [this]
  exact Ideal.mul_mem_left _ _ h

/-- The `x₂`-chart of the blow-up of `q` has no point of order `2`, at every prime:
`∂_z(x²z − y²) = x²` puts `x` in a prime containing `D(K)`, and then
`∂_z(z(x⁴z + 1 − w³x²)) = 2x⁴z + 1 − w³x²` puts `1` in it. -/
theorem not_le_derivative_Kz_zero (p : Ideal R4) [hp : p.IsPrime] :
    ¬ Ideal.derivative ℚ (Ideal.span {x ^ 2 * z - y ^ 2, z * (x ^ 4 * z + 1 - w ^ 3 * x ^ 2)}) ≤
      p := by
  intro h
  set K := Ideal.span {x ^ 2 * z - y ^ 2, z * (x ^ 4 * z + 1 - w ^ 3 * x ^ 2)} with hK
  have hg1 : x ^ 2 * z - y ^ 2 ∈ K := Ideal.subset_span (by simp)
  have hg2 : z * (x ^ 4 * z + 1 - w ^ 3 * x ^ 2) ∈ K := Ideal.subset_span (by simp)
  have e1 : pd 2 (x ^ 2 * z - y ^ 2) = x ^ 2 := by simp
  have e2 : pd 2 (z * (x ^ 4 * z + 1 - w ^ 3 * x ^ 2)) = 2 * x ^ 4 * z + 1 - w ^ 3 * x ^ 2 := by
    simp
    ring
  have h1 := h (Ideal.derivation_apply_mem_derivative (pd 2) hg1)
  have h2 := h (Ideal.derivation_apply_mem_derivative (pd 2) hg2)
  rw [e1] at h1
  rw [e2] at h2
  have hx : x ∈ p := hp.mem_of_pow_mem 2 h1
  have hone : (1 : R4) ∈ p := by
    have : (1 : R4) = (2 * x ^ 4 * z + 1 - w ^ 3 * x ^ 2) - x * (2 * x ^ 3 * z - w ^ 3 * x) := by
      ring
    rw [this]
    exact Ideal.sub_mem _ h2 (Ideal.mul_mem_right _ _ hx)
  exact hp.ne_top ((Ideal.eq_top_iff_one _).mpr hone)

/-- The `y₂`-chart has no point of order `2`: `x³y²z − 1 ∈ D(K)` and `∂_z(x³y²z − 1) = x³y² ∈ D(K)`,
so `1 ∈ D(K)`. -/
theorem not_le_derivative_Kz_one (p : Ideal R4) [hp : p.IsPrime] :
    ¬ Ideal.derivative ℚ
      (Ideal.span {x ^ 3 * y ^ 2 * z - 1, z * (x ^ 4 * y ^ 4 * z + x - w ^ 3 * y ^ 2)}) ≤ p := by
  intro h
  set K := Ideal.span {x ^ 3 * y ^ 2 * z - 1, z * (x ^ 4 * y ^ 4 * z + x - w ^ 3 * y ^ 2)} with hK
  have hg1 : x ^ 3 * y ^ 2 * z - 1 ∈ K := Ideal.subset_span (by simp)
  have hg : x ^ 3 * y ^ 2 * z - 1 ∈ Ideal.derivative ℚ K := Ideal.le_derivative K hg1
  have e : pd 2 (x ^ 3 * y ^ 2 * z - 1) = x ^ 3 * y ^ 2 := by simp
  have h1 := Ideal.derivation_apply_mem_derivative (pd 2) hg1
  rw [e] at h1
  have hone : (1 : R4) ∈ Ideal.derivative ℚ K := by
    have : (1 : R4) = x ^ 3 * y ^ 2 * z - (x ^ 3 * y ^ 2 * z - 1) := by ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ h1) hg
  exact hp.ne_top ((Ideal.eq_top_iff_one _).mpr (h hone))

/-- The `z₂`-chart has no point of order `2`: `∂_z(x³z² − y²) = 2x³z` gives `x ∈ p` or `z ∈ p`, and
`∂_x(x⁴z⁴ + x − w³z²) = 4x³z⁴ + 1` then gives `1 ∈ p` in either case. -/
theorem not_le_derivative_Kz_two (p : Ideal R4) [hp : p.IsPrime] :
    ¬ Ideal.derivative ℚ (Ideal.span {x ^ 3 * z ^ 2 - y ^ 2, x ^ 4 * z ^ 4 + x - w ^ 3 * z ^ 2}) ≤
      p := by
  intro h
  set K := Ideal.span {x ^ 3 * z ^ 2 - y ^ 2, x ^ 4 * z ^ 4 + x - w ^ 3 * z ^ 2} with hK
  have hg1 : x ^ 3 * z ^ 2 - y ^ 2 ∈ K := Ideal.subset_span (by simp)
  have hg2 : x ^ 4 * z ^ 4 + x - w ^ 3 * z ^ 2 ∈ K := Ideal.subset_span (by simp)
  have e1 : pd 2 (x ^ 3 * z ^ 2 - y ^ 2) = 2 * (x ^ 3 * z) := by
    simp
    ring
  have e2 : pd 0 (x ^ 4 * z ^ 4 + x - w ^ 3 * z ^ 2) = 4 * x ^ 3 * z ^ 4 + 1 := by
    simp
    ring
  have h1 := h (Ideal.derivation_apply_mem_derivative (pd 2) hg1)
  have h2 := h (Ideal.derivation_apply_mem_derivative (pd 0) hg2)
  rw [e1] at h1
  rw [e2] at h2
  have hone : (1 : R4) ∈ p := by
    rcases hp.mem_or_mem (mem_of_two_mul_mem p h1) with hx3 | hz
    · have hx : x ∈ p := hp.mem_of_pow_mem 3 hx3
      have : (1 : R4) = (4 * x ^ 3 * z ^ 4 + 1) - x * (4 * x ^ 2 * z ^ 4) := by ring
      rw [this]
      exact Ideal.sub_mem _ h2 (Ideal.mul_mem_right _ _ hx)
    · have : (1 : R4) = (4 * x ^ 3 * z ^ 4 + 1) - z * (4 * x ^ 3 * z ^ 3) := by ring
      rw [this]
      exact Ideal.sub_mem _ h2 (Ideal.mul_mem_right _ _ hz)
  exact hp.ne_top ((Ideal.eq_top_iff_one _).mpr hone)

/-- On the `w₂`-chart a prime contains `D(K_zw)` iff it is the origin `q'`: `∂_y(x³zw² − y²) = −2y`,
`∂_z(x³zw² − y²) = x³w²`, `∂_x(z(x⁴zw⁴ + x − w²)) = 4x³z²w⁴ + z` and
`∂_z(z(x⁴zw⁴ + x − w²)) = 2x⁴zw⁴ + x − w²` put `y, x, z, w` in the prime (in the case `w ∈ p` of the
second derivative, `x ∈ p` follows from the fourth); conversely `K_zw ⊆ 𝔪²`
(`ord_zero_example106_zw`) gives `D(K_zw) ⊆ 𝔪`. -/
theorem le_derivative_Kzw_iff (p : Spec (CommRingCat.of R4)) :
    Ideal.derivative ℚ Kzw ≤ p.asIdeal ↔ p = origin ℚ 4 := by
  have hp : p.asIdeal.IsPrime := p.isPrime
  constructor
  · intro h
    have hg1 : x ^ 3 * z * w ^ 2 - y ^ 2 ∈ Kzw := Ideal.subset_span (by simp)
    have hg2 : z * (x ^ 4 * z * w ^ 4 + x - w ^ 2) ∈ Kzw := Ideal.subset_span (by simp)
    have e1 : pd 1 (x ^ 3 * z * w ^ 2 - y ^ 2) = -(2 * y) := by simp
    have e2 : pd 2 (x ^ 3 * z * w ^ 2 - y ^ 2) = x ^ 3 * w ^ 2 := by
      simp
      ring
    have e3 : pd 0 (z * (x ^ 4 * z * w ^ 4 + x - w ^ 2)) = 4 * x ^ 3 * z ^ 2 * w ^ 4 + z := by
      simp
      ring
    have e4 : pd 2 (z * (x ^ 4 * z * w ^ 4 + x - w ^ 2)) = 2 * x ^ 4 * z * w ^ 4 + x - w ^ 2 := by
      simp
      ring
    have h1 := h (Ideal.derivation_apply_mem_derivative (pd 1) hg1)
    have h2 := h (Ideal.derivation_apply_mem_derivative (pd 2) hg1)
    have h3 := h (Ideal.derivation_apply_mem_derivative (pd 0) hg2)
    have h4 := h (Ideal.derivation_apply_mem_derivative (pd 2) hg2)
    rw [e1] at h1
    rw [e2] at h2
    rw [e3] at h3
    rw [e4] at h4
    have hy : y ∈ p.asIdeal := mem_of_two_mul_mem _ ((Ideal.neg_mem_iff _).mp h1)
    have hx : x ∈ p.asIdeal := by
      rcases hp.mem_or_mem h2 with hx3 | hw2
      · exact hp.mem_of_pow_mem 3 hx3
      · have hw : w ∈ p.asIdeal := hp.mem_of_pow_mem 2 hw2
        have : x = (2 * x ^ 4 * z * w ^ 4 + x - w ^ 2) - w * (2 * x ^ 4 * z * w ^ 3 - w) := by
          ring
        rw [this]
        exact Ideal.sub_mem _ h4 (Ideal.mul_mem_right _ _ hw)
    have hz : z ∈ p.asIdeal := by
      have : z = (4 * x ^ 3 * z ^ 2 * w ^ 4 + z) - x * (4 * x ^ 2 * z ^ 2 * w ^ 4) := by ring
      rw [this]
      exact Ideal.sub_mem _ h3 (Ideal.mul_mem_right _ _ hx)
    have hw : w ∈ p.asIdeal := by
      have : w ^ 2 = x * (2 * x ^ 3 * z * w ^ 4 + 1) - (2 * x ^ 4 * z * w ^ 4 + x - w ^ 2) := by
        ring
      exact hp.mem_of_pow_mem 2 (this ▸ Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hx) h4)
    rw [eq_origin_iff_forall_X_mem]
    intro i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
    · exact hw
  · rintro rfl
    have hle : Kzw ≤ m0 ^ (1 + 1) := ord_zero_example106_zw.1
    have := Ideal.derivative_le_pow (k := ℚ) hle
    rwa [pow_one, m0_eq_origin_asIdeal] at this

/-- Off the `w₂`-chart, no prime of the blow-up of `q` has `ord I₂ ≥ 2`. -/
theorem not_le_derivative_chartColon_Kz (j : Fin 4) (hj : j ≠ 3) (p : Spec (CommRingCat.of R4)) :
    ¬ Ideal.derivative ℚ (chartColon Kz j) ≤ p.asIdeal := by
  have hp : p.asIdeal.IsPrime := p.isPrime
  rcases fin4_cases j with rfl | rfl | rfl | rfl
  · rw [chartColon_Kz_zero]
    exact not_le_derivative_Kz_zero p.asIdeal
  · rw [chartColon_Kz_one]
    exact not_le_derivative_Kz_one p.asIdeal
  · rw [chartColon_Kz_two]
    exact not_le_derivative_Kz_two p.asIdeal
  · exact absurd rfl hj

/-- On the `w₂`-chart the order-`2` locus of `I₂` is the origin `q'`, at every scheme point. -/
theorem le_derivative_chartColon_Kz_three_iff (p : Spec (CommRingCat.of R4)) :
    Ideal.derivative ℚ (chartColon Kz 3) ≤ p.asIdeal ↔ p = origin ℚ 4 := by
  rw [chartColon_Kz_three]
  exact le_derivative_Kzw_iff p

/-- On the `w₃`-chart the origin `q''` has `ord I₃ ≥ 2` (`ord_zero_example106_zww`). -/
theorem le_derivative_chartColon_Kzw_three :
    Ideal.derivative ℚ (chartColon Kzw 3) ≤ (origin ℚ 4).asIdeal := by
  rw [chartColon_Kzw_three]
  have hle : Ideal.span {x ^ 3 * z * w ^ 4 - y ^ 2, z * (x ^ 4 * z * w ^ 8 + x - w)} ≤
      m0 ^ (1 + 1) := ord_zero_example106_zww.1
  have := Ideal.derivative_le_pow (k := ℚ) hle
  rwa [pow_one, m0_eq_origin_asIdeal] at this

/-! ### The order-2 run of `BO_{4,2}` has at least four blow-ups -/

/-- The `z`-chart of the blow-up of `𝔸⁴_ℚ` at the origin; Kollár's `q` is its origin. -/
noncomputable abbrev chartTwo : 𝔸⁴ ⟶ 𝔹ᵣ := (chart 2) ≫ (Φ).inv

/-- The `z`-chart is an open immersion. -/
instance isOpenImmersion_chartTwo : IsOpenImmersion chartTwo := by
  unfold chartTwo
  infer_instance

/-- Kollár's `q` is the origin of the `z`-chart. -/
theorem chartTwo_origin : chartTwo (origin ℚ 4) = qB := Scheme.Hom.comp_apply _ _ _

/-- On the `z`-chart the weak transform `I₁` is `V(K_z)`. -/
theorem comap_weakTransform_chartTwo
    [Smooth ((specIdealSheaf c44).subschemeι ≫ affineSpaceToSpec ℚ 4)]
    (hord : (specIdealSheaf I106).OrdAlongEq (specIdealSheaf c44).support ((2 : ℕ) : ℕ∞)) :
    ((specIdealSheaf I106).weakTransform (specIdealSheaf c44)).comap chartTwo =
      specIdealSheaf Kz := by
  rw [chartTwo, comap_comp, comap_weakTransform_inv hord, comap_modelW_modelChart, chartIdeal_two]

/-- For any smooth blow-up sequence for `(𝔸⁴_ℚ, I, E)` of order `2` with no empty centre and final
maximal order `< 2` (the three properties of the values of `BO_{4,2}`) that begins with the
blow-up of the origin, the tail has at least three blow-ups: the centres `Z₁ ∋ q` and `Z₂ ∋ q'` are
forced, and `I₃` still has the point `q''` of order `2`. Stated for a centre `J` equal to
`centerIdeal ℚ 4 4` so that `𝔪₀` may be passed. -/
theorem three_le_length_of_axioms (J : Ideal R4) (hJ : J = centerIdeal ℚ 4 4)
    (E : DivisorFamily 𝔸⁴) (rest : BlowUpSequence (specIdealSheaf J).blowUp)
    (hS : (cons _ (specIdealSheaf J) rest).IsOrderSeq (affineSpaceToSpec ℚ 4)
      (specIdealSheaf I106) E 2)
    (hne : (cons _ (specIdealSheaf J) rest).NoEmptyCenters)
    (hend : ((cons _ (specIdealSheaf J) rest).weakTransformSeq (specIdealSheaf I106)
      (Fin.last _)).maxOrd < ((2 : ℕ) : ℕ∞)) :
    3 ≤ rest.length := by
  subst hJ
  have hf4 := smoothOfRelativeDimension_affineSpaceToSpec
  -- stage 1 → 2: the centre `Z₁` is forced at `q`
  obtain ⟨⟨hsm, -, hord⟩, hrest⟩ := (isOrderSeq_cons_iff (f := affineSpaceToSpec ℚ 4)
    (I := specIdealSheaf I106) (E := E) (m := 2) _ _).mp hS
  have hne' := ((noEmptyCenters_cons_iff _ _).mp hne).2
  have hend' : (rest.weakTransformSeq ((specIdealSheaf I106).weakTransform (specIdealSheaf c44))
      (Fin.last _)).maxOrd < ((2 : ℕ) : ℕ∞) := hend
  have hsm' : Smooth ((specIdealSheaf c44).subschemeι ≫ affineSpaceToSpec ℚ 4) := hsm
  have hπ₀ : SmoothOfRelativeDimension 4
      ((specIdealSheaf c44).blowUpπ ≫ affineSpaceToSpec ℚ 4) :=
    smoothOfRelativeDimension_blowUpπ_comp_of_smooth _ 4 _
  obtain ⟨Z₁, rest', rfl, hsupp₁⟩ := exists_eq_cons_of_ord_le_iff rest
    ((specIdealSheaf c44).blowUpπ ≫ affineSpaceToSpec ℚ 4) _ _ 2 hrest hne' hend'
    isClosed_singleton_qB (two_le_ord_weakTransform_iff hord)
  -- the data of stage 2: on the `z`-chart, `Z₁` is the origin and `I₁ = V(K_z)`
  have hsupp₁' : ∀ q, q ∈ Z₁.support ↔ q = chartTwo (origin ℚ 4) := fun q => by
    rw [hsupp₁, chartTwo_origin]
    exact Set.mem_singleton_iff
  have hZ₁ : Z₁.comap chartTwo = specIdealSheaf c44 :=
    comap_eq_specIdealSheaf_centerIdeal chartTwo _ 4 Z₁ _ _ rest' hrest hsupp₁'
  have hI₁ := comap_weakTransform_chartTwo hord
  have hcos₁ : ∀ b : 𝔹ᵣ, ((2 : ℕ) : ℕ∞) ≤
      ((specIdealSheaf I106).weakTransform (specIdealSheaf c44)).ord b ↔
        b = chartTwo (origin ℚ 4) := by
    intro b
    rw [chartTwo_origin]
    exact two_le_ord_weakTransform_iff hord b
  obtain ⟨⟨hsm₁, -, hord₁⟩, hrest'⟩ := (isOrderSeq_cons_iff
    (f := (specIdealSheaf c44).blowUpπ ≫ affineSpaceToSpec ℚ 4)
    (I := (specIdealSheaf I106).weakTransform (specIdealSheaf c44))
    (E := E.totalTransform _) (m := 2) _ _).mp hrest
  have hne'' := ((noEmptyCenters_cons_iff _ _).mp hne').2
  have hend'' : (rest'.weakTransformSeq
      (((specIdealSheaf I106).weakTransform (specIdealSheaf c44)).weakTransform Z₁)
      (Fin.last _)).maxOrd < ((2 : ℕ) : ℕ∞) := hend'
  have hsm₁' : Smooth (Z₁.subschemeι ≫
      ((specIdealSheaf c44).blowUpπ ≫ affineSpaceToSpec ℚ 4)) := hsm₁
  -- stage 2 → 3: the centre `Z₂` is forced at `q'`
  obtain ⟨Z₂, rest'', rfl, hsupp₂⟩ := exists_eq_cons_step Z₁ _ chartTwo
    ((specIdealSheaf c44).blowUpπ ≫ affineSpaceToSpec ℚ 4) 4 hZ₁ Kz hI₁ hord₁
    (fun q hq => (hsupp₁' q).mp hq) hcos₁ 3 not_le_derivative_chartColon_Kz
    le_derivative_chartColon_Kz_three_iff rest' hrest' hne'' hend''
  -- the data of stage 3: on the `w₂`-chart of the open piece, `Z₂` is the origin, `I₂ = V(K_zw)`
  have hπ₁ : SmoothOfRelativeDimension 4 (Z₁.blowUpπ ≫
      ((specIdealSheaf c44).blowUpπ ≫ affineSpaceToSpec ℚ 4)) :=
    smoothOfRelativeDimension_blowUpπ_comp_of_smooth _ 4 _
  have hsupp₂' : ∀ q, q ∈ Z₂.support ↔ q = ((chart 3) ≫ stepMap Z₁ chartTwo hZ₁) (origin ℚ 4) := by
    intro q
    rw [Scheme.Hom.comp_apply]
    exact hsupp₂ q
  have hZ₂ : Z₂.comap ((chart 3) ≫ stepMap Z₁ chartTwo hZ₁) = specIdealSheaf c44 :=
    comap_eq_specIdealSheaf_centerIdeal ((chart 3) ≫ stepMap Z₁ chartTwo hZ₁) _ 4 Z₂ _ _ rest''
      hrest' hsupp₂'
  have hI₂ : (((specIdealSheaf I106).weakTransform (specIdealSheaf c44)).weakTransform Z₁).comap
      ((chart 3) ≫ stepMap Z₁ chartTwo hZ₁) = specIdealSheaf Kzw := by
    rw [comap_comp, weakTransform_comap_stepMap Z₁ _ chartTwo
      ((specIdealSheaf c44).blowUpπ ≫ affineSpaceToSpec ℚ 4) 4 hZ₁ Kz hI₁ hord₁,
      comap_modelWP_modelChart, chartColon_Kz_three]
  obtain ⟨⟨hsm₂, -, hord₂⟩, -⟩ := (isOrderSeq_cons_iff
    (f := Z₁.blowUpπ ≫ ((specIdealSheaf c44).blowUpπ ≫ affineSpaceToSpec ℚ 4))
    (I := ((specIdealSheaf I106).weakTransform (specIdealSheaf c44)).weakTransform Z₁)
    (E := (E.totalTransform _).totalTransform Z₁) (m := 2) _ _).mp hrest'
  have hend''' : (rest''.weakTransformSeq
      ((((specIdealSheaf I106).weakTransform (specIdealSheaf c44)).weakTransform Z₁).weakTransform
      Z₂)
      (Fin.last _)).maxOrd < ((2 : ℕ) : ℕ∞) := hend''
  have hsm₂' : Smooth (Z₂.subschemeι ≫ (Z₁.blowUpπ ≫
      ((specIdealSheaf c44).blowUpπ ≫ affineSpaceToSpec ℚ 4))) := hsm₂
  -- stage 3: `I₃` has the order-2 point `q''`, so the sequence goes on
  have hq'' := two_le_ord_weakTransform_stepMap Z₂ _ ((chart 3) ≫ stepMap Z₁ chartTwo hZ₁)
    (Z₁.blowUpπ ≫ ((specIdealSheaf c44).blowUpπ ≫ affineSpaceToSpec ℚ 4)) 4
        hZ₂ Kzw hI₂
    hord₂ 3 le_derivative_chartColon_Kzw_three
  have h1 := one_le_length_of_le_ord rest'' _ 2 hend''' hq''
  change 3 ≤ rest''.length + 1 + 1
  omega

/-- **Kollár's Example 106, continued**: every smooth blow-up sequence for `(𝔸⁴_ℚ, I, E)` of order
`2` with no empty centre and final maximal order `< 2` has at least four blow-ups; the origin, `q`
and `q'` are forced as centres and `q''` remains of order `2`. Where [Kol07, Example 106] passes to
the mark `1` after the first blow-up ("the order has dropped to 1"), the order-`2` run of `BO_{4,2}`
continues for at least three more blow-ups. -/
theorem four_le_length_of_axioms (S : BlowUpSequence 𝔸⁴) (E : DivisorFamily 𝔸⁴)
    (hS : S.IsOrderSeq (affineSpaceToSpec ℚ 4) (specIdealSheaf I106) E 2) (hne : S.NoEmptyCenters)
    (hend : (S.weakTransformSeq (specIdealSheaf I106) (Fin.last _)).maxOrd < ((2 : ℕ) : ℕ∞)) :
    4 ≤ S.length := by
  obtain ⟨rest, rfl⟩ := exists_eq_cons_specIdealSheaf_m0 S E hS hne hend
  have := three_le_length_of_axioms m0 centerIdeal_eq_m0.symm E rest hS hne hend
  change 4 ≤ rest.length + 1
  omega

end Hironaka.Examples.Example106BO
