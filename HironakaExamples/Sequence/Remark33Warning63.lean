/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Smooth.Graph
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import HironakaExamples.Sequence.Remark33Iso
import Hironaka.Resolution.Algebraic.Kol07.Warning63
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Membership
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.Smooth.BlowUpSmoothChart
import Hironaka.Scheme.Smooth.Origin
import HironakaExamples.Sequence.Remark33Exceptional
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Warning 63 on the model of Remark 33: the transforms along `Π` and the order dichotomy

[Kol07, Warning 63] compares the marked transforms of `(I_C, 1)` along the two sequences of
Remark 33 on `𝔸³_k`: `Π` (blow up the origin `p`, then the birational transform `C'` of the
`z`-axis `C`) and `Σ` (blow up `C`, then `D = σ_0⁻¹(p)`).
`HironakaExamples/Sequence/Warning63.lean` computes the values along `Σ` (`𝒪` at both stages); this
module computes the values along `Π` and proves the dichotomy: `Π` is a smooth blow-up sequence of
order `≥ 1` for `(𝔸³, I_C, 1, ∅)` and `Σ` is not, although `Π = Σ` as morphisms.

* **The first transform along `Π`.** `(π_0)_*⁻¹(I_C, 1) = C'`: the marked transform is the colon
  `(π_0^* I_C : E_0)`, and `π_0^* I_C = E_0 · C'` is the key identity of
  `HironakaExamples/Sequence/Remark33Iso.lean` (`curve_comap_eq`), so the colon is `C'` by the
  uniqueness clause of [Kol07, Definition 60] (`eq_markedTransform_of_pow_mul_eq`).
* **The end value along `Π`** is `(π_1)_*⁻¹(C', 1) = (E_1 : E_1) = 𝒪` (`markedTransform_self`).
* **`Σ` is not of order `≥ 1`.** Along `Σ` the second stage carries the marked ideal
  `(σ_0)_*⁻¹(I_C, 1) = 𝒪`, whose order along the center `D` is `0 < 1`; `D` is nonempty because
  the origin of the model's `x`-chart of `B_C 𝔸³` lies over `p`.
* **`Π` is of order `≥ 1`.** The six clauses of Definition 66 for `Π`: the centers `p` and `C'`
  are smooth over `k`, the total transforms of the empty family have simple normal crossings with
  them, and the marked ideals `I_C` and `C'` have order `≥ 1` along `p` and `C'`
  (`HironakaExamples/Sequence/Remark33OrderSeq.lean`). Two general lemmas serve here and later: the
  empty family has snc with every smooth center (adapted parameters,
  `exists_adaptedParameters_of_smooth`), and `ord_Z I ≥ 1` whenever `I ≤ Z`.

The two general lemmas (`hasSncWith_empty_of_smooth`, `leOrdAlong_one_of_le`) are in the
library module `Hironaka/Resolution/Algebraic/Kol07/Remark33Warning63.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData
  Scheme BlowUpSequence CoordinateSubspace affineBlowUpAlgebra Hironaka.Sequence.Remark33
  AlgebraicGeometry.Scheme.IdealSheafData MvPolynomial

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### The values along `Π` -/

section Model

variable (k : Type u) [Field k]

/-- The first transform along `Π` in [Kol07, Warning 63]: `(π_0)_*⁻¹(I_C, 1) = C'`, since
`π_0^* I_C = E_0 · C'` (`curve_comap_eq`). -/
theorem markedTransform_point_curve :
    (curve k).markedTransform (point k) 1 = (curve k).strictTransform (point k) := by
  refine (eq_markedTransform_of_pow_mul_eq (point k) (curve k) 1
    ((curve k).strictTransform (point k)) ?_).symm
  rw [pow_one]
  exact (curve_comap_eq k).symm

theorem markedTransformSeq_seqPointCurve_one :
    (seqPointCurve k).markedTransformSeq (curve k) 1
        ⟨1, Nat.lt_succ_of_lt (Nat.lt_of_lt_of_eq one_lt_two (length_seqPointCurve k).symm)⟩ =
      (curve k).strictTransform (point k) := by
  change (curve k).markedTransform (point k) 1 = (curve k).strictTransform (point k)
  exact markedTransform_point_curve k

/-- The end value along `Π` in [Kol07, Warning 63] is the unit ideal,
`(π_1)_*⁻¹(C', 1) = (E_1 : E_1) = 𝒪`. -/
theorem markedTransformSeq_seqPointCurve :
    (seqPointCurve k).markedTransformSeq (curve k) 1 (Fin.last 2) = ⊤ := by
  change ((curve k).markedTransform (point k) 1).markedTransform ((curve k).strictTransform
      (point k)) 1 = ⊤
  rw [markedTransform_point_curve]
  exact markedTransform_self _

/-! ### The order dichotomy: `Σ` is not of order `≥ 1` -/

/-- A point `𝔭` of `Spec R` lies in the support of the ideal sheaf of `J` iff `J ⊆ 𝔭`. -/
theorem mem_support_specIdealSheaf_iff {R : Type u} [CommRing R] (J : Ideal R)
    (y : Spec (.of R)) : y ∈ (specIdealSheaf J).support ↔ J ≤ y.asIdeal := by
  have hbij : Function.Bijective (Scheme.ΓSpecIso (.of R)).inv.hom :=
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective
  rw [mem_support_iff_of_mem (U := ⟨⊤, isAffineOpen_top _⟩) trivial, specIdealSheaf,
    ofIdealTop_ideal_top, Spec_zeroLocus]
  constructor
  · intro h a ha
    have h' := (PrimeSpectrum.mem_zeroLocus (R := R) y _).mp h
    have hmem : (Scheme.ΓSpecIso (.of R)).inv a ∈
        J.map (Scheme.ΓSpecIso (.of R)).inv.hom := Ideal.mem_map_of_mem _ ha
    exact h' hmem
  · intro hJ
    refine (PrimeSpectrum.mem_zeroLocus (R := R) y _).mpr fun a ha => ?_
    have h : a ∈ (J.map (Scheme.ΓSpecIso (.of R)).inv.hom).comap
        (Scheme.ΓSpecIso (.of R)).inv.hom := ha
    rw [Ideal.comap_map_of_bijective _ hbij] at h
    exact hJ h

/-- A point `𝔭` of `Spec R` lies in the support of the ideal sheaf of `J` when `J ⊆ 𝔭`. -/
theorem mem_support_specIdealSheaf_of_le {R : Type u} [CommRing R] (J : Ideal R)
    (y : Spec (.of R)) (hJ : J ≤ y.asIdeal) : y ∈ (specIdealSheaf J).support :=
  (mem_support_specIdealSheaf_iff J y).mpr hJ

/-- `D = σ_0⁻¹(p)` is nonempty: the origin of the model's `x`-chart of `B_C 𝔸³` lies over `p`
(the chart substitution `x ↦ x`, `y ↦ yx`, `z ↦ z` sends `(x, y, z)` into the origin). -/
theorem exists_mem_support_comap_π_Zs :
    ∃ z : IdealSheafData.blowUp (Ys k), z ∈ ((Zs k).comap (IdealSheafData.blowUpπ
        (Ys k))).support := by
  obtain ⟨e, he⟩ := exists_iso_blowUp_coordinateSubspace k 3 2
  refine ⟨e.inv (modelChart k 3 2 0 (by decide) (origin k 3)), ?_⟩
  rw [support_comap]
  change IdealSheafData.blowUpπ (Ys k) (e.inv (modelChart k 3 2 0 (by decide) (origin k 3))) ∈
      (Zs k).support
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← he, Iso.inv_hom_id_assoc, modelChart_π,
    Spec.map_apply]
  refine mem_support_specIdealSheaf_of_le _ _ ?_
  rw [centerIdeal, coordinateIdeal, Ideal.span_le]
  rintro _ ⟨i, -, rfl⟩
  change subst2 k 0 (X i) ∈ (origin k 3).asIdeal
  rw [subst2_X]
  split_ifs
  · exact Ideal.mul_mem_right _ _ (X_mem_origin_asIdeal k 3 i)
  · exact X_mem_origin_asIdeal k 3 i

/-- `Σ` is not a sequence of order `≥ 1` for `(𝔸³, I_C, 1, ∅)` (stated for the coordinate
subspaces): at its second stage the marked ideal is `𝒪` (`markedTransform_self`), whose order
along the nonempty center `D` is `0 < 1`. -/
theorem not_isOrderGeSeq_aux {p C : (Spec (.of (MvPolynomial (Fin 3) k))).IdealSheafData}
    (hp : p = Zs k) (hC : C = Ys k) :
    ¬ (cons _ C (cons _ (p.comap C.blowUpπ) (nil _))).IsOrderGeSeq
        (affineSpaceToSpec k 3) C 1
      (DivisorFamily.empty _) := by
  subst hp hC
  intro h
  rw [isOrderGeSeq_cons_iff, isOrderGeSeq_cons_iff] at h
  have hord := h.2.1.2.2
  rw [markedTransform_self] at hord
  obtain ⟨z, hz⟩ := exists_mem_support_comap_π_Zs k
  obtain ⟨η, hη, -⟩ := Closeds.exists_mem_genericPoints_specializes _ hz
  have h1 := hord η hη
  rw [ord_top, Nat.cast_one] at h1
  exact absurd h1 (not_le.mpr zero_lt_one)

/-- [Kol07, Warning 63]: `Σ` is not a smooth blow-up sequence of order `≥ 1` starting with
`(𝔸³, I_C, 1, ∅)`. -/
theorem not_isOrderGeSeq_seqCurvePoint :
    ¬ (seqCurvePoint k).IsOrderGeSeq (affineSpaceToSpec k 3) (curve k) 1
      (DivisorFamily.empty (affine3 k)) :=
  not_isOrderGeSeq_aux k (point_eq_coordinateSubspace k) (curve_eq_coordinateSubspace k)

end Model

end Hironaka.Sequence
