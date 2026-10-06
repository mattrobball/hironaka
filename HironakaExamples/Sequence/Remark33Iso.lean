/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import HironakaExamples.Sequence.Remark33Charts
public import HironakaExamples.Sequence.Remark33Model
public import Hironaka.Scheme.Smooth.EtaleCoordinatesDefs
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUp.Composite.ChartIdeal
import Hironaka.Scheme.BlowUp.Glue.Product
import Hironaka.Scheme.BlowUp.InverseImage
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUp.Transform.TransformIso
import Hironaka.Scheme.BlowUp.Transform.WeakTransform
import Hironaka.Scheme.BlowUpSequence.Remark33Iso
import Hironaka.Scheme.Smooth.BlowUpSmoothChart
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Remark 33 on the affine model: the isomorphism of end results

[Kol07, Remark 33]: blowing up `𝔸³` at the origin `p` and then along the birational transform `C'`
of the `z`-axis `C`, or first along `C` and then along `D = σ_0⁻¹(p)`, gives isomorphic end
results. "It is easy to see" made explicit:

* `X_2' = B_D(B_C 𝔸³)` is the blow-up of `𝔸³` along `C · p` (`blowUp.exists_mulIso`: blowing up
  the inverse image of `p` on `B_C 𝔸³` is blowing up the product `C · p` on `𝔸³`);
* `X_2 = B_{C'}(B_p 𝔸³)`, and **the total transform of `C` under the point blow-up is the
  exceptional divisor times the birational transform**, `C.comap π_0 = E_0 · C'`
  (`curve_comap_eq`): `C` passes through `p` with multiplicity one. This is the one computation of
  the module; it is checked on the three charts of the model blow-up
  (`HironakaExamples/Sequence/Remark33Charts.lean`) and transported along the isomorphism of the
  blow-up `blowUp` with the model (`exists_iso_blowUp_coordinateSubspace`). So blowing up `C'` is
  blowing up `C' · E_0 = C.comap π_0` (`blowUp.exists_mul_isInvertible_iso`: multiplying the center
  by an invertible ideal does not change the blow-up), which is the blow-up of `𝔸³` along
  `p · C = C · p` (`blowUp.exists_mulIso` again).

The chain of these isomorphisms over `𝔸³` is `exists_iso_last`.

**The saturation.** On the blow-up `B` of `p`, with exceptional ideal `E`, the birational transform
of `C` is the `E`-saturation `⨆ i (I : Eⁱ)` of the total transform `I = C.comap π_0`. Since
`C ⊆ p`, `I ⊆ E` and `I = E · (I : E)`; and the saturation stops after one step,
`(I : E²) = (I : E)`, because on the chart of `z` the ideal `I` is `(z) · (x, y)` with `(x, y)` a
prime not containing `z`, while on the charts of `x` and `y` it is the exceptional ideal itself
(`colon_map_le`). Hence `⨆ i (I : Eⁱ) = (I : E)` and `I = E · C'`. The chartwise inequality is
transported from the polynomial ring through the ring isomorphisms of the charts
(`comap_colon_of_isOpenImmersion`, `le_of_comap_le_of_iSup_eq_top`).

The ring-level and sheaf-level helpers (colons along ring maps and open immersions,
inequalities on covers) are in the library module `Hironaka/Scheme/BlowUpSequence/Remark33Iso.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData CoordinateSubspace MvPolynomial

namespace Hironaka.Sequence.Remark33

open AlgebraicGeometry.Remark33

/-! ### The model: `B_p 𝔸³` and its charts -/

variable (k : Type u) [Field k]

/-- The origin `p = V(x, y, z)` as a coordinate subspace (`coordinateSubspace`). -/
noncomputable abbrev Zs : (Spec (.of (MvPolynomial (Fin 3) k))).IdealSheafData :=
  coordinateSubspace k 3 3

/-- The `z`-axis `C = V(x, y)` as a coordinate subspace (`coordinateSubspace`). -/
noncomputable abbrev Ys : (Spec (.of (MvPolynomial (Fin 3) k))).IdealSheafData :=
  coordinateSubspace k 3 2

/-- The model blow-up `B_p 𝔸³` (`modelBlowUp`). -/
noncomputable abbrev M : Scheme.{u} := modelBlowUp k 3 3

/-- The projection of the model blow-up. -/
noncomputable abbrev πm : M k ⟶ Spec (.of (MvPolynomial (Fin 3) k)) :=
  affineBlowUp.π (centerIdeal k 3 3)

/-- The exceptional ideal of the model blow-up. -/
noncomputable abbrev Em : (M k).IdealSheafData := (Zs k).comap (πm k)

/-- The total transform of `C` on the model blow-up. -/
noncomputable abbrev Im : (M k).IdealSheafData := (Ys k).comap (πm k)

theorem Em_isInvertible : (Em k).IsInvertible :=
  affineBlowUp.isInvertible_exceptionalIdeal (centerIdeal k 3 3)

theorem centerIdeal_two_le : centerIdeal k 3 2 ≤ centerIdeal k 3 3 := by
  unfold centerIdeal affineBlowUpAlgebra.coordinateIdeal
  refine Ideal.span_mono (Set.image_mono fun i hi => ?_)
  change i.val < 3
  have h2 : i.val < 2 := hi
  omega

theorem Im_le_Em : Im k ≤ Em k :=
  comap_mono (πm k) ((specIdealSheaf_le_iff _ _).mpr (centerIdeal_two_le k))

/-- The chart of `x_j`. -/
noncomputable abbrev chart (j : Fin 3) : Spec (.of (MvPolynomial (Fin 3) k)) ⟶ M k :=
  modelChart k 3 3 j j.isLt

theorem iSup_opensRange_chart : ⨆ j : Fin 3, (chart k j).opensRange = ⊤ := by
  rw [← iSup_opensRange_modelChart k 3 3]
  exact iSup_congr fun j =>
    (iSup_pos (f := fun hj : j.val < 3 => (modelChart k 3 3 j hj).opensRange) j.isLt).symm

theorem chart_πm (j : Fin 3) :
    chart k j ≫ πm k = Spec.map (CommRingCat.ofHom (subst k j).toRingHom) :=
  modelChart_π k 3 3 j j.isLt

theorem Im_comap_chart (j : Fin 3) :
    (Im k).comap (chart k j) = specIdealSheaf (totalChart k j) := by
  rw [Im, ← comap_comp, chart_πm]
  exact comap_ofIdealTop_Spec_map _ _

theorem Em_comap_chart (j : Fin 3) :
    (Em k).comap (chart k j) = specIdealSheaf (excChart k j) := by
  rw [Em, ← comap_comp, chart_πm]
  exact comap_ofIdealTop_Spec_map _ _

theorem excChart_isInvertible (j : Fin 3) : (specIdealSheaf (excChart k j)).IsInvertible := by
  rw [excChart, map_centerIdeal_three_subst]
  exact isInvertible_specIdealSheaf_span_singleton (mem_nonZeroDivisors_of_ne_zero (X_ne_zero _))

/-- The saturation stops after one step on the model: `(I : E²) ≤ (I : E)`. -/
theorem Im_colon_sq_le : (Im k).colon (Em k ^ 2) ≤ (Im k).colon (Em k) := by
  refine le_of_comap_le_of_iSup_eq_top (chart k) (iSup_opensRange_chart k) fun j => ?_
  have hE1 := excChart_isInvertible k j
  have hE2 : (specIdealSheaf (excChart k j ^ 2)).IsInvertible := by
    rw [specIdealSheaf_pow]
    exact isInvertible_pow hE1 2
  rw [comap_colon_of_isOpenImmersion _ _ (isInvertible_pow (Em_isInvertible k) 2),
    comap_colon_of_isOpenImmersion _ _ (Em_isInvertible k), comap_pow, Im_comap_chart,
    Em_comap_chart, ← specIdealSheaf_pow, specIdealSheaf_colon _ _ hE2,
    specIdealSheaf_colon _ _ hE1, specIdealSheaf_le_iff]
  exact colon_map_le k j

theorem Im_colon_pow_succ_le (i : ℕ) : (Im k).colon (Em k ^ (i + 1)) ≤ (Im k).colon (Em k) := by
  induction i with
  | zero => rw [zero_add, pow_one]
  | succ i ih =>
    calc (Im k).colon (Em k ^ (i + 2)) = ((Im k).colon (Em k ^ (i + 1))).colon (Em k) := by
          rw [colon_colon, pow_succ]
      _ ≤ ((Im k).colon (Em k)).colon (Em k) := by
          apply colon_mono_left
          exact ih
      _ = (Im k).colon (Em k ^ 2) := by rw [colon_colon, pow_two]
      _ ≤ (Im k).colon (Em k) := Im_colon_sq_le k

/-- On the model, the birational transform of `C` is `(I : E)`. -/
theorem strictTransformAlong_πm_eq :
    (Ys k).strictTransformAlong (πm k) (Em k) = (Im k).colon (Em k) := by
  refine le_antisymm (iSup_le fun i => ?_) ?_
  · cases i with
    | zero =>
      rw [pow_zero, one_eq_top, colon_top]
      exact le_colon_self _ _
    | succ i => exact Im_colon_pow_succ_le k i
  · have := colon_pow_le_saturate (Im k) (Em k) 1
    rwa [pow_one] at this

/-- On the model: `I = E · (I : E)`. -/
theorem Em_mul_colon : Em k * (Im k).colon (Em k) = Im k := by
  have h := pow_mul_colon_of_dvd (Em k) 1 (I := Im k)
    (pow_dvd_of_le_pow_of_isInvertible (Em_isInvertible k) (by rw [pow_one]; exact Im_le_Em k))
  rwa [pow_one] at h

/-- The key identity on the model: the total transform of `C` is the exceptional ideal times the
birational transform. -/
theorem Im_eq_Em_mul_strictTransform :
    Im k = Em k * (Ys k).strictTransformAlong (πm k) (Em k) := by
  rw [strictTransformAlong_πm_eq, Em_mul_colon]

/-! ### Transport to the blow-up `blowUp` -/

/-- The key identity on `blowUp (coordinateSubspace k 3 3)`, the blow-up of `𝔸³` at `p`. -/
theorem coordinateSubspace_comap_eq :
    (Ys k).comap (blowUpπ (Zs k)) =
      (Zs k).comap (blowUpπ (Zs k)) *
        (Ys k).strictTransformAlong (blowUpπ (Zs k)) ((Zs k).comap (blowUpπ (Zs k))) := by
  obtain ⟨e, he⟩ := exists_iso_blowUp_coordinateSubspace k 3 3
  have hY : (Ys k).comap (blowUpπ (Zs k)) = (Im k).comap e.hom := by
    rw [← he]
    exact comap_comp _ _ _
  have hZ : (Zs k).comap (blowUpπ (Zs k)) = (Em k).comap e.hom := by
    rw [← he]
    exact comap_comp _ _ _
  rw [strictTransformAlong, hY, hZ, ← comap_saturate_of_isIso, ← comap_mul]
  exact congrArg (fun I : (M k).IdealSheafData => I.comap e.hom) (Im_eq_Em_mul_strictTransform k)

theorem point_eq_coordinateSubspace : point k = Zs k := by
  change specIdealSheaf (pointIdeal k) =
    specIdealSheaf (affineBlowUpAlgebra.coordinateIdeal k {j : Fin 3 | j.val < 3})
  congr 1
  rw [pointIdeal, affineBlowUpAlgebra.coordinateIdeal,
    show ({j : Fin 3 | j.val < 3} : Set (Fin 3)) = Set.univ from
      Set.eq_univ_of_forall fun j => j.isLt,
    Set.image_univ]

theorem curve_eq_coordinateSubspace : curve k = Ys k := by
  change specIdealSheaf (curveIdeal k) =
    specIdealSheaf (affineBlowUpAlgebra.coordinateIdeal k {j : Fin 3 | j.val < 2})
  congr 1
  rw [curveIdeal, affineBlowUpAlgebra.coordinateIdeal]
  congr 2
  ext i
  constructor
  · rintro (rfl | rfl)
    · exact (by decide : (0 : Fin 3).val < 2)
    · exact (by decide : (1 : Fin 3).val < 2)
  · intro hi
    have h2 : i.val < 2 := hi
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd h2 (by decide)

/-- **The total transform of `C` under the point blow-up is `E_0 · C'`** (the one computation
behind "it is easy to see" in [Kol07, Remark 33]), stated for the blow-up and strict transform
used throughout the library. -/
theorem curve_comap_eq :
    (curve k).comap (point k).blowUpπ =
      (point k).exceptionalDivisor *
        (curve k).strictTransform (point k) := by
  rw [point_eq_coordinateSubspace, curve_eq_coordinateSubspace]
  exact coordinateSubspace_comap_eq k

/-! ### The isomorphism of the end results -/

/-- `X_2 ≅ X_2'` over `𝔸³` [Kol07, Remark 33]. -/
theorem exists_iso_last :
    ∃ e : (seqPointCurve k).last ≅ (seqCurvePoint k).last,
      e.hom ≫ (seqCurvePoint k).composite = (seqPointCurve k).composite := by
  have hEinv : (point k).exceptionalDivisor.IsInvertible :=
    blowUp.isInvertible_comap_π (point k)
  have hkey : (curve k).strictTransform (point k) *
      (point k).exceptionalDivisor =
      (curve k).comap (blowUpπ (point k)) := by
    rw [mul_comm]
    exact (curve_comap_eq k).symm
  have hcomm : point k * curve k = curve k * point k := mul_comm _ _
  obtain ⟨e₁, he₁, -⟩ := blowUp.exists_mul_isInvertible_iso
    ((curve k).strictTransform (point k))
    (point k).exceptionalDivisor hEinv
  obtain ⟨e₂, he₂, -⟩ := blowUp.exists_mulIso (point k) (curve k)
  obtain ⟨e₃, he₃, -⟩ := blowUp.exists_mulIso (curve k) (point k)
  have he₃' : e₃.inv ≫ blowUpπ ((point k).comap (blowUpπ (curve k))) ≫ blowUpπ (curve k) =
      blowUpπ (curve k * point k) := by
    rw [← he₃, Iso.inv_hom_id_assoc]
  have he₁' : e₁.inv ≫ blowUpπ ((curve k).strictTransform (point k) *
      (point k).exceptionalDivisor) =
      blowUpπ ((curve k).strictTransform (point k)) := by
    rw [← he₁, Iso.inv_hom_id_assoc]
  have main : ∃ e : blowUp ((curve k).strictTransform (point k)) ≅
      blowUp ((point k).comap (blowUpπ (curve k))),
      e.hom ≫ blowUpπ ((point k).comap (blowUpπ (curve k))) ≫ blowUpπ (curve k) =
        blowUpπ ((curve k).strictTransform (point k)) ≫ blowUpπ (point k) := by
    refine ⟨e₁.symm ≪≫ eqToIso (congrArg blowUp hkey) ≪≫ e₂ ≪≫
      eqToIso (congrArg blowUp hcomm) ≪≫ e₃.symm, ?_⟩
    simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc]
    rw [he₃', eqToHom_comp_blowUpπ hcomm, he₂,
      eqToHom_comp_blowUpπ_assoc hkey, ← Category.assoc,
      he₁']
  obtain ⟨e, he⟩ := main
  refine ⟨e, ?_⟩
  change e.hom ≫ (𝟙 _ ≫ blowUpπ ((point k).comap (blowUpπ (curve k)))) ≫ blowUpπ (curve k) =
    (𝟙 _ ≫ blowUpπ ((curve k).strictTransform (point k))) ≫ blowUpπ (point k)
  rw [Category.id_comp, Category.id_comp]
  exact he

end Hironaka.Sequence.Remark33
