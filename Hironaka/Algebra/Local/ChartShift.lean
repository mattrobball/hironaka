/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.BirationalTransform
import Hironaka.Algebra.Local.Chart
import Hironaka.Algebra.Local.Transform

/-!
# The chart of the shifted coordinates

Kollár's linear change of the `(x₁, …, x_r)`-coordinates that moves the origin of the chart to
another point of the exceptional fibre (the proof of [Kol07, Lemma 61]): for `a ∈ Kʳ` with lifts
`ãᵢ ∈ R`, the coordinates `x'ᵢ = xᵢ − ãᵢ x_r` (`i < r`), `x'ⱼ = xⱼ` (`j ≥ r`) generate `𝔪` and `P`,
define the same chart ring (`x'ᵢ/x_r = yᵢ − ãᵢ`), and the origin of their chart is the point
`𝔪'_a = ⟨yᵢ − ãᵢ, x_r, xⱼ⟩` of the fibre.  `Hironaka/Algebra/Local/Chart.lean` proves this with the
denominator as a parameter (`chartRingOf x' r (x r) = chartRing x r`, `chartOriginAt`).  For
Lemma 61 at `𝔪'_a` (`Hironaka/Algebra/Local/Lemma61.lean`) the statements about the chart of `x'` —
its origin, its local ring, its Cohen structure — are stated for `chartRing x' r`, whose ambient
ring is `R[1/x'_r]`; this file provides the `R`-algebra isomorphism
`chartRingEquivShift : chartRing x' r ≃ₐ[R] chartRing x r` (through `R[1/x'_r] ≃ R[1/x_r]`,
`x'_r = x_r`) and computes it on the generators: `yᵢ' ↦ yᵢ − ãᵢ` (`i < r`), `yⱼ' ↦ yⱼ` (`j ≥ r`),
so that it carries the origin of the chart of `x'` onto `𝔪'_a`.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing

section Shift

variable {R : Type*} [CommRing R] {n : ℕ} (x : Fin n → R) (r : Fin n) (a : Fin n → R)

theorem powers_shiftCoords_self :
    Submonoid.powers (shiftCoords x r a r) = Submonoid.powers (x r) := by
  rw [shiftCoords_self]

/-- `R[1/x_r]` is also the localization at the powers of `x'_r = x_r`. -/
theorem isLocalization_powers_shiftCoords :
    IsLocalization (Submonoid.powers (shiftCoords x r a r)) (Localization.Away (x r)) := by
  rw [powers_shiftCoords_self]
  infer_instance

/-- The identification `R[1/x'_r] ≃ R[1/x_r]` (`x'_r = x_r`). -/
noncomputable def awayEquivShift :
    Localization.Away (shiftCoords x r a r) ≃ₐ[R] Localization.Away (x r) :=
  haveI := isLocalization_powers_shiftCoords x r a
  IsLocalization.algEquiv (Submonoid.powers (shiftCoords x r a r)) _ _

theorem awayEquivShift_algebraMap (b : R) :
    awayEquivShift x r a (algebraMap R _ b) = algebraMap R _ b :=
  (awayEquivShift x r a).commutes b

theorem awayEquivShift_mk (b : R) :
    awayEquivShift x r a (Localization.mk b ⟨shiftCoords x r a r, Submonoid.mem_powers _⟩) =
      Localization.mk b ⟨x r, Submonoid.mem_powers _⟩ := by
  have hxr : algebraMap R (Localization.Away (x r)) (x r) =
      algebraMap R (Localization.Away (x r)) (shiftCoords x r a r) := by
    rw [shiftCoords_self]
  have h1 : awayEquivShift x r a
      (Localization.mk b ⟨shiftCoords x r a r, Submonoid.mem_powers _⟩) *
        algebraMap R (Localization.Away (x r)) (x r) = algebraMap R _ b := by
    rw [hxr, ← awayEquivShift_algebraMap, ← map_mul, Localization.mk_eq_mk',
      IsLocalization.mk'_spec, awayEquivShift_algebraMap]
  have h2 : Localization.mk b ⟨x r, Submonoid.mem_powers _⟩ *
      algebraMap R (Localization.Away (x r)) (x r) = algebraMap R _ b := by
    rw [Localization.mk_eq_mk', IsLocalization.mk'_spec]
  exact (IsLocalization.map_units (Localization.Away (x r))
    ⟨x r, Submonoid.mem_powers _⟩).mul_right_cancel (h1.trans h2.symm)

/-- The identification carries the chart ring of `x'` onto the chart ring of `x`
(`chartRingOf_shiftCoords`). -/
theorem map_chartRing_awayEquivShift :
    (chartRing (shiftCoords x r a) r).map (awayEquivShift x r a : _ →ₐ[R] _) = chartRing x r := by
  rw [← chartRingOf_shiftCoords x r a, chartRing, chartRingOf, AlgHom.map_adjoin, Set.image_image]
  congr 1
  refine Set.image_congr fun i _ => ?_
  exact awayEquivShift_mk x r a (shiftCoords x r a i)

/-- The equality of the two chart rings as an isomorphism of `R`-algebras:
`chartRing x' r ≃ chartRing x r`. -/
noncomputable def chartRingEquivShift : chartRing (shiftCoords x r a) r ≃ₐ[R] chartRing x r :=
  ((awayEquivShift x r a).subalgebraMap (chartRing (shiftCoords x r a) r)).trans
    (Subalgebra.equivOfEq _ _ (map_chartRing_awayEquivShift x r a))

theorem coe_chartRingEquivShift (z : chartRing (shiftCoords x r a) r) :
    (chartRingEquivShift x r a z : Localization.Away (x r)) = awayEquivShift x r a z := rfl

theorem chartRingEquivShift_algebraMap (b : R) :
    chartRingEquivShift x r a (algebraMap R _ b) = algebraMap R _ b :=
  (chartRingEquivShift x r a).commutes b

/-- `yᵢ' ↦ yᵢ − ãᵢ` for `i < r`. -/
theorem chartRingEquivShift_chartYR_of_lt {i : Fin n} (hi : i < r) :
    chartRingEquivShift x r a (chartYR (shiftCoords x r a) r i) =
      chartYR x r i - algebraMap R _ (a i) := by
  apply Subtype.ext
  rw [coe_chartRingEquivShift, coe_chartYROf, chartYOf_of_lt _ _ _ hi, awayEquivShift_mk,
    Subalgebra.coe_sub, Subalgebra.coe_algebraMap, coe_chartYROf, chartYOf_of_lt _ _ _ hi]
  exact mk_shiftCoords_of_lt x r a hi

/-- `yⱼ' ↦ yⱼ` for `j ≥ r`. -/
theorem chartRingEquivShift_chartYR_of_not_lt {j : Fin n} (hj : ¬ j < r) :
    chartRingEquivShift x r a (chartYR (shiftCoords x r a) r j) = chartYR x r j := by
  apply Subtype.ext
  rw [coe_chartRingEquivShift, coe_chartYROf, chartYOf_of_not_lt _ _ _ hj,
    awayEquivShift_algebraMap, coe_chartYROf, chartYOf_of_not_lt _ _ _ hj,
    shiftCoords_of_not_lt _ _ _ hj]

/-- The isomorphism carries the origin of the chart of `x'` onto the point `𝔪'_a` (`𝔪'_a` is the
origin of the chart for `x'`, `mem_chartOriginAt_iff`). -/
theorem map_chartOrigin_chartRingEquivShift :
    (chartOrigin (shiftCoords x r a) r).map (chartRingEquivShift x r a) = chartOriginAt x r a := by
  have hf : (chartRingEquivShift x r a) ∘ chartYR (shiftCoords x r a) r = fun i : Fin n =>
      if i < r then chartYR x r i - algebraMap R _ (a i) else chartYR x r i := by
    funext i
    simp only [Function.comp_apply]
    split_ifs with hi
    · exact chartRingEquivShift_chartYR_of_lt x r a hi
    · exact chartRingEquivShift_chartYR_of_not_lt x r a hi
  rw [chartOrigin, chartOriginOf, Ideal.map_span, chartOriginAt, ← Set.range_comp, hf]

theorem chartCenter_shiftCoords : chartCenter (shiftCoords x r a) r = chartCenter x r :=
  span_shiftCoords_le x r a

theorem chartRingEquivShift_comp_algebraMap :
    (chartRingEquivShift x r a : chartRing (shiftCoords x r a) r →+* chartRing x r).comp
      (algebraMap R (chartRing (shiftCoords x r a) r)) = algebraMap R (chartRing x r) :=
  RingHom.ext (chartRingEquivShift_algebraMap x r a)

/-- The transform does not depend on the coordinates: the isomorphism carries the transform of
`I` computed with `x'` onto the transform computed with `x`
(`eq_transformIdeal_of_map_chartCenter_pow_mul_eq`). -/
theorem map_transformIdeal_chartRingEquivShift {I : Ideal R} {m : ℕ}
    (hI : I ≤ chartCenter x r ^ m) :
    (transformIdeal (shiftCoords x r a) r I m).map
        (chartRingEquivShift x r a : chartRing (shiftCoords x r a) r →+* chartRing x r) =
      transformIdeal x r I m := by
  have hI' : I ≤ chartCenter (shiftCoords x r a) r ^ m := by rwa [chartCenter_shiftCoords]
  refine eq_transformIdeal_of_span_pow_mul_eq x r hI ?_
  have h := congrArg
    (Ideal.map (chartRingEquivShift x r a : chartRing (shiftCoords x r a) r →+* chartRing x r))
    (span_pow_mul_transformIdeal (shiftCoords x r a) r hI')
  rw [Ideal.map_mul, Ideal.map_pow, Ideal.map_span, Set.image_singleton, Ideal.map_map,
    chartRingEquivShift_comp_algebraMap] at h
  have hxr : algebraMap R (chartRing x r) (shiftCoords x r a r) =
      algebraMap R (chartRing x r) (x r) := by
    rw [shiftCoords_self]
  rw [← h, RingHom.coe_coe, chartRingEquivShift_algebraMap, hxr]

end Shift

section Localize

variable {R : Type*} [CommRing R] {n : ℕ} (x : Fin n → R) (r : Fin n) (a : Fin n → R)
  [(chartOrigin (shiftCoords x r a) r).IsPrime] [(chartOriginAt x r a).IsPrime]

theorem map_primeCompl_chartRingEquivShift :
    (chartOrigin (shiftCoords x r a) r).primeCompl.map
        (chartRingEquivShift x r a).toRingEquiv.toMonoidHom = (chartOriginAt x r a).primeCompl := by
  ext z
  have hmap : ∀ w, chartRingEquivShift x r a w ∈ chartOriginAt x r a ↔
      w ∈ chartOrigin (shiftCoords x r a) r := by
    intro w
    rw [← map_chartOrigin_chartRingEquivShift]
    constructor
    · intro hw
      obtain ⟨w', hw', hww'⟩ := Ideal.mem_map_iff_of_surjective _
        (chartRingEquivShift x r a).surjective |>.mp hw
      rwa [(chartRingEquivShift x r a).injective hww'] at hw'
    · exact fun hw => Ideal.mem_map_of_mem _ hw
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact fun hz => hw ((hmap w).mp hz)
  · intro hz
    refine ⟨(chartRingEquivShift x r a).symm z, fun hw => hz ?_,
      (chartRingEquivShift x r a).apply_symm_apply z⟩
    have := (hmap _).mpr hw
    rwa [AlgEquiv.apply_symm_apply] at this

/-- The isomorphism of the local rings at the origin of the chart of `x'` and at `𝔪'_a`. -/
noncomputable def localizationEquivShift :
    Localization.AtPrime (chartOrigin (shiftCoords x r a) r) ≃+*
      Localization.AtPrime (chartOriginAt x r a) :=
  IsLocalization.ringEquivOfRingEquiv _ _ (chartRingEquivShift x r a).toRingEquiv
    (map_primeCompl_chartRingEquivShift x r a)

theorem localizationEquivShift_algebraMap (z : chartRing (shiftCoords x r a) r) :
    localizationEquivShift x r a (algebraMap _ _ z) =
      algebraMap _ _ (chartRingEquivShift x r a z) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ z

theorem localizationEquivShift_algebraMap_R (b : R) :
    localizationEquivShift x r a (algebraMap R _ b) = algebraMap R _ b := by
  rw [IsScalarTower.algebraMap_apply R (chartRing (shiftCoords x r a) r),
    localizationEquivShift_algebraMap, chartRingEquivShift_algebraMap,
    ← IsScalarTower.algebraMap_apply R (chartRing x r)]

theorem map_transformIdeal_localizationEquivShift {I : Ideal R} {m : ℕ}
    (hI : I ≤ chartCenter x r ^ m) :
    ((transformIdeal (shiftCoords x r a) r I m).map
        (algebraMap _ (Localization.AtPrime (chartOrigin (shiftCoords x r a) r)))).map
        (localizationEquivShift x r a : _ →+* _) =
      (transformIdeal x r I m).map (algebraMap _ (Localization.AtPrime (chartOriginAt x r a))) := by
  rw [Ideal.map_map, ← map_transformIdeal_chartRingEquivShift x r a hI, Ideal.map_map]
  congr 1
  exact RingHom.ext (localizationEquivShift_algebraMap x r a)

end Localize

end IsLocalRing
