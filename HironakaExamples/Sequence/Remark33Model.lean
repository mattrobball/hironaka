/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Basic
import Hironaka.Scheme.BlowUp.Composite.ChartIdeal
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Kollár's Remark 33 on the affine model: two blow-up sequences with the same end result

Kollár's genuine counterexample to "the end result determines the sequence" [Kol07, Remark 33]:
for a smooth pointed curve `p ∈ C` in a smooth 3-fold `X_0`, blowing up `p` and then the
birational transform of `C` gives `Π : X_2 → X_1 = B_p X_0 → X_0` with exceptional divisors
`E_0, E_1 ⊂ X_2`, while blowing up `C` and then the preimage `D = σ_0⁻¹(p)` gives
`Σ : X_2' → X_1' = B_C X_0 → X_0`; the end results are isomorphic, `X_2 ≅ X_2'`, and under this
isomorphism `E_1` corresponds to `E_0'` and `E_0` to `E_1'`.

This module defines the two sequences on the affine model `X_0 = 𝔸³_k = Spec k[x, y, z]`,
`C = V(x, y)` (the `z`-axis) and `p = V(x, y, z)` (the origin), as terms of
`AlgebraicGeometry.Scheme.BlowUpSequence`, so that the isomorphism of the end results, the matching
of the exceptional divisors and the computations of Warning 63 can refer to them:

* `seqPointCurve k`: blow up `p`, then the birational (strict) transform of `C` in `B_p 𝔸³`;
* `seqCurvePoint k`: blow up `C`, then `σ_0⁻¹(p)`, the inverse image ideal sheaf of `p` in
  `B_C 𝔸³`.

Both have length `2`, and they are different terms because their first centers differ
(`seqPointCurve_ne_seqCurvePoint`, from `ne_of_center_zero_ne`: `z ∈ (x, y, z)` but
`z ∉ (x, y)`, `MvPolynomial.mem_ideal_span_X_image`). The isomorphism `X_2 ≅ X_2'` of the end
results is proved in `HironakaExamples/Sequence/Remark33Iso.lean`, and the matching of the
exceptional divisors in `HironakaExamples/Sequence/Remark33Exceptional.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial Scheme.IdealSheafData Scheme
  BlowUpSequence

namespace Hironaka.Sequence.Remark33

variable (k : Type u) [Field k]

/-- The affine 3-space `𝔸³_k = Spec k[x, y, z]`, with `x = X 0`, `y = X 1`, `z = X 2`. -/
noncomputable abbrev affine3 : Scheme.{u} := Spec (.of (MvPolynomial (Fin 3) k))

/-- The ideal `(x, y, z)` of the origin `p`. -/
noncomputable abbrev pointIdeal : Ideal (MvPolynomial (Fin 3) k) := Ideal.span (Set.range X)

/-- The ideal `(x, y)` of the `z`-axis `C`. -/
noncomputable abbrev curveIdeal : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span (X '' ({0, 1} : Set (Fin 3)))

/-- The origin `p = V(x, y, z) ⊂ 𝔸³_k` as an ideal sheaf. -/
noncomputable abbrev point : (affine3 k).IdealSheafData := specIdealSheaf (pointIdeal k)

/-- The `z`-axis `C = V(x, y) ⊂ 𝔸³_k` as an ideal sheaf. -/
noncomputable abbrev curve : (affine3 k).IdealSheafData := specIdealSheaf (curveIdeal k)

/-- The first process of [Kol07, Remark 33]: blow up `p`, then the birational transform of `C`. -/
noncomputable def seqPointCurve : BlowUpSequence (affine3 k) :=
  cons _ (point k) (cons _ ((curve k).strictTransform (point k)) (nil _))

/-- The second process of [Kol07, Remark 33]: blow up `C`, then `D = σ_0⁻¹(p)`. -/
noncomputable def seqCurvePoint : BlowUpSequence (affine3 k) :=
  cons _ (curve k) (cons _ ((point k).comap (curve k).blowUpπ) (nil _))

theorem length_seqPointCurve : (seqPointCurve k).length = 2 := rfl

theorem length_seqCurvePoint : (seqCurvePoint k).length = 2 := rfl

/-- `z ∈ (x, y, z)` but `z ∉ (x, y)`. -/
theorem pointIdeal_ne_curveIdeal : pointIdeal k ≠ curveIdeal k := by
  intro h
  have hz : (X 2 : MvPolynomial (Fin 3) k) ∈ curveIdeal k := h ▸ Ideal.subset_span ⟨2, rfl⟩
  rw [curveIdeal, mem_ideal_span_X_image] at hz
  obtain ⟨i, hi, hne⟩ := hz (Finsupp.single 2 1) (by simp [support_X])
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with rfl | rfl <;> simp at hne

theorem point_ne_curve : point k ≠ curve k := fun h =>
  pointIdeal_ne_curveIdeal k (specIdealSheaf_inj h)

/-- The two processes of [Kol07, Remark 33] are different sequences, their first centers being `p`
and `C`. -/
theorem seqPointCurve_ne_seqCurvePoint : seqPointCurve k ≠ seqCurvePoint k :=
  ne_of_center_zero_ne (point_ne_curve k)

/-! ### The exceptional divisors on the two end results

Kollár writes `E_0, E_1 ⊂ X_2` for the exceptional divisors of `Π` and `E_0', E_1' ⊂ X_2'` for
those of `Σ` [Kol07, Remark 33]: `E_1` (resp. `E_1'`) is the exceptional divisor of the second
blow-up, `E_0` (resp. `E_0'`) the birational (strict) transform under the second blow-up of the
exceptional divisor of the first. All four are reduced divisors, given here by their ideal
sheaves. -/

/-- `E_1 ⊂ X_2`: the exceptional divisor of the second blow-up of `Π` (the blow-up of the
birational transform of `C`). -/
noncomputable abbrev excSecondPointCurve : (seqPointCurve k).last.IdealSheafData :=
  (seqPointCurve k).exceptionalAt (1 : Fin 2)

/-- `E_0 ⊂ X_2`: the birational transform, under the second blow-up of `Π`, of the exceptional
divisor of the first blow-up (the blow-up of `p`). -/
noncomputable abbrev excFirstTransformPointCurve : (seqPointCurve k).last.IdealSheafData :=
  ((seqPointCurve k).exceptionalAt (0 : Fin 2)).strictTransform ((seqPointCurve k).center
      (1 : Fin 2))

/-- `E_1' ⊂ X_2'`: the exceptional divisor of the second blow-up of `Σ` (the blow-up of
`D = σ_0⁻¹(p)`). -/
noncomputable abbrev excSecondCurvePoint : (seqCurvePoint k).last.IdealSheafData :=
  (seqCurvePoint k).exceptionalAt (1 : Fin 2)

/-- `E_0' ⊂ X_2'`: the birational transform, under the second blow-up of `Σ`, of the exceptional
divisor of the first blow-up (the blow-up of `C`). -/
noncomputable abbrev excFirstTransformCurvePoint : (seqCurvePoint k).last.IdealSheafData :=
  ((seqCurvePoint k).exceptionalAt (0 : Fin 2)).strictTransform ((seqCurvePoint k).center
      (1 : Fin 2))

end Hironaka.Sequence.Remark33
