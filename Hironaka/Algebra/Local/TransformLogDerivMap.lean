/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.TransformLogDeriv
public import Hironaka.Scheme.IdealSheaf.Derivative.Logarithmic
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The chart logarithmic derivative ideal under a ring map carrying the transformed derivations

The logarithmic counterpart of `Hironaka/Algebra/Local/TransformDerivMap.lean`, for [Kol07, (87.3)]
("proved the same way using (75.4)"): the chart logarithmic derivative ideal
`chartDlog r h K = K + y_h ∂'_h K + ∑_{j ≠ h} ∂'_j K` of
`Hironaka/Algebra/Local/TransformLogDeriv.lean` maps, under a ring homomorphism `χ` carrying the
transported derivations `∂'ⱼ` to derivations `δ j` of the target, into the logarithmic derivative
ideal `D(−log (χ y_h))(χ K)` of the target (`Ideal.logDerivative`,
`Hironaka/Scheme/IdealSheaf/Derivative/Logarithmic.lean`), provided the `δ j`, `j ≠ h`, preserve the
ideal `(χ y_h)` (`map_chartDlog_le_logDerivative`); the derivation `χ(y_h) • δ h` always preserves
`(χ y_h)`. On a manifold the `δ j` are the partial derivatives of a blow-up chart and `χ y_h` is one
of its coordinates, killed by the other partials. Iterating gives the statement for `chartDlogpow`
(`map_chartDlogpow_le_logDerivativeIter`).

Also here, a converse of `map_chartD_le_derivative`: if every `k`-derivation of the target is,
pointwise, a combination of the `δ j`, then `D(χ K) ⊆ χ(D' K)`
(`derivative_map_le_map_chartD_of_span`) and `D^s(χ K) ⊆ χ(D'^s K)`
(`derivativeIter_map_le_map_iterate_chartD_of_span`); this is how the chart-level inclusion `⊆` of
[Kol07, (88.1)] (`Hironaka/Algebra/Local/TransformDerivNormalForm.lean`) is read on the stalks of a
blow-up of a manifold.

Used in `Hironaka/Manifold/BlowUp/Transform/LogDerivBlowUp.lean`.
-/

public section

namespace IsLocalRing.RegularCoords

variable {k : Type*} [CommRing k] {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R]
  [Algebra k R] {n : ℕ} (c : RegularCoords R n) (r : Fin n)
  {S : Type*} [CommRing S] [Algebra k S]

omit [Algebra k R] in
/-- The logarithmic counterpart of `map_chartD_le_derivative` ([Kol07, (87.3)] at the chart
level): if `χ` carries the transported derivations `∂'_j` to derivations `δ j` of `S`, and the
`δ j` for `j ≠ h` preserve the ideal `(χ y_h)`, then `χ(D'(−log y_h)(K)) ⊆ D(−log (χ y_h))(χ K)`. -/
theorem map_chartDlog_le_logDerivative (χ : chartRing c.x r →+* S)
    (δ : Fin n → Derivation k S S)
    (hδ : ∀ (j : Fin n) (g : chartRing c.x r), χ (c.chartDerivRing r j g) = δ j (χ g))
    (h : Fin n) (hpres : ∀ j, j ≠ h → (δ j).PreservesIdeal (Ideal.span {χ (chartYR c.x r h)}))
    (K : Ideal (chartRing c.x r)) :
    Ideal.map χ (c.chartDlog r h K) ≤
      Ideal.logDerivative k (Ideal.span {χ (chartYR c.x r h)}) (Ideal.map χ K) := by
  rw [Ideal.map_le_iff_le_comap]
  unfold chartDlog
  refine sup_le (sup_le ?_ (Ideal.span_le.mpr ?_)) (iSup_le fun j => iSup_le fun hj =>
    Ideal.span_le.mpr ?_)
  · exact Ideal.le_comap_map.trans (Ideal.comap_mono (Ideal.le_logDerivative (k := k) _ _))
  · rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, map_mul, hδ]
    have hpres_h : (χ (chartYR c.x r h) • δ h).PreservesIdeal
        (Ideal.span {χ (chartYR c.x r h)}) := by
      rw [Derivation.preservesIdeal_span_singleton_iff, Derivation.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    have := Ideal.derivation_apply_mem_logDerivative hpres_h (Ideal.mem_map_of_mem χ hg)
    simpa only [Derivation.smul_apply, smul_eq_mul] using this
  · rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, hδ]
    exact Ideal.derivation_apply_mem_logDerivative (hpres j hj) (Ideal.mem_map_of_mem χ hg)

omit [Algebra k R] in
/-- The iterated form: `χ(D'^j(−log y_h)(K)) ⊆ D^j(−log (χ y_h))(χ K)`. -/
theorem map_chartDlogpow_le_logDerivativeIter (χ : chartRing c.x r →+* S)
    (δ : Fin n → Derivation k S S)
    (hδ : ∀ (j : Fin n) (g : chartRing c.x r), χ (c.chartDerivRing r j g) = δ j (χ g))
    (h : Fin n) (hpres : ∀ j, j ≠ h → (δ j).PreservesIdeal (Ideal.span {χ (chartYR c.x r h)}))
    (j : ℕ) (K : Ideal (chartRing c.x r)) :
    Ideal.map χ (c.chartDlogpow r h j K) ≤
      Ideal.logDerivativeIter k (Ideal.span {χ (chartYR c.x r h)}) j (Ideal.map χ K) := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    rw [chartDlogpow_succ, Ideal.logDerivativeIter_succ]
    exact (map_chartDlog_le_logDerivative c r χ δ hδ h hpres _).trans
      (Ideal.logDerivative_mono (k := k) ih)

/-! ### A converse of `map_chartD_le_derivative` under a spanning hypothesis -/

omit [Algebra k R] in
/-- A converse of `map_chartD_le_derivative`, used to read the inclusion `⊆` of [Kol07, (88.1)] in
the chart: if `χ` carries the transported derivations `∂'_j` to derivations `δ j` of `S` and every
`k`-derivation of `S` is, pointwise, an `S`-combination of the `δ j` (as the partial derivatives of
a chart of a manifold are), then `D(χ K) ⊆ χ(D' K)`. -/
theorem derivative_map_le_map_chartD_of_span (χ : chartRing c.x r →+* S)
    (δ : Fin n → Derivation k S S)
    (hδ : ∀ (j : Fin n) (g : chartRing c.x r), χ (c.chartDerivRing r j g) = δ j (χ g))
    (hspan : ∀ (D : Derivation k S S) (f : S), ∃ a : Fin n → S, D f = ∑ j, a j * δ j f)
    (K : Ideal (chartRing c.x r)) :
    Ideal.derivative k (Ideal.map χ K) ≤ Ideal.map χ (c.chartD r K) := by
  rw [Ideal.derivative_le_iff]
  refine ⟨Ideal.map_mono (c.le_chartD r K), fun D f hf => ?_⟩
  have hf' : f ∈ Ideal.span (χ '' (K : Set (chartRing c.x r))) := hf
  clear hf
  induction hf' using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, hg, rfl⟩ := hf
    obtain ⟨a, ha⟩ := hspan D (χ g)
    rw [ha]
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ ?_
    rw [← hδ]
    exact Ideal.mem_map_of_mem χ (c.chartDerivRing_mem_chartD r hg j)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x hx hDx =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_left _ _ hDx)
      (Ideal.mul_mem_right _ _ (Ideal.map_mono (c.le_chartD r K) hx))

omit [Algebra k R] in
/-- The iterated form of `derivative_map_le_map_chartD_of_span`: `D^s(χ K) ⊆ χ(D'^s K)`. -/
theorem derivativeIter_map_le_map_iterate_chartD_of_span (χ : chartRing c.x r →+* S)
    (δ : Fin n → Derivation k S S)
    (hδ : ∀ (j : Fin n) (g : chartRing c.x r), χ (c.chartDerivRing r j g) = δ j (χ g))
    (hspan : ∀ (D : Derivation k S S) (f : S), ∃ a : Fin n → S, D f = ∑ j, a j * δ j f) (s : ℕ)
    (K : Ideal (chartRing c.x r)) :
    Ideal.derivativeIter k s (Ideal.map χ K) ≤ Ideal.map χ ((c.chartD r)^[s] K) := by
  induction s with
  | zero => exact le_rfl
  | succ s ih =>
    rw [Ideal.derivativeIter_succ, Function.iterate_succ_apply']
    exact (Ideal.derivative_mono ih).trans (derivative_map_le_map_chartD_of_span c r χ δ hδ hspan _)

end IsLocalRing.RegularCoords
