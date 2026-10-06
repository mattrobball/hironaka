/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Divisor
public import Hironaka.Manifold.BlowUp.Transform.Basic
import Hironaka.Manifold.BlowUp.Transform.Strict
import Hironaka.Manifold.BlowUp.Transform.StrictFlag
import Hironaka.Manifold.Chart.Transport
import Hironaka.Manifold.LocalDiffeomorph
import Hironaka.Manifold.Submanifold.Charts
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The strict transform of a smooth hypersurface is a smooth hypersurface

Under the chart-form hypothesis that the smooth hypersurface `H` is a coordinate hyperplane of a
chart adapted to the centre `Y` at every point of `H ∩ Y` (the form in which simple normal
crossings charts present the boundary), the strict transform `H' = closure (π⁻¹(H ∖ Y))` is a
closed submanifold of codimension one of the blow-up
(`isClosedSubmanifold_strictTransform_of_charts`): [BM97, §3, "The strict transform"], and the
local computation in the proof of [Kol07, Theorem 88]. At a point of `H'` over the centre, a
blow-up chart of index `i` over the adapted chart is adapted to `H'` with the single coordinate
`u_k` (centre index `k ≠ i`; `strictTransform_inter_source_of_ne`) or `w_j` (off-centre index,
`strictTransform_inter_source_off`); the chart of index `k` is excluded because `H'` misses it
(`strictTransform_inter_source_self`). Off the exceptional divisor, `π` is a local diffeomorphism
(`IsBlowUp.isLocalDiffeomorphOn_compl`) and `H' = π⁻¹(H)` there (the set forms of
`Hironaka.Manifold.BlowUp.Transform.Strict`), so an adapted chart of `H` transports along the
local inverse (`transportChart`, `isAdaptedChart_transportChart`) and is restricted to `π⁻¹(Yᶜ)`.
For `Y ⊆ H` the chart-form hypothesis is supplied by the pair-chart lemma
`exists_adaptedChart_pair`: at `a ∈ Y`, a defining function `h` of `H` vanishes on `Y`, so
`h = ∑_k g_k z_k` near `a` in the centre coordinates `z_k` of an adapted chart; its differential
`dh(a) = ∑_k g_k(a) dz_k(a)` is nonzero (`h` is a chart coordinate of `H`), so some
`g_{k₀}(a) ≠ 0`, the family `z` with `z_{k₀}` replaced by `h` has independent differentials, and
the chart completion `exists_chart_extending` (through `exists_adaptedChart_zeroSet'`) completes
it to a chart; where `g_{k₀} ≠ 0` its zero set is `Y` and `H = {h = 0}`: the pair chart. Hence
`isClosedSubmanifold_strictTransform`.

Codimension-`s` forms: for a closed submanifold `S ⊇ Y` of codimension `s`, the strict transform
`S'` is a closed submanifold of `M'` of codimension `s` (`IsClosedSubmanifold.strictTransform`;
the identification of the blow-up of `S` along `Y` with the birational transform of `S` is
[Kol07, Definition 30, 30.2]), over the centre by the flag chart (`exists_adaptedChart_flag` of
`Hironaka.Manifold.BlowUp.Transform.StrictFlag`, of which the pair lemma is the case `s = 1`)
and the chart lemmas in flag coordinates, off the centre by the transport
`exists_adaptedChart_strictTransform_off'`; the hypersurface statements are its instances.
-/

public section

open TopologicalSpace Opposite CategoryTheory Filter Topology IsLocalRing Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M}
  {c : ℕ} {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M} {H : Set M}

/-- A chart in which a set is the zero set of one coordinate is adapted to the set, with the single
index. -/
theorem isAdaptedChart_singleIdx {N : Type u} [TopologicalSpace N] [ChartedSpace E N]
    {e : OpenPartialHomeomorph N E} (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω N) {S : Set N} {k : Fin n}
    (hS : ∀ x ∈ e.source, x ∈ S ↔ ψ (e x) k = 0) : IsAdaptedChart ψ S e (singleEmb k) := by
  refine ⟨he, fun x hx => ?_⟩
  rw [hS x hx]
  exact ⟨fun h0 _ => h0, fun hall => hall 0⟩

/-- In codimension `s`: off the exceptional divisor the strict
transform of `S` is `π⁻¹(S)`, and an adapted chart of `S` at `π p` transports along the local
inverse of `π` to an adapted chart of `S'` at `p` with the coordinates `z ∘ π`; the hypersurface
form is `exists_adaptedChart_strictTransform_off`. -/
theorem exists_adaptedChart_strictTransform_off' {S : Set M} {s : ℕ}
    (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π) (hS : IsClosedSubmanifold ψ S s)
    {p : M'} (hpS : π p ∈ S)
    (hpY : π p ∉ Y) :
    ∃ (φ : OpenPartialHomeomorph M E) (σ₁ : Fin s ↪ Fin n) (e : OpenPartialHomeomorph M' E),
      π p ∈ φ.source ∧ IsAdaptedChart ψ S φ σ₁ ∧ p ∈ e.source ∧
        IsAdaptedChart ψ (strictTransformSet π Y S) e σ₁ ∧
        ∀ x ∈ e.source, ∀ j, ψ (e x) (σ₁ j) = ψ (φ (π x)) (σ₁ j) := by
  have hπc : Continuous π := h.contMDiff.continuous
  obtain ⟨Ψ, hpΨ, hEq⟩ := (h.isLocalDiffeomorphOn_compl ⟨p, hpY⟩).exists_partialDiffeomorph
  obtain ⟨φ, σ₁, hpφ, hφ⟩ := hS.exists_adaptedChart (π p) hpS
  have hg : Ψ.symm '' (S ∩ Ψ.symm.source) = π ⁻¹' S ∩ Ψ.symm.target := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyS, hy⟩, rfl⟩
      have hy' : y ∈ Ψ.target := hy
      refine ⟨?_, Ψ.toPartialEquiv.map_target hy'⟩
      change π (Ψ.toPartialEquiv.symm y) ∈ S
      rw [hEq (Ψ.toPartialEquiv.map_target hy'), Ψ.toPartialEquiv.right_inv hy']
      exact hyS
    · rintro ⟨hxS, hx⟩
      have hx' : x ∈ Ψ.source := hx
      refine ⟨Ψ x, ⟨?_, Ψ.toPartialEquiv.map_source hx'⟩, Ψ.toPartialEquiv.left_inv hx'⟩
      rw [← hEq hx']
      exact hxS
  have hT : IsAdaptedChart ψ (π ⁻¹' S) (transportChart Ψ.symm φ) σ₁ :=
    isAdaptedChart_transportChart Ψ.symm hg hφ
  have hopen : IsOpen (π ⁻¹' Yᶜ) := hY.isClosed.isOpen_compl.preimage hπc
  have hT' := hT.restrOpen' (π ⁻¹' Yᶜ) hopen
  refine ⟨φ, σ₁, (transportChart Ψ.symm φ).restrOpen (π ⁻¹' Yᶜ) hopen, hpφ, hφ, ?_,
    ⟨hT'.1, fun x hx => ?_⟩, fun x hx j => ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    refine ⟨⟨hpΨ, ?_⟩, hpY⟩
    change Ψ.toPartialEquiv p ∈ φ.source
    rw [← hEq hpΨ]
    exact hpφ
  · rw [← hT'.2 x hx]
    rw [OpenPartialHomeomorph.restrOpen_source] at hx
    have hxY : π x ∉ Y := hx.2
    exact ⟨fun hxS' => strictTransform_subset_preimage hπc hS.isClosed hxS',
      fun hxS => (preimage_subset_strictTransform_union hxS).resolve_right hxY⟩
  · rw [OpenPartialHomeomorph.restrOpen_source] at hx
    change ψ (φ (Ψ.toPartialEquiv.symm.symm x)) (σ₁ j) = ψ (φ (π x)) (σ₁ j)
    rw [PartialEquiv.symm_symm, hEq hx.1.1]

/-- Off the exceptional divisor the strict transform is `π⁻¹(H)`, and an adapted
chart of `H` at `π p` transports along the local inverse of `π` to an adapted chart of `H'` at `p`
whose coordinate is `h ∘ π`, `h` the coordinate of the chart of `H`. -/
theorem exists_adaptedChart_strictTransform_off
    (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π) (hH : IsClosedSubmanifold ψ H 1)
    {p : M'} (hpH : π p ∈ H) (hpY : π p ∉ Y) :
    ∃ (φ : OpenPartialHomeomorph M E) (σ₁ : Fin 1 ↪ Fin n) (e : OpenPartialHomeomorph M' E),
      π p ∈ φ.source ∧ IsAdaptedChart ψ H φ σ₁ ∧ p ∈ e.source ∧
        IsAdaptedChart ψ (strictTransformSet π Y H) e σ₁ ∧
        ∀ x ∈ e.source, ψ (e x) (σ₁ 0) = ψ (φ (π x)) (σ₁ 0) := by
  obtain ⟨φ, σ₁, e, h1, h2, h3, h4, h5⟩ :=
    exists_adaptedChart_strictTransform_off' hY h hH hpH hpY
  exact ⟨φ, σ₁, e, h1, h2, h3, h4, fun x hx => h5 x hx 0⟩

/-- If the smooth
hypersurface `H` is a coordinate hyperplane of an adapted chart of `Y` at every point of `H ∩ Y`,
its
strict transform is a smooth hypersurface of `M'`. -/
theorem isClosedSubmanifold_strictTransform_of_charts
    (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π) (hH : IsClosedSubmanifold ψ H 1)
    (hchart : ∀ a ∈ H ∩ Y, ∃ (φ : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n) (k : Fin n),
      a ∈ φ.source ∧ IsAdaptedChart ψ Y φ σ ∧ ∀ x ∈ φ.source, x ∈ H ↔ ψ (φ x) k = 0) :
    IsClosedSubmanifold ψ (strictTransformSet π Y H) 1 := by
  have hπc : Continuous π := h.contMDiff.continuous
  refine ⟨isClosed_closure, fun p hp => ?_⟩
  have hpH : π p ∈ H := strictTransform_subset_preimage hπc hH.isClosed hp
  by_cases hpY : π p ∈ Y
  · obtain ⟨φ, σ, k, hpφ, hφ, hHk⟩ := hchart (π p) ⟨hpH, hpY⟩
    obtain ⟨i, Φ, hΦ, hpΦ⟩ := h.cover φ σ hφ p hpφ
    by_cases hkr : ∃ k', σ k' = k
    · obtain ⟨k', rfl⟩ := hkr
      by_cases hki : k' = i
      · subst hki
        exfalso
        have hE := strictTransform_inter_source_self hφ hΦ hHk
        exact Set.eq_empty_iff_forall_notMem.mp hE p ⟨hp, hpΦ⟩
      · refine ⟨Φ, singleEmb (σ k'), hpΦ, isAdaptedChart_singleIdx hΦ.mem_maximalAtlas fun x hx =>
      ?_⟩
        have hE := strictTransform_inter_source_of_ne hφ hΦ hHk (Ne.symm hki)
        constructor
        · intro hxH
          exact ((Set.ext_iff.mp hE x).mp ⟨hxH, hx⟩).2
        · intro h0
          exact ((Set.ext_iff.mp hE x).mpr ⟨hx, h0⟩).1
    · have hkr' : ∀ k', σ k' ≠ k := fun k' hk' => hkr ⟨k', hk'⟩
      refine ⟨Φ, singleEmb k, hpΦ, isAdaptedChart_singleIdx hΦ.mem_maximalAtlas fun x hx => ?_⟩
      have hE := strictTransform_inter_source_off hφ hΦ hkr' hHk
      constructor
      · intro hxH
        exact ((Set.ext_iff.mp hE x).mp ⟨hxH, hx⟩).2
      · intro h0
        exact ((Set.ext_iff.mp hE x).mpr ⟨hx, h0⟩).1
  · obtain ⟨φ, σ₁, e, hpφ, hφ, hpe, he, -⟩ :=
      exists_adaptedChart_strictTransform_off hY h hH hpH hpY
    exact ⟨e, σ₁, hpe, he⟩

/-- At a point of a closed
submanifold `Y` contained in a smooth hypersurface `H`, there is a chart adapted to `Y` in which `H`
is a coordinate hyperplane — replace one centre coordinate by a defining function of `H` and
complete the coordinates (`exists_chart_extending`); the case `s = 1` of the flag lemma
`exists_adaptedChart_flag` (`StrictFlag.lean`). -/
theorem exists_adaptedChart_pair [IsManifold 𝓘(𝕜, E) ω M] (hY : IsClosedSubmanifold ψ Y c)
    (hH : IsClosedSubmanifold ψ H 1) (hYH : Y ⊆ H) {a : M} (ha : a ∈ Y) :
    ∃ (φ : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n) (k₀ : Fin c),
      a ∈ φ.source ∧ IsAdaptedChart ψ Y φ σ ∧ ∀ x ∈ φ.source, x ∈ H ↔ ψ (φ x) (σ k₀) = 0 := by
  obtain ⟨φ, σ, τ, haφ, hφ, hS⟩ := exists_adaptedChart_flag hY hH hYH ha
  refine ⟨φ, σ, τ 0, haφ, hφ, fun x hx => ?_⟩
  rw [hS x hx]
  exact ⟨fun h => h 0, fun h j => by rw [Subsingleton.elim j 0]; exact h⟩

/-- For a blowing-up `π` of `M` along a
closed submanifold `Y ⊆ S`, the strict transform of `S` is a closed submanifold of `M'` of the
codimension of `S` — over the centre by the flag chart, `cover` and the chart lemmas, off the centre
by the transport `exists_adaptedChart_strictTransform_off'`. -/
theorem IsClosedSubmanifold.strictTransform [IsManifold 𝓘(𝕜, E) ω M] {S : Set M} {s : ℕ}
    (hS : IsClosedSubmanifold ψ S s) (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
    (hYS : Y ⊆ S) : IsClosedSubmanifold ψ (strictTransformSet π Y S) s := by
  have hπc : Continuous π := h.contMDiff.continuous
  refine ⟨isClosed_closure, fun p hp => ?_⟩
  have hpS : π p ∈ S := strictTransform_subset_preimage hπc hS.isClosed hp
  by_cases hpY : π p ∈ Y
  · obtain ⟨φ, σ, τ, hpφ, hφ, hSflag⟩ := exists_adaptedChart_flag hY hS hYS hpY
    obtain ⟨i, Φ, hΦ, hpΦ⟩ := h.cover φ σ hφ p hpφ
    by_cases hi : i ∈ Set.range τ
    · exfalso
      have hE := strictTransform_inter_source_of_mem_range hφ hΦ hSflag hi
      exact Set.eq_empty_iff_forall_notMem.mp hE p ⟨hp, hpΦ⟩
    · exact ⟨Φ, τ.trans σ, hpΦ, isAdaptedChart_strictTransform_of_not_mem_range hφ hΦ hSflag hi⟩
  · obtain ⟨φ, σ₁, e, hpφ, hφ, hpe, he, -⟩ :=
      exists_adaptedChart_strictTransform_off' hY h hS hpS hpY
    exact ⟨e, σ₁, hpe, he⟩

/-- The strict transform of a smooth
hypersurface containing the centre is a smooth hypersurface of `M'`. -/
theorem isClosedSubmanifold_strictTransform {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M']
    [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M'] {π : M' → M}
    [IsManifold 𝓘(𝕜, E) ω M] (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
    (hH : IsClosedSubmanifold ψ H 1) (hYH : Y ⊆ H) :
    IsClosedSubmanifold ψ (strictTransformSet π Y H) 1 :=
  hH.strictTransform hY h hYH

end Manifold
