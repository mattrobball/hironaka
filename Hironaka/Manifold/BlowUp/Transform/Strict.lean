/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Transform.Basic
import Hironaka.Manifold.BlowUp.Charts
import Hironaka.Manifold.BlowUp.Divisor
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.Module.PerfectSpace

/-!
# The strict transform of a hypersurface in the blow-up charts

The strict transform of `H ⊆ M` under the blowing-up `π` with centre `Y` is
`H' = closure (π⁻¹(H ∖ Y))` (`strictTransformSet`;
[BM97, §3, "The strict transform"]). Set forms: `H' ⊆ π⁻¹(H)` for closed `H` and
`π⁻¹(H) ⊆ H' ∪ π⁻¹(Y)` (`strictTransform_subset_preimage`,
`preimage_subset_strictTransform_union`). Chart forms, with the adapted chart as hypothesis: for
`H = {z_k = 0}` on an adapted chart `φ` of `Y` and a blow-up chart `Φ` of index `i` over it
(`z_{σ k} ∘ π = u_i u_k` for `k ≠ i`, `z_{σ i} ∘ π = u_i`, `w_j ∘ π = w_j` off the centre, by
`IsBlowUpChart.comm` and the pointwise formulas for `blowUpChartMap`), `H' ∩ Φ.source = {u_k = 0}`
for a centre index `k ≠ i` (`strictTransform_inter_source_of_ne`), `H' ∩ Φ.source = ∅` for `k = i`
(`strictTransform_inter_source_self`), and `H' ∩ Φ.source = {w_j = 0} = π⁻¹(H) ∩ Φ.source` for an
off-centre index `j` (`strictTransform_inter_source_off`, `strictTransform_eq_preimage_inter`).
These are the local computations of the proof of [Kol07, Theorem 88] ("`S₁ = (y₁ = 0)` is the
birational transform of `S`"; only `r − 1` of the `r` charts meet the strict transform). The
inclusions `⊆` read the vanishing of a chart coordinate on `π⁻¹(H ∖ Y)` (where `u_i ≠ 0`) through
the closure (`coord_eq_zero_of_mem_closure`); the inclusions `⊇` approximate a point of the
coordinate hyperplane by points with `u_i ≠ 0`, perturbing the scaling coordinate
(`mem_closure_of_coord_eq_zero`).

Codimension-`s` forms: in flag coordinates `Y = {z_σ = 0} ⊆ S = {z_{σ (τ j)} = 0}` the strict
transform of `S` misses the blow-up charts of index `i ∈ range τ`
(`strictTransform_inter_source_of_mem_range`) and is `{u_{σ (τ j)} = 0 ∀ j}` on the others
(`strictTransform_inter_source_of_not_mem_range`,
`isAdaptedChart_strictTransform_of_not_mem_range`), by the multi-coordinate perturbation
`mem_closure_of_forall_coord_eq`, of which `mem_closure_of_coord_eq_zero` is the one-coordinate
case. These describe the strict transform of a smooth subvariety containing the centre, as in the
proof of [Kol07, Theorem 88].
-/

public section

open TopologicalSpace Opposite CategoryTheory Filter Topology IsLocalRing Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M}
  {c : ℕ} {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] {π : M' → M}
  {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n} {i : Fin c} {Φ : OpenPartialHomeomorph M' E}
  {H : Set M}

/-- The strict transform of a closed set lies over it. -/
theorem strictTransform_subset_preimage (hπ : Continuous π) (hH : IsClosed H) :
    strictTransformSet π Y H ⊆ π ⁻¹' H :=
  closure_minimal (Set.preimage_mono Set.sdiff_subset) (hH.preimage hπ)

omit [TopologicalSpace M] in
/-- The preimage of `H` is covered by the strict transform
and the exceptional divisor. -/
theorem preimage_subset_strictTransform_union :
    π ⁻¹' H ⊆ strictTransformSet π Y H ∪ π ⁻¹' Y := by
  intro p hp
  by_cases hpY : π p ∈ Y
  · exact Or.inr hpY
  · exact Or.inl (subset_closure ⟨hp, hpY⟩)

omit [ChartedSpace E M'] in
variable (ψ) in
/-- Multi-coordinate form (for the flag charts of the codimension-`s` forms): a point of a blow-up
chart is a limit of points of the chart with the same coordinates except the scaling coordinate
`u_{σ i}`, which is made nonzero (perturb the scaling coordinate alone); the one-coordinate form is
`mem_closure_of_coord_eq_zero`. -/
theorem mem_closure_of_forall_coord_eq {p : M'} (hp : p ∈ Φ.source) (A : Set M')
    (hA : ∀ q ∈ Φ.source, (∀ j, j ≠ σ i → ψ (Φ q) j = ψ (Φ p) j) → ψ (Φ q) (σ i) ≠ 0 → q ∈ A) :
    p ∈ closure A := by
  classical
  by_cases hp0 : ψ (Φ p) (σ i) = 0
  · set q : 𝕜 → M' := fun t => Φ.symm (ψ.symm (ψ (Φ p) + Pi.single (σ i) t)) with hq
    have hcont : Continuous fun t : 𝕜 => ψ.symm (ψ (Φ p) + Pi.single (σ i) t) := by
      refine ψ.symm.continuous.comp (continuous_const.add (continuous_pi fun k => ?_))
      simp only [Pi.single_apply]
      split_ifs <;> fun_prop
    have h0 : ψ.symm (ψ (Φ p) + Pi.single (σ i) (0 : 𝕜)) = Φ p := by simp
    have h1 : Tendsto (fun t : 𝕜 => ψ.symm (ψ (Φ p) + Pi.single (σ i) t)) (𝓝 0) (𝓝 (Φ p)) := by
      have := hcont.continuousAt (x := (0 : 𝕜))
      rwa [ContinuousAt, h0] at this
    have hT : ∀ᶠ t : 𝕜 in 𝓝 0, ψ.symm (ψ (Φ p) + Pi.single (σ i) t) ∈ Φ.target :=
      h1 (Φ.open_target.mem_nhds (Φ.map_source hp))
    have htend : Tendsto q (𝓝[≠] 0) (𝓝 p) := by
      have h3 := (Φ.continuousAt_symm (Φ.map_source hp)).tendsto
      rw [Φ.left_inv hp] at h3
      exact (h3.comp h1).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto htend ?_
    filter_upwards [hT.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht0
    have hqs : q t ∈ Φ.source := Φ.map_target ht
    have hΦq : Φ (q t) = ψ.symm (ψ (Φ p) + Pi.single (σ i) t) := Φ.right_inv ht
    refine hA (q t) hqs (fun j hj => ?_) ?_
    · rw [hΦq, ψ.apply_symm_apply, Pi.add_apply, Pi.single_eq_of_ne hj, add_zero]
    · rw [hΦq, ψ.apply_symm_apply, Pi.add_apply, Pi.single_eq_same, hp0, zero_add]
      exact ht0
  · exact subset_closure (hA p hp (fun _ _ => rfl) hp0)

omit [ChartedSpace E M'] in
variable (ψ) in
/-- A point of a blow-up chart at which a coordinate function other than the scaling
coordinate vanishes is a limit of points of the chart at which that coordinate still vanishes and
the
scaling coordinate does not (perturb the scaling coordinate). -/
theorem mem_closure_of_coord_eq_zero {j : Fin n} (hj : j ≠ σ i) {p : M'} (hp : p ∈ Φ.source)
    (S : Set M') (hS : ∀ q ∈ Φ.source, ψ (Φ q) j = ψ (Φ p) j → ψ (Φ q) (σ i) ≠ 0 → q ∈ S) :
    p ∈ closure S :=
  mem_closure_of_forall_coord_eq ψ hp S fun q hq hall hne => hS q hq (hall j hj) hne

omit [ChartedSpace E M'] in
variable (ψ) in
/-- The coordinate functions of a chart are continuous on its source. -/
theorem continuousOn_coord_fn (Φ : OpenPartialHomeomorph M' E) (j : Fin n) :
    ContinuousOn (fun q => ψ (Φ q) j) Φ.source :=
  (continuous_apply j).comp_continuousOn (ψ.continuous.comp_continuousOn Φ.continuousOn)

omit [ChartedSpace E M'] in
variable (ψ) in
/-- A coordinate function vanishing on `Φ.source ∩ A` vanishes on `Φ.source ∩ closure A`. -/
theorem coord_eq_zero_of_mem_closure {A : Set M'} (j : Fin n)
    (hA : ∀ q ∈ Φ.source ∩ A, ψ (Φ q) j = 0) {p : M'} (hp : p ∈ Φ.source) (hpA : p ∈ closure A) :
    ψ (Φ p) j = 0 := by
  have h1 : p ∈ closure (Φ.source ∩ A) := Φ.open_source.inter_closure ⟨hp, hpA⟩
  have h2 : ContinuousWithinAt (fun q => ψ (Φ q) j) (Φ.source ∩ A) p :=
    ((continuousOn_coord_fn ψ Φ j).continuousWithinAt hp).mono Set.inter_subset_left
  have h3 := h2.mem_closure_image h1
  have h4 : (fun q => ψ (Φ q) j) '' (Φ.source ∩ A) ⊆ {0} := by
    rintro _ ⟨q, hq, rfl⟩
    exact hA q hq
  have h5 : closure ((fun q => ψ (Φ q) j) '' (Φ.source ∩ A)) ⊆ {0} :=
    closure_minimal h4 isClosed_singleton
  exact h5 h3

/-- For `H = {z_k = 0}` with `k` a centre
index, the strict transform is `{u_k = 0}` in the blow-up charts of index `i ≠ k`. -/
theorem strictTransform_inter_source_of_ne (hφ : IsAdaptedChart ψ Y φ σ)
    (hΦ : IsBlowUpChart ψ π φ σ i Φ) {k : Fin c}
    (hH : ∀ x ∈ φ.source, x ∈ H ↔ ψ (φ x) (σ k) = 0) (hik : i ≠ k) :
    strictTransformSet π Y H ∩ Φ.source = {p ∈ Φ.source | ψ (Φ p) (σ k) = 0} := by
  ext p
  constructor
  · rintro ⟨hp, hps⟩
    refine ⟨hps, coord_eq_zero_of_mem_closure ψ (σ k) ?_ hps hp⟩
    rintro q ⟨hqs, hqH, hqY⟩
    have h1 : ψ (φ (π q)) (σ k) = 0 := (hH _ (hΦ.source_subset hqs)).mp hqH
    rw [hΦ.comm q hqs, blowUpChartMap_apply_ratio σ _ hik.symm] at h1
    have h2 : ψ (Φ q) (σ i) ≠ 0 := fun h0 => hqY ((IsBlowUpChart.mem_preimage_iff hφ hΦ hqs).mpr h0)
    exact (mul_eq_zero.mp h1).resolve_left h2
  · rintro ⟨hps, hpk⟩
    refine ⟨mem_closure_of_coord_eq_zero ψ (σ.injective.ne hik.symm) hps _ ?_, hps⟩
    intro q hqs hqk hqi
    refine ⟨(hH _ (hΦ.source_subset hqs)).mpr ?_,
      fun hqY => hqi ((IsBlowUpChart.mem_preimage_iff hφ hΦ hqs).mp hqY)⟩
    rw [hΦ.comm q hqs, blowUpChartMap_apply_ratio σ _ hik.symm, hqk, hpk, mul_zero]

/-- For `H = {z_k = 0}` with `k` a centre index, the strict transform misses the blow-up chart
of
index `k`. -/
theorem strictTransform_inter_source_self (hφ : IsAdaptedChart ψ Y φ σ)
    (hΦ : IsBlowUpChart ψ π φ σ i Φ) (hH : ∀ x ∈ φ.source, x ∈ H ↔ ψ (φ x) (σ i) = 0) :
    strictTransformSet π Y H ∩ Φ.source = ∅ := by
  have hA : Φ.source ∩ π ⁻¹' (H \ Y) = ∅ := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_sdiff, Set.mem_empty_iff_false,
      iff_false, not_and, not_not]
    intro hqs hqH
    have h1 : ψ (φ (π q)) (σ i) = 0 := (hH _ (hΦ.source_subset hqs)).mp hqH
    rw [hΦ.comm q hqs, blowUpChartMap_apply_scaling] at h1
    exact (IsBlowUpChart.mem_preimage_iff hφ hΦ hqs).mpr h1
  apply Set.eq_empty_of_subset_empty
  rintro p ⟨hp, hps⟩
  have := Φ.open_source.inter_closure ⟨hps, hp⟩
  rw [hA, closure_empty] at this
  exact this

/-- For `H = {w_j = 0}` with `j` off the centre (`Y` transverse to `H`), the strict
transform is `{w_j = 0}` in every blow-up chart. -/
theorem strictTransform_inter_source_off (hφ : IsAdaptedChart ψ Y φ σ)
    (hΦ : IsBlowUpChart ψ π φ σ i Φ) {j : Fin n} (hj : ∀ k, σ k ≠ j)
    (hH : ∀ x ∈ φ.source, x ∈ H ↔ ψ (φ x) j = 0) :
    strictTransformSet π Y H ∩ Φ.source = {p ∈ Φ.source | ψ (Φ p) j = 0} := by
  ext p
  constructor
  · rintro ⟨hp, hps⟩
    refine ⟨hps, coord_eq_zero_of_mem_closure ψ j ?_ hps hp⟩
    rintro q ⟨hqs, hqH, -⟩
    have h1 : ψ (φ (π q)) j = 0 := (hH _ (hΦ.source_subset hqs)).mp hqH
    rwa [hΦ.comm q hqs, blowUpChartMap_apply_off σ _ hj] at h1
  · rintro ⟨hps, hpj⟩
    refine ⟨mem_closure_of_coord_eq_zero ψ (hj i).symm hps _ ?_, hps⟩
    intro q hqs hqj hqi
    refine ⟨(hH _ (hΦ.source_subset hqs)).mpr ?_,
      fun hqY => hqi ((IsBlowUpChart.mem_preimage_iff hφ hΦ hqs).mp hqY)⟩
    rw [hΦ.comm q hqs, blowUpChartMap_apply_off σ _ hj, hqj, hpj]

/-- For `H = {w_j = 0}` with `j` off the centre, the strict transform
is the total transform on the chart. -/
theorem strictTransform_eq_preimage_inter (hφ : IsAdaptedChart ψ Y φ σ)
    (hΦ : IsBlowUpChart ψ π φ σ i Φ) {j : Fin n} (hj : ∀ k, σ k ≠ j)
    (hH : ∀ x ∈ φ.source, x ∈ H ↔ ψ (φ x) j = 0) :
    strictTransformSet π Y H ∩ Φ.source = π ⁻¹' H ∩ Φ.source := by
  rw [strictTransform_inter_source_off hφ hΦ hj hH]
  ext p
  constructor
  · rintro ⟨hps, hpj⟩
    refine ⟨(hH _ (hΦ.source_subset hps)).mpr ?_, hps⟩
    rw [hΦ.comm p hps, blowUpChartMap_apply_off σ _ hj, hpj]
  · rintro ⟨hpH, hps⟩
    refine ⟨hps, ?_⟩
    have h1 : ψ (φ (π p)) j = 0 := (hH _ (hΦ.source_subset hps)).mp hpH
    rwa [hΦ.comm p hps, blowUpChartMap_apply_off σ _ hj] at h1

/-! ### Codimension-`s` forms: flag coordinates -/

variable {S : Set M} {s : ℕ} {τ : Fin s ↪ Fin c}

omit [TopologicalSpace M'] [ChartedSpace E M'] in
/-- In flag coordinates (`Y = {z_σ = 0}`, `S = {z_{σ (τ j)} = 0}`) the adapted chart of `Y` is
adapted to `S` with the indices `τ.trans σ`. -/
theorem IsAdaptedChart.flag (hφ : IsAdaptedChart ψ Y φ σ)
    (hS : ∀ x ∈ φ.source, x ∈ S ↔ ∀ j, ψ (φ x) (σ (τ j)) = 0) :
    IsAdaptedChart ψ S φ (τ.trans σ) :=
  ⟨hφ.1, hS⟩

/-- In flag coordinates (`S = {z_{σ (τ j)} = 0 ∀ j}` on the adapted chart), the strict transform
of `S` misses the blow-up charts whose index is one of the `S`-coordinates: on such a chart the
scaling coordinate `u_{σ i} = z_{σ i} ∘ π` vanishes exactly over the centre, so `π⁻¹(S ∖ Y)` misses
the chart. -/
theorem strictTransform_inter_source_of_mem_range (hφ : IsAdaptedChart ψ Y φ σ)
    (hΦ : IsBlowUpChart ψ π φ σ i Φ) (hS : ∀ x ∈ φ.source, x ∈ S ↔ ∀ j, ψ (φ x) (σ (τ j)) = 0)
    (hi : i ∈ Set.range τ) : strictTransformSet π Y S ∩ Φ.source = ∅ := by
  obtain ⟨j₀, hj₀⟩ := hi
  have hA : Φ.source ∩ π ⁻¹' (S \ Y) = ∅ := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_sdiff, Set.mem_empty_iff_false,
      iff_false, not_and, not_not]
    intro hqs hqS
    have h1 : ψ (φ (π q)) (σ i) = 0 := by
      have := (hS _ (hΦ.source_subset hqs)).mp hqS j₀
      rwa [hj₀] at this
    rw [hΦ.comm q hqs, blowUpChartMap_apply_scaling] at h1
    exact (IsBlowUpChart.mem_preimage_iff hφ hΦ hqs).mpr h1
  apply Set.eq_empty_of_subset_empty
  rintro p ⟨hp, hps⟩
  have := Φ.open_source.inter_closure ⟨hps, hp⟩
  rw [hA, closure_empty] at this
  exact this

/-- In flag coordinates, the strict transform of `S` is `{u_{σ (τ j)} = 0 ∀ j}` on the blow-up
charts whose index is not one of the `S`-coordinates. -/
theorem strictTransform_inter_source_of_not_mem_range (hφ : IsAdaptedChart ψ Y φ σ)
    (hΦ : IsBlowUpChart ψ π φ σ i Φ) (hS : ∀ x ∈ φ.source, x ∈ S ↔ ∀ j, ψ (φ x) (σ (τ j)) = 0)
    (hi : i ∉ Set.range τ) :
    strictTransformSet π Y S ∩ Φ.source = {p ∈ Φ.source | ∀ j, ψ (Φ p) (σ (τ j)) = 0} := by
  have hτ : ∀ j, τ j ≠ i := fun j hj => hi ⟨j, hj⟩
  ext p
  constructor
  · rintro ⟨hp, hps⟩
    refine ⟨hps, fun j => coord_eq_zero_of_mem_closure ψ (σ (τ j)) ?_ hps hp⟩
    rintro q ⟨hqs, hqS, hqY⟩
    have h1 : ψ (φ (π q)) (σ (τ j)) = 0 := (hS _ (hΦ.source_subset hqs)).mp hqS j
    rw [hΦ.comm q hqs, blowUpChartMap_apply_ratio σ _ (hτ j)] at h1
    have h2 : ψ (Φ q) (σ i) ≠ 0 := fun h0 => hqY ((IsBlowUpChart.mem_preimage_iff hφ hΦ hqs).mpr h0)
    exact (mul_eq_zero.mp h1).resolve_left h2
  · rintro ⟨hps, hpj⟩
    refine ⟨mem_closure_of_forall_coord_eq (σ := σ) (i := i) ψ hps _ ?_, hps⟩
    intro q hqs hqj hqi
    refine ⟨(hS _ (hΦ.source_subset hqs)).mpr fun j => ?_,
      fun hqY => hqi ((IsBlowUpChart.mem_preimage_iff hφ hΦ hqs).mp hqY)⟩
    rw [hΦ.comm q hqs, blowUpChartMap_apply_ratio σ _ (hτ j),
      hqj (σ (τ j)) (σ.injective.ne (hτ j)), hpj j, mul_zero]

/-- On a blow-up chart whose index is not one of the `S`-coordinates, the chart is
adapted to the strict transform of `S` with the `S`-indices `τ.trans σ`. -/
theorem isAdaptedChart_strictTransform_of_not_mem_range (hφ : IsAdaptedChart ψ Y φ σ)
    (hΦ : IsBlowUpChart ψ π φ σ i Φ) (hS : ∀ x ∈ φ.source, x ∈ S ↔ ∀ j, ψ (φ x) (σ (τ j)) = 0)
    (hi : i ∉ Set.range τ) : IsAdaptedChart ψ (strictTransformSet π Y S) Φ (τ.trans σ) := by
  have hE := strictTransform_inter_source_of_not_mem_range hφ hΦ hS hi
  refine ⟨hΦ.mem_maximalAtlas, fun x hx => ?_⟩
  constructor
  · intro hxS'
    exact ((Set.ext_iff.mp hE x).mp ⟨hxS', hx⟩).2
  · intro h0
    exact ((Set.ext_iff.mp hE x).mpr ⟨hx, h0⟩).1

end Manifold
