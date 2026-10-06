/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Snc.Basic
import Hironaka.Manifold.BlowUp.Charts
import Hironaka.Manifold.BlowUp.Divisor
import Hironaka.Manifold.Chart.Transport
import Hironaka.Manifold.LocalDiffeomorph
import Hironaka.Manifold.Snc.FlagProtected
import Hironaka.Manifold.Snc.TotalTransform
import Hironaka.Manifold.Submanifold.Charts
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Proper simple normal crossings with a submanifold, and its transport by a blowing-up

Kollár restricts a smooth blow-up sequence `Π` with centres `Z_i ⊆ S_i` to the strict transforms
`S_i` of a closed submanifold `S` [Kol07, 30.2], and the blow-up sequences of his algorithm have
centres with simple normal crossings with the boundary [Kol07, Definition 66]. For `Π|_S` to be
such a sequence on `S` the boundary `E_i ∩ S_i` must have only normal crossings with `Z_i ∩ S_i`.
The invariant carried along `Π` is the **proper** form of "`S_i` has simple normal crossings with
`E_i`" (`HypersurfaceFamily.HasSncWithProper`): at every point of `S_i` one chart adapted to `S_i`
which is an snc chart of the family `E_i` and in which no component's coordinate is an
`S_i`-coordinate — no component contains `S_i` near the point. (Without "proper" a component could
contain `S_i`, and its trace on `S_i` would be all of `S_i`, not a hypersurface; the proper form
removes this degenerate case at the root, and the invariant is propagated directly, see
`hasSncWithProper_totalTransform`.)

The transport by one blowing-up `π : M' → M` along `Z ⊆ H` (`hasSncWithProper_totalTransform`):
over a point `a ∈ Z`, the simultaneous chart of `Hironaka/Manifold/Snc/FlagProtected.lean`
(`exists_isSncChartAt_flag_proper`: adapted to `Z`, `H` cut out by the centre block `σ ∘ τ`, snc
for `E` with component coordinates off that block) lifts to blow-up charts; a blow-up chart of an
index `k ∈ range τ` misses the strict transform of `H`
(`strictTransform_inter_source_eq_empty_of_subset`, the one-directional form of
`strictTransform_inter_source_self`; Kollár: only `r − 1` of the `r` charts meet the strict
transform, [Kol07, Theorem 88, proof]), so a point of `H'` over `a` lies in a chart of index
`k ∉ range τ`, where `isAdaptedChart_strictTransform_of_not_mem_range` adapts the chart to `H'`
with the block `τ.trans σ` and `totalTransform_isSncChartAt` keeps the component coordinates
(`cidx j`, off the block) and gives the exceptional divisor `σ k`, off the block as `k ∉ range τ`.
Off the centre `π` is a local isomorphism and the proper chart at `π p` transports along a local
inverse (`IsBlowUp.exists_transportChart_of_notMem`, through `transportChart`), where the strict
transform of `H` is the preimage of `H` and the strict transforms of the components are the
preimages of the components.

The traces of the boundary on `S` and the transported invariant are in
`Hironaka/Manifold/Snc/Trace.lean`; the invariant is carried along the restricted sequences of
the embedded resolution (`Hironaka/Resolution/Analytic/Wlo09/ProperSnc.lean`).
-/

@[expose] public section

noncomputable section

open TopologicalSpace Filter Topology Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

namespace HypersurfaceFamily

variable (F : HypersurfaceFamily M)

/-- `Y` **has simple normal crossings with `F`, properly**: at every point of `Y` there is a chart
adapted to `Y` which is an snc chart of `F` there and in which no component's coordinate is a
`Y`-coordinate — no component of `F` contains `Y` near the point. The form of
[Kol07, Definition 24 (4)] needed to restrict a blow-up sequence to `Y` [Kol07, 30.2]; compare
`HasSncWith`, which allows components containing `Y`. -/
def HasSncWithProper (Y : Set M) (s : ℕ) : Prop :=
  ∀ a ∈ Y, ∃ (φ : OpenPartialHomeomorph M E) (σ : Fin s ↪ Fin n)
    (cidx : {j // a ∈ F.hyp j} → Fin n),
    IsAdaptedChart ψ Y φ σ ∧ F.IsSncChartAt ψ φ a cidx ∧ ∀ j, cidx j ∉ Set.range σ

variable {ψ F}

/-- The proper form implies `HasSncWith`. -/
theorem HasSncWithProper.hasSncWith {Y : Set M} {s : ℕ} (h : F.HasSncWithProper ψ Y s) :
    F.HasSncWith ψ Y s := fun a ha => by
  obtain ⟨φ, σ, cidx, hφ, hc, -⟩ := h a ha
  exact ⟨φ, σ, cidx, hφ, hc⟩

/-- The empty family has simple normal crossings with every closed submanifold, properly (every
adapted chart is an snc chart of the empty family). -/
theorem hasSncWithProper_empty {Y : Set M} {s : ℕ} (hY : IsClosedSubmanifold ψ Y s) :
    (HypersurfaceFamily.empty M).HasSncWithProper ψ Y s := by
  intro a ha
  obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart a ha
  exact ⟨φ, σ, fun j => j.1.elim, hφ, ⟨hφ.1, haφ, fun j => j.1.elim, fun j => j.1.elim⟩,
    fun j => j.1.elim⟩

end HypersurfaceFamily

/-! ### Blow-up charts of a flag index miss the strict transform -/

variable {ψ} {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] {π : M' → M} {Y H : Set M}
  {c : ℕ} {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n} {i : Fin c}
  {Φ : OpenPartialHomeomorph M' E}

/-- If `H ∩ φ.source ⊆ {z_{σ i} = 0}` for a centre index `i`, the strict transform of `H` misses
the blow-up chart of index `i` (the one-directional form of `strictTransform_inter_source_self`;
Kollár's "only `r − 1` of these" charts, [Kol07, Theorem 88, proof]). -/
theorem strictTransform_inter_source_eq_empty_of_subset (hφ : IsAdaptedChart ψ Y φ σ)
    (hΦ : IsBlowUpChart ψ π φ σ i Φ) (hH : ∀ x ∈ φ.source, x ∈ H → ψ (φ x) (σ i) = 0) :
    strictTransformSet π Y H ∩ Φ.source = ∅ := by
  have hA : Φ.source ∩ π ⁻¹' (H \ Y) = ∅ := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_sdiff, Set.mem_empty_iff_false,
      iff_false, not_and, not_not]
    intro hqs hqH
    have h1 : ψ (φ (π q)) (σ i) = 0 := hH _ (hΦ.source_subset hqs) hqH
    rw [hΦ.comm q hqs, blowUpChartMap_apply_scaling] at h1
    exact (IsBlowUpChart.mem_preimage_iff hφ hΦ hqs).mpr h1
  apply Set.eq_empty_of_subset_empty
  rintro p ⟨hp, hps⟩
  have := Φ.open_source.inter_closure ⟨hps, hp⟩
  rw [hA, closure_empty] at this
  exact this

/-- Off the centre the strict transform of a closed set is its preimage. -/
theorem mem_strictTransformSet_iff_of_notMem (hπ : Continuous π) (hH : IsClosed H) {p : M'}
    (hpY : π p ∉ Y) : p ∈ strictTransformSet π Y H ↔ π p ∈ H := by
  refine ⟨fun hp => strictTransform_subset_preimage hπ hH hp, fun hp => ?_⟩
  rcases preimage_subset_strictTransform_union (π := π) (Y := Y) (H := H) hp with h' | h'
  · exact h'
  · exact absurd h' hpY

/-! ### Transport of a chart along a local inverse of the blowing-up, off the centre -/

variable [IsManifold 𝓘(𝕜, E) ω M] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M']
  [SecondCountableTopology M']

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- Off the centre, a chart `φ` of `M` at `π p` transports to a chart `e` of `M'` at `p` whose
source lies over `φ.source ∖ Y` and on which `e = φ ∘ π` (`transportChart` along a local inverse of
the blowing-up, an analytic isomorphism off the centre, [BM88, Definition 4.1 (1)]). -/
theorem IsBlowUp.exists_transportChart_of_notMem (hY : IsClosed Y) (h : IsBlowUp ψ Y c π)
    (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {p : M'} (hpY : π p ∉ Y) (hpφ : π p ∈ φ.source) :
    ∃ e : OpenPartialHomeomorph M' E, e ∈ maximalAtlas 𝓘(𝕜, E) ω M' ∧ p ∈ e.source ∧
      ∀ x ∈ e.source, π x ∉ Y ∧ π x ∈ φ.source ∧ e x = φ (π x) := by
  have hπc : Continuous π := h.contMDiff.continuous
  obtain ⟨Ψ, hpΨ, hEq⟩ := (h.isLocalDiffeomorphOn_compl ⟨p, hpY⟩).exists_partialDiffeomorph
  have hopen : IsOpen (π ⁻¹' Yᶜ) := hY.isOpen_compl.preimage hπc
  set e₀ := transportChart Ψ.symm φ with he₀
  have he₀mem : e₀ ∈ maximalAtlas 𝓘(𝕜, E) ω M' := transportChart_mem_maximalAtlas Ψ.symm hφ
  set e := e₀.restrOpen (π ⁻¹' Yᶜ) hopen with he
  have hemem : e ∈ maximalAtlas 𝓘(𝕜, E) ω M' := by
    rw [he, OpenPartialHomeomorph.restrOpen_eq_restr]
    exact restr_mem_maximalAtlas _ he₀mem hopen
  have hsrc : ∀ x ∈ e.source, π x ∉ Y ∧ π x ∈ φ.source ∧ e x = φ (π x) := by
    intro x hx
    have hx' : x ∈ e₀.source ∧ x ∈ π ⁻¹' Yᶜ := by
      simpa [he, OpenPartialHomeomorph.restrOpen_source] using hx
    have hx₀ := hx'.1
    rw [he₀, transportChart_source] at hx₀
    have hxΨ : x ∈ Ψ.source := hx₀.1
    have hΨx : Ψ.symm.invFun x = π x := by
      change Ψ x = π x
      exact (hEq hxΨ).symm
    refine ⟨hx'.2, ?_, ?_⟩
    · have := hx₀.2
      rwa [Set.mem_preimage, hΨx] at this
    · change e₀ x = φ (π x)
      rw [he₀, transportChart_apply, hΨx]
  refine ⟨e, hemem, ?_, hsrc⟩
  simp only [he, OpenPartialHomeomorph.restrOpen_source, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_compl_iff]
  refine ⟨?_, hpY⟩
  rw [he₀, transportChart_source]
  refine ⟨hpΨ, ?_⟩
  change Ψ p ∈ φ.source
  rw [← hEq hpΨ]
  exact hpφ

/-! ### Transport of the proper invariant by one blowing-up -/

namespace HypersurfaceFamily

variable {F : HypersurfaceFamily M} {Z : Set M} {s : ℕ}

/-- The proper invariant is transported by a blowing-up ([Kol07, 30.2] with [Kol07, Definition 25]
and the proof of [Kol07, Theorem 88]). Let `π : M' → M` blow up `Z ⊆ H`, with `F` snc, `Z` having
snc with `F` and `H` having snc with `F` properly. Then the strict transform `H'` of `H` has snc
with the total transform of `F`, properly. Over `a ∈ Z`, the simultaneous chart
(`exists_isSncChartAt_flag_proper`) has `H` cut out by the block `σ ∘ τ`; a point of `H'` over `a`
lies in a blow-up chart of an index `k ∉ range τ` (the charts of the indices `τ j` miss `H'`,
`strictTransform_inter_source_eq_empty_of_subset`), which is adapted to `H'` with the block
`τ.trans σ` and an snc chart of the total transform with the component coordinates
`cidx j ∉ range (τ.trans σ)` and the exceptional coordinate `σ k`, `k ∉ range τ`. Off the centre the
proper chart at `π p` transports along a local inverse of `π`
(`IsBlowUp.exists_transportChart_of_notMem`), `H'` and the strict transforms of the components
being the preimages of `H` and of the components there. -/
theorem hasSncWithProper_totalTransform (hZ : IsClosedSubmanifold ψ Z c) (h : IsBlowUp ψ Z c π)
    (hF : F.IsSnc ψ) (hH : IsClosedSubmanifold ψ H s) (hZH : Z ⊆ H) (hFZ : F.HasSncWith ψ Z c)
    (hFH : F.HasSncWithProper ψ H s) :
    (F.totalTransform π Z).HasSncWithProper ψ (strictTransformSet π Z H) s := by
  intro p hp
  have hπc : Continuous π := h.contMDiff.continuous
  have hpH : π p ∈ H := strictTransform_subset_preimage hπc hH.isClosed hp
  by_cases hpZ : π p ∈ Z
  · -- over the centre
    obtain ⟨φ₀, σ₀, cidx₀, hφ₀, hc₀⟩ := hFZ (π p) hpZ
    obtain ⟨φ₁, σ₁, cidx₁, hφ₁, hc₁, hproper⟩ := hFH (π p) hpH
    obtain ⟨e, σ, τ, cidx, heZ, hflag, hc, hcτ⟩ :=
      exists_isSncChartAt_flag_proper hF hZ hZH hφ₀ hpZ hc₀ hφ₁ hc₁ hproper
    obtain ⟨k, Φ, hΦ, hpΦ⟩ := h.cover e σ heZ p hc.2.1
    -- the index `k` is off the flag: the charts of the indices `τ j` miss `H'`
    have hk : k ∉ Set.range τ := by
      rintro ⟨j, hj⟩
      have hsub : ∀ x ∈ e.source, x ∈ H → ψ (e x) (σ k) = 0 := fun x hx hxH => by
        rw [← hj]
        exact (hflag x hx).mp hxH j
      have := strictTransform_inter_source_eq_empty_of_subset heZ hΦ hsub
      exact absurd ((Set.ext_iff.mp this p).mp ⟨hp, hpΦ⟩) (Set.notMem_empty p)
    have hΦH : IsAdaptedChart ψ (strictTransformSet π Z H) Φ (τ.trans σ) :=
      isAdaptedChart_strictTransform_of_not_mem_range heZ hΦ hflag hk
    have hcT := totalTransform_isSncChartAt h hF heZ hc hΦ hpΦ rfl
    refine ⟨Φ, τ.trans σ, _, hΦH, hcT, ?_⟩
    rintro ⟨j, hj⟩ ⟨l, hl⟩
    obtain j' | u := j
    · exact hcτ _ ⟨l, hl⟩
    · have hl' : σ (τ l) = σ k := hl
      exact hk ⟨l, σ.injective hl'⟩
  · -- off the centre
    obtain ⟨φ, σ, cidx, hφ, hc, hproper⟩ := hFH (π p) hpH
    obtain ⟨e, hemem, hpe, hsrc⟩ := h.exists_transportChart_of_notMem hZ.isClosed hφ.1 hpZ hc.2.1
    -- the components through `p` lie over the components through `π p`
    have hover : ∀ k : {k // p ∈ (F.totalTransform π Z).hyp k}, ∃ j : {j // π p ∈ F.hyp j},
        k.1 = toLex (Sum.inl j.1) := by
      rintro ⟨k, hk⟩
      obtain j | u := k
      · exact ⟨⟨j, mem_hyp_of_mem_strictTransform h hF hk⟩, rfl⟩
      · exact absurd hk hpZ
    choose idx hidx using hover
    refine ⟨e, σ, fun k => cidx (idx k), ⟨hemem, fun x hx => ?_⟩, ⟨hemem, hpe, ?_, ?_⟩,
      fun k => hproper (idx k)⟩
    · obtain ⟨hxZ, hxφ, hex⟩ := hsrc x hx
      rw [mem_strictTransformSet_iff_of_notMem hπc hH.isClosed hxZ, hex]
      exact hφ.2 _ hxφ
    · rintro ⟨k, hk⟩ x hx
      obtain ⟨hxZ, hxφ, hex⟩ := hsrc x hx
      obtain j | u := k
      · have h0 : toLex (Sum.inl j) = toLex (Sum.inl (idx ⟨toLex (Sum.inl j), hk⟩).1) :=
          hidx ⟨toLex (Sum.inl j), hk⟩
        have hj : (idx ⟨toLex (Sum.inl j), hk⟩).1 = j :=
          (Sum.inl_injective (toLex.injective h0)).symm
        have hm := hc.mem_iff (idx ⟨toLex (Sum.inl j), hk⟩) hxφ
        rw [hj] at hm
        change x ∈ strictTransformSet π Z (F.hyp j) ↔
          ψ (e x) (cidx (idx ⟨toLex (Sum.inl j), hk⟩)) = 0
        rw [mem_strictTransform_iff_of_notMem h hF hxZ, hex]
        exact hm
      · exact absurd (hk : π p ∈ Z) hpZ
    · intro k₁ k₂ heq
      have h1 := hidx k₁
      have h2 := hidx k₂
      have : idx k₁ = idx k₂ := hc.injective heq
      exact Subtype.ext (h1.trans (by rw [this, ← h2]))

end HypersurfaceFamily

end Manifold

end
