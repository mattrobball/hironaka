/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Submanifold
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Adapted charts: basic lemmas and locality

On the source of an adapted chart `(φ, σ)` for `Y` (`IsAdaptedChart`), `Y`
is the zero set of the adapted coordinates `ψ_{σ i} ∘ φ` (`IsAdaptedChart.mem_iff'`), so
`φ(Y ∩ U) = φ(U) ∩ {z_σ = 0}` (`image_inter'`), the form of Bierstone–Milman's blowing-up charts
[BM88, Definition 4.1 (2)]; adapted charts restrict to open sets (`restrOpen'`, through Mathlib's
`restr_mem_maximalAtlas`); the zero set of `c` coordinates of any chart of the maximal atlas is
adapted to that chart (`isAdaptedChart_zeroSet'`, the entry point for the charts produced by the
chart-extension theorem); a nonempty closed submanifold has codimension at most `n`; the empty set
is a closed submanifold of every codimension; and on a manifold the closed submanifolds of
codimension `0` are the clopen sets. Locality: a closed submanifold of `M` is one of every open
subset (`isClosedSubmanifoldOn'`), the zero set of adapted coordinates is a closed submanifold of
the chart domain (`IsAdaptedChart.isClosedSubmanifoldOn'`), and closed submanifolds of the members
of an open cover glue (`of_cover'`; Bierstone–Milman: a set which is locally the support of a
smooth subspace "is globally the support of a smooth subspace" [BM97, §3]). These are the lemmas
every later use of closed submanifolds (centres, hypersurfaces of maximal contact, components of
the boundary) rests on.
-/

public noncomputable section

open TopologicalSpace Filter Topology Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

/-- `restrOpen` is `restr` for an open set. -/
theorem _root_.OpenPartialHomeomorph.restrOpen_eq_restr {X Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Z] (e : OpenPartialHomeomorph X Z) {s : Set X} (hs : IsOpen s) :
    e.restrOpen s hs = e.restr s :=
  OpenPartialHomeomorph.toPartialEquiv_injective (by
    change (e.restrOpen s hs).toPartialEquiv = (e.restr s).toPartialEquiv
    rw [OpenPartialHomeomorph.restrOpen_toPartialEquiv, e.restr_toPartialEquiv' s hs])

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)}
  {Y : Set M} {φ : OpenPartialHomeomorph M E} {c : ℕ} {σ : Fin c ↪ Fin n}

/-- On the source of an adapted chart, `Y` is the zero set of the adapted coordinates. -/
theorem IsAdaptedChart.mem_iff' (h : IsAdaptedChart ψ Y φ σ) {x : M} (hx : x ∈ φ.source) :
    x ∈ Y ↔ ∀ i, ψ (φ x) (σ i) = 0 :=
  h.2 x hx

/-- `φ(Y ∩ U) = φ(U) ∩ {z_σ = 0}` [BM88, Definition 4.1 (2)]. -/
theorem IsAdaptedChart.image_inter' (h : IsAdaptedChart ψ Y φ σ) :
    φ '' (Y ∩ φ.source) = φ.target ∩ {y | ∀ i, ψ y (σ i) = 0} := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxY, hxs⟩, rfl⟩
    exact ⟨φ.map_source hxs, (h.2 x hxs).mp hxY⟩
  · rintro ⟨hyt, hy⟩
    refine ⟨φ.symm y, ⟨(h.2 _ (φ.map_target hyt)).mpr ?_, φ.map_target hyt⟩, φ.right_inv hyt⟩
    rwa [φ.right_inv hyt]

/-- The restriction of an adapted chart to an open set is adapted. -/
theorem IsAdaptedChart.restrOpen' (h : IsAdaptedChart ψ Y φ σ) (s : Set M) (hs : IsOpen s) :
    IsAdaptedChart ψ Y (φ.restrOpen s hs) σ := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_eq_restr]
    exact restr_mem_maximalAtlas _ h.1 hs
  · rw [OpenPartialHomeomorph.restrOpen_source] at hx
    exact h.2 x hx.1

/-- The zero set of `c` coordinates of a chart of the maximal atlas, on its source, has that chart
as an adapted chart (the entry point for the charts produced by the chart-extension theorem). -/
theorem isAdaptedChart_zeroSet' (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) (σ : Fin c ↪ Fin n) :
    IsAdaptedChart ψ (φ.source ∩ {x | ∀ i, ψ (φ x) (σ i) = 0}) φ σ :=
  ⟨hφ, fun _ hx => ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩⟩

/-- A nonempty closed submanifold has codimension at most `n`. -/
theorem IsClosedSubmanifold.codim_le' (hY : IsClosedSubmanifold ψ Y c) (hne : Y.Nonempty) :
    c ≤ n := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨_, σ, -, -⟩ := hY.exists_adaptedChart a ha
  simpa using Fintype.card_le_of_embedding σ

/-- The empty set is a closed submanifold of every codimension. -/
theorem isClosedSubmanifold_empty' (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (c : ℕ) :
    IsClosedSubmanifold ψ (∅ : Set M) c :=
  ⟨isClosed_empty, fun _ ha => ha.elim⟩

/-- On a manifold, the closed submanifolds of codimension `0` are the clopen sets. -/
theorem isClosedSubmanifold_zero_iff' [IsManifold 𝓘(𝕜, E) ω M] :
    IsClosedSubmanifold ψ Y 0 ↔ IsClopen Y := by
  constructor
  · intro hY
    refine ⟨hY.isClosed, isOpen_iff_forall_mem_open.mpr fun a ha => ?_⟩
    obtain ⟨φ, _, haφ, h⟩ := hY.exists_adaptedChart a ha
    exact ⟨φ.source, fun x hx => (h.2 x hx).mpr fun i => i.elim0, φ.open_source, haφ⟩
  · intro hY
    refine ⟨hY.isClosed, fun a ha => ⟨(chartAt E a).restrOpen Y hY.isOpen,
      ⟨Fin.elim0, fun i => i.elim0⟩, ?_, ?_, fun x hx => ?_⟩⟩
    · rw [OpenPartialHomeomorph.restrOpen_source]
      exact ⟨mem_chart_source E a, ha⟩
    · rw [OpenPartialHomeomorph.restrOpen_eq_restr]
      exact restr_mem_maximalAtlas _ (IsManifold.chart_mem_maximalAtlas a) hY.isOpen
    · rw [OpenPartialHomeomorph.restrOpen_source] at hx
      exact ⟨fun _ i => i.elim0, fun _ => hx.2⟩

/-! ## Locality -/

/-- A closed submanifold of `M` is a closed submanifold of every open subset. -/
theorem IsClosedSubmanifold.isClosedSubmanifoldOn' (hY : IsClosedSubmanifold ψ Y c) {U : Set M}
    (hU : IsOpen U) : IsClosedSubmanifoldOn ψ U Y c := by
  refine ⟨hY.isClosed.preimage continuous_subtype_val, fun a ⟨haY, haU⟩ => ?_⟩
  obtain ⟨φ, σ, haφ, h⟩ := hY.exists_adaptedChart a haY
  refine ⟨φ.restrOpen U hU, σ, ?_, ?_, h.restrOpen' U hU⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨haφ, haU⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact inter_subset_right

/-- The coordinate subspace `{y | ∀ i, y (σ i) = 0}` is closed. -/
theorem isClosed_zeroSet_coords (σ : Fin c ↪ Fin n) :
    IsClosed {y : Fin n → 𝕜 | ∀ i, y (σ i) = 0} := by
  have : {y : Fin n → 𝕜 | ∀ i, y (σ i) = 0} = ⋂ i, (fun y : Fin n → 𝕜 => y (σ i)) ⁻¹' {0} := by
    ext y
    simp
  rw [this]
  exact isClosed_iInter fun i => isClosed_singleton.preimage (continuous_apply _)

/-- On the source of an adapted chart, `Y` is a closed submanifold. -/
theorem IsAdaptedChart.isClosedSubmanifoldOn' (h : IsAdaptedChart ψ Y φ σ) :
    IsClosedSubmanifoldOn ψ φ.source Y c := by
  refine ⟨?_, fun a ⟨_, has⟩ => ⟨φ, σ, has, subset_rfl, h⟩⟩
  have h1 : ((Subtype.val : φ.source → M) ⁻¹' Y) =
      (fun x : φ.source => ψ (φ x)) ⁻¹' {y | ∀ i, y (σ i) = 0} := by
    ext x
    exact h.2 x x.2
  rw [h1]
  refine (isClosed_zeroSet_coords σ).preimage ?_
  exact ψ.continuous.comp (φ.continuousOn.comp_continuous continuous_subtype_val fun x => x.2)

/-- A set that is a closed submanifold of every member of an open cover is a closed submanifold of
`M` [BM97, §3]. -/
theorem IsClosedSubmanifold.of_cover' {ι : Type*} {U : ι → Set M} (hU : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = univ) (h : ∀ i, IsClosedSubmanifoldOn ψ (U i) Y c) :
    IsClosedSubmanifold ψ Y c := by
  have hmem : ∀ x : M, ∃ i, x ∈ U i := fun x => mem_iUnion.mp (hcov ▸ mem_univ x)
  refine ⟨?_, fun a ha => ?_⟩
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨i, hi⟩ := hmem x
    obtain ⟨t, ht, hteq⟩ := isOpen_induced_iff.mp (h i).1.isOpen_compl
    refine ⟨t ∩ U i, fun y ⟨hyt, hyU⟩ => ?_, ht.inter (hU i), ?_, hi⟩
    · have : (⟨y, hyU⟩ : U i) ∈ (Subtype.val ⁻¹' t) := hyt
      rw [hteq] at this
      exact this
    · have : (⟨x, hi⟩ : U i) ∈ ((Subtype.val : U i → M) ⁻¹' Y)ᶜ := hx
      rw [← hteq] at this
      exact this
  · obtain ⟨i, hi⟩ := hmem a
    obtain ⟨φ, σ, haφ, -, hφ⟩ := (h i).2 a ⟨ha, hi⟩
    exact ⟨φ, σ, haφ, hφ⟩

end Manifold
