/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Submanifold.Manifold
import Hironaka.Manifold.AdaptedChart
public import Hironaka.Manifold.Submanifold.Restrict
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
/-!
# A closed submanifold as a bundled analytic manifold; restriction of analytic maps

The restriction of a blow-up sequence of `X` to a closed subscheme `S ⊆ X` is a blow-up sequence
starting with `S` [Kol07, Definition 30.2]. A finite succession (`FiniteSuccession`) starts with a
bundled `AnalyticManifold 𝕜 E`, so a closed submanifold `S ⊆ M` of codimension `s`
(`IsClosedSubmanifold ψ S s`) has to be bundled with its induced structure: the charts are the
complementary coordinates of the adapted charts (`IsAdaptedChart.chartOn`), modelled on `𝕜^{n-s}`
(`IsClosedSubmanifold.chartedSpace`, `IsClosedSubmanifold.isManifold'`), and the space is
Hausdorff and second countable as a subspace of `M`. That a smooth closed subspace of a manifold
is a manifold, locally a coordinate subspace, is [BM97, (3.8)(2)]. This module provides

* `IsClosedSubmanifold.toAnalyticManifold hS : AnalyticManifold 𝕜 (Fin (n - s) → 𝕜)`;
* `IsClosedSubmanifold.contMDiff_codRestrict`: an analytic map into `M` with values in `S` is
  analytic into `S` for the induced charts (in the induced chart at the image point it is
  `projCompl σ ∘ ψ ∘ φ ∘ f`, a composition of analytic maps; `contMDiffAt_iff_target`);
* `IsClosedSubmanifold.restrictMap`: the restriction `S' → S` of an analytic map `f : M' → M` with
  `f(S') ⊆ S` between closed submanifolds of the same codimension `s` in manifolds modelled on `E`,
  as a bundled analytic map between the bundled submanifolds (the inclusion `S' → M'` is analytic,
  `IsClosedSubmanifold.contMDiff_val`); the restricted blow-downs `π_i|_{S_{i+1}} : S_{i+1} → S_i`
  of a restricted blow-up sequence are its instances;
* `IsClosedSubmanifold.congr_chart`: the notion of closed submanifold does not depend on the
  linear chart `ψ : E ≃ 𝕜ⁿ` (a succession carries one chosen chart per step,
  `FiniteSuccession.chartAt`): an adapted chart for `ψ` becomes one for `ψ'` after the linear
  change `ψ'⁻¹ ∘ ψ` of `E`, with the same coordinate functions.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] {S : Set M} {s : ℕ}

/-! ### The bundle -/

/-- A closed submanifold `S ⊆ M` of codimension `s` as a bundled analytic manifold modelled on
`𝕜^{n-s}`, with the induced charts (`IsClosedSubmanifold.chartedSpace`,
`IsClosedSubmanifold.isManifold'`); Hausdorff and second countable as a subspace of `M`. It is the
manifold with which the restriction of a blow-up sequence to `S` starts [Kol07, Definition 30.2]. -/
def IsClosedSubmanifold.toAnalyticManifold [T2Space M] [SecondCountableTopology M]
    (hS : IsClosedSubmanifold ψ S s) :
        AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜) :=
  letI := hS.chartedSpace
  haveI := hS.isManifold'
  ⟨S⟩

/-- A subset `Y ⊆ M` read inside the bundled submanifold `S`: the preimage of `Y` under the
inclusion `S → M` (Kollár's restricted centre `Z_i ∩ S_i`, a subset of `S_i`
[Kol07, Definition 30.2]). -/
def IsClosedSubmanifold.preimageVal [T2Space M] [SecondCountableTopology M]
    (hS : IsClosedSubmanifold ψ S s) (Y : Set M) : Set hS.toAnalyticManifold :=
  {p | (p : S).1 ∈ Y}

omit [IsManifold 𝓘(𝕜, E) ω M] in
theorem IsClosedSubmanifold.mem_preimageVal [T2Space M] [SecondCountableTopology M]
    (hS : IsClosedSubmanifold ψ S s) (Y : Set M) (p : hS.toAnalyticManifold) :
    p ∈ hS.preimageVal Y ↔ (p : S).1 ∈ Y :=
  Iff.rfl

/-! ### Restriction of analytic maps to closed submanifolds -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {N : Type u} [TopologicalSpace N]
  [ChartedSpace F N]

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- An analytic map into `M` with values in the closed submanifold `S` is analytic into `S` for the
induced charts: in the induced chart at the image point it reads `projCompl σ ∘ ψ ∘ φ ∘ f`. -/
theorem IsClosedSubmanifold.contMDiff_codRestrict (hS : IsClosedSubmanifold ψ S s) {f : N → M}
    (hf : ContMDiff 𝓘(𝕜, F) 𝓘(𝕜, E) ω f) (hfS : ∀ x, f x ∈ S) :
    letI := hS.chartedSpace
    ContMDiff 𝓘(𝕜, F) 𝓘(𝕜, Fin (n - s) → 𝕜) ω (Set.codRestrict f S hfS) := by
  let _i := hS.chartedSpace
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨(hf.continuous.codRestrict hfS).continuousAt, ?_⟩
  set y : S := Set.codRestrict f S hfS x with hy
  set φ := hS.adaptedChartAt y with hφdef
  set σ := hS.adaptedIdx y with hσdef
  have hφ : IsAdaptedChart ψ S φ σ := hS.isAdaptedChart_adaptedChartAt y
  have hyφ : (y : M) ∈ φ.source := hS.mem_source_adaptedChartAt y
  have heq : (extChartAt 𝓘(𝕜, Fin (n - s) → 𝕜) y ∘ Set.codRestrict f S hfS) =
      fun z => projCompl σ (ψ (φ (f z))) := by
    funext z
    rfl
  rw [heq]
  have h1 : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, Fin (n - s) → 𝕜) ω (fun v : E => projCompl σ (ψ v))
      (φ (f x)) :=
    (contMDiff_iff_contDiff.mpr ((contDiff_projCompl σ).comp ψ.contDiff)).contMDiffAt
  have h2 : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω φ (f x) :=
    (contMDiffOn_of_mem_maximalAtlas (n := ω) hφ.1).contMDiffAt (φ.open_source.mem_nhds hyφ)
  exact h1.comp x (h2.comp x (hf x))

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  {S' : Set M'}

/-- The restriction of an analytic map `f : M' → M` with `f(S') ⊆ S` to closed submanifolds of
the same codimension, as a bundled analytic map between the bundled submanifolds. The blow-downs
`π_i^S : S_{i+1} → S_i` of a restricted blow-up sequence [Kol07, Definition 30.2] are of this
form. -/
def IsClosedSubmanifold.restrictMap [T2Space M] [SecondCountableTopology M] [T2Space M']
    [SecondCountableTopology M'] (hS' : IsClosedSubmanifold ψ S' s) (hS : IsClosedSubmanifold ψ S s)
    (f : M' → M) (hf : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω f) (hfS : ∀ x ∈ S', f x ∈ S) :
    AnalyticMap hS'.toAnalyticManifold hS.toAnalyticManifold :=
  letI := hS'.chartedSpace
  letI := hS.chartedSpace
  ⟨Set.codRestrict (f ∘ (Subtype.val : S' → M')) S fun p => hfS p p.2,
    hS.contMDiff_codRestrict (hf.comp hS'.contMDiff_val) _⟩

omit [IsManifold 𝓘(𝕜, E) ω M] [IsManifold 𝓘(𝕜, E) ω M'] in
/-- The restricted map is the restriction: its values in `M` are those of `f` (`rfl`). -/
theorem IsClosedSubmanifold.restrictMap_apply [T2Space M] [SecondCountableTopology M] [T2Space M']
    [SecondCountableTopology M'] (hS' : IsClosedSubmanifold ψ S' s) (hS : IsClosedSubmanifold ψ S s)
    (f : M' → M) (hf : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω f) (hfS : ∀ x ∈ S', f x ∈ S)
    (p : hS'.toAnalyticManifold) :
    Subtype.val (hS'.restrictMap hS f hf hfS p) = f (Subtype.val p) :=
  rfl

/-! ### Independence of the chart `ψ` -/

variable {Y : Set M} {c : ℕ}

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- An adapted chart for `ψ` becomes an adapted chart for `ψ'` (the same source, the same
coordinate functions) after the linear change of `E` carrying `ψ` to `ψ'`. -/
theorem IsAdaptedChart.exists_congr_chart {n' : ℕ} (ψ' : E ≃L[𝕜] (Fin n' → 𝕜))
    {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n} (hφ : IsAdaptedChart ψ Y φ σ) :
    ∃ (φ' : OpenPartialHomeomorph M E) (σ' : Fin c ↪ Fin n'), φ'.source = φ.source ∧
      IsAdaptedChart ψ' Y φ' σ' ∧ ∀ x ∈ φ.source, ∀ i, ψ' (φ' x) (σ' i) = ψ (φ x) (σ i) := by
  have hn : n = n' := by
    have h := (ψ.symm.trans ψ').toLinearEquiv.finrank_eq
    simpa [Module.finrank_fin_fun] using h
  subst hn
  set L : E ≃L[𝕜] E := ψ.trans ψ'.symm with hL
  have hL0 : L.toHomeomorph.toOpenPartialHomeomorph ∈ contDiffGroupoid ω 𝓘(𝕜, E) :=
    mem_contDiffGroupoid_self _ (L.contDiff.contDiffOn) (L.symm.contDiff.contDiffOn)
  refine ⟨φ.trans L.toHomeomorph.toOpenPartialHomeomorph, σ, ?_, ⟨trans_mem_maximalAtlas hφ.1 hL0,
    fun x hx => ?_⟩, fun x hx i => ?_⟩
  · rw [OpenPartialHomeomorph.trans_source]
    ext x
    exact ⟨fun h => h.1, fun h => ⟨h, Set.mem_univ _⟩⟩
  · rw [OpenPartialHomeomorph.trans_source] at hx
    rw [hφ.2 x hx.1]
    refine forall_congr' fun i => ?_
    change ψ (φ x) (σ i) = 0 ↔ ψ' (ψ'.symm (ψ (φ x))) (σ i) = 0
    rw [ψ'.apply_symm_apply]
  · change ψ' (ψ'.symm (ψ (φ x))) (σ i) = ψ (φ x) (σ i)
    rw [ψ'.apply_symm_apply]

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The notion "closed submanifold of codimension `c`" does not depend on the linear chart
`ψ : E ≃ 𝕜ⁿ` (a succession carries one chosen chart per step). Not in the sources; a routine
change of charts. -/
theorem IsClosedSubmanifold.congr_chart {n' : ℕ} (ψ' : E ≃L[𝕜] (Fin n' → 𝕜))
    (hY : IsClosedSubmanifold ψ Y c) : IsClosedSubmanifold ψ' Y c where
  isClosed := hY.isClosed
  exists_adaptedChart a ha := by
    obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart a ha
    obtain ⟨φ', σ', hs, hφ', -⟩ := hφ.exists_congr_chart ψ'
    exact ⟨φ', σ', hs ▸ haφ, hφ'⟩

end Manifold

end
