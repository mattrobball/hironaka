/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.LocalIsoEquiv
public import Hironaka.Manifold.IdealSheaf.Basic
import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Manifold.Submanifold.Ideal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Agreement on a closed analytic subspace: set-level consequences

`AgreeOnSubspace ψ ψ' J` (`Hironaka/Resolution/Analytic/LocalIsoEquiv.lean`), the analytic form
of condition (4′) of Kollár's étale equivalence [Kol07, Definition 91], says `ψ^*h − ψ'^*h ∈ J_u`
for every local section `h` near `ψ u` and `ψ' u`. Its set-level content: on the closed analytic
subspace `V(J) = {u | J_u ≠ 𝒪_{U,u}}` the two maps coincide
(`AgreeOnSubspace.apply_eq_of_mem_support`) — if `ψ u ≠ ψ' u`, a locally constant analytic
section on the union of two disjoint neighbourhoods, `1` near `ψ u` and `0` near `ψ' u`, has
`ψ^*h − ψ'^*h = 1 ∈ J_u`. This is the step "`ψ_i|_{W_i} = ψ'_i|_{W_i}`, thus
`Z_i = ψ_i(Z^U_i) = ψ'_i(Z^U_i) = Z'_i`" of Kollár's proof of the uniqueness of blow-up sequences
[Kol07, Theorem 97, proof]. Also the symmetry of the relation and its monotonicity in `J`.
-/

public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory Set Filter Topology
open scoped Manifold ContDiff

universe u v

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U M : AnalyticManifold.{u} 𝕜 E} {ψ ψ' : AnalyticMap U M} {J : AnalyticManifold.IdealSheaf U}

theorem AgreeOnSubspace.symm (h : AgreeOnSubspace ψ ψ' J) : AgreeOnSubspace ψ' ψ J := by
  intro u W hu' hu f
  have := h u W hu hu' f
  rw [← neg_mem_iff, neg_sub] at this
  exact this

theorem AgreeOnSubspace.mono {J' : AnalyticManifold.IdealSheaf U} (h : AgreeOnSubspace ψ ψ' J)
    (hJ : J ≤ J') : AgreeOnSubspace ψ ψ' J' := fun u W hu hu' f => hJ u (h u W hu hu' f)

/-- The germ at `u` of a section that is constant near `ψ u` pulls back to the constant germ. -/
theorem germMap_germ_eq_const_of_eventuallyEq {W : Opens M} {u : U} (hu : ψ u ∈ W)
    (f : (structureSheaf 𝕜 E M).presheaf.obj (op W)) {c : 𝕜}
    (hf : ∀ᶠ x in 𝓝 (ψ u), extendSection 𝕜 E f x = c) :
    germMap (⇑ψ) ψ.contMDiff u ((structureSheaf 𝕜 E M).presheaf.germ W (ψ u) hu f) =
      const 𝕜 E U u c := by
  apply stalkToGerm_injective
  rw [stalkToGerm_germMap, stalkToGerm_structureSheaf_germ, stalkToGerm_const,
    Germ.coe_compTendsto]
  refine Germ.coe_eq.mpr ?_
  filter_upwards [(ψ.contMDiff.continuous.tendsto u).eventually hf] with x hx
  exact hx

/-- Kollár's "`ψ_i|_{W_i} = ψ'_i|_{W_i}`" [Kol07, Theorem 97, proof]: two maps agreeing on the
closed analytic subspace `V(J)` coincide at every point of `V(J)`. -/
theorem AgreeOnSubspace.apply_eq_of_mem_support (h : AgreeOnSubspace ψ ψ' J) {u : U}
    (hu : u ∈ J.support) : ψ u = ψ' u := by
  classical
  by_contra hne
  obtain ⟨W₁, W₂, hW₁, hW₂, h1, h2, hdisj⟩ := t2_separation hne
  let W : Opens M := ⟨W₁ ∪ W₂, hW₁.union hW₂⟩
  let f : M → 𝕜 := fun x => if x ∈ W₁ then 1 else 0
  have hf : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω f W := by
    refine contMDiffOn_of_locally_contMDiffOn fun x hx => ?_
    rcases (hx : x ∈ W₁ ∪ W₂) with hx | hx
    · refine ⟨W₁, hW₁, hx, (contMDiffOn_const (c := (1 : 𝕜))).congr fun y hy => ?_⟩
      simp [f, hy.2]
    · refine ⟨W₂, hW₂, hx, (contMDiffOn_const (c := (0 : 𝕜))).congr fun y hy => ?_⟩
      have : y ∉ W₁ := fun hy1 => Set.disjoint_left.mp hdisj hy1 hy.2
      simp [f, this]
  set s := sectionOfContMDiffOn f W hf with hs
  have hu1 : ψ u ∈ W := Or.inl h1
  have hu2 : ψ' u ∈ W := Or.inr h2
  have hmem := h u W hu1 hu2 s
  have e1 : germMap (⇑ψ) ψ.contMDiff u ((structureSheaf 𝕜 E M).presheaf.germ W (ψ u) hu1 s) =
      const 𝕜 E U u 1 := by
    refine germMap_germ_eq_const_of_eventuallyEq hu1 s ?_
    filter_upwards [hW₁.mem_nhds h1] with x hx
    rw [extendSection_of_mem 𝕜 E s (Or.inl hx : x ∈ W), hs, sectionOfContMDiffOn_apply]
    simp [f, hx]
  have e2 : germMap (⇑ψ') ψ'.contMDiff u ((structureSheaf 𝕜 E M).presheaf.germ W (ψ' u) hu2 s) =
      const 𝕜 E U u 0 := by
    refine germMap_germ_eq_const_of_eventuallyEq hu2 s ?_
    filter_upwards [hW₂.mem_nhds h2] with x hx
    rw [extendSection_of_mem 𝕜 E s (Or.inr hx : x ∈ W), hs, sectionOfContMDiffOn_apply]
    have : x ∉ W₁ := fun hx1 => Set.disjoint_left.mp hdisj hx1 hx
    simp [f, this]
  rw [e1, e2, map_one, map_zero, sub_zero] at hmem
  exact hu ((Ideal.eq_top_iff_one _).mpr hmem)

end Hironaka.Manifold

end
