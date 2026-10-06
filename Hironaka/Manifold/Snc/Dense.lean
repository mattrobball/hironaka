/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Snc.Defs
import Hironaka.Manifold.Snc.Coherence
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# The complement of a simple normal crossings divisor is dense

The complement of the support of an snc divisor is dense (`IsSnc.dense_compl_support`): near a
point `a` the support is the union of the components through `a` (`IsSnc.exists_nhds_support_eq`,
local finiteness), and in an snc chart at `a` those components are finitely many coordinate
hyperplanes (`IsSncChartAt`, the coordinate indices `c` injective), whose complement is dense in
the model space `E` (a proper closed subspace of a normed space has empty interior — Mathlib's
`Submodule.eq_top_of_nonempty_interior'`; finitely many, by the Baire property of the
finite-dimensional `E`). This is the density that makes a resolution a modification: Hironaka
remarks that the complement of the exceptional set is dense for reduced complex-analytic spaces but
not always for real ones [Hir64, p. 111], and Bierstone–Milman ask for `Reg X` to be Zariski-dense
[BM97, Remarks 1.7 (2)]; for the boundary divisor of a resolution the density holds on the nose.

* `dense_setOf_coord_ne_zero`: the complement of one coordinate hyperplane `{ψ z i = 0}` of `E` is
  dense;
* `dense_setOf_forall_coord_ne_zero`: the complement of finitely many is dense;
* `HypersurfaceFamily.IsSnc.exists_notMem_support_of_mem_nhds`: every neighbourhood of a point
  contains a point off the support;
* `HypersurfaceFamily.IsSnc.dense_compl_support`: the complement of the support is dense.

It is used to define the set of a simple normal crossings divisor on an analytic space
(`Hironaka/AnalyticSpace/SncDivisorSetLocal.lean`).
-/

public section

open Set Topology TopologicalSpace Filter
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜))

/-- The complement of the coordinate hyperplane `{z | ψ z i = 0}` of `E` is dense: the hyperplane
is a proper closed subspace, hence has empty interior (`Submodule.eq_top_of_nonempty_interior'`). -/
theorem dense_setOf_coord_ne_zero (i : Fin n) : Dense {z : E | ψ z i ≠ 0} := by
  set S : Submodule 𝕜 E := (LinearMap.ker (LinearMap.proj i : (Fin n → 𝕜) →ₗ[𝕜] 𝕜)).comap
    ψ.toLinearEquiv.toLinearMap with hS
  have hmem : ∀ z : E, z ∈ S ↔ ψ z i = 0 := fun z => by
    simp [hS, Submodule.mem_comap, LinearMap.mem_ker]
  have hne : S ≠ ⊤ := by
    intro htop
    have h1 : ψ.symm (Pi.single i (1 : 𝕜)) ∈ S := htop ▸ Submodule.mem_top
    rw [hmem, ψ.apply_symm_apply, Pi.single_eq_same] at h1
    exact one_ne_zero h1
  have := NormedField.nhdsWithin_isUnit_neBot (α := 𝕜)
  have hint : interior (S : Set E) = ∅ := by
    by_contra h
    exact hne (Submodule.eq_top_of_nonempty_interior' S (Set.nonempty_iff_ne_empty.mpr h))
  have hd := interior_eq_empty_iff_dense_compl.mp hint
  convert hd using 1
  ext z
  simp [hmem]

/-- The complement of finitely many coordinate hyperplanes of `E` is dense (`E` is
finite-dimensional, hence complete and a Baire space). -/
theorem dense_setOf_forall_coord_ne_zero {J : Type*} [Finite J] (c : J → Fin n) :
    Dense {z : E | ∀ j, ψ z (c j) ≠ 0} := by
  have : FiniteDimensional 𝕜 E := ψ.symm.toLinearEquiv.finiteDimensional
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have h := dense_iInter_of_isOpen (f := fun j : J => {z : E | ψ z (c j) ≠ 0})
    (fun j => isOpen_ne.preimage ((continuous_apply (c j)).comp ψ.continuous))
    (fun j => dense_setOf_coord_ne_zero ψ (c j))
  convert h using 1
  ext z
  exact ⟨fun hz => mem_iInter.mpr hz, fun hz => mem_iInter.mp hz⟩

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

namespace HypersurfaceFamily

variable {F : HypersurfaceFamily M}

variable {ψ} in
/-- Every neighbourhood of a point `a` of the manifold contains a point off the support of an snc
divisor: near `a` the support is the union of the components through `a`
(`IsSnc.exists_nhds_support_eq`), which in an snc chart at `a` are finitely many coordinate
hyperplanes, and the complement of finitely many coordinate hyperplanes is dense in the model. -/
theorem IsSnc.exists_notMem_support_of_mem_nhds (hF : F.IsSnc ψ) {a : M} {N : Set M}
    (hN : N ∈ 𝓝 a) : ∃ x ∈ N, x ∉ F.support := by
  obtain ⟨V, hVo, haV, hV⟩ := hF.exists_nhds_support_eq a
  obtain ⟨φ, c, hφatlas, haφ, hchart, hcinj⟩ := hF.2.2 a
  obtain ⟨N', hN'N, hN'o, haN'⟩ := mem_nhds_iff.mp hN
  have : Finite {j // a ∈ F.hyp j} := Finite.of_injective c hcinj
  have hWo : IsOpen (N' ∩ V ∩ φ.source) := (hN'o.inter hVo).inter φ.open_source
  have haW : a ∈ N' ∩ V ∩ φ.source := ⟨⟨haN', haV⟩, haφ⟩
  have himg : IsOpen (φ '' (N' ∩ V ∩ φ.source)) :=
    (φ.isOpen_image_iff_of_subset_source fun _ hx => hx.2).mpr hWo
  obtain ⟨z, hz, x, hxW, rfl⟩ :=
    (dense_setOf_forall_coord_ne_zero ψ c).exists_mem_open himg ⟨φ a, a, haW, rfl⟩
  have hz' : ∀ j, ψ (φ x) (c j) ≠ 0 := hz
  refine ⟨x, hN'N hxW.1.1, fun hxs => ?_⟩
  obtain ⟨j, haj, hxj⟩ := (hV x hxW.1.2).mp hxs
  exact hz' ⟨j, haj⟩ ((hchart ⟨j, haj⟩ x hxW.2).mp hxj)

variable {ψ} in
/-- The complement of the support of a simple normal crossings divisor is dense. -/
theorem IsSnc.dense_compl_support (hF : F.IsSnc ψ) : Dense F.supportᶜ :=
  dense_iff_inter_open.mpr fun _U hU ⟨_a, ha⟩ =>
    let ⟨x, hxU, hxs⟩ := hF.exists_notMem_support_of_mem_nhds (hU.mem_nhds ha)
    ⟨x, hxU, hxs⟩

end HypersurfaceFamily

end Manifold
