/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Defs
import Hironaka.Manifold.IdealSheaf.Vanishing
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Resolution.Analytic.Principalization.MonomialStalk
import Hironaka.Resolution.Analytic.Wlo09.BoundaryBridge
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The local Hadamard lemma for a single coordinate on an unbundled manifold

The local Hadamard lemma `vanishingStalk_zeroSet_eq_span_coord`
(`Hironaka/Resolution/Analytic/Wlo09/BoundaryBridge.lean`) reads the vanishing stalk of the zero set
`φ.source ∩ {z_σ = 0}` of chart coordinates at a point of
the chart as the span of those coordinates, for a bundled manifold `M : AnalyticManifold` (its
proof restricts to the chart's source, `M.restrict U`). A statement that binds its manifold as a
charted type, with the manifold structure as instances, may need the vanishing stalk of a strict
transform at a point of a blow-up chart, where the strict transform is
the zero set of one coordinate on the chart's source (`strictTransform_inter_source_of_ne`,
`strictTransform_inter_source_of_ne_off`) but is not known to be a closed submanifold without a
simple-normal-crossing hypothesis on the centre. `vanishingStalk_eq_span_coord_of_forall_mem_iff`
is the single-coordinate form of the local lemma for such a manifold, with no hypothesis on `Z`
beyond its description on the chart's source: the bundled lemma applied to the bundle `⟨M⟩` of the
charted type (whose instance fields are exactly the binders), plus the unit-ideal case off `Z`.
Not in the sources; the coordinate description of the members of a simple normal crossing divisor
is [Kol07, Definition 24].
-/

public section

open Set TopologicalSpace Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

namespace Hironaka.Manifold

open _root_.Manifold

universe u

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M]

/-- **The vanishing stalk at a point `p` of a chart `φ` of a set `Z` that is, on the chart's source,
the zero set of the coordinate `k`, is spanned by that coordinate**, with no closedness or
submanifold hypothesis on `Z`. The single-coordinate form of `vanishingStalk_zeroSet_eq_span_coord`
for an unbundled manifold: the vanishing stalk sees only `Z ∩ φ.source`
(`vanishingStalk_inter_of_mem_nhds`); on `Z` the bundled lemma at `⟨M⟩ : AnalyticManifold 𝕜 E`
(whose five instance fields are exactly the binders here) gives the span of the single coordinate
(`singleEmb`); off `Z`, `p` lies outside the closure of `Z ∩ φ.source` (the open
`φ.source ∩ {ψ (φ ·) k ≠ 0}` contains `p` and misses it), so both sides are the unit ideal
(`vanishingStalk_eq_top_of_notMem_closure`, `isUnit_coord_of_ne_zero`). Not in the sources. -/
theorem vanishingStalk_eq_span_coord_of_forall_mem_iff {φ : OpenPartialHomeomorph M E}
    (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {Z : Set M} {k : Fin n}
    (hS : ∀ x ∈ φ.source, x ∈ Z ↔ ψ (φ x) k = 0) {p : M} (hp : p ∈ φ.source) :
    vanishingStalk (𝕜 := 𝕜) (E := E) Z p = Ideal.span {coord E ψ φ hφ hp k} := by
  rw [← vanishingStalk_inter_of_mem_nhds (φ.open_source.mem_nhds hp)]
  by_cases hpZ : p ∈ Z
  · -- on `Z`: the local Hadamard lemma of the bundled manifold `⟨M⟩`
    have hZ : Z ∩ φ.source = φ.source ∩ {y | ∀ i : Fin 1, ψ (φ y) (singleEmb k i) = 0} := by
      ext y
      constructor
      · rintro ⟨hyZ, hy⟩
        exact ⟨hy, fun _ => (hS y hy).mp hyZ⟩
      · rintro ⟨hy, h0⟩
        exact ⟨(hS y hy).mpr (h0 0), hy⟩
    have hloc : vanishingStalk (𝕜 := 𝕜) (E := E)
        (φ.source ∩ {y | ∀ i : Fin 1, ψ (φ y) (singleEmb k i) = 0}) p =
          Ideal.span (Set.range fun i => coord E ψ φ hφ hp (singleEmb k i)) :=
      vanishingStalk_zeroSet_eq_span_coord (M := ⟨M⟩) ψ hφ hp (singleEmb k)
        fun _ => (hS p hp).mp hpZ
    rw [hZ, hloc, Set.range_unique, singleEmb_apply]
  · -- off `Z`: `p` is not in the closure of `Z ∩ φ.source`, and the coordinate is a unit at `p`
    have hne : ψ (φ p) k ≠ 0 := fun h0 => hpZ ((hS p hp).mpr h0)
    have hopen : IsOpen (φ.source ∩ {y | ψ (φ y) k ≠ 0}) :=
      φ.continuousOn.isOpen_inter_preimage φ.open_source
        (isOpen_ne_fun ((continuous_apply k).comp ψ.continuous) continuous_const)
    have hnot : p ∉ closure (Z ∩ φ.source) := fun hcl => by
      obtain ⟨y, ⟨-, hyne⟩, hyZ, hy⟩ := mem_closure_iff.mp hcl _ hopen ⟨hp, hne⟩
      exact hyne ((hS y hy).mp hyZ)
    rw [vanishingStalk_eq_top_of_notMem_closure hnot, eq_comm, Ideal.span_singleton_eq_top]
    exact isUnit_coord_of_ne_zero φ hφ hp hne

end Hironaka.Manifold
