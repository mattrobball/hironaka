/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Transform.Basic
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.Submanifold.Components
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Hironaka's weak transform has the colon stalks

The weak transform of `I` by the blowing-up `π` with centre `Y` divides `π⁻¹(I)` by the `ν`-th power
of `I_F`, `ν` the generic order of `I` along the connected component of `Y` through the point
[Hir64, Ch. 0, §5, p. 142]. The definition (`IdealSheaf.weakTransformOf`, the unbundled reading of
`AnalyticManifold.IdealSheaf.weakTransform`) uses the pointwise exponent
`a' ↦ (genericOrdAlong I_Y I (π a')).toNat`; the existence theorem of
`Hironaka.Manifold.BlowUp.Transform.Colon` applies because this exponent is at most the order of `I`
along `Y` at `π a'` (`genericOrdAlong_le`: the infimum over the component through `π a'` is bounded
by the value at `π a'`) and is locally constant on the exceptional divisor: near a point of `Y`, the
points of `Y` lie in a connected chart ball, hence in the same connected component of `Y`
(`IsClosedSubmanifold.eventually_connectedComponentIn_eq`, from
`IsAdaptedChart.exists_preconnected_mem_nhds`), and the generic order only depends on the component
(`genericOrdAlong_eq_of_mem_connectedComponentIn`). The definition carries no hypothesis `I ≠ 0`
(Hironaka's standing assumption, under which the generic order is finite): where the order is `⊤`
the exponent is `0` and the weak transform is the total transform there.

The result, `isDivExceptional_weakTransformOf`, is transferred to the weak transform of the
vocabulary of the main theorems in `Hironaka.Manifold.BlowUp.Transform.Bundled`.
-/

public section

open TopologicalSpace Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

section Generic

variable {X : TopCat} {𝒪 : TopCat.Sheaf CommRingCat X}

/-- The generic order along the component through `a` depends only on the component. -/
theorem IdealSheaf.genericOrdAlong_eq_of_mem_connectedComponentIn (D J : IdealSheaf 𝒪) {a b : X}
    (h : b ∈ connectedComponentIn D.support a) :
    IdealSheaf.genericOrdAlong D J b = IdealSheaf.genericOrdAlong D J a := by
  unfold IdealSheaf.genericOrdAlong
  rw [connectedComponentIn_eq h]

/-- The generic order along the component through `a ∈ D` is at most the order along `D` at
`a`. -/
theorem IdealSheaf.genericOrdAlong_le (D J : IdealSheaf 𝒪) {a : X} (ha : a ∈ D.support) :
    IdealSheaf.genericOrdAlong D J a ≤ IdealSheaf.ordAlongIdeal D J a := by
  unfold IdealSheaf.genericOrdAlong
  exact biInf_le (fun y => IdealSheaf.ordAlongIdeal D J y) (mem_connectedComponentIn ha)

end Generic

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M}
  {c : ℕ}

/-- A closed submanifold is locally connected: near a point `a` of `Y`, the points of `Y` lie in
the connected component of `Y` through `a`. -/
theorem IsClosedSubmanifold.eventually_connectedComponentIn_eq (hY : IsClosedSubmanifold ψ Y c)
    {a : M} (ha : a ∈ Y) :
    ∀ᶠ b in 𝓝 a, b ∈ Y → connectedComponentIn Y b = connectedComponentIn Y a := by
  obtain ⟨φ, σ, has, hφ⟩ := hY.exists_adaptedChart a ha
  obtain ⟨V, hV, -, hVc, -⟩ := hφ.exists_preconnected_mem_nhds ha has univ_mem
  obtain ⟨O, hO, hOV⟩ := (mem_nhds_subtype Y ⟨a, ha⟩ V).mp hV
  have hsub : Subtype.val '' V ⊆ connectedComponentIn Y a :=
    (hVc.image _ continuous_subtype_val.continuousOn).subset_connectedComponentIn
      ⟨⟨a, ha⟩, mem_of_mem_nhds hV, rfl⟩ (by rintro _ ⟨y, -, rfl⟩; exact y.2)
  filter_upwards [hO] with b hbO hbY
  exact (connectedComponentIn_eq (hsub ⟨⟨b, hbY⟩, hOV hbO, rfl⟩)).symm

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M}

/-- The weak transform has the colon stalks `(π⁻¹(I)_{a'} : I_{F,a'}^{ν})`, `ν` the generic order
of `I` along the component of `Y` through `π a'` [Hir64, Ch. 0, §5, p. 142]. -/
theorem isDivExceptional_weakTransformOf [IsManifold 𝓘(𝕜, E) ω M] [T2Space M]
    [SecondCountableTopology M]
    (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) :
    IdealSheaf.IsDivExceptional (I.pullback π h.contMDiff)
      (hY.idealSheaf.pullback π h.contMDiff)
      (fun a' => (IdealSheaf.genericOrdAlong hY.idealSheaf I (π a')).toNat)
      (IdealSheaf.weakTransformOf hY h I) := by
  have hex : ∃ J' : IdealSheaf (structureSheaf 𝕜 E M'), IdealSheaf.IsDivExceptional
      (I.pullback π h.contMDiff) (hY.idealSheaf.pullback π h.contMDiff)
      (fun a' => (IdealSheaf.genericOrdAlong hY.idealSheaf I (π a')).toNat) J' := by
    refine ⟨IdealSheaf.ofStalks _ _ (hasLocalGenerators_colon hY h I _ ?_ ?_),
      fun a' => IdealSheaf.stalkIdeal_ofStalks _ _ a'⟩
    · intro a' ha'
      refine (ENat.natCast_toNat_le_self _).trans (IdealSheaf.genericOrdAlong_le _ _ ?_)
      rw [hY.cosupport_idealSheaf]
      exact ha'
    · intro a' ha'
      filter_upwards [Filter.Tendsto.eventually h.contMDiff.continuous.continuousAt
        (hY.eventually_connectedComponentIn_eq ha')] with b hb hbY
      unfold IdealSheaf.genericOrdAlong
      rw [hY.cosupport_idealSheaf, hb hbY]
  unfold IdealSheaf.weakTransformOf AnalyticManifold.IdealSheaf.weakTransform
  split_ifs with hex'
  · exact Classical.choose_spec hex'
  · exact absurd hex hex'

end Manifold
