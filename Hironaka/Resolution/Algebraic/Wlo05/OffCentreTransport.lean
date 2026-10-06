/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses
import Hironaka.Resolution.Algebraic.Kol07.StrictTransformSupport
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Snc.TotalTransformOffCentre
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# A blow-up whose centre misses a closed subscheme

In the isolation passage of the proof of [Wlo05, Theorem 4.7.1], after the strict transform of a
component is isolated, the later centres of the modified run either miss the isolated strict
transforms or are strata of the boundary transversal to them. This module is the first case: **a
blow-up whose centre is disjoint from a closed subscheme `Z` changes nothing near `Z`**. The
blow-up is an isomorphism off the exceptional divisor (`isIso_stalkMap_π_of_notMem_support`), so
the pull-back of the ideal of `Z` is its strict transform, simple normal crossings with the
boundary pass to the total transform and the strict transform (the snc coordinates transport along
the isomorphism of stalks, `exists_snc_data_totalTransform_of_notMem_support`), and "contained in
no member near any point" passes as well. Stalkwise throughout; no coordinates are computed.
Simple normal crossings and the total transform are those of [Kol07, Definition 24] and
[Kol07, Definition 25]. Used in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedProtected` and, for the
two elementary lemmas on disjoint closed sets, throughout the loop modules.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData
  Scheme BlowUpSequence Hironaka.Sequence

namespace Hironaka.Resolution

variable {X : Scheme.{u}}

/-- A point of one of two disjoint closed sets is not in the other. -/
theorem notMem_of_disjoint_closeds {A B : Closeds X} (h : Disjoint A B) {x : X} (hx : x ∈ A) :
    x ∉ B := fun hxB => by
  have hmem : x ∈ ((A ⊓ B : Closeds X) : Set X) := by
    rw [Closeds.coe_inf]
    exact ⟨hx, hxB⟩
  have hbot : x ∈ ((⊥ : Closeds X) : Set X) := h.le_bot hmem
  rw [Closeds.coe_bot] at hbot
  exact hbot

/-- Two closed sets are disjoint iff no point of the first lies in the second. -/
theorem disjoint_closeds_iff {A B : Closeds X} : Disjoint A B ↔ ∀ x ∈ A, x ∉ B := by
  refine ⟨fun h x hx hxB => notMem_of_disjoint_closeds h hx hxB, fun h => ?_⟩
  refine disjoint_iff_inf_le.mpr fun x hx => ?_
  have hmem : x ∈ ((A ⊓ B : Closeds X) : Set X) := hx
  rw [Closeds.coe_inf] at hmem
  exact (h x hmem.1 hmem.2).elim

variable (D Z : X.IdealSheafData)

/-- A point of the strict transform of `Z` along a centre disjoint from `Z` is off the exceptional
divisor. -/
theorem notMem_support_exceptionalDivisor_of_mem_support_strictTransform [IsLocallyNoetherian X]
    (hdisj : Disjoint D.support Z.support) {x' : D.blowUp}
    (hx' : x' ∈ (Z.strictTransform D).support) : x' ∉ D.exceptionalDivisor.support := fun h =>
  notMem_of_disjoint_closeds hdisj ((mem_support_comap_iff_apply D D.blowUpπ x').mp h)
    (blowUpπ_mem_support_of_mem_support_strictTransform D Z hx')

/-- Off the exceptional divisor the stalk of the strict transform is the image of the stalk below
(`stalkIdeal_strictTransformAlong_of_notMem_support` for `strictTransform`). -/
theorem stalkIdeal_strictTransform_of_notMem_support_exceptionalDivisor {x' : D.blowUp}
    (hx' : x' ∉ D.exceptionalDivisor.support) :
    (Z.strictTransform D).stalkIdeal x' =
      (Z.stalkIdeal (D.blowUpπ x')).map (D.blowUpπ.stalkMap x').hom :=
  stalkIdeal_strictTransformAlong_of_notMem_support D Z hx'

/-- The pull-back of the ideal of a closed subscheme along a blow-up whose centre misses it is its
strict transform (the isolation passage of the proof of [Wlo05, Theorem 4.7.1], the disjoint
case): stalkwise the unit ideal on the exceptional divisor, the image of the stalk below
elsewhere. -/
theorem comap_blowUpπ_eq_strictTransform_of_disjoint
    (hdisj : Disjoint D.support Z.support) : Z.comap D.blowUpπ = Z.strictTransform D
        := by
  refine ext_stalkIdeal fun x' => ?_
  by_cases hx' : x' ∈ D.exceptionalDivisor.support
  · have hZ : D.blowUpπ x' ∉ Z.support :=
      notMem_of_disjoint_closeds hdisj ((mem_support_comap_iff_apply D
          D.blowUpπ x').mp hx')
    have h1 : (Z.comap D.blowUpπ).stalkIdeal x' = ⊤ := by
      rw [stalkIdeal_comap, stalkIdeal_eq_top_of_notMem_support Z hZ, Ideal.map_top]
    have h2 : (Z.strictTransform D).stalkIdeal x' = ⊤ :=
      top_le_iff.mp (h1 ▸ stalkIdeal_mono (le_saturate (Z.comap D.blowUpπ)
        D.exceptionalDivisor) x')
    rw [h1, h2]
  · rw [stalkIdeal_strictTransform_of_notMem_support_exceptionalDivisor D Z hx', stalkIdeal_comap]

/-- [Kol07, Definition 25] read off the centre: if `Z` has simple normal crossings with `E` and the
centre `D` misses `Z`, the strict transform of `Z` has simple normal crossings with the total
transform of `E` — the snc coordinates at the point below transport along the isomorphism of
stalks, and the stalk of the strict transform is the image of that of `Z`. -/
theorem hasSncWith_totalTransform_strictTransform_of_disjoint [IsLocallyNoetherian X]
    (E : DivisorFamily X) (hdisj : Disjoint D.support Z.support) (hZ : E.HasSncWith Z) :
    (E.totalTransform D).HasSncWith (Z.strictTransform D) := by
  intro x' hx'
  have hex := notMem_support_exceptionalDivisor_of_mem_support_strictTransform D Z hdisj hx'
  have hπ := blowUpπ_mem_support_of_mem_support_strictTransform D Z hx'
  obtain ⟨n, z, ⟨⟨hspan, hdim⟩, c, hcinj, hc⟩, s, hs⟩ := hZ _ hπ
  have h' := exists_snc_data_totalTransform_of_notMem_support D E.component hex
    hspan.symm hdim c hcinj hc
  refine ⟨n, fun i => D.blowUpπ.stalkMap x' (z i), ⟨⟨h'.1.1.symm, h'.1.2⟩, h'.2⟩, s,
      ?_⟩
  have hs' : Z.stalkIdeal (D.blowUpπ x') = Ideal.span (z '' ↑s) := hs
  rw [stalkIdeal_strictTransform_of_notMem_support_exceptionalDivisor D Z hex, hs', Ideal.map_span,
    Set.image_image]

/-- The last sentence of [Kol07, Definition 24] off the centre: if no member of `E` contains `Z`
near any of its points and the centre `D` misses `Z`, no member of the total transform contains
the strict transform of `Z` near any of its points — the members through a point off the
exceptional divisor are the strict transforms of the members below, with the transported
stalks. -/
theorem notContainedInMembers_totalTransform_strictTransform_of_disjoint [IsLocallyNoetherian X]
    (E : DivisorFamily X) (hdisj : Disjoint D.support Z.support)
    (hZ : NotContainedInMembers E Z) :
    NotContainedInMembers (E.totalTransform D) (Z.strictTransform D) := by
  intro x' hx' i hi
  have hex := notMem_support_exceptionalDivisor_of_mem_support_strictTransform D Z hdisj hx'
  have hπ := blowUpπ_mem_support_of_mem_support_strictTransform D Z hx'
  have hbij : Function.Bijective (D.blowUpπ.stalkMap x').hom := by
    have := isIso_stalkMap_π_of_notMem_support D hex
    exact (asIso (D.blowUpπ.stalkMap x')).commRingCatIsoToRingEquiv.bijective
  rcases i with j | j
  · change x' ∈ ((E.component j).strictTransform D).support at hi
    change ¬ ((E.component j).strictTransform D).stalkIdeal x' ≤
      (Z.strictTransform D).stalkIdeal x'
    have hπj := blowUpπ_mem_support_of_mem_support_strictTransform D (E.component j) hi
    rw [stalkIdeal_strictTransform_of_notMem_support_exceptionalDivisor D _ hex,
      stalkIdeal_strictTransform_of_notMem_support_exceptionalDivisor D _ hex]
    intro hle
    refine hZ _ hπ j hπj fun a ha => ?_
    rw [← Ideal.comap_map_of_bijective _ hbij (I := Z.stalkIdeal (D.blowUpπ x')),
      Ideal.mem_comap]
    exact hle (Ideal.mem_map_of_mem _ ha)
  · exact (hex hi).elim

end Hironaka.Resolution
