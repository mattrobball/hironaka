/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Defs
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Resolution.Algebraic.Wlo05.ComponentsColon
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Scheme.BlowUpSequence.StalkProdDisjointSupport
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The strict transform of a reduced subscheme is the product of those of its components

Clause (c) of [Wlo05, Theorem 1.0.2] speaks of the strict transform `Ỹ` of the reduced subscheme
`Y`, while [Wlo05, Theorem 4.7.1] and its proof work with the strict transforms of the irreducible
components `Y_i`. The bridge is bookkeeping about strict transforms of reduced ideals, assembled
here from `Hironaka/Resolution/Algebraic/Wlo05/EmbeddedPullbackTools.lean` (the strict transform of
a reduced closed subscheme stays reduced along a sequence, `isReduced_strictTransformSeq_subscheme`;
the support of the strict transform of a finite union is the union of the strict transforms'
supports, `coe_support_strictTransformSeq_biUnion`; a reduced ideal is the vanishing ideal of its
support, `vanishingIdeal_support_of_isReduced`): when the strict transforms of the components at
a stage are pairwise disjoint, the strict transform of `Y` at that stage is their product
(`vanishingIdeal_iSup_support_eq_prod`), and simple normal crossings with the boundary pass from
the factors to the product pointwise.
-/

public section

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Sequence

variable {X : Scheme.{u}}

/-- The strict transform of a reduced ideal whose support is the union of the supports of finitely
many reduced ideals is, at a stage where the strict transforms of those are pairwise disjoint, the
product of their strict transforms: both sides are reduced with the same support. This passes
from the disjoint strict transforms of the components in [Wlo05, Theorem 4.7.1] to the strict
transform of the subvariety in [Wlo05, Theorem 1.0.2 (c)]. -/
theorem strictTransformSeq_eq_prod_of_pairwise_disjoint [IsLocallyNoetherian X]
    (S : BlowUpSequence X) (J : X.IdealSheafData) [IsReduced J.subscheme] {ι : Type v}
    (C : Finset ι) (c : ι → X.IdealSheafData) (hc : ∀ a ∈ C, IsReduced (c a).subscheme)
    (hJ : (J.support : Set X) = ⋃ a ∈ C, ((c a).support : Set X)) (i : Fin (S.length + 1))
    (hdisj : (C : Set ι).Pairwise fun a b =>
      Disjoint (S.strictTransformSeq (c a) i).support (S.strictTransformSeq (c b) i).support) :
    S.strictTransformSeq J i = ∏ a ∈ C, S.strictTransformSeq (c a) i := by
  have hred := Hironaka.Resolution.isReduced_strictTransformSeq_subscheme S J i
  have hsupp : (S.strictTransformSeq J i).support =
      ⨆ a ∈ C, (S.strictTransformSeq (c a) i).support := by
    apply Closeds.ext
    rw [Hironaka.Resolution.coe_support_strictTransformSeq_biUnion S (C : Set ι) C.finite_toSet c J
      hJ i, ← Finset.sup_eq_iSup, Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion]
    rfl
  rw [← Hironaka.Resolution.vanishingIdeal_support_of_isReduced (S.strictTransformSeq J i), hsupp]
  refine IdealSheafData.vanishingIdeal_iSup_support_eq_prod _ C (fun a ha => ?_) hdisj
  have := hc a ha
  have := Hironaka.Resolution.isReduced_strictTransformSeq_subscheme S (c a) i
  exact Hironaka.Resolution.vanishingIdeal_support_of_isReduced _

/-- Simple normal crossings with a family pass from finitely many pairwise disjoint closed
subschemes to their product: at a point of the product's support exactly one factor passes, and
the product's stalk is that factor's stalk. -/
theorem hasSncWith_prod_of_pairwise_disjoint (E : DivisorFamily X) {ι : Type v} (A : Finset ι)
    (I : ι → X.IdealSheafData)
    (hdisj : (A : Set ι).Pairwise fun a b => Disjoint (I a).support (I b).support)
    (h : ∀ a ∈ A, E.HasSncWith (I a)) : E.HasSncWith (∏ a ∈ A, I a) := by
  intro x hx
  have hx' : x ∈ ((⨆ a ∈ A, (I a).support : Closeds X) : Set X) := by
    rw [← support_finset_prod]
    exact hx
  rw [← Finset.sup_eq_iSup, Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion,
    Set.mem_iUnion₂] at hx'
  obtain ⟨a, ha, hxa⟩ := hx'
  obtain ⟨n, z, hsnc, s, hs⟩ := h a ha x hxa
  refine ⟨n, z, hsnc, s, ?_⟩
  rw [IdealSheafData.stalkIdeal_finset_prod_eq_of_mem_of_pairwise_disjoint A I hdisj ha hxa]
  exact hs

end Hironaka.Sequence
