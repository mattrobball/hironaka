/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses
import Hironaka.Algebra.Local.Regular
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Snc.DictionaryComponents
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Snc.SmoothDivisorLocal
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The reduced closure of a point: members, smooth divisors, `Z_{-1}`

Elementary tools about `c̄ := V(closure {η})`, the reduced closure of a point `η`, for the proof of
the statement CP1 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`): the chain form depends on the stratum
only through its stalk (`chainRelativeAt_congr_stalkIdeal`); when `η` lies on no member of `E`, no
member contains `c̄` near any of its points (`notContainedInMembers_vanishingIdeal_closure` — a
containment of stalks at `x` would put `η`, which specialises to `x`, on the member); a smooth
divisor `H` is locally irreducible, so at a point of the closure of one of its generic points `ξ`
the reduced ideal of that closure is `H`'s own stalk and the closure is a smooth divisor
(`stalkIdeal_vanishingIdeal_closure_eq_of_isSmoothDivisor`,
`isSmoothDivisor_vanishingIdeal_closure_of_mem_genericPoints`); and when the subscheme
`Z_{-1}(I, 1, H)` of the proof of [Kol07, Lemma 102] (the components of `H` along which `I` has
order `≥ 1`) contains `c̄` for a generic point `η` of `V(I)`, `η` is a generic point of `H`
(`mem_genericPoints_of_Zminus1_le`). Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step22Core`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Absorbed`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Cover` and the `EmbeddedCP3*` modules.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Scheme.IdealSheafData
  Hironaka.Sequence Hironaka.Snc Hironaka.BD IsLocalRing

namespace Hironaka.Resolution

variable {X : Scheme.{u}}

/-- The chain form depends on `Γ` only through its stalk at `p`. -/
theorem chainRelativeAt_congr_stalkIdeal {E : DivisorFamily X} {I Γ Γ' : X.IdealSheafData}
    {p : X} (h : Γ.stalkIdeal p = Γ'.stalkIdeal p) :
    ChainRelativeAt E I Γ p ↔ ChainRelativeAt E I Γ' p := by
  unfold ChainRelativeAt ChainCoords
  rw [h]

/-- The closure of a point lying on no member of `E` is contained in no member of `E` near any of
its points (the last sentence of [Kol07, Definition 24] for the reduced closure of a point):
`E^j_x ⊆ I(c̄)_x` would give `E^j_η ⊆ I(c̄)_η = 𝔪_η` at the generic point `η`, which specialises
to `x`. -/
theorem notContainedInMembers_vanishingIdeal_closure (E : DivisorFamily X) {η : X}
    (hη : ∀ j, η ∉ (E.component j).support) :
    NotContainedInMembers E (IdealSheafData.vanishingIdeal (Closeds.closure {η})) := by
  intro x hx j _ hle
  apply hη j
  have hsp : η ⤳ x := by
    rw [support_vanishingIdeal_eq] at hx
    exact specializes_iff_mem_closure.mpr hx
  rw [IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal,
      IdealSheafData.stalkIdeal_specializes (E.component j) hsp]
  calc ((E.component j).stalkIdeal x).map (X.presheaf.stalkSpecializes hsp).hom
      ≤ ((IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal x).map
          (X.presheaf.stalkSpecializes hsp).hom := Ideal.map_mono hle
    _ = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η :=
        (IdealSheafData.stalkIdeal_specializes (IdealSheafData.vanishingIdeal (Closeds.closure
            {η})) hsp).symm
    _ = maximalIdeal (X.presheaf.stalk η) := Hironaka.BMO.stalkIdeal_vanishingIdeal_closure_self η

/-- A smooth divisor is locally irreducible — at a point `x` of the closure of one of its generic
points `ξ`, the reduced ideal of that closure is the divisor's own stalk: `H_x` is prime
(`𝒪_{X,x} / H_x` is regular, hence a domain) and `I(closure ξ)_x` is a minimal prime over it. -/
theorem stalkIdeal_vanishingIdeal_closure_eq_of_isSmoothDivisor {H : X.IdealSheafData}
    (hH : IsSmoothDivisor H) {ξ x : X} (hξ : ξ ∈ H.support.genericPoints) (hx : ξ ⤳ x) :
    (IdealSheafData.vanishingIdeal (Closeds.closure {ξ})).stalkIdeal x = H.stalkIdeal x := by
  have hxH : x ∈ H.support :=
    H.support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hξ.1)
      (specializes_iff_mem_closure.mp hx)
  have hsm : IsSmoothDivisorAt H x := (isSmoothDivisor_iff_forall_isSmoothDivisorAt H).mp hH x hxH
  have hprime : (H.stalkIdeal x).IsPrime := by
    have : IsRegularLocalRing (X.presheaf.stalk x ⧸ H.stalkIdeal x) := hsm.1
    exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  have hmin := stalkIdeal_vanishingIdeal_mem_minimalPrimes H hξ hx
  rwa [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hmin

/-- The component of a smooth divisor through one of its generic points is a smooth divisor — its
stalks are the divisor's. -/
theorem isSmoothDivisor_vanishingIdeal_closure_of_mem_genericPoints {H : X.IdealSheafData}
    (hH : IsSmoothDivisor H) {ξ : X} (hξ : ξ ∈ H.support.genericPoints) :
    IsSmoothDivisor (IdealSheafData.vanishingIdeal (Closeds.closure {ξ})) := by
  rw [isSmoothDivisor_iff_forall_isSmoothDivisorAt]
  intro x hx
  have hsp : ξ ⤳ x := by
    rw [support_vanishingIdeal_eq] at hx
    exact specializes_iff_mem_closure.mpr hx
  have hxH : x ∈ H.support :=
    H.support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hξ.1)
      (specializes_iff_mem_closure.mp hsp)
  unfold IsSmoothDivisorAt
  rw [stalkIdeal_vanishingIdeal_closure_eq_of_isSmoothDivisor hH hξ hsp]
  exact (isSmoothDivisor_iff_forall_isSmoothDivisorAt H).mp hH x hxH

/-- When `Z_{-1}(I, 1, H)` (the proof of [Kol07, Lemma 102]) contains the closure of a generic
point `η` of `V(I)`, that closure is a component of `H` — `η` lies on `Z_{-1}`, so under a generic
point `ξ` of `H` with `ord_ξ I ≥ 1`; `ξ ∈ V(I)` specialises to the generic point `η`, so
`ξ = η`. -/
theorem mem_genericPoints_of_Zminus1_le [NoetherianSpace X] (I H : X.IdealSheafData) {η : X}
    (hη : η ∈ I.support.genericPoints)
    (hle : Zminus1 I 1 H ≤ IdealSheafData.vanishingIdeal (Closeds.closure {η})) :
    η ∈ H.support.genericPoints := by
  have hmem : η ∈ (Zminus1 I 1 H).support := by
    have hη' : η ∈ (IdealSheafData.vanishingIdeal (Closeds.closure {η})).support := by
      rw [support_vanishingIdeal_eq]
      exact subset_closure (Set.mem_singleton η)
    exact IdealSheafData.support_antitone hle hη'
  rw [← SetLike.mem_coe, coe_support_Zminus1] at hmem
  obtain ⟨ξ, hξ, hord, hsp⟩ := hmem
  have hξI : ξ ∈ I.support := by
    rw [Nat.cast_one] at hord
    exact (IdealSheafData.one_le_ord_iff I ξ).mp hord
  rw [← hη.2 hξI hsp]
  exact hξ

end Hironaka.Resolution
