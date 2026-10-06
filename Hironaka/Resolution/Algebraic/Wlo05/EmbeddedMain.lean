/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedState
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Reduced
import Hironaka.Resolution.Algebraic.Snc.DictionaryComponents
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The initial state of the loop `BED`: the irreducible components of `Y`

The initial state of the loop `BED` of `Hironaka.Resolution.Algebraic.Wlo05.Embedded`: the members
are the reduced ideals of the irreducible components of `Y` (`componentIdeals`), each the vanishing
ideal of the closure of a generic point of `V(I_Y)`, at which the reduced `I_Y` is the maximal ideal
(`stalkIdeal_eq_maximalIdeal_of_mem_genericPoints_of_isReduced`: every prime over the stalk is a
generic point specializing to it); the boundary is empty; nothing is protected yet
(`embeddedStateData_componentIdeals`). The support of `I_Y` is the union of the supports of the
members (`coe_support_eq_biUnion_componentIdeals`).

The clauses of [Wlo05, Theorem 1.0.2] about the final strict transform of `Y` are derived from the
end result of the loop in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedEndBridge`, and the proof of
the theorem supplies that end result from CP1–CP6
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCPBridge`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.BMO IsLocalRing

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-- The stalk of a reduced ideal at a generic point of its support is the maximal ideal: the stalk
is radical, and every prime over it contains a minimal prime over it, the stalk of the reduced ideal
of the closure of a generic point specializing to `η` — which is `η` itself. -/
theorem stalkIdeal_eq_maximalIdeal_of_mem_genericPoints_of_isReduced {X : Scheme.{u}}
    (I : X.IdealSheafData) [IsReduced I.subscheme] {η : X} (hη : η ∈ I.support.genericPoints) :
    I.stalkIdeal η = maximalIdeal (X.presheaf.stalk η) := by
  have hrad : (I.stalkIdeal η).radical = I.stalkIdeal η := by
    rw [← stalkIdeal_radical, radical_eq_self_of_isReduced_subscheme]
  refine le_antisymm ((Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp
      hη.1) ?_
  rw [← hrad, Ideal.radical_eq_sInf]
  refine le_sInf fun P ⟨hIP, hP⟩ => ?_
  obtain ⟨p, hp, hpP⟩ := Ideal.exists_minimalPrimes_le hIP
  obtain ⟨η', hη', hsp, hpeq⟩ := exists_mem_genericPoints_of_mem_minimalPrimes I hp
  have heq : η' = η := hη.2 hη'.1 hsp
  subst heq
  rw [← hpeq, stalkIdeal_vanishingIdeal_closure_self] at hpP
  exact hpP

section Main

variable (TX : Triple k) (hE : IsEmpty TX.E.ι) [IsReduced TX.I.subscheme]

omit [CharZero k] [IsReduced TX.I.subscheme] in
/-- The members of the initial state are the reduced ideals of the irreducible components of
`V(I_Y)`. -/
theorem mem_componentIdeals_iff {c : TX.X.left.IdealSheafData} :
    c ∈ componentIdeals TX ↔
      ∃ η ∈ TX.I.support.genericPoints, c = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
          {η}) := by
  have := Hironaka.BD.noetherianSpace_triple TX
  simp only [componentIdeals, Finset.mem_image, Set.Finite.mem_toFinset]
  exact ⟨fun ⟨η, hη, h⟩ => ⟨η, hη, h.symm⟩, fun ⟨η, hη, h⟩ => ⟨η, hη, h.symm⟩⟩

omit [CharZero k] in
include hE in
/-- The invariant of the loop at the start (the components of [Wlo05, Theorem 4.7.1]): the state
of the loop for `(X, I_Y, ∅)` with the irreducible components of `Y` as members and nothing
protected. -/
theorem embeddedStateData_componentIdeals :
    EmbeddedStateData TX.I TX.E (componentIdeals TX) (∅ : Finset TX.X.left.IdealSheafData) := by
  refine ⟨⟨fun c hc => ?_⟩, fun γ hγ => (Finset.notMem_empty γ hγ).elim,
    fun γ hγ => (Finset.notMem_empty γ hγ).elim, ?_,
    fun c _ γ hγ => (Finset.notMem_empty γ hγ).elim, fun γ hγ => (Finset.notMem_empty γ hγ).elim⟩
  · obtain ⟨η, hη, rfl⟩ := (mem_componentIdeals_iff TX).mp hc
    refine ⟨η, hη, rfl, fun i => hE.elim i, ?_⟩
    rw [stalkIdeal_eq_maximalIdeal_of_mem_genericPoints_of_isReduced TX.I hη,
      stalkIdeal_vanishingIdeal_closure_self]
  · rw [Finset.coe_empty]
    exact Set.pairwise_empty _

omit [CharZero k] [IsReduced TX.I.subscheme] in
/-- The support of `I_Y` is the union of the supports of its irreducible components. -/
theorem coe_support_eq_biUnion_componentIdeals :
    (TX.I.support : Set TX.X.left) = ⋃ c ∈ componentIdeals TX, (c.support : Set TX.X.left) := by
  ext x
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · intro hx
    obtain ⟨η, hη, hsp⟩ := Closeds.exists_mem_genericPoints_specializes _ hx
    refine ⟨Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η}),
        (mem_componentIdeals_iff TX).mpr ⟨η, hη, rfl⟩, ?_⟩
    rw [support_vanishingIdeal_eq, Closeds.coe_closure]
    exact specializes_iff_mem_closure.mp hsp
  · rintro ⟨c, hc, hxc⟩
    obtain ⟨η, hη, rfl⟩ := (mem_componentIdeals_iff TX).mp hc
    rw [support_vanishingIdeal_eq, Closeds.coe_closure] at hxc
    exact TX.I.support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη.1) hxc

end Main

end Hironaka.Resolution
