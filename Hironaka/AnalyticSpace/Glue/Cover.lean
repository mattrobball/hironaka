/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Defs
import Hironaka.AnalyticSpace.Restrict.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Compactness.Paracompact

/-!
# Locally finite countable covers of an analytic space

An analytic `K`-space is locally compact (locally a local analytic `K`-space, clause (i) of the
definition in [Hir64, Ch. 0, §1, p. 120]), countable at infinity (clause (ii)) and Hausdorff
(clause (iii)), hence paracompact. If a property `P` of open subspaces is stable under passing to
smaller open subsets and holds on a neighbourhood of every point, then `X` has a
countable, locally finite open cover by open subsets with compact closures on which `P` holds
(`exists_locallyFinite_cover`). This is the cover the gluing of local complexifications starts from,
with `P` the property of admitting an analytic complexification (stable under restriction by
`Complexification.restrictLe`, `Hironaka.AnalyticSpace.Glue.Restrict`); it is the locally finite
cover of the proof of [BW59, Proposition 1], and the pair of locally finite covers `V̄_i ⊆ U_i` of
the proof of [Car57, §3, Proposition 2].

Conventions. The cover is indexed by a type `ι : Type u` with `Countable ι`; empty members are
excluded, so that the countability comes from the local finiteness in a σ-compact space (Mathlib's
`LocallyFinite.countable_univ`). The refinement is Mathlib's `precise_refinement` on the cover by
the neighbourhoods `U x ∩ K x`, `K x` an open neighbourhood of `x` with compact closure. For `X = ∅`
the index type is empty and every clause holds trivially; for `X` compact the cover is finite; for
`P` trivially true one gets a locally finite countable cover by relatively compact open subsets.
-/

public section

open TopologicalSpace Topology Set

namespace AnalyticSpace.Glue

universe u

variable {K : Type} [RCLike K]

/-- A locally finite countable open cover of an analytic space by relatively compact opens on which
a restriction-stable local property holds. -/
theorem exists_locallyFinite_cover (X : AnalyticSpace.{u} K) (P : Opens X → Prop)
    (hmono : ∀ {U V : Opens X}, V ≤ U → P U → P V)
    (hloc : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ P U) :
    ∃ (ι : Type u) (_ : Countable ι) (U : ι → Opens X),
      (∀ i, P (U i)) ∧ (∀ i, IsCompact (closure (U i : Set X))) ∧
      LocallyFinite (fun i => (U i : Set X)) ∧ (⋃ i, (U i : Set X)) = Set.univ := by
  choose U hxU hPU using hloc
  choose Kx hKo hxK hKc using fun x : X => exists_isOpen_mem_isCompact_closure x
  let u : X → Set X := fun x => (U x : Set X) ∩ Kx x
  have huo : ∀ x, IsOpen (u x) := fun x => (U x).isOpen.inter (hKo x)
  have huc : ⋃ x, u x = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨x, hxU x, hxK x⟩
  obtain ⟨v, hvo, hvc, hvf, hvu⟩ := precise_refinement u huo huc
  let ι := {x : X // (v x).Nonempty}
  have hlf : LocallyFinite (fun i : ι => v i.1) := hvf.comp_injective Subtype.val_injective
  have hcount : Countable ι :=
    Set.countable_univ_iff.mp (hlf.countable_univ fun i => i.2)
  refine ⟨ι, hcount, fun i => ⟨v i.1, hvo i.1⟩, fun i => ?_, fun i => ?_, hlf, ?_⟩
  · exact hmono (fun y hy => (hvu i.1 hy).1) (hPU i.1)
  · exact (hKc i.1).of_isClosed_subset isClosed_closure
      (closure_mono fun y hy => (hvu i.1 hy).2)
  · apply Set.eq_univ_of_forall
    intro y
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hvc ▸ Set.mem_univ y : y ∈ ⋃ x, v x)
    exact Set.mem_iUnion.mpr ⟨⟨x, ⟨y, hx⟩⟩, hx⟩

end AnalyticSpace.Glue
