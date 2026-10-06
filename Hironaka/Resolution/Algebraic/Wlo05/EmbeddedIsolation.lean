/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Stage.DimFreeTheorems
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilCoreTools
import Hironaka.Resolution.Algebraic.Wlo05.FirstCenterExhaustive
import Hironaka.Resolution.Algebraic.Wlo05.FirstCenterLocalIso
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The isolation round: the loop's stage, the run's end, and exhaustiveness

The embedded desingularization sequence (`Hironaka.Resolution.Algebraic.Wlo05.Embedded`) stops a run
of `BMO_1` at the FIRST stage `n₀ = Nat.find h` whose centre contains the strict transform of some
member of `C` (`HasAbsorptionAt`). This module records what that stage is for each member and what
happens when there is no such stage:

* `find_lt_length`, `not_centerContains_of_lt_find`, `find_le_firstCenterIndex` — the loop's stage
  is a centre index of the run, no earlier centre contains any member's strict transform, and it is
  at most each member's first containing index (`firstCenterIndex`,
  `Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine`); every member absorbed at `n₀` is at ITS first
  absorbing stage (Włodarczyk's rule that the loop runs until "the strict transform of one of the
  components `Yᵢ` is the center", [Wlo05, Theorem 4.7.1, proof]).
* `markedTransformSeq_bmoOneRun_last_eq_top` — [Kol07, Theorem 69 (1)] at the mark `1`: the marked
  transform at the end of a complete run is the unit ideal.
* `exists_centerContains_bmoOneRun_of_invCE` — exhaustiveness for the loop's members (the argument
  of the proof of [Kol07, Corollary 22] and of [Wlo05, 4.6];
  `Hironaka.Resolution.Algebraic.Wlo05.FirstCenterExhaustive`): under the loop's invariant every
  member is absorbed at some stage of the run, so a round WITHOUT absorption has `C = ∅`
  (Włodarczyk's last round, which principalizes what is left).

Used throughout the CP modules (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP2Entry`,
`EmbeddedCP5`, `EmbeddedCP6Loop`, `EmbeddedCPBridge`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData Hironaka.Stage Hironaka.Sequence Hironaka.BMO

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-! ### The loop's stage -/

open Classical in
/-- The loop's stage `Nat.find h` is a centre index of the run (some member's strict transform is
contained in the centre there). -/
theorem find_lt_length (T : MarkedTriple k) (hm : T.m = 1) (C : Finset T.X.left.IdealSheafData)
    (h : ∃ n, HasAbsorptionAt T hm C n) : Nat.find h < (bmoOneRun T hm).length := by
  obtain ⟨_, _, hcc⟩ := Nat.find_spec h
  exact hcc.1

open Classical in
/-- No centre before the loop's stage contains the strict transform of any member. -/
theorem not_centerContains_of_lt_find (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) (h : ∃ n, HasAbsorptionAt T hm C n)
    {c : T.X.left.IdealSheafData}
    (hc : c ∈ C) {m : ℕ} (hm' : m < Nat.find h) : ¬ CenterContains (bmoOneRun T hm) c m :=
  fun hcc => Nat.find_min h hm' ⟨c, hc, hcc⟩

open Classical in
/-- The loop's stage is at most every member's first containing index — a member absorbed at the
loop's stage is at its own first absorbing stage (Włodarczyk's stop rule,
[Wlo05, Theorem 4.7.1, proof]). -/
theorem find_le_firstCenterIndex (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) (h : ∃ n, HasAbsorptionAt T hm C n)
    {c : T.X.left.IdealSheafData}
    (hc : c ∈ C) : Nat.find h ≤ firstCenterIndex (bmoOneRun T hm) c :=
  le_firstCenterIndex_of_forall_lt_not (bmoOneRun T hm) c (find_lt_length T hm C h).le
    fun _ hm' => not_centerContains_of_lt_find T hm C h hc hm'

/-! ### The end of a complete run -/

/-- [Kol07, Theorem 69 (1)] at the mark `1`: the marked transform of `(I, 1)` at the end of the run
of `BMO_1` is the unit ideal — its maximal order is `< 1`, and a proper ideal sheaf has maximal
order `≥ 1` (`one_le_maxOrd_of_ne_top`). -/
theorem markedTransformSeq_bmoOneRun_last_eq_top (T : MarkedTriple k) (hm : T.m = 1) :
    (bmoOneRun T hm).markedTransformSeq T.I 1 (Fin.last _) = ⊤ := by
  obtain ⟨T, m⟩ := T
  have h1 : m = 1 := hm
  subst h1
  have hlt := dimFreeBMO_maxOrd_lt stage0 1 (⟨T, 1⟩ : MarkedTriple k) ⟨le_rfl, hm⟩
  by_contra hne
  have hge := one_le_maxOrd_of_ne_top _ hne
  rw [Nat.cast_one] at hge hlt
  exact (not_le.mpr hlt) hge

/-! ### Exhaustiveness for the loop's members -/

/-- Exhaustiveness for the loop's members (the proof of [Kol07, Corollary 22]; [Wlo05, 4.6]): under
the loop's invariant every member of `C` — the reduced ideal of a component of `V(I)`, integral —
has its strict transform contained in some centre of the run of `BMO_1` on `T`
(`exists_centerContains_of_markedTransformSeq_last_eq_top` at the run's end, which is the unit
ideal by Theorem 69 (1)). -/
theorem exists_centerContains_bmoOneRun_of_invCE (T : MarkedTriple k) (hm : T.m = 1)
    {C : Finset T.X.left.IdealSheafData} (hinv : InvCE T.I T.E C)
    {c : T.X.left.IdealSheafData} (hc : c ∈ C)
    [IsIntegral c.subscheme] : ∃ n, CenterContains (bmoOneRun T hm) c n := by
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  obtain ⟨η, hη, rfl, -, hIc⟩ := hinv.mem c hc
  exact exists_centerContains_of_markedTransformSeq_last_eq_top (bmoOneRun T hm) T.I _ 1
    (Hironaka.BMO.isGenericPoint_support_vanishingIdeal_closure η) hη hIc
    (markedTransformSeq_bmoOneRun_last_eq_top T hm)

end Hironaka.Resolution
