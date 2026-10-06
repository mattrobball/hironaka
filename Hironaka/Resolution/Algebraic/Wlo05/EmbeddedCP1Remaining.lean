/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedIsolatedState
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedBridge
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Main
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRemaining
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedStep
import Hironaka.Scheme.BlowUpSequence.TakeLast
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The invariant of the loop persists through an isolation

The loop `bedAux` of `Hironaka.Resolution.Algebraic.Wlo05.Embedded` restarts, after the absorbing
stage `n`, on the isolated triple `(X_n, K_n : I_abs, E_n)` with the remaining members — the strict
transforms of the members of `C` not absorbed at `n`. The strong inductions on `C.card` of the
statement CP6 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`; the loop theorem
`markedTransformSeq_take_eq_inf_of_protectedStates` and the end identity,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Loop`) apply the induction hypothesis to that state,
so the invariant `InvCE` of the loop must hold for it.
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRemaining` proved this under the false hypothesis
`ClaimKC` (`exists_genericPoint_isolatedMarkedIdeal_of_not_absorbed`); its single use of that
hypothesis was the disjointness of the strict transform of a remaining member from the absorbed
ones, which is now CP1 (`disjoint_strictTransformSeq_of_absorbed`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Main`, in the form of the truncation). This module
carries that disjointness to the index form across the cast of the truncation
(`disjoint_strictTransformSeq_of_not_absorbed_of_cp1`), restores the invariant in index form
(`invCE_isolated`) and transports it to the form of the truncation used by the loop
(`invCE_isolatedTriple`), as `embeddedStateData_isolatedTriple` transports the state of the
conditional loop. The generic points are those of the proof of [Kol07, Corollary 22]; the isolation
is that of the proof of [Wlo05, Theorem 4.7.1]. This is not in the literature. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Loop` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCPBridge`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.BMO

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-- Disjointness of supports transports across a cast of the ambient scheme. -/
theorem disjoint_support_of_heq {Y Y' : Scheme.{u}} (hY : Y = Y') {a b : Y.IdealSheafData}
    {a' b' : Y'.IdealSheafData} (ha : HEq a a') (hb : HEq b b')
    (hd : Disjoint a.support b.support) : Disjoint a'.support b'.support := by
  subst hY
  rw [← eq_of_heq ha, ← eq_of_heq hb]
  exact hd

/-- The invariant of the loop transports across a cast of the ambient scheme. -/
theorem InvCE.of_heq {Y Y' : Scheme.{u}} (hY : Y = Y') {I : Y.IdealSheafData}
    {E : DivisorFamily Y} {C : Finset Y.IdealSheafData} {I' : Y'.IdealSheafData}
    {E' : DivisorFamily Y'} {C' : Finset Y'.IdealSheafData} (hI : HEq I I') (hE : HEq E E')
    (hC : HEq C C') (hinv : InvCE I' E' C') : InvCE I E C := by
  subst hY
  rw [eq_of_heq hI, eq_of_heq hE, eq_of_heq hC]
  exact hinv

section Index

variable {T : MarkedTriple k} {hm : T.m = 1} {C : Finset T.X.left.IdealSheafData}
  {h : ∃ n, HasAbsorptionAt T hm C n}

open Classical in
/-- CP1 in the index form: a member not absorbed at the stage of the loop has its strict transform
disjoint from every absorbed one (`disjoint_strictTransformSeq_of_absorbed` carried across the
cast of the truncation). -/
theorem disjoint_strictTransformSeq_of_not_absorbed_of_cp1 (hinv : InvCE T.I T.E C)
    {c' : T.X.left.IdealSheafData} (hc' : c' ∈ C)
    (hnot : ¬ CenterContains (bmoOneRun T hm) c' (Nat.find h)) {c : T.X.left.IdealSheafData}
    (hc : c ∈ absorbed T hm C h) :
    Disjoint ((bmoOneRun T hm).strictTransformSeq c' (absorbIndex T hm C h).castSucc).support
      ((bmoOneRun T hm).strictTransformSeq c (absorbIndex T hm C h).castSucc).support := by
  have hcc : CenterContains (bmoOneRun T hm) c (Nat.find h) := (Finset.mem_filter.mp hc).2
  have hne : c' ≠ c := fun heq => hnot (heq ▸ hcc)
  exact disjoint_support_of_heq (stage_take_last _ (find_lt_length T hm C h).le)
    (strictTransformSeq_take_last_heq _ c' (find_lt_length T hm C h).le)
    (strictTransformSeq_take_last_heq _ c (find_lt_length T hm C h).le)
    (disjoint_strictTransformSeq_of_absorbed T hm C hinv h (absorbed_subset hc) hcc hc' hne)

open Classical in
/-- The invariant of the loop for the isolated marked ideal and the remaining members, in index
form (the proof of [Kol07, Corollary 22] for the generic points). -/
theorem invCE_isolated (hinv : InvCE T.I T.E C) :
    InvCE (isolatedMarkedIdeal T hm C h)
      ((bmoOneRun T hm).totalTransformSeq T.E (absorbIndex T hm C h).castSucc)
      (remainingIdx T hm C h) := by
  refine ⟨fun c'' hc'' => ?_⟩
  rw [remainingIdx, Finset.mem_image] at hc''
  obtain ⟨c', hc', rfl⟩ := hc''
  rw [Finset.mem_filter] at hc'
  obtain ⟨η', hgen, heq, hηE', hst⟩ :=
    exists_genericPoint_isolatedMarkedIdeal_of_not_absorbed_of_disjoint hinv hc'.1 hc'.2
      fun c hc => disjoint_strictTransformSeq_of_not_absorbed_of_cp1 hinv hc'.1 hc'.2 hc
  exact ⟨η', hgen, heq, hηE', hst⟩

end Index

open Classical in
/-- **The invariant of the loop holds again for the isolated triple and the remaining members**
(the isolation of the proof of [Wlo05, Theorem 4.7.1]; the generic points of the proof of
[Kol07, Corollary 22]): the strict transform of each remaining member is the reduced ideal of a
generic point of the support of the isolated ideal, off the boundary, at which the isolated ideal
agrees with it. Needed by the strong inductions of the loop theorem and of the end identity. -/
theorem invCE_isolatedTriple (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData)
    (hinv : InvCE T.I T.E C) (h : ∃ n, HasAbsorptionAt T hm C n) :
    InvCE (isolatedTriple T hm C (Nat.find h)).I (isolatedTriple T hm C (Nat.find h)).E
      (remainingComponents T hm C (Nat.find h)) := by
  obtain ⟨T, m⟩ := T
  have hm' : m = 1 := hm
  subst hm'
  exact InvCE.of_heq last_take_eq_stage isolatedTriple_I_heq isolatedTriple_E_heq
    (heq_finset_image last_take_eq_stage _ fun z => strictTransformSeq_take_heq z)
    (invCE_isolated hinv)

end Hironaka.Resolution
