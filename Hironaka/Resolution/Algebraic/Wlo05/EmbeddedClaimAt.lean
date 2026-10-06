/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Włodarczyk's Claim along the tower of order reductions

Włodarczyk proves the Claim of [Wlo05, Theorem 4.7.1] "by induction on codimension": at a purely
nonmonomial stage (Step 1 of the proof of [Kol07, Theorem 107] has reduced to the round of order
`1`), the order reduction restricts to a smooth hypersurface of maximal contact `V(u)`; either
`V(u)` is the strict transform of `Y₁` itself (Kollár's `Z_{-1}` of [Kol07, Lemma 102]) or
Włodarczyk's Claim for `I|_{V(u)}` on `V(u)` gives it for `I`, since `u` lies in the controlled
transform of `I`. Here the codimension induction is the induction on the stage of the tower of
order reductions
(`Hironaka.Stage.tower stage0 n`; [Kol07, 70]: (69) in dimensions `≤ n − 1` gives (68) in
dimension `n`), with the boundary explicit:

* `ClaimBOAt k n` — the Claim for the run of `BO_{n,1}` ([Kol07, Theorem 68] at mark `1`, the
  stage-`n` unmarked family) on a triple `(X, I, E)` with `max-ord I ≤ 1` (its `BOClass n 1`): at
  the first stage whose centre contains the strict transform of `c := I_{closure η}`, the
  nonmonomial part of the marked transform of `I` agrees with that strict transform at each of its
  points.
* `ClaimBMOAt k n` — the same for the run of `BMO_{n,1}` ([Kol07, Theorem 107] at mark `1`, the
  stage-`n` marked family) on a marked triple of mark `1`.

`ClaimKC k` (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses`) is `ClaimBMOAt k` at the
stage `T.dim`: the dimension-free `BMO_1` (`Hironaka.Stage.BMO_m 1 k`) evaluates the tower at the
triple's own dimension (`dimFreeBMO`). Since `ClaimKC k` is false for the order of the steps used
here, these predicates are not all provable; the same induction, with the chain-relative local form
in place of the stalk equality, is the one that proves CP1
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1For`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1At`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.BMO Hironaka.Stage

namespace Hironaka.Resolution

variable (k : Type u) [Field k] [CharZero k]

/-- The run of the stage-`n` order reduction `BO_{n,1}` ([Kol07, Theorem 68] at mark `1`, the tower
of order reductions) on a triple of its class. -/
noncomputable def boRun (n : ℕ) (T : Triple k) (hT : T.BOClass n 1) : BlowUpSequence T.X.left :=
  (((tower stage0 n).bo 1).functor k).seq T hT

/-- The run of the stage-`n` marked order reduction `BMO_{n,1}` ([Kol07, Theorem 107] at mark `1`)
on a marked triple of its class. -/
noncomputable def bmoRun (n : ℕ) (T : MarkedTriple k) (hT : T.BMOClass n 1) :
    BlowUpSequence T.X.left :=
  (((tower stage0 n).bmo 1).functor k).seq T hT

variable {k} in
/-- **The conclusion of Włodarczyk's Claim for a blow-up sequence** `S` on `(X, I, m, E)` and a
point `η` — at the FIRST stage `i` of `S` whose centre contains the strict transform of
`c := vanishingIdeal (closure {η})`, the nonmonomial part of the marked transform of `I` at stage
`i` (with respect to the total transform of `E` there) agrees with that strict transform at every
point of it. -/
def ClaimFor {X : Scheme.{u}} (S : BlowUpSequence X) (I : X.IdealSheafData) (E : DivisorFamily X)
    (m : ℕ) (η : X) : Prop :=
  ∀ i : Fin S.length, CenterContains S (IdealSheafData.vanishingIdeal (Closeds.closure {η})) i →
    (∀ l < i.val, ¬ CenterContains S (IdealSheafData.vanishingIdeal (Closeds.closure {η})) l) →
    ∀ p ∈ (S.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
        {η})) i.castSucc).support,
      (nonmonomialPart (S.markedTransformSeq I m i.castSucc)
          (S.totalTransformSeq E i.castSucc)).stalkIdeal p =
        (S.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
            {η})) i.castSucc).stalkIdeal p

/-- **Włodarczyk's Claim for `BO_{n,1}`** — for a triple `T` of `BOClass n 1`, a generic point
`η` of `supp T.I` on no member of `T.E` at which `T.I` agrees with
`c := vanishingIdeal (closure {η})`, the conclusion of Włodarczyk's Claim holds for the run of the
stage-`n` order reduction `BO_{n,1}` on `T`. -/
def ClaimBOAt (n : ℕ) : Prop :=
  ∀ (T : Triple k) (hT : T.BOClass n 1) (η : T.X.left), η ∈ T.I.support.genericPoints →
    (∀ i, η ∉ (T.E.component i).support) →
    T.I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η →
    ClaimFor (boRun k n T hT) T.I T.E 1 η

/-- **Włodarczyk's Claim for `BMO_{n,1}`** — `ClaimKC k`'s statement for the run of the
stage-`n` marked family `(tower stage0 n).bmo 1` on a marked triple of `BMOClass n 1`. -/
def ClaimBMOAt (n : ℕ) : Prop :=
  ∀ (T : MarkedTriple k) (hT : T.BMOClass n 1) (η : T.X.left), η ∈ T.I.support.genericPoints →
    (∀ i, η ∉ (T.E.component i).support) →
    T.I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η →
    ClaimFor (bmoRun k n T hT) T.I T.E 1 η

variable {k}

/-- `bmoOneRun` is the tower's marked family at the triple's own dimension (`dimFreeBMO`), so
Włodarczyk's Claim at every stage gives `ClaimKC k`. -/
theorem claimKC_of_claimBMOAt (h : ∀ n, ClaimBMOAt k n) : ClaimKC k := by
  intro T hm η hη hηE hIc n hn hfirst p hp
  have h' := h T.toTriple.dim
  unfold ClaimBMOAt ClaimFor at h'
  exact h' T (MarkedTriple.bmoClass_of_bmoClassFree ⟨le_rfl, hm⟩) η hη hηE hIc n hn hfirst p hp

end Hironaka.Resolution
