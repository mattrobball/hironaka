/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.Embedded
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The loop's invariant and three named hypotheses

The invariant of the embedded desingularization loop
(`Hironaka.Resolution.Algebraic.Wlo05.Embedded`) and three propositions about the order reduction
functor `BMO_1`, stated as `Prop`-valued definitions so that lemmas can be proved conditionally on
them.

* `InvCE I E C` — the loop's invariant on a state `(X, I, E, C)`: every member `c` of `C` is the
  reduced ideal of the closure of a generic point `η` of `supp I` lying on no member of `E`, and
  `I` agrees with `c` at `η` (the hypothesis of Włodarczyk's Claim in the proof of
  [Wlo05, Theorem 4.7.1]: `I = I_{Y₁}` in a neighbourhood of a generic point of `Y₁`). Initially the
  members are the components of the reduced `Y` (`componentIdeals`); after an isolation the
  remaining members' strict transforms. This invariant is used throughout the proofs of CP1–CP6.
* `ClaimKC k` — Włodarczyk's Claim in Kollár's setting: for a marked triple of mark `1` and a
  member `c` as in `InvCE`, at the FIRST stage `n` whose centre contains the strict transform of
  `c`, the nonmonomial part of the induced marked ideal agrees with that strict transform at every
  point of it (stalkwise; the boundary at stage `n` explicit). Stated per member at its own first
  absorbing stage; at the loop's first absorbing stage, minimal over all members, every absorbed
  member is at its own first stage. **`ClaimKC k` fails** for the order of the steps of `BMO_1`
  transcribed here: on `X = 𝔸³` with `I = (u, v·w)` and the member `ℓ₁ = V(u, v)` the conclusion
  fails at the first absorbing stage. Włodarczyk's Claim holds for the order of his modified Step
  2b (the monomial part first) and fails for Kollár's order. The clauses of the theorem are
  therefore proved without it, from the local form of the ideal
  (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`, CP1–CP6).
* `StratumBlowUp k` — the blow-up of a centre `D` that is locally an intersection of members of a
  simple normal crossing family `E` preserves, for a closed subscheme `Z` having simple normal
  crossings with `E` and contained in no member of `E` near any of its points, its smoothness
  (through `HasSncWith`), its simple normal crossings with the total transform of `E`, and pulls
  its ideal back to its strict transform.
* `CentersInNonmonomialSupportOrStratum k` — the structure of one run of `BMO_1` (the proof of
  [Kol07, Theorem 107]): every centre of the run lies in the support of the nonmonomial part of the
  induced marked ideal at its stage (Steps 1 and 2 run on `N(I)`) or is locally an intersection of
  members of the boundary at its stage (Step 3: the strata of the snc divisor), and the support of
  the nonmonomial part at any stage maps into the support of the nonmonomial part at the start.

The lemmas conditional on `ClaimKC`, `StratumBlowUp` and `CentersInNonmonomialSupportOrStratum`
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedProtected`, `EmbeddedState`, `EmbeddedStep`,
`EmbeddedIsolatedIdeal`, `EmbeddedIsolatedState`, `EmbeddedRemaining`) are CONDITIONAL LEMMAS: the
first hypothesis is false and the other two are not proved in this development. Nothing in the proof
of the theorem uses them, and no main theorem depends on them.
`InvCE`, `IsLocalStratum` and `NotContainedInMembers` are in use.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData
  Hironaka BlowUpSequence Scheme.IdealSheafData Hironaka.BMO

namespace Hironaka.Resolution

/-! ### The loop's invariant -/

/-- **The loop's invariant** on a state `(X, I, E, C)` — every member `c` of `C` is the reduced
ideal `vanishingIdeal (closure {η})` of a generic point `η` of `supp I` (an irreducible component
of `V(I)`) lying on no member of the boundary `E`, at which `I` agrees with `c`: the hypothesis of
Włodarczyk's Claim in the proof of [Wlo05, Theorem 4.7.1] (`Y₁` an irreducible component of
`supp(I)` and `I = I_{Y₁}` near a generic point of `Y₁`). -/
structure InvCE {X : Scheme.{u}} (I : X.IdealSheafData) (E : DivisorFamily X)
    (C : Finset X.IdealSheafData) : Prop where
  mem : ∀ c ∈ C, ∃ η ∈ I.support.genericPoints,
    c = vanishingIdeal (Closeds.closure {η}) ∧ (∀ i, η ∉ (E.component i).support) ∧
      I.stalkIdeal η = c.stalkIdeal η

variable {k : Type u} [Field k] [CharZero k]

/-! ### The named hypotheses -/

/-- **Włodarczyk's Claim** of the proof of [Wlo05, Theorem 4.7.1] in Kollár's setting, as a
proposition — for a marked triple `T` of mark `1`, a generic point `η` of `supp T.I` on no member
of `T.E` at which `T.I` agrees with `c := vanishingIdeal (closure {η})`, and the FIRST stage `n` of
the run of `BMO_1` on `T` whose centre contains the strict transform of `c` (`CenterContains` at
`n`, not before), the nonmonomial part of the marked transform at stage `n` — with respect to the
total transform of the boundary at stage `n`, all read at the run's stage `n.castSucc` — agrees
stalkwise with the strict transform of `c` at every point of that strict transform. Fails for the
order of the steps of `BMO_1` used here (module docstring); kept as the hypothesis of the
conditional lemmas. -/
def ClaimKC (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (T : MarkedTriple k) (hm : T.m = 1) (η : T.X.left), η ∈ T.I.support.genericPoints →
    (∀ i, η ∉ (T.E.component i).support) →
    T.I.stalkIdeal η = (vanishingIdeal (Closeds.closure {η})).stalkIdeal η →
    ∀ n : Fin (bmoOneRun T hm).length,
      CenterContains (bmoOneRun T hm) (vanishingIdeal (Closeds.closure {η})) n →
      (∀ m < n.val, ¬ CenterContains (bmoOneRun T hm) (vanishingIdeal (Closeds.closure {η})) m) →
      ∀ p ∈ ((bmoOneRun T hm).strictTransformSeq (vanishingIdeal (Closeds.closure {η}))
          n.castSucc).support,
        (nonmonomialPart ((bmoOneRun T hm).markedTransformSeq T.I 1 n.castSucc)
            ((bmoOneRun T hm).totalTransformSeq T.E n.castSucc)).stalkIdeal p =
          ((bmoOneRun T hm).strictTransformSeq (vanishingIdeal (Closeds.closure {η}))
            n.castSucc).stalkIdeal p

/-- `D` is **locally a stratum** of the family `E` ([Kol07, Definition 24 (4)] read for a centre):
at every point of `D` its stalk ideal is the sum of the stalk ideals of some members of `E` (the
intersection of those members near the point). -/
def IsLocalStratum {X : Scheme.{u}} (E : DivisorFamily X) (D : X.IdealSheafData) : Prop :=
  ∀ x ∈ D.support, ∃ s : Finset E.ι, D.stalkIdeal x = ∑ i ∈ s, (E.component i).stalkIdeal x

/-- No member of `E` contains `Z` near a point of `Z` (the last sentence of
[Kol07, Definition 24], pointwise): at every point of `Z` on a member, that member's stalk ideal is
not contained in `Z`'s. -/
def NotContainedInMembers {X : Scheme.{u}} (E : DivisorFamily X) (Z : X.IdealSheafData) : Prop :=
  ∀ x ∈ Z.support, ∀ i, x ∈ (E.component i).support →
    ¬ (E.component i).stalkIdeal x ≤ Z.stalkIdeal x

/-- **The stratum blow-up preserves an snc closed subscheme**, as a proposition — for a smooth `X`
over `k`, a simple normal crossing family `E`, a centre `D` having simple normal crossings with `E`
and locally a stratum of `E`, and a closed subscheme `Z` having simple normal crossings with `E`
and contained in no member of `E` near any of its points: the total transform of `E` has simple
normal crossings with the strict transform of `Z`, no member of the total transform contains the
strict transform near any of its points, and the pullback of `Z`'s ideal is that strict transform
(no exceptional factor: the centre is contained in `Z` nowhere). -/
def StratumBlowUp (k : Type u) [Field k] : Prop :=
  ∀ {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] (E : DivisorFamily X)
    (D Z : X.IdealSheafData), E.IsSnc → E.HasSncWith D → IsLocalStratum E D →
    E.HasSncWith Z → NotContainedInMembers E Z →
    (E.totalTransform D).HasSncWith (Z.strictTransform D) ∧
      NotContainedInMembers (E.totalTransform D) (Z.strictTransform D) ∧
      Z.comap D.blowUpπ = Z.strictTransform D

/-- **The structure of one run of `BMO_1`**, as a proposition (the proof of [Kol07, Theorem 107]:
Steps 1 and 2 run on the nonmonomial part `N(I)` and transform it by its own marked transforms,
Step 3 blows up strata of the boundary; [Kol07, Definition–Lemma 110] for the splitting
`I = M(I) · N(I)`) — (1) every centre lies in the support of the nonmonomial part of the induced
marked ideal at its stage, or is locally a stratum of the boundary at its stage; (2) the support of
the nonmonomial part at any stage maps into the support of the nonmonomial part at the start (the
nonmonomial part of a stage is a marked transform of the initial one, or the unit ideal). -/
def CentersInNonmonomialSupportOrStratum (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (T : MarkedTriple k) (hm : T.m = 1),
    (∀ j : Fin (bmoOneRun T hm).length,
      (∀ p ∈ ((bmoOneRun T hm).center j).support,
        (nonmonomialPart ((bmoOneRun T hm).markedTransformSeq T.I 1 j.castSucc)
          ((bmoOneRun T hm).totalTransformSeq T.E j.castSucc)).stalkIdeal p ≠ ⊤) ∨
      IsLocalStratum ((bmoOneRun T hm).totalTransformSeq T.E j.castSucc)
        ((bmoOneRun T hm).center j)) ∧
    ∀ (i : Fin ((bmoOneRun T hm).length + 1)) (p : (bmoOneRun T hm).stage i),
      p ∈ (nonmonomialPart ((bmoOneRun T hm).markedTransformSeq T.I 1 i)
        ((bmoOneRun T hm).totalTransformSeq T.E i)).support →
      (bmoOneRun T hm).stageMap i p ∈ (nonmonomialPart T.I T.E).support

end Hironaka.Resolution
