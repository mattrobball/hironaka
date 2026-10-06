/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.State

/-!
# The example states of the monomial procedure

Concrete states of `Hironaka/Resolution/Algebraic/Monomial/State.lean` on which the procedure of
[Kol07, 111, Step 3] is computed, and the maximal-multiplicity procedure that
[Kol07, Example 112] refutes. The computations themselves are in
`HironakaExamples/Monomial/Example112.lean` (which is imported by the root) and in
`HironakaExamples/MonomialState.lean` and `HironakaExamples/MonomialRestrict.lean`.

* `example112 m hm`: the surface of [Kol07, Example 112], two curves `E¹, E²` meeting at one
  point, both with exponent `m + 1`.
* `maxMultChoice`, `maxMultRun`, `maxMultFaces`, `example112OtherPath`: the maximal-multiplicity
  procedure that Kollár dismisses at the start of Step 3 (blow up the locus of highest
  multiplicity; "this, however, does not work, not even for surfaces"). It is defined here
  only to be computed against, not used by the procedure: the faces of maximal sum `≥ m`
  (`maxMultFaces`), with the lexicographically largest label tuple as the tie-break (Kollár's
  `E² ∩ E³`); the centres of the other tie-break, which gives the same exponents by symmetry,
  are listed as `example112OtherPath`.
* `threePhase`: `n = 3`, `m = 8`, one component per label, exponents `4, 9, 3, 6`, maximal faces
  `{0}` and `{1, 2, 3}`, an instance in which all three phases act.
* `splitX`, `splitU`: the example showing why the components of a member must carry their own
  exponents (the deviation recorded in `Hironaka/Resolution/Algebraic/Monomial/State.lean`), in its
  fine, labelled form: the four lines `V(x), V(x-1)` (label `0`), `V(y), V(y-1)` (label `1`) of `𝔸²`
  with the exponents `1, 0, 1, 0` of `I = (xy)`, `m = 1`, on `X = 𝔸²` and on `U = D((x-1)(y-1))`;
  `coarseX`, `coarseU`: the same example with one exponent per member, the minimum over its
  components, as the members of [Kol07, Definition–Lemma 110] are printed (not assumed
  irreducible): exponents `0, 0` on `X` and `1, 1` on `U`. Not in the sources.
-/

@[expose] public section

namespace Hironaka.Monomial.Examples

open Hironaka.Monomial MonomialState

/-! ### Example 112 -/

/-- The surface of [Kol07, Example 112]: `E¹, E²` two curves intersecting at a point with
`a₁ = a₂ = m + 1`, as a state with components `0, 1` (labels `0, 1`, the curves `E¹, E²`), nerve
`{0}, {1}, {0, 1}`, exponents `m + 1`, `n = 2`. -/
def example112 (m : ℕ) (hm : 1 ≤ m) : MonomialState :=
  ofValid 2 m 2 2 (fun c => c) (fun _ => m + 1) {{0}, {1}, {0, 1}}
    ⟨hm, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The maximal-multiplicity choice ([Kol07, 111, Step 3], the "usual method" that Kollár
rejects), defined for the computations only: the faces of maximal sum `≥ m`, with the
lexicographically largest label tuple as the tie-break (Kollár's `E² ∩ E³` in Example 112; the
other tie-break gives the same exponents by symmetry). -/
def maxMultChoice (st : MonomialState) : Finset (Finset ℕ) :=
  let cands := st.nerve.filter fun T => st.m ≤ st.total T
  let maxs := cands.filter fun T => st.total T = cands.sup st.total
  maxs.filter fun T => ∀ T' ∈ maxs, st.labelTuple T' ≤ st.labelTuple T

/-- `k` steps of the maximal-multiplicity procedure: the final state and the list of centres, in
order. -/
def maxMultRun : ℕ → MonomialState → MonomialState × List (Finset (Finset ℕ))
  | 0, st => (st, [])
  | k + 1, st =>
    let r := maxMultRun k (st.blowUp (maxMultChoice st))
    (r.1, maxMultChoice st :: r.2)

/-- The maximal-multiplicity locus before the tie-break: the faces of maximal sum `≥ m`
(Kollár's "highest multiplicity locus"); `maxMultChoice` is its tie-break. -/
def maxMultFaces (st : MonomialState) : Finset (Finset ℕ) :=
  let cands := st.nerve.filter fun T => st.m ≤ st.total T
  cands.filter fun T => st.total T = cands.sup st.total

/-- The centres of six steps of the maximal-multiplicity procedure on Example 112 under the
other tie-break (the lexicographically smallest label tuple): the point `{0, 1}`, then `{0, 2}`
(Kollár's `E¹ ∩ E³` instead of `E² ∩ E³`), then the unique maximizers `{2, 3}`, `{3, 4}`,
`{4, 5}`, `{5, 6}`; the exponents come out the same by symmetry. -/
def example112OtherPath : List (Finset (Finset ℕ)) :=
  [{{0, 1}}, {{0, 2}}, {{2, 3}}, {{3, 4}}, {{4, 5}}, {{5, 6}}]

/-! ### The three-phase instance -/

/-- An instance in which all three phases act: `n = 3`, `m = 8`, one component per label,
exponents `4, 9, 3, 6`, maximal faces `{0}` and `{1, 2, 3}`. -/
def threePhase : MonomialState :=
  ofValid 3 8 4 4 (fun c => c) (fun c => [4, 9, 3, 6].getD c 0)
    {{0}, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}} (by decide)

/-! ### The split example -/

/-- The fine split of the boundary `E¹ = V(x(x-1))`, `E² = V(y(y-1))` of `𝔸²`: the four lines
`V(x), V(x-1)` (label `0`) and `V(y), V(y-1)` (label `1`) with the exponents `1, 0, 1, 0` of
`I = (xy)` along them, `m = 1`; the nerve is the four double points. -/
def splitX : MonomialState :=
  ofValid 2 1 4 2 (fun c => [0, 0, 1, 1].getD c 0) (fun c => [1, 0, 1, 0].getD c 0)
    {{0}, {1}, {2}, {3}, {0, 2}, {0, 3}, {1, 2}, {1, 3}} (by decide)

/-- The same on `U = D((x-1)(y-1))`: the components `1, 3` (`V(x-1)`, `V(y-1)`) are dead, the
nerve is `{0}, {2}, {0, 2}`. -/
def splitU : MonomialState :=
  ofValid 2 1 4 2 (fun c => [0, 0, 1, 1].getD c 0) (fun c => [1, 0, 1, 0].getD c 0)
    {{0}, {2}, {0, 2}} (by decide)

/-- The coarse split, one exponent per member as in [Kol07, Definition–Lemma 110] with members
not assumed irreducible: on `X = 𝔸²`, `E¹ = V(x(x-1))`, `E² = V(y(y-1))` with the coarse exponents
`c_j = min_D ord_D (xy) = 0, 0`; `m = 1`; nerve `{0}, {1}, {0, 1}`. -/
def coarseX : MonomialState :=
  ofValid 2 1 2 2 (fun c => c) (fun _ => 0) {{0}, {1}, {0, 1}} (by decide)

/-- The coarse split on `U = D((x-1)(y-1))`: `E¹|_U = V(x)` and `E²|_U = V(y)` are irreducible,
so the coarse exponents are `1, 1`. -/
def coarseU : MonomialState :=
  ofValid 2 1 2 2 (fun c => c) (fun _ => 1) {{0}, {1}, {0, 1}} (by decide)

end Hironaka.Monomial.Examples
