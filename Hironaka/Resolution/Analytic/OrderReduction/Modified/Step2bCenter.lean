/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.MarkedData
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.Snc.Dictionary
import Hironaka.Resolution.Analytic.OrderReduction.FirstStep
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The centre of the monomial phase at the mark `1`: the positive locus of the latest member

The modified algorithm of [Wlo09, Theorem 7.4.1] resolves the monomial marked ideal `(M(𝓘), 1)`
"by blow-ups at exceptional divisors for which `ρ(x)` is maximal". The monomial case of the
resolution, [Wlo09, §6, Step 2b], orders the divisors of `E` (the linear order of the boundary
family, Kollár's ordered index set [Kol07, Definition 65]; the total transform appends the new
member last, so the order is the order of birth), compares subsets lexicographically, and takes
`ρ(x)` to be the maximal subset whose exponents sum to at least `µ` with every proper sub-sum below
`µ`. At `µ = 1` with natural exponents the admissible subsets are the singletons `{D}` of components
through `x` with exponent `a_D ≥ 1`, so `ρ(x)` is the singleton of the latest-born such component,
and the centre of a step is the locus of the positive-exponent components of the latest-born
member which has one: "the maximal locus of `ρ` determines at most one maximal component of
`supp(I, µ)` through each `x`", and here that locus is the positive locus of the top member, taken
whole.

A component `D ⊆ E^j` has exponent `a_D = ord_D 𝓘 ≥ 1` iff `𝓘` vanishes along `D`, i.e.
`D ⊆ cosupp(𝓘, 1)`, so the positive locus of `E^j` is Kollár's `Z_{-1}` of the proof of
[Kol07, Lemma 102] at the mark `1` ("the union of those irreducible components `E^{jk} ⊂ E^j` that
are contained in `cosupp(I, m)`"), `BD.Zminus1 T.I 1 (T.F.hyp j)`. Its closed-submanifold witness
(`isClosedSubmanifold_Zminus1`), its simple normal crossings with `E` (`hasSncWith_Zminus1`, hence
clause (3′) of [Kol07, Definition 66] through `HasSncWith.hasOnlyNormalCrossingsWith_idealSheaf`)
and the order clause (1′) at the mark `1` (`Zminus1_subset_cosupp`) are reused from there. The
identification with the fine exponents of `componentExponent` is proved in `Step2bLocal.lean`.

This module provides the objects of the rule: `positiveLocus` (Kollár's `Z_{-1}` at the mark `1`),
`activeMembers` (the members with a nonempty positive locus, finitely many by the finiteness clause
of the class), `topMember` (the latest-born active member, the maximum in the linear order) and
`step2bCenter`, with the two head clauses of `isOfOrderGe_cons_iff` for the centre. The blow-up
step (the marked transform at the mark `1` and the total transform) is `Step2bStep.lean`, the
phase by recursion `Step2bPhase.lean`, the exponents after a step `Step2bExponent.lean`. A centre
of codimension one is a legal member of a `CenterList` (the constructor takes any codimension; the
blow-up is then an isomorphism, `cons_codimOne_exists_diffeomorph`, as in the remarks after
[Wlo09, Theorem 2.0.3]).
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

open Hironaka.Manifold.BD

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  (T : AnalyticTriple ψ₀ M)

/-! ### The positive locus of a member: Kollár's `Z_{-1}` at the mark `1` -/

/-- **The positive locus of the member `E^j`**: the union of the connected components of `E^j` along
which `𝓘` vanishes (exponent `a_D = ord_D 𝓘 ≥ 1`), Kollár's `Z_{-1}` of the proof of
[Kol07, Lemma 102] at the mark `1` (`BD.Zminus1`); the singletons of [Wlo09, §6, Step 2b] at
`µ = 1`. -/
def positiveLocus (j : T.F.ι) : Set M := Zminus1 T.I 1 (T.F.hyp j)

omit [FiniteDimensional 𝕜 E] in
theorem positiveLocus_def (j : T.F.ι) : positiveLocus T j = Zminus1 T.I 1 (T.F.hyp j) := rfl

/-- The positive locus lies in its member ("`E^{jk} ⊂ E^j`", the proof of [Kol07, Lemma 102]). -/
theorem positiveLocus_subset (j : T.F.ι) : positiveLocus T j ⊆ T.F.hyp j := Zminus1_subset T 1 j

/-- The positive locus of a member is a closed submanifold of codimension `1`
(`isClosedSubmanifold_Zminus1`). -/
theorem isClosedSubmanifold_positiveLocus (j : T.F.ι) :
    IsClosedSubmanifold ψ₀ (positiveLocus T j) 1 :=
  isClosedSubmanifold_Zminus1 T 1 j

/-- The positive locus has simple normal crossings with `E` (`hasSncWith_Zminus1`; the proof of
[Kol07, Lemma 102] at the mark `1`). -/
theorem hasSncWith_positiveLocus (j : T.F.ι) : T.F.HasSncWith ψ₀ (positiveLocus T j) 1 :=
  hasSncWith_Zminus1 T 1 j

/-- Clause (3′) of [Kol07, Definition 66] for the positive locus as a centre: the reduced boundary
ideal sheaf has only normal crossings with the ideal sheaf of the centre. -/
theorem hasOnlyNormalCrossingsWith_positiveLocus (j : T.F.ι) :
    AnalyticManifold.IdealSheaf.HasOnlyNormalCrossingsWith (T.F.idealSheaf (𝕜 := 𝕜) (E := E))
      (isClosedSubmanifold_positiveLocus T j).idealSheaf :=
  HasSncWith.hasOnlyNormalCrossingsWith_idealSheaf T.isSnc _ (hasSncWith_positiveLocus T j)

/-- `𝓘` vanishes on the positive locus (`Z_{-1} ⊆ cosupp(𝓘, 1)`). -/
theorem one_le_ord_of_mem_positiveLocus {j : T.F.ι} {x : M} (hx : x ∈ positiveLocus T j) :
    ((1 : ℕ) : ℕ∞) ≤ T.I.ord x :=
  Zminus1_subset_cosupp T 1 j hx

/-- Clause (1′) of [Kol07, Definition 66] for the positive locus as a centre at the mark `1`: the
order of `𝓘` along the positive locus is at least `1` at each of its points
(`stalkIdeal_le_pow_of_eventually_le_ord` applied to `Z_{-1} ⊆ cosupp(𝓘, 1)`). -/
theorem one_le_ordAlong_of_mem_positiveLocus {j : T.F.ι} {a : M} (ha : a ∈ positiveLocus T j) :
    ((1 : ℕ) : ℕ∞) ≤
      IdealSheaf.ordAlongIdeal (isClosedSubmanifold_positiveLocus T j).idealSheaf T.I a :=
  (IdealSheaf.le_ordAlongIdeal_iff _ T.I a 1).mpr
    (stalkIdeal_le_pow_of_eventually_le_ord (isClosedSubmanifold_positiveLocus T j) T.I ha
      (Filter.Eventually.of_forall fun y => Zminus1_subset_cosupp T 1 j y.2))

/-! ### The active members and the top member -/

/-- **The active members**: those with a nonempty positive locus, i.e. carrying a component of
positive exponent. -/
def activeMembers : Set T.F.ι := {j | (positiveLocus T j).Nonempty}

theorem activeMembers_subset_nonempty : activeMembers T ⊆ {j | T.F.hyp j ≠ ∅} := by
  intro j hj
  obtain ⟨x, hx⟩ := hj
  exact Set.nonempty_iff_ne_empty.mp ⟨x, positiveLocus_subset T j hx⟩

/-- Finitely many members are active (the finiteness clause of `BMOClass`: finitely many nonempty
members). -/
theorem activeMembers_finite (hT : AnalyticTriple.BMOClass 1 T) : (activeMembers T).Finite := by
  have hfin : Set.Finite {j : T.F.ι | T.F.hyp j ≠ ∅} := Set.finite_coe_iff.mp hT.2
  exact hfin.subset (activeMembers_subset_nonempty T)

/-- **The top member**: the largest active member in the linear order of the family (Kollár's
ordered index set [Kol07, Definition 65], the order of birth along the total transforms). At `µ = 1`
this is the maximal subset of [Wlo09, §6, Step 2b]: the singleton of the latest-born component of
positive exponent. -/
def topMember (hfin : (activeMembers T).Finite) (hne : (activeMembers T).Nonempty) : T.F.ι :=
  hfin.toFinset.max' (by simpa using hne)

omit [FiniteDimensional 𝕜 E] in
theorem topMember_mem (hfin : (activeMembers T).Finite) (hne : (activeMembers T).Nonempty) :
    topMember T hfin hne ∈ activeMembers T :=
  hfin.mem_toFinset.mp (hfin.toFinset.max'_mem _)

omit [FiniteDimensional 𝕜 E] in
theorem le_topMember (hfin : (activeMembers T).Finite) (hne : (activeMembers T).Nonempty)
    {j : T.F.ι} (hj : j ∈ activeMembers T) : j ≤ topMember T hfin hne :=
  hfin.toFinset.le_max' j (hfin.mem_toFinset.mpr hj)

/-! ### The Step 2b centre -/

/-- **The centre of a step of the monomial phase** ([Wlo09, Theorem 7.4.1] with [Wlo09, §6, Step 2b]
at `µ = 1`): the positive locus of the top member, blown up as one centre (its components may be
infinitely many on a non-compact stage; the number of steps at a member is its maximal exponent,
not the number of components). -/
def step2bCenter (hfin : (activeMembers T).Finite) (hne : (activeMembers T).Nonempty) : Set M :=
  positiveLocus T (topMember T hfin hne)

variable (hfin : (activeMembers T).Finite) (hne : (activeMembers T).Nonempty)

/-- The centre is a closed submanifold of codimension `1` (a legal member of a `CenterList`,
`cons_codimOne_exists_diffeomorph`). -/
theorem isClosedSubmanifold_step2bCenter : IsClosedSubmanifold ψ₀ (step2bCenter T hfin hne) 1 :=
  isClosedSubmanifold_positiveLocus T _

omit [FiniteDimensional 𝕜 E] in
/-- The centre is nonempty (the top member is active): no empty blow-up [Kol07, 32]. -/
theorem step2bCenter_nonempty : (step2bCenter T hfin hne).Nonempty :=
  topMember_mem T hfin hne

/-- The centre lies in the top member, inside the support of the boundary ("blow-ups at exceptional
divisors", [Wlo09, Theorem 7.4.1]). -/
theorem step2bCenter_subset : step2bCenter T hfin hne ⊆ T.F.hyp (topMember T hfin hne) :=
  positiveLocus_subset T _

theorem step2bCenter_subset_support : step2bCenter T hfin hne ⊆ T.F.support :=
  (positiveLocus_subset T _).trans (Set.subset_iUnion T.F.hyp _)

/-- The centre has simple normal crossings with `E` (the proof of [Kol07, Lemma 102]). -/
theorem hasSncWith_step2bCenter : T.F.HasSncWith ψ₀ (step2bCenter T hfin hne) 1 :=
  hasSncWith_positiveLocus T _

/-- Clause (3′) of [Kol07, Definition 66] for the centre, the first head clause of
`isOfOrderGe_cons_iff`. -/
theorem hasOnlyNormalCrossingsWith_step2bCenter :
    AnalyticManifold.IdealSheaf.HasOnlyNormalCrossingsWith (T.F.idealSheaf (𝕜 := 𝕜) (E := E))
      (isClosedSubmanifold_step2bCenter T hfin hne).idealSheaf :=
  hasOnlyNormalCrossingsWith_positiveLocus T _

/-- Clause (1′) of [Kol07, Definition 66] at the mark `1` for the centre, the second head clause of
`isOfOrderGe_cons_iff`. -/
theorem one_le_ordAlong_step2bCenter :
    ∀ a ∈ step2bCenter T hfin hne, ((1 : ℕ) : ℕ∞) ≤
      IdealSheaf.ordAlongIdeal (isClosedSubmanifold_step2bCenter T hfin hne).idealSheaf T.I a :=
  fun _ ha => one_le_ordAlong_of_mem_positiveLocus T ha

end Hironaka.Manifold.BMOmod

end
