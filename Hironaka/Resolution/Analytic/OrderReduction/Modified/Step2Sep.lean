/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepALink
public import Hironaka.Resolution.Analytic.OrderReduction.Step22Fam
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.BlowUp.Transform.TuningTransform
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.GoingUp.BoundaryDrop
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1Measure
import Hironaka.Resolution.Analytic.OrderReduction.BMO.SupPow
import Hironaka.Resolution.Analytic.OrderReduction.ClassPullback
import Hironaka.Resolution.Analytic.OrderReduction.FamilyIndependence
import Hironaka.Resolution.Analytic.OrderReduction.Modified.NonmonomialFunctor
import Hironaka.Resolution.Analytic.OrderReduction.Modified.NonmonomialIndiff
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The separation step of the marked order reduction: the invariant and the separating ideal

The second step of Kollár's proof of the marked order reduction theorem [Kol07, Theorem 107]
separates the cosupport of `(I, m)` from the cosupport of the nonmonomial part `N(I)`
[Kol07, 111, Step 2]. With `s` the maximal order of `N(I)` along `cosupp(I, m) = {x | ord_x I ≥ m}`,
one applies the order reduction `BO_{n, ms}` [Kol07, Theorem 68] to the single ideal
`N(I)^m + I^s`, by the observation

  `ord_Z J₁ ≥ s` and `ord_Z J₂ ≥ m`  ⇔  `ord_Z (J₁^m + J₂^s) ≥ ms`,

so that every smooth blow-up sequence of order `ms` for `N(I)^m + I^s` is one of order `s` for
`N(I)` and one of order `m` for `I`; then `s` has dropped and one continues with `s − 1`, until
`s = 0`, i.e. `cosupp(I, m) ∩ cosupp N(I) = ∅`.

On an analytic manifold the rounds of this descent are links of a chain over shrinking relatively
compact opens (`ChainState`), and Kollár's `s` is carried as an **invariant of the state** rather
than read as a supremum: `SepOrdLe S m s` says `ord N(𝓘) ≤ s` at every point of `cosupp(𝓘, m)`.
The descent starts at the bound `s = t − 1` with which the first step exits (`NonmonomialOrdLe`)
and runs through `s = t − 1, …, 1`; a round at a bound above the actual separation order is empty
up to the deletion of empty blow-ups [Kol07, 32]. This module provides:

* **the observation along a smooth centre** (`IdealSheaf.le_ordAlongIdeal_pow_add_pow_iff`), from
  the characterisation of the order along a centre by the pointwise orders at the nearby points
  of the centre (`IdealSheaf.le_ordAlongIdeal_iff_eventually_le_ord`) and the pointwise form
  `IdealSheaf.le_ord_pow_add_pow_iff`; and the additivity of pull-back, `IdealSheaf.pullback_add`;
* **the transform identity modulo `N`**, `NonmonomialTransformIdentityMod`: the predicate, which
  the assembly takes as a parameter and which `nonmonomialTransformIdentityMod_inhabitant` proves;
* **the separation invariant** `SepOrdLe`, the two exit facts at `s = 0`, the separating ideal and
  triple `sepIdealAt` and `sepTripleAt` at an explicit `s`, the order bound `ord_sepIdealAt_le`, and
  the class `SepClass m s` of triples whose separating triple lies in the domain of `BO_{n, ms}`;
* **the order reduction read at the separating triple**, `sepFunctor`, a family functor on
  `SepClass m s` which commutes with local analytic isomorphisms and is indifferent to empty
  boundary members, so that the transport lemmas for values at induced triples apply to the links
  of the separation step.

The scheme-theoretic counterparts are `Hironaka.BMO.sepTriple` and
`AlgebraicGeometry.Scheme.IdealSheafData.leOrdAlong_pow_sup_pow_iff`.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace Filter
open scoped Manifold ContDiff

universe u

namespace Manifold

/-! ### The observation of the separation step along a smooth centre -/

section Along

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] {Y : Set M} {c : ℕ}

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The order of `I` along a smooth centre `Y` at a point `a ∈ Y` is `≥ p` iff the pointwise order
of `I` is `≥ p` at all points of `Y` near `a`. Forwards: the order along `Y` is locally constant
on `Y` (`isLocallyConstant_ordAlong`) and bounds the pointwise order from below
(`ordAlong_le_ord`); backwards: `stalkIdeal_le_pow_of_eventually_le_ord`. -/
theorem IdealSheaf.le_ordAlongIdeal_iff_eventually_le_ord (hY : IsClosedSubmanifold ψ Y c)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) {a : M} (ha : a ∈ Y) (p : ℕ) :
    (p : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I a ↔
      ∀ᶠ y : Y in 𝓝 (⟨a, ha⟩ : Y), (p : ℕ∞) ≤ I.ord (y : M) := by
  constructor
  · intro hp
    filter_upwards [(hY.isLocallyConstant_ordAlong I).eventually_eq (⟨a, ha⟩ : Y)] with y hy
    have hy' : IdealSheaf.ordAlongIdeal hY.idealSheaf I (y : M) =
        IdealSheaf.ordAlongIdeal hY.idealSheaf I a := hy
    calc (p : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I a := hp
      _ = IdealSheaf.ordAlongIdeal hY.idealSheaf I (y : M) := hy'.symm
      _ ≤ I.ord (y : M) := ordAlong_le_ord hY I y.2
  · intro h
    rw [IdealSheaf.le_ordAlongIdeal_iff]
    exact stalkIdeal_le_pow_of_eventually_le_ord hY I ha h

/-- The observation of [Kol07, 111, Step 2] along a smooth centre: for `m, s ≥ 1` and `a ∈ Y`,
`ms ≤ ord_{Y,a} (J₁^m + J₂^s)` iff `s ≤ ord_{Y,a} J₁` and `m ≤ ord_{Y,a} J₂`. It is the pointwise
statement `IdealSheaf.le_ord_pow_add_pow_iff` at the points of `Y` near `a`, through the
characterisation `le_ordAlongIdeal_iff_eventually_le_ord`. -/
theorem IdealSheaf.le_ordAlongIdeal_pow_add_pow_iff [FiniteDimensional 𝕜 E]
    (hY : IsClosedSubmanifold ψ Y c) (J₁ J₂ : IdealSheaf (structureSheaf 𝕜 E M)) {m s : ℕ}
    (hm : 1 ≤ m) (hs : 1 ≤ s) {a : M} (ha : a ∈ Y) :
    ((m * s : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf (J₁ ^ m + J₂ ^ s) a ↔
      (s : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J₁ a ∧
        (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J₂ a := by
  rw [IdealSheaf.le_ordAlongIdeal_iff_eventually_le_ord hY _ ha,
    IdealSheaf.le_ordAlongIdeal_iff_eventually_le_ord hY J₁ ha,
    IdealSheaf.le_ordAlongIdeal_iff_eventually_le_ord hY J₂ ha, ← eventually_and]
  exact eventually_congr
    (Eventually.of_forall fun y => IdealSheaf.le_ord_pow_add_pow_iff J₁ J₂ hm hs (y : M))

end Along

section PullbackAdd

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {M : Type u} [TopologicalSpace M]
  [ChartedSpace E M] {N : Type u} [TopologicalSpace N] [ChartedSpace E' N] (φ : N → M)
  (hφ : ContMDiff 𝓘(𝕜, E') 𝓘(𝕜, E) ω φ)

/-- The pull-back of a sum of ideal sheaves is the sum of the pull-backs (stalkwise
`Ideal.map_sup`). -/
theorem IdealSheaf.pullback_add (I J : IdealSheaf (structureSheaf 𝕜 E M)) :
    (I + J).pullback φ hφ = I.pullback φ hφ + J.pullback φ hφ :=
  IdealSheaf.ext fun b => by
    rw [IdealSheaf.stalkIdeal_pullback, IdealSheaf.stalkIdeal_add, IdealSheaf.stalkIdeal_add,
      IdealSheaf.stalkIdeal_pullback, IdealSheaf.stalkIdeal_pullback, Ideal.map_sup]

end PullbackAdd

end Manifold

namespace Hironaka.Manifold.BMO

open _root_.Manifold

open Hironaka.Manifold.BMOmod

/-! ### The transform identity modulo `N`, as a predicate -/

section Interfaces

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ}

/-- **The transform identity modulo `N`** along a list of centres: for a list of order `≥ m` for
`(𝓘, m)` and of order `≥ s` for `(N(𝓘), s)`, with `m ≥ 1`, no bound on the order of `N(𝓘)` and no
relation between `m` and `s`, the nonmonomial part of the marked transform of `(𝓘, m)` is the
nonmonomial part of the marked transform of `(N(𝓘), s)` at every stage, with respect to the
transformed boundary. This is the observation at the end of [Kol07, 111, Step 1] (the two
birational transforms differ by a product of powers of the exceptional divisors, hence only in their
monomial part) read modulo the monomial part. The descent of the separation step
uses it at `s < m`, where the identity at the exact order (`NonmonomialTransformIdentity`, which
needs `m ≤ d`) does not apply. The assembly takes the predicate as a parameter;
`nonmonomialTransformIdentityMod_inhabitant` proves it. -/
def NonmonomialTransformIdentityMod (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)) : Prop :=
  ∀ {M : AnalyticManifold.{u} 𝕜 E} (S : AnalyticTriple ψ₀ M) (L : AnalyticManifold.BlowUpSequence
      ψ₀ M) (m s : ℕ),
    1 ≤ m →
    ∀ (hL : L.toSuccession.IsOfOrderGe S.I m (S.F.idealSheaf (𝕜 := 𝕜) (E := E)))
      (_hN : L.toSuccession.IsOfOrderGe (nonmonomialTriple S).I s
        (S.F.idealSheaf (𝕜 := 𝕜) (E := E)))
      (i : Fin (L.toSuccession.length + 1)),
      nonmonomialPart (L.toSuccession.totalTransformSeqFrom S.F i)
          (L.toSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq S.isSnc
            (fun j => hL.hasOnlyNormalCrossingsWith j) i).1
          (L.toSuccession.markedTransformSeq S.I m i) =
        nonmonomialPart (L.toSuccession.totalTransformSeqFrom S.F i)
          (L.toSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq S.isSnc
            (fun j => hL.hasOnlyNormalCrossingsWith j) i).1
          (L.toSuccession.markedTransformSeq (nonmonomialTriple S).I s i)

end Interfaces

/-! ### The separation invariant and the separating triple at an explicit `s` -/

section Sep

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- **The separation invariant**: `ord N(𝓘) ≤ s` at every point where `ord 𝓘 ≥ m`. It carries
Kollár's `s`, "the maximum order of `N(I)` along `cosupp(I, m)`" [Kol07, 111, Step 2], as an upper
bound rather than as a supremum. `SepOrdLe S m 0` is the disjointness
`cosupp(𝓘, m) ∩ cosupp N(𝓘) = ∅` (`sepOrdLe_zero_iff`). -/
def SepOrdLe (S : AnalyticTriple ψ₀ M) (m s : ℕ) : Prop :=
  ∀ x, (m : ℕ∞) ≤ S.I.ord x → (nonmonomialTriple S).I.ord x ≤ (s : ℕ∞)

theorem SepOrdLe.weaken {S : AnalyticTriple ψ₀ M} {m s s' : ℕ} (h : SepOrdLe S m s)
    (hss : s ≤ s') : SepOrdLe S m s' :=
  fun x hx => (h x hx).trans (by exact_mod_cast hss)

/-- The separation bound `0` is the disjointness of the cosupports: no point of `cosupp(𝓘, m)`
lies in `cosupp N(𝓘)` [Kol07, 111, Step 2]. -/
theorem sepOrdLe_zero_iff (S : AnalyticTriple ψ₀ M) (m : ℕ) :
    SepOrdLe S m 0 ↔ ∀ x, (m : ℕ∞) ≤ S.I.ord x → x ∉ (nonmonomialTriple S).I.support := by
  unfold SepOrdLe
  simp only [Nat.cast_zero, nonpos_iff_eq_zero, IdealSheaf.ord_eq_zero_iff]

/-- At the exit of the separation step, `ord 𝓘 < m` at every point of `cosupp N(𝓘)`; hence the
centre of any further blow-up, which lies in `cosupp(𝓘, m)`, misses `cosupp N(𝓘)`
[Kol07, 111, Step 2]. -/
theorem SepOrdLe.ord_lt_of_mem_cosupport {S : AnalyticTriple ψ₀ M} {m : ℕ} (h : SepOrdLe S m 0)
    {x : M} (hx : x ∈ (nonmonomialTriple S).I.support) : S.I.ord x < (m : ℕ∞) := by
  by_contra hle
  rw [not_lt] at hle
  have h0 := h x hle
  rw [Nat.cast_zero, nonpos_iff_eq_zero, IdealSheaf.ord_eq_zero_iff] at h0
  exact h0 hx

/-- Off `cosupp N(𝓘)` the stalk of `𝓘` is the stalk of its monomial part: `𝓘 = M(𝓘) · N(𝓘)`
(`monomialPart_mul_nonmonomialPart`) and `N(𝓘)_x = 𝒪_x` there. This is the pointwise form of
"replace `X` by `X ∖ cosupp N(I)` and thus assume that `I = M(I)`" [Kol07, 111, Step 2]. -/
theorem stalkIdeal_eq_monomialPart_of_notMem_cosupport (S : AnalyticTriple ψ₀ M) {x : M}
    (hx : x ∉ (nonmonomialTriple S).I.support) :
    S.I.stalkIdeal x = (monomialPart S.F S.isSnc S.I).stalkIdeal x := by
  have hN : (nonmonomialPart S.F S.isSnc S.I).stalkIdeal x = ⊤ := by
    have h := not_not.mp hx
    rwa [nonmonomialTriple_I] at h
  conv_lhs => rw [← monomialPart_mul_nonmonomialPart S.F S.isSnc S.I]
  rw [IdealSheaf.stalkIdeal_mul, hN, Ideal.mul_top]

/-- **The separating ideal** `N(𝓘)^m + 𝓘^s` of [Kol07, 111, Step 2] at an explicit `s`; the sum is
the sum of ideal sheaves, stalkwise the join. -/
def sepIdealAt (S : AnalyticTriple ψ₀ M) (m s : ℕ) : AnalyticManifold.IdealSheaf M :=
  (nonmonomialTriple S).I ^ m + S.I ^ s

@[simp] theorem stalkIdeal_sepIdealAt (S : AnalyticTriple ψ₀ M) (m s : ℕ) (x : M) :
    (sepIdealAt S m s).stalkIdeal x =
      (nonmonomialTriple S).I.stalkIdeal x ^ m ⊔ S.I.stalkIdeal x ^ s := by
  change ((nonmonomialTriple S).I ^ m + S.I ^ s).stalkIdeal x = _
  rw [IdealSheaf.stalkIdeal_add, IdealSheaf.stalkIdeal_pow, IdealSheaf.stalkIdeal_pow]

/-- The separating ideal is nonzero at every point: its summand `N(𝓘)^m` is nonzero in the stalk,
which is a domain (for `m = 0` the summand is the unit ideal). -/
theorem isNonzeroEverywhere_sepIdealAt (S : AnalyticTriple ψ₀ M) (m s : ℕ) :
    (sepIdealAt S m s).IsNonzeroEverywhere := by
  intro x hx
  have _hdom : IsDomain ((structureSheaf 𝕜 E M).presheaf.stalk x) :=
    isDomain_stalk ψ₀ (IsManifold.chart_mem_maximalAtlas x) (mem_chart_source E x)
  rw [stalkIdeal_sepIdealAt, sup_eq_bot_iff] at hx
  obtain ⟨a, ha, ha0⟩ :=
    (Submodule.ne_bot_iff _).mp ((nonmonomialTriple S).isNonzeroEverywhere x)
  exact (Submodule.ne_bot_iff _).mpr ⟨a ^ m, Ideal.pow_mem_pow ha m, pow_ne_zero m ha0⟩ hx.1

/-- **The separating triple** `(M, N(𝓘)^m + 𝓘^s, E)` of [Kol07, 111, Step 2] at an explicit `s`:
the manifold and the boundary of `S`, with the separating ideal. -/
def sepTripleAt (S : AnalyticTriple ψ₀ M) (m s : ℕ) : AnalyticTriple ψ₀ M :=
  { S with I := sepIdealAt S m s, isNonzeroEverywhere := isNonzeroEverywhere_sepIdealAt S m s }

@[simp] theorem sepTripleAt_I (S : AnalyticTriple ψ₀ M) (m s : ℕ) :
    (sepTripleAt S m s).I = sepIdealAt S m s := rfl

@[simp] theorem sepTripleAt_F (S : AnalyticTriple ψ₀ M) (m s : ℕ) : (sepTripleAt S m s).F = S.F :=
  rfl

/-- Under the separation invariant at `s ≥ 1` (and `m ≥ 1`) the separating ideal has order at most
`ms` at every point, so that the separating triple lies in the domain of `BO_{n, ms}` (Kollár's
"which has order `≥ ms`" [Kol07, 111, Step 2] is the lower bound at the centres; this is the upper
bound the order reduction theorem needs). The order of a sum is the minimum of the orders and the
order of a power is the multiple (the cosupport identities of [Kol07, Definition 59 (3), (4)], read
on orders); on
`cosupp(𝓘, m)` the bound comes from `ord N(𝓘) ≤ s`, off it from `ord 𝓘 < m`. -/
theorem ord_sepIdealAt_le {S : AnalyticTriple ψ₀ M} {m s : ℕ} (hm : 1 ≤ m) (hs : 1 ≤ s)
    (hsep : SepOrdLe S m s) (x : M) : (sepIdealAt S m s).ord x ≤ ((m * s : ℕ) : ℕ∞) := by
  have := finiteDimensional_of_chartIso ψ₀
  have hord : (sepIdealAt S m s).ord x =
      min ((m : ℕ∞) * (nonmonomialTriple S).I.ord x) ((s : ℕ∞) * S.I.ord x) := by
    have h1 := IdealSheaf.ord_add_eq_min ((nonmonomialTriple S).I ^ m) (S.I ^ s) x
    rw [IdealSheaf.ord_pow _ hm x, IdealSheaf.ord_pow _ hs x] at h1
    exact h1
  rw [hord, Nat.cast_mul]
  by_cases hxc : (m : ℕ∞) ≤ S.I.ord x
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left (hsep x hxc) zero_le)
  · refine (min_le_right _ _).trans ?_
    calc (s : ℕ∞) * S.I.ord x ≤ (s : ℕ∞) * (m : ℕ∞) :=
          mul_le_mul_of_nonneg_left (le_of_lt (not_le.mp hxc)) zero_le
      _ = (m : ℕ∞) * (s : ℕ∞) := mul_comm _ _

/-- The separating triple of a triple whose boundary is replaced by an empty extension is the
separating triple with the boundary replaced: the nonmonomial part ignores empty members
(`nonmonomialTriple_eq_of_isEmptyExtension`). This is the input of the indifference property of
the round. -/
theorem sepTripleAt_eq_of_isEmptyExtension (T : AnalyticTriple ψ₀ M) (m s : ℕ)
    (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc ψ₀) {e : F'.ι ↪o T.F.ι}
    (he : HypersurfaceFamily.IsEmptyExtension e) :
    sepTripleAt (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple ψ₀ M) m s =
      ⟨(sepTripleAt T m s).I, (sepTripleAt T m s).isNonzeroEverywhere, F', hsnc'⟩ := by
  refine AnalyticTriple.ext' ?_ rfl
  change (nonmonomialTriple (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple ψ₀ M)).I ^ m +
      T.I ^ s = (nonmonomialTriple T).I ^ m + T.I ^ s
  rw [nonmonomialTriple_eq_of_isEmptyExtension T F' hsnc' he]

/-- The exit bound of the first step, `ord N(𝓘) ≤ d` everywhere, gives the separation invariant at
`d`: the separation step starts at the bound the first step exits with (`stepAChainState_bound`),
with no new supremum. -/
theorem _root_.Hironaka.Manifold.BMOmod.NonmonomialOrdLe.sepOrdLe {S : AnalyticTriple ψ₀ M}
    {d : ℕ} (h : NonmonomialOrdLe S d) (m : ℕ) : SepOrdLe S m d :=
  fun x _ => h x

/-- The class of triples whose separating triple at `(m, s)` lies in the domain of `BO_{n, ms}`
[Kol07, Theorem 68]: `ms ≥ 1`, order at most `ms` everywhere, finitely many nonempty boundary
members. It is the domain of the round of the separation step. -/
abbrev SepClass (m s : ℕ) {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) : Prop :=
  AnalyticTriple.BOClass (m * s) (sepTripleAt T m s)

/-- A triple of the marked class which satisfies the separation invariant at `s ≥ 1` lies in
`SepClass m s`: the mark `ms ≥ 1`, the order bound `ord_sepIdealAt_le`, and the finiteness of the
nonempty members from `BMOClass`. -/
theorem sepClass_of_sepOrdLe {T : AnalyticTriple ψ₀ M} {m s : ℕ}
    (hT : AnalyticTriple.BMOClass m T) (hs : 1 ≤ s) (hsep : SepOrdLe T m s) : SepClass m s T :=
  ⟨Nat.mul_pos hT.1 hs, fun x => ord_sepIdealAt_le hT.1 hs hsep x, by
    rw [sepTripleAt_F]; exact hT.2⟩

/-- The class is indifferent to empty boundary members: deleting or adding empty members keeps the
separating ideal (`sepTripleAt_eq_of_isEmptyExtension`) and the finiteness of the nonempty
members. -/
theorem sepClass_of_isEmptyExtension {T : AnalyticTriple ψ₀ M} {m s : ℕ} (hT : SepClass m s T)
    (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc ψ₀) {e : F'.ι ↪o T.F.ι}
    (he : HypersurfaceFamily.IsEmptyExtension e) :
    SepClass m s (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple ψ₀ M) := by
  unfold SepClass at hT ⊢
  rw [sepTripleAt_eq_of_isEmptyExtension T m s F' hsnc' he]
  have hfin : Finite {b // T.F.hyp b ≠ ∅} := by
    have h := hT.2.2
    rwa [sepTripleAt_F] at h
  exact ⟨hT.1, hT.2.1, finite_nonempty_left_of_isEmptyExtension he hfin⟩

end Sep

/-! ### The class of the round and the order-reduction family read at the separating triple -/

section SepClass

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

variable (hcomp : NonmonomialComap.{u} ψ₀)

include hcomp in
/-- The separating triple of a pull-back is the pull-back of the separating triple — the nonmonomial
part commutes with pull-back (`NonmonomialComap`), and pull-back is additive and multiplicative
(`pullback_add`, `pullback_pow`). -/
theorem sepTripleAt_pullback (S : AnalyticTriple ψ₀ M) (m s : ℕ) {N : AnalyticManifold.{u} 𝕜 E}
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) :
    sepTripleAt (S.pullback h hh) m s = (sepTripleAt S m s).pullback h hh := by
  refine AnalyticTriple.ext' ?_ rfl
  change (nonmonomialTriple (S.pullback h hh)).I ^ m + (S.pullback h hh).I ^ s =
    ((nonmonomialTriple S).I ^ m + S.I ^ s).pullback h h.contMDiff
  rw [hcomp S h hh]
  change ((nonmonomialTriple S).I.pullback h h.contMDiff) ^ m + (S.I.pullback h h.contMDiff) ^ s = _
  simp only
      [IdealSheaf.pullback_add, IdealSheaf.pullback_pow]

include hcomp in
/-- The class is closed under pull-back along local analytic isomorphisms (`sepTripleAt_pullback`,
`boClass_of_isPullbackOf`). -/
theorem sepClass_pullback [FiniteDimensional 𝕜 E] {T : AnalyticTriple ψ₀ M} {m s : ℕ}
    (hT : SepClass m s T) {N : AnalyticManifold.{u} 𝕜 E} (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) : SepClass m s (T.pullback g hg) := by
  unfold SepClass
  rw [sepTripleAt_pullback hcomp T m s g hg]
  exact AnalyticTriple.boClass_of_isPullbackOf hT hg (AnalyticTriple.isPullbackOf_pullback _ _ _)



end SepClass

section SepFunctor

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {m s : ℕ} (bo : BOanFam.{u} 𝕜 n (m * s))

/-- **The order reduction `BO_{n, ms}` read at the separating triple**, as a family functor on
`SepClass m s`: the value of `bo` at `(M, N(𝓘)^m + 𝓘^s, E)`, re-typed as a family for `(M, 𝓘, E)`
(`CompatibleFamily.changeTriple`; the triple is not part of the data of a compatible family).
This is "we apply order reduction to the ideal `N(I)^m + I^s`" [Kol07, 111, Step 2]. The link of
the separation step is `ChainState.linkWith` at its value on the induced triple, so the transport
lemmas for values at induced triples (`AnalyticFamilyFunctor.inducedValue_rel`) apply. -/
def sepFunctor :
    AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (SepClass m s) where
  fam T hT := (bo.functor.fam (sepTripleAt T m s) hT).changeTriple

@[simp] theorem sepFunctor_fam_seqOn {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : SepClass m s T)
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    ((sepFunctor bo).fam T hT).seqOn U hU = (bo.functor.fam (sepTripleAt T m s) hT).seqOn U hU :=
  rfl

/-- The family read at the separating triple commutes with local analytic isomorphisms
([Kol07, Theorem 103 (2)] for the composite): the separating triple of a pull-back is the
pull-back of the separating triple (`sepTripleAt_pullback`), and `bo` commutes. -/
theorem sepFunctor_commutesWithLocalIsos
    (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))) :
    (sepFunctor bo).CommutesWithLocalIsos := by
  intro M N T T' g hg hpull hT hT' U' hU'
  simp only [sepFunctor_fam_seqOn]
  have hT'eq : T' = T.pullback g hg := hpull.eq (AnalyticTriple.isPullbackOf_pullback T g hg)
  have hN : (sepTripleAt T' m s).IsPullbackOf (sepTripleAt T m s) g := by
    rw [hT'eq, sepTripleAt_pullback hcomp T m s g hg]
    exact AnalyticTriple.isPullbackOf_pullback _ _ _
  exact bo.commutesWithLocalIsos (sepTripleAt T m s) (sepTripleAt T' m s) g hg hN hT hT' U' hU'

/-- The family read at the separating triple is indifferent to empty boundary members (the
counterpart, for boundary members, of [Kol07, 32]): the separating triple of the triple with the
replaced boundary is
the separating triple with the boundary replaced (`sepTripleAt_eq_of_isEmptyExtension`), and `bo`
is indifferent. -/
theorem sepFunctor_indifferentToEmptyMembers : (sepFunctor bo).IndifferentToEmptyMembers := by
  intro M T F' hsnc' e h1 h2 hT hT' U hU
  simp only [sepFunctor_fam_seqOn]
  have heq := sepTripleAt_eq_of_isEmptyExtension T m s F' hsnc'
    (⟨h1, h2⟩ : HypersurfaceFamily.IsEmptyExtension e)
  have hT'' : AnalyticTriple.BOClass (m * s) (⟨(sepTripleAt T m s).I,
      (sepTripleAt T m s).isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple _ M) := by
    rw [← heq]
    exact hT'
  rw [AnalyticFamilyFunctor.fam_seqOn_congr_triple bo.functor heq hT' hT'' U hU]
  exact AnalyticFamilyFunctor.IndifferentToEmptyMembers.seqOn_eq_of_eq_F
    bo.indifferentToEmptyMembers (sepTripleAt T m s) (sepTripleAt_F T m s) F' hsnc' e h1 h2 hT
    hT'' U hU

end SepFunctor

end Hironaka.Manifold.BMO

end
