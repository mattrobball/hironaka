/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Basic
public import Hironaka.Scheme.IdealSheaf.Order.Along
import Hironaka.Algebra.Local.ChartFibre
import Hironaka.Algebra.Local.PolynomialOrder
import Hironaka.Algebra.Local.TransformOrder
import Hironaka.Resolution.Algebraic.Hir64.ExtendOpen
import Hironaka.Resolution.Algebraic.Hir64.OrderProduct
import Hironaka.Resolution.Algebraic.Hir64.OrderReductionRound
import Hironaka.Resolution.Algebraic.Hir64.TrivializationLoci
import Hironaka.Resolution.Algebraic.Kol07.CosuppTransport
import Hironaka.Resolution.Algebraic.Tuning.Transform
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.ConcatApi
import Hironaka.Scheme.BlowUpSequence.ConcatClauses
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.OpenTransport
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.BlowUpSequence.Triple
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Invariance
import Hironaka.Scheme.IdealSheaf.Order.Lemma61
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Snc.DictionaryOrder
import Hironaka.Scheme.Snc.EmptyFamily
import Mathlib.Data.ENat.BigOperators
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Hironaka's Corollary 1: simultaneous trivialization of a finite system of ideal sheaves

Corollary 1 of Main Theorem II [Hir64, Corollary 1, pp. 143–144]: given nonzero ideal sheaves
`J_1, …, J_e` on a non-singular `X`, there is a finite succession of monoidal transformations with
non-singular irreducible centers such that (1) every weak transform `J_j(i)` has constant positive
order along the center `D(i)`, and (2) at every point of the end result at least one `J_j(r)` is
the unit ideal. Hironaka calls this the trivialization of a system of coherent sheaves of ideals.

**The proof**, following Hironaka's. Let `J := ∏ J_j`, `T_0 := ⋂ |J_j|` and, if `T_0 ≠ ∅`,
`d := max {ν(J_x) : x ∈ T_0}` (finite since `J` is nonzero everywhere on a Noetherian scheme).
Hironaka's loci are `T := {ν(J) ≥ d}`, `S := T ∖ T_0` and `T ∖ S = T ∩ T_0`. The last is closed
(`trivializationLoci_closed`); `S` is closed too, Hironaka's "we can prove that `T`, `S` and
`T − S` are all closed", proved here by upper semicontinuity and additivity of the orders
(`isClosed_trivialLocus`): around a point `q ∈ T ∖ S`, where `ν(J_q) = d` and every
`ν((J_j)_q) ≥ 1`, the open set `{ν(J) ≤ d} ∩ ⋂_j {ν(J_j) ≤ ν((J_j)_q)}` misses `S`, since a point
of `S` in it would have some `ν(J_{j_0}) = 0` and hence `ν(J) ≤ d − 1`; and `{ν(J) < d}` misses
`S` outright. Main Theorem II (one round of order reduction, `exists_orderReductionRound`) applied
to `(X̄ := X ∖ S, J|_{X̄}, ∅)`, whose `max-ord` is exactly `d`, gives a smooth blow-up sequence with
regular irreducible centers of order `d` whose last weak transform has `max-ord < d`; by clause
(ii) of Main Theorem II the centers lie over `T ∖ S`. The sequence extends across `S`
(`Hironaka/Resolution/Algebraic/Hir64/ExtendOpen.lean`), the extension `S₁` on `X` having
`S₁.pullback u = S̄` and centers in the ranges of the stage lifts, along which regularity,
irreducibility, smoothness and the weak transforms transport
(`Hironaka/Scheme/BlowUpSequence/OpenTransport.lean`). Along `S̄` the weak transform of the product
is the product of the weak transforms and each factor has constant order on each center; the
constants are positive because the order of a weak transform at a point over the center never
exceeds the order at the image (Hironaka's (B*) [Hir64, p. 143]; [Kol07, Lemma 61] read pointwise
along a center of constant order, `ord_weakTransform_le_ord_of_forall_ord_eq`), the image lies in
`T ∖ S` where every factor has order `≥ 1`, and the orders add up to `d` on both sides. Over `S`
the transforms are unchanged (`ord_weakTransformSeq_of_stageMap_notMem`), so on the end result the
factors are simultaneously nontrivial only over `X̄`, where the product has order `< d`. Induction
on `d` and concatenation (`concat`, with the per-stage clauses of
`Hironaka/Scheme/BlowUpSequence/ConcatClauses.lean`) finish; at `T_0 = ∅` the empty sequence does.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData Scheme Hironaka
  BlowUpSequence TopologicalSpace IsLocalRing

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### `ℕ∞` bookkeeping -/

/-- `ℕ∞` bookkeeping for the two "some factor is trivial" arguments: termwise `a ≤ b` with one
`a_{i₀} = 0 < 1 ≤ b_{i₀}` gives `∑ a + 1 ≤ ∑ b`. -/
theorem sum_add_one_le_sum {ι : Type*} [Fintype ι] (a b : ι → ℕ∞) (hab : ∀ i, a i ≤ b i)
    (i₀ : ι) (ha : a i₀ = 0) (hb : 1 ≤ b i₀) : ∑ i, a i + 1 ≤ ∑ i, b i := by
  classical
  rw [← Finset.sum_erase_add _ a (Finset.mem_univ i₀),
    ← Finset.sum_erase_add _ b (Finset.mem_univ i₀), ha, add_zero]
  exact add_le_add (Finset.sum_le_sum fun i _ => hab i) hb

/-! ### Kollár's Lemma 61 pointwise along a center of constant order -/

section LocalBound

variable {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ f)]
  (I : X.IdealSheafData)

include f n in
/-- Hironaka's (B*) [Hir64, p. 143]; [Kol07, Lemma 61] read pointwise: along a smooth center `Z`
on which `I` has constant order `m` at every point, the weak transform of `I` has order at most
`m = ord_{π q} I` at every point `q` over the center. This is the argument of
`ord_controlledTransform_le_of_smooth` with the global hypothesis `max-ord I = m` replaced by the
constancy on `Z` (the only use of `max-ord` there was `ord_{π q} I ≤ m`). Off the center the
blow-up is an isomorphism and the orders agree.
Used for the positivity in condition (1) of [Hir64, Corollary 1]. -/
theorem ord_weakTransform_le_ord_of_forall_ord_eq {m : ℕ} (hZ : ∀ z ∈ Z.support, I.ord z = m)
    (q : Z.blowUp) : (I.weakTransform Z).ord q ≤ I.ord (Z.blowUpπ q) := by
  classical
  by_cases hq : Z.blowUpπ q ∈ Z.support
  · have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
    have hm : I.OrdAlongEq Z.support (m : ℕ∞) := fun η hη => hZ η hη.1
    have hle : I.LeOrdAlong Z.support (m : ℕ∞) := fun η hη => (hm η hη).ge
    have hordz : I.ord (Z.blowUpπ q) = m := hZ _ hq
    rw [weakTransform_eq_markedTransform_of_smooth f n Z I hm, hordz]
    have hP : (Z.stalkIdeal (Z.blowUpπ q)).IsPrime :=
        isPrime_stalkIdeal_of_smooth f n Z hq
    have hreg := isRegularLocalRing_stalk f (Z.blowUpπ q)
    have hIZ : I.stalkIdeal (Z.blowUpπ q) ≤ Z.stalkIdeal (Z.blowUpπ q) ^ m :=
      stalkIdeal_le_pow_of_leOrdAlong f n Z I hle hq
        (stalkIdeal_ne_bot_of_mem_support_of_smooth f Z q hq)
    have hFT : Z.exceptionalDivisor ^ m *
        I.controlledTransformAlong Z.blowUpπ Z.exceptionalDivisor m =
        I.comap Z.blowUpπ :=
      pow_mul_markedTransform Z I m (pow_dvd_comap_of_leOrdAlong f n Z I hle)
    -- the chart at `q`
    obtain ⟨n', y, ρ, hn', hy, hZ', 𝔮, hprime, hle', e, he⟩ :=
      exists_stalk_equiv_localization_chart_of_smooth f Z q hq
    change (I.controlledTransformAlong Z.blowUpπ Z.exceptionalDivisor m).ord q ≤ m
    rw [Scheme.IdealSheafData.ord_eq_ord_stalkIdeal,
      ← ord_map_ringEquiv (B := Localization.AtPrime 𝔮) e,
      ← RingEquiv.toRingHom_eq_coe]
    -- an element `f₀ ∈ I_z` of order exactly `m`, in `Z_z^m = P^m`
    have hordIz : IsLocalRing.ord (I.stalkIdeal (Z.blowUpπ q)) = m := by
      rw [← Scheme.IdealSheafData.ord_eq_ord_stalkIdeal]
      exact hordz
    obtain ⟨f₀, hf₀I, hf₀⟩ := exists_mem_ordElem_eq_of_ord_eq hordIz
    have hf₀P : f₀ ∈ chartCenter y ρ ^ m := by
      have := hIZ hf₀I
      rwa [hZ'] at this
    -- `π^♯ f₀` lies in the stalk of `F^m · T = I^*`
    have hmem0 : Z.blowUpπ.stalkMap q f₀ ∈
        (Z.exceptionalDivisor ^ m *
          I.controlledTransformAlong Z.blowUpπ Z.exceptionalDivisor m).stalkIdeal q := by
      rw [hFT, Scheme.IdealSheafData.stalkIdeal_comap]
      exact Ideal.mem_map_of_mem _ hf₀I
    have hkey := algebraMap_transformElem_mem_map_of_mem q y hy hn' ρ hZ' 𝔮 e he _
      hf₀P hmem0
    -- the local Lemma 61 at the prime `𝔮` of the fibre
    have hbound := ordElem_algebraMap_transformElem_le y hy hn' ρ 𝔮 hle' hf₀P hf₀
    refine le_trans (IsLocalRing.ord_anti (Ideal.span_le.mpr
      (Set.singleton_subset_iff.mpr hkey))) ?_
    rw [ord_span_singleton]
    exact hbound
  · have hq' : q ∉ Z.exceptionalDivisor.support := fun h =>
      hq ((mem_support_comap_iff_apply Z Z.blowUpπ q).mp h)
    exact (ord_weakTransform_of_notMem Z I hq').le

end LocalBound

/-! ### Orders along a smooth sequence: monotonicity, the unchanged region, the product -/

section Along

variable {k : Type u} [Field k] [CharZero k]

/-- Along a smooth sequence whose induced ideals have constant order on every center, the order of
the `i`-th induced ideal at any point is at most the order of the original ideal at its image;
`ord_weakTransform_le_ord_of_forall_ord_eq` stage by stage. -/
theorem ord_weakTransformSeq_le_ord_stageMap :
    ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
      (S : BlowUpSequence X), S.IsSmooth f → ∀ (J : X.IdealSheafData),
      (∀ (j : ℕ) (hj : j < S.length), ∃ c : ℕ, ∀ y ∈ (S.center ⟨j, hj⟩).support,
        (S.weakTransformSeq J ⟨j, Nat.lt_succ_of_lt hj⟩).ord y = c) →
      ∀ (i : Fin (S.length + 1)) (z : S.stage i),
        (S.weakTransformSeq J i).ord z ≤ J.ord (S.stageMap i z)
  | _, _, _, _, nil _, _, _, _, ⟨0, _⟩, _ => le_rfl
  | _, _, _, _, nil _, _, _, _, ⟨_ + 1, hj⟩, _ =>
    (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ hj)).elim
  | _, _, _, _, cons _ _ _, _, _, _, ⟨0, _⟩, _ => le_rfl
  | X, f, n, _, cons _ D rest, hsm, J, hpt, ⟨j + 1, hj⟩, z => by
    obtain ⟨hD, ht⟩ := (isSmooth_cons_iff f D rest).1 hsm
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    have ih := ord_weakTransformSeq_le_ord_stageMap (D.blowUpπ ≫ f) n rest ht
      (J.weakTransform D) (fun j' hj' => hpt (j' + 1) (Nat.succ_lt_succ hj'))
      ⟨j, Nat.lt_of_succ_lt_succ hj⟩ z
    obtain ⟨c, hc⟩ := hpt 0 (Nat.succ_pos _)
    have h1 := ord_weakTransform_le_ord_of_forall_ord_eq f n D J hc
      (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ z)
    change (rest.weakTransformSeq (J.weakTransform D) ⟨j, Nat.lt_of_succ_lt_succ hj⟩).ord z ≤
      J.ord (D.blowUpπ (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ z))
    exact ih.trans h1

/-- Over a point outside a closed set `C` containing the images of all the centers, the order of
every induced ideal is the order of the original: each blow-up is an isomorphism there
(`ord_weakTransform_of_notMem`). In the proof of [Hir64, Corollary 1] this is the observation that
over `S` the transforms are unchanged. -/
theorem ord_weakTransformSeq_of_stageMap_notMem :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (J : X.IdealSheafData) (C : Set X),
      (∀ (i : Fin S.length) (y : S.stage i.castSucc), y ∈ (S.center i).support →
        S.stageMap i.castSucc y ∈ C) →
      ∀ (i : Fin (S.length + 1)) (z : S.stage i), S.stageMap i z ∉ C →
        (S.weakTransformSeq J i).ord z = J.ord (S.stageMap i z)
  | _, nil _, _, _, _, ⟨0, _⟩, _, _ => rfl
  | _, nil _, _, _, _, ⟨_ + 1, hj⟩, _, _ =>
    (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ hj)).elim
  | _, cons _ _ _, _, _, _, ⟨0, _⟩, _, _ => rfl
  | _, cons X D rest, J, C, hC, ⟨j + 1, hj⟩, z, hz => by
    have hz' : rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ z ∉ D.blowUpπ ⁻¹' C := hz
    have ih := ord_weakTransformSeq_of_stageMap_notMem rest (J.weakTransform D)
      (D.blowUpπ ⁻¹' C) (fun i y hy => hC ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ y hy)
      ⟨j, Nat.lt_of_succ_lt_succ hj⟩ z hz'
    have hnot : rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ z ∉
        D.exceptionalDivisor.support := fun hmem =>
      hz (hC ⟨0, Nat.succ_pos _⟩ _ ((mem_support_comap_iff_apply D
          D.blowUpπ _).mp hmem))
    change (rest.weakTransformSeq (J.weakTransform D) ⟨j, Nat.lt_of_succ_lt_succ hj⟩).ord z =
      J.ord (D.blowUpπ (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ z))
    rw [ih]
    exact ord_weakTransform_of_notMem D J hnot

/-- Along a smooth sequence with irreducible centers on which the induced ideals of the product
`∏ J_l` have constant order `d`, the induced ideal of the product at every stage is the product of
the induced ideals of the factors; `weakTransform_prod_of_smooth` stage by stage, the constancy of
each factor's order on the center being `ord_factors_const_on_center_of_smooth`. -/
theorem weakTransformSeq_prod_of_forall_ord_eq :
    ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
      (S : BlowUpSequence X), S.IsSmooth f →
      (∀ i : Fin S.length, IrreducibleSpace (S.center i).subscheme) →
      ∀ {e : ℕ} (J : Fin e → X.IdealSheafData) (d : ℕ),
      (∀ (j : ℕ) (hj : j < S.length), ∀ y ∈ (S.center ⟨j, hj⟩).support,
        (S.weakTransformSeq (∏ l, J l) ⟨j, Nat.lt_succ_of_lt hj⟩).ord y = d) →
      ∀ i : Fin (S.length + 1),
        S.weakTransformSeq (∏ l, J l) i = ∏ l, S.weakTransformSeq (J l) i
  | _, _, _, _, nil _, _, _, _, _, _, _, ⟨0, _⟩ => rfl
  | _, _, _, _, nil _, _, _, _, _, _, _, ⟨_ + 1, hj⟩ =>
    (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ hj)).elim
  | _, _, _, _, cons _ _ _, _, _, _, _, _, _, ⟨0, _⟩ => rfl
  | X, f, n, _, cons _ D rest, hsm, hirr, _, J, d, hcen, ⟨j + 1, hj⟩ => by
    obtain ⟨hD, ht⟩ := (isSmooth_cons_iff f D rest).1 hsm
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    have hD0 : ∀ y ∈ D.support, (∏ l, J l).ord y = d := hcen 0 (Nat.succ_pos _)
    choose c hc using fun l =>
      ord_factors_const_on_center_of_smooth f n D (hirr ⟨0, Nat.succ_pos _⟩) J d hD0 l
    have hw : (∏ l, J l).weakTransform D = ∏ l, (J l).weakTransform D :=
      weakTransform_prod_of_smooth f n D J c hc
    have ih := weakTransformSeq_prod_of_forall_ord_eq (D.blowUpπ ≫ f) n rest ht
      (fun i => hirr ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) (fun l => (J l).weakTransform D) d
      (fun j' hj' y hy => by
        have := hcen (j' + 1) (Nat.succ_lt_succ hj') y hy
        rwa [weakTransformSeq_cons_succ, hw] at this) ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    change rest.weakTransformSeq ((∏ l, J l).weakTransform D) ⟨j, Nat.lt_of_succ_lt_succ hj⟩ =
      ∏ l, rest.weakTransformSeq ((J l).weakTransform D) ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    rw [hw]
    exact ih

/-- Condition (1) of [Hir64, Corollary 1] without positivity: along a smooth sequence with
irreducible centers on which the induced ideals of `∏ J_l` have constant order `d`, every factor's
induced ideal has constant order on every center. -/
theorem exists_ord_weakTransformSeq_eq_on_center {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (S : BlowUpSequence X) (hsm : S.IsSmooth f)
    (hirr : ∀ i : Fin S.length, IrreducibleSpace (S.center i).subscheme) {e : ℕ}
    (J : Fin e → X.IdealSheafData) (d : ℕ)
    (hcen : ∀ (j : ℕ) (hj : j < S.length), ∀ y ∈ (S.center ⟨j, hj⟩).support,
      (S.weakTransformSeq (∏ l, J l) ⟨j, Nat.lt_succ_of_lt hj⟩).ord y = d)
    (j : ℕ) (hj : j < S.length) (l : Fin e) :
    ∃ c : ℕ, ∀ y ∈ (S.center ⟨j, hj⟩).support,
      (S.weakTransformSeq (J l) ⟨j, Nat.lt_succ_of_lt hj⟩).ord y = c := by
  have hP := weakTransformSeq_prod_of_forall_ord_eq f n S hsm hirr J d hcen
    ⟨j, Nat.lt_succ_of_lt hj⟩
  have hst : SmoothOfRelativeDimension n (S.stageMap ⟨j, Nat.lt_succ_of_lt hj⟩ ≫ f) :=
    IsSmooth.smoothOfRelativeDimension_stageMap (n := n) hsm _
  refine ord_factors_const_on_center_of_smooth (S.stageMap ⟨j, Nat.lt_succ_of_lt hj⟩ ≫ f) n
    (S.center ⟨j, hj⟩) (hirr ⟨j, hj⟩) (fun l => S.weakTransformSeq (J l) ⟨j, Nat.lt_succ_of_lt hj⟩)
    d (fun y hy => ?_) l
  rw [← hP]
  exact hcen j hj y hy

/-- Along a smooth sequence the induced ideals of an ideal nonzero on every component are nonzero
on every component. -/
theorem isNonzeroEverywhere_weakTransformSeq_of_isSmooth :
    ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
      (S : BlowUpSequence X), S.IsSmooth f → ∀ (J : X.IdealSheafData), IsNonzeroEverywhere J →
      ∀ i : Fin (S.length + 1), IsNonzeroEverywhere (S.weakTransformSeq J i)
  | _, _, _, _, nil _, _, _, hJ, ⟨0, _⟩ => hJ
  | _, _, _, _, nil _, _, _, _, ⟨_ + 1, hj⟩ =>
    (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ hj)).elim
  | _, _, _, _, cons _ _ _, _, _, hJ, ⟨0, _⟩ => hJ
  | X, f, n, _, cons _ D rest, hsm, J, hJ, ⟨j + 1, hj⟩ => by
    obtain ⟨hD, ht⟩ := (isSmooth_cons_iff f D rest).1 hsm
    have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    exact isNonzeroEverywhere_weakTransformSeq_of_isSmooth (D.blowUpπ ≫ f) n rest ht
      (J.weakTransform D) (isNonzeroEverywhere_weakTransform f D hD J hJ)
      ⟨j, Nat.lt_of_succ_lt_succ hj⟩

/-- A finite product of ideal sheaves nonzero on every component is nonzero on every component of
a smooth `k`-scheme (the orders add and are finite). -/
theorem isNonzeroEverywhere_prod {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] {e : ℕ}
    (J : Fin e → X.IdealSheafData) (hJ : ∀ j, IsNonzeroEverywhere (J j)) :
    IsNonzeroEverywhere (∏ j, J j) := by
  have := SmoothOfRelativeDimension.smooth n f
  intro x hx
  have key : ∀ I : X.IdealSheafData, I.stalkIdeal x = ⊥ ↔ I.ord x = ⊤ := fun I =>
    (Set.ext_iff.mp
      (Scheme.IdealSheafData.setOf_ord_eq_top_eq_setOf_stalkIdeal_eq_bot f I) x).symm
  have h1 : (∏ j, J j).ord x = ⊤ := (key _).mp hx
  rw [ord_prod_of_smooth f n Finset.univ J x] at h1
  obtain ⟨j, -, hj⟩ := ENat.sum_eq_top.mp h1
  exact hJ j x ((key (J j)).mpr hj)

/-- "We can prove that `T`, `S` and `T − S` are all closed" [Hir64, Corollary 1, proof], the case
of `S`: in Hironaka's notation `T := {ν(J) ≥ d}`, the set `S := T ∖ ⋂_j |J_j|` is closed when `d`
bounds `ν(J)` on `⋂_j |J_j|`. The complement is open: around a point of order `< d` by upper
semicontinuity, and around a point `q` of order `≥ d` with all `J_j` nontrivial (so `ν(J_q) = d`)
the open set `{ν(J) ≤ d} ∩ ⋂_j {ν(J_j) ≤ ν((J_j)_q)}` misses `S`, a point of `S` in it having some
`ν(J_{j₀}) = 0` and hence `ν(J) ≤ d − 1`. -/
theorem isClosed_trivialLocus {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] {e : ℕ} (J : Fin e → X.IdealSheafData) (d : ℕ)
    (hd : ∀ x, (∀ j, x ∈ (J j).support) → (∏ j, J j).ord x ≤ d) :
    IsClosed {x : X | (d : ℕ∞) ≤ (∏ j, J j).ord x ∧ ∃ j, x ∉ (J j).support} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro q hq
  have hq' : (d : ℕ∞) ≤ (∏ j, J j).ord q → ∀ j, q ∈ (J j).support := fun hdq j => by
    by_contra hj
    exact hq ⟨hdq, j, hj⟩
  by_cases hlt : (∏ j, J j).ord q < d
  · refine ⟨{x | (∏ j, J j).ord x < d}, fun x hx hmem => absurd hmem.1 (not_le.mpr hx), ?_, hlt⟩
    exact (Scheme.IdealSheafData.upperSemicontinuous_ord f n (∏ j, J j)).isOpen_preimage _
  · have hdq : (d : ℕ∞) ≤ (∏ j, J j).ord q := not_lt.mp hlt
    have hsupp := hq' hdq
    have hqd : (∏ j, J j).ord q ≤ d := hd q hsupp
    have hfin : ∀ j, (J j).ord q ≠ ⊤ := fun j htop => by
      have : (J j).ord q ≤ (∏ j, J j).ord q := by
        rw [ord_prod_of_smooth f n Finset.univ J q]
        exact Finset.single_le_sum (f := fun j => (J j).ord q) (fun _ _ => zero_le)
          (Finset.mem_univ j)
      exact ENat.natCast_ne_top d (top_le_iff.mp ((htop ▸ this).trans hqd))
    refine ⟨{x | (∏ j, J j).ord x < d + 1} ∩ ⋂ j, {x | (J j).ord x < (J j).ord q + 1}, ?_, ?_, ?_⟩
    · rintro x ⟨hx1, hx2⟩ ⟨hdx, j₀, hj₀⟩
      simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hx2
      have hle : ∀ j, (J j).ord x ≤ (J j).ord q := fun j =>
        (ENat.lt_add_one_iff (hfin j)).mp (hx2 j)
      have h0 : (J j₀).ord x = 0 := (Scheme.IdealSheafData.ord_eq_zero_iff _ _).mpr hj₀
      have h1 : 1 ≤ (J j₀).ord q := Order.one_le_iff_ne_zero.mpr fun h =>
        (Scheme.IdealSheafData.ord_eq_zero_iff _ _).mp h (hsupp j₀)
      have hsum := sum_add_one_le_sum (fun j => (J j).ord x) (fun j => (J j).ord q) hle j₀ h0 h1
      rw [← ord_prod_of_smooth f n Finset.univ J x, ← ord_prod_of_smooth f n Finset.univ J q]
        at hsum
      have : (d : ℕ∞) + 1 ≤ d := (add_le_add hdx le_rfl).trans (hsum.trans hqd)
      exact absurd ((ENat.add_one_le_iff (ENat.natCast_ne_top d)).mp this) (lt_irrefl _)
    · exact ((Scheme.IdealSheafData.upperSemicontinuous_ord f n (∏ j, J j)).isOpen_preimage
        _).inter (isOpen_iInter_of_finite fun j =>
          (Scheme.IdealSheafData.upperSemicontinuous_ord f n (J j)).isOpen_preimage _)
    · refine ⟨(ENat.lt_add_one_iff (ENat.natCast_ne_top d)).mpr hqd, ?_⟩
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      exact fun j => (ENat.lt_add_one_iff (hfin j)).mpr le_rfl

end Along

/-! ### One round of Hironaka's argument -/

section Round

variable {k : Type u} [Field k] [CharZero k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsSeparated (X ↘ Spec (CommRingCat.of k))]
  (N : ℕ) [SmoothOfRelativeDimension N (X ↘ Spec (CommRingCat.of k))]

/-- The trivial case of [Hir64, Corollary 1] ("if otherwise, the assertion is trivial"): when at
every point some `J_j` is the unit ideal, the empty sequence does. -/
theorem exists_corollary1_seq_of_forall_exists_notMem {e : ℕ} (J : Fin e → X.IdealSheafData)
    (h : ∀ x, ∃ j, x ∉ (J j).support) :
    ∃ S : BlowUpSequence X,
      (∀ i : Fin S.length,
        IsRegular (S.center i).subscheme ∧ IrreducibleSpace (S.center i).subscheme) ∧
      (∀ (i : Fin S.length) (j : Fin e), ∃ c : ℕ, 0 < c ∧
        ∀ y ∈ (S.center i).support, (S.weakTransformSeq (J j) i.castSucc).ord y = c) ∧
      ∀ x : S.last, ∃ j : Fin e,
        (S.weakTransformSeq (J j) (Fin.last S.length)).stalkIdeal x = ⊤ :=
  ⟨nil X, fun i => absurd i.2 (Nat.not_lt_zero _), fun i => absurd i.2 (Nat.not_lt_zero _),
    fun x => by
      obtain ⟨j, hj⟩ := h x
      exact ⟨j, Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support (J j) hj⟩⟩

include N in
/-- One round of Hironaka's argument for [Hir64, Corollary 1], as described in the module
docstring, at the maximal order `d ≥ 1` of `∏ J_j` on `⋂_j |J_j| ≠ ∅`: a smooth sequence on `X`
with regular irreducible centers, every factor of constant positive order on every center
(condition (1)), and `ν(∏_j J_j(r)) < d` at every point of the end result where all the `J_j(r)`
are nontrivial. -/
theorem exists_round {e : ℕ} (J : Fin e → X.IdealSheafData) (hJ : ∀ j, IsNonzeroEverywhere (J j))
    (hne : {x : X | ∀ j, x ∈ (J j).support}.Nonempty) (d : ℕ) (hd0 : 0 < d)
    (hmax : (∏ j, J j).maxOrdAlong {x : X | ∀ j, x ∈ (J j).support} = d) :
    ∃ S : BlowUpSequence X,
      (∀ i : Fin S.length,
        IsRegular (S.center i).subscheme ∧ IrreducibleSpace (S.center i).subscheme) ∧
      (∀ (i : Fin S.length) (j : Fin e), ∃ c : ℕ, 0 < c ∧
        ∀ y ∈ (S.center i).support, (S.weakTransformSeq (J j) i.castSucc).ord y = c) ∧
      S.IsSmooth (X ↘ Spec (CommRingCat.of k)) ∧
      ∀ x : S.last, (∀ j, x ∈ (S.weakTransformSeq (J j) (Fin.last S.length)).support) →
        (∏ j, S.weakTransformSeq (J j) (Fin.last S.length)).ord x < d := by
  classical
  have := SmoothOfRelativeDimension.smooth N (X ↘ Spec (CommRingCat.of k))
  set f := X ↘ Spec (CommRingCat.of k) with hf
  have hlnoeth : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  have hnoeth : IsNoetherian X := f.isNoetherian_of_field
  have hprod : IsNonzeroEverywhere (∏ j, J j) := isNonzeroEverywhere_prod f N J hJ
  have hI : ∀ x ∈ {x : X | ∀ j, x ∈ (J j).support}, (∏ j, J j).stalkIdeal x ≠ ⊥ :=
    fun x _ => hprod x
  have hle : ∀ x, (∀ j, x ∈ (J j).support) → (∏ j, J j).ord x ≤ d := fun x hx => by
    rw [← hmax]
    exact Scheme.IdealSheafData.le_maxOrdAlong _ (Z := {x : X | ∀ j, x ∈ (J j).support}) hx
  obtain ⟨z₀, hz₀, hz₀ord⟩ :=
    Scheme.IdealSheafData.exists_ord_eq_maxOrdAlong (∏ j, J j) f N hne hI
  rw [hmax] at hz₀ord
  -- Hironaka's loci `S` and `T ∖ S`
  have hSclosed : IsClosed {x : X | (d : ℕ∞) ≤ (∏ j, J j).ord x ∧ ∃ j, x ∉ (J j).support} :=
    isClosed_trivialLocus f N J d hle
  have hCclosed : IsClosed {x : X | (d : ℕ∞) ≤ (∏ j, J j).ord x ∧ ∀ j, x ∈ (J j).support} :=
    trivializationLoci_closed (k := k) X ⟨N, inferInstance⟩ J d
  have hSU : ∀ x, x ∉ {x : X | (d : ℕ∞) ≤ (∏ j, J j).ord x ∧ ∃ j, x ∉ (J j).support} →
      (d : ℕ∞) ≤ (∏ j, J j).ord x → ∀ j, x ∈ (J j).support := fun x hx hdx j => by
    by_contra hj
    exact hx ⟨hdx, j, hj⟩
  have hordU : ∀ x, x ∉ {x : X | (d : ℕ∞) ≤ (∏ j, J j).ord x ∧ ∃ j, x ∉ (J j).support} →
      (∏ j, J j).ord x ≤ d := fun x hx => by
    by_cases hdx : (d : ℕ∞) ≤ (∏ j, J j).ord x
    · exact hle x (hSU x hx hdx)
    · exact (not_le.mp hdx).le
  -- the open subscheme `X̄ = X ∖ S`
  let U : X.Opens := ⟨{x : X | (d : ℕ∞) ≤ (∏ j, J j).ord x ∧ ∃ j, x ∉ (J j).support}ᶜ,
    hSclosed.isOpen_compl⟩
  have hUmem : ∀ p : (U : Scheme.{u}),
      U.ι p ∉ {x : X | (d : ℕ∞) ≤ (∏ j, J j).ord x ∧ ∃ j, x ∉ (J j).support} := fun p => p.2
  have hCU : {x : X | (d : ℕ∞) ≤ (∏ j, J j).ord x ∧ ∀ j, x ∈ (J j).support} ⊆
      Set.range U.ι := by
    intro x hx
    rw [Scheme.Opens.range_ι]
    exact fun ⟨_, j, hj⟩ => hj (hx.2 j)
  let _ : (U : Scheme.{u}).Over (Spec (CommRingCat.of k)) := ⟨U.ι ≫ f⟩
  have hlft : LocallyOfFiniteType ((U : Scheme.{u}) ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ f))
  have hqc : QuasiCompact ((U : Scheme.{u}) ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (QuasiCompact (U.ι ≫ f))
  have hsep : IsSeparated ((U : Scheme.{u}) ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (IsSeparated (U.ι ≫ f))
  have hUN : SmoothOfRelativeDimension N (U.ι ≫ f) := by
    have h1 : SmoothOfRelativeDimension (0 + N) (U.ι ≫ f) := inferInstance
    rwa [Nat.zero_add] at h1
  have hUN' : SmoothOfRelativeDimension N ((U : Scheme.{u}) ↘ Spec (CommRingCat.of k)) := hUN
  have hUsm : Smooth ((U : Scheme.{u}) ↘ Spec (CommRingCat.of k)) :=
    SmoothOfRelativeDimension.smooth N _
  let T : Triple k :=
    { X := .of (U : Scheme.{u})
      smoothOfRelativeDimension := ⟨N, hUN'⟩
      I := (∏ j, J j).comap U.ι
      isNonzeroEverywhere := isNonzeroEverywhere_comap_of_flat U.ι hprod
      E := DivisorFamily.empty (U : Scheme.{u})
      isSnc := isSnc_empty_of_smooth ((U : Scheme.{u}) ↘ Spec (CommRingCat.of k)) }
  -- `max-ord` of `J` on `X̄` is `d`
  have hTI : T.I.maxOrd = d := by
    apply le_antisymm
    · rw [Scheme.IdealSheafData.maxOrd_le_iff]
      intro y
      change ((∏ j, J j).comap U.ι).ord y ≤ d
      rw [Scheme.IdealSheafData.ord_comap_of_isOpenImmersion]
      exact hordU _ (hUmem y)
    · have hz₀U : z₀ ∈ Set.range U.ι := by
        rw [Scheme.Opens.range_ι]
        exact fun ⟨_, j, hj⟩ => hj (hz₀ j)
      obtain ⟨y₀, hy₀⟩ := hz₀U
      have := Scheme.IdealSheafData.le_maxOrd T.I y₀
      change ((∏ j, J j).comap U.ι).ord y₀ ≤ _ at this
      rwa [Scheme.IdealSheafData.ord_comap_of_isOpenImmersion, hy₀, hz₀ord] at this
  -- Main Theorem II, one round, on `X̄`
  obtain ⟨S', hS', hirr', hlt'⟩ := exists_orderReductionRound T d hTI hd0
  have hsm' : S'.IsSmooth (U.ι ≫ f) := hS'.1
  have hii : ∀ (i : Fin S'.length) (y : S'.stage i.castSucc), y ∈ (S'.center i).support →
      (d : ℕ∞) ≤ (S'.weakTransformSeq T.I i.castSucc).ord y := fun i y hy =>
    IsOrderSeq.le_ord_of_mem_center ((U : Scheme.{u}) ↘ Spec (CommRingCat.of k)) N hS' i hy
  -- clause (ii): the centers lie over `T ∖ S`
  have hcent : ∀ (i : Fin S'.length) (y : S'.stage i.castSucc), y ∈ (S'.center i).support →
      U.ι (S'.stageMap i.castSucc y) ∈
        {x : X | (d : ℕ∞) ≤ (∏ j, J j).ord x ∧ ∀ j, x ∈ (J j).support} := fun i y hy => by
    have h1 := le_ord_stageMap_of_le_ord_weakTransformSeq_gen S' T.I d hii i.castSucc y
      (hii i y hy)
    change (d : ℕ∞) ≤ ((∏ j, J j).comap U.ι).ord _ at h1
    rw [Scheme.IdealSheafData.ord_comap_of_isOpenImmersion] at h1
    exact ⟨h1, hSU _ (hUmem _) h1⟩
  -- the extension across `S`
  obtain ⟨S₁, hpull, hcentC⟩ := exists_extend_of_isOpenImmersion U.ι S' _ hCclosed hCU hcent
  subst hpull
  have hCR : S₁.CentersInRange U.ι := fun i y hy => by
    rw [range_pullbackStageHom]
    exact hCU (hcentC i y hy)
  have hsm₁ : S₁.IsSmooth f := isSmooth_of_isSmooth_pullback U.ι S₁ f hCR hsm'
  have hreg₁ := forall_isRegular_center_of_pullback U.ι S₁ hCR fun i => (hirr' i).1
  have hirr₁ := forall_irreducibleSpace_center_of_pullback U.ι S₁ hCR fun i => (hirr' i).2
  -- the product and the constants on `X̄`
  have hcomap : (∏ j, J j).comap U.ι = ∏ j, (J j).comap U.ι :=
    Scheme.IdealSheafData.comap_finset_prod Finset.univ J U.ι
  have hcen : ∀ (j : ℕ) (hj : j < (S₁.pullback U.ι).length),
      ∀ y ∈ ((S₁.pullback U.ι).center ⟨j, hj⟩).support,
        ((S₁.pullback U.ι).weakTransformSeq (∏ l, (J l).comap U.ι)
          ⟨j, Nat.lt_succ_of_lt hj⟩).ord y = d := fun j hj y hy => by
    rw [← hcomap]
    exact IsOrderSeq.ord_eq_of_mem_center ((U : Scheme.{u}) ↘ Spec (CommRingCat.of k)) N hS'
      hTI ⟨j, hj⟩ hy
  have hP := weakTransformSeq_prod_of_forall_ord_eq (U.ι ≫ f) N (S₁.pullback U.ι) hsm'
    (fun i => (hirr' i).2) (fun l => (J l).comap U.ι) d hcen
  have hconst : ∀ (j : ℕ) (hj : j < (S₁.pullback U.ι).length) (l : Fin e), ∃ c : ℕ,
      ∀ y ∈ ((S₁.pullback U.ι).center ⟨j, hj⟩).support,
        ((S₁.pullback U.ι).weakTransformSeq ((J l).comap U.ι)
          ⟨j, Nat.lt_succ_of_lt hj⟩).ord y = c := fun j hj l =>
    exists_ord_weakTransformSeq_eq_on_center (U.ι ≫ f) N (S₁.pullback U.ι) hsm'
      (fun i => (hirr' i).2) (fun l => (J l).comap U.ι) d hcen j hj l
  have hpt : ∀ (l : Fin e) (j : ℕ) (hj : j < S₁.length), ∃ c : ℕ,
      ∀ y ∈ ((S₁.pullback U.ι).center (S₁.pullbackCenterIdx U.ι ⟨j, hj⟩)).support,
        ((S₁.pullback U.ι).weakTransformSeq ((J l).comap U.ι)
          (S₁.pullbackStageIdx U.ι ⟨j, Nat.lt_succ_of_lt hj⟩)).ord y = c :=
    fun l j hj => hconst j (by rwa [length_pullback]) l
  have hwt : ∀ (l : Fin e) (i : Fin (S₁.length + 1)),
      (S₁.pullback U.ι).weakTransformSeq ((J l).comap U.ι) (S₁.pullbackStageIdx U.ι i) =
        (S₁.weakTransformSeq (J l) i).comap (S₁.pullbackStageHom U.ι i) := fun l i =>
    weakTransformSeq_pullback_of_isOpenImmersion f N U.ι S₁ hCR hsm₁ (J l) (hpt l) i
  -- positivity of the constants: the orders at a point of the center sum to `d`, each is at most
  -- the order of the factor at the image in `T ∖ S`, where every factor has order `≥ 1`
  have hpos : ∀ (j : ℕ) (hj : j < (S₁.pullback U.ι).length) (l : Fin e) (c : ℕ),
      (∀ y ∈ ((S₁.pullback U.ι).center ⟨j, hj⟩).support,
        ((S₁.pullback U.ι).weakTransformSeq ((J l).comap U.ι)
          ⟨j, Nat.lt_succ_of_lt hj⟩).ord y = c) → 0 < c := fun j hj l c hc => by
    have := (hirr' ⟨j, hj⟩).2
    obtain ⟨p⟩ := (inferInstance : Nonempty ((S₁.pullback U.ι).center ⟨j, hj⟩).subscheme)
    have hy : ((S₁.pullback U.ι).center ⟨j, hj⟩).subschemeι p ∈
        ((S₁.pullback U.ι).center ⟨j, hj⟩).support := by
      rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
      exact Set.mem_range_self p
    have hst : SmoothOfRelativeDimension N
        ((S₁.pullback U.ι).stageMap ⟨j, Nat.lt_succ_of_lt hj⟩ ≫ (U.ι ≫ f)) :=
      IsSmooth.smoothOfRelativeDimension_stageMap (n := N) hsm' _
    have hsum : ∑ l', ((S₁.pullback U.ι).weakTransformSeq ((J l').comap U.ι)
        ⟨j, Nat.lt_succ_of_lt hj⟩).ord (((S₁.pullback U.ι).center ⟨j, hj⟩).subschemeι p) = d := by
      rw [← ord_prod_of_smooth ((S₁.pullback U.ι).stageMap ⟨j, Nat.lt_succ_of_lt hj⟩ ≫ (U.ι ≫ f))
        N Finset.univ, ← hP ⟨j, Nat.lt_succ_of_lt hj⟩]
      exact hcen j hj _ hy
    have hmono : ∀ l', ((S₁.pullback U.ι).weakTransformSeq ((J l').comap U.ι)
        ⟨j, Nat.lt_succ_of_lt hj⟩).ord (((S₁.pullback U.ι).center ⟨j, hj⟩).subschemeι p) ≤
        (J l').ord (U.ι ((S₁.pullback U.ι).stageMap ⟨j, Nat.lt_succ_of_lt hj⟩
          (((S₁.pullback U.ι).center ⟨j, hj⟩).subschemeι p))) := fun l' => by
      have h1 := ord_weakTransformSeq_le_ord_stageMap (U.ι ≫ f) N (S₁.pullback U.ι) hsm'
        ((J l').comap U.ι) (fun j'' hj'' => hconst j'' hj'' l') ⟨j, Nat.lt_succ_of_lt hj⟩
        (((S₁.pullback U.ι).center ⟨j, hj⟩).subschemeι p)
      rwa [Scheme.IdealSheafData.ord_comap_of_isOpenImmersion] at h1
    have hqC := hcent ⟨j, hj⟩ _ hy
    have hsumq : ∑ l', (J l').ord (U.ι ((S₁.pullback U.ι).stageMap ⟨j, Nat.lt_succ_of_lt hj⟩
        (((S₁.pullback U.ι).center ⟨j, hj⟩).subschemeι p))) ≤ d := by
      rw [← ord_prod_of_smooth f N Finset.univ]
      exact hle _ hqC.2
    by_contra hc0
    have h0 : ((S₁.pullback U.ι).weakTransformSeq ((J l).comap U.ι)
        ⟨j, Nat.lt_succ_of_lt hj⟩).ord (((S₁.pullback U.ι).center ⟨j, hj⟩).subschemeι p) = 0 := by
      rw [hc _ hy, Nat.eq_zero_of_not_pos hc0, Nat.cast_zero]
    have h1 : 1 ≤ (J l).ord (U.ι ((S₁.pullback U.ι).stageMap ⟨j, Nat.lt_succ_of_lt hj⟩
        (((S₁.pullback U.ι).center ⟨j, hj⟩).subschemeι p))) :=
      Order.one_le_iff_ne_zero.mpr fun h =>
        (Scheme.IdealSheafData.ord_eq_zero_iff _ _).mp h (hqC.2 l)
    have := sum_add_one_le_sum _ _ hmono l h0 h1
    rw [hsum] at this
    exact absurd ((ENat.add_one_le_iff (ENat.natCast_ne_top d)).mp (this.trans hsumq))
      (lt_irrefl _)
  -- condition (1) on `X`
  have hclause1 : ∀ (i : Fin S₁.length) (j : Fin e), ∃ c : ℕ, 0 < c ∧
      ∀ y ∈ (S₁.center i).support, (S₁.weakTransformSeq (J j) i.castSucc).ord y = c := by
    rintro ⟨i, hi⟩ l
    have hi' : i < (S₁.pullback U.ι).length := by rwa [length_pullback]
    obtain ⟨c, hc⟩ := hconst i hi' l
    refine ⟨c, hpos i hi' l c hc, fun y hy => ?_⟩
    obtain ⟨yb, rfl⟩ := hCR ⟨i, hi⟩ hy
    have hyb : yb ∈ ((S₁.pullback U.ι).center (S₁.pullbackCenterIdx U.ι ⟨i, hi⟩)).support := by
      rw [center_pullback_mk S₁ U.ι i hi]
      exact (mem_support_comap_iff_apply _ _ _).mpr hy
    have := isOpenImmersion_pullbackStageHom S₁ U.ι (Fin.castSucc ⟨i, hi⟩)
    rw [← Scheme.IdealSheafData.ord_comap_of_isOpenImmersion, ← hwt l]
    exact hc yb hyb
  -- the end result: where all factors are nontrivial, the product has order `< d`
  have hidx : S₁.pullbackStageIdx U.ι (Fin.last S₁.length) = Fin.last _ :=
    Fin.ext (length_pullback S₁ U.ι).symm
  have hlast : ∀ x : S₁.last,
      (∀ j, x ∈ (S₁.weakTransformSeq (J j) (Fin.last S₁.length)).support) →
      (∏ j, S₁.weakTransformSeq (J j) (Fin.last S₁.length)).ord x < d := fun x hx => by
    have hstX : SmoothOfRelativeDimension N (S₁.stageMap (Fin.last S₁.length) ≫ f) :=
      IsSmooth.smoothOfRelativeDimension_stageMap (n := N) hsm₁ _
    by_cases hxU : x ∈ Set.range (S₁.pullbackStageHom U.ι (Fin.last S₁.length))
    · obtain ⟨xb, rfl⟩ := hxU
      have := isOpenImmersion_pullbackStageHom S₁ U.ι (Fin.last S₁.length)
      have hstU : SmoothOfRelativeDimension N ((S₁.pullback U.ι).stageMap
          (S₁.pullbackStageIdx U.ι (Fin.last S₁.length)) ≫ (U.ι ≫ f)) :=
        IsSmooth.smoothOfRelativeDimension_stageMap (n := N) hsm' _
      have hterm : ∀ l, (S₁.weakTransformSeq (J l) (Fin.last S₁.length)).ord
          (S₁.pullbackStageHom U.ι (Fin.last S₁.length) xb) =
          ((S₁.pullback U.ι).weakTransformSeq ((J l).comap U.ι)
            (S₁.pullbackStageIdx U.ι (Fin.last S₁.length))).ord xb := fun l => by
        rw [← Scheme.IdealSheafData.ord_comap_of_isOpenImmersion, ← hwt l]
      have hlt'' : ((S₁.pullback U.ι).weakTransformSeq T.I
          (S₁.pullbackStageIdx U.ι (Fin.last S₁.length))).maxOrd < d := by
        rw [hidx]
        exact hlt'
      rw [ord_prod_of_smooth (S₁.stageMap (Fin.last S₁.length) ≫ f) N Finset.univ]
      simp_rw [hterm]
      rw [← ord_prod_of_smooth ((S₁.pullback U.ι).stageMap
        (S₁.pullbackStageIdx U.ι (Fin.last S₁.length)) ≫ (U.ι ≫ f)) N Finset.univ, ← hP, ← hcomap]
      exact lt_of_le_of_lt (Scheme.IdealSheafData.le_maxOrd _ _) hlt''
    · exfalso
      have hxS : S₁.stageMap (Fin.last S₁.length) x ∈
          {x : X | (d : ℕ∞) ≤ (∏ j, J j).ord x ∧ ∃ j, x ∉ (J j).support} := by
        by_contra hxS
        apply hxU
        rw [range_pullbackStageHom]
        change S₁.stageMap (Fin.last S₁.length) x ∈ Set.range U.ι
        rw [Scheme.Opens.range_ι]
        exact hxS
      obtain ⟨_, j, hj⟩ := hxS
      have hnotC : S₁.stageMap (Fin.last S₁.length) x ∉
          {x : X | (d : ℕ∞) ≤ (∏ j, J j).ord x ∧ ∀ j, x ∈ (J j).support} :=
        fun hC => hj (hC.2 j)
      have h0 := ord_weakTransformSeq_of_stageMap_notMem S₁ (J j) _ hcentC (Fin.last _) x hnotC
      have h0' : (S₁.weakTransformSeq (J j) (Fin.last S₁.length)).ord x =
          (J j).ord (S₁.stageMap (Fin.last S₁.length) x) := h0
      rw [(Scheme.IdealSheafData.ord_eq_zero_iff _ _).mpr hj] at h0'
      exact (Scheme.IdealSheafData.ord_eq_zero_iff _ _).mp h0' (hx j)
  exact ⟨S₁, fun i => ⟨hreg₁ i, hirr₁ i⟩, hclause1, hsm₁, hlast⟩

end Round

/-! ### Induction on `d` and assembly -/

section Assembly

variable {k : Type u} [Field k] [CharZero k]

/-- [Hir64, Corollary 1] for every system whose product has order at most `d` on the common
support ("either the integer `d` gets reduced, or (2) is achieved"): induction on `d`, one round
(`exists_round`) followed by the induction hypothesis at the end result, the two sequences
concatenated. -/
theorem exists_corollary1_seq_of_maxOrdAlong_le (d : ℕ) :
    ∀ (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
      [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsSeparated (X ↘ Spec (CommRingCat.of k))]
      (N : ℕ) [SmoothOfRelativeDimension N (X ↘ Spec (CommRingCat.of k))]
      {e : ℕ} (_he : 0 < e) (J : Fin e → X.IdealSheafData) (_hJ : ∀ j, IsNonzeroEverywhere (J j)),
      (∏ j, J j).maxOrdAlong {x : X | ∀ j, x ∈ (J j).support} ≤ d →
      ∃ S : BlowUpSequence X,
        (∀ i : Fin S.length,
          IsRegular (S.center i).subscheme ∧ IrreducibleSpace (S.center i).subscheme) ∧
        (∀ (i : Fin S.length) (j : Fin e), ∃ c : ℕ, 0 < c ∧
          ∀ y ∈ (S.center i).support, (S.weakTransformSeq (J j) i.castSucc).ord y = c) ∧
        ∀ x : S.last, ∃ j : Fin e,
          (S.weakTransformSeq (J j) (Fin.last S.length)).stalkIdeal x = ⊤ := by
  induction d with
  | zero =>
    intro X _ _ _ N _ e he J _ hle
    have := SmoothOfRelativeDimension.smooth N (X ↘ Spec (CommRingCat.of k))
    apply exists_corollary1_seq_of_forall_exists_notMem
    intro x
    by_contra hx
    push Not at hx
    have h1 : (∏ j, J j).ord x ≤ 0 := by
      have := Scheme.IdealSheafData.le_maxOrdAlong (∏ j, J j)
        (Z := {x : X | ∀ j, x ∈ (J j).support}) hx
      rw [Nat.cast_zero] at hle
      exact this.trans hle
    have h2 : 1 ≤ (∏ j, J j).ord x := by
      rw [ord_prod_of_smooth (X ↘ Spec (CommRingCat.of k)) N Finset.univ]
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => (J j).ord x) (fun _ _ => zero_le)
        (Finset.mem_univ ⟨0, he⟩))
      exact Order.one_le_iff_ne_zero.mpr fun h =>
        (Scheme.IdealSheafData.ord_eq_zero_iff _ _).mp h (hx ⟨0, he⟩)
    exact absurd (h2.trans h1) (not_le.mpr zero_lt_one)
  | succ d ih =>
    intro X _ _ _ N _ e he J hJ hle
    have := SmoothOfRelativeDimension.smooth N (X ↘ Spec (CommRingCat.of k))
    set f := X ↘ Spec (CommRingCat.of k) with hf
    by_cases hall : ∀ x, ∃ j, x ∉ (J j).support
    · exact exists_corollary1_seq_of_forall_exists_notMem X J hall
    push Not at hall
    have hnoeth : IsNoetherian X := f.isNoetherian_of_field
    have hlnoeth : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
    have hprod : IsNonzeroEverywhere (∏ j, J j) := isNonzeroEverywhere_prod f N J hJ
    have hfin : (∏ j, J j).maxOrdAlong {x : X | ∀ j, x ∈ (J j).support} ≠ ⊤ :=
      Scheme.IdealSheafData.maxOrdAlong_ne_top (∏ j, J j) f N fun x _ => hprod x
    have hm : (((∏ j, J j).maxOrdAlong {x : X | ∀ j, x ∈ (J j).support}).toNat : ℕ∞) =
        (∏ j, J j).maxOrdAlong {x : X | ∀ j, x ∈ (J j).support} := ENat.natCast_toNat hfin
    rcases Nat.lt_or_ge ((∏ j, J j).maxOrdAlong {x : X | ∀ j, x ∈ (J j).support}).toNat
        (d + 1) with hlt | hge
    · -- the maximal order is already `≤ d`
      exact ih X N he J hJ (by rw [← hm]; exact_mod_cast Nat.lt_succ_iff.mp hlt)
    · have hmd : ((∏ j, J j).maxOrdAlong {x : X | ∀ j, x ∈ (J j).support}).toNat = d + 1 := by
        apply le_antisymm _ hge
        rw [← hm] at hle
        exact_mod_cast hle
      rw [hmd] at hm
      -- one round at the maximal order `d + 1`
      obtain ⟨S₁, hcen₁, hcl₁, hsm₁, hlast₁⟩ := exists_round (k := k) X N J hJ hall (d + 1)
        (Nat.succ_pos d) hm.symm
      -- the induced data on the end result
      let _ : S₁.last.Over (Spec (CommRingCat.of k)) := ⟨S₁.stageMap (Fin.last _) ≫ f⟩
      have hprop := isProper_stageMap S₁ (Fin.last _)
      have hlft : LocallyOfFiniteType (S₁.last ↘ Spec (CommRingCat.of k)) :=
        inferInstanceAs (LocallyOfFiniteType (S₁.stageMap (Fin.last _) ≫ f))
      have hqc : QuasiCompact (S₁.last ↘ Spec (CommRingCat.of k)) :=
        inferInstanceAs (QuasiCompact (S₁.stageMap (Fin.last _) ≫ f))
      have hsep : IsSeparated (S₁.last ↘ Spec (CommRingCat.of k)) :=
        inferInstanceAs (IsSeparated (S₁.stageMap (Fin.last _) ≫ f))
      have hsor : SmoothOfRelativeDimension N (S₁.last ↘ Spec (CommRingCat.of k)) :=
        IsSmooth.smoothOfRelativeDimension_stageMap (n := N) hsm₁ _
      have hJ' : ∀ j, IsNonzeroEverywhere (S₁.weakTransformSeq (J j) (Fin.last S₁.length)) :=
        fun j => isNonzeroEverywhere_weakTransformSeq_of_isSmooth f N S₁ hsm₁ (J j) (hJ j) _
      have hle' : (∏ j, S₁.weakTransformSeq (J j) (Fin.last S₁.length)).maxOrdAlong
          {x : S₁.last | ∀ j, x ∈ (S₁.weakTransformSeq (J j) (Fin.last S₁.length)).support} ≤
            d := by
        rw [Scheme.IdealSheafData.maxOrdAlong_le_iff]
        intro x hx
        have := hlast₁ x hx
        rw [Nat.cast_succ] at this
        exact (ENat.lt_add_one_iff (ENat.natCast_ne_top d)).mp this
      obtain ⟨S₂, hcen₂, hcl₂, hlast₂⟩ := ih S₁.last N he
        (fun j => S₁.weakTransformSeq (J j) (Fin.last S₁.length)) hJ' hle'
      refine ⟨S₁.concat S₂, forall_center_concat
        (fun D => IsRegular D.subscheme ∧ IrreducibleSpace D.subscheme) S₁ S₂ hcen₁ hcen₂,
        fun i j => ?_, fun x => ?_⟩
      · exact forall_stage_concat
          (fun D W _ => ∃ c : ℕ, 0 < c ∧ ∀ y ∈ D.support, W.ord y = c) S₁ S₂ (J j) ⊤
          (fun i => hcl₁ i j) (fun i => hcl₂ i j) i
      · obtain ⟨j, hj⟩ := hlast₂ (eqToHom (last_concat S₁ S₂) x)
        refine ⟨j, ?_⟩
        rw [weakTransformSeq_concat_last]
        change ((S₂.weakTransformSeq (S₁.weakTransformSeq (J j) (Fin.last S₁.length))
          (Fin.last S₂.length)).comap (eqToHom (last_concat S₁ S₂))).stalkIdeal x = ⊤
        rw [Scheme.IdealSheafData.stalkIdeal_comap]
        have hj' : (S₂.weakTransformSeq (S₁.weakTransformSeq (J j) (Fin.last S₁.length))
            (Fin.last S₂.length)).stalkIdeal (eqToHom (last_concat S₁ S₂) x) = ⊤ := hj
        exact (congrArg (Ideal.map ((eqToHom (last_concat S₁ S₂)).stalkMap x).hom) hj').trans
          (Ideal.map_top _)

/-- **Hironaka's Corollary 1** [Hir64, Corollary 1, pp. 143–144], the trivialization of a system
of coherent sheaves of ideals: a finite succession of monoidal transformations with
non-singular irreducible centers such that (1) every weak transform `J_j(i)` has constant positive
order along the center `D(i)`, and (2) at every point of the end result at least one `J_j(r)` is
the unit ideal. This is `exists_corollary1_seq_of_maxOrdAlong_le` at the (finite) maximal order of
`∏ J_j` on `⋂_j |J_j|`. Hironaka's non-singularity of `X` is not a hypothesis: the proof runs the
order reduction of Main Theorem II on `X`, which is smooth of a single relative dimension over the
field `k` of characteristic zero (`hN`; the restriction is lifted in `ComponentwiseCorollaries`),
and smoothness over the perfect field `k` gives the regularity of the local rings. -/
theorem hironaka_corollary1 (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    (hN : ∃ N : ℕ, SmoothOfRelativeDimension N (X ↘ Spec (CommRingCat.of k)))
    {e : ℕ} (he : 0 < e) (J : Fin e → X.IdealSheafData)
    (hJ : ∀ j, IsNonzeroEverywhere (J j)) :
    ∃ S : BlowUpSequence X,
      (∀ i : Fin S.length,
        IsRegular (S.center i).subscheme ∧ IrreducibleSpace (S.center i).subscheme) ∧
      (∀ (i : Fin S.length) (j : Fin e), ∃ c : ℕ, 0 < c ∧
        ∀ y ∈ (S.center i).support, (S.weakTransformSeq (J j) i.castSucc).ord y = c) ∧
      ∀ x : S.last, ∃ j : Fin e,
        (S.weakTransformSeq (J j) (Fin.last S.length)).stalkIdeal x = ⊤ := by
  obtain ⟨N, hN⟩ := hN
  have := SmoothOfRelativeDimension.smooth N (X ↘ Spec (CommRingCat.of k))
  have hnoeth : IsNoetherian X := (X ↘ Spec (CommRingCat.of k)).isNoetherian_of_field
  have hprod : IsNonzeroEverywhere (∏ j, J j) :=
    isNonzeroEverywhere_prod (X ↘ Spec (CommRingCat.of k)) N J hJ
  have hfin : (∏ j, J j).maxOrdAlong {x : X | ∀ j, x ∈ (J j).support} ≠ ⊤ :=
    Scheme.IdealSheafData.maxOrdAlong_ne_top (∏ j, J j) (X ↘ Spec (CommRingCat.of k)) N
      fun x _ => hprod x
  exact exists_corollary1_seq_of_maxOrdAlong_le (k := k) _ X N he J hJ (ENat.natCast_toNat hfin).ge

end Assembly

end Hironaka.Sequence
