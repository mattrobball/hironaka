/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.Pushforward
public import Hironaka.Manifold.FiniteSuccession.Order
public import Hironaka.Manifold.IdealSheaf.Tuning
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.BlowUp.Transform.TuningTransform
import Hironaka.Manifold.FiniteSuccession.DerivTransform
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Tuning
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Going up: the order bookkeeping of Kollár's proof of Theorem 84

The tools of the induction in Kollár's proof of the going-up theorem [Kol07, 90], on analytic
manifolds: the elementary properties of the cosupport of a marked ideal sheaf
[Kol07, Definition 59] along a blow-up sequence, and the passage from orders at points to the
order along a pushed-forward centre. The algebraic counterparts are `cosupp_pow`,
`cosupp_markedTransformSeq_subset_of_le`, `cosupp_markedTransformSeq_pow`,
`cosupp_markedTransformSeq_subset_iInter` and `ordAlongEq_map_of_cosupp_subset`.

* `setOf_le_ord_pow`: `cosupp(A^s, c s) = cosupp(A, c)` for `s ≥ 1` (property (3) of the cosupport
  in [Kol07, Definition 59]), read on the sets `{x | c ≤ ord_x}` with `ord_pow`.
* `IsOfOrderGe.isOfOrderGe_pow`: a sequence of order `≥ m` for `(I, m)` is of order `≥ m s` for
  `(I^s, m s)`; the marked transforms are the powers (`markedTransformSeq_pow`).
* `IsOfOrderGe.markedTransformSeq_le_of_le`, `setOf_le_ord_markedTransformSeq_subset_of_le`: the
  marked transform along a sequence is monotone in the ideal sheaf (`birationalTransform_mono`
  stage by stage), so its cosupport is antitone (property (1) of the cosupport).
* `setOf_le_ord_markedTransformSeq_pow`: `cosupp Π_*^{-1}(I^s, m s) = cosupp Π_*^{-1}(I, m)` at
  every stage.
* `setOf_le_ord_markedTransformSeq_subset_iInter`: for `I` D-balanced and `T` of order `≥ m` for
  `(I|_S, m)`, `cosupp T_*^{-1}(I|_S, m) ⊆ ⋂_{j<m} cosupp T_*^{-1}((D^j I)|_S, m − j)` at every
  stage: the D-balanced inclusion `(D^j I)^m ⊆ I^{m−j}` pulled back to `S`, the power rule and
  `pow_markedTransformSeq_le` give
  `m · ord T_*^{-1}((D^j I)|_S, m − j) ≥ (m − j) · ord T_*^{-1}(I|_S, m) ≥ (m − j) m`.
* `le_ordAlong_pushforward_center_of_setOf_le_ord_subset`: at a step of `T` whose centre `Z_i` has
  order `≥ m` for `J` and whose points of order `≥ m` for `J` map to points of order `≥ m` for `A`,
  the order of `A` along the pushed-forward centre `j_i(Z_i)` is `≥ m`, since the order along a
  centre at `a` is determined by the orders at the nearby points of the centre
  (`stalkIdeal_le_pow_of_eventually_le_ord`).

Kollár's Lemma 61 iterated and Remark 67 are in
`Hironaka/Resolution/Analytic/GoingUp/MaxOrder.lean`; the induction itself is
`le_ordAlong_pushforward` in `GoingUp/Corollary89.lean`.
-/

public section

noncomputable section

open TopologicalSpace Filter
open scoped Manifold ContDiff Topology

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

section Cosupport

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(𝕜, E) ω M]
  [FiniteDimensional 𝕜 E]

/-- `cosupp(A^s, cs) = cosupp(A, c)` for `s ≥ 1` (property (3) of the cosupport in
[Kol07, Definition 59]): `ord_pow` read on the sets `{x | c ≤ ord_x}`. -/
theorem setOf_le_ord_pow (A : IdealSheaf (structureSheaf 𝕜 E M)) {s : ℕ} (hs : 1 ≤ s) (c : ℕ) :
    {x : M | ((c * s : ℕ) : ℕ∞) ≤ (A ^ s).ord x} = {x | (c : ℕ∞) ≤ A.ord x} := by
  ext x
  change ((c * s : ℕ) : ℕ∞) ≤ (A ^ s).ord x ↔ (c : ℕ∞) ≤ A.ord x
  rw [IdealSheaf.ord_pow A hs x, Nat.cast_mul, mul_comm (c : ℕ∞) (s : ℕ∞)]
  exact ENat.mul_le_mul_left_iff (Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hs))
    (ENat.natCast_ne_top s)

end Cosupport

end Hironaka.Manifold

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} [FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E}

/-! ### Along one sequence -/

section Succession

variable (B : FiniteSuccession M) {I E₀ : IdealSheaf M} {m : ℕ}

omit [FiniteDimensional 𝕜 E] in
/-- A sequence of order `≥ m` for `(I, m)` is of order `≥ m·s` for `(I^s, m·s)` (the order
bookkeeping of the power rule, the second line of Kollár's computation in [Kol07, 90]): the marked
transforms of the power are the powers (`markedTransformSeq_pow`), whose order along the centres
is `s` times the order. -/
theorem IsOfOrderGe.isOfOrderGe_pow (hge : B.IsOfOrderGe I m E₀) (s : ℕ) :
    B.IsOfOrderGe (I ^ s) (m * s) E₀ := fun i =>
  ⟨(hge i).1, fun a ha => by
    rw [hge.markedTransformSeq_pow s i.castSucc, IdealSheaf.le_ordAlongIdeal_iff,
      IdealSheaf.stalkIdeal_pow, pow_mul]
    exact Ideal.pow_right_mono
      ((IdealSheaf.le_ordAlongIdeal_iff _ _ _ _).mp (hge.le_ordAlong i ha)) s⟩

omit [FiniteDimensional 𝕜 E] in
/-- The marked transform along a sequence is monotone in the ideal sheaf, the larger ideal being
of order `≥ c` along the centres: `birationalTransform_mono` stage by stage (the third line of
Kollár's computation in [Kol07, 90]). -/
theorem IsOfOrderGe.markedTransformSeq_le_of_le {A A' : IdealSheaf M} (hAA' : A ≤ A') {c : ℕ}
    (hA' : B.IsOfOrderGe A' c E₀) (i : Fin (B.length + 1)) :
    B.markedTransformSeq A c i ≤ B.markedTransformSeq A' c i := by
  induction i using Fin.induction with
  | zero => exact hAA'
  | succ i ih =>
    rw [markedTransformSeq_succ, markedTransformSeq_succ]
    exact birationalTransform_mono (B.isClosedSubmanifold_center i) (B.isBlowUp_map i) ih
      fun a ha => by rw [B.idealSheaf_center i]; exact hA'.le_ordAlong i ha

omit [FiniteDimensional 𝕜 E] in
/-- The marked transform along a sequence is monotone in the ideal sheaf, so the cosupport is
antitone (property (1) of the cosupport in [Kol07, Definition 59]): `A ≤ A'` gives
`cosupp Π_*^{-1}(A', c) ⊆ cosupp Π_*^{-1}(A, c)` at every stage. -/
theorem setOf_le_ord_markedTransformSeq_subset_of_le {A A' : IdealSheaf M} (hAA' : A ≤ A')
    {c : ℕ} (hA' : B.IsOfOrderGe A' c E₀) (i : Fin (B.length + 1)) :
    {x : B.stage i | (c : ℕ∞) ≤ (B.markedTransformSeq A' c i).ord x} ⊆
      {x | (c : ℕ∞) ≤ (B.markedTransformSeq A c i).ord x} := fun x hx =>
  le_trans hx (IdealSheaf.ord_anti (hA'.markedTransformSeq_le_of_le B hAA' i) x)

/-- Along a sequence of order `≥ m` for `(I, m)`,
`cosupp Π_*^{-1}(I^s, m s) = cosupp Π_*^{-1}(I, m)` at every stage, for `s ≥ 1` (lines 2 and 4 of
Kollár's computation in [Kol07, 90]): `markedTransformSeq_pow` with `setOf_le_ord_pow`. -/
theorem setOf_le_ord_markedTransformSeq_pow (hge : B.IsOfOrderGe I m E₀) {s : ℕ} (hs : 1 ≤ s)
    (i : Fin (B.length + 1)) :
    {x : B.stage i | ((m * s : ℕ) : ℕ∞) ≤ (B.markedTransformSeq (I ^ s) (m * s) i).ord x} =
      {x | (m : ℕ∞) ≤ (B.markedTransformSeq I m i).ord x} := by
  rw [hge.markedTransformSeq_pow s i]
  exact Hironaka.Manifold.setOf_le_ord_pow _ hs m

end Succession

/-! ### The hypersurface side of the induction -/

section Hypersurface

variable {S : Set M} (hS : IsClosedSubmanifold ψ S 1) (T : FiniteSuccession hS.toAnalyticManifold)
  {I E₀ : IdealSheaf M} {m : ℕ}

/-- For `I` D-balanced and `T` a sequence on the hypersurface `S` of order `≥ m` for `(I|_S, m)`,
at every stage `cosupp T_*^{-1}(I|_S, m) ⊆ ⋂_{j<m} cosupp T_*^{-1}((D^j I)|_S, m − j)` (the use of
the D-balanced property in Kollár's computation in [Kol07, 90]): `(D^j I)^m ⊆ I^{m−j}`, pulled back
to `S`, the power rule and `pow_markedTransformSeq_le`
(`(T_*^{-1}((D^j I)|_S, m−j))^m ⊆ T_*^{-1}((I|_S)^{m−j}, m(m−j))`), whence
`m · ord T_*^{-1}((D^j I)|_S, m−j) ≥ (m−j) · ord T_*^{-1}(I|_S, m) ≥ (m−j) m`. -/
theorem setOf_le_ord_markedTransformSeq_subset_iInter (hI : I.IsDBalanced m) {E' : IdealSheaf
    hS.toAnalyticManifold}
    (hT : T.IsOfOrderGe (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) m E')
    (i : Fin (T.length + 1)) :
    {y : T.stage i | (m : ℕ∞) ≤
        (T.markedTransformSeq (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) m i).ord y} ⊆
      ⋂ j, ⋂ (_ : j < m), {y | ((m - j : ℕ) : ℕ∞) ≤ (T.markedTransformSeq
        ((I.iteratedDeriv j).pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) (m - j)
          i).ord y} := by
  intro y hy
  refine Set.mem_iInter₂.mpr fun j hj => ?_
  have hy' : (m : ℕ∞) ≤
      (T.markedTransformSeq (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) m i).ord y :=
    hy
  have hm : 1 ≤ m := by omega
  have hmj : 1 ≤ m - j := by omega
  -- `((D^j I)|_S)^m ⊆ (I|_S)^{m−j}`: the D-balanced inclusion pulled back to `S`
  have hpow : ((I.iteratedDeriv j).pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) ^ m ≤
      (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) ^ (m - j) := by
    rw [← IdealSheaf.pullback_pow, ← IdealSheaf.pullback_pow]
    exact IdealSheaf.pullback_le_pullback _ _ (hI j hj)
  -- `T` is of order `≥ (m−j) m` for `((I|_S)^{m−j}, (m−j) m)`
  have hT' : T.IsOfOrderGe ((I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) ^ (m - j))
      ((m - j) * m) E' := by
    have h := IsOfOrderGe.isOfOrderGe_pow T hT (m - j)
    rwa [mul_comm m (m - j)] at h
  -- the power rule: `(T_*^{-1}((D^j I)|_S, m−j))^m ⊆ T_*^{-1}((I|_S)^{m−j}, (m−j) m) =
  -- (T_*^{-1}(I|_S, m))^{m−j}`
  have hle := hT'.pow_markedTransformSeq_le hm hpow i
  rw [mul_comm (m - j) m, hT.markedTransformSeq_pow (m - j) i] at hle
  have h1 := IdealSheaf.ord_anti hle y
  rw [IdealSheaf.ord_pow _ hmj, IdealSheaf.ord_pow _ hm] at h1
  -- `m (m−j) ≤ (m−j) · ord T_*^{-1}(I|_S, m) ≤ m · ord T_*^{-1}((D^j I)|_S, m−j)`
  have h2 : (m : ℕ∞) * ((m - j : ℕ) : ℕ∞) ≤ (m : ℕ∞) *
      (T.markedTransformSeq ((I.iteratedDeriv j).pullback ⇑hS.inclusionMap
        hS.inclusionMap.contMDiff) (m - j) i).ord y :=
    calc (m : ℕ∞) * ((m - j : ℕ) : ℕ∞) = ((m - j : ℕ) : ℕ∞) * (m : ℕ∞) := mul_comm _ _
      _ ≤ ((m - j : ℕ) : ℕ∞) * (T.markedTransformSeq (I.pullback ⇑hS.inclusionMap
          hS.inclusionMap.contMDiff) m i).ord y := mul_le_mul' le_rfl hy'
      _ ≤ _ := h1
  exact (ENat.mul_le_mul_left_iff (Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hm))
    (ENat.natCast_ne_top m)).mp h2

omit [FiniteDimensional 𝕜 E] in
/-- At a step `i` of `T` with centre `Z_i ⊆ S_i`, if `J` has order `≥ m` along `Z_i` and the points
of `S_i` where `J` has order `≥ m` map to points where `A` has order `≥ m`, then `A` has order
`≥ m` along the pushed-forward centre `j_i(Z_i)` (Kollár's "the last blow-up also has order `≥ m`,
or, equivalently, `cosupp(J_{r−1}, m) ⊆ cosupp(I_{r−1}, m)`" in [Kol07, 90]): the order along a
centre is the order at the points of its component through the point, and every point of
`j_i(Z_i)` is `j_i(y)` with `y ∈ Z_i`, where `m ≤ ord_{Z_i} J ≤ ord_y J`. -/
theorem le_ordAlong_pushforward_center_of_setOf_le_ord_subset (i : Fin T.length)
    {A : IdealSheaf ((T.pushforward hS).stage i.castSucc)} {J : IdealSheaf (T.stage i.castSucc)}
    (hJ : ∀ a ∈ (T.center i).support, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (T.center i) J a)
    (hsub : ∀ y, (m : ℕ∞) ≤ J.ord y → (m : ℕ∞) ≤ A.ord (T.pushforwardIncl hS i.castSucc y)) :
    ∀ a ∈ ((T.pushforward hS).center i).support,
      (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal ((T.pushforward hS).center i) A a := by
  intro a ha
  refine (IdealSheaf.le_ordAlongIdeal_iff _ _ _ _).mpr ?_
  rw [← (T.pushforward hS).idealSheaf_center i]
  refine stalkIdeal_le_pow_of_eventually_le_ord ((T.pushforward hS).isClosedSubmanifold_center i)
    A ha (Eventually.of_forall ?_)
  rintro ⟨b, hb⟩
  rw [T.support_center_pushforward hS i] at hb
  obtain ⟨y, hy, rfl⟩ := hb
  have h1 : (m : ℕ∞) ≤ J.ord y := by
    have h := ordAlong_le_ord (T.isClosedSubmanifold_center i) J hy
    rw [T.idealSheaf_center i] at h
    exact (hJ y hy).trans h
  exact hsub y h1

end Hypersurface

end AnalyticManifold.FiniteSuccession

end
