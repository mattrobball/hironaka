/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.Embedded
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineEndResult
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Snc.RestrictSubscheme
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedGenericLift
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# At the first containing stage the centre is the strict transform near it

Włodarczyk runs the algorithm until "the strict transform of one of the components `Yᵢ` is the
center" ([Wlo05, Theorem 4.7.1, proof]). For the loop `BED`
(`Hironaka.Resolution.Algebraic.Wlo05.Embedded`) this is made precise as follows: at the FIRST stage
`j` of a smooth blow-up sequence of order `≥ m ≥ 1` whose centre `Z_j` contains the strict transform
`c̃_j` of a component `c = V(closure {η})` of `V(I)` (with `η` off the boundary and `I = c` at `η`),
the centre coincides with `c̃_j` at every point of `c̃_j`: `(Z_j)_p = (c̃_j)_p` for all `p ∈ c̃_j`.
So the absorbing centre is `c̃_j` on a neighbourhood of `c̃_j`, and no other component of `Z_j`
meets it.

The proof is the argument of the proof of [Kol07, Corollary 22] in the general form
`isOpenImmersion_inclusion_of_isGenericPoint` of
`Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification`: the lifted generic point `η'` of `c̃_j`
(`GenericLift`, `exists_genericLift`, `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedGenericLift`) is
a generic point of `V(I_j)`; the centre lies in `V(I_j)` (the order condition,
`IsOrderGeSeq.leOrdAlong`), so `η'` is a maximal point of `Z_j`; `c̃_j` is integral and `Z_j` is
regular (smooth over `k`, `isRegular_of_smooth`), hence `V(c̃_j) ⟶ V(Z_j)` is an open immersion and
the stalk ideals agree along `c̃_j` (`stalkIdeal_eq_of_isOpenImmersion_inclusion`,
`Hironaka.Resolution.Algebraic.Snc.RestrictSubscheme`). Nothing here uses the hypothesis `ClaimKC`
of `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses`, which is false for the transcribed
order; `stalkIdeal_center_eq_of_absorbed` of `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedAbsorbed`
is the conditional form of the same statement. This observation is not in the literature. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP2Entry`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}

/-- Along a smooth blow-up sequence of order `≥ m ≥ 1` for `(I, m, E)` on a Noetherian `X`, at a
stage `j` whose centre contains the strict transform of `c = vanishingIdeal (closure {η})` (`η` a
generic point of `V(I)` off the boundary at which `I = c`) while no earlier centre does, the centre
and the strict transform have the same stalk ideal at every point of the strict transform (the
argument of the proof of [Kol07, Corollary 22]). -/
theorem stalkIdeal_center_eq_strictTransformSeq_of_first [IsNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    {S : BlowUpSequence X} {I : X.IdealSheafData} {E : DivisorFamily X} {m : ℕ}
    (hS : S.IsOrderGeSeq f I m E) (hm : 1 ≤ m) {η : X} (hη : η ∈ I.support.genericPoints)
    (hηE : ∀ i, η ∉ (E.component i).support)
    (hIc : I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η)
    (j : Fin S.length)
    (hle : S.center j ≤ S.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
        {η})) j.castSucc)
    (hmin : ∀ l < j.val, ¬ CenterContains S (IdealSheafData.vanishingIdeal (Closeds.closure
        {η})) l) :
    ∀ p ∈ (S.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
        {η})) j.castSucc).support,
      (S.center j).stalkIdeal p =
        (S.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
            {η})) j.castSucc).stalkIdeal p := by
  intro p hp
  obtain ⟨η', hl⟩ := exists_genericLift S I E m hη hηE hIc j.castSucc hmin
  have hse := hl.strict_eq
  have hint : IsIntegral (S.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η}))
      j.castSucc).subscheme := by
    rw [hse]
    exact isIntegral_subscheme_vanishingIdeal_closure η'
  have hgen : IsGenericPoint η' ((S.strictTransformSeq (IdealSheafData.vanishingIdeal
      (Closeds.closure {η}))
      j.castSucc).support : Set (S.stage j.castSucc)) := by
    rw [hse]
    exact Hironaka.BMO.isGenericPoint_support_vanishingIdeal_closure η'
  have hsm : SmoothOfRelativeDimension n (S.stageMap j.castSucc ≫ f) :=
    IsSmooth.smoothOfRelativeDimension_stageMap hS.1 j.castSucc
  have hmax : η' ∈ (S.center j).support.genericPoints := by
    refine ⟨IdealSheafData.support_antitone hle hgen.mem, ?_⟩
    intro ξ hξ hspec
    have h1 : (m : ℕ∞) ≤ (S.markedTransformSeq I m j.castSucc).ord ξ :=
      (IdealSheafData.leOrdAlong_iff_forall_mem _ (S.stageMap j.castSucc ≫ f) n _ _).1
        (IsOrderGeSeq.leOrdAlong hS j) ξ hξ
    have h2 : ξ ∈ (S.markedTransformSeq I m j.castSucc).support :=
      (IdealSheafData.one_le_ord_iff _ ξ).1 (le_trans (by exact_mod_cast hm) h1)
    exact hl.mem_genericPoints.2 h2 hspec
  have hsmZ : Smooth ((S.center j).subschemeι ≫ S.stageMap j.castSucc ≫ f) := hS.1 j
  have hZ : IsRegular (S.center j).subscheme :=
    isRegular_of_smooth ((S.center j).subschemeι ≫ S.stageMap j.castSucc ≫ f)
  have : IsNoetherian (S.stage j.castSucc) := isNoetherian_stage S j.castSucc
  have : IsOpenImmersion (IdealSheafData.inclusion hle) :=
    isOpenImmersion_inclusion_of_isGenericPoint (S.center j) _ hle hZ hgen hmax
  exact Hironaka.Snc.stalkIdeal_eq_of_isOpenImmersion_inclusion hle hp

/-- The identity of the centre and the strict transform for one run of `BMO_1` (`bmoOneRun`, the
round of the loop): the first centre containing the strict transform of a member
`c = vanishingIdeal (closure {η})` agrees with it stalkwise along it. -/
theorem stalkIdeal_center_eq_strictTransformSeq_bmoOneRun (T : MarkedTriple k) (hm : T.m = 1)
    {η : T.X.left} (hη : η ∈ T.I.support.genericPoints) (hηE : ∀ i, η ∉ (T.E.component i).support)
    (hIc : T.I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η)
    (j : Fin (bmoOneRun T hm).length)
    (hle : (bmoOneRun T hm).center j ≤
      (bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
          {η})) j.castSucc)
    (hmin : ∀ l < j.val,
      ¬ CenterContains (bmoOneRun T hm) (IdealSheafData.vanishingIdeal (Closeds.closure {η})) l) :
    ∀ p ∈ ((bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η}))
        j.castSucc).support,
      ((bmoOneRun T hm).center j).stalkIdeal p =
        ((bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η}))
          j.castSucc).stalkIdeal p := by
  have : IsNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isNoetherian_of_field
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  exact stalkIdeal_center_eq_strictTransformSeq_of_first (T.X.left ↘ Spec (.of k)) n
    (isOrderGeSeq_bmoOneRun T hm) (by rw [hm]) hη hηE hIc j hle hmin

open Classical in
/-- The identity at the truncation index of the loop (the `Nat.find` of `bedAux`, the first stage
with an absorption): a member `c = vanishingIdeal (closure {η})` of `C` absorbed there is the centre
near its strict transform, since no earlier stage absorbs any member, so none contains `c̃`. -/
theorem stalkIdeal_center_eq_strictTransformSeq_find (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) (h : ∃ n, HasAbsorptionAt T hm C n) {η : T.X.left}
    (hη : η ∈ T.I.support.genericPoints) (hηE : ∀ i, η ∉ (T.E.component i).support)
    (hIc : T.I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η)
    (hcC : IdealSheafData.vanishingIdeal (Closeds.closure {η}) ∈ C)
    (hcc : CenterContains (bmoOneRun T hm) (IdealSheafData.vanishingIdeal (Closeds.closure {η}))
        (Nat.find h)) :
    ∀ p ∈ ((bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η}))
        ⟨Nat.find h, Nat.lt_succ_of_lt hcc.1⟩).support,
      ((bmoOneRun T hm).center ⟨Nat.find h, hcc.1⟩).stalkIdeal p =
        ((bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η}))
          ⟨Nat.find h, Nat.lt_succ_of_lt hcc.1⟩).stalkIdeal p := by
  obtain ⟨hlt, hle⟩ := hcc
  exact stalkIdeal_center_eq_strictTransformSeq_bmoOneRun T hm hη hηE hIc ⟨Nat.find h, hlt⟩ hle
    fun l hl hcl => Nat.find_min h hl ⟨_, hcC, hcl⟩

end Hironaka.Resolution
