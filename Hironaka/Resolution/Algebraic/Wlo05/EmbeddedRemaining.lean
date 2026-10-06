/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedIsolatedIdeal
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Kol07.OffCenters
import Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenter
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedAbsorbed
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedDisjoint
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Resolution.Algebraic.Wlo05.FirstCenterLocalIso
import Hironaka.Resolution.Algebraic.Wlo05.OffCentreTransport
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.FlatColon
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The remaining members after an isolation

In the isolation passage of the proof of [Wlo05, Theorem 4.7.1], after the isolation the modified
run restarts on `(X_n, I_n : I_Γ, E_n)` with the remaining components. This module shows that the
invariant `InvCE` of the loop (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses`) holds again
for the strict transforms of the members not absorbed at the absorbing stage: each has a generic
point `η'` over the member's generic point (the proof of [Kol07, Corollary 22]: the blow-ups are
local isomorphisms at the generic point before the first containing centre), lying on no member of
the boundary, off the absorbed strict transforms, so that the colon by `I_Γ` changes nothing at `η'`
and the isolated ideal agrees there with the strict transform, which is the reduced ideal of the
closure of `η'`; and `η'` is a generic point of the support of the isolated ideal. The remaining
strict transforms are disjoint from the absorbed ones.

The disjointness from the absorbed strict transforms is a hypothesis of the general form
`exists_genericPoint_isolatedMarkedIdeal_of_not_absorbed_of_disjoint`, discharged here from
`ClaimKC` (a CONDITIONAL lemma, since `ClaimKC` is false) and unconditionally from CP1 in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Remaining`. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedIsolatedState`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Remaining`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP2Entry` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Absorbed`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.BMO

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

section Remaining

variable {T : MarkedTriple k} {hm : T.m = 1} {C : Finset T.X.left.IdealSheafData}
  {h : ∃ n, HasAbsorptionAt T hm C n}

/-- The data of a member not absorbed at the stage of the loop: the invariant of the loop gives its
generic point `η`, off the boundary, at which `T.I` agrees with it; the stop rule gives no
absorption before the stage of the loop. -/
theorem remaining_spec (hinv : InvCE T.I T.E C) {c : T.X.left.IdealSheafData} (hc : c ∈ C) :
    ∃ η : T.X.left, η ∈ T.I.support.genericPoints ∧ c = Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure {η}) ∧
      (∀ i, η ∉ (T.E.component i).support) ∧
      T.I.stalkIdeal η = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η ∧
      ∀ m < (absorbIndex T hm C h).val,
        ¬ CenterContains (bmoOneRun T hm) (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
            {η})) m := by
  obtain ⟨η, hη, rfl, hηE, hIc⟩ := hinv.mem c hc
  exact ⟨η, hη, rfl, hηE, hIc, fun m hm' => not_centerContains_of_lt_find T hm C h hc hm'⟩

open Classical in
/-- A member not absorbed at the stage of the loop has its strict transform disjoint from every
absorbed one (the disjointness of [Wlo05, Theorem 4.7.1] for the loop; conditional on
`ClaimKC`). -/
theorem disjoint_strictTransformSeq_of_not_absorbed (hinv : InvCE T.I T.E C) (hKC : ClaimKC k)
    {c' : T.X.left.IdealSheafData} (hc' : c' ∈ C)
    (hnot : ¬ CenterContains (bmoOneRun T hm) c' (Nat.find h)) {c : T.X.left.IdealSheafData}
    (hc : c ∈ absorbed T hm C h) :
    Disjoint ((bmoOneRun T hm).strictTransformSeq c' (absorbIndex T hm C h).castSucc).support
      ((bmoOneRun T hm).strictTransformSeq c (absorbIndex T hm C h).castSucc).support := by
  obtain ⟨η', hη', rfl, hηE', hIc', hfirst'⟩ := remaining_spec hinv hc'
  obtain ⟨η, hη, rfl, hηE, hIc, habs, hfirst⟩ := absorbed_spec hinv hc
  refine disjoint_closeds_iff.mpr fun p hp' hp => hnot ?_
  have heq := eq_of_mem_strictTransformSeq_support_of_absorbed T hm hη hηE hIc hη' hηE' hIc'
    (absorbIndex T hm C h) habs hfirst hfirst' hKC hp hp'
  rw [← heq]
  exact habs

open Classical in
/-- **The invariant is restored for a remaining member**, with the disjointness from the absorbed
strict transforms as a hypothesis (the proof of [Kol07, Corollary 22]): the strict transform of a
member not absorbed at the stage of the loop is the reduced ideal of the closure of a generic
point `η'` of the support of the isolated ideal, lying on no member of the boundary, at which the
isolated ideal agrees with it. -/
theorem exists_genericPoint_isolatedMarkedIdeal_of_not_absorbed_of_disjoint
    (hinv : InvCE T.I T.E C) {c' : T.X.left.IdealSheafData} (hc' : c' ∈ C)
    (hnot : ¬ CenterContains (bmoOneRun T hm) c' (Nat.find h))
    (hdisj : ∀ c ∈ absorbed T hm C h,
      Disjoint ((bmoOneRun T hm).strictTransformSeq c' (absorbIndex T hm C h).castSucc).support
        ((bmoOneRun T hm).strictTransformSeq c (absorbIndex T hm C h).castSucc).support) :
    ∃ η' : (bmoOneRun T hm).stage (absorbIndex T hm C h).castSucc,
      η' ∈ (isolatedMarkedIdeal T hm C h).support.genericPoints ∧
      (bmoOneRun T hm).strictTransformSeq c' (absorbIndex T hm C h).castSucc =
        Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η'}) ∧
      (∀ i, η' ∉ (((bmoOneRun T hm).totalTransformSeq T.E (absorbIndex T hm C h).castSucc).component
        i).support) ∧
      (isolatedMarkedIdeal T hm C h).stalkIdeal η' =
        ((bmoOneRun T hm).strictTransformSeq c' (absorbIndex T hm C h).castSucc).stalkIdeal η' := by
  have hrun := isOrderGeSeq_bmoOneRun T hm
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hlN : IsLocallyNoetherian ((bmoOneRun T hm).stage (absorbIndex T hm C h).castSucc) :=
    ((T.induced (bmoOneRun T hm) hrun (absorbIndex T hm C h).castSucc).X.left ↘
      Spec (.of k)).isLocallyNoetherian_of_field
  obtain ⟨η, hη, rfl, hηE, hIc, hfirst⟩ := remaining_spec hinv hc'
  obtain ⟨η', hgen, hmap, huniq, havoid, -, hηE'⟩ :=
    exists_genericPoint_strictTransformSeq_of_absorbed T hm hηE (absorbIndex T hm C h) hfirst
  -- the marked ideal and the strict transform agree at `η'` (local isomorphism, `I = c` at `η`)
  have hIc' : T.I.stalkIdeal ((bmoOneRun T hm).stageMap (absorbIndex T hm C h).castSucc η') =
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal
        ((bmoOneRun T hm).stageMap (absorbIndex T hm C h).castSucc η') := by
    rw [hmap]
    exact hIc
  have hIN : ((bmoOneRun T hm).markedTransformSeq T.I 1 (absorbIndex T hm C h).castSucc).stalkIdeal
      η' = ((bmoOneRun T hm).strictTransformSeq (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure {η}))
        (absorbIndex T hm C h).castSucc).stalkIdeal η' := by
    rw [stalkIdeal_markedTransformSeq_of_forall_notMem _ _ _ _ _ havoid,
      stalkIdeal_strictTransformSeq_of_forall_notMem _ _ _ _ havoid, hIc']
  -- `η'` lies on no absorbed strict transform
  have hΓ : η' ∉ (absorbedIdeal T hm C h).support := by
    rw [absorbedIdeal, support_vanishingIdeal_eq, mem_biSup_closeds_iff]
    rintro ⟨c, hc, hη'c⟩
    exact notMem_of_disjoint_closeds (hdisj c hc) hgen.mem hη'c
  have hI' : (isolatedMarkedIdeal T hm C h).stalkIdeal η' =
      ((bmoOneRun T hm).markedTransformSeq T.I 1
        (absorbIndex T hm C h).castSucc).stalkIdeal η' := by
    rw [isolatedMarkedIdeal, Scheme.IdealSheafData.stalkIdeal_colon_of_isLocallyNoetherian,
      Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support _ hΓ, Submodule.top_coe,
          Submodule.colon_univ]
  -- `η'` is a generic point of the isolated ideal's support
  have hgenN := mem_genericPoints_markedTransformSeq_support_of_forall_notMem (bmoOneRun T hm) T.I
    _ 1 (Hironaka.BMO.isGenericPoint_support_vanishingIdeal_closure η) hη hIc
    (absorbIndex T hm C h).castSucc hmap huniq havoid
  have hmem : η' ∈ (isolatedMarkedIdeal T hm C h).support := by
    rw [Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal, hI', hIN]
    exact (Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp hgen.mem
  refine ⟨η', ⟨hmem, fun y hy hsp => hgenN.2 (Scheme.IdealSheafData.support_antitone
      (Scheme.IdealSheafData.le_colon_self _ _) hy) hsp⟩, ?_,
    hηE', by rw [hI', hIN]⟩
  -- the strict transform is integral with generic point `η'`
  have := isIntegral_subscheme_vanishingIdeal_closure η
  have := isIntegral_strictTransformSeq_of_le_firstCenterIndex (bmoOneRun T hm)
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})) (absorbIndex T hm C h).castSucc
    (val_le_firstCenterIndex_of_absorbed T hm (absorbIndex T hm C h) hfirst)
  rw [← radical_eq_self_of_isReduced_subscheme ((bmoOneRun T hm).strictTransformSeq
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})) (absorbIndex T hm C h).castSucc),
    ← Scheme.IdealSheafData.vanishingIdeal_support]
  congr 1
  apply Closeds.ext
  rw [Closeds.coe_closure]
  exact hgen.def.symm

open Classical in
/-- **The invariant is restored for a remaining member** (the proof of [Kol07, Corollary 22];
conditional on `ClaimKC`, which supplies the disjointness): the strict transform of a member not
absorbed at the stage of the loop is the reduced ideal of the closure of a generic point `η'` of
the support of the isolated ideal, lying on no member of the boundary, at which the isolated ideal
agrees with it. -/
theorem exists_genericPoint_isolatedMarkedIdeal_of_not_absorbed (hinv : InvCE T.I T.E C)
    (hKC : ClaimKC k) {c' : T.X.left.IdealSheafData} (hc' : c' ∈ C)
    (hnot : ¬ CenterContains (bmoOneRun T hm) c' (Nat.find h)) :
    ∃ η' : (bmoOneRun T hm).stage (absorbIndex T hm C h).castSucc,
      η' ∈ (isolatedMarkedIdeal T hm C h).support.genericPoints ∧
      (bmoOneRun T hm).strictTransformSeq c' (absorbIndex T hm C h).castSucc =
        Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η'}) ∧
      (∀ i, η' ∉ (((bmoOneRun T hm).totalTransformSeq T.E (absorbIndex T hm C h).castSucc).component
        i).support) ∧
      (isolatedMarkedIdeal T hm C h).stalkIdeal η' =
        ((bmoOneRun T hm).strictTransformSeq c' (absorbIndex T hm C h).castSucc).stalkIdeal η' :=
  exists_genericPoint_isolatedMarkedIdeal_of_not_absorbed_of_disjoint hinv hc' hnot
    fun _ hc => disjoint_strictTransformSeq_of_not_absorbed hinv hKC hc' hnot hc

/-- The strict transform at the stage of the loop determines the member (the proof of
[Kol07, Corollary 22]): two members with the same strict transform have the same generic point,
the unique point over it being the generic point of the strict transform. -/
theorem eq_of_strictTransformSeq_eq (hinv : InvCE T.I T.E C) {c₁ c₂ : T.X.left.IdealSheafData}
    (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C)
    (heq : (bmoOneRun T hm).strictTransformSeq c₁ (absorbIndex T hm C h).castSucc =
      (bmoOneRun T hm).strictTransformSeq c₂ (absorbIndex T hm C h).castSucc) : c₁ = c₂ := by
  obtain ⟨η₁, -, rfl, hηE₁, -, hfirst₁⟩ := remaining_spec hinv hc₁
  obtain ⟨η₂, -, rfl, hηE₂, -, hfirst₂⟩ := remaining_spec hinv hc₂
  obtain ⟨η₁', hgen₁, hmap₁, -, -, -, -⟩ :=
    exists_genericPoint_strictTransformSeq_of_absorbed T hm hηE₁ (absorbIndex T hm C h) hfirst₁
  obtain ⟨η₂', hgen₂, hmap₂, -, -, -, -⟩ :=
    exists_genericPoint_strictTransformSeq_of_absorbed T hm hηE₂ (absorbIndex T hm C h) hfirst₂
  rw [heq] at hgen₁
  have hη' : η₁' = η₂' :=
    ((hgen₁.specializes hgen₂.mem).antisymm (hgen₂.specializes hgen₁.mem)).eq
  rw [← hmap₁, ← hmap₂, hη']

end Remaining

end Hironaka.Resolution
