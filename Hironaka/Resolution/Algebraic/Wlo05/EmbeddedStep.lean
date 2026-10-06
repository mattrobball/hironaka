/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedIsolatedIdeal
public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedState
import Hironaka.Resolution.Algebraic.Kol07.ExceptionalFamilyErasure
import Hironaka.Resolution.Algebraic.Tuning.Transform
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedBridge
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedIsolatedState
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRemaining
import Hironaka.Resolution.Algebraic.Wlo05.MarkedTransformMul
import Hironaka.Scheme.BlowUpSequence.TakeLast
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# One round of the loop

The definition of `BED` (`Hironaka.Resolution.Algebraic.Wlo05.Embedded`) writes a round of the loop
as the run truncated before the absorbing stage `n`, glued to the loop restarted on the isolated
triple (`isolatedTriple T hm C n`, the marked triple induced at the end of the truncation with its
ideal enlarged to the colon by the absorbed components) with the remaining members
(`remainingComponents T hm C n`). Both are read through the truncation `run.take n` at its
`Fin.last`; the facts of the isolation are read at the stage `n` of the run
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedIsolatedState`). This module:

* carries the state of the loop across the cast of the truncation
  (`embeddedStateData_isolatedTriple`): the invariant holds for the isolated triple with the
  remaining members and the protected components `protectedTake` (the previously protected ones
  and the absorbed ones, transported to the end of the truncation);
* derives the end result of a round from the end result of the restarted loop
  (`embeddedEnd_concat_of_isolated`): the marked transform along the glued sequence is the marked
  transform of `I_n = (I_n : I_Γ) · I_Γ` along the restarted loop — the marked transform of the
  isolated ideal times the pull-back of `I_Γ` (`markedTransformSeq_mul_comap_last_of_isOrderGeSeq`);
  the first is the product of the final strict transforms of the remaining members (the end result
  of the restarted loop), the second the product of those of the absorbed members (their ideals
  pull back to their strict transforms, being protected); simple normal crossings and disjointness
  pass through the restarted loop, the protected components and the members mapping into the
  members and protected components of the restarted loop.

The concatenation is that of [Kol07, Definition 29] and the marked transform that of
[Kol07, Definition 60]. The two theorems assume `ClaimKC`, `StratumBlowUp` and
`CentersInNonmonomialSupportOrStratum` (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses`;
the first is false, the other two unproved) and are CONDITIONAL lemmas; the definitions and the cast
lemmas are used unconditionally by `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Remaining`. The
proof of the theorem passes through the loop by CP5 and CP6 instead
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Loop`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.BMO

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

section Step

variable (T : Triple k) (hm : (⟨T, 1⟩ : MarkedTriple k).m = 1)
  (C Γ : Finset T.X.left.IdealSheafData) (h : ∃ n, HasAbsorptionAt ⟨T, 1⟩ hm C n)

open Classical in
/-- The protected components at the isolated triple: the strict transforms, along the truncated
run, of the previously protected components and of the members absorbed at the stage of the
loop. -/
noncomputable def protectedTake :
    Finset ((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).last.IdealSheafData :=
  (Γ ∪ absorbed (⟨T, 1⟩ : MarkedTriple k) hm C h).image fun z =>
    ((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).strictTransformSeq z (Fin.last _)

variable {T hm C Γ h}

open Classical in
/-- The end result of the truncation is the stage `Nat.find h` of the run. -/
theorem last_take_eq_stage :
    ((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).last =
      (bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).stage
        (absorbIndex (⟨T, 1⟩ : MarkedTriple k) hm C h).castSucc :=
  stage_take_last _ (find_lt_length (⟨T, 1⟩ : MarkedTriple k) hm C h).le

open Classical in
/-- The strict transforms along the truncation, heterogeneously, are those at the stage of the
run. -/
theorem strictTransformSeq_take_heq (z : T.X.left.IdealSheafData) :
    HEq (((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).strictTransformSeq z
        (Fin.last _))
      ((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).strictTransformSeq z
        (absorbIndex (⟨T, 1⟩ : MarkedTriple k) hm C h).castSucc) :=
  strictTransformSeq_take_last_heq _ z (find_lt_length (⟨T, 1⟩ : MarkedTriple k) hm C h).le

open Classical in
/-- The ideal of the isolated triple, unfolded: the colon of the marked transform along the
truncation by the reduced ideal of the union of the absorbed strict transforms (the definition,
with the mark `1`). -/
theorem isolatedTriple_I_eq :
    (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).I =
      (((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).markedTransformSeq T.I 1
        (Fin.last _)).colon (IdealSheafData.vanishingIdeal (⨆ c ∈ absorbed (⟨T,
            1⟩ : MarkedTriple k) hm C h,
          (((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).strictTransformSeq c
            (Fin.last _)).support)) :=
  rfl

open Classical in
/-- The boundary of the isolated triple, unfolded: the total transform along the truncation. -/
theorem isolatedTriple_E_eq :
    (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).E =
      ((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).totalTransformSeq T.E
        (Fin.last _) :=
  rfl

open Classical in
/-- The ideal of the isolated triple, heterogeneously, is the isolated marked ideal in index
form. -/
theorem isolatedTriple_I_heq :
    HEq (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).I
      (isolatedMarkedIdeal (⟨T, 1⟩ : MarkedTriple k) hm C h) := by
  rw [isolatedTriple_I_eq]
  exact heq_colon last_take_eq_stage
    (markedTransformSeq_take_last_heq _ T.I 1 (find_lt_length (⟨T, 1⟩ : MarkedTriple k) hm C h).le)
    (heq_vanishingIdeal_biSup_support last_take_eq_stage
      (absorbed (⟨T, 1⟩ : MarkedTriple k) hm C h) fun z => strictTransformSeq_take_heq z)

open Classical in
/-- The boundary of the isolated triple, heterogeneously, is the total transform at the stage of
the run. -/
theorem isolatedTriple_E_heq :
    HEq (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).E
      ((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).totalTransformSeq T.E
        (absorbIndex (⟨T, 1⟩ : MarkedTriple k) hm C h).castSucc) := by
  rw [isolatedTriple_E_eq]
  exact totalTransformSeq_take_last_heq _ T.E (find_lt_length (⟨T, 1⟩ : MarkedTriple k) hm C h).le

open Classical in
/-- **The state of the loop holds for the isolated triple**, the remaining members and the
protected components at the end of the truncation (the isolation passage of the proof of
[Wlo05, Theorem 4.7.1]); conditional on `ClaimKC`, `StratumBlowUp` and
`CentersInNonmonomialSupportOrStratum`. -/
theorem embeddedStateData_isolatedTriple (hKC : ClaimKC k) (hG : StratumBlowUp k)
    (hL : CentersInNonmonomialSupportOrStratum k)
    (hs : EmbeddedStateData T.I T.E C Γ) :
    EmbeddedStateData (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).I
      (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).E
      (remainingComponents (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h))
      (protectedTake T hm C Γ h) :=
  EmbeddedStateData.of_heq last_take_eq_stage isolatedTriple_I_heq isolatedTriple_E_heq
    (heq_finset_image last_take_eq_stage _ fun z => strictTransformSeq_take_heq z)
    (heq_finset_image last_take_eq_stage _ fun z => strictTransformSeq_take_heq z)
    (embeddedStateData_isolated (T := ⟨T, 1⟩) (hm := hm) (C := C) (h := h) hKC hG hL Γ hs)

open Classical in
/-- The strict transform along the truncated run determines the member (the proof of
[Kol07, Corollary 22] on the truncation). -/
theorem eq_of_strictTransformSeq_take_eq (hinv : InvCE T.I T.E C) {c₁ c₂ : T.X.left.IdealSheafData}
    (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C)
    (heq : ((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).strictTransformSeq c₁
        (Fin.last _) =
      ((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).strictTransformSeq c₂
        (Fin.last _)) : c₁ = c₂ :=
  eq_of_strictTransformSeq_eq hinv hc₁ hc₂
    (eq_of_heq_of_heq last_take_eq_stage.symm (strictTransformSeq_take_heq c₁).symm
      (strictTransformSeq_take_heq c₂).symm heq)

open Classical in
/-- A member or protected component maps into the remaining members or the protected components
of the isolated triple. -/
theorem strictTransformSeq_take_mem_union {z : T.X.left.IdealSheafData} (hz : z ∈ C ∪ Γ) :
    ((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).strictTransformSeq z
        (Fin.last _) ∈
      remainingComponents (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h) ∪
        protectedTake T hm C Γ h := by
  rcases Finset.mem_union.mp hz with hzC | hzΓ
  · by_cases habs : CenterContains (bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm) z (Nat.find h)
    · refine Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_union_right _ ?_))
      exact Finset.mem_filter.mpr ⟨hzC, habs⟩
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hzC, habs⟩))
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_union_left _ hzΓ))

open Classical in
/-- **One round of the loop** (the passes of the proof of [Wlo05, Theorem 4.7.1] compose): the end
result of the truncated run glued to a sequence `S'` on the isolated triple, of order `≥ 1` for
the isolated ideal, whose end result satisfies the conclusions of the loop for the remaining
members and the protected components, satisfies the conclusions of the loop for the original
members and protected components. Conditional on `ClaimKC`, `StratumBlowUp` and
`CentersInNonmonomialSupportOrStratum`. -/
theorem embeddedEnd_concat_of_isolated (hKC : ClaimKC k) (hG : StratumBlowUp k)
    (hL : CentersInNonmonomialSupportOrStratum k) (hs : EmbeddedStateData T.I T.E C Γ)
    (S' : BlowUpSequence (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).X.left)
    (hS' : S'.IsOrderGeSeq
      ((isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).X.left ↘ Spec
        (CommRingCat.of k))
      (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).I 1
      (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).E)
    (hend : EmbeddedEnd (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h))
      (remainingComponents (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h))
      (protectedTake T hm C Γ h) S') :
    EmbeddedEnd ⟨T, 1⟩ C Γ
      (((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).concat S') := by
  classical
  have hlN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  obtain ⟨d', hd'⟩ :=
    (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).smoothOfRelativeDimension
  -- the take-form facts
  have hK4 : ((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).markedTransformSeq T.I 1
        (Fin.last _) =
      (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).I *
        (IdealSheafData.vanishingIdeal (⨆ c ∈ absorbed (⟨T, 1⟩ : MarkedTriple k) hm C h,
          (((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).strictTransformSeq c
            (Fin.last _)).support) :
          (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).X.left.IdealSheafData) :=
    eq_of_heq_of_heq last_take_eq_stage
      (markedTransformSeq_take_last_heq _ T.I 1 (find_lt_length
        (⟨T, 1⟩ : MarkedTriple k) hm C h).le)
      (heq_mul last_take_eq_stage isolatedTriple_I_heq
        (heq_vanishingIdeal_biSup_support last_take_eq_stage _ fun z =>
          strictTransformSeq_take_heq z))
      (markedTransformSeq_eq_isolatedMarkedIdeal_mul_absorbedIdeal (T := ⟨T, 1⟩) (hm := hm)
        (C := C) (h := h) hs.invCE hKC)
  have hΓprod : (IdealSheafData.vanishingIdeal (⨆ c ∈ absorbed (⟨T, 1⟩ : MarkedTriple k) hm C h,
          (((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).strictTransformSeq c
            (Fin.last _)).support) :
          (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).X.left.IdealSheafData) =
      (∏ c ∈ absorbed (⟨T, 1⟩ : MarkedTriple k) hm C h,
        ((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).strictTransformSeq c
          (Fin.last _) :
        (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).X.left.IdealSheafData) :=
    eq_of_heq_of_heq last_take_eq_stage
      (heq_vanishingIdeal_biSup_support last_take_eq_stage _ fun z =>
        strictTransformSeq_take_heq z)
      (heq_finset_prod last_take_eq_stage _ fun z => strictTransformSeq_take_heq z)
      (absorbedIdeal_eq_prod (T := ⟨T, 1⟩) (hm := hm) (C := C) (h := h) hs.invCE hKC)
  have hprot : ∀ γ ∈ Γ,
      γ.comap ((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).composite =
        ((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).strictTransformSeq γ
          (Fin.last _) :=
    fun γ hγ => eq_of_heq_of_heq last_take_eq_stage
      (heq_comap last_take_eq_stage
        (composite_take_heq _ (find_lt_length (⟨T, 1⟩ : MarkedTriple k) hm C h).le) γ)
      (strictTransformSeq_take_heq γ)
      (hs.protected_transport_bmoOneRun hG hL hγ _).2.2
  -- across the cast of the concatenation's end result
  unfold EmbeddedEnd
  refine EmbeddedEndData.of_heq (last_concat _ S') (totalTransformSeq_concat_last_heq _ S' T.E)
    (markedTransformSeq_concat_last_heq _ S' T.I 1)
    (heq_pi (last_concat _ S') fun z => strictTransformSeq_concat_last_heq _ S' z)
    (heq_pi (last_concat _ S') fun z => comap_composite_concat_heq _ S' z) ?_
  refine ⟨?_, fun γ hγ => ?_, fun z hz => hend.snc _ (strictTransformSeq_take_mem_union hz), ?_⟩
  · -- the marked transform at the end is the product of the members' strict transforms
    have hprod := markedTransformSeq_mul_comap_last_of_isOrderGeSeq
      ((isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).X.left ↘ Spec (.of k)) d' S'
      (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).I
      (IdealSheafData.vanishingIdeal (⨆ c ∈ absorbed (⟨T, 1⟩ : MarkedTriple k) hm C h,
          (((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).strictTransformSeq c
            (Fin.last _)).support) :
          (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).X.left.IdealSheafData) 1
      (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).E hS'
    rw [hK4]
    refine hprod.trans ?_
    rw [hend.marked_eq, hΓprod]
    have h1 : ((∏ c ∈ absorbed (⟨T, 1⟩ : MarkedTriple k) hm C h,
          ((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).strictTransformSeq c
            (Fin.last _) :
          (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).X.left.IdealSheafData)).comap
          (S'.stageMap (Fin.last _)) =
        ∏ c ∈ absorbed (⟨T, 1⟩ : MarkedTriple k) hm C h,
          S'.strictTransformSeq (((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take
            (Nat.find h)).strictTransformSeq c (Fin.last _)) (Fin.last _) :=
      (IdealSheafData.comap_finset_prod _ (fun c => ((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take
        (Nat.find h)).strictTransformSeq c (Fin.last _)) (S'.stageMap (Fin.last _))).trans
        (Finset.prod_congr rfl fun c hc =>
          hend.comap_eq _ (Finset.mem_image_of_mem _ (Finset.mem_union_right _ hc)))
    have h2 : ∏ c' ∈ remainingComponents (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h),
        S'.strictTransformSeq c' (Fin.last _) =
        ∏ c ∈ C.filter (fun c => ¬ CenterContains (bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm) c
          (Nat.find h)),
          S'.strictTransformSeq (((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take
            (Nat.find h)).strictTransformSeq c (Fin.last _)) (Fin.last _) :=
      Finset.prod_image fun c₁ hc₁ c₂ hc₂ heq =>
        eq_of_strictTransformSeq_take_eq hs.invCE (Finset.mem_filter.mp hc₁).1
          (Finset.mem_filter.mp hc₂).1 heq
    rw [h1, h2, mul_comm]
    exact Finset.prod_filter_mul_prod_filter_not C _ _
  · -- the protected components pull back to their strict transforms
    exact (congrArg (fun J => Scheme.IdealSheafData.comap J S'.composite) (hprot γ hγ)).trans
      (hend.comap_eq _ (Finset.mem_image_of_mem _ (Finset.mem_union_left _ hγ)))
  · -- pairwise disjointness at the end
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    by_cases hg : ((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).strictTransformSeq a
        (Fin.last _) =
        ((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).strictTransformSeq b
          (Fin.last _)
    · have hd : Disjoint
          (((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).strictTransformSeq a
            (Fin.last _)).support
          (((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).strictTransformSeq b
            (Fin.last _)).support := by
        rcases Finset.mem_union.mp ha with haC | haΓ <;>
          rcases Finset.mem_union.mp hb with hbC | hbΓ
        · exact absurd (eq_of_strictTransformSeq_take_eq hs.invCE haC hbC hg) hab
        · exact disjoint_strictTransformSeq_support_of_disjoint _ a b
            (hs.disjointCΓ a haC b hbΓ) _
        · exact disjoint_strictTransformSeq_support_of_disjoint _ a b
            (hs.disjointCΓ b hbC a haΓ).symm _
        · exact disjoint_strictTransformSeq_support_of_disjoint _ a b
            (hs.pairwise (Finset.mem_coe.mpr haΓ) (Finset.mem_coe.mpr hbΓ) hab) _
      rw [hg] at hd
      have htop : ((bmoOneRun (⟨T, 1⟩ : MarkedTriple k) hm).take (Nat.find h)).strictTransformSeq b
          (Fin.last _) = ⊤ := by
        have hb' := disjoint_self.mp hd
        rwa [IdealSheafData.support_eq_bot_iff] at hb'
      change Disjoint (S'.strictTransformSeq _ (Fin.last _)).support
        (S'.strictTransformSeq _ (Fin.last _)).support
      rw [hg, htop]
      change Disjoint (S'.strictTransformSeq
          (⊤ : (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).X.left.IdealSheafData)
          (Fin.last _)).support
        (S'.strictTransformSeq
          (⊤ : (isolatedTriple (⟨T, 1⟩ : MarkedTriple k) hm C (Nat.find h)).X.left.IdealSheafData)
          (Fin.last _)).support
      rw [strictTransformSeq_top, IdealSheafData.support_top]
      exact disjoint_bot_left
    · exact hend.pairwise (Finset.mem_coe.mpr (strictTransformSeq_take_mem_union ha))
        (Finset.mem_coe.mpr (strictTransformSeq_take_mem_union hb)) hg

end Step

end Hironaka.Resolution
