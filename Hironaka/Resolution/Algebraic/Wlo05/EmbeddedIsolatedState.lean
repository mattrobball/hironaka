/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedState
public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedIsolatedIdeal
import Hironaka.Resolution.Algebraic.Kol07.StrictTransformSupport
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedAbsorbed
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNotContained
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRemaining
import Hironaka.Resolution.Algebraic.Wlo05.OffCentreTransport
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The state of the loop after an isolation, in index form

In the isolation passage of the proof of [Wlo05, Theorem 4.7.1], after the isolation the loop
restarts on `(X_n, I_n : I_Γ, E_n)` with the remaining components, the absorbed ones "ignored".
This module shows that the state of the loop (`EmbeddedStateData`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedState`) is restored at the absorbing stage, read in the
index form of the stages of the run: the strict transforms of the remaining members satisfy the
invariant (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRemaining`); the absorbed strict transforms
join the protected components — with simple normal crossings, contained in no member
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNotContained`), pairwise disjoint, disjoint from the
remaining members, and with the nonmonomial part of the isolated ideal trivial along them
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedIsolatedIdeal`); the previously protected components
are carried by the protected transport along the run
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedProtected`), their disjointness by the preimage of
supports, and the triviality of the nonmonomial part along them by the monotonicity of the
nonmonomial support along the run (the hypothesis `CentersInNonmonomialSupportOrStratum`) and at the
isolation (`nonmonomialPart_le_nonmonomialPart_isolatedMarkedIdeal`).

The theorem `embeddedStateData_isolated` assumes `ClaimKC`, `StratumBlowUp` and
`CentersInNonmonomialSupportOrStratum` (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses`;
the first is false, the other two unproved) and is a CONDITIONAL lemma, used only by the conditional
loop (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedStep`); the proof of the theorem uses CP5 instead
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP5`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.BMO

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

section IsolatedState

variable (T : MarkedTriple k) (hm : T.m = 1) (C : Finset T.X.left.IdealSheafData)
  (h : ∃ n, HasAbsorptionAt T hm C n)

open Classical in
/-- The remaining members at the absorbing stage, in index form: the strict transforms of the
members not absorbed there (`remainingComponents` of `Hironaka.Resolution.Algebraic.Wlo05.Embedded`,
read at the stage of the run). -/
noncomputable def remainingIdx :
    Finset ((bmoOneRun T hm).stage (absorbIndex T hm C h).castSucc).IdealSheafData :=
  (C.filter fun c => ¬ CenterContains (bmoOneRun T hm) c (Nat.find h)).image fun c =>
    (bmoOneRun T hm).strictTransformSeq c (absorbIndex T hm C h).castSucc

open Classical in
/-- The protected components at the absorbing stage, in index form: the strict transforms of the
previously protected components and of the members absorbed there. -/
noncomputable def protectedIdx (Γ : Finset T.X.left.IdealSheafData) :
    Finset ((bmoOneRun T hm).stage (absorbIndex T hm C h).castSucc).IdealSheafData :=
  (Γ ∪ absorbed T hm C h).image fun z =>
    (bmoOneRun T hm).strictTransformSeq z (absorbIndex T hm C h).castSucc

variable {T hm C h}

/-- **The state of the loop is restored at the isolation**, in index form (the isolation passage
of the proof of [Wlo05, Theorem 4.7.1]); conditional on `ClaimKC`, `StratumBlowUp` and
`CentersInNonmonomialSupportOrStratum`. -/
theorem embeddedStateData_isolated (hKC : ClaimKC k) (hG : StratumBlowUp k)
    (hL : CentersInNonmonomialSupportOrStratum k) (Γ : Finset T.X.left.IdealSheafData)
    (hs : EmbeddedStateData T.I T.E C Γ) :
    EmbeddedStateData (isolatedMarkedIdeal T hm C h)
      ((bmoOneRun T hm).totalTransformSeq T.E (absorbIndex T hm C h).castSucc)
      (remainingIdx T hm C h) (protectedIdx T hm C h Γ) := by
  classical
  have hrun := isOrderGeSeq_bmoOneRun T hm
  obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hprot : ∀ γ ∈ Γ,
      ((bmoOneRun T hm).totalTransformSeq T.E (absorbIndex T hm C h).castSucc).HasSncWith
          ((bmoOneRun T hm).strictTransformSeq γ (absorbIndex T hm C h).castSucc) ∧
        NotContainedInMembers
          ((bmoOneRun T hm).totalTransformSeq T.E (absorbIndex T hm C h).castSucc)
          ((bmoOneRun T hm).strictTransformSeq γ (absorbIndex T hm C h).castSucc) ∧
        γ.comap ((bmoOneRun T hm).stageMap (absorbIndex T hm C h).castSucc) =
          (bmoOneRun T hm).strictTransformSeq γ (absorbIndex T hm C h).castSucc := fun γ hγ =>
    protected_transport hG (bmoOneRun T hm) (T.X.left ↘ Spec (.of k)) T.E γ
      (fun i => IsSmooth.smooth_stageMap (n := d) hrun.1 i) T.isSnc (fun i => (hrun.2 i).1)
      (missesOrStratum_bmoOneRun hL T hm (hs.nonmonomial γ hγ)) (hs.snc γ hγ)
      (hs.notContained γ hγ) (absorbIndex T hm C h).castSucc
  refine ⟨⟨fun c'' hc'' => ?_⟩, fun z hz => ?_, fun z hz => ?_, ?_, fun c'' hc'' z hz => ?_,
    fun z hz => ?_⟩
  · -- the invariant for the remaining members
    rw [remainingIdx, Finset.mem_image] at hc''
    obtain ⟨c', hc', rfl⟩ := hc''
    rw [Finset.mem_filter] at hc'
    obtain ⟨η', hgen, heq, hηE', hst⟩ :=
      exists_genericPoint_isolatedMarkedIdeal_of_not_absorbed hs.invCE hKC hc'.1 hc'.2
    exact ⟨η', hgen, heq, hηE', hst⟩
  · -- simple normal crossings for the protected components
    rw [protectedIdx, Finset.mem_image] at hz
    obtain ⟨γ, hγ, rfl⟩ := hz
    rcases Finset.mem_union.mp hγ with hγΓ | hγA
    · exact (hprot γ hγΓ).1
    · obtain ⟨η, hη, rfl, hηE, hIc, habs, hfirst⟩ := absorbed_spec hs.invCE hγA
      exact hasSncWith_strictTransformSeq_of_absorbed T hm hη hηE hIc (absorbIndex T hm C h) habs
        hfirst hKC
  · -- contained in no member
    rw [protectedIdx, Finset.mem_image] at hz
    obtain ⟨γ, hγ, rfl⟩ := hz
    rcases Finset.mem_union.mp hγ with hγΓ | hγA
    · exact (hprot γ hγΓ).2.1
    · obtain ⟨η, -, rfl, hηE, -, -, hfirst⟩ := absorbed_spec hs.invCE hγA
      exact notContainedInMembers_strictTransformSeq_of_absorbed T hm hηE (absorbIndex T hm C h)
        hfirst
  · -- the protected components are pairwise disjoint
    intro a ha b hb hab
    rw [Finset.mem_coe, protectedIdx, Finset.mem_image] at ha hb
    obtain ⟨γ₁, hγ₁, rfl⟩ := ha
    obtain ⟨γ₂, hγ₂, rfl⟩ := hb
    have hne : γ₁ ≠ γ₂ := fun heq => hab (heq ▸ rfl)
    rcases Finset.mem_union.mp hγ₁ with h₁ | h₁ <;> rcases Finset.mem_union.mp hγ₂ with h₂ | h₂
    · exact disjoint_strictTransformSeq_support_of_disjoint _ γ₁ γ₂ (hs.pairwise h₁ h₂ hne) _
    · exact disjoint_strictTransformSeq_support_of_disjoint _ γ₁ γ₂
        (hs.disjointCΓ γ₂ (absorbed_subset h₂) γ₁ h₁).symm _
    · exact disjoint_strictTransformSeq_support_of_disjoint _ γ₁ γ₂
        (hs.disjointCΓ γ₁ (absorbed_subset h₁) γ₂ h₂) _
    · exact pairwise_disjoint_strictTransformSeq_absorbed hs.invCE hKC (Finset.mem_coe.mpr h₁)
        (Finset.mem_coe.mpr h₂) hne
  · -- the remaining members miss the protected components
    rw [remainingIdx, Finset.mem_image] at hc''
    obtain ⟨c', hc', rfl⟩ := hc''
    rw [Finset.mem_filter] at hc'
    rw [protectedIdx, Finset.mem_image] at hz
    obtain ⟨γ, hγ, rfl⟩ := hz
    rcases Finset.mem_union.mp hγ with hγΓ | hγA
    · exact disjoint_strictTransformSeq_support_of_disjoint _ c' γ
        (hs.disjointCΓ c' hc'.1 γ hγΓ) _
    · exact disjoint_strictTransformSeq_of_not_absorbed hs.invCE hKC hc'.1 hc'.2 hγA
  · -- the nonmonomial part of the isolated ideal is trivial along the protected components
    rw [protectedIdx, Finset.mem_image] at hz
    obtain ⟨γ, hγ, rfl⟩ := hz
    rcases Finset.mem_union.mp hγ with hγΓ | hγA
    · refine disjoint_closeds_iff.mpr fun p hpN hpγ => ?_
      have hpN' := Scheme.IdealSheafData.support_antitone
          (nonmonomialPart_le_nonmonomialPart_isolatedMarkedIdeal
        hs.invCE hKC) hpN
      exact notMem_of_disjoint_closeds (hs.nonmonomial γ hγΓ)
        ((hL T hm).2 (absorbIndex T hm C h).castSucc p hpN')
        (stageMap_mem_support_of_mem_support_strictTransformSeq _ γ _ hpγ)
    · refine disjoint_closeds_iff.mpr fun p hpN hpγ => ?_
      have htop := stalkIdeal_nonmonomialPart_isolatedMarkedIdeal_eq_top hs.invCE hKC hγA hpγ
      have hle := (Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp hpN
      rw [htop] at hle
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hle)

end IsolatedState

end Hironaka.Resolution
