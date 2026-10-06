/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bPhase
import Hironaka.Resolution.Analytic.MaximalContact.Theorem97Induction
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bPullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The monomial phase is indifferent to empty boundary members

The counterpart, for boundary members, of the empty blow-up convention [Kol07, 32], for the monomial
phase at the mark `1`: deleting empty members of the boundary does not change the phase. Two triples
on the same manifold with the same ideal sheaf whose boundary families differ by an empty extension
along an order embedding `e` (`HypersurfaceFamily.IsEmptyExtension`: the members correspond along
`e`, the members outside its range are empty) have the same phase at every fuel
(`step2bPhase_eq_of_isEmptyExtension`): an empty member has an empty positive locus, so it is never
active; the active members correspond along `e`; the top members correspond (the maximum in a linear
order along an order embedding); the centres are the same set; and after one step the two total
transforms differ again by an empty extension, along `e ⊕ₗ id` (`sumLexEmb`; the strict transform of
an empty member is empty, `strictTransformSet_empty`).
-/

@[expose] public section

noncomputable section

open Set Topology Filter
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

/-! ### The order embedding `e ⊕ₗ id` -/

/-- The order embedding `α ⊕ₗ PUnit ↪o β ⊕ₗ PUnit` induced by `e : α ↪o β` on the first summand. -/
def sumLexEmb {α β : Type u} [LinearOrder α] [LinearOrder β] (e : α ↪o β) :
    α ⊕ₗ PUnit.{u + 1} ↪o β ⊕ₗ PUnit.{u + 1} :=
  OrderEmbedding.ofMapLEIff (fun s => toLex (Sum.map e id (ofLex s))) fun a b => by
    obtain ⟨a, rfl⟩ : ∃ a', toLex a' = a := ⟨ofLex a, rfl⟩
    obtain ⟨b, rfl⟩ : ∃ b', toLex b' = b := ⟨ofLex b, rfl⟩
    rcases a with a | a <;> rcases b with b | b <;> simp

theorem sumLexEmb_inl {α β : Type u} [LinearOrder α] [LinearOrder β] (e : α ↪o β) (a : α) :
    sumLexEmb e (toLex (Sum.inl a)) = toLex (Sum.inl (e a)) := rfl

theorem sumLexEmb_inr {α β : Type u} [LinearOrder α] [LinearOrder β] (e : α ↪o β) :
    sumLexEmb e (toLex (Sum.inr PUnit.unit)) = toLex (Sum.inr PUnit.unit) := rfl

namespace BMOmod

open _root_.Manifold

open Hironaka.Manifold.BD

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

section Ext

variable (T₁ T₂ : AnalyticTriple ψ₀ M)

omit [FiniteDimensional 𝕜 E] in
theorem positiveLocus_of_isEmptyExtension (hI : T₁.I = T₂.I) (e : T₁.F.ι ↪o T₂.F.ι)
    (hext : HypersurfaceFamily.IsEmptyExtension e) (j : T₁.F.ι) :
    positiveLocus T₂ (e j) = positiveLocus T₁ j := by
  change Zminus1 T₂.I 1 (T₂.F.hyp (e j)) = Zminus1 T₁.I 1 (T₁.F.hyp j)
  rw [hext.1 j, hI]

theorem positiveLocus_eq_empty_of_notMem_range (e : T₁.F.ι ↪o T₂.F.ι)
    (hext : HypersurfaceFamily.IsEmptyExtension e) {b : T₂.F.ι} (hb : b ∉ Set.range e) :
    positiveLocus T₂ b = ∅ :=
  Set.subset_empty_iff.mp ((positiveLocus_subset T₂ b).trans (hext.2 b hb).subset)

theorem activeMembers_of_isEmptyExtension (hI : T₁.I = T₂.I) (e : T₁.F.ι ↪o T₂.F.ι)
    (hext : HypersurfaceFamily.IsEmptyExtension e) :
    activeMembers T₂ = e '' activeMembers T₁ := by
  ext b
  constructor
  · intro hb
    by_cases hr : b ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hr
      refine ⟨j, ?_, rfl⟩
      change (positiveLocus T₁ j).Nonempty
      rw [← positiveLocus_of_isEmptyExtension T₁ T₂ hI e hext j]
      exact hb
    · exfalso
      have : (positiveLocus T₂ b).Nonempty := hb
      rw [positiveLocus_eq_empty_of_notMem_range T₁ T₂ e hext hr] at this
      exact this.ne_empty rfl
  · rintro ⟨j, hj, rfl⟩
    change (positiveLocus T₂ (e j)).Nonempty
    rw [positiveLocus_of_isEmptyExtension T₁ T₂ hI e hext j]
    exact hj

theorem activeMembers_nonempty_iff_of_isEmptyExtension (hI : T₁.I = T₂.I) (e : T₁.F.ι ↪o T₂.F.ι)
    (hext : HypersurfaceFamily.IsEmptyExtension e) :
    (activeMembers T₂).Nonempty ↔ (activeMembers T₁).Nonempty := by
  rw [activeMembers_of_isEmptyExtension T₁ T₂ hI e hext, Set.image_nonempty]

/-- The top member corresponds along the order embedding. -/
theorem topMember_of_isEmptyExtension (hI : T₁.I = T₂.I) (e : T₁.F.ι ↪o T₂.F.ι)
    (hext : HypersurfaceFamily.IsEmptyExtension e) (hfin₁ : (activeMembers T₁).Finite)
    (hne₁ : (activeMembers T₁).Nonempty) (hfin₂ : (activeMembers T₂).Finite)
    (hne₂ : (activeMembers T₂).Nonempty) :
    topMember T₂ hfin₂ hne₂ = e (topMember T₁ hfin₁ hne₁) := by
  have hact := activeMembers_of_isEmptyExtension T₁ T₂ hI e hext
  refine le_antisymm ?_ ?_
  · have hmem := topMember_mem T₂ hfin₂ hne₂
    rw [hact] at hmem
    obtain ⟨j, hj, hje⟩ := hmem
    rw [← hje]
    exact e.le_iff_le.mpr (le_topMember T₁ hfin₁ hne₁ hj)
  · refine le_topMember T₂ hfin₂ hne₂ ?_
    rw [hact]
    exact ⟨_, topMember_mem T₁ hfin₁ hne₁, rfl⟩

/-- The Step 2b centres coincide. -/
theorem step2bCenter_of_isEmptyExtension (hI : T₁.I = T₂.I) (e : T₁.F.ι ↪o T₂.F.ι)
    (hext : HypersurfaceFamily.IsEmptyExtension e) (hfin₁ : (activeMembers T₁).Finite)
    (hne₁ : (activeMembers T₁).Nonempty) (hfin₂ : (activeMembers T₂).Finite)
    (hne₂ : (activeMembers T₂).Nonempty) :
    step2bCenter T₁ hfin₁ hne₁ = step2bCenter T₂ hfin₂ hne₂ := by
  unfold step2bCenter
  rw [topMember_of_isEmptyExtension T₁ T₂ hI e hext hfin₁ hne₁ hfin₂ hne₂,
    positiveLocus_of_isEmptyExtension T₁ T₂ hI e hext]

/-- After one step the two total transforms differ again by an empty extension, along `e ⊕ₗ id`
(the strict transform of an empty member is empty). -/
theorem isEmptyExtension_stepTripleOf (hI : T₁.I = T₂.I) (e : T₁.F.ι ↪o T₂.F.ι)
    (hext : HypersurfaceFamily.IsEmptyExtension e) (hfin₁ : (activeMembers T₁).Finite)
    (hne₁ : (activeMembers T₁).Nonempty) (hfin₂ : (activeMembers T₂).Finite)
    (hne₂ : (activeMembers T₂).Nonempty) :
    HypersurfaceFamily.IsEmptyExtension
      (G := (stepTriple T₁ hfin₁ hne₁).F)
      (G' := (stepTripleOf T₂ hfin₂ hne₂ (stepCenter T₁ hfin₁ hne₁)
        (step2bCenter_of_isEmptyExtension T₁ T₂ hI e hext hfin₁ hne₁ hfin₂ hne₂)).F)
      (sumLexEmb e) := by
  constructor
  · intro j
    obtain ⟨j, rfl⟩ : ∃ j', toLex j' = j := ⟨ofLex j, rfl⟩
    rcases j with j | u
    · change strictTransformSet _ _ (T₂.F.hyp (e j)) = strictTransformSet _ _ (T₁.F.hyp j)
      rw [hext.1 j]
    · rfl
  · intro b hb
    obtain ⟨b, rfl⟩ : ∃ b', toLex b' = b := ⟨ofLex b, rfl⟩
    rcases b with b | u
    · have hb' : b ∉ Set.range e := fun ⟨j, hj⟩ => hb ⟨toLex (Sum.inl j), by
        change toLex (Sum.inl (e j)) = toLex (Sum.inl b)
        rw [hj]⟩
      change strictTransformSet _ _ (T₂.F.hyp b) = ∅
      rw [hext.2 b hb', strictTransformSet_empty]
    · exact absurd ⟨toLex (Sum.inr PUnit.unit), sumLexEmb_inr e⟩ hb

end Ext

/-! ### The phase is indifferent to empty members -/

/-- **The phase does not see empty boundary members** (the counterpart, for boundary members, of
[Kol07, 32]): two triples on the same manifold
with the same ideal sheaf whose boundaries differ by an empty extension have the same phase at
every fuel. Induction on the fuel: the centres coincide (`step2bCenter_of_isEmptyExtension`), and
the steps differ again by an empty extension (`isEmptyExtension_stepTripleOf`), compared on the
same blow-up through the step at the witness of the first triple (`stepTripleOf`,
`heq_stepTripleOf`). -/
theorem step2bPhase_eq_of_isEmptyExtension :
    ∀ (k : ℕ) {M : AnalyticManifold.{u} 𝕜 E} (T₁ T₂ : AnalyticTriple ψ₀ M), T₁.I = T₂.I →
      ∀ (e : T₁.F.ι ↪o T₂.F.ι), HypersurfaceFamily.IsEmptyExtension e →
      ∀ (h₁ : AnalyticTriple.BMOClass 1 T₁) (h₂ : AnalyticTriple.BMOClass 1 T₂),
      step2bPhase k T₁ h₁ = step2bPhase k T₂ h₂
  | 0, M, T₁, T₂, hI, e, hext, h₁, h₂ => rfl
  | k + 1, M, T₁, T₂, hI, e, hext, h₁, h₂ => by
    by_cases hne₁ : (activeMembers T₁).Nonempty
    · have hne₂ : (activeMembers T₂).Nonempty :=
        (activeMembers_nonempty_iff_of_isEmptyExtension T₁ T₂ hI e hext).mpr hne₁
      have hfin₁ := activeMembers_finite T₁ h₁
      have hfin₂ := activeMembers_finite T₂ h₂
      have eZ := step2bCenter_of_isEmptyExtension T₁ T₂ hI e hext hfin₁ hne₁ hfin₂ hne₂
      rw [step2bPhase_succ_of_nonempty T₁ h₁ k hne₁, step2bPhase_succ_of_nonempty T₂ h₂ k hne₂]
      refine AnalyticManifold.BlowUpSequence.cons_congr_heq eZ _ _ _ _ ?_
      have hstep : HEq (stepTripleOf T₂ hfin₂ hne₂ (stepCenter T₁ hfin₁ hne₁) eZ)
          (stepTriple T₂ hfin₂ hne₂) := by
        rw [stepTriple]
        exact heq_stepTripleOf T₂ hfin₂ hne₂ _ _ _ _
      refine HEq.trans (heq_of_eq (step2bPhase_eq_of_isEmptyExtension k (stepTriple T₁ hfin₁ hne₁)
        (stepTripleOf T₂ hfin₂ hne₂ (stepCenter T₁ hfin₁ hne₁) eZ) ?_ (sumLexEmb e)
        (isEmptyExtension_stepTripleOf T₁ T₂ hI e hext hfin₁ hne₁ hfin₂ hne₂)
        (bmoClass_stepTriple T₁ hfin₁ hne₁ h₁) (bmoClass_stepTripleOf T₂ hfin₂ hne₂ _ eZ h₂))) ?_
      · change (MarkedIdealSheaf.birationalTransform _ (isBlowUp_blowUpπ ψ₀ _) ⟨T₁.I, 1⟩).I =
          (MarkedIdealSheaf.birationalTransform _ (isBlowUp_blowUpπ ψ₀ _) ⟨T₂.I, 1⟩).I
        rw [hI]
      · exact heq_step2bPhase k (AnalyticManifold.BlowUpSequence.blowUp_congr eZ _ _) _ _ hstep _ _
    · have hne₂ : ¬ (activeMembers T₂).Nonempty := fun h =>
        hne₁ ((activeMembers_nonempty_iff_of_isEmptyExtension T₁ T₂ hI e hext).mp h)
      rw [step2bPhase_succ_of_not_nonempty T₁ h₁ k hne₁,
        step2bPhase_succ_of_not_nonempty T₂ h₂ k hne₂]

end BMOmod

end Hironaka.Manifold

end
