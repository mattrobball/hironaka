/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses
import Hironaka.Resolution.Algebraic.Kol07.StrictTransformSupport
import Hironaka.Resolution.Algebraic.Wlo05.OffCentreTransport
import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.Snc.HasSncWith
import Hironaka.Scheme.Snc.TotalTransformSmoothBlowUp
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Transport of a protected closed subscheme along a blow-up sequence

In the isolation passage of the proof of [Wlo05, Theorem 4.7.1], once the strict transform of a
component is isolated, the later blow-ups of the modified run leave it alone: each centre either
misses it or is a stratum of the boundary transversal to it. This module carries a closed
subscheme `γ` having simple normal crossings with the boundary, and contained in no member of it
near any of its points, along a blow-up sequence whose every centre misses the strict transform of
`γ` at its stage or is locally a stratum of the boundary at its stage (`MissesOrStratum`): at every
stage the strict transform of `γ` has simple normal crossings with the total transform of the
boundary, is contained in no member near any point, and is the pull-back of the ideal of `γ` along
the stage map. The two cases are `Hironaka.Resolution.Algebraic.Wlo05.OffCentreTransport` (the
centre misses `γ`) and the hypothesis `StratumBlowUp` (the stratum case;
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses`). Structural recursion on the sequence.
Blow-up sequences of order `≥ m` are those of [Kol07, Definition 66].

`StratumBlowUp` is not proved in this development, so `protected_transport` and
`smooth_strictTransformSeq_of_protected` are CONDITIONAL lemmas; they are used by the conditional
loop modules `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedState` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedIsolatedState`, not by the proof of the theorem, which
reaches the same conclusions through CP4 and CP5
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP5`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData
  BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-- The dichotomy of the isolation passage of the proof of [Wlo05, Theorem 4.7.1] for the centres
of a sequence relative to a protected closed subscheme `γ`: every centre misses the strict
transform of `γ` at its stage, or is locally a stratum of the boundary at its stage. -/
def MissesOrStratum {X : Scheme.{u}} (S : BlowUpSequence X) (E : DivisorFamily X)
    (γ : X.IdealSheafData) : Prop :=
  ∀ i : Fin S.length,
    Disjoint (S.center i).support (S.strictTransformSeq γ i.castSucc).support ∨
      IsLocalStratum (S.totalTransformSeq E i.castSucc) (S.center i)

/-- Disjoint closed subschemes have disjoint strict transforms at every stage (the strict transform
maps into the closed subscheme below). -/
theorem disjoint_strictTransformSeq_support_of_disjoint {X : Scheme.{u}} [IsLocallyNoetherian X]
    (S : BlowUpSequence X) (γ γ' : X.IdealSheafData) (h : Disjoint γ.support γ'.support)
    (i : Fin (S.length + 1)) :
    Disjoint (S.strictTransformSeq γ i).support (S.strictTransformSeq γ' i).support :=
  disjoint_closeds_iff.mpr fun _ hp hp' => notMem_of_disjoint_closeds h
    (stageMap_mem_support_of_mem_support_strictTransformSeq S γ i hp)
    (stageMap_mem_support_of_mem_support_strictTransformSeq S γ' i hp')

/-- **The protected transport**, conditional on the hypothesis `StratumBlowUp`: along a sequence
of smooth stages whose centres have simple normal crossings with the boundary and satisfy the
dichotomy for `γ`, the strict transform of `γ` at every stage has simple normal crossings with the
total transform of the boundary, is contained in no member of it near any point, and is the
pull-back of the ideal of `γ` along the stage map (the isolation passage of the proof of
[Wlo05, Theorem 4.7.1]). -/
theorem protected_transport (hG : StratumBlowUp k) :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X)
      (f : X ⟶ Spec (CommRingCat.of k)) (E : DivisorFamily X) (γ : X.IdealSheafData),
      (∀ i : Fin (S.length + 1), Smooth (S.stageMap i ≫ f)) → E.IsSnc →
      (∀ i : Fin S.length, (S.totalTransformSeq E i.castSucc).HasSncWith (S.center i)) →
      MissesOrStratum S E γ → E.HasSncWith γ → NotContainedInMembers E γ →
      ∀ i : Fin (S.length + 1),
        (S.totalTransformSeq E i).HasSncWith (S.strictTransformSeq γ i) ∧
          NotContainedInMembers (S.totalTransformSeq E i) (S.strictTransformSeq γ i) ∧
          γ.comap (S.stageMap i) = S.strictTransformSeq γ i
  | X, nil _, _, _, γ, _, _, _, _, hγ, hno, _ =>
    ⟨hγ, hno, by
      change γ.comap (𝟙 X) = γ
      exact comap_id γ⟩
  | X, cons _ _ _, _, _, γ, _, _, _, _, hγ, hno, ⟨0, _⟩ =>
    ⟨hγ, hno, by
      change γ.comap (𝟙 X) = γ
      exact comap_id γ⟩
  | X, cons _ D rest, f, E, γ, hsm, hE, hcen, hdich, hγ, hno, ⟨j + 1, hj⟩ => by
    have hf : Smooth f := by
      have := hsm ⟨0, Nat.succ_pos _⟩
      change Smooth (𝟙 X ≫ f) at this
      rwa [Category.id_comp] at this
    have := LocallyOfFiniteType.isLocallyNoetherian f
    have hD : E.HasSncWith D := hcen ⟨0, Nat.succ_pos _⟩
    have hstep : (E.totalTransform D).HasSncWith (γ.strictTransform D) ∧
        NotContainedInMembers (E.totalTransform D) (γ.strictTransform D) ∧
        γ.comap D.blowUpπ = γ.strictTransform D := by
      rcases hdich ⟨0, Nat.succ_pos _⟩ with hdisj | hstr
      · exact ⟨hasSncWith_totalTransform_strictTransform_of_disjoint D γ E hdisj hγ,
          notContainedInMembers_totalTransform_strictTransform_of_disjoint D γ E hdisj hno,
          comap_blowUpπ_eq_strictTransform_of_disjoint D γ hdisj⟩
      · exact hG f E D γ hE hD hstr hγ hno
    have hE' : (E.totalTransform D).IsSnc := totalTransform_isSnc f E D hE hD
    have ih := protected_transport hG rest (D.blowUpπ ≫ f) (E.totalTransform D)
      (γ.strictTransform D)
      (fun ⟨v, hv⟩ => by
        have := hsm ⟨v + 1, Nat.succ_lt_succ hv⟩
        change Smooth ((rest.stageMap ⟨v, hv⟩ ≫ D.blowUpπ) ≫ f) at this
        rwa [Category.assoc] at this)
      hE' (fun ⟨v, hv⟩ => hcen ⟨v + 1, Nat.succ_lt_succ hv⟩)
      (fun ⟨v, hv⟩ => hdich ⟨v + 1, Nat.succ_lt_succ hv⟩) hstep.1 hstep.2.1
      ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    refine ⟨ih.1, ih.2.1, ?_⟩
    change γ.comap (rest.stageMap ⟨j, _⟩ ≫ D.blowUpπ) =
      rest.strictTransformSeq (γ.strictTransform D) ⟨j, _⟩
    rw [comap_comp, hstep.2.2, ih.2.2]

/-- The protected strict transform is smooth over `k` at every stage (a subvariety with simple
normal crossings with `E` is smooth, [Kol07, Definition 24]; `HasSncWith.smooth`), conditional on
`StratumBlowUp`. -/
theorem smooth_strictTransformSeq_of_protected (hG : StratumBlowUp k) {X : Scheme.{u}}
    (S : BlowUpSequence X) (f : X ⟶ Spec (CommRingCat.of k))
    (E : DivisorFamily X) (γ : X.IdealSheafData)
    (hsm : ∀ i : Fin (S.length + 1), Smooth (S.stageMap i ≫ f)) (hE : E.IsSnc)
    (hcen : ∀ i : Fin S.length, (S.totalTransformSeq E i.castSucc).HasSncWith (S.center i))
    (hdich : MissesOrStratum S E γ) (hγ : E.HasSncWith γ) (hno : NotContainedInMembers E γ)
    (i : Fin (S.length + 1)) :
    Smooth ((S.strictTransformSeq γ i).subschemeι ≫ S.stageMap i ≫ f) :=
  have := hsm i
  HasSncWith.smooth (S.stageMap i ≫ f)
    (protected_transport hG S f E γ hsm hE hcen hdich hγ hno i).1

end Hironaka.Resolution
