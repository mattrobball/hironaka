/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedAdmissibleStratum
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4Sheaf
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Isolation
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Tools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The intersection form along a sequence, with per-stage hypotheses

The statement CP6 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) follows the un-isolated ideal `I = I_A
⊓ K` through the blow-ups of a round: at each stage the mark-`1` transform of `I` is the meet of the
strict transforms of the protected components with the mark-`1` transform of `K`, provided each
blow-up is admissible for `K` along the protected components (the sheaf form of CP4,
`markedTransform_biInf_inf_of_admissible` of
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4Sheaf`). This module proves that transport with
PER-STAGE hypotheses, the form that the protected states of CP5 instantiate on the run of `BMO_1`
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Loop`):

* `markedTransformSeq_eq_biInf_inf_of_forall_stage`: for `I₀ = (⨅ γ ∈ Γs, γ) ⊓ K` with `Γs`
  reduced and pairwise disjoint, if at every stage the ambient scheme is smooth, the boundary is
  snc, each transported `γ̃_i` is smooth and snc with it, `K_i` has the K-shape along `γ̃_i` and
  is admissible at the centre, and `K_i ≤ Z_i`, then `I_i = (⨅ γ, γ̃_i) ⊓ K_i` at every stage — the
  transport engine `markedTransformSeq_eq_inf_of_forall_step` on the single protected ideal
  `P := ⨅ γ ∈ Γs, γ`, with the disjoint-union bridge
  `strictTransformSeq_biInf_of_pairwise_disjoint` at every stage (its reducedness input needed at
  stage `0` only) and the finset form of CP4 at each blow-up on the transported family, whose
  pairwise disjointness is `pairwise_disjoint_strictTransformSeq_support`.

This statement is not in the literature.
-/

public section

universe u

open Ideal CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence
  Scheme.IdealSheafData

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}

/-- **The intersection form along a sequence, with per-stage hypotheses**: for
`I₀ = (⨅ γ ∈ Γs, γ) ⊓ K` with `Γs` reduced and pairwise disjoint, if at every stage the boundary
is snc, each transported `γ̃_i` is smooth and snc with it, `K_i` has the K-shape along `γ̃_i` and
is admissible at the centre, and `K_i ≤ Z_i`, then at every stage `I_i = (⨅ γ, γ̃_i) ⊓ K_i`. -/
theorem markedTransformSeq_eq_biInf_inf_of_forall_stage [IsLocallyNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of k)) (S : BlowUpSequence X) (E : DivisorFamily X)
    (K I₀ : X.IdealSheafData) (Γs : Finset X.IdealSheafData)
    (hred : ∀ γ ∈ Γs, IsReduced γ.subscheme)
    (hdisj : (↑Γs : Set X.IdealSheafData).Pairwise fun a b => Disjoint a.support b.support)
    (hI₀ : I₀ = (⨅ γ ∈ Γs, γ) ⊓ K)
    (hst : ∀ i : Fin S.length, Smooth (S.stageMap i.castSucc ≫ f))
    (hE : ∀ i : Fin S.length, (S.totalTransformSeq E i.castSucc).IsSnc)
    (hΓ : ∀ (i : Fin S.length), ∀ γ ∈ Γs,
      (S.totalTransformSeq E i.castSucc).HasSncWith (S.strictTransformSeq γ i.castSucc))
    (hsm : ∀ (i : Fin S.length), ∀ γ ∈ Γs,
      Smooth ((S.strictTransformSeq γ i.castSucc).subschemeι ≫ S.stageMap i.castSucc ≫ f))
    (hK : ∀ (i : Fin S.length), ∀ γ ∈ Γs, ∀ p ∈ (S.strictTransformSeq γ i.castSucc).support,
      ChainRelativeKAt (S.totalTransformSeq E i.castSucc) (S.markedTransformSeq K 1 i.castSucc)
        (S.strictTransformSeq γ i.castSucc) p)
    (hZ : ∀ (i : Fin S.length), ∀ γ ∈ Γs,
      ∀ p ∈ (S.center i).support ⊓ (S.strictTransformSeq γ i.castSucc).support,
      AdmissibleChainStratumKAt (S.totalTransformSeq E i.castSucc)
        (S.markedTransformSeq K 1 i.castSucc) (S.strictTransformSeq γ i.castSucc) (S.center i) p)
    (hKZ : ∀ i : Fin S.length, S.markedTransformSeq K 1 i.castSucc ≤ S.center i) :
    ∀ i : Fin (S.length + 1),
      S.markedTransformSeq I₀ 1 i = (⨅ γ ∈ Γs, S.strictTransformSeq γ i) ⊓
        S.markedTransformSeq K 1 i := by
  classical
  intro i
  rw [← strictTransformSeq_biInf_of_pairwise_disjoint S Γs hred hdisj i]
  refine markedTransformSeq_eq_inf_of_forall_step S (⨅ γ ∈ Γs, γ) I₀ K hI₀ (fun j hj => ?_) i
  -- the one-blow-up identity at stage `j`, from the finset form of CP4 on the transported family
  have := isLocallyNoetherian_stage S j.castSucc
  have := hst j
  have hredj : ∀ γ' ∈ Γs.image fun γ => S.strictTransformSeq γ j.castSucc,
      IsReduced γ'.subscheme := by
    intro γ' hγ'
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hγ'
    have := hred γ hγ
    exact isReduced_strictTransformSeq_subscheme S γ j.castSucc
  have hdisjj := pairwise_disjoint_strictTransformSeq_support S Γs hdisj j.castSucc
  have hiInf : (⨅ γ' ∈ Γs.image fun γ => S.strictTransformSeq γ j.castSucc, γ') =
      ⨅ γ ∈ Γs, S.strictTransformSeq γ j.castSucc := by
    simp only [Finset.iInf_finset_image]
  rw [strictTransformSeq_biInf_of_pairwise_disjoint S Γs hred hdisj j.castSucc, ← hiInf] at hj ⊢
  rw [strictTransform_biInf_of_pairwise_disjoint (S.center j) _ hredj hdisjj]
  refine markedTransform_biInf_inf_of_admissible (S.stageMap j.castSucc ≫ f)
    (S.totalTransformSeq E j.castSucc) _ _ (S.center j) _ (hE j) ?_ ?_ hdisjj hj ?_ ?_ (hKZ j)
  · intro γ' hγ'
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hγ'
    exact hΓ j γ hγ
  · intro γ' hγ'
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hγ'
    exact hsm j γ hγ
  · intro γ' hγ'
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hγ'
    exact hK j γ hγ
  · intro γ' hγ'
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hγ'
    exact hZ j γ hγ

end Hironaka.Resolution
