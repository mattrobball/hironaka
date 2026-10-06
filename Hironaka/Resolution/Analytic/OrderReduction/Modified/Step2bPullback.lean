/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bPhase
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bLocal
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Hironaka.Resolution.Analytic.Functor.PullbackTransport
import Hironaka.Resolution.Analytic.MaximalContact.Theorem97Induction
import Hironaka.Resolution.Analytic.OrderReduction.BDErase
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The monomial phase commutes with surjective local isomorphisms

The first condition of [Kol07, 34.1] for the monomial phase at the mark `1`: along a **surjective**
local analytic isomorphism `g : N → M` the phase of the pulled-back triple is the pull-back of the
phase, `step2bPhase k (T.pullback g) = (step2bPhase k T).pullback g` at every fuel `k`
(`step2bPhase_pullback_of_surjective`). The rule is intrinsic: the active members of the pull-back
are those of `T` (`activeMembers_pullback_of_surjective`), so the top members agree and the centre
pulls back to the centre (`step2bCenter_pullback` of `Step2bLocal.lean`); one step pulls back to
one step (`stepTripleOf_pullback_eq`: `birationalTransform_comap_liftStep` for the marked
transform, `totalTransform_comap_of_square` for the boundary, along the lift `liftStep g` of `g` to
the blow-ups); and the lift of a surjective local isomorphism to the blow-ups of a centre of
codimension one is again surjective (`liftStep_surjective`, the blow-downs being isomorphisms). The
two `cons` are compared by `cons_congr_heq`: the pulled-back centre and the centre of the pull-back
are propositionally equal sets with different witnesses, so the step is stated at an arbitrary
witness (`stepTripleOf`, `Step2bStep.lean`) and the tails are heterogeneously equal
(`heq_step2bPhase`).

This is the first of the two halves of the functoriality of the phase; the half for open
embeddings, up to the deletion of empty blow-ups, is `Step2bCommute.lean`.
-/

public section

noncomputable section

open Set Topology Filter
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

open Hironaka.Manifold.BD

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The phase is congruent under heterogeneous equality of triples over equal manifolds. -/
theorem heq_step2bPhase (k : ℕ) {M₁ M₂ : AnalyticManifold.{u} 𝕜 E} (hM : M₁ = M₂)
    (T₁ : AnalyticTriple ψ₀ M₁) (T₂ : AnalyticTriple ψ₀ M₂) (hT : HEq T₁ T₂)
    (h₁ : AnalyticTriple.BMOClass 1 T₁) (h₂ : AnalyticTriple.BMOClass 1 T₂) :
    HEq (step2bPhase k T₁ h₁) (step2bPhase k T₂ h₂) := by
  subst hM
  obtain rfl := eq_of_heq hT
  rfl

/-! ### One step pulls back to one step -/

section PullbackStep

variable {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
  (hfin : (activeMembers T).Finite) (hne : (activeMembers T).Nonempty) (g : AnalyticMap N M)
  (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g)
  (hfin' : (activeMembers (T.pullback g hg)).Finite)
  (hne' : (activeMembers (T.pullback g hg)).Nonempty)

/-- [Kol07, 34.1] for one step of the monomial phase: when the top members agree, the step of the
pull-back (at the witness of the pulled-back centre) is the pull-back of the step along the lift of
`g`: the marked transform by `birationalTransform_comap_liftStep`, the total transform by
`totalTransform_comap_of_square` with the square `blowUpπ_liftStep` of the lift. -/
theorem stepTripleOf_pullback_eq
    (htop : topMember (T.pullback g hg) hfin' hne' = topMember T hfin hne) :
    stepTripleOf (T.pullback g hg) hfin' hne'
        ((stepCenter T hfin hne).preimage_of_isLocalDiffeomorph hg)
        (step2bCenter_pullback T g hg hfin hne hfin' hne' htop).symm =
      (stepTriple T hfin hne).pullback (AnalyticManifold.BlowUpSequence.liftStep g hg
          (stepCenter T hfin hne))
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
            (stepCenter T hfin hne)) := by
  refine AnalyticTriple.ext' ?_ ?_
  · change
      (MarkedIdealSheaf.birationalTransform _ (isBlowUp_blowUpπ ψ₀ _)
          ⟨T.I.pullback g g.contMDiff, 1⟩).I =
      Manifold.IdealSheaf.pullback _ (AnalyticManifold.BlowUpSequence.liftStep g hg
          (stepCenter T hfin hne)).contMDiff
        (MarkedIdealSheaf.birationalTransform _ (isBlowUp_blowUpπ ψ₀ _) ⟨T.I, 1⟩).I
    exact (birationalTransform_comap_liftStep g hg (stepCenter T hfin hne) ⟨T.I, 1⟩
      (one_le_ordAlong_step2bCenter T hfin hne)).symm
  · change (T.F.comap ⇑g).totalTransform (Manifold.blowUpπ ψ₀ _) (⇑g ⁻¹' step2bCenter T hfin hne) =
      (T.F.totalTransform (Manifold.blowUpπ ψ₀ (stepCenter T hfin hne))
          (step2bCenter T hfin hne)).comap
        ⇑(AnalyticManifold.BlowUpSequence.liftStep g hg (stepCenter T hfin hne))
    exact (HypersurfaceFamily.totalTransform_comap_of_square g (stepCenter T hfin hne) _ rfl
      (AnalyticManifold.BlowUpSequence.liftStep g hg (stepCenter T hfin hne))
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg (stepCenter T hfin hne))
      (AnalyticManifold.BlowUpSequence.blowUpπ_liftStep g hg (stepCenter T hfin hne)) T.F).symm

end PullbackStep

/-! ### The lift of a surjective local isomorphism to codimension-one blowings-up is surjective -/

omit [FiniteDimensional 𝕜 E] in
/-- For a centre of codimension one both blow-downs are isomorphisms, so the lift of a surjective
local analytic isomorphism is surjective. -/
theorem liftStep_surjective {M N : AnalyticManifold.{u} 𝕜 E} (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) (hs : Function.Surjective g) {Y : Set M}
    (hY : IsClosedSubmanifold ψ₀ Y 1) : Function.Surjective
        (AnalyticManifold.BlowUpSequence.liftStep g hg hY) := by
  intro q
  obtain ⟨φ, hφ⟩ := (isBlowUp_blowUpπ ψ₀ hY).exists_diffeomorph_of_codim_one hY
  obtain ⟨φ', hφ'⟩ := IsBlowUp.exists_diffeomorph_of_codim_one
    (hY.preimage_of_isLocalDiffeomorph hg)
    (isBlowUp_blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hg))
  obtain ⟨p, hp⟩ := hs (Manifold.blowUpπ ψ₀ hY q)
  refine ⟨φ'.symm p, ?_⟩
  have h1 : φ (AnalyticManifold.BlowUpSequence.liftStep g hg hY (φ'.symm p)) = φ q := by
    rw [hφ (AnalyticManifold.BlowUpSequence.liftStep g hg hY (φ'.symm p)), hφ q,
        AnalyticManifold.BlowUpSequence.blowUpπ_liftStep,
      ← hφ' (φ'.symm p), φ'.apply_symm_apply, hp]
  calc AnalyticManifold.BlowUpSequence.liftStep g hg hY (φ'.symm p)
      = φ.symm (φ (AnalyticManifold.BlowUpSequence.liftStep g hg hY (φ'.symm p))) :=
          (φ.symm_apply_apply _).symm
    _ = φ.symm (φ q) := by rw [h1]
    _ = q := φ.symm_apply_apply q

/-! ### The phase commutes with surjective local isomorphisms -/

/-- The first condition of [Kol07, 34.1]: **along a surjective local analytic isomorphism the phase
of the pull-back is the pull-back of the phase**, at every fuel. The active members and the top
member agree (`activeMembers_pullback_of_surjective`, `topMember_pullback_eq`), the centre pulls
back to the centre, one step to one step (`stepTripleOf_pullback_eq`), and the lift is again a
surjective local isomorphism (`liftStep_surjective`). -/
theorem step2bPhase_pullback_of_surjective :
    ∀ (k : ℕ) {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
      (hT : AnalyticTriple.BMOClass 1 T) (g : AnalyticMap N M)
      (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g), Function.Surjective g →
      ∀ (hT' : AnalyticTriple.BMOClass 1 (T.pullback g hg)),
      step2bPhase k (T.pullback g hg) hT' = (step2bPhase k T hT).pullback g hg
  | 0, _, _, _, _, _, _, _, _ => by
    rw [step2bPhase_zero, step2bPhase_zero, AnalyticManifold.BlowUpSequence.pullback_nil]
  | k + 1, _, _, T, hT, g, hg, hs, hT' => by
    by_cases hne : (activeMembers T).Nonempty
    · have hne' : (activeMembers (T.pullback g hg)).Nonempty := by
        rw [activeMembers_pullback_of_surjective T g hg hs]
        exact hne
      have hfin := activeMembers_finite T hT
      have hfin' := activeMembers_finite (T.pullback g hg) hT'
      have hmem : topMember T hfin hne ∈ activeMembers (T.pullback g hg) := by
        rw [activeMembers_pullback_of_surjective T g hg hs]
        exact topMember_mem T hfin hne
      have htop := topMember_pullback_eq T g hg hfin hne hfin' hne' hmem
      have e := step2bCenter_pullback T g hg hfin hne hfin' hne' htop
      rw [step2bPhase_succ_of_nonempty (T.pullback g hg) hT' k hne',
        step2bPhase_succ_of_nonempty T hT k hne, AnalyticManifold.BlowUpSequence.pullback_cons]
      refine AnalyticManifold.BlowUpSequence.cons_congr_heq e _ _ _ _ ?_
      have hstep : HEq (stepTriple (T.pullback g hg) hfin' hne')
          ((stepTriple T hfin hne).pullback (AnalyticManifold.BlowUpSequence.liftStep g hg
              (stepCenter T hfin hne))
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
                (stepCenter T hfin hne))) := by
        rw [stepTriple, ← stepTripleOf_pullback_eq T hfin hne g hg hfin' hne' htop]
        exact heq_stepTripleOf (T.pullback g hg) hfin' hne' _ _ _ _
      refine HEq.trans (heq_step2bPhase k (AnalyticManifold.BlowUpSequence.blowUp_congr e _ _) _ _
          hstep _
        (AnalyticTriple.bmoClass_pullback (bmoClass_stepTriple T hfin hne hT) _ _)) ?_
      exact heq_of_eq (step2bPhase_pullback_of_surjective k (stepTriple T hfin hne)
        (bmoClass_stepTriple T hfin hne hT) _ _
        (liftStep_surjective g hg hs (stepCenter T hfin hne)) _)
    · have hne' : ¬ (activeMembers (T.pullback g hg)).Nonempty := fun h =>
        hne (h.mono (activeMembers_pullback_subset T g hg))
      rw [step2bPhase_succ_of_not_nonempty (T.pullback g hg) hT' k hne',
        step2bPhase_succ_of_not_nonempty T hT k hne, AnalyticManifold.BlowUpSequence.pullback_nil]

end Hironaka.Manifold.BMOmod

end
