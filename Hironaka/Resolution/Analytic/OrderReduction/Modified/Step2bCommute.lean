/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bMeasure
public import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Hironaka.Resolution.Analytic.Functor.PullbackTransport
import Hironaka.Resolution.Analytic.MaximalContact.Theorem97Induction
import Hironaka.Resolution.Analytic.OrderReduction.BDErase
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bEmpty
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bPullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The monomial phase commutes with local isomorphisms up to empty blow-ups

The second condition of [Kol07, 34.1] and the compatibility of [Wlo09, Theorem 2.0.3 (4)] (in the
sense of [Wlo09, Definition 3.2.6]) for the monomial phase at the mark `1`: along a local analytic
isomorphism `g : N → M` the **complete** phase of the pulled-back triple is the pull-back of the
complete phase of `T` with its empty blow-ups deleted,
`step2bPhase k' (T.pullback g) = ((step2bPhase k T).pullback g).eraseEmpty` for every
`k ≥ step2bMeasure T` and `k' ≥ step2bMeasure (T.pullback g)` (`step2bPhase_pullback_eraseEmpty`).
This gives the compatibility of the family of the phase and the half of its commutation with local
isomorphisms for open embeddings.

Induction on the fuel of `T`. At a step with centre `Z` (the positive locus of the top member `j`)
either `g⁻¹(Z)` is nonempty, and then `j` is the top member of the pull-back too, the centre pulls
back to the centre and the step to the step (`Step2bPullback.lean`), and the induction continues
along the lift of `g`; or `g⁻¹(Z)` is empty: the pulled-back blow-up is the empty one, which the
deletion of empty blow-ups removes by carrying the tail back along the isomorphism `Bl_∅ N ≃ N`
(`eraseEmpty_cons_of_eq_empty`, `map_eq_pullback_symm`); the triple of the tail carried back is the
pull-back with one **empty** member appended (`emptyStepTriple_I`,
`isEmptyExtension_emptyStepTriple`: the marked transform along an empty blow-up is the total
transform, `birationalTransform_I_of_eq_empty`), so the phase is indifferent to it
(`Step2bEmpty.lean`) and the carried-back phase is the pull-back's own (`Step2bPullback.lean`, the
isomorphism being surjective). The fuels are reconciled by the stabilisation of
`Step2bMeasure.lean`: the measure does not increase under pull-back (`step2bMeasure_pullback_le`)
nor under the deletion of empty members (`step2bMeasure_le_of_isEmptyExtension`).
-/

@[expose] public section

noncomputable section

open Set Topology Filter
open scoped Manifold ContDiff BigOperators

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

open Hironaka.Manifold.BD

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The measure under pull-back and under empty extensions -/

section MeasureMono

variable {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (g : AnalyticMap N M)
  (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g)

omit [FiniteDimensional 𝕜 E] in
/-- The supremum along a pulled-back member is at most the supremum along the member (the order
along the member transports along `g`, `ordAlongIdeal_comap_of_isLocalDiffeomorphAt`). -/
theorem memberSup_pullback_le (k : T.F.ι) : memberSup (T.pullback g hg) k ≤ memberSup T k := by
  refine iSup_le fun x' => ?_
  have hxk : g x' ∈ T.F.hyp k := x'.2
  have hD : ((T.pullback g hg).isSnc.1 k).idealSheaf =
      (T.isSnc.1 k).idealSheaf.pullback g g.contMDiff :=
    (comap_idealSheaf_of_isLocalDiffeomorph ψ₀ g hg (T.isSnc.1 k)).symm
  calc IdealSheaf.ordAlongIdeal ((T.pullback g hg).isSnc.1 k).idealSheaf (T.pullback g hg).I x'
      = IdealSheaf.ordAlongIdeal ((T.isSnc.1 k).idealSheaf.pullback g g.contMDiff)
          (T.I.pullback g g.contMDiff) x' :=
        congrArg
            (fun D => IdealSheaf.ordAlongIdeal D (T.I.pullback g g.contMDiff) x')
                hD
    _ = IdealSheaf.ordAlongIdeal (T.isSnc.1 k).idealSheaf T.I (g x') :=
        IdealSheaf.ordAlongIdeal_comap_of_isLocalDiffeomorphAt g _ _ (hg x')
    _ ≤ memberSup T k := ordAlong_le_memberSup T hxk

omit [FiniteDimensional 𝕜 E] in
/-- A nonempty member of the pull-back lies over a nonempty member. -/
theorem nonemptyFinset_pullback_subset (hT : AnalyticTriple.BMOClass 1 T)
    (hT' : AnalyticTriple.BMOClass 1 (T.pullback g hg)) :
    (T.pullback g hg).F.nonemptyFinset hT'.2 ⊆ T.F.nonemptyFinset hT.2 := by
  intro k hk
  have hk' : (T.pullback g hg).F.hyp k ≠ ∅ := ((T.pullback g hg).F.mem_nonemptyFinset hT'.2 _).mp hk
  refine (T.F.mem_nonemptyFinset hT.2 _).mpr fun h => hk' ?_
  change ⇑g ⁻¹' T.F.hyp k = ∅
  rw [h, Set.preimage_empty]

omit [FiniteDimensional 𝕜 E] in
/-- The measure does not increase under pull-back along a local isomorphism. -/
theorem step2bMeasure_pullback_le (hT : AnalyticTriple.BMOClass 1 T)
    (hT' : AnalyticTriple.BMOClass 1 (T.pullback g hg)) :
    step2bMeasure (T.pullback g hg) hT' ≤ step2bMeasure T hT :=
  (Finset.sum_le_sum fun k _ => memberSup_pullback_le T g hg k).trans
    (Finset.sum_le_sum_of_subset (nonemptyFinset_pullback_subset T g hg hT hT'))

end MeasureMono

section MeasureExt

variable {M : AnalyticManifold.{u} 𝕜 E} (T₁ T₂ : AnalyticTriple ψ₀ M)

omit [FiniteDimensional 𝕜 E] in
/-- Members with the same underlying set (and the same ideal sheaf) have the same sup. -/
theorem memberSup_le_of_hyp_eq (hI : T₁.I = T₂.I) {k₁ : T₁.F.ι} {k₂ : T₂.F.ι}
    (hk : T₂.F.hyp k₂ = T₁.F.hyp k₁) : memberSup T₁ k₁ ≤ memberSup T₂ k₂ := by
  refine iSup_le fun x => ?_
  have hx : (x : M) ∈ T₂.F.hyp k₂ := by
    rw [hk]
    exact x.2
  calc IdealSheaf.ordAlongIdeal (T₁.isSnc.1 k₁).idealSheaf T₁.I x
      = IdealSheaf.ordAlongIdeal (T₂.isSnc.1 k₂).idealSheaf T₂.I x := by
        rw [hI, IsClosedSubmanifold.idealSheaf_congr (T₁.isSnc.1 k₁) (T₂.isSnc.1 k₂) hk.symm]
    _ ≤ memberSup T₂ k₂ := ordAlong_le_memberSup T₂ hx

omit [FiniteDimensional 𝕜 E] in
/-- The measure does not increase under an empty extension of the boundary. -/
theorem step2bMeasure_le_of_isEmptyExtension (hI : T₁.I = T₂.I) (e : T₁.F.ι ↪o T₂.F.ι)
    (hext : HypersurfaceFamily.IsEmptyExtension e) (h₁ : AnalyticTriple.BMOClass 1 T₁)
    (h₂ : AnalyticTriple.BMOClass 1 T₂) : step2bMeasure T₁ h₁ ≤ step2bMeasure T₂ h₂ := by
  have himg : (T₁.F.nonemptyFinset h₁.2).image e ⊆ T₂.F.nonemptyFinset h₂.2 := by
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    rw [HypersurfaceFamily.mem_nonemptyFinset] at hj ⊢
    rw [hext.1 j]
    exact hj
  calc step2bMeasure T₁ h₁ = ∑ j ∈ T₁.F.nonemptyFinset h₁.2, memberSup T₁ j := rfl
    _ ≤ ∑ j ∈ T₁.F.nonemptyFinset h₁.2, memberSup T₂ (e j) :=
        Finset.sum_le_sum fun j _ => memberSup_le_of_hyp_eq T₁ T₂ hI (hext.1 j)
    _ = ∑ b ∈ (T₁.F.nonemptyFinset h₁.2).image e, memberSup T₂ b :=
        (Finset.sum_image fun _ _ _ _ h => e.injective h).symm
    _ ≤ step2bMeasure T₂ h₂ := Finset.sum_le_sum_of_subset himg

end MeasureExt

/-! ### Fuels above the measure give the same phase -/

theorem step2bPhase_eq_of_step2bMeasure_le' {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BMOClass 1 T) {k k' : ℕ} (hk : step2bMeasure T hT ≤ k)
    (hk' : step2bMeasure T hT ≤ k') : step2bPhase k T hT = step2bPhase k' T hT := by
  rcases le_total k k' with h | h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    exact (step2bPhase_eq_of_step2bMeasure_le T hT hk m).symm
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    exact step2bPhase_eq_of_step2bMeasure_le T hT hk' m

omit [FiniteDimensional 𝕜 E] in
/-- The measure is congruent under heterogeneous equality of triples over equal manifolds. -/
theorem step2bMeasure_congr_heq {M₁ M₂ : AnalyticManifold.{u} 𝕜 E} (hM : M₁ = M₂)
    (T₁ : AnalyticTriple ψ₀ M₁) (T₂ : AnalyticTriple ψ₀ M₂) (hT : HEq T₁ T₂)
    (h₁ : AnalyticTriple.BMOClass 1 T₁) (h₂ : AnalyticTriple.BMOClass 1 T₂) :
    step2bMeasure T₁ h₁ = step2bMeasure T₂ h₂ := by
  subst hM
  obtain rfl := eq_of_heq hT
  rfl

/-! ### The empty case: the tail carried back along `Bl_∅ N ≃ N` -/

section EmptyCase

variable {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
  (hfin : (activeMembers T).Finite) (hne : (activeMembers T).Nonempty) (g : AnalyticMap N M)
  (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g)

/-- The preimage of the centre, as a closed submanifold of `N`. -/
abbrev emptyPre : IsClosedSubmanifold ψ₀ (⇑g ⁻¹' step2bCenter T hfin hne) 1 :=
  (stepCenter T hfin hne).preimage_of_isLocalDiffeomorph hg

variable (hZe : ⇑g ⁻¹' step2bCenter T hfin hne = ∅)

/-- The isomorphism `Bl_∅ N ≃ N` of the empty blow-up (`emptyBlowUpDiffeomorph`). -/
abbrev emptyIso := AnalyticManifold.BlowUpSequence.emptyBlowUpDiffeomorph
    (emptyPre T hfin hne g hg) hZe

/-- Its inverse as an analytic map `N → Bl_∅ N`. -/
abbrev emptyBack : AnalyticMap N (Manifold.blowUp ψ₀ (emptyPre T hfin hne g hg)) :=
  Diffeomorph.toAnalyticMap (emptyIso T hfin hne g hg hZe).symm

theorem blowUpπ_emptyBack (x : N) :
    Manifold.blowUpπ ψ₀ (emptyPre T hfin hne g hg) (emptyBack T hfin hne g hg hZe x) = x := by
  change Manifold.blowUpπ ψ₀ (emptyPre T hfin hne g hg) ((emptyIso T hfin hne g hg hZe).symm x) = x
  rw [← AnalyticManifold.BlowUpSequence.emptyBlowUpDiffeomorph_apply]
  exact (emptyIso T hfin hne g hg hZe).apply_symm_apply x

theorem emptyBack_surjective : Function.Surjective (emptyBack T hfin hne g hg hZe) := fun y =>
  ⟨emptyIso T hfin hne g hg hZe y, (emptyIso T hfin hne g hg hZe).symm_apply_apply y⟩

/-- The step pulled back along the lift and carried back to `N`. -/
abbrev emptyStepTriple : AnalyticTriple ψ₀ N :=
  ((stepTriple T hfin hne).pullback (AnalyticManifold.BlowUpSequence.liftStep g hg
      (stepCenter T hfin hne))
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
        (stepCenter T hfin hne))).pullback
    (emptyBack T hfin hne g hg hZe) (emptyIso T hfin hne g hg hZe).symm.isLocalDiffeomorph

/-- Along the empty blow-up the marked transform is the total transform
(`birationalTransform_I_of_eq_empty`), so the carried-back ideal sheaf is the pull-back's own. -/
theorem emptyStepTriple_I : (emptyStepTriple T hfin hne g hg hZe).I = (T.pullback g hg).I := by
  change (Manifold.IdealSheaf.pullback _ (AnalyticManifold.BlowUpSequence.liftStep g hg
        (stepCenter T hfin hne)).contMDiff
      (MarkedIdealSheaf.birationalTransform _ (isBlowUp_blowUpπ ψ₀ _) ⟨T.I, 1⟩).I).pullback _
        (emptyBack T hfin hne g hg hZe).contMDiff = T.I.pullback g g.contMDiff
  rw [birationalTransform_comap_liftStep g hg (stepCenter T hfin hne) ⟨T.I, 1⟩
    (one_le_ordAlong_step2bCenter T hfin hne),
    MarkedIdealSheaf.birationalTransform_I_of_eq_empty (emptyPre T hfin hne g hg) hZe _ _]
  change ((T.I.pullback g g.contMDiff).pullback _ (Manifold.blowUpπ ψ₀ (emptyPre T hfin hne g
      hg)).contMDiff).pullback _ (emptyBack T hfin hne g hg hZe).contMDiff = T.I.pullback g
          g.contMDiff
  rw [AnalyticManifold.IdealSheaf.pullback_comp]
  have hid : (Manifold.blowUpπ ψ₀ (emptyPre T hfin hne g hg)).comp (emptyBack T hfin hne g hg hZe) =
      ContMDiffMap.id := ContMDiffMap.ext (blowUpπ_emptyBack T hfin hne g hg hZe)
  rw [hid]
  exact IdealSheaf.pullback_id_eq_self _

/-- The carried-back boundary is the pull-back's boundary with one empty member appended. -/
theorem isEmptyExtension_emptyStepTriple :
    HypersurfaceFamily.IsEmptyExtension (G := (T.pullback g hg).F)
      (G' := (emptyStepTriple T hfin hne g hg hZe).F)
      (HypersurfaceFamily.inlLexEmb T.F.ι) := by
  have hcomp : ⇑(Manifold.blowUpπ ψ₀ (emptyPre T hfin hne g hg)) ∘ ⇑(emptyBack T hfin hne g hg hZe)
      = id :=
    funext (blowUpπ_emptyBack T hfin hne g hg hZe)
  constructor
  · intro j
    -- the strict transform of a member pulls back along the lift to the strict transform of the
    -- pulled-back member (`strictTransformSet_preimage_of_square`); along the empty centre it is
    -- the member itself
    change ⇑(emptyBack T hfin hne g hg hZe) ⁻¹' (⇑(AnalyticManifold.BlowUpSequence.liftStep g hg
        (stepCenter T hfin hne))
      ⁻¹' strictTransformSet (Manifold.blowUpπ ψ₀ (stepCenter T hfin hne)) (step2bCenter T hfin hne)
        (T.F.hyp j)) = ⇑g ⁻¹' T.F.hyp j
    rw [strictTransformSet_preimage_of_square g (stepCenter T hfin hne) (emptyPre T hfin hne g hg)
      rfl (AnalyticManifold.BlowUpSequence.liftStep g hg (stepCenter T hfin hne))
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg (stepCenter T hfin hne))
      (AnalyticManifold.BlowUpSequence.blowUpπ_liftStep g hg (stepCenter T hfin hne)) (T.F.hyp j)]
    have hcl : IsClosed (⇑(Manifold.blowUpπ ψ₀ (emptyPre T hfin hne g hg)) ⁻¹'
        (⇑g ⁻¹' T.F.hyp j)) :=
      ((T.isSnc.1 j).isClosed.preimage g.contMDiff.continuous).preimage
        (Manifold.blowUpπ ψ₀ (emptyPre T hfin hne g hg)).contMDiff.continuous
    have hd : ⇑g ⁻¹' T.F.hyp j \ ⇑g ⁻¹' step2bCenter T hfin hne = ⇑g ⁻¹' T.F.hyp j := by
      rw [hZe, Set.sdiff_empty]
    change ⇑(emptyBack T hfin hne g hg hZe) ⁻¹' closure (⇑(Manifold.blowUpπ ψ₀
        (emptyPre T hfin hne g hg))
      ⁻¹' (⇑g ⁻¹' T.F.hyp j \ ⇑g ⁻¹' step2bCenter T hfin hne)) = ⇑g ⁻¹' T.F.hyp j
    rw [hd, hcl.closure_eq, ← Set.preimage_comp, hcomp, Set.preimage_id]
  · intro b hb
    obtain ⟨b, rfl⟩ : ∃ b', toLex b' = b := ⟨ofLex b, rfl⟩
    rcases b with j | u
    · exact absurd ⟨j, rfl⟩ hb
    · -- the exceptional member: the preimage of the (empty) pulled-back centre
      refine Set.subset_empty_iff.mp fun q hq => ?_
      have h1 : Manifold.blowUpπ ψ₀ (stepCenter T hfin hne)
          (AnalyticManifold.BlowUpSequence.liftStep g hg (stepCenter T hfin hne)
              (emptyBack T hfin hne g hg hZe q)) ∈
            step2bCenter T hfin hne := hq
      rw [AnalyticManifold.BlowUpSequence.blowUpπ_liftStep g hg (stepCenter T hfin hne),
          blowUpπ_emptyBack] at h1
      have h2 : q ∈ ⇑g ⁻¹' step2bCenter T hfin hne := h1
      rw [hZe] at h2
      exact h2

end EmptyCase

/-! ### The commutation theorem -/

/-- The second condition of [Kol07, 34.1] and the compatibility of [Wlo09, Theorem 2.0.3 (4)]:
**along a local analytic isomorphism `g`, the complete phase of the pull-back is the pull-back of
the complete phase with its empty blow-ups deleted.** -/
theorem step2bPhase_pullback_eraseEmpty :
    ∀ (k : ℕ) {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
      (hT : AnalyticTriple.BMOClass 1 T) (g : AnalyticMap N M)
      (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g)
      (hT' : AnalyticTriple.BMOClass 1 (T.pullback g hg)), step2bMeasure T hT ≤ k →
      ∀ (k' : ℕ), step2bMeasure (T.pullback g hg) hT' ≤ k' →
      step2bPhase k' (T.pullback g hg) hT' = ((step2bPhase k T hT).pullback g hg).eraseEmpty
  | 0, _, _, T, hT, g, hg, hT', hle, k', _ => by
    have hne : ¬ (activeMembers T).Nonempty := fun hne => by
      have := (one_le_step2bMeasure_of_nonempty T hT hne).trans hle
      simp at this
    have hne' : ¬ (activeMembers (T.pullback g hg)).Nonempty := fun h =>
      hne (h.mono (activeMembers_pullback_subset T g hg))
    rw [step2bPhase_of_not_nonempty (T.pullback g hg) hT' hne', step2bPhase_zero,
      AnalyticManifold.BlowUpSequence.pullback_nil, AnalyticManifold.BlowUpSequence.eraseEmpty_nil]
  | k + 1, _, _, T, hT, g, hg, hT', hle, k', hk' => by
    by_cases hne : (activeMembers T).Nonempty
    · have hfin := activeMembers_finite T hT
      have hmeas : step2bMeasure (stepTriple T hfin hne) (bmoClass_stepTriple T hfin hne hT) ≤ k :=
          by
        have h := (step2bMeasure_stepTriple_add_one_le T hfin hne hT).trans hle
        rw [Nat.cast_succ] at h
        exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h
      rw [step2bPhase_succ_of_nonempty T hT k hne, AnalyticManifold.BlowUpSequence.pullback_cons]
      by_cases hZ : (⇑g ⁻¹' step2bCenter T hfin hne).Nonempty
      · -- the top member is active for the pull-back
        obtain ⟨y, hy⟩ := hZ
        have hne' : (activeMembers (T.pullback g hg)).Nonempty :=
          ⟨_, mem_activeMembers_pullback_of_range T g hg hy ⟨y, rfl⟩⟩
        have hfin' := activeMembers_finite (T.pullback g hg) hT'
        have hmem : topMember T hfin hne ∈ activeMembers (T.pullback g hg) :=
          mem_activeMembers_pullback_of_range T g hg hy ⟨y, rfl⟩
        have htop := topMember_pullback_eq T g hg hfin hne hfin' hne' hmem
        have e := step2bCenter_pullback T g hg hfin hne hfin' hne' htop
        rw [AnalyticManifold.BlowUpSequence.eraseEmpty_cons_of_ne_empty _ _
            (Set.nonempty_iff_ne_empty.mp ⟨y, hy⟩)]
        obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := by
          refine Nat.exists_eq_succ_of_ne_zero fun h0 => ?_
          have := (one_le_step2bMeasure_of_nonempty _ hT' hne').trans hk'
          rw [h0] at this
          simp at this
        rw [step2bPhase_succ_of_nonempty (T.pullback g hg) hT' k'' hne']
        refine AnalyticManifold.BlowUpSequence.cons_congr_heq e _ _ _ _ ?_
        have hstep : HEq (stepTriple (T.pullback g hg) hfin' hne')
            ((stepTriple T hfin hne).pullback (AnalyticManifold.BlowUpSequence.liftStep g hg
                (stepCenter T hfin hne))
              (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
                  (stepCenter T hfin hne))) := by
          rw [stepTriple,
            ← stepTripleOf_pullback_eq T hfin hne g hg hfin' hne' htop]
          exact heq_stepTripleOf (T.pullback g hg) hfin' hne' _ _ _ _
        have hT₂ := AnalyticTriple.bmoClass_pullback (bmoClass_stepTriple T hfin hne hT) _
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg (stepCenter T hfin hne))
        have hmeas' : step2bMeasure _ hT₂ ≤ k'' := by
          rw [← step2bMeasure_congr_heq (AnalyticManifold.BlowUpSequence.blowUp_congr e _ _) _ _
              hstep
            (bmoClass_stepTriple (T.pullback g hg) hfin' hne' hT') hT₂]
          have h := (step2bMeasure_stepTriple_add_one_le (T.pullback g hg) hfin' hne' hT').trans hk'
          rw [Nat.cast_succ] at h
          exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h
        refine HEq.trans (heq_step2bPhase k'' (AnalyticManifold.BlowUpSequence.blowUp_congr e _ _)
            _ _ hstep _ hT₂) ?_
        exact heq_of_eq (step2bPhase_pullback_eraseEmpty k (stepTriple T hfin hne)
          (bmoClass_stepTriple T hfin hne hT) _ _ hT₂ hmeas k'' hmeas')
      · -- the top member is inactive for the pull-back: the pulled-back blow-up is empty
        have hZe : ⇑g ⁻¹' step2bCenter T hfin hne = ∅ := Set.not_nonempty_iff_eq_empty.mp hZ
        rw [AnalyticManifold.BlowUpSequence.eraseEmpty_cons_of_eq_empty _ _ hZe]
        have hT₂ := AnalyticTriple.bmoClass_pullback (bmoClass_stepTriple T hfin hne hT) _
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg (stepCenter T hfin hne))
        have hmeas₂ : step2bMeasure _ hT₂ ≤ k :=
          (step2bMeasure_pullback_le (stepTriple T hfin hne) _ _ (bmoClass_stepTriple T hfin hne hT)
            hT₂).trans hmeas
        have hT₃ := AnalyticTriple.bmoClass_pullback hT₂ (emptyBack T hfin hne g hg hZe)
          (emptyIso T hfin hne g hg hZe).symm.isLocalDiffeomorph
        have hmeas₃ : step2bMeasure (emptyStepTriple T hfin hne g hg hZe) hT₃ ≤ k :=
          (step2bMeasure_pullback_le _ _ _ hT₂ hT₃).trans hmeas₂
        have hmeas' : step2bMeasure (T.pullback g hg) hT' ≤ k :=
          (step2bMeasure_le_of_isEmptyExtension (T.pullback g hg)
            (emptyStepTriple T hfin hne g hg hZe)
            (emptyStepTriple_I T hfin hne g hg hZe).symm _
            (isEmptyExtension_emptyStepTriple T hfin hne g hg hZe) hT' hT₃).trans hmeas₃
        rw [step2bPhase_eq_of_step2bMeasure_le' (T.pullback g hg) hT' hk' hmeas',
          ← step2bPhase_pullback_eraseEmpty k (stepTriple T hfin hne)
            (bmoClass_stepTriple T hfin hne hT) _ _ hT₂ hmeas k hmeas₂,
          AnalyticManifold.BlowUpSequence.map_eq_pullback_symm,
          ← step2bPhase_pullback_of_surjective k _ hT₂ (emptyBack T hfin hne g hg hZe)
            (emptyIso T hfin hne g hg hZe).symm.isLocalDiffeomorph
            (emptyBack_surjective T hfin hne g hg hZe) hT₃]
        exact step2bPhase_eq_of_isEmptyExtension k (T.pullback g hg) _
          (emptyStepTriple_I T hfin hne g hg hZe).symm _
          (isEmptyExtension_emptyStepTriple T hfin hne g hg hZe) hT' hT₃
    · have hne' : ¬ (activeMembers (T.pullback g hg)).Nonempty := fun h =>
        hne (h.mono (activeMembers_pullback_subset T g hg))
      rw [step2bPhase_of_not_nonempty (T.pullback g hg) hT' hne',
        step2bPhase_succ_of_not_nonempty T hT k hne, AnalyticManifold.BlowUpSequence.pullback_nil,
        AnalyticManifold.BlowUpSequence.eraseEmpty_nil]

end Hironaka.Manifold.BMOmod

end
