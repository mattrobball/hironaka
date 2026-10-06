/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepBComm
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.IdealSheaf.DerivLemmas
import Hironaka.Manifold.IdealSheaf.Monoid
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Submanifold.Charts
import Hironaka.Resolution.Analytic.Functor.EraseEmptyOrder
import Hironaka.Resolution.Analytic.OrderReduction.BDBridge
import Hironaka.Resolution.Analytic.OrderReduction.BDCor85
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.OrderReduction.Functoriality
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The modified first step: the modified core is of order `≥ 1`

[Kol07, Definition 66 (2′)–(4′)] at the mark `1` for the modified core of [Wlo09, Theorem 7.4.1]:
on a relatively compact open `U` the modified core is a smooth blow-up sequence of order `≥ 1`
starting with the restricted triple `(U, 𝓘|_U, E|_U)`; every centre has only normal crossings with
the boundary and lies in the zero set of the current controlled transform. This is the counterpart
of `BDan.coreOfListOf_isOfOrderGe_of_bridge` and `coreFamOn_isOfOrderGe` **without** the first
blow-up.

The argument: the run one dimension down on the trace `U ∩ H⁺` is of order `≥ 1` for the restricted
triple (the order clause of the lower functor, a hypothesis here), pulled back along the bridge to
the bundled trace; [Kol07, Corollary 85] with the hypersurface in the boundary
(`FiniteSuccession.pushforward_isOfOrderGe_append`: `𝓘|_U` is trivially `D`-balanced at the mark `1`
and of order `≤ 1`) pushes the order clause forward, with the boundary `(E − E^j) + Z_{-1} + H⁺`:
the member `E^j = Z_{-1} ⊔ H⁺` is read as its two clopen pieces (`stopLocus_union_hplus`), the
stopped piece `Z_{-1}` being a closed hypersurface in proper normal crossings with `E − E^j`
(`hasSncWithProper_stopLocus`) and disjoint from `H⁺` (`hasSncWithProper_append_of_notMem`), so that
the reduced ideal sheaves of `(E − E^j) + Z_{-1} + H⁺` and of `E` coincide
(`idealSheaf_congr_support`: the same support), and the trace of `Z_{-1}` on `H⁺` is empty (the
ideal sheaf of the lower boundary is unchanged). The succession of the pushed-forward list is the
push-forward of the succession (`pushforwardBridge`), and the deletion of empty blow-ups keeps the
order clause (`isOfOrderGe_eraseEmpty`).
-/

public section

noncomputable section

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
  (R : AnalyticFamilyFunctor.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
    (AnalyticTriple.BMOClass 1))
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (j : T.F.ι)

/-! ### The stopped locus as a closed hypersurface in proper normal crossings with `E − E^j` -/

theorem stopLocus_subset : stopLocus T j ⊆ T.F.hyp j := fun _ hx => hx.1

theorem mem_stopLocus_of_notMem_hplus {x : M} (hx : x ∈ T.F.hyp j) (h : x ∉ hplus T j) :
    x ∈ stopLocus T j :=
  by_contra fun hnot => h ⟨hx, hnot⟩

/-- `E^j = Z_{-1} ⊔ H⁺`. -/
theorem stopLocus_union_hplus : stopLocus T j ∪ hplus T j = T.F.hyp j :=
  Set.union_sdiff_cancel (stopLocus_subset T j)

/-- An adapted chart of `E^j`, restricted to the complement of `H⁺`, is an adapted chart of the
stopped locus (the mirror image of `isAdaptedChart_hplus_restrOpen`). -/
theorem isAdaptedChart_stopLocus_restrOpen {φ : OpenPartialHomeomorph M (Fin n → 𝕜)}
    {σ : Fin 1 ↪ Fin n}
    (h : IsAdaptedChart (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (T.F.hyp j) φ σ) :
    IsAdaptedChart (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (stopLocus T j)
      (φ.restrOpen (hplus T j)ᶜ (isClosed_hplus T j).isOpen_compl) σ := by
  refine ⟨(h.restrOpen' _ (isClosed_hplus T j).isOpen_compl).1, fun x hx => ?_⟩
  rw [OpenPartialHomeomorph.restrOpen_source] at hx
  change x ∈ stopLocus T j ↔ ∀ i, ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜) (φ x) (σ i) = 0
  rw [← h.2 x hx.1]
  exact ⟨fun hxZ => hxZ.1, fun hxE => mem_stopLocus_of_notMem_hplus T j hxE hx.2⟩

/-- The boundary `E − E^j` has simple normal crossings with the stopped locus, properly (the mirror
image of `hasSncWithProper_hplus`: the proper charts of `E^j` restricted off `H⁺`). -/
theorem hasSncWithProper_stopLocus :
    (T.F.emptyMember j).HasSncWithProper (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (stopLocus T j) 1 := by
  intro a ha
  obtain ⟨φ, σ, cidx, hφ, hc, hproper⟩ := T.isSnc.hasSncWithProper_emptyMember j a ha.1
  exact ⟨φ.restrOpen (hplus T j)ᶜ (isClosed_hplus T j).isOpen_compl, σ, cidx,
    isAdaptedChart_stopLocus_restrOpen T j hφ, hc.restrOpen _ fun h => h.2 ha, hproper⟩

section Pullback

variable {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (g : AnalyticMap N M)
  (hg : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g)

/-- The stopped locus pulls back along local analytic isomorphisms (`Zminus1_comap`). -/
theorem stopLocus_pullback : stopLocus (T.pullback g hg) j = ⇑g ⁻¹' stopLocus T j :=
  BD.Zminus1_comap g hg T.I 1 (T.isSnc.1 j)

end Pullback

/-! ### The order clause -/

section Order

variable (hT : AnalyticTriple.BMOClass 1 T) (hmax : ∀ y, T.I.ord y ≤ 1)
  (hRo : ∀ {N : AnalyticManifold.{u} 𝕜 (Fin (n - 1) → 𝕜)}
    (T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) N)
    (hT' : AnalyticTriple.BMOClass 1 T') (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))),
    ((R.fam T' hT').seqOn U' hU').toSuccession.IsOfOrderGe
      (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).I 1
      (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).F.idealSheaf)
  (U : Opens M) (hU : IsCompact (closure (U : Set M)))

/-- The restriction `g|_{H⁺}` for the open inclusion `g = (U ⊆ M)` is the inclusion of the trace
`U ∩ H⁺` composed with the bridge (both maps are the inclusion of the subtype). -/
theorem hplusRestrictMap_inclusion_eq :
    hplusRestrictMap T j (M.inclusion U) (isLocalDiffeomorph_inclusion M U) =
      ((isClosedSubmanifold_hplus T j).toAnalyticManifold.inclusion
          ((isClosedSubmanifold_hplus T j).preimageOpens U)).comp
        ⟨((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm,
          ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.contMDiff⟩ :=
  ContMDiffMap.ext fun _ => Subtype.ext rfl

include hmax hRo in
/-- **The modified core is of order `≥ 1`** ([Kol07, Definition 66 (2′)–(4′)] at the mark `1`, on
each open; the counterpart of `coreFamOn_isOfOrderGe` without the first blow-up): the order clause
of the run one dimension down on the trace, pulled back along the bridge, pushed forward by
[Kol07, Corollary 85] with `E^j = Z_{-1} ⊔ H⁺` read as two boundary members, the deletion of empty
blow-ups keeping the clause. -/
theorem coreModOn_isOfOrderGe :
    (coreModOn R T j hT U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf := by
  have hincl : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (M.inclusion U) :=
    isLocalDiffeomorph_inclusion M U
  have hSU : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (⇑(M.inclusion U) ⁻¹' hplus T j) 1 :=
    isClosedSubmanifold_preimage_hplus T j (M.inclusion U) hincl
  have hZ' : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (⇑(M.inclusion U) ⁻¹' stopLocus T j) 1 :=
    (BD.isClosedSubmanifold_Zminus1 T 1 j).preimage_of_isLocalDiffeomorph hincl
  -- the lower run's order clause on the trace, pulled back along the bridge
  have hL := hRo (restrictedTripleMod T j) (bmoClass_restrictedTripleMod T j hT)
    ((isClosedSubmanifold_hplus T j).preimageOpens U)
    ((isClosedSubmanifold_hplus T j).isCompact_closure_preimageOpens U hU)
  have hL' := AnalyticTriple.isOfOrderGe_pullback _ 1 _ hL
    ⟨((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm,
      ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.contMDiff⟩
    ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.isLocalDiffeomorph
  -- the twice-pulled-back triple is the restricted triple of `T|_U` on the trace of `H⁺`
  have htr : ((restrictedTripleMod T j).pullback
        ((isClosedSubmanifold_hplus T j).toAnalyticManifold.inclusion
          ((isClosedSubmanifold_hplus T j).preimageOpens U))
        (isLocalDiffeomorph_inclusion _ _)).pullback
        ⟨((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm,
          ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.contMDiff⟩
        ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.isLocalDiffeomorph =
      restrictedTripleModOf (T.pullback (M.inclusion U) hincl) j hSU
        (hplus_pullback T j (M.inclusion U) hincl).symm := by
    refine AnalyticTriple.IsPullbackOf.eq
      (((restrictedTripleMod T j).isPullbackOf_pullback _ _).comp
        (((restrictedTripleMod T j).pullback _ _).isPullbackOf_pullback _ _)) ?_
    have h := restrictedTripleModOf_isPullbackOf T j (M.inclusion U) hincl
    rw [hplusRestrictMap_inclusion_eq T j U] at h
    exact h
  replace hL' := htr ▸ hL'
  -- the lower boundary with the (empty) trace of the stopped locus appended
  have hFtr : (restrictedTripleModOf (T.pullback (M.inclusion U) hincl) j hSU
        (hplus_pullback T j (M.inclusion U) hincl).symm).F.idealSheaf (𝕜 := 𝕜)
          (E := Fin (n - 1) → 𝕜) =
      (hSU.traceFamily (((T.pullback (M.inclusion U) hincl).F.emptyMember j).append
        (⇑(M.inclusion U) ⁻¹' stopLocus T j))).idealSheaf (𝕜 := 𝕜) (E := Fin (n - 1) → 𝕜) := by
    apply HypersurfaceFamily.idealSheaf_congr_support
    change (hSU.traceFamily ((T.pullback (M.inclusion U) hincl).F.emptyMember j)).support = _
    rw [IsClosedSubmanifold.traceFamily_support, IsClosedSubmanifold.traceFamily_support,
      HypersurfaceFamily.support_append]
    ext p
    constructor
    · intro hp
      exact Or.inl hp
    · rintro (hp | hp)
      · exact hp
      · exact absurd hp (p : ⇑(M.inclusion U) ⁻¹' hplus T j).2.2
  rw [hFtr] at hL'
  -- Corollary 85 with the hypersurface `H⁺` in the boundary
  have hmax' : ∀ y, (T.pullback (M.inclusion U) hincl).I.ord y ≤ 1 := fun y =>
    (IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ T.I (hincl y)).trans_le (hmax _)
  have hI : (T.pullback (M.inclusion U) hincl).I.IsDBalanced 1 := IdealSheaf.isDBalanced_one _
  have hF : (((T.pullback (M.inclusion U) hincl).F.emptyMember j).append
      (⇑(M.inclusion U) ⁻¹' stopLocus T j)).IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) := by
    have h := hasSncWithProper_stopLocus (T.pullback (M.inclusion U) hincl) j
    rw [stopLocus_pullback T j (M.inclusion U) hincl] at h
    exact HypersurfaceFamily.isSnc_append_of_hasSncWithProper
      ((T.pullback (M.inclusion U) hincl).isSnc.emptyMember j) hZ' h
  have hFS : (((T.pullback (M.inclusion U) hincl).F.emptyMember j).append
      (⇑(M.inclusion U) ⁻¹' stopLocus T j)).HasSncWithProper
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (⇑(M.inclusion U) ⁻¹' hplus T j) 1 := by
    have h := hasSncWithProper_hplus (T.pullback (M.inclusion U) hincl) j
    rw [hplus_pullback T j (M.inclusion U) hincl] at h
    exact HypersurfaceFamily.hasSncWithProper_append_of_notMem h fun _ ha haZ => ha.2 haZ
  have hP := FiniteSuccession.pushforward_isOfOrderGe_append hSU _ hI hmax' hF hFS hL'
  -- the boundary `(E − E^j) + Z_{-1} + H⁺` is `E`
  have hbound : ((((T.pullback (M.inclusion U) hincl).F.emptyMember j).append
        (⇑(M.inclusion U) ⁻¹' stopLocus T j)).append
        (⇑(M.inclusion U) ⁻¹' hplus T j)).idealSheaf (𝕜 := 𝕜) (E := Fin n → 𝕜) =
      (T.pullback (M.inclusion U) hincl).F.idealSheaf (𝕜 := 𝕜) (E := Fin n → 𝕜) := by
    apply HypersurfaceFamily.idealSheaf_congr_support
    rw [HypersurfaceFamily.support_append, HypersurfaceFamily.support_append, Set.union_assoc,
      ← Set.preimage_union, stopLocus_union_hplus]
    exact HypersurfaceFamily.support_emptyMember_union (T.pullback (M.inclusion U) hincl).F j
  rw [hbound] at hP
  -- assemble: the list push-forward's succession is the succession's push-forward
  have hLne : ((coreModTrace R T j hT U hU).pullback
      ⟨((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm,
        ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.contMDiff⟩
      ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.isLocalDiffeomorph
      ).NoEmptyCenters :=
    BlowUpSequence.noEmptyCenters_pullback_of_surjective _ _ _
      ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.surjective
      ((R.fam (restrictedTripleMod T j) (bmoClass_restrictedTripleMod T j hT)).noEmptyCenters _ _)
  unfold coreModOn
  refine BlowUpSequence.isOfOrderGe_eraseEmpty _ _ 1 (T.pullback (M.inclusion U) hincl).isSnc ?_
  rw [BlowUpSequence.pushforwardRestrict_eq,
    pushforwardBridge (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) _ _ hLne]
  exact hP

end Order

end Hironaka.Manifold.BMOmod

end
