/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.Basic
import Hironaka.AnalyticSpace.ClosedSubspace
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.IdealSheaf.Vanishing
import Hironaka.Manifold.Snc.NonSingular
import Hironaka.Resolution.Analytic.Functor.LocalIsoTools
import Hironaka.Resolution.Analytic.Functor.PullbackSequence
import Hironaka.Resolution.Analytic.MaximalContact.StalkEquiv
import Hironaka.Resolution.Analytic.MaximalContact.Theorem97Induction
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The embedded desingularization: the normal-crossings clause, and the value on a smooth subspace

The first clauses of [Wlo09, Theorem 2.0.2] for the embedded desingularization functor
`bedanFamOfInput bmod n` of `Hironaka/Resolution/Analytic/Wlo09/Basic.lean`, per relatively compact
open `U`, from the fields of the modified marked resolution `bmod n`:

* clause (1): the value on `U` is, by the order clause `isOfOrderGe` of `bmod n`, a smooth
  blow-up sequence of order `≥ 1` for the restricted `(M, 𝓘, 1, E)`; on `DomBEDan` the boundary
  `E` has no member, so its reduced ideal sheaf is the unit ideal, and the exceptional divisors
  form a simple normal crossing family at every stage with which every centre has simple normal
  crossings (`bedanFamOfInput_isSnc_totalTransformSeq`, `bedanFamOfInput_hasSncWith_center`, from
  `isSnc_totalTransformSeq` and `hasSncWith_totalTransformSeq_center`);
* the value on an open on which `Y` is non-singular is the empty sequence
  (`bedanFamOfInput_eq_nil_of_sing_eq_empty`): a first centre would be a nonempty subset of
  `supp(𝓘, 1) = Y ∩ U` (`noEmptyCenters`, `center_mem_support`), every point of which is stopped
  at stage `0` by the stop rule `stopped_never_blownUp` (at a regular point the ideal is a
  coordinate ideal, and there is no divisor). This is Włodarczyk's stop rule, "if `I′ = (u)` is
  the ideal of a smooth hypersurface of maximal contact the algorithm is stopped" (the proof of
  [Wlo09, Theorem 7.4.1]), applied at once;
* its local form (`bedanFamOfInput_center_disjoint_fiber_near_regular`): for an open `V` of the
  ambient manifold on which `Y` is non-singular, no centre of the value on `U` lies over `U ∩ V`,
  by the previous item on `U ⊓ V` and the compatibility of the family under restriction to a
  smaller open (`compat`, the extension property of [Wlo09, Definition 3.2.6]): the value on
  `U ⊓ V` is the empty sequence, so every centre of the pull-back of the value on `U` to `U ⊓ V`
  is empty, while a centre point over `U ∩ V` would lift to one.

Also here: the regular points of the closed subspace `V(J)` are the points where the quotient
stalk `𝒪_p/J_p` is a regular local ring (`mem_reg_toAnalyticSpace_iff`), this transports along
local analytic isomorphisms and passes to smaller opens, and a list of centres whose empty
blow-ups erase to the empty list has only empty centres. The algebraic counterparts of clause (1)
are `BED_isSnc_totalTransformSeq` and `BED_hasSncWith_center`.

The local form is the input for clause (2) of [Wlo09, Theorem 2.0.2], that no centre lies over a
simple point of `Y`, proved in `Hironaka/Resolution/Analytic/Wlo09/Assembly.lean`.
-/

public section

open Set Topology TopologicalSpace AnalyticManifold Hironaka.Manifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

section EmptyFamily

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

omit [TopologicalSpace M] in
/-- A hypersurface family without members has empty support. -/
theorem _root_.Manifold.HypersurfaceFamily.support_eq_empty_of_isEmpty (F : HypersurfaceFamily M)
    [IsEmpty F.ι] : F.support = ∅ := by
  simp [HypersurfaceFamily.support]

/-- The reduced ideal sheaf of a hypersurface family without members is the unit ideal sheaf. -/
theorem _root_.Manifold.HypersurfaceFamily.idealSheaf_eq_top_of_isEmpty (F : HypersurfaceFamily M)
    [IsEmpty F.ι] :
    F.idealSheaf (𝕜 := 𝕜) (E := E) = ⊤ := by
  unfold HypersurfaceFamily.idealSheaf
  split_ifs with h
  · apply IdealSheaf.ext
    intro x
    rw [IdealSheaf.stalkIdeal_ofStalks, IdealSheaf.stalkIdeal_top]
    apply vanishingStalk_eq_top_of_notMem_closure
    rw [F.support_eq_empty_of_isEmpty, closure_empty]
    exact notMem_empty x
  · rfl

end EmptyFamily

section Clauses

variable (𝕜 : Type) [RCLike 𝕜] (bmod : ∀ n : ℕ, BMOmodFam.{u} 𝕜 n) (n : ℕ)
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
  (U : Opens M) (hU : IsCompact (closure (U : Set M)))

/-- The order clause `isOfOrderGe` of the modified marked resolution, for the embedded
desingularization functor and with the unit boundary: on `DomBEDan` the restricted divisor has no
member. -/
theorem bedanFamOfInput_isOfOrderGe :
    (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1 ⊤ := by
  have h := (bmod n).isOfOrderGe T (DomBEDan.bmoClass_one 𝕜 hT) U hU
  have : IsEmpty (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.ι := hT.1
  rwa [HypersurfaceFamily.idealSheaf_eq_top_of_isEmpty] at h

/-- Clause (1) of [Wlo09, Theorem 2.0.2] per open, first half: the exceptional divisors form a
simple normal crossing family at every stage. -/
theorem bedanFamOfInput_isSnc_totalTransformSeq
    (i : Fin ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.length + 1)) :
    ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.totalTransformSeq i).IsSnc
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) :=
  FiniteSuccession.isSnc_totalTransformSeq (bedanFamOfInput_isOfOrderGe 𝕜 bmod n T hT U hU) i

/-- Clause (1) of [Wlo09, Theorem 2.0.2] per open, second half: every centre has simple normal
crossings with the exceptional divisors of its stage. -/
theorem bedanFamOfInput_hasSncWith_center
    (i : Fin (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.length) :
    ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.totalTransformSeq
        i.castSucc).HasSncWith (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.center i).support
      ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.codim i) :=
  FiniteSuccession.hasSncWith_totalTransformSeq_center
    (bedanFamOfInput_isOfOrderGe 𝕜 bmod n T hT U hU) i

end Clauses

section Pin

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

/-- The empty-boundary form of the stop predicate `IsSmoothTransversalIdealAt` of the modified
marked resolution: at a point where `𝒪/J` is regular, `J` is locally the ideal of a smooth
submanifold, and with no divisor through the point there is nothing to be transversal to. -/
theorem _root_.Manifold.HypersurfaceFamily.isSmoothTransversalIdealAt_of_isEmpty {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(𝕜, E) ω M] (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (F : HypersurfaceFamily M) [IsEmpty F.ι]
    (J : Manifold.IdealSheaf (structureSheaf 𝕜 E M)) {x : M}
    (hreg : IsRegularLocalRing ((structureSheaf 𝕜 E M).presheaf.stalk x ⧸ J.stalkIdeal x)) :
    F.IsSmoothTransversalIdealAt ψ J x := by
  obtain ⟨c, φ, σ, hφ, hx, hJ⟩ :=
    exists_adaptedChart_of_isRegularLocalRing_quotient (ψ := ψ) J hreg
  exact ⟨c, φ, σ, fun j => isEmptyElim j.1, ⟨hφ.1, hx, fun j => isEmptyElim j.1,
    fun j => isEmptyElim j.1⟩, hJ, fun j => isEmptyElim j.1⟩

/-- A point of the support of `J` is a simple point of the closed subspace `Sp(A)/J` iff `𝒪_p/J_p`
is regular; when the subspace has no singular point every support point qualifies. -/
theorem isRegularLocalRing_quotient_of_sing_eq_empty {A : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (J : AnalyticManifold.IdealSheaf A)
    (h : (IdealSheaf.toAnalyticSpace J).singularLocus = ∅) {p : A}
    (hp : p ∈ J.support) :
    IsRegularLocalRing ((structureSheaf 𝕜 (Fin n → 𝕜) A).presheaf.stalk p ⧸ J.stalkIdeal p) := by
  have hreg : (IdealSheaf.toAnalyticSpace J).regularLocus = Set.univ := by
    unfold AnalyticSpace.singularLocus at h
    exact Set.compl_empty_iff.mp h
  have hy : (⟨p, hp⟩ : IdealSheaf.toAnalyticSpace J) ∈
      (IdealSheaf.toAnalyticSpace J).regularLocus := by
    rw [hreg]; exact Set.mem_univ _
  obtain ⟨hp', hr⟩ := (AnalyticSpace.mem_reg_closedSubspace_iff _ _ _).mp hy
  have hr' : IsRegularLocalRing ((AnalyticSpace.QuotientSpace.presheafCommRing
      (AnalyticSpace.toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) A).toLocallyRingedSpace
      J).stalk ⟨p, hp'⟩) := hr
  exact IsRegularLocalRing.of_ringEquiv (AnalyticSpace.QuotientSpace.stalkEquiv
    (AnalyticSpace.toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) A).toLocallyRingedSpace
    J ⟨p, hp'⟩)

end Pin

section PinValue

variable (𝕜 : Type) [RCLike 𝕜] (bmod : ∀ n : ℕ, BMOmodFam.{u} 𝕜 n) (n : ℕ)
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
  (U : Opens M) (hU : IsCompact (closure (U : Set M)))

/-- Over a relatively compact open on which `Y` is non-singular, the embedded desingularization is
the empty sequence: its first centre would be a nonempty subset of `supp(𝓘, 1) = Y ∩ U`
(`noEmptyCenters`, `center_mem_support`), every point of which is stopped at stage `0` by the
stop rule `stopped_never_blownUp` (at a regular point the ideal is a coordinate ideal, and there
is no divisor). Włodarczyk's stop rule (the proof of [Wlo09, Theorem 7.4.1]), applied at once.
-/
theorem bedanFamOfInput_eq_nil_of_sing_eq_empty
    (h : (IdealSheaf.toAnalyticSpace
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I).singularLocus = ∅) :
    ((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU = BlowUpSequence.nil (M.restrict U) := by
  apply BlowUpSequence.eq_nil_of_length_eq_zero
  by_contra hne
  have hpos : 0 < (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.length :=
    Nat.pos_of_ne_zero hne
  have hC : ¬ (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.IsEmptyAt ⟨0, hpos⟩ :=
    ((bedanFamOfInput 𝕜 bmod n).fam T hT).noEmptyCenters U hU ⟨0, hpos⟩
  obtain ⟨y, hy⟩ : ∃ y, ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.center
      ⟨0, hpos⟩).stalkIdeal y ≠ ⊤ := by
    by_contra hall
    refine hC (IdealSheaf.ext fun y => ?_)
    rw [IdealSheaf.stalkIdeal_top]
    exact not_not.mp (not_exists.mp hall y)
  have hyc : y ∈ ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.center
      ⟨0, hpos⟩).support := hy
  have hord := (bmod n).center_mem_support T (DomBEDan.bmoClass_one 𝕜 hT) U hU ⟨0, hpos⟩ hyc
  have hord' : (1 : ℕ∞) ≤
      ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.markedTransformSeq
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      (Fin.castSucc ⟨0, hpos⟩)).ord y := hord
  have hne0 : ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.markedTransformSeq
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      (Fin.castSucc ⟨0, hpos⟩)).ord y ≠ 0 := Order.one_le_iff_ne_zero.mp hord'
  have hyJ0 : y ∈
      ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.markedTransformSeq
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      (Fin.castSucc ⟨0, hpos⟩)).support :=
    not_not.mp ((not_congr
      ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.markedTransformSeq
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      (Fin.castSucc ⟨0, hpos⟩)).ord_eq_zero_iff).mp hne0)
  have hyJ : y ∈ (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I.support := hyJ0
  have : IsEmpty (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.ι := hT.1
  have hsm := HypersurfaceFamily.isSmoothTransversalIdealAt_of_isEmpty
    (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
    (isRegularLocalRing_quotient_of_sing_eq_empty _ h hyJ)
  exact (bmod n).stopped_never_blownUp T (DomBEDan.bmoClass_one 𝕜 hT) U hU 0 0 hpos y hsm
    (fun j => isEmptyElim
      (α := (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.ι) j) y rfl hyc

end PinValue

section Restriction

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

/-- An ideal is the unit ideal iff its image under a bijective ring homomorphism is. -/
theorem Ideal.map_eq_top_iff_of_bijective {R S F : Type*} [CommRing R] [CommRing S]
    [FunLike F R S] [RingHomClass F R S] (e : F) (he : Function.Bijective e) (I : Ideal R) :
    I.map e = ⊤ ↔ I = ⊤ := by
  constructor
  · intro h
    have := Ideal.comap_map_of_bijective e he (I := I)
    rw [h, Ideal.comap_top] at this
    exact this.symm
  · rintro rfl
    exact Ideal.map_top _

/-- Regularity of the quotient stalk `𝒪_b / (h^*J)_b` transports along a local analytic
isomorphism `h` to `𝒪_{h b} / J_{h b}` (the stalk isomorphism `germAlgEquiv`). -/
theorem isRegularLocalRing_quotient_stalkIdeal_comap_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {M N : AnalyticManifold.{u} 𝕜 E} (J : AnalyticManifold.IdealSheaf M)
    (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (b : N) :
    IsRegularLocalRing ((structureSheaf 𝕜 E N).presheaf.stalk b ⧸
        (J.pullback h h.contMDiff).stalkIdeal b) ↔
      IsRegularLocalRing ((structureSheaf 𝕜 E M).presheaf.stalk (h b) ⧸ J.stalkIdeal (h b)) := by
  have e : (structureSheaf 𝕜 E M).presheaf.stalk (h b) ⧸ J.stalkIdeal (h b) ≃+*
      (structureSheaf 𝕜 E N).presheaf.stalk b ⧸
          (J.pullback h h.contMDiff).stalkIdeal b :=
    Ideal.quotientEquiv _ _ (germAlgEquiv h (hh b)).toRingEquiv
      (stalkIdeal_comap_eq_map_germAlgEquiv h hh J b)
  exact ⟨fun hr => IsRegularLocalRing.of_ringEquiv e.symm,
    fun hr => IsRegularLocalRing.of_ringEquiv e⟩

/-- The cosupport of a pulled-back ideal sheaf along a local analytic isomorphism is the preimage
of the cosupport. -/
theorem mem_cosupport_comap_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {M N : AnalyticManifold.{u} 𝕜 E} (J : AnalyticManifold.IdealSheaf M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (b : N) :
    b ∈ (J.pullback h h.contMDiff).support ↔ h b ∈ J.support := by
  change (J.pullback h h.contMDiff).stalkIdeal b ≠ ⊤ ↔ J.stalkIdeal (h b) ≠ ⊤
  rw [stalkIdeal_comap_eq_map_germAlgEquiv h hh J b]
  exact not_congr (Ideal.map_eq_top_iff_of_bijective (germAlgEquiv h (hh b))
    (germAlgEquiv h (hh b)).bijective _)

/-- A point of the closed subspace `Sp(A)/J` is regular iff the quotient stalk `𝒪_p / J_p` at its
image is a regular local ring (through `QuotientSpace.stalkEquiv`). -/
theorem mem_reg_toAnalyticSpace_iff {A : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (J : AnalyticManifold.IdealSheaf A) (y : IdealSheaf.toAnalyticSpace J) :
    y ∈ (IdealSheaf.toAnalyticSpace J).regularLocus ↔
      IsRegularLocalRing
        ((structureSheaf 𝕜 (Fin n → 𝕜) A).presheaf.stalk y.1 ⧸ J.stalkIdeal y.1) := by
  refine (AnalyticSpace.mem_reg_closedSubspace_iff
    (AnalyticSpace.toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) A) J y).trans ?_
  constructor
  · rintro ⟨hp, hr⟩
    have hr' : IsRegularLocalRing ((AnalyticSpace.QuotientSpace.presheafCommRing
        (AnalyticSpace.toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          A).toLocallyRingedSpace J).stalk ⟨y.1, hp⟩) := hr
    exact IsRegularLocalRing.of_ringEquiv (AnalyticSpace.QuotientSpace.stalkEquiv
      (AnalyticSpace.toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) A).toLocallyRingedSpace
      J ⟨y.1, hp⟩)
  · intro hr
    refine ⟨y.2, ?_⟩
    have hr' : IsRegularLocalRing (AnalyticSpace.QuotientSpace.fiber
        (AnalyticSpace.toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          A).toLocallyRingedSpace J y) := hr
    exact IsRegularLocalRing.of_ringEquiv (AnalyticSpace.QuotientSpace.stalkEquiv
      (AnalyticSpace.toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) A).toLocallyRingedSpace
      J y).symm

/-- `(Sp(A)/J).singularLocus = ∅` iff every support point has a regular quotient stalk. -/
theorem sing_toAnalyticSpace_eq_empty_iff {A : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (J : AnalyticManifold.IdealSheaf A) :
    (IdealSheaf.toAnalyticSpace J).singularLocus = ∅ ↔
      ∀ p (_ : p ∈ J.support),
        IsRegularLocalRing
          ((structureSheaf 𝕜 (Fin n → 𝕜) A).presheaf.stalk p ⧸ J.stalkIdeal p) := by
  unfold AnalyticSpace.singularLocus
  rw [Set.compl_empty_iff, Set.eq_univ_iff_forall]
  constructor
  · intro h p hp
    exact (mem_reg_toAnalyticSpace_iff J ⟨p, hp⟩).mp (h ⟨p, hp⟩)
  · intro h y
    exact (mem_reg_toAnalyticSpace_iff J y).mpr (h y.1 y.2)

/-- Non-singularity of the restricted closed subspace passes to a smaller open: `Y ∩ W` is
non-singular when `Y ∩ V` is, for `W ≤ V`. -/
theorem sing_comap_inclusion_eq_empty_of_le {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (J : AnalyticManifold.IdealSheaf M) {W V : Opens M} (hWV : W ≤ V)
    (hV : (IdealSheaf.toAnalyticSpace
      (J.pullback _ (M.inclusion V).contMDiff)).singularLocus = ∅) :
    (IdealSheaf.toAnalyticSpace
      (J.pullback _ (M.inclusion W).contMDiff)).singularLocus = ∅ := by
  rw [sing_toAnalyticSpace_eq_empty_iff] at hV ⊢
  intro q hq
  have hq' : (⟨q.1, hWV q.2⟩ : M.restrict V) ∈
      (J.pullback _ (M.inclusion V).contMDiff).support :=
    (mem_cosupport_comap_iff J (M.inclusion V) (isLocalDiffeomorph_inclusion M V)
      ⟨q.1, hWV q.2⟩).mpr
      ((mem_cosupport_comap_iff J (M.inclusion W) (isLocalDiffeomorph_inclusion M W) q).mp hq)
  have hV' := (isRegularLocalRing_quotient_stalkIdeal_comap_iff J (M.inclusion V)
    (isLocalDiffeomorph_inclusion M V) ⟨q.1, hWV q.2⟩).mp (hV _ hq')
  exact (isRegularLocalRing_quotient_stalkIdeal_comap_iff J (M.inclusion W)
    (isLocalDiffeomorph_inclusion M W) q).mpr hV'

end Restriction

section EraseEmptyNil

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- A list whose empty blow-ups erase to the empty list has only empty centres. -/
theorem _root_.AnalyticManifold.BlowUpSequence.isEmptyAt_of_eraseEmpty_eq_nil
    {M : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M) (h : L.eraseEmpty = BlowUpSequence.nil M)
        (i : Fin L.toSuccession.length) :
    L.toSuccession.IsEmptyAt i := by
  induction L with
  | nil => exact i.elim0
  | cons hY rest ih =>
    rename_i Y c
    by_cases hY₀ : Y = ∅
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact (FiniteSuccession.isEmptyAt_cons_zero hY rest.toSuccession).mpr hY₀
      · rw [BlowUpSequence.eraseEmpty_cons_of_eq_empty hY rest hY₀] at h
        have hlen : rest.eraseEmpty.toSuccession.length = 0 := by
          have := congrArg BlowUpSequence.length h
          rwa [BlowUpSequence.length_map] at this
        exact (FiniteSuccession.isEmptyAt_cons_succ hY rest.toSuccession j).mpr
          (ih (BlowUpSequence.eq_nil_of_length_eq_zero _ hlen) j)
    · rw [BlowUpSequence.eraseEmpty_cons_of_ne_empty hY rest hY₀] at h
      exact absurd h (by simp)

end EraseEmptyNil

section CPrime

variable (𝕜 : Type) [RCLike 𝕜] (bmod : ∀ n : ℕ, BMOmodFam.{u} 𝕜 n) (n : ℕ)
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
  (U : Opens M) (hU : IsCompact (closure (U : Set M)))

/-- The local form of the previous theorem: for an open `V` of the ambient manifold on which `Y` is
non-singular, no centre of the value on `U` lies over `U ∩ V`. By
`bedanFamOfInput_eq_nil_of_sing_eq_empty` on `U ⊓ V` and the compatibility of the family under
restriction (`compat`, the extension
property of [Wlo09, Definition 3.2.6]): the value on `U ⊓ V` is the empty sequence, so every
centre of the pull-back of the value on `U` to `U ⊓ V` is empty, while a centre point over `U ∩ V`
would lift to one. -/
theorem bedanFamOfInput_center_disjoint_fiber_near_regular (V : Opens M)
    (hV : (IdealSheaf.toAnalyticSpace
      (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).I).singularLocus = ∅)
    (i : Fin (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.length)
    (x : (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.stage i.castSucc)
    (hx : x ∈
      ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.center i).support) :
    M.inclusion U ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.stageMap
      i.castSucc x) ∉ (V : Set M) := by
  intro hxV
  have hW : IsCompact (closure ((U ⊓ V : Opens M) : Set M)) :=
    hU.of_isClosed_subset isClosed_closure (closure_mono fun p hp => hp.1)
  have hSingW : (IdealSheaf.toAnalyticSpace (T.pullback (M.inclusion (U ⊓ V))
      (isLocalDiffeomorph_inclusion M (U ⊓ V))).I).singularLocus = ∅ :=
    sing_comap_inclusion_eq_empty_of_le T.I inf_le_right hV
  have hnil := bedanFamOfInput_eq_nil_of_sing_eq_empty 𝕜 bmod n T hT (U ⊓ V) hW hSingW
  have hcompat := ((bedanFamOfInput 𝕜 bmod n).fam T hT).compat (U ⊓ V) U hW hU inf_le_left
  rw [hnil] at hcompat
  have hempty := fun j => BlowUpSequence.isEmptyAt_of_eraseEmpty_eq_nil _ hcompat.symm j
  have hxr : (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.stageMapAux i.1
      (Nat.lt_succ_of_lt i.2) x ∈ Set.range (M.restrictLE (inf_le_left : U ⊓ V ≤ U)) := by
    rw [range_restrictLE]
    exact ⟨((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.stageMap
      i.castSucc x).2, hxV⟩
  obtain ⟨q, hq⟩ := BlowUpSequence.mem_range_pullbackLift_of_stageMap_mem
    (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU) (M.restrictLE inf_le_left)
    (isLocalDiffeomorph_restrictLE inf_le_left) i.1 (Nat.lt_succ_of_lt i.2)
    (Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt i.2)
      (congrArg (· + 1) (BlowUpSequence.length_pullback _ _ _)).symm) x hxr
  have htop : ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).pullback
      (M.restrictLE inf_le_left) (isLocalDiffeomorph_restrictLE inf_le_left)).toSuccession.center
      ⟨i.1, Nat.lt_of_lt_of_eq i.2 (BlowUpSequence.length_pullback _ _ _).symm⟩ = ⊤ :=
    hempty ⟨i.1, Nat.lt_of_lt_of_eq i.2 (BlowUpSequence.length_pullback _ _ _).symm⟩
  rw [BlowUpSequence.center_pullback] at htop
  have h1 : (Manifold.IdealSheaf.pullback _ ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U
      hU).pullbackLift (M.restrictLE inf_le_left)
        (isLocalDiffeomorph_restrictLE inf_le_left) i.castSucc).contMDiff
      ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.center i)).stalkIdeal q =
      (⊤ : AnalyticManifold.IdealSheaf _).stalkIdeal q :=
    congrArg (fun K : AnalyticManifold.IdealSheaf _ => K.stalkIdeal q) htop
  rw [stalkIdeal_comap_eq_map_germAlgEquiv _ (BlowUpSequence.isLocalDiffeomorph_pullbackLift
    (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU) (M.restrictLE inf_le_left)
    (isLocalDiffeomorph_restrictLE inf_le_left) i.castSucc) _ q,
    IdealSheaf.stalkIdeal_top] at h1
  have h2 := (Ideal.map_eq_top_iff_of_bijective _ (germAlgEquiv _ _).bijective _).mp h1
  apply hx
  rw [← hq]
  exact h2

end CPrime

end Hironaka.Manifold
