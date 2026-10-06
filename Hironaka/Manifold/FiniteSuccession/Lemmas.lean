/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Basic
public import Hironaka.Manifold.FiniteSuccession.Cons
import Hironaka.Manifold.BlowUp.Divisor
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.IdealSheaf.Basic
import Hironaka.Manifold.Submanifold.Charts
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Analytic blow-up sequences: recursions, constructors, trivial and empty blow-ups

Basic lemmas on a finite sequence of monoidal transformations `FiniteSuccession` and on the
constructors `FiniteSuccession.nil` and `FiniteSuccession.cons`:

* the accessors satisfy the clauses of [Kol07, Definition 29] definitionally (`X_0 = M`,
  `Π_0 = id`, `Π_{i+1} = Π_i ∘ π_i`, `Π = Π_r`), and the constructor lemmas are `rfl` because
  `cons` puts the head in front of the fields of `rest` by `Fin.cases` over `finStages`;
* the centre `C_i` is the ideal sheaf of its cosupport `Z_i` (`idealSheaf_center`), so the
  witnesses chosen from `isMonoidal` do not enter it;
* equality of sequences built by `cons` is equality of centres (the sense in which a sequence is
  identified with its centres, [Kol07, Warning 20]): the first centre of a `cons` is the ideal
  sheaf of its submanifold, whose cosupport is that submanifold, and the tail is recovered field
  by field from the structure equality (`FiniteSuccession.mk.injEq`, `Fin.cases_succ`);
* trivial and empty blow-ups [Kol07, Warning 20]: an empty centre has empty cosupport, so its
  blowing-up is an isomorphism (`IsBlowUp.exists_diffeomorph_of_empty` at the witnesses of
  `isMonoidal`), as is the blowing-up along a centre of codimension one
  (`exists_diffeomorph_of_codim_one`); the exceptional divisor of an empty blow-up is empty;
* the recursions of the weak and marked transforms [Kol07, Definition 66 (1), (1′)] are
  definitional, and the constructor form of the weak-transform recursion follows by induction on
  the stage.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Manifold
open scoped Manifold ContDiff Topology

universe u

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

section Sequence

variable (S : FiniteSuccession M)

theorem stage_zero : S.stage 0 = M := rfl

theorem stage_succ (i : Fin S.length) : S.stage i.succ = S.later i := rfl

theorem stageMap_zero : S.stageMap 0 = ContMDiffMap.id := rfl

theorem stageMap_succ (i : Fin S.length) :
    S.stageMap i.succ = (S.stageMap i.castSucc).comp (S.map i) := rfl

theorem composite_eq : S.composite = S.stageMap (Fin.last S.length) := rfl

/-- The centre `C_i` is the ideal sheaf `idealSheaf` of the closed submanifold `Z_i = cosupp C_i`
(by the uniqueness of the ideal sheaf of a closed submanifold): the witnesses chosen from
`isMonoidal i` do not enter the value. -/
@[simp]
theorem idealSheaf_center (i : Fin S.length) :
    (S.isClosedSubmanifold_center i).idealSheaf = S.center i :=
  ((S.isIdealSheafOf_center i).eq_idealSheaf (S.isClosedSubmanifold_center i)).symm

end Sequence

/-! ### The cosupport of the unit ideal sheaf and the empty centre -/

/-- The unit ideal sheaf has empty cosupport. -/
@[simp]
theorem _root_.Manifold.IdealSheaf.support_top {X : TopCat}
    {𝒪 : TopCat.Sheaf CommRingCat X} :
    (⊤ : Manifold.IdealSheaf 𝒪).support = ∅ := by
  ext x
  simp only [IdealSheaf.mem_support,
    IdealSheaf.stalkIdeal_top, ne_eq, not_true_eq_false,
    Set.mem_empty_iff_false]

/-- An ideal sheaf with empty cosupport is the unit ideal sheaf. -/
theorem _root_.Manifold.IdealSheaf.eq_top_of_support_eq_empty {X : TopCat}
    {𝒪 : TopCat.Sheaf CommRingCat X} {J : Manifold.IdealSheaf 𝒪}
    (h : J.support = ∅) : J = ⊤ := by
  refine IdealSheaf.ext fun x => ?_
  rw [IdealSheaf.stalkIdeal_top]
  by_contra hx
  refine (Set.eq_empty_iff_forall_notMem.mp h x) ?_
  rwa [IdealSheaf.mem_support]

/-- The unit ideal sheaf is the ideal sheaf of the empty submanifold of any codimension. -/
theorem _root_.Manifold.isIdealSheafOf_empty_top {N : Type u} [TopologicalSpace N]
    [ChartedSpace E N] (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (c : ℕ) :
    IsIdealSheafOf ψ (∅ : Set N) c (⊤ : Manifold.IdealSheaf (structureSheaf 𝕜 E N)) :=
  ⟨IdealSheaf.support_top, fun _ _ _ _ _ ha => ha.elim⟩

section Trivial

variable (S : FiniteSuccession M)

theorem isEmptyAt_iff (i : Fin S.length) : S.IsEmptyAt i ↔ (S.center i).support = ∅ :=
  ⟨fun h => by rw [IsEmptyAt] at h; rw [h]; exact IdealSheaf.support_top,
    fun h => IdealSheaf.eq_top_of_support_eq_empty h⟩

theorem IsEmptyAt.isTrivialAt {i : Fin S.length} (h : S.IsEmptyAt i) : S.IsTrivialAt i := by
  have hs : (S.center i).support = ∅ := (S.isEmptyAt_iff i).mp h
  refine ⟨S.dimAt i, S.chartAt i, ?_, ?_⟩
  · rw [hs]; exact isClosedSubmanifold_empty' _ 1
  · rw [IsEmptyAt] at h
    rw [hs, h]
    exact isIdealSheafOf_empty_top _ 1

theorem IsEmptyAt.exists_diffeomorph_map {i : Fin S.length} (h : S.IsEmptyAt i) :
    ∃ g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (S.stage i.succ) (S.stage i.castSucc) ω,
      ∀ p, g p = S.map i p := by
  have hs : (S.center i).support = ∅ := (S.isEmptyAt_iff i).mp h
  have hb := S.isBlowUp_map i
  rw [hs] at hb
  exact hb.exists_diffeomorph_of_empty

theorem cons_codimOne_exists_diffeomorph {Y : Set M} (hY : IsClosedSubmanifold ψ Y 1) :
    ∃ g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (blowUp ψ hY) M ω, ∀ p, g p = blowUpπ ψ hY p :=
  (isBlowUp_blowUpπ ψ hY).exists_diffeomorph_of_codim_one hY

theorem mem_exceptionalAt_iff (i : Fin S.length) (p : S.stage i.succ) :
    p ∈ S.exceptionalAt i ↔ S.map i p ∈ (S.center i).support := Iff.rfl

theorem IsEmptyAt.exceptionalAt_eq_empty {i : Fin S.length} (h : S.IsEmptyAt i) :
    S.exceptionalAt i = ∅ := by
  rw [exceptionalAt, (S.isEmptyAt_iff i).mp h, Set.preimage_empty]

end Trivial

/-! ### Equality of sequences is equality of centres -/

section Constructors

variable {Y : Set M} {c : ℕ}

/-- The support of the first centre, as a function of the sequence (empty for the empty
sequence), so that it can be applied to both sides of an equality of sequences. -/
def firstCenterSupport : FiniteSuccession M → Set M
  | ⟨0, _, _, _, _⟩ => ∅
  | ⟨_ + 1, _, center, _, _⟩ => (center 0).support

theorem firstCenterSupport_cons (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) : firstCenterSupport (cons ψ hY rest) = Y :=
  hY.cosupport_idealSheaf

theorem center_zero_eq_of_cons_eq {n' : ℕ} {ψ' : E ≃L[𝕜] (Fin n' → 𝕜)} {Y' : Set M} {c' : ℕ}
    (hY : IsClosedSubmanifold ψ Y c) (hY' : IsClosedSubmanifold ψ' Y' c')
    (rest : FiniteSuccession (blowUp ψ hY)) (rest' : FiniteSuccession (blowUp ψ' hY'))
    (h : cons ψ hY rest = cons ψ' hY' rest') : Y = Y' := by
  have := congrArg firstCenterSupport h
  rwa [firstCenterSupport_cons, firstCenterSupport_cons] at this

theorem cons_inj (hY : IsClosedSubmanifold ψ Y c) (rest rest' : FiniteSuccession (blowUp ψ hY))
    (h : cons ψ hY rest = cons ψ hY rest') : rest = rest' := by
  obtain ⟨l, later, center, map, iso⟩ := rest
  obtain ⟨l', later', center', map', iso'⟩ := rest'
  simp only [cons, FiniteSuccession.mk.injEq] at h
  have hl : l + 1 = l' + 1 := h.1
  have hlater := h.2.1
  have hcenter := h.2.2.1
  have hmap := h.2.2.2
  clear h
  have hl' : l = l' := Nat.succ_injective hl
  subst hl'
  have hlater' : later = later' := by
    funext i
    have := congrFun (eq_of_heq hlater) i.succ
    exact this
  subst hlater'
  have hcenter' : center = center' := by
    funext i
    have := congrFun (eq_of_heq hcenter) i.succ
    exact this
  subst hcenter'
  have hmap' : map = map' := by
    funext i
    have := congrFun (eq_of_heq hmap) i.succ
    exact this
  subst hmap'
  rfl

end Constructors

/-! ### The recursions of the weak and marked transforms -/

section Induced

variable (S : FiniteSuccession M)

theorem weakTransformSeq_zero (J : IdealSheaf M) : S.weakTransformSeq J 0 = J := rfl

theorem weakTransformSeq_succ (J : IdealSheaf M) (i : Fin S.length) :
    S.weakTransformSeq J i.succ =
      IdealSheaf.weakTransform (S.map i) (S.weakTransformSeq J i.castSucc) (S.center i) := rfl

theorem markedTransformSeq_zero (J : IdealSheaf M) (m : ℕ) :
    S.markedTransformSeq J m 0 = J := rfl

theorem markedTransformSeq_succ (J : IdealSheaf M) (m : ℕ) (i : Fin S.length) :
    S.markedTransformSeq J m i.succ =
      (MarkedIdealSheaf.birationalTransform (S.isClosedSubmanifold_center i) (S.isBlowUp_map i)
        ⟨S.markedTransformSeq J m i.castSucc, m⟩).I := rfl

variable {Y : Set M} {c : ℕ}

theorem cons_weakTransformSeq_zero (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) (J : IdealSheaf M) :
    (cons ψ hY rest).weakTransformSeq J 0 = J := rfl

/-- The recursion of the weak transforms on the constructor form, at the level of the ℕ-indexed
auxiliary recursion. -/
theorem cons_weakTransformSeqAux_succ (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) (J : IdealSheaf M) :
    ∀ (k : ℕ) (h : k + 1 < (cons ψ hY rest).length + 1),
      (cons ψ hY rest).weakTransformSeqAux J (k + 1) h =
        rest.weakTransformSeqAux (IdealSheaf.weakTransform (blowUpπ ψ hY) J hY.idealSheaf) k
          (Nat.lt_of_succ_lt_succ h)
  | 0, _ => rfl
  | k + 1, h => by
    change IdealSheaf.weakTransform ((cons ψ hY rest).map ⟨k + 1,
        _⟩) ((cons ψ hY rest).weakTransformSeqAux J (k + 1)
        (Nat.lt_of_succ_lt h)) ((cons ψ hY rest).center ⟨k + 1, _⟩) = _
    rw [cons_weakTransformSeqAux_succ hY rest J k (Nat.lt_of_succ_lt h)]
    rfl

theorem cons_weakTransformSeq_succ (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) (J : IdealSheaf M) (j : Fin (rest.length + 1)) :
    (cons ψ hY rest).weakTransformSeq J j.succ =
      rest.weakTransformSeq (IdealSheaf.weakTransform (blowUpπ ψ hY) J hY.idealSheaf) j :=
  cons_weakTransformSeqAux_succ hY rest J j.1 j.succ.2

end Induced

end AnalyticManifold.FiniteSuccession

end
