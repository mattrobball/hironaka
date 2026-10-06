/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Order
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.Restrict.Bundle
import Hironaka.Manifold.FiniteSuccession.Restrict.CongrChart
import Hironaka.Manifold.IdealSheaf.Vanishing
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Manifold.Snc.Dictionary
import Hironaka.Manifold.Snc.NormalCrossings
import Hironaka.Manifold.Snc.TotalTransform
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The boundary of a blow-up sequence as a simple normal crossing family

The boundary `E_i` of a sequence `Π` starting with the empty boundary (`boundarySeq` from
`⊤`) is defined by the recursion `E_{i+1} = red(π_i⁻¹(E_i) ∪ π_i⁻¹(Z_i))`
(`reducedTransform`), the recursion of the analytic main theorem
[Hir64, Main Theorem II′(N), clause (iii), p. 156]. Kollár works instead with the ordered family
of the exceptional divisors [Kol07, Definition 25]: `F_0 = ∅`, and `F_{i+1}` is the total
transform of `F_i` by `π_i`, the strict transforms of the components followed by the new
exceptional divisor (`HypersurfaceFamily.totalTransform`). This module defines that family along
the sequence (`totalTransformSeq`, by recursion on the stage; more generally
`totalTransformSeqFrom` from an arbitrary start family) and proves, for a sequence of order `≥ m`
(`IsOfOrderGe`, whose clause (3′) says that `E_i` has only normal crossings with `Z_i`), that
`F_i` is a simple normal crossing family with `E_i` its reduced ideal sheaf at every stage
(`boundarySeq_eq_idealSheaf_totalTransformSeq`), and that the centre `Z_i` has simple normal
crossings with `F_i` in the chart sense of [Kol07, Definition 24 (4)]
(`hasSncWith_totalTransformSeq_center`). Induction on the stage: the stalk clause (3′) is the
chart clause "`Z_i` has simple normal crossings with `F_i`" by the dictionary
`hasOnlyNormalCrossingsWith_idealSheaf_iff`; `isSnc_totalTransform` makes `F_{i+1}` a simple
normal crossing family, and `reducedTransform_eq_idealSheaf_totalTransform` identifies
`red(π_i⁻¹E_i ∪ π_i⁻¹Z_i)` with its reduced ideal sheaf. Each statement also comes in a
prefix-bounded form (`…_of_forall_lt`) assuming clause (3′) only at the stages before the one
considered, for the joint inductions in which clause (3′) of a sequence is itself being proved.

The two descriptions of the boundary bridge the stalk-local normal-crossings clause of the main
theorems and Kollár's chart-wise simple normal crossings; both are used throughout the going-up
and order-reduction arguments.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Manifold
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

include ψ in
/-- The reduced ideal sheaf of the empty divisor is the unit ideal sheaf. -/
theorem HypersurfaceFamily.idealSheaf_empty [IsManifold 𝓘(𝕜, E) ω M] :
    (HypersurfaceFamily.empty M).idealSheaf (𝕜 := 𝕜) (E := E) = ⊤ := by
  refine IdealSheaf.ext fun x => ?_
  rw [(HypersurfaceFamily.isSnc_empty (ψ := ψ)).stalkIdeal_idealSheaf, IdealSheaf.stalkIdeal_top]
  refine vanishingStalk_eq_top_of_notMem_closure ?_
  have : (HypersurfaceFamily.empty M).support = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun y hy => ?_
    obtain ⟨j, -⟩ := Set.mem_iUnion.mp hy
    exact j.elim
  rw [this, closure_empty]
  exact Set.notMem_empty x

end Manifold

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- The family of exceptional divisors along the sequence from a start family `F`
[Kol07, Definition 25], by recursion on the stage: `F_0 = F`, and `F_{i+1}` is the total transform
of `F_i` under `π_i` with centre `Z_i`. The empty start is `totalTransformSeqAux`. -/
def totalTransformSeqFromAux (F : HypersurfaceFamily M) :
    ∀ (i : ℕ) (h : i < S.length + 1), HypersurfaceFamily (finStages M S.later ⟨i, h⟩)
  | 0, _ => F
  | i + 1, h =>
    (totalTransformSeqFromAux F i (Nat.lt_of_succ_lt h)).totalTransform
      (S.map ⟨i, Nat.lt_of_succ_lt_succ h⟩) (S.center ⟨i, Nat.lt_of_succ_lt_succ h⟩).support

/-- The boundary family at stage `i` starting from `F`. -/
def totalTransformSeqFrom (F : HypersurfaceFamily M) (i : Fin (S.length + 1)) :
    HypersurfaceFamily (S.stage i) :=
  S.totalTransformSeqFromAux F i.1 i.2

theorem totalTransformSeqFrom_zero (F : HypersurfaceFamily M) :
    S.totalTransformSeqFrom F 0 = F := rfl

theorem totalTransformSeqFrom_succ (F : HypersurfaceFamily M) (i : Fin S.length) :
    S.totalTransformSeqFrom F i.succ =
      (S.totalTransformSeqFrom F i.castSucc).totalTransform (S.map i) (S.center i).support :=
  rfl

/-- The family of exceptional divisors at stage `i` [Kol07, Definition 25], by recursion on the
stage: `F_0 = ∅`, and `F_{i+1}` is the total transform of `F_i` under `π_i` with centre `Z_i` (the
strict transforms of the components of `F_i` followed by `π_i⁻¹(Z_i)`). -/
def totalTransformSeqAux :
    ∀ (i : ℕ) (h : i < S.length + 1), HypersurfaceFamily (finStages M S.later ⟨i, h⟩) :=
  S.totalTransformSeqFromAux (HypersurfaceFamily.empty M)

/-- The family `F_i` of exceptional divisors on the stage `X_i` [Kol07, Definition 25]. -/
def totalTransformSeq (i : Fin (S.length + 1)) : HypersurfaceFamily (S.stage i) :=
  S.totalTransformSeqAux i.1 i.2

theorem totalTransformSeq_zero : S.totalTransformSeq 0 = HypersurfaceFamily.empty M := rfl

theorem totalTransformSeq_succ (i : Fin S.length) :
    S.totalTransformSeq i.succ =
      (S.totalTransformSeq i.castSucc).totalTransform (S.map i) (S.center i).support :=
  rfl

/-- The empty start is the family of exceptional divisors, definitionally. -/
theorem totalTransformSeqFrom_empty (i : Fin (S.length + 1)) :
    S.totalTransformSeqFrom (HypersurfaceFamily.empty M) i = S.totalTransformSeq i := rfl

/-- The boundary recursion, one step (definitional). -/
theorem boundarySeq_succ (E₀ : IdealSheaf M) (i : Fin S.length) :
    S.boundarySeq E₀ i.succ =
      IdealSheaf.reducedTransform (S.map i) (S.boundarySeq E₀ i.castSucc) (S.center i) :=
  rfl

variable {S} {J : IdealSheaf M} {m : ℕ}

/-- The comparison of Kollár's family of exceptional divisors [Kol07, Definition 25] with the
reduced boundary of [Hir64, Main Theorem II′(N), p. 156], from a start family and in
prefix-bounded form: for a simple normal crossing start `F`, under clause (3′) for the boundary
starting with `red F` at the stages `< i`, the family `F_i` from the start `F` is a simple normal
crossing family at stage `i` and the boundary `E_i` is its reduced ideal sheaf. Induction on the
stage: clause (3′) at a stage says that `E_i` has only normal crossings with `Z_i`, which by the
dictionary `hasOnlyNormalCrossingsWith_idealSheaf_iff` is "`Z_i` has simple normal crossings with
`F_i`"; `isSnc_totalTransform` makes `F_{i+1}` a simple normal crossing family and
`reducedTransform_eq_idealSheaf_totalTransform` identifies `red(π_i⁻¹E_i ∪ π_i⁻¹Z_i)` with the
reduced ideal sheaf of the total transform. The start enters only through `E_0 = red F`, so the
base case is `rfl`. Not in the sources in this form. -/
theorem isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt {F : HypersurfaceFamily M}
    (hF : F.IsSnc ψ) (i : Fin (S.length + 1))
    (h3 : ∀ i' : Fin S.length, i'.1 < i.1 →
      (S.boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E)) i'.castSucc).HasOnlyNormalCrossingsWith
        (S.center i')) :
    (S.totalTransformSeqFrom F i).IsSnc ψ ∧
      S.boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E)) i =
        (S.totalTransformSeqFrom F i).idealSheaf := by
  induction i using Fin.induction with
  | zero => exact ⟨hF, rfl⟩
  | succ i ih =>
    obtain ⟨hsnc, heq⟩ := ih fun i' hi' => h3 i' (by
      rw [Fin.val_castSucc] at hi'; rw [Fin.val_succ]; omega)
    have hZ : IsClosedSubmanifold ψ (S.center i).support (S.codim i) :=
      (S.isClosedSubmanifold_center i).congr_chart ψ
    have hπ : IsBlowUp ψ (S.center i).support (S.codim i) (S.map i) :=
      (S.isBlowUp_map i).congr_chart ψ
    have hZI : hZ.idealSheaf = S.center i :=
      (IsClosedSubmanifold.idealSheaf_congr hZ (S.isClosedSubmanifold_center i) rfl).trans
        (S.idealSheaf_center i)
    have hsw : (S.totalTransformSeqFrom F i.castSucc).HasSncWith ψ (S.center i).support
        (S.codim i) := by
      have h := h3 i (by rw [Fin.val_succ]; exact Nat.lt_succ_self _)
      rw [heq, ← hZI] at h
      exact (hasOnlyNormalCrossingsWith_idealSheaf_iff hsnc hZ).mp h
    refine ⟨HypersurfaceFamily.isSnc_totalTransform hZ hπ hsnc hsw, ?_⟩
    rw [S.boundarySeq_succ, heq, ← hZI]
    exact reducedTransform_eq_idealSheaf_totalTransform hZ hπ hsnc hsw

/-- The form of `hasSncWith_totalTransformSeq_center` from a start family: clause (3′) for the
boundary starting with `red F` at the stages `≤ i` gives Kollár's chart-wise clause at stage `i`,
that `Z_i` has simple normal crossings with `F_i`. -/
theorem hasSncWith_totalTransformSeqFrom_center_of_forall_lt {F : HypersurfaceFamily M}
    (hF : F.IsSnc ψ) (i : Fin S.length)
    (h3 : ∀ i' : Fin S.length, i'.1 < i.1 + 1 →
      (S.boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E)) i'.castSucc).HasOnlyNormalCrossingsWith
        (S.center i')) :
    (S.totalTransformSeqFrom F i.castSucc).HasSncWith ψ (S.center i).support (S.codim i) := by
  obtain ⟨hsnc, heq⟩ := isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt hF i.castSucc
    fun i' hi' => h3 i' (by rw [Fin.val_castSucc] at hi'; omega)
  have hZ : IsClosedSubmanifold ψ (S.center i).support (S.codim i) :=
    (S.isClosedSubmanifold_center i).congr_chart ψ
  have hZI : hZ.idealSheaf = S.center i :=
    (IsClosedSubmanifold.idealSheaf_congr hZ (S.isClosedSubmanifold_center i) rfl).trans
      (S.idealSheaf_center i)
  have h := h3 i (Nat.lt_succ_self _)
  rw [heq, ← hZI] at h
  exact (hasOnlyNormalCrossingsWith_idealSheaf_iff hsnc hZ).mp h

/-- The prefix-bounded form of `isSnc_totalTransformSeq_and_boundarySeq_eq`, for the joint
inductions that prove clause (3′) of a transformed sequence (a restriction or push-forward in the
sense of [Kol07, Definition 30]): the conclusion at stage `i` uses clause (3′) of `Π` at the
stages `< i` only, and the order clause never enters. -/
theorem isSnc_totalTransformSeq_and_boundarySeq_eq_of_forall_lt (i : Fin (S.length + 1))
    (h3 : ∀ i' : Fin S.length, i'.1 < i.1 →
      (S.boundarySeq (⊤) i'.castSucc).HasOnlyNormalCrossingsWith (S.center i')) :
    (S.totalTransformSeq i).IsSnc ψ ∧
      S.boundarySeq (⊤) i = (S.totalTransformSeq i).idealSheaf := by
  have h := isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt (S := S)
    (HypersurfaceFamily.isSnc_empty (ψ := ψ)) i (by
      rwa [HypersurfaceFamily.idealSheaf_empty (ψ := ψ)])
  rwa [HypersurfaceFamily.idealSheaf_empty (ψ := ψ)] at h

/-- For a sequence of order `≥ m` with the empty boundary, the family `F_i` of exceptional
divisors [Kol07, Definition 25] is a simple normal crossing family at every stage, and the
boundary `E_i` of the recursion of [Hir64, Main Theorem II′(N), p. 156] is its reduced ideal sheaf.
Induction on the stage: clause (3′) of `Π` at stage `i` says that `E_i` has only normal crossings
with `Z_i`, which by the dictionary is "`Z_i` has simple normal crossings with `F_i`";
`isSnc_totalTransform` then makes `F_{i+1}` a simple normal crossing family and
`reducedTransform_eq_idealSheaf_totalTransform` identifies `red(π_i⁻¹E_i ∪ π_i⁻¹Z_i)` with the
reduced ideal sheaf of the total transform. -/
theorem isSnc_totalTransformSeq_and_boundarySeq_eq (hge : S.IsOfOrderGe J m (⊤))
    (i : Fin (S.length + 1)) :
    (S.totalTransformSeq i).IsSnc ψ ∧
      S.boundarySeq (⊤) i = (S.totalTransformSeq i).idealSheaf :=
  isSnc_totalTransformSeq_and_boundarySeq_eq_of_forall_lt i fun i' _ => (hge i').1

/-- The prefix-bounded form of `isSnc_totalTransformSeq`. -/
theorem isSnc_totalTransformSeq_of_forall_lt (i : Fin (S.length + 1))
    (h3 : ∀ i' : Fin S.length, i'.1 < i.1 →
      (S.boundarySeq (⊤) i'.castSucc).HasOnlyNormalCrossingsWith (S.center i')) :
    (S.totalTransformSeq i).IsSnc ψ :=
  (isSnc_totalTransformSeq_and_boundarySeq_eq_of_forall_lt i h3).1

/-- The family of exceptional divisors of a sequence of order `≥ m` is a simple normal crossing
family at every stage. -/
theorem isSnc_totalTransformSeq (hge : S.IsOfOrderGe J m (⊤))
    (i : Fin (S.length + 1)) : (S.totalTransformSeq i).IsSnc ψ :=
  isSnc_totalTransformSeq_of_forall_lt i fun i' _ => (hge i').1

/-- The prefix-bounded form of `boundarySeq_eq_idealSheaf_totalTransformSeq`. -/
theorem boundarySeq_eq_idealSheaf_totalTransformSeq_of_forall_lt (ψ : E ≃L[𝕜] (Fin n → 𝕜))
    (i : Fin (S.length + 1))
    (h3 : ∀ i' : Fin S.length, i'.1 < i.1 →
      (S.boundarySeq (⊤) i'.castSucc).HasOnlyNormalCrossingsWith (S.center i')) :
    S.boundarySeq (⊤) i = (S.totalTransformSeq i).idealSheaf :=
  (isSnc_totalTransformSeq_and_boundarySeq_eq_of_forall_lt (ψ := ψ) i h3).2

/-- The boundary of a sequence of order `≥ m` with the empty boundary is the reduced ideal sheaf
of its family of exceptional divisors. -/
theorem boundarySeq_eq_idealSheaf_totalTransformSeq (ψ : E ≃L[𝕜] (Fin n → 𝕜))
    (hge : S.IsOfOrderGe J m (⊤)) (i : Fin (S.length + 1)) :
    S.boundarySeq (⊤) i = (S.totalTransformSeq i).idealSheaf :=
  boundarySeq_eq_idealSheaf_totalTransformSeq_of_forall_lt ψ i fun i' _ => (hge i').1

/-- The prefix-bounded form of `hasSncWith_totalTransformSeq_center`: clause (3′) of `Π` at the
stages `≤ i` gives Kollár's chart-wise clause at stage `i`. -/
theorem hasSncWith_totalTransformSeq_center_of_forall_lt (i : Fin S.length)
    (h3 : ∀ i' : Fin S.length, i'.1 < i.1 + 1 →
      (S.boundarySeq (⊤) i'.castSucc).HasOnlyNormalCrossingsWith (S.center i')) :
    (S.totalTransformSeq i.castSucc).HasSncWith ψ (S.center i).support (S.codim i) := by
  have h3c : ∀ i' : Fin S.length, i'.1 < i.castSucc.1 →
      (S.boundarySeq (⊤) i'.castSucc).HasOnlyNormalCrossingsWith (S.center i') :=
    fun i' hi' => h3 i' (by rw [Fin.val_castSucc] at hi'; omega)
  have hZ : IsClosedSubmanifold ψ (S.center i).support (S.codim i) :=
    (S.isClosedSubmanifold_center i).congr_chart ψ
  have hZI : hZ.idealSheaf = S.center i :=
    (IsClosedSubmanifold.idealSheaf_congr hZ (S.isClosedSubmanifold_center i) rfl).trans
      (S.idealSheaf_center i)
  have h := h3 i (Nat.lt_succ_self _)
  rw [boundarySeq_eq_idealSheaf_totalTransformSeq_of_forall_lt ψ i.castSucc h3c, ← hZI] at h
  exact (hasOnlyNormalCrossingsWith_idealSheaf_iff
    (isSnc_totalTransformSeq_of_forall_lt i.castSucc h3c) hZ).mp h

/-- Clause (3′) of a sequence of order `≥ m` in Kollár's form: the centre `Z_i` has simple normal
crossings with the family of exceptional divisors `F_i` [Kol07, Definition 24 (4)]. -/
theorem hasSncWith_totalTransformSeq_center (hge : S.IsOfOrderGe J m (⊤))
    (i : Fin S.length) :
    (S.totalTransformSeq i.castSucc).HasSncWith ψ (S.center i).support (S.codim i) :=
  hasSncWith_totalTransformSeq_center_of_forall_lt i fun i' _ => (hge i').1

end AnalyticManifold.FiniteSuccession

end
