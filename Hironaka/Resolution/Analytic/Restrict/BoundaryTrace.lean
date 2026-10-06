/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.BoundaryFamily
public import Hironaka.Manifold.Snc.Trace
public import Hironaka.Manifold.FiniteSuccession.Restrict.Restrict
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.Restrict.CongrChart
import Hironaka.Manifold.IdealSheaf.Vanishing
import Hironaka.Manifold.Snc.Bundled
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Manifold.Snc.NormalCrossings
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The boundary of the restricted succession is the trace

Kollár restricts a smooth blow-up sequence `Π` with centres `Z_i ⊆ S_i` to the strict transforms
`S_i` of a closed submanifold `S` [Kol07, Definition 30.2] (`restrictSubmanifold`, whose stages are
the `S_i` and whose blow-downs are the restrictions of the `π_i`). This module proves the
set-theoretic half of the normal-crossings clause (3′) of [Kol07, Definition 66] for `Π|_S`: the
support of the boundary `E'_i` of `Π|_S` (`boundarySeq` from the unit ideal sheaf) is the trace
`E_i ∩ S_i` of the boundary of `Π` — the preimage of `supp E_i` under the inclusion `S_i ↪ X_i`
(`support_boundarySeq_restrictSubmanifold`). Induction on the stage: both boundaries start empty,
and `reducedTransform_support` reads the recursion `E_{i+1} = red(π_i⁻¹E_i ∪ π_i⁻¹Z_i)` on the
supports (the reduced analytic subspace `red(f⁻¹(E) ∪ f⁻¹(D))` of Hironaka's analytic theorem,
[Hir64, Ch. 0, §7, Main Theorem II′(N)]), where the centres of `Π|_S` are the traces of the centres
(`support_center_restrictSubmanifold`) and the blow-downs commute with the inclusions
(`restrictIncl_map`). The proper invariant of `Snc/Proper.lean` is carried along the succession
(`hasSncWithProper_totalTransformSeq_strictTransformSeq`: `S_i` has simple normal crossings with
the boundary family `F_i`, properly, at every stage — vacuous at stage 0 and transported by each
blowing-up through `hasSncWithProper_totalTransform`, the centre `Z_i ⊆ S_i` having simple normal
crossings with `F_i` by clause (3′) of `Π`). The prefix-bounded forms (clause (3′) assumed only at
the stages `< i`) and the forms with an arbitrary starting boundary family `F` serve the lifting of
simple normal crossings along the restriction. Not in the sources; routine.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Manifold
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)
  {H : Set M} {s : ℕ} (hH : IsClosedSubmanifold ψ H s) (hc : S.CentersIn H)

/-- The support of the boundary of `Π|_S` started with `E₀'` is the trace of the support of the
boundary of `Π` started with `E₀`, at every stage, as soon as it is at stage `0` — the recursion is
start-agnostic (`support_boundarySeq_restrictSubmanifold` is the unit start; the traces of
[Kol07, Definition 30.2] on the supports). -/
theorem support_boundarySeq_restrictSubmanifold_of_support_eq (E₀ : IdealSheaf M)
    (E₀' : IdealSheaf hH.toAnalyticManifold)
    (hbase : E₀'.support = ⇑(S.restrictIncl hH hc 0) ⁻¹' E₀.support) (i : Fin (S.length + 1)) :
    ((S.restrictSubmanifold hH hc).boundarySeq E₀' i).support =
      ⇑(S.restrictIncl hH hc i) ⁻¹' (S.boundarySeq E₀ i).support := by
  induction i using Fin.induction with
  | zero => exact hbase
  | succ i ih =>
    -- the recursion is definitional on both successions
    have e1 : ((S.restrictSubmanifold hH hc).boundarySeq E₀'
        i.succ).support =
        ⇑((S.restrictSubmanifold hH hc).map i) ⁻¹' ((S.restrictSubmanifold hH hc).boundarySeq
          E₀' i.castSucc).support ∪
        ⇑((S.restrictSubmanifold hH hc).map i) ⁻¹'
          ((S.restrictSubmanifold hH hc).center i).support :=
      reducedTransform_support ((S.restrictSubmanifold hH hc).map i)
        ((S.restrictSubmanifold hH hc).center i)
        ((S.restrictSubmanifold hH hc).boundarySeq E₀'
          i.castSucc)
    -- the blow-downs commute with the inclusions
    have hcomm : ∀ p, S.restrictIncl hH hc i.castSucc ((S.restrictSubmanifold hH hc).map i p) =
        S.map i (S.restrictIncl hH hc i.succ p) := S.restrictIncl_map hH hc i
    have key : ∀ A : Set (S.stage i.castSucc),
        ⇑((S.restrictSubmanifold hH hc).map i) ⁻¹' (⇑(S.restrictIncl hH hc i.castSucc) ⁻¹' A) =
          ⇑(S.restrictIncl hH hc i.succ) ⁻¹' (⇑(S.map i) ⁻¹' A) := fun A =>
      Set.ext fun p => by
        change S.restrictIncl hH hc i.castSucc ((S.restrictSubmanifold hH hc).map i p) ∈ A ↔
          S.map i (S.restrictIncl hH hc i.succ p) ∈ A
        rw [hcomm p]
    rw [e1, S.boundarySeq_succ, reducedTransform_support, ih,
      S.support_center_restrictSubmanifold hH hc i, Set.preimage_union]
    exact congrArg₂ (· ∪ ·) (key _) (key _)
/-- The boundary of the restricted succession `Π|_S`, started with the unit ideal sheaf, has as
support the trace of the boundary of `Π` at every stage — `supp E'_i = S_i ∩ supp E_i`, read as the
preimage under the inclusion `S_i ↪ X_i` ([Kol07, Definition 30.2] on the supports). -/
theorem support_boundarySeq_restrictSubmanifold (i : Fin (S.length + 1)) :
    ((S.restrictSubmanifold hH hc).boundarySeq (⊤) i).support =
      ⇑(S.restrictIncl hH hc i) ⁻¹' (S.boundarySeq (⊤) i).support :=
  S.support_boundarySeq_restrictSubmanifold_of_support_eq hH hc _ _ (by
    change (⊤ : IdealSheaf _).support = _ ⁻¹' (⊤ : IdealSheaf _).support
    rw [IdealSheaf.support_top, IdealSheaf.support_top]
    exact Set.preimage_empty.symm) i

include hH hc in
/-- The prefix-bounded form of `hasSncWithProper_totalTransformSeq_strictTransformSeq` — clause
(3′) of `Π` at the stages `< i` suffices for the proper invariant at stage `i`. -/
theorem hasSncWithProper_totalTransformSeq_strictTransformSeq_of_forall_lt (i : Fin (S.length + 1))
    (h3 : ∀ i' : Fin S.length, i'.1 < i.1 →
      (S.boundarySeq (⊤) i'.castSucc).HasOnlyNormalCrossingsWith (S.center i')) :
    (S.totalTransformSeq i).HasSncWithProper ψ (S.strictTransformSeq H i) s := by
  induction i using Fin.induction with
  | zero => exact HypersurfaceFamily.hasSncWithProper_empty hH
  | succ i ih =>
    have h3c : ∀ i' : Fin S.length, i'.1 < i.castSucc.1 →
        (S.boundarySeq (⊤) i'.castSucc).HasOnlyNormalCrossingsWith (S.center i') :=
      fun i' hi' => h3 i' (by rw [Fin.val_castSucc] at hi'; rw [Fin.val_succ]; omega)
    have hZ : IsClosedSubmanifold ψ (S.center i).support (S.codim i) :=
      (S.isClosedSubmanifold_center i).congr_chart ψ
    have hπ : IsBlowUp ψ (S.center i).support (S.codim i) (S.map i) :=
      (S.isBlowUp_map i).congr_chart ψ
    exact HypersurfaceFamily.hasSncWithProper_totalTransform hZ hπ
      (isSnc_totalTransformSeq_of_forall_lt i.castSucc h3c)
      (S.isClosedSubmanifold_strictTransformSeq H hH hc i.castSucc) (hc i)
      (hasSncWith_totalTransformSeq_center_of_forall_lt i fun i' hi' =>
        h3 i' (by rw [Fin.val_succ]; exact hi'))
      (ih h3c)

include hH hc in
/-- Along a succession of order `≥ m` with centres `Z_i ⊆ S_i` [Kol07, Definition 30.2], the strict
transform `S_i` has simple normal crossings with the boundary family `F_i`, properly (no component
of `F_i` contains `S_i` near any point), at every stage. Induction on the stage: vacuous for the
empty family at stage 0; the step is the transport of the proper invariant by the blowing-up `π_i`
along `Z_i ⊆ S_i` (`hasSncWithProper_totalTransform`), with `Z_i` having simple normal crossings
with `F_i` by clause (3′) of `Π` (`hasSncWith_totalTransformSeq_center`). No clopen argument on the
components enters: the trace of a component on `S_i` is a hypersurface of `S_i` by the invariant at
each point. -/
theorem hasSncWithProper_totalTransformSeq_strictTransformSeq {J : IdealSheaf M} {m : ℕ}
    (hge : S.IsOfOrderGe J m (⊤)) (i : Fin (S.length + 1)) :
    (S.totalTransformSeq i).HasSncWithProper ψ (S.strictTransformSeq H i) s :=
  S.hasSncWithProper_totalTransformSeq_strictTransformSeq_of_forall_lt hH hc i
    fun i' _ => (hge i').1

/-! ### The trace of the boundary family on the stages of the restriction -/

/-- The trace on `S_i` of the boundary family from the start `F`, typed on the stages
`finStages`. -/
def traceFamilyFromAux (F : HypersurfaceFamily M) : ∀ (i : ℕ) (hi : i < S.length + 1),
    HypersurfaceFamily (finStages hH.toAnalyticManifold (S.restrictLater hH hc) ⟨i, hi⟩)
  | 0, hi => (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc 0 hi).traceFamily
      (S.totalTransformSeqFromAux F 0 hi)
  | i + 1, hi =>
    (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc (i + 1) hi).traceFamily
        (S.totalTransformSeqFromAux F (i + 1) hi)

/-- The trace on `S_i` of the boundary family `F_i` from the start `F` (Kollár's `E_i ∩ S_i`
[Kol07, Definition 30.2] with the boundary `E = red F`). -/
def traceFamilyFrom (F : HypersurfaceFamily M) (i : Fin (S.length + 1)) :
    HypersurfaceFamily ((S.restrictSubmanifold hH hc).stage i) :=
  S.traceFamilyFromAux hH hc F i.1 i.2

/-- The trace of the boundary family `F_i` on the stage `S_i` of `Π|_S`, typed on the stages
`finStages` (as `restrictCenterAux`) — the empty start of `traceFamilyFromAux`. -/
def traceFamilyAux : ∀ (i : ℕ) (hi : i < S.length + 1),
    HypersurfaceFamily (finStages hH.toAnalyticManifold (S.restrictLater hH hc) ⟨i, hi⟩) :=
  S.traceFamilyFromAux hH hc (HypersurfaceFamily.empty M)

/-- Kollár's boundary `E_i ∩ S_i` [Kol07, Definition 30.2] as a family of hypersurfaces of `S_i`:
the trace of the boundary family `F_i` on the stage `S_i` of `Π|_S`. -/
def traceFamily (i : Fin (S.length + 1)) :
    HypersurfaceFamily ((S.restrictSubmanifold hH hc).stage i) :=
  S.traceFamilyAux hH hc i.1 i.2

/-- The support of the trace family is the trace of the support of `F_i`. -/
theorem support_traceFamily (i : Fin (S.length + 1)) :
    (S.traceFamily hH hc i).support =
      ⇑(S.restrictIncl hH hc i) ⁻¹' (S.totalTransformSeq i).support := by
  obtain ⟨i, hi⟩ := i
  cases i with
  | zero => exact (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc 0 hi).traceFamily_support
                (S.totalTransformSeqAux 0 hi)
  | succ k =>
    exact (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc (k + 1) hi).traceFamily_support
      (S.totalTransformSeqAux (k + 1) hi)

/-- The support of the trace family from `F` is the trace of the support of `F_i`. -/
theorem support_traceFamilyFrom (F : HypersurfaceFamily M) (i : Fin (S.length + 1)) :
    (S.traceFamilyFrom hH hc F i).support =
      ⇑(S.restrictIncl hH hc i) ⁻¹' (S.totalTransformSeqFrom F i).support := by
  obtain ⟨i, hi⟩ := i
  cases i with
  | zero =>
    exact (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc 0 hi).traceFamily_support
        (S.totalTransformSeqFromAux F 0 hi)
  | succ k =>
    exact (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc (k + 1) hi).traceFamily_support
      (S.totalTransformSeqFromAux F (k + 1) hi)

variable {J : IdealSheaf M} {m : ℕ}

/-- The prefix-bounded form of `isSnc_traceFamily`. -/
theorem isSnc_traceFamily_of_forall_lt (i : Fin (S.length + 1))
    (h3 : ∀ i' : Fin S.length, i'.1 < i.1 →
      (S.boundarySeq (⊤) i'.castSucc).HasOnlyNormalCrossingsWith (S.center i')) :
    (S.traceFamily hH hc i).IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) := by
  obtain ⟨i, hi⟩ := i
  cases i with
  | zero =>
    exact (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc 0 hi).isSnc_traceFamily
      (isSnc_totalTransformSeq_of_forall_lt ⟨0, hi⟩ h3)
      (S.hasSncWithProper_totalTransformSeq_strictTransformSeq_of_forall_lt hH hc ⟨0, hi⟩ h3)
  | succ k =>
    exact (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc (k + 1) hi).isSnc_traceFamily
      (isSnc_totalTransformSeq_of_forall_lt ⟨k + 1, hi⟩ h3)
      (S.hasSncWithProper_totalTransformSeq_strictTransformSeq_of_forall_lt hH hc ⟨k + 1, hi⟩ h3)

/-- The trace of the boundary family on `S_i` is a simple normal crossings divisor of `S_i` —
`S_i` has simple normal crossings with `F_i` properly along `Π`. -/
theorem isSnc_traceFamily (hge : S.IsOfOrderGe J m (⊤)) (i : Fin (S.length + 1)) :
    (S.traceFamily hH hc i).IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) :=
  S.isSnc_traceFamily_of_forall_lt hH hc i fun i' _ => (hge i').1

/-- The prefix-bounded form of `support_traceFamily_eq_support_boundarySeq`. -/
theorem support_traceFamily_eq_support_boundarySeq_of_forall_lt (i : Fin (S.length + 1))
    (h3 : ∀ i' : Fin S.length, i'.1 < i.1 →
      (S.boundarySeq (⊤) i'.castSucc).HasOnlyNormalCrossingsWith (S.center i')) :
    (S.traceFamily hH hc i).support =
      ((S.restrictSubmanifold hH hc).boundarySeq (⊤)
        i).support := by
  rw [S.support_traceFamily hH hc i, S.support_boundarySeq_restrictSubmanifold hH hc i,
    boundarySeq_eq_idealSheaf_totalTransformSeq_of_forall_lt ψ i h3]
  exact congrArg (Set.preimage ⇑(S.restrictIncl hH hc i))
    (isSnc_totalTransformSeq_of_forall_lt (ψ := ψ) i h3).cosupport_idealSheaf.symm

/-- The support of the trace family is the support of the boundary of `Π|_S`. -/
theorem support_traceFamily_eq_support_boundarySeq (hge : S.IsOfOrderGe J m (⊤))
    (i : Fin (S.length + 1)) :
    (S.traceFamily hH hc i).support =
      ((S.restrictSubmanifold hH hc).boundarySeq (⊤)
        i).support :=
  S.support_traceFamily_eq_support_boundarySeq_of_forall_lt hH hc i fun i' _ => (hge i').1

/-- The prefix-bounded form of `stalkIdeal_boundarySeq_restrictSubmanifold`. -/
theorem stalkIdeal_boundarySeq_restrictSubmanifold_of_forall_lt (i : Fin (S.length + 1))
    (h3 : ∀ i' : Fin S.length, i'.1 < i.1 →
      (S.boundarySeq (⊤) i'.castSucc).HasOnlyNormalCrossingsWith (S.center i'))
    (x : (S.restrictSubmanifold hH hc).stage i) :
    ((S.restrictSubmanifold hH hc).boundarySeq (⊤)
        i).stalkIdeal x =
      vanishingStalk (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)
        (((S.restrictSubmanifold hH hc).boundarySeq (⊤)
          i).support) x := by
  revert x
  induction i using Fin.induction with
  | zero =>
    intro x
    change ((⊤ : IdealSheaf ((S.restrictSubmanifold hH hc).stage
        (0 : Fin (S.length + 1))))).stalkIdeal x =
      vanishingStalk (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)
        ((⊤ : IdealSheaf ((S.restrictSubmanifold hH hc).stage
          (0 : Fin (S.length + 1)))).support) x
    rw [IdealSheaf.stalkIdeal_top, IdealSheaf.support_top]
    refine (vanishingStalk_eq_top_of_notMem_closure ?_).symm
    rw [closure_empty]
    exact Set.notMem_empty x
  | succ i _ =>
    intro x
    have e1 : (S.restrictSubmanifold hH hc).boundarySeq (⊤)
        i.succ = IdealSheaf.reducedTransform ((S.restrictSubmanifold hH
            hc).map i) ((S.restrictSubmanifold hH hc).boundarySeq
            (⊤) i.castSucc) ((S.restrictSubmanifold hH hc).center i) := rfl
    have hset : ⇑((S.restrictSubmanifold hH hc).map i) ⁻¹'
          ((S.restrictSubmanifold hH hc).boundarySeq (⊤)
            i.castSucc).support ∪
        ⇑((S.restrictSubmanifold hH hc).map i) ⁻¹'
          ((S.restrictSubmanifold hH hc).center i).support =
        (S.traceFamily hH hc i.succ).support := by
      rw [S.support_traceFamily_eq_support_boundarySeq_of_forall_lt hH hc i.succ h3, e1]
      exact (reducedTransform_support _ _ _).symm
    have hloc :=
      (S.isSnc_traceFamily_of_forall_lt hH hc i.succ h3).hasLocalGenerators_vanishingStalk_support
    rw [← hset] at hloc
    rw [e1]
    exact (reducedTransform_stalkIdeal_of_hasLocalGenerators _ _ _ hloc x).trans
      (congrArg (fun t => vanishingStalk (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜) t x)
        (reducedTransform_support _ _ _).symm)

/-- The boundary of `Π|_S` is the reduced ideal sheaf of its support at every stage — the unit
ideal sheaf at stage 0, and at a later stage the `red` branch of the recursion (Hironaka's reduced
analytic subspace, [Hir64, Ch. 0, §7, Main Theorem II′(N)]), the vanishing ideals of
`supp E'_i = |E_i ∩ S_i|` having local generators because the trace family has simple normal
crossings. -/
theorem stalkIdeal_boundarySeq_restrictSubmanifold (hge : S.IsOfOrderGe J m (⊤))
    (i : Fin (S.length + 1)) (x : (S.restrictSubmanifold hH hc).stage i) :
    ((S.restrictSubmanifold hH hc).boundarySeq (⊤)
        i).stalkIdeal x =
      vanishingStalk (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)
        (((S.restrictSubmanifold hH hc).boundarySeq (⊤)
          i).support) x :=
  S.stalkIdeal_boundarySeq_restrictSubmanifold_of_forall_lt hH hc i
    (fun i' _ => (hge i').1) x

/-- The prefix-bounded form of `boundarySeq_restrictSubmanifold_eq_idealSheaf_traceFamily` — the
input of the lifting of simple normal crossings along the restriction. -/
theorem boundarySeq_restrictSubmanifold_eq_idealSheaf_traceFamily_of_forall_lt
    (i : Fin (S.length + 1))
    (h3 : ∀ i' : Fin S.length, i'.1 < i.1 →
      (S.boundarySeq (⊤) i'.castSucc).HasOnlyNormalCrossingsWith (S.center i')) :
    (S.restrictSubmanifold hH hc).boundarySeq (⊤) i =
      (S.traceFamily hH hc i).idealSheaf := by
  refine IdealSheaf.ext fun x => ?_
  rw [S.stalkIdeal_boundarySeq_restrictSubmanifold_of_forall_lt hH hc i h3 x,
    (S.isSnc_traceFamily_of_forall_lt hH hc i h3).stalkIdeal_idealSheaf x,
    S.support_traceFamily_eq_support_boundarySeq_of_forall_lt hH hc i h3]

/-- The boundary of `Π|_S` is the reduced ideal sheaf of the trace of the boundary family — both
are the reduced ideal sheaves of the same set `|E_i ∩ S_i|`. -/
theorem boundarySeq_restrictSubmanifold_eq_idealSheaf_traceFamily
    (hge : S.IsOfOrderGe J m (⊤)) (i : Fin (S.length + 1)) :
    (S.restrictSubmanifold hH hc).boundarySeq (⊤) i =
      (S.traceFamily hH hc i).idealSheaf :=
  S.boundarySeq_restrictSubmanifold_eq_idealSheaf_traceFamily_of_forall_lt hH hc i
    fun i' _ => (hge i').1

/-- The trace of the boundary family from `F` on `S_i` has simple normal crossings when `F_i` has
and has simple normal crossings with `S_i` properly (`isSnc_traceFamily` is the empty start). -/
theorem isSnc_traceFamilyFrom (F : HypersurfaceFamily M) (i : Fin (S.length + 1))
    (hsnc : (S.totalTransformSeqFrom F i).IsSnc ψ)
    (hprop : (S.totalTransformSeqFrom F i).HasSncWithProper ψ (S.strictTransformSeq H i) s) :
    (S.traceFamilyFrom hH hc F i).IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) := by
  obtain ⟨i, hi⟩ := i
  cases i with
  | zero => exact (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc 0 hi).isSnc_traceFamily hsnc
                hprop
  | succ k => exact (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc (k + 1)
                hi).isSnc_traceFamily hsnc hprop

/-- The base identity of the supports for the start `E = red F` on `M` and `E|_S = red (F|_S)` on
`S`, for `F` snc having simple normal crossings with `S` properly. -/
theorem support_idealSheaf_traceFamily_eq {F : HypersurfaceFamily M} (hF : F.IsSnc ψ)
    (hFH : F.HasSncWithProper ψ H s) :
    ((hH.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)).support =
      ⇑(S.restrictIncl hH hc 0) ⁻¹' (F.idealSheaf (𝕜 := 𝕜) (E := E)).support := by
  rw [(hH.isSnc_traceFamily hF hFH).cosupport_idealSheaf, hH.traceFamily_support,
    hF.cosupport_idealSheaf]
  rfl

/-- The support of the trace family from `F` is the support of the boundary of `Π|_S` started
with `E|_S = red (F|_S)`, under clause (3′) at the stages `< i`. -/
theorem support_traceFamilyFrom_eq_support_boundarySeq {F : HypersurfaceFamily M} (hF : F.IsSnc ψ)
    (hFH : F.HasSncWithProper ψ H s) (i : Fin (S.length + 1))
    (h3 : ∀ i' : Fin S.length, i'.1 < i.1 →
      (S.boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E)) i'.castSucc).HasOnlyNormalCrossingsWith
        (S.center i')) :
    (S.traceFamilyFrom hH hc F i).support =
      ((S.restrictSubmanifold hH hc).boundarySeq
        ((hH.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)) i).support := by
  obtain ⟨hsnc, heq⟩ := isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt hF i h3
  rw [S.support_traceFamilyFrom hH hc F i,
    S.support_boundarySeq_restrictSubmanifold_of_support_eq hH hc _ _
      (S.support_idealSheaf_traceFamily_eq hH hc hF hFH) i, heq]
  exact congrArg (Set.preimage ⇑(S.restrictIncl hH hc i)) hsnc.cosupport_idealSheaf.symm

/-- The boundary of `Π|_S` started with `E|_S = red (F|_S)` is the reduced ideal sheaf of its
support at every stage — at stage `0` because `F|_S` has simple normal crossings, at a later stage
the `red` branch of the recursion ([Hir64, Ch. 0, §7, Main Theorem II′(N)]), the vanishing ideals
of `|E_i ∩ S_i|` having local generators because the trace family from `F` has simple normal
crossings (the proper invariant `hprop` at the stages `≤ i`). -/
theorem stalkIdeal_boundarySeq_restrictSubmanifold_from {F : HypersurfaceFamily M} (hF : F.IsSnc ψ)
    (hFH : F.HasSncWithProper ψ H s) (i : Fin (S.length + 1))
    (h3 : ∀ i' : Fin S.length, i'.1 < i.1 →
      (S.boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E)) i'.castSucc).HasOnlyNormalCrossingsWith
        (S.center i'))
    (hprop : ∀ j : Fin (S.length + 1), j.1 ≤ i.1 →
      (S.totalTransformSeqFrom F j).HasSncWithProper ψ (S.strictTransformSeq H j) s)
    (x : (S.restrictSubmanifold hH hc).stage i) :
    ((S.restrictSubmanifold hH hc).boundarySeq
        ((hH.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)) i).stalkIdeal x =
      vanishingStalk (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)
        (((S.restrictSubmanifold hH hc).boundarySeq
          ((hH.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)) i).support) x := by
  revert x
  induction i using Fin.induction with
  | zero =>
    intro x
    have hsnc₀ := hH.isSnc_traceFamily hF hFH
    change ((hH.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)).stalkIdeal x =
      vanishingStalk (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)
        ((hH.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)).support x
    rw [hsnc₀.stalkIdeal_idealSheaf x, hsnc₀.cosupport_idealSheaf]
  | succ i _ =>
    intro x
    have e1 : (S.restrictSubmanifold hH hc).boundarySeq
        ((hH.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)) i.succ =
        IdealSheaf.reducedTransform ((S.restrictSubmanifold hH hc).map i)
          ((S.restrictSubmanifold hH hc).boundarySeq
            ((hH.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)) i.castSucc)
          ((S.restrictSubmanifold hH hc).center i) := rfl
    have hset : ⇑((S.restrictSubmanifold hH hc).map i) ⁻¹'
          ((S.restrictSubmanifold hH hc).boundarySeq
            ((hH.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)) i.castSucc).support ∪
        ⇑((S.restrictSubmanifold hH hc).map i) ⁻¹'
          ((S.restrictSubmanifold hH hc).center i).support =
        (S.traceFamilyFrom hH hc F i.succ).support := by
      rw [S.support_traceFamilyFrom_eq_support_boundarySeq hH hc hF hFH i.succ h3, e1]
      exact (reducedTransform_support _ _ _).symm
    have hloc := (S.isSnc_traceFamilyFrom hH hc F i.succ
      (isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt hF i.succ h3).1
      (hprop i.succ le_rfl)).hasLocalGenerators_vanishingStalk_support
    rw [← hset] at hloc
    rw [e1]
    exact (reducedTransform_stalkIdeal_of_hasLocalGenerators _ _ _ hloc x).trans
      (congrArg (fun t => vanishingStalk (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜) t x)
        (reducedTransform_support _ _ _).symm)

/-- The boundary of `Π|_S` started with `E|_S` is the reduced ideal sheaf of the trace of the
boundary family from `F` — both are the reduced ideal sheaves of the same set ([Kol07, Definition
30.2] with the boundary `E = red F`). -/
theorem boundarySeq_restrictSubmanifold_eq_idealSheaf_traceFamilyFrom {F : HypersurfaceFamily M}
    (hF : F.IsSnc ψ) (hFH : F.HasSncWithProper ψ H s) (i : Fin (S.length + 1))
    (h3 : ∀ i' : Fin S.length, i'.1 < i.1 →
      (S.boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E)) i'.castSucc).HasOnlyNormalCrossingsWith
        (S.center i'))
    (hprop : ∀ j : Fin (S.length + 1), j.1 ≤ i.1 →
      (S.totalTransformSeqFrom F j).HasSncWithProper ψ (S.strictTransformSeq H j) s) :
    (S.restrictSubmanifold hH hc).boundarySeq
        ((hH.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)) i =
      (S.traceFamilyFrom hH hc F i).idealSheaf := by
  refine IdealSheaf.ext fun x => ?_
  rw [S.stalkIdeal_boundarySeq_restrictSubmanifold_from hH hc hF hFH i h3 hprop x,
    (S.isSnc_traceFamilyFrom hH hc F i
      (isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt hF i h3).1
      (hprop i le_rfl)).stalkIdeal_idealSheaf x,
    S.support_traceFamilyFrom_eq_support_boundarySeq hH hc hF hFH i h3]

/-- The normal-crossings clause (3′) of [Kol07, Definition 66] for `Π|_S`: along a succession of
order `≥ m` with the empty boundary and centres `Z_i ⊆ S_i`, the boundary `E'_i` of the restricted
succession `Π|_S` has only normal crossings with its centre `Z_i ∩ S_i` at every stage. Proof:
`E'_i` is the reduced ideal sheaf of the trace family
(`boundarySeq_restrictSubmanifold_eq_idealSheaf_traceFamily`), the centre of `Π|_S` is the ideal
sheaf of the closed submanifold `Z_i ∩ S_i` of `S_i` (`restrictCenterSub'`), and the dictionary
`hasOnlyNormalCrossingsWith_idealSheaf_iff` reduces clause (3′) to "`Z_i ∩ S_i` has simple normal
crossings with the trace family" (`hasSncWith_traceFamily`, from a chart adapted simultaneously to
the centre, the submanifold and the family). -/
theorem boundarySeq_restrictSubmanifold_hasOnlyNormalCrossingsWith_center
    (hge : S.IsOfOrderGe J m (⊤)) (i : Fin S.length) :
    ((S.restrictSubmanifold hH hc).boundarySeq (⊤)
      i.castSucc).HasOnlyNormalCrossingsWith ((S.restrictSubmanifold hH hc).center i) := by
  rw [S.boundarySeq_restrictSubmanifold_eq_idealSheaf_traceFamily hH hc hge i.castSucc]
  obtain ⟨i, hi⟩ := i
  cases i with
  | zero =>
    exact (hasOnlyNormalCrossingsWith_idealSheaf_iff
      (S.isSnc_traceFamily hH hc hge (Fin.castSucc ⟨0, hi⟩)) (S.restrictCenterSub' hH hc 0 hi)).mpr
      ((S.isClosedSubmanifold_strictTransformSeqAux _ hH hc 0
          (Nat.lt_succ_of_lt hi)).hasSncWith_traceFamily
        (isSnc_totalTransformSeq hge (Fin.castSucc ⟨0, hi⟩)) (S.restrictCenterSub 0 hi)
        (hc ⟨0, hi⟩) (hasSncWith_totalTransformSeq_center hge ⟨0, hi⟩)
        (S.hasSncWithProper_totalTransformSeq_strictTransformSeq hH hc hge
          (Fin.castSucc ⟨0, hi⟩)))
  | succ k =>
    exact (hasOnlyNormalCrossingsWith_idealSheaf_iff
      (S.isSnc_traceFamily hH hc hge (Fin.castSucc ⟨k + 1, hi⟩))
      (S.restrictCenterSub' hH hc (k + 1) hi)).mpr
      ((S.isClosedSubmanifold_strictTransformSeqAux _ hH hc (k + 1)
          (Nat.lt_succ_of_lt hi)).hasSncWith_traceFamily
        (isSnc_totalTransformSeq hge (Fin.castSucc ⟨k + 1, hi⟩))
        (S.restrictCenterSub (k + 1) hi) (hc ⟨k + 1, hi⟩)
        (hasSncWith_totalTransformSeq_center hge ⟨k + 1, hi⟩)
        (S.hasSncWithProper_totalTransformSeq_strictTransformSeq hH hc hge
          (Fin.castSucc ⟨k + 1, hi⟩)))

end AnalyticManifold.FiniteSuccession

end
