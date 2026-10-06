/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.BoundaryFamily
public import Hironaka.Manifold.FiniteSuccession.Restrict.Pushforward
public import Hironaka.Manifold.IdealSheaf.Tuning
public import Hironaka.Manifold.Snc.Trace
public import Hironaka.Resolution.Analytic.LocalIsoEquiv
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
import Hironaka.Resolution.Analytic.GoingUp.Corollary85
import Hironaka.Resolution.Analytic.GoingUp.Corollary89
import Hironaka.Resolution.Analytic.GoingUp.NormalCrossingsTransport
import Hironaka.Resolution.Analytic.GoingUp.StageIso
import Hironaka.Resolution.Analytic.OrderReduction.BDLift
import Hironaka.Resolution.Analytic.OrderReduction.Step22Defs
import Hironaka.Resolution.Analytic.Restrict.BoundaryTrace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Corollary 85 with the hypersurface in the boundary

In the proof of [Kol07, Lemma 102] the going-up theorem gives a blow-up sequence of order `m`
starting with `(X_0, I_0, E - E^j)`, and, `S` being `E^j`, "every blow-up center is a smooth
subvariety" of the transform of `E^j`, so that one has in fact a blow-up sequence of order `m`
starting with `(X_0, I_0, E)`. This module is that sentence: the going-up statement
[Kol07, Corollary 85] for the push-forward along a closed hypersurface `S`, with the boundary
`F + S` (`HypersurfaceFamily.append`) in place of `F`.

* `HypersurfaceFamily.support_append`, `FiniteSuccession.isClosed_hyp_totalTransformSeqFrom`,
  `FiniteSuccession.support_totalTransformSeqFrom_append` — the support of the boundary family
  from the start `F + S` at stage `i` is the support from the start `F` together with the strict
  transform `S_i` (the exceptional divisors already lie in the family from `F`, and the preimage of
  `S_i` is `S_{i+1}` up to the exceptional divisor).
* `FiniteSuccession.pushforward_hasOnlyNormalCrossingsWith_center_append_of_forall_lt` — the
  normal-crossings clause of the push-forward with the boundary `F + S` at stage `i`, from the
  clause of the sequence on `S` with the boundary `F|_S`: the boundary at stage `i` is the reduced
  ideal sheaf of `F_i + S_i`, and the lifting with the hypersurface appended (`BDLift.lean`) lifts
  the clause through the identification of the stages of the restricted sequence.
* `FiniteSuccession.pushforward_isOfOrderGe_append` — **[Kol07, Corollary 85] with `S` in the
  boundary**: for `I` D-balanced with `ord I ≤ m` everywhere, the push-forward of a sequence of
  order `≥ m` for `(I|_S, m)` with the boundary `F|_S` is of order `≥ m` for `(I, m)` with the
  boundary `F + S`; the order clause does not involve the boundary (`le_ordAlong_pushforward`).

It is used in `BDCore.lean` for the order clause of Lemma 102 and in `BDCosupp.lean` for its
clause (1).
-/

public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

section Support

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

omit [TopologicalSpace M] [ChartedSpace E M] in
/-- The support of `F + H` is the support of `F` together with `H`. -/
theorem HypersurfaceFamily.support_append (F : HypersurfaceFamily M) (H : Set M) :
    (F.append H).support = F.support ∪ H := by
  ext x
  simp only [HypersurfaceFamily.support, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨k, hk⟩
    rcases k with j | u
    · exact Or.inl ⟨j, hk⟩
    · exact Or.inr hk
  · rintro (⟨j, hj⟩ | hH)
    · exact ⟨toLex (Sum.inl j), hj⟩
    · exact ⟨toLex (Sum.inr PUnit.unit), hH⟩

end Support

end Manifold

namespace AnalyticManifold.FiniteSuccession

open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

section SupportSeq

variable (B : FiniteSuccession M)

/-- Along any succession of blow-ups the members of the boundary family from a start with closed
members stay closed. -/
theorem isClosed_hyp_totalTransformSeqFrom {F : HypersurfaceFamily M}
    (hF : ∀ j, IsClosed (F.hyp j)) (i : Fin (B.length + 1)) :
    ∀ k, IsClosed ((B.totalTransformSeqFrom F i).hyp k) := by
  induction i using Fin.induction with
  | zero => exact hF
  | succ i _ =>
    rw [totalTransformSeqFrom_succ]
    exact fun k => HypersurfaceFamily.isClosed_hyp_totalTransform (B.map i).contMDiff.continuous
      (IdealSheaf.isClosed_support (J := B.center i)) _ k

/-- [Kol07, Definition 25] with the hypersurface appended: the support of the boundary family from
the start `F + S` at stage `i` is the support from the start `F` together with the strict transform
`S_i`, since the preimage of `S_i` is `S_{i+1}` together with the exceptional divisor, which the
family from `F` already carries. -/
theorem support_totalTransformSeqFrom_append {F : HypersurfaceFamily M}
    (hF : ∀ j, IsClosed (F.hyp j)) {S : Set M} (hS : IsClosed S) (i : Fin (B.length + 1)) :
    (B.totalTransformSeqFrom (F.append S) i).support =
      (B.totalTransformSeqFrom F i).support ∪ B.strictTransformSeq S i := by
  have hFS : ∀ k, IsClosed ((F.append S).hyp k) := fun k => by
    rcases k with j | u
    · exact hF j
    · exact hS
  induction i using Fin.induction with
  | zero => exact HypersurfaceFamily.support_append F S
  | succ i ih =>
    rw [totalTransformSeqFrom_succ, totalTransformSeqFrom_succ, strictTransformSeq_succ,
      HypersurfaceFamily.support_totalTransform _ _ _ (B.map i).contMDiff.continuous
        (B.isClosed_hyp_totalTransformSeqFrom hFS i.castSucc),
      HypersurfaceFamily.support_totalTransform _ _ _ (B.map i).contMDiff.continuous
        (B.isClosed_hyp_totalTransformSeqFrom hF i.castSucc), ih, Set.preimage_union]
    have h1 : ⇑(B.map i) ⁻¹' B.strictTransformSeq S i.castSucc ∪
        ⇑(B.map i) ⁻¹' (B.center i).support =
        strictTransformSet (B.map i) (B.center i).support (B.strictTransformSeq S i.castSucc) ∪
          ⇑(B.map i) ⁻¹' (B.center i).support := by
      apply Set.Subset.antisymm
      · exact Set.union_subset preimage_subset_strictTransform_union Set.subset_union_right
      · exact Set.union_subset_union_left _ (strictTransform_subset_preimage
          (B.map i).contMDiff.continuous (B.isClosed_strictTransformSeq S hS i.castSucc))
    ext x
    have hx1 := Set.ext_iff.mp h1 x
    simp only [Set.mem_union] at hx1 ⊢
    tauto

end SupportSeq

section Corollary85Append

variable {S : Set M} (hS : IsClosedSubmanifold ψ S 1) (T : FiniteSuccession hS.toAnalyticManifold)
  {I : IdealSheaf M} {m : ℕ}

/-- The normal-crossings clause of the push-forward with the boundary `F + S` at stage `i`, given
it at the stages `< i`: the boundary at stage `i` is the reduced ideal sheaf of `F_i + S_i`, and the
clause of the sequence `T` on `S` lifts through the identification of the stages of `T` with those
of the restriction of the push-forward to `S` by
`hasOnlyNormalCrossingsWith_idealSheaf_append_of_traceFamily`
(the proof of [Kol07, Lemma 102], "every blow-up center is a smooth subvariety" of the transform
of `E^j`). -/
theorem pushforward_hasOnlyNormalCrossingsWith_center_append_of_forall_lt
    {F : HypersurfaceFamily M} (hF : F.IsSnc ψ) (hFS : F.HasSncWithProper ψ S 1)
    {J : IdealSheaf hS.toAnalyticManifold}
    (hge : T.IsOfOrderGe J m ((hS.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - 1) → 𝕜)))
    (i : Fin T.length)
    (h3 : ∀ i' : Fin T.length, i'.1 < i.1 →
      ((T.pushforward hS).boundarySeq ((F.append S).idealSheaf (𝕜 := 𝕜) (E := E))
        i'.castSucc).HasOnlyNormalCrossingsWith ((T.pushforward hS).center i')) :
    ((T.pushforward hS).boundarySeq ((F.append S).idealSheaf (𝕜 := 𝕜) (E := E))
      i.castSucc).HasOnlyNormalCrossingsWith ((T.pushforward hS).center i) := by
  have hFS' : (F.append S).IsSnc ψ := HypersurfaceFamily.isSnc_append_of_hasSncWithProper hF hS hFS
  -- the normal-crossings clause for the boundary `red F` at every stage (Corollary 85)
  have hcsF : ∀ i' : Fin (T.pushforward hS).length, i'.1 < i.castSucc.1 →
      ((T.pushforward hS).boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E))
        i'.castSucc).HasOnlyNormalCrossingsWith ((T.pushforward hS).center i') :=
    fun i' _ => T.pushforward_hasOnlyNormalCrossingsWith_center_from hS hF hFS hge i'
  have hcs' : ∀ i' : Fin (T.pushforward hS).length, i'.1 < i.castSucc.1 →
      ((T.pushforward hS).boundarySeq ((F.append S).idealSheaf (𝕜 := 𝕜) (E := E))
        i'.castSucc).HasOnlyNormalCrossingsWith ((T.pushforward hS).center i') :=
    fun i' hi' => h3 i' (by rw [Fin.val_castSucc] at hi'; exact hi')
  -- the normal-crossings clause of `T` at stage `i`, transported to `Π|_S` along `e_i⁻¹`
  have hT : IdealSheaf.HasOnlyNormalCrossingsWith
      (T.boundarySeq ((hS.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - 1) → 𝕜)) i.castSucc)
      (T.center i) := (hge i).1
  have key : ∀ J' : IdealSheaf
      (((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).stage i.castSucc),
      (J'.pullback ⇑(T.pushforwardStageIso hS i.castSucc)
        (T.pushforwardStageIso hS i.castSucc).contMDiff).pullback
          ⇑(T.pushforwardStageIso hS i.castSucc).symm
          (T.pushforwardStageIso hS i.castSucc).symm.contMDiff = J' := fun J' =>
    (IdealSheaf.pullback_pullback J' _ _ _ _).trans
      ((IdealSheaf.pullback_congr J' _ contMDiff_id
        (funext fun x => (T.pushforwardStageIso hS i.castSucc).apply_symm_apply x)).trans
        (IdealSheaf.pullback_id_eq_self J'))
  have h1 := hT.pullback_diffeomorph (T.pushforwardStageIso hS i.castSucc).symm
  have h2 : IdealSheaf.HasOnlyNormalCrossingsWith
      (((((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).boundarySeq
        ((hS.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - 1) → 𝕜)) i.castSucc).pullback
          ⇑(T.pushforwardStageIso hS i.castSucc)
          (T.pushforwardStageIso hS i.castSucc).contMDiff).pullback
            ⇑(T.pushforwardStageIso hS i.castSucc).symm
            (T.pushforwardStageIso hS i.castSucc).symm.contMDiff)
      (((((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).center i).pullback
          ⇑(T.pushforwardStageIso hS i.castSucc)
          (T.pushforwardStageIso hS i.castSucc).contMDiff).pullback
            ⇑(T.pushforwardStageIso hS i.castSucc).symm
            (T.pushforwardStageIso hS i.castSucc).symm.contMDiff) :=
    (congrArg₂ (fun (X Y : IdealSheaf (T.stage i.castSucc)) =>
        IdealSheaf.HasOnlyNormalCrossingsWith
          (X.pullback ⇑(T.pushforwardStageIso hS i.castSucc).symm
            (T.pushforwardStageIso hS i.castSucc).symm.contMDiff)
          (Y.pullback ⇑(T.pushforwardStageIso hS i.castSucc).symm
            (T.pushforwardStageIso hS i.castSucc).symm.contMDiff))
      (T.boundarySeq_pushforwardStageIso hS i.castSucc) (T.center_pushforwardStageIso hS i)).mpr h1
  have hR : IdealSheaf.HasOnlyNormalCrossingsWith
      (((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).boundarySeq
        ((hS.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - 1) → 𝕜)) i.castSucc)
      (((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).center i) :=
    (congrArg₂ IdealSheaf.HasOnlyNormalCrossingsWith (key _) (key _)).mp h2
  -- the boundary of `Π|_S` is the reduced ideal sheaf of the trace of `F_i^X` (from the start `F`)
  obtain ⟨hsnc, -⟩ := isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt
    (S := T.pushforward hS) hF i.castSucc hcsF
  have hprop : ∀ j : Fin ((T.pushforward hS).length + 1), j.1 ≤ i.castSucc.1 →
      ((T.pushforward hS).totalTransformSeqFrom F j).HasSncWithProper ψ
        ((T.pushforward hS).strictTransformSeq S j) 1 :=
    fun j hj =>
      (T.pushforward hS).hasSncWithProper_totalTransformSeqFrom_strictTransformSeq_of_forall_lt hS
        (T.centersIn_pushforward hS) hF hFS j fun i' hi' => hcsF i' (by omega)
  have htr : ((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).boundarySeq
      ((hS.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - 1) → 𝕜)) i.castSucc =
      ((T.pushforward hS).traceFamilyFrom hS (T.centersIn_pushforward hS) F
        i.castSucc).idealSheaf :=
    (T.pushforward hS).boundarySeq_restrictSubmanifold_eq_idealSheaf_traceFamilyFrom hS
      (T.centersIn_pushforward hS) hF hFS i.castSucc hcsF hprop
  have hR' : IdealSheaf.HasOnlyNormalCrossingsWith
      ((T.pushforward hS).traceFamilyFrom hS (T.centersIn_pushforward hS) F i.castSucc).idealSheaf
      (((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).center i) :=
    (congrArg (fun X => IdealSheaf.HasOnlyNormalCrossingsWith X
      (((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).center i))
      htr).mp hR
  -- the boundary from the start `F + S` at stage `i` is the reduced ideal sheaf of `F_i + S_i`
  obtain ⟨-, hbd'⟩ := isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt
    (S := T.pushforward hS) hFS' i.castSucc hcs'
  have hsupp : ((T.pushforward hS).totalTransformSeqFrom (F.append S) i.castSucc).idealSheaf
      (𝕜 := 𝕜) (E := E) =
      (((T.pushforward hS).totalTransformSeqFrom F i.castSucc).append
        ((T.pushforward hS).strictTransformSeq S i.castSucc)).idealSheaf := by
    apply HypersurfaceFamily.idealSheaf_eq_of_support_eq
    rw [HypersurfaceFamily.support_append]
    exact (T.pushforward hS).support_totalTransformSeqFrom_append (fun j => (hF.1 j).isClosed)
      hS.isClosed i.castSucc
  -- lift to `X_i`, with `S_i` in the boundary
  obtain ⟨k, hk⟩ := i
  have hct : ((T.pushforward hS).restrictCenterSub (ψ := ψ) k hk).idealSheaf =
      (T.pushforward hS).center ⟨k, hk⟩ :=
    (IsClosedSubmanifold.idealSheaf_congr ((T.pushforward hS).restrictCenterSub (ψ := ψ) k hk)
      ((T.pushforward hS).isClosedSubmanifold_center ⟨k, hk⟩) rfl).trans
      ((T.pushforward hS).idealSheaf_center ⟨k, hk⟩)
  refine (congrArg₂ IdealSheaf.HasOnlyNormalCrossingsWith (hbd'.trans hsupp)
    hct.symm).mpr ?_
  cases k with
  | zero =>
    exact hasOnlyNormalCrossingsWith_idealSheaf_append_of_traceFamily
      ((T.pushforward hS).isClosedSubmanifold_strictTransformSeqAux _ hS
          (T.centersIn_pushforward hS) 0 _) _ hsnc
      (hprop _ le_rfl) ((T.pushforward hS).restrictCenterSub (ψ := ψ) 0 hk)
      (T.centersIn_pushforward hS ⟨0, hk⟩) hR'
  | succ k =>
    exact hasOnlyNormalCrossingsWith_idealSheaf_append_of_traceFamily
      ((T.pushforward hS).isClosedSubmanifold_strictTransformSeqAux _ hS
          (T.centersIn_pushforward hS) (k + 1) _) _ hsnc
      (hprop _ le_rfl) ((T.pushforward hS).restrictCenterSub (ψ := ψ) (k + 1) hk)
      (T.centersIn_pushforward hS ⟨k + 1, hk⟩) hR'

variable [FiniteDimensional 𝕜 E]

/-- **[Kol07, Corollary 85] with the hypersurface in the boundary** (the proof of
[Kol07, Lemma 102]): for `I` D-balanced with `ord I ≤ m` everywhere and `F` with simple normal
crossings having simple normal crossings with the closed hypersurface `S` properly, the
push-forward of a sequence of order `≥ m` for `(I|_S, m)` with the boundary `F|_S` is of order
`≥ m` for `(I, m)` with the boundary `F + S`. The order clause is `le_ordAlong_pushforward` and
does not involve the boundary; the normal-crossings clause is
`pushforward_hasOnlyNormalCrossingsWith_center_append_of_forall_lt`, stage by stage. -/
theorem pushforward_isOfOrderGe_append {F : HypersurfaceFamily M} (hI : I.IsDBalanced m)
    (hmax : ∀ y, I.ord y ≤ m) (hF : F.IsSnc ψ) (hFS : F.HasSncWithProper ψ S 1)
    (hT : T.IsOfOrderGe (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) m
      ((hS.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - 1) → 𝕜))) :
    (T.pushforward hS).IsOfOrderGe I m ((F.append S).idealSheaf (𝕜 := 𝕜) (E := E)) := by
  suffices h : ∀ N : ℕ, ∀ i : Fin T.length, i.1 < N →
      ((T.pushforward hS).boundarySeq ((F.append S).idealSheaf (𝕜 := 𝕜) (E := E))
        i.castSucc).HasOnlyNormalCrossingsWith ((T.pushforward hS).center i) by
    intro i
    exact ⟨h (i.1 + 1) i (Nat.lt_succ_self _), le_ordAlong_pushforward hS T hI hmax hT i⟩
  intro N
  induction N with
  | zero => exact fun i hi => absurd hi (Nat.not_lt_zero _)
  | succ N ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact ih i hlt
    · exact T.pushforward_hasOnlyNormalCrossingsWith_center_append_of_forall_lt hS hF hFS hT i
        fun i' hi' => ih i' (by omega)

end Corollary85Append

end AnalyticManifold.FiniteSuccession

end
