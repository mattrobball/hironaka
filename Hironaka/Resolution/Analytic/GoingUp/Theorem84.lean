/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Order
public import Hironaka.Manifold.FiniteSuccession.Restrict.Pushforward
public import Hironaka.Manifold.IdealSheaf.Tuning
public import Hironaka.Manifold.Snc.Trace
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.NormalCrossings
import Hironaka.Resolution.Analytic.GoingUp.Corollary89
import Hironaka.Resolution.Analytic.GoingUp.MaxOrder
import Hironaka.Resolution.Analytic.GoingUp.NormalCrossingsTransport
import Hironaka.Resolution.Analytic.GoingUp.SncLift
import Hironaka.Resolution.Analytic.GoingUp.StageIso
import Hironaka.Resolution.Analytic.Restrict.BoundaryTrace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's Theorem 84: the normal-crossings clause of the push-forward, and the theorem

The going-up theorem [Kol07, Theorem 84] lifts a smooth blow-up sequence `T` of order `≥ m` for
`(I|_S, m)` on a hypersurface `S ⊆ X` to the push-forward `Π = j_* T` of order `≥ m` for `(I, m)`
on `X`, when `I` is D-balanced with `max-ord I = m`. The order clause (4′) is Kollár's induction
[Kol07, 90] (`le_ordAlong_pushforward` in `GoingUp/Corollary89.lean`); this module proves the
normal-crossings clause (3′), that the centre `Z_i^X = j_i(Z_i)` of the push-forward has only
normal crossings with the boundary `E_i^X` of the push-forward at every stage, and assembles the
theorem.

Kollár argues the order clause only (his items 86–90) and states in [Kol07, 30.3] that the
push-forward of a smooth blow-up sequence is smooth, without further argument; the clause is proved
here from the restriction of sequences [Kol07, 30.2] and Hironaka's reduced boundary
[Hir64, Main Theorem II′(N), p. 156]. The boundary `E_i^X` is the reduced ideal sheaf of the family
`F_i^X` of exceptional divisors, which has simple normal crossings with the strict transform `S_i`
properly, and its trace on `S_i` is, through the identification `e_i : T_i ≃ S_i`, the boundary of
`T`; clause (3′) of `T` at stage `i` transports along `e_i`
(`HasOnlyNormalCrossingsWith.pullback_diffeomorph`) to the trace level and lifts to `X_i` by
`hasSncWith_of_hasSncWith_traceFamily`. The induction on the stage is the point: the identification
of `E_i^X` with `F_i^X` and of its trace with the boundary of `Π|_S` (in the prefix-bounded forms
`…_of_forall_lt` of `Hironaka/Manifold/FiniteSuccession/BoundaryFamily.lean` and
`Restrict/BoundaryTrace.lean`) uses clause (3′) at the stages `< i` only, so the argument closes
stage by stage.

* `hasOnlyNormalCrossingsWith_idealSheaf_of_traceFamily`: for one closed submanifold, clause (3′)
  at the trace level implies clause (3′) in the ambient manifold.
* `pushforward_hasOnlyNormalCrossingsWith_center_of_forall_lt`: the stage step.
* `pushforward_hasOnlyNormalCrossingsWith_center`: clause (3′) of the push-forward.
* `pushforward_isOfOrderGe`, `pushforward_isOfOrder`, `pushforward_isOfOrder_of_not_subset_cosupp`:
  Theorem 84 in the `≥ m` form, with the exact order (by [Kol07, Remark 67]), and as printed.

Together with going down [Kol07, 51.1] this yields Kollár's Corollary 85, in
`GoingUp/Corollary85.lean`.
-/

public section

noncomputable section

open TopologicalSpace Topology
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {X : AnalyticManifold.{u} 𝕜 E}

/-- The lifting of clause (3′) from a closed submanifold to the ambient manifold (the ingredient
of [Kol07, 30.2] the push-forward needs): for a closed submanifold `S ⊆ X` and a simple normal
crossing family `F` having simple normal crossings with `S` properly, a closed submanifold `Z ⊆ S`
whose ideal sheaf in `S` has only normal crossings with the reduced ideal sheaf of the trace `F|_S`
has, in `X`, an ideal sheaf with only normal crossings with the reduced ideal sheaf of `F`: the
dictionary `hasOnlyNormalCrossingsWith_idealSheaf_iff` on both sides around
`hasSncWith_of_hasSncWith_traceFamily`. -/
theorem hasOnlyNormalCrossingsWith_idealSheaf_of_traceFamily {S : Set X} {s : ℕ}
    (hS : IsClosedSubmanifold ψ S s) (F : HypersurfaceFamily X) (hF : F.IsSnc ψ)
    (hFS : F.HasSncWithProper ψ S s) {Z : Set X} {c : ℕ} (hZ : IsClosedSubmanifold ψ Z c)
    (hZS : Z ⊆ S)
    (h : AnalyticManifold.IdealSheaf.HasOnlyNormalCrossingsWith (hS.traceFamily F).idealSheaf
      (hS.preimage_val_of_subset hZ hZS).idealSheaf) :
    AnalyticManifold.IdealSheaf.HasOnlyNormalCrossingsWith F.idealSheaf hZ.idealSheaf := by
  have htr := (hasOnlyNormalCrossingsWith_idealSheaf_iff (hS.isSnc_traceFamily hF hFS)
    (hS.preimage_val_of_subset hZ hZS)).mp h
  have hlift := hasSncWith_of_hasSncWith_traceFamily hS F hF hFS (hS.preimage_val_of_subset hZ hZS)
    htr
  have hZ' : IsClosedSubmanifold ψ (hS.imageVal (hS.preimageVal Z)) (c - s + s) :=
    hS.imageVal_isClosedSubmanifold (hS.preimage_val_of_subset hZ hZS)
  have hset : hS.imageVal (hS.preimageVal Z) = Z := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hx
      exact ⟨(⟨x, hZS hx⟩ : S), hx, rfl⟩
  rw [← IsClosedSubmanifold.idealSheaf_congr hZ' hZ hset]
  exact (hasOnlyNormalCrossingsWith_idealSheaf_iff hF hZ').mpr hlift

end Hironaka.Manifold

namespace AnalyticManifold.FiniteSuccession

open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

section Step

variable {S : Set M} {s : ℕ} (hS : IsClosedSubmanifold ψ S s)
  (T : FiniteSuccession hS.toAnalyticManifold) {J : IdealSheaf hS.toAnalyticManifold} {m : ℕ}

/-- The stage step for clause (3′) of the push-forward ([Kol07, 30.2–30.3]): if the push-forward
`Π = j_* T` of a sequence `T` of order `≥ m` (with the empty boundary) satisfies clause (3′) at
every stage `< i`, it satisfies it at stage `i`. Through `e_i : T_i ≃ S_i`, clause (3′) of `T` at
stage `i` becomes clause (3′) of `Π|_S` (`HasOnlyNormalCrossingsWith.pullback_diffeomorph` along
`e_i⁻¹`, the boundary and centre identities `boundarySeq_pushforwardStageIso`,
`center_pushforwardStageIso`); by the prefix-bounded comparison of the boundary with the family of
exceptional divisors, the boundary of `Π|_S` is the reduced ideal sheaf of the trace of `F_i^X` on
`S_i`, and the lifting `hasOnlyNormalCrossingsWith_idealSheaf_of_traceFamily` gives clause (3′) of
`Π` at stage `i`. -/
theorem pushforward_hasOnlyNormalCrossingsWith_center_of_forall_lt
    (hge : T.IsOfOrderGe J m (⊤)) (i : Fin T.length)
    (h3 : ∀ i' : Fin T.length, i'.1 < i.1 →
      ((T.pushforward hS).boundarySeq (⊤) i'.castSucc).HasOnlyNormalCrossingsWith
        ((T.pushforward hS).center i')) :
    ((T.pushforward hS).boundarySeq (⊤) i.castSucc).HasOnlyNormalCrossingsWith
      ((T.pushforward hS).center i) := by
  have hcs : ∀ i' : Fin (T.pushforward hS).length, i'.1 < i.castSucc.1 →
      ((T.pushforward hS).boundarySeq (⊤) i'.castSucc).HasOnlyNormalCrossingsWith
        ((T.pushforward hS).center i') :=
    fun i' hi' => h3 i' (by rw [Fin.val_castSucc] at hi'; exact hi')
  -- clause (3′) of `T` at stage `i`, transported to `Π|_S` along `e_i⁻¹`
  have hT : IdealSheaf.HasOnlyNormalCrossingsWith
      (T.boundarySeq (⊤) i.castSucc) (T.center i) := (hge i).1
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
        (⊤) i.castSucc).pullback
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
        (⊤) i.castSucc)
      (((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).center i) :=
    (congrArg₂ IdealSheaf.HasOnlyNormalCrossingsWith (key _) (key _)).mp h2
  -- the boundary of `Π|_S` is the reduced ideal sheaf of the trace of `F_i^X`
  have hbd : (T.pushforward hS).boundarySeq (⊤) i.castSucc =
      ((T.pushforward hS).totalTransformSeq i.castSucc).idealSheaf :=
    boundarySeq_eq_idealSheaf_totalTransformSeq_of_forall_lt (S := T.pushforward hS) ψ i.castSucc
      hcs
  have hsnc : ((T.pushforward hS).totalTransformSeq i.castSucc).IsSnc ψ :=
    isSnc_totalTransformSeq_of_forall_lt (S := T.pushforward hS) i.castSucc hcs
  have hprop : ((T.pushforward hS).totalTransformSeq i.castSucc).HasSncWithProper ψ
      ((T.pushforward hS).strictTransformSeq S i.castSucc) s :=
    (T.pushforward hS).hasSncWithProper_totalTransformSeq_strictTransformSeq_of_forall_lt hS
      (T.centersIn_pushforward hS) i.castSucc hcs
  have htr : ((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).boundarySeq
      (⊤) i.castSucc =
      ((T.pushforward hS).traceFamily hS (T.centersIn_pushforward hS) i.castSucc).idealSheaf :=
    (T.pushforward hS).boundarySeq_restrictSubmanifold_eq_idealSheaf_traceFamily_of_forall_lt hS
      (T.centersIn_pushforward hS) i.castSucc hcs
  have hR' : IdealSheaf.HasOnlyNormalCrossingsWith
      ((T.pushforward hS).traceFamily hS (T.centersIn_pushforward hS) i.castSucc).idealSheaf
      (((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).center i) :=
    (congrArg (fun X => IdealSheaf.HasOnlyNormalCrossingsWith X
      (((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).center i))
      htr).mp hR
  -- lift to `X_i`
  obtain ⟨k, hk⟩ := i
  have hct : ((T.pushforward hS).restrictCenterSub (ψ := ψ) k hk).idealSheaf =
      (T.pushforward hS).center ⟨k, hk⟩ :=
    (IsClosedSubmanifold.idealSheaf_congr ((T.pushforward hS).restrictCenterSub (ψ := ψ) k hk)
      ((T.pushforward hS).isClosedSubmanifold_center ⟨k, hk⟩) rfl).trans
      ((T.pushforward hS).idealSheaf_center ⟨k, hk⟩)
  refine (congrArg₂ IdealSheaf.HasOnlyNormalCrossingsWith hbd hct.symm).mpr ?_
  cases k with
  | zero =>
    exact hasOnlyNormalCrossingsWith_idealSheaf_of_traceFamily
      ((T.pushforward hS).isClosedSubmanifold_strictTransformSeqAux _ hS
          (T.centersIn_pushforward hS) 0 _) _ hsnc hprop
      ((T.pushforward hS).restrictCenterSub (ψ := ψ) 0 hk) (T.centersIn_pushforward hS ⟨0, hk⟩) hR'
  | succ k =>
    exact hasOnlyNormalCrossingsWith_idealSheaf_of_traceFamily
      ((T.pushforward hS).isClosedSubmanifold_strictTransformSeqAux _ hS
          (T.centersIn_pushforward hS) (k + 1) _) _ hsnc
      hprop ((T.pushforward hS).restrictCenterSub (ψ := ψ) (k + 1) hk)
      (T.centersIn_pushforward hS ⟨k + 1, hk⟩) hR'

/-- **Clause (3′) of the push-forward** ([Kol07, 30.2–30.3] made precise, with Hironaka's reduced
boundary [Hir64, Main Theorem II′(N), p. 156]): the centre `Z_i^X` of `j_* T` has only normal
crossings with its boundary at every stage, for `T` of order `≥ m` with the empty boundary.
Induction on a bound for the stage with the stage step. -/
theorem pushforward_hasOnlyNormalCrossingsWith_center
    (hge : T.IsOfOrderGe J m (⊤)) (i : Fin T.length) :
    ((T.pushforward hS).boundarySeq (⊤) i.castSucc).HasOnlyNormalCrossingsWith
      ((T.pushforward hS).center i) := by
  suffices h : ∀ N : ℕ, ∀ i : Fin T.length, i.1 < N →
      ((T.pushforward hS).boundarySeq (⊤) i.castSucc).HasOnlyNormalCrossingsWith
        ((T.pushforward hS).center i) from h (i.1 + 1) i (Nat.lt_succ_self _)
  intro N
  induction N with
  | zero => exact fun i hi => absurd hi (Nat.not_lt_zero _)
  | succ N ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact ih i hlt
    · exact T.pushforward_hasOnlyNormalCrossingsWith_center_of_forall_lt hS hge i
        fun i' hi' => ih i' (by omega)

end Step

section Theorem84

variable [FiniteDimensional 𝕜 E] {S : Set M} (hS : IsClosedSubmanifold ψ S 1)
  (T : FiniteSuccession hS.toAnalyticManifold) {I : IdealSheaf M} {m : ℕ}

/-- **Theorem 84** [Kol07, Theorem 84] in the `≥ m` form: the push-forward `j_* T` of a smooth
blow-up sequence of order `≥ m` for `(I|_S, m)` (empty boundary) is of order `≥ m` for `(I, m)`,
when `I` is D-balanced with `ord I ≤ m` everywhere. Clause (4′) is Kollár's induction
(`le_ordAlong_pushforward`), clause (3′) is `pushforward_hasOnlyNormalCrossingsWith_center` (the
identification `S_{i+1} = (π_i)^{-1}_* S_i` of [Kol07, 30.2] and the lifting of simple normal
crossings; Kollár does not argue it beyond 30.2). -/
theorem pushforward_isOfOrderGe (hI : I.IsDBalanced m) (hmax : ∀ y, I.ord y ≤ m)
    (hT : T.IsOfOrderGe (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) m
      (⊤)) :
    (T.pushforward hS).IsOfOrderGe I m (⊤) := by
  intro i
  exact ⟨T.pushforward_hasOnlyNormalCrossingsWith_center hS hT i,
    le_ordAlong_pushforward hS T hI hmax hT i⟩

/-- **Theorem 84** [Kol07, Theorem 84], the conclusion as printed: `j_* T` is of order exactly `m`
([Kol07, Remark 67], `isOfOrder_of_isOfOrderGe_of_ord_le`). -/
theorem pushforward_isOfOrder (hI : I.IsDBalanced m) (hmax : ∀ y, I.ord y ≤ m)
    (hT : T.IsOfOrderGe (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) m
      (⊤)) :
    (T.pushforward hS).IsOfOrder I (⊤) m :=
  isOfOrder_of_isOfOrderGe_of_ord_le (T.pushforward hS) (T.pushforward_isOfOrderGe hS hI hmax hT)
    hmax

/-- **Theorem 84 as printed** [Kol07, Theorem 84]. The hypothesis `_hSc : S ⊄ cosupp(I, m)` is part
of Kollár's statement and is kept so that the theorem reads as printed; the proof does not need
it, because it is `pushforward_isOfOrder`, whose induction on the stage works for every smooth
hypersurface `S` (the algebraic version `IsDBalanced.isOrderSeq_pushforward` likewise does without
it). -/
theorem pushforward_isOfOrder_of_not_subset_cosupp (hI : I.IsDBalanced m)
    (hmax : ∀ y, I.ord y ≤ m) (_hSc : ¬ S ⊆ {x | (m : ℕ∞) ≤ I.ord x})
    (hT : T.IsOfOrderGe (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) m
      (⊤)) :
    (T.pushforward hS).IsOfOrder I (⊤) m :=
  T.pushforward_isOfOrder hS hI hmax hT

end Theorem84

end AnalyticManifold.FiniteSuccession

end
