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
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.FiniteSuccession.Restrict.CongrChart
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.NormalCrossings
import Hironaka.Resolution.Analytic.GoingUp.Corollary89
import Hironaka.Resolution.Analytic.GoingUp.MaxOrder
import Hironaka.Resolution.Analytic.GoingUp.NormalCrossingsTransport
import Hironaka.Resolution.Analytic.GoingUp.StageIso
import Hironaka.Resolution.Analytic.GoingUp.Theorem84
import Hironaka.Resolution.Analytic.MaximalContactTheorem
import Hironaka.Resolution.Analytic.Restrict.BoundaryTrace
import Hironaka.Resolution.Analytic.Restrict.GoingDown
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's Corollary 85: going up and down with a boundary

Kollár's Corollary 85 [Kol07, Corollary 85]: with `I` D-balanced of maximal order `m`, `H` a
smooth hypersurface of maximal contact and `E` a simple normal crossing divisor such that `E + H`
is a simple normal crossing divisor, pushing forward from `H` to `X` is a one-to-one correspondence
between smooth blow-up sequences of order `≥ m` starting with `(H, I|_H, m, E|_H)` and smooth
blow-up sequences of order `m` starting with `(X, I, E)`. This module proves both directions with
the boundary `E = red F`, for `F` a simple normal crossing family having simple normal crossings
with `H` properly.

Going up, (1) ⇒ (2): a sequence `T` of order `≥ m` for `(I|_H, m)` with the boundary `E|_H` pushes
forward to a sequence of order exactly `m` for `(I, m)` with the boundary `E`. The order clause is
Kollár's induction [Kol07, 90] (`le_ordAlong_pushforward`, which does not look at the boundary)
with [Kol07, Remark 67]; the normal-crossings clause is the argument of `GoingUp/Theorem84.lean`
from the start `F` instead of the empty family: the boundary `E_i^X` of the push-forward is the
reduced ideal sheaf of the family `F_i^X` from the start `F`, which has simple normal crossings
with the strict transform `H_i` properly (the invariant starts from the proper hypothesis
`F.HasSncWithProper H`), its trace on `H_i` is through `e_i : T_i ≃ H_i` the boundary of `T`
started with `E|_H`, and clause (3′) of `T` lifts stage by stage.

Going down, (2) ⇒ (1): for `H` in `MC(I)`, i.e. `I_H ⊆ D^{m−1}(I)` (the static form of maximal
contact, [Kol07, Theorem 80]), a sequence of order `m` for `(I, m)` with the boundary `E` has its
centres in the strict transforms of `H` and restricts to a sequence of order `≥ m` for
`(I|_H, m)` with the boundary `E|_H`: the order clause by `le_ordAlong_restrictSubmanifold`, the
normal-crossings clause because the boundary of `B|_H` is the reduced ideal sheaf of the trace of
`F_i` on `H_i` and `Z_i ∩ H_i` has simple normal crossings with that trace
(`hasSncWith_traceFamily`).

* `hasSncWithProper_totalTransformSeqFrom_strictTransformSeq_of_forall_lt`: the proper invariant
  from a start family `F` (`hasSncWithProper_totalTransformSeq_strictTransformSeq` is the empty
  start).
* `pushforward_hasOnlyNormalCrossingsWith_center_from_of_forall_lt`, `…_from`: clause (3′) of the
  push-forward from the start `F`.
* `pushforward_isOfOrderGe_of_isOfOrderGe_traceFamily`,
  `pushforward_isOfOrder_of_isOfOrderGe_traceFamily`: going up, in the `≥ m` form and as printed.
* `restrictSubmanifold_isOfOrderGe_traceFamily_of_isOfOrderGe`,
  `restrictSubmanifold_isOfOrderGe_of_isOfOrder_of_le_iteratedDeriv`: going down, for centres in
  the strict transforms of `H` and from a hypersurface in `MC(I)` ([Kol07, Theorem 80]).

Corollary 85 is the dimension reduction of the order-reduction algorithm: order reduction on `X`
is carried out on a hypersurface of maximal contact and pushed forward.
-/

public section

noncomputable section

open TopologicalSpace Topology
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.FiniteSuccession

open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

section ProperFrom

variable (S : FiniteSuccession M) {H : Set M} {s : ℕ} (hH : IsClosedSubmanifold ψ H s)
  (hc : S.CentersIn H)

include hH hc in
/-- The proper invariant from a start family (the restriction of sequences, [Kol07, 30.2]): along
a sequence with centres `Z_i ⊆ H_i`, starting from a simple normal crossing family `F` having
simple normal crossings with `H` properly, the strict transform `H_i` has simple normal crossings
with the boundary family `F_i` from the start `F`, properly, at every stage `i` at which clause
(3′) for the boundary `red F` holds at the stages `< i`. The base is the proper hypothesis on `F`
(a plain `HasSncWith` base would not start the induction: a component of `F` could contain `H`
near a point); the step is the transport of the proper invariant by the blowing-up along
`Z_i ⊆ H_i` (`hasSncWithProper_totalTransform`). -/
theorem hasSncWithProper_totalTransformSeqFrom_strictTransformSeq_of_forall_lt
    {F : HypersurfaceFamily M} (hF : F.IsSnc ψ) (hFH : F.HasSncWithProper ψ H s)
    (i : Fin (S.length + 1))
    (h3 : ∀ i' : Fin S.length, i'.1 < i.1 →
      (S.boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E)) i'.castSucc).HasOnlyNormalCrossingsWith
        (S.center i')) :
    (S.totalTransformSeqFrom F i).HasSncWithProper ψ (S.strictTransformSeq H i) s := by
  induction i using Fin.induction with
  | zero => exact hFH
  | succ i ih =>
    have h3c : ∀ i' : Fin S.length, i'.1 < i.castSucc.1 →
        (S.boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E)) i'.castSucc).HasOnlyNormalCrossingsWith
          (S.center i') :=
      fun i' hi' => h3 i' (by rw [Fin.val_castSucc] at hi'; rw [Fin.val_succ]; omega)
    have hZ : IsClosedSubmanifold ψ (S.center i).support (S.codim i) :=
      (S.isClosedSubmanifold_center i).congr_chart ψ
    have hπ : IsBlowUp ψ (S.center i).support (S.codim i) (S.map i) :=
      (S.isBlowUp_map i).congr_chart ψ
    exact HypersurfaceFamily.hasSncWithProper_totalTransform hZ hπ
      (isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt hF i.castSucc h3c).1
      (S.isClosedSubmanifold_strictTransformSeq H hH hc i.castSucc) (hc i)
      (hasSncWith_totalTransformSeqFrom_center_of_forall_lt hF i fun i' hi' =>
        h3 i' (by rw [Fin.val_succ]; exact hi'))
      (ih h3c)

end ProperFrom

section GoingUp

variable {S : Set M} {s : ℕ} (hS : IsClosedSubmanifold ψ S s)
  (T : FiniteSuccession hS.toAnalyticManifold) {J : IdealSheaf hS.toAnalyticManifold} {m : ℕ}

/-- The stage step with a boundary ([Kol07, 30.2–30.3]): if the push-forward `Π = j_* T` of a
sequence `T` of order `≥ m` with the boundary `E|_S = red (F|_S)` satisfies clause (3′) for the
boundary `E = red F` at every stage `< i`, it satisfies it at stage `i`. This is the step of
`GoingUp/Theorem84.lean` from the start `F`: clause (3′) of `T` at stage `i` becomes clause (3′)
of `Π|_S` through `e_i⁻¹` (`boundarySeq_pushforwardStageIso` with the start `E|_S`,
`center_pushforwardStageIso`), the boundary of `Π|_S` is the reduced ideal sheaf of the trace of
`F_i^X` on `S_i` (`boundarySeq_restrictSubmanifold_eq_idealSheaf_traceFamilyFrom`, with the proper
invariant from `F`), and the lifting `hasOnlyNormalCrossingsWith_idealSheaf_of_traceFamily` gives
clause (3′) of `Π`. -/
theorem pushforward_hasOnlyNormalCrossingsWith_center_from_of_forall_lt {F : HypersurfaceFamily M}
    (hF : F.IsSnc ψ) (hFS : F.HasSncWithProper ψ S s)
    (hge : T.IsOfOrderGe J m ((hS.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)))
    (i : Fin T.length)
    (h3 : ∀ i' : Fin T.length, i'.1 < i.1 →
      ((T.pushforward hS).boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E))
        i'.castSucc).HasOnlyNormalCrossingsWith ((T.pushforward hS).center i')) :
    ((T.pushforward hS).boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E))
      i.castSucc).HasOnlyNormalCrossingsWith ((T.pushforward hS).center i) := by
  have hcs : ∀ i' : Fin (T.pushforward hS).length, i'.1 < i.castSucc.1 →
      ((T.pushforward hS).boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E))
        i'.castSucc).HasOnlyNormalCrossingsWith ((T.pushforward hS).center i') :=
    fun i' hi' => h3 i' (by rw [Fin.val_castSucc] at hi'; exact hi')
  -- clause (3′) of `T` at stage `i`, transported to `Π|_S` along `e_i⁻¹`
  have hT : IdealSheaf.HasOnlyNormalCrossingsWith
      (T.boundarySeq ((hS.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)) i.castSucc)
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
        ((hS.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)) i.castSucc).pullback
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
        ((hS.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)) i.castSucc)
      (((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).center i) :=
    (congrArg₂ IdealSheaf.HasOnlyNormalCrossingsWith (key _) (key _)).mp h2
  -- the boundary of `Π|_S` is the reduced ideal sheaf of the trace of `F_i^X` (from the start `F`)
  obtain ⟨hsnc, hbd⟩ := isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt
    (S := T.pushforward hS) hF i.castSucc hcs
  have hprop : ∀ j : Fin ((T.pushforward hS).length + 1), j.1 ≤ i.castSucc.1 →
      ((T.pushforward hS).totalTransformSeqFrom F j).HasSncWithProper ψ
        ((T.pushforward hS).strictTransformSeq S j) s :=
    fun j hj =>
      (T.pushforward hS).hasSncWithProper_totalTransformSeqFrom_strictTransformSeq_of_forall_lt hS
        (T.centersIn_pushforward hS) hF hFS j fun i' hi' => hcs i' (by omega)
  have htr : ((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).boundarySeq
      ((hS.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)) i.castSucc =
      ((T.pushforward hS).traceFamilyFrom hS (T.centersIn_pushforward hS) F
        i.castSucc).idealSheaf :=
    (T.pushforward hS).boundarySeq_restrictSubmanifold_eq_idealSheaf_traceFamilyFrom hS
      (T.centersIn_pushforward hS) hF hFS i.castSucc hcs hprop
  have hR' : IdealSheaf.HasOnlyNormalCrossingsWith
      ((T.pushforward hS).traceFamilyFrom hS (T.centersIn_pushforward hS) F i.castSucc).idealSheaf
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
          (T.centersIn_pushforward hS) 0 _) _ hsnc
      (hprop _ le_rfl) ((T.pushforward hS).restrictCenterSub (ψ := ψ) 0 hk)
      (T.centersIn_pushforward hS ⟨0, hk⟩) hR'
  | succ k =>
    exact hasOnlyNormalCrossingsWith_idealSheaf_of_traceFamily
      ((T.pushforward hS).isClosedSubmanifold_strictTransformSeqAux _ hS
          (T.centersIn_pushforward hS) (k + 1) _) _ hsnc
      (hprop _ le_rfl) ((T.pushforward hS).restrictCenterSub (ψ := ψ) (k + 1) hk)
      (T.centersIn_pushforward hS ⟨k + 1, hk⟩) hR'

/-- **Clause (3′) of the push-forward with the boundary `E = red F`** ([Kol07, 30.2–30.3]), for
`T` of order `≥ m` with the boundary `E|_S`. Induction on a bound for the stage with the stage
step. -/
theorem pushforward_hasOnlyNormalCrossingsWith_center_from {F : HypersurfaceFamily M}
    (hF : F.IsSnc ψ) (hFS : F.HasSncWithProper ψ S s)
    (hge : T.IsOfOrderGe J m ((hS.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)))
    (i : Fin T.length) :
    ((T.pushforward hS).boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E))
      i.castSucc).HasOnlyNormalCrossingsWith ((T.pushforward hS).center i) := by
  suffices h : ∀ N : ℕ, ∀ i : Fin T.length, i.1 < N →
      ((T.pushforward hS).boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E))
        i.castSucc).HasOnlyNormalCrossingsWith ((T.pushforward hS).center i) from
    h (i.1 + 1) i (Nat.lt_succ_self _)
  intro N
  induction N with
  | zero => exact fun i hi => absurd hi (Nat.not_lt_zero _)
  | succ N ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact ih i hlt
    · exact T.pushforward_hasOnlyNormalCrossingsWith_center_from_of_forall_lt hS hF hFS hge i
        fun i' hi' => ih i' (by omega)

end GoingUp

section Corollary85

variable [FiniteDimensional 𝕜 E] {H : Set M} (hH : IsClosedSubmanifold ψ H 1)
  (T : FiniteSuccession hH.toAnalyticManifold) {I : IdealSheaf M} {m : ℕ}

/-- **Corollary 85** [Kol07, Corollary 85], going up (1) ⇒ (2), the `≥ m` form with the boundary:
for `I` D-balanced with `ord I ≤ m` everywhere and `E = red F` a simple normal crossing boundary
having simple normal crossings with the hypersurface `H` properly, the push-forward of a sequence
of order `≥ m` for `(I|_H, m)` with the boundary `E|_H` is of order `≥ m` for `(I, m)` with the
boundary `E`. Clause (4′) is Kollár's induction [Kol07, 90] (which does not look at the boundary),
clause (3′) is `pushforward_hasOnlyNormalCrossingsWith_center_from` ([Kol07, 30.2] and the
lifting of simple normal crossings). -/
theorem pushforward_isOfOrderGe_of_isOfOrderGe_traceFamily {F : HypersurfaceFamily M}
    (hI : I.IsDBalanced m) (hmax : ∀ y, I.ord y ≤ m) (hF : F.IsSnc ψ)
    (hFH : F.HasSncWithProper ψ H 1)
    (hT : T.IsOfOrderGe (I.pullback ⇑hH.inclusionMap hH.inclusionMap.contMDiff) m
      ((hH.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - 1) → 𝕜))) :
    (T.pushforward hH).IsOfOrderGe I m (F.idealSheaf (𝕜 := 𝕜) (E := E)) := by
  intro i
  exact ⟨T.pushforward_hasOnlyNormalCrossingsWith_center_from hH hF hFH hT i,
    le_ordAlong_pushforward hH T hI hmax hT i⟩

/-- **Corollary 85** [Kol07, Corollary 85], going up (1) ⇒ (2) as printed: the push-forward is of
order exactly `m` with the boundary `E` ([Kol07, Remark 67], `isOfOrder_of_isOfOrderGe_of_ord_le`).
The maximal-contact and component hypotheses of the printed statement are not needed for this
direction and are omitted. -/
theorem pushforward_isOfOrder_of_isOfOrderGe_traceFamily {F : HypersurfaceFamily M}
    (hI : I.IsDBalanced m) (hmax : ∀ y, I.ord y ≤ m) (hF : F.IsSnc ψ)
    (hFH : F.HasSncWithProper ψ H 1)
    (hT : T.IsOfOrderGe (I.pullback ⇑hH.inclusionMap hH.inclusionMap.contMDiff) m
      ((hH.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - 1) → 𝕜))) :
    (T.pushforward hH).IsOfOrder I (F.idealSheaf (𝕜 := 𝕜) (E := E)) m :=
  isOfOrder_of_isOfOrderGe_of_ord_le (T.pushforward hH)
    (T.pushforward_isOfOrderGe_of_isOfOrderGe_traceFamily hH hI hmax hF hFH hT) hmax

end Corollary85

section GoingDown

variable {H : Set M} {s : ℕ} (hH : IsClosedSubmanifold ψ H s) (B : FiniteSuccession M)
  {I : IdealSheaf M} {m : ℕ}

/-- Going down with a boundary ([Kol07, Corollary 85] (2) ⇒ (1), with the restriction of sequences
[Kol07, 30.2]): for a sequence `B` of order `≥ m` for `(I, m)` with the boundary `E = red F` whose
centres lie in the strict transforms of `H` (`F` a simple normal crossing family having simple
normal crossings with `H` properly), the restriction `B|_H` is of order `≥ m` for `(I|_H, m)` with
the boundary `E|_H`. Clause (4′) is `le_ordAlong_restrictSubmanifold`; clause (3′) is the form
from the start `F` of `boundarySeq_restrictSubmanifold_hasOnlyNormalCrossingsWith_center`: the
boundary of `B|_H` is the reduced ideal sheaf of the trace of `F_i` on `H_i`
(`boundarySeq_restrictSubmanifold_eq_idealSheaf_traceFamilyFrom`), and `Z_i ∩ H_i` has simple
normal crossings with that trace (`hasSncWith_traceFamily`, from clause (3′) of `B` and the proper
invariant from `F`). -/
theorem restrictSubmanifold_isOfOrderGe_traceFamily_of_isOfOrderGe {F : HypersurfaceFamily M}
    (hF : F.IsSnc ψ) (hFH : F.HasSncWithProper ψ H s)
    (hge : B.IsOfOrderGe I m (F.idealSheaf (𝕜 := 𝕜) (E := E))) (hc : B.CentersIn H) :
    (B.restrictSubmanifold hH hc).IsOfOrderGe
      (I.pullback ⇑hH.inclusionMap hH.inclusionMap.contMDiff) m
      ((hH.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - s) → 𝕜)) := by
  intro i
  refine ⟨?_, B.le_ordAlong_restrictSubmanifold hH hc hge i⟩
  have h3 : ∀ i' : Fin B.length, i'.1 < i.castSucc.1 →
      (B.boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E)) i'.castSucc).HasOnlyNormalCrossingsWith
        (B.center i') := fun i' _ => (hge i').1
  have hprop : ∀ j : Fin (B.length + 1), j.1 ≤ i.castSucc.1 →
      (B.totalTransformSeqFrom F j).HasSncWithProper ψ (B.strictTransformSeq H j) s :=
    fun j _ => B.hasSncWithProper_totalTransformSeqFrom_strictTransformSeq_of_forall_lt hH hc hF hFH
      j fun i' _ => (hge i').1
  have htr := B.boundarySeq_restrictSubmanifold_eq_idealSheaf_traceFamilyFrom hH hc hF hFH
    i.castSucc h3 hprop
  have hsnc : (B.totalTransformSeqFrom F i.castSucc).IsSnc ψ :=
    (isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt hF i.castSucc h3).1
  have hFZ : (B.totalTransformSeqFrom F i.castSucc).HasSncWith ψ (B.center i).support (B.codim i) :=
    hasSncWith_totalTransformSeqFrom_center_of_forall_lt hF i fun i' _ => (hge i').1
  rw [htr]
  obtain ⟨k, hk⟩ := i
  cases k with
  | zero =>
    exact (hasOnlyNormalCrossingsWith_idealSheaf_iff
      (B.isSnc_traceFamilyFrom hH hc F (Fin.castSucc ⟨0, hk⟩) hsnc (hprop _ le_rfl))
      (B.restrictCenterSub' hH hc 0 hk)).mpr
      ((B.isClosedSubmanifold_strictTransformSeqAux _ hH hc 0
          (Nat.lt_succ_of_lt hk)).hasSncWith_traceFamily hsnc
        (B.restrictCenterSub 0 hk) (hc ⟨0, hk⟩) hFZ (hprop _ le_rfl))
  | succ k =>
    exact (hasOnlyNormalCrossingsWith_idealSheaf_iff
      (B.isSnc_traceFamilyFrom hH hc F (Fin.castSucc ⟨k + 1, hk⟩) hsnc (hprop _ le_rfl))
      (B.restrictCenterSub' hH hc (k + 1) hk)).mpr
      ((B.isClosedSubmanifold_strictTransformSeqAux _ hH hc (k + 1)
          (Nat.lt_succ_of_lt hk)).hasSncWith_traceFamily hsnc
        (B.restrictCenterSub (k + 1) hk) (hc ⟨k + 1, hk⟩) hFZ (hprop _ le_rfl))

end GoingDown

section Corollary85Down

variable [FiniteDimensional 𝕜 E] {H : Set M} (hH : IsClosedSubmanifold ψ H 1) {I : IdealSheaf M}
  {m : ℕ}

/-- Going down in the static form of [Kol07, Theorem 80 (1)]
(`IsOfOrder.centersIn_of_idealSheaf_le_iteratedDeriv`): with `I_H ⊆ D^{m−1}(I)` in place of
maximal contact, the centres lie in the strict transforms of `H` and the restriction is of order
`≥ m` with the boundary `E|_H`. -/
theorem restrictSubmanifold_isOfOrderGe_of_isOfOrder_of_le_iteratedDeriv
    {F : HypersurfaceFamily M} (hm : 1 ≤ m) (hF : F.IsSnc ψ) (hFH : F.HasSncWithProper ψ H 1)
    (hle : hH.idealSheaf ≤ I.iteratedDeriv (m - 1)) (B : FiniteSuccession M)
    (hB : B.IsOfOrder I (F.idealSheaf (𝕜 := 𝕜) (E := E)) m) :
    ∃ hc : B.CentersIn H, (B.restrictSubmanifold hH hc).IsOfOrderGe
      (I.pullback ⇑hH.inclusionMap hH.inclusionMap.contMDiff) m
      ((hH.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - 1) → 𝕜)) :=
  ⟨hB.centersIn_of_idealSheaf_le_iteratedDeriv hm hH hle,
    B.restrictSubmanifold_isOfOrderGe_traceFamily_of_isOfOrderGe hH hF hFH hB.isOfOrderGe _⟩

end Corollary85Down

end AnalyticManifold.FiniteSuccession

end
