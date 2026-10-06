/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineEndResult
import Hironaka.Resolution.Algebraic.Kol07.Thm36.SncPreimageSingular
import Hironaka.Resolution.Algebraic.Wlo05.ComponentsColon
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedBridge
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Absorbed
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Main
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Remaining
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP2Entry
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP5
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Isolation
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6LoopTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Stage
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Tools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral
import Hironaka.Scheme.BlowUpSequence.TakeLast
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The loop of the un-isolated ideal

The statement CP6 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) follows the un-isolated ideal `I₀ =
I_A ⊓ K` — the controlled transform of `I_Y` along the WHOLE loop `bedAux` of
`Hironaka.Resolution.Algebraic.Wlo05.Embedded`, isolations ignored — and proves the end identity: at
the end of the loop the transform of `I_Y` is the product of the final strict transforms of the
members, which are pairwise disjoint (the `marked_eq` and `pairwise` clauses of the end data of
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedState`, hence the fine form of clause (e) of [Wlo05,
Theorem 1.0.2]). This module proves that argument on `bedAux`, `bmoOneRun`, `stageTriple`,
`isolatedTriple` and `remainingComponents`:

* the FULL-RUN form of the intersection form along a round,
  `bmoOneRun_marked_eq_inf_of_protectedStates` — the per-stage engine
  `markedTransformSeq_eq_biInf_inf_of_forall_stage`
  (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Stage`) on the run of `BMO_1`, its hypotheses
  supplied by the protected states of CP5 (`protectedState_stageTriple` through the casts of the
  truncation, `admissibleChainStratumKAt_center_of_protectedState`), the order property of the run
  (smooth stages, snc boundary) and `K_i ≤ Z_i` (`markedTransformSeq_le_center_of_isOrderGeSeq`);
  its truncated form is `markedTransformSeq_take_eq_inf_of_protectedStates`;
* the isolation step `isolatedTriple_marked_eq_inf_of_absorbed` — the truncated form at the
  absorbing stage with the isolation identity `markedTransformSeq_take_eq_biInf_inf_colon`
  (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Isolation`): the invariant is re-established with
  the enlarged protected set and the isolated ideal;
* `protectedState_transported_of_absorbed` — the enlarged protected set is protected for the
  isolated state (CP5's `protectedState_isolatedTriple` for the transports, the entry of CP2 for
  the absorbed members);
* **the loop theorem** `bedAux_marked_eq_biInf_of_protectedStates` and **the loop separates**
  `bedAux_pairwise_disjoint_of_protectedStates` — strong induction on the number of members along
  `bedAux_of_exists` and `bedAux_of_not_exists`: at an absorbing stage the goal transports across
  the concatenation, the isolation step and the transported protected set feed the induction
  hypothesis at the isolated triple (with `invCE_isolatedTriple`,
  `card_remainingComponents_lt`), the index sets match membership-wise; with no absorption the
  members are empty by exhaustiveness and the full-run form at the end with
  `markedTransformSeq_bmoOneRun_last_eq_top` closes;
* **the end identity** `markedTransformSeq_bedAux_last_eq_prod`: both clauses at `Γs = ∅`, the
  product from the meet by `prod_eq_inf_of_pairwise_disjoint`, stated for every state satisfying
  `InvCE`.

This is the identity `σ^*(I_Y) = M(σ^*(I_Y)) · I_Ỹ` of [Wlo05, Theorem 4.7.1] up to the monomial
factor, proved from the chain forms; the argument is not in the literature. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCPBridge` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Remaining`.
-/

public section

universe u

open Ideal CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-- **The full-run form of the intersection form along a round**: from a state with pairwise
disjoint protected components `Γs`, the transform of `I₀ = (⨅ γ ∈ Γs, γ) ⊓ T.I` at every stage of
the run is the meet of the transported protected components with the transform of `T.I` —
`markedTransformSeq_eq_biInf_inf_of_forall_stage` on `bmoOneRun T hm`, its per-stage hypotheses
supplied by the protected states of CP5 (`protectedState_stageTriple` through the casts of the
truncation, and `admissibleChainStratumKAt_center_of_protectedState`), the order property of the
run (snc boundary, smooth stages, `K_i ≤ Z_i` by `markedTransformSeq_le_center_of_isOrderGeSeq`)
and the integrality of the members (reducedness). -/
theorem bmoOneRun_marked_eq_inf_of_protectedStates (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) (Γs : Finset T.X.left.IdealSheafData)
    (I₀ : T.X.left.IdealSheafData)
    (hP : ∀ γ ∈ Γs, ProtectedState T C γ)
    (hdisj : (↑Γs : Set T.X.left.IdealSheafData).Pairwise fun a b => Disjoint a.support b.support)
    (hI₀ : I₀ = (⨅ γ ∈ Γs, γ) ⊓ T.I) (i : Fin ((bmoOneRun T hm).length + 1)) :
    (bmoOneRun T hm).markedTransformSeq I₀ 1 i =
      (⨅ γ ∈ Γs, (bmoOneRun T hm).strictTransformSeq γ i) ⊓
        (bmoOneRun T hm).markedTransformSeq T.I 1 i := by
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hPF : PerfectField k := PerfectField.ofCharZero
  obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
  have hsmd : SmoothOfRelativeDimension d (T.X.left ↘ Spec (.of k)) := hd
  have hsmT : Smooth (T.X.left ↘ Spec (.of k)) := T.smooth
  have hrun : (bmoOneRun T hm).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I 1 T.E := by
    have h0 := isOrderGeSeq_bmoOneRun T hm
    rwa [hm] at h0
  refine markedTransformSeq_eq_biInf_inf_of_forall_stage (T.X.left ↘ Spec (.of k))
    (bmoOneRun T hm) T.E
    T.I I₀ Γs (fun γ hγ => ?_) hdisj hI₀ (fun j => ?_) (fun j => ?_) (fun j γ hγ => ?_)
    (fun j γ hγ => ?_) (fun j γ hγ => ?_) (fun j γ hγ => ?_) (fun j => ?_) i
  · -- reducedness of the protected components
    have := (hP γ hγ).integral
    infer_instance
  · -- smooth stages
    exact IsSmooth.smooth_stageMap (n := d) hrun.1 j.castSucc
  · -- snc boundary at every stage
    exact IsOrderGeSeq.isSnc_totalTransformSeq (T.X.left ↘ Spec (.of k)) d hrun T.isSnc
      j.castSucc
  · -- the transported component has snc with the boundary (CP5 through the take-last bridge)
    have hs := (protectedState_stageTriple T hm C γ (hP γ hγ) j.val j.is_lt.le).snc
    exact hasSncWith_of_heq (stage_take_last (bmoOneRun T hm) j.is_lt.le)
      (totalTransformSeq_take_last_heq (bmoOneRun T hm) T.E j.is_lt.le)
      (strictTransformSeq_take_last_heq (bmoOneRun T hm) γ j.is_lt.le) hs
  · -- the transported component is smooth over `k`
    have hs := (protectedState_stageTriple T hm C γ (hP γ hγ) j.val j.is_lt.le).smooth
    exact smooth_subschemeι_comp_of_heq
      (stage_take_last (bmoOneRun T hm) j.is_lt.le).symm
      (strictTransformSeq_take_last_heq (bmoOneRun T hm) γ j.is_lt.le).symm
      (composite_take_heq (bmoOneRun T hm) j.is_lt.le).symm (T.X.left ↘ Spec (.of k))
      hs
  · -- the K-shape of the transform along the transported component
    have hs := (protectedState_stageTriple T hm C γ (hP γ hγ) j.val j.is_lt.le).chain
    rw [stageTriple_I] at hs
    exact forall_chainRelativeKAt_of_heq
      (stage_take_last (bmoOneRun T hm) j.is_lt.le)
      (totalTransformSeq_take_last_heq (bmoOneRun T hm) T.E j.is_lt.le)
      (markedTransformSeq_take_last_heq (bmoOneRun T hm) T.I 1 j.is_lt.le)
      (strictTransformSeq_take_last_heq (bmoOneRun T hm) γ j.is_lt.le) hs
  · -- admissibility at the centre (CP5)
    exact admissibleChainStratumKAt_center_of_protectedState T hm C γ (hP γ hγ) j
  · -- `K_j ≤ Z_j` (the order condition of the run)
    exact markedTransformSeq_le_center_of_isOrderGeSeq (T.X.left ↘ Spec (.of k))
      (bmoOneRun T hm) T.I T.E hrun j

open Classical in
/-- **The intersection form along a round, truncated anywhere**: from the start of a round with
the protected members `Γs` (each a protected state, pairwise disjoint supports) and the
un-isolated ideal `I₀ = (⨅ γ ∈ Γs, γ) ⊓ T.I`, the identity persists along the run truncated
anywhere — `markedTransform_inf_of_admissible` iterated with CP3 for the centres. Off the `Γ̃` it
reads `I_n = K_n`; at their points it is the local un-isolated form. -/
theorem markedTransformSeq_take_eq_inf_of_protectedStates (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) (Γs : Finset T.X.left.IdealSheafData)
    (I₀ : T.X.left.IdealSheafData)
    (hP : ∀ γ ∈ Γs, ProtectedState T C γ)
    (hdisj : (↑Γs : Set T.X.left.IdealSheafData).Pairwise fun a b => Disjoint a.support b.support)
    (hI₀ : I₀ = (⨅ γ ∈ Γs, γ) ⊓ T.I) (n : ℕ) (hn : n ≤ (bmoOneRun T hm).length) :
    ((bmoOneRun T hm).take n).markedTransformSeq I₀ 1 (Fin.last _) =
      (⨅ γ ∈ Γs, ((bmoOneRun T hm).take n).strictTransformSeq γ (Fin.last _)) ⊓
        ((bmoOneRun T hm).take n).markedTransformSeq T.I 1 (Fin.last _) := by
  have hlt := Nat.lt_succ_of_le hn
  refine eq_of_heq_of_heq (stage_take_last (bmoOneRun T hm) hn)
    (markedTransformSeq_take_last_heq (bmoOneRun T hm) I₀ 1 hn)
    (heq_inf (stage_take_last (bmoOneRun T hm) hn)
      (heq_biInf (stage_take_last (bmoOneRun T hm) hn) Γs fun γ =>
        strictTransformSeq_take_last_heq (bmoOneRun T hm) γ hn)
      (markedTransformSeq_take_last_heq (bmoOneRun T hm) T.I 1 hn))
    (bmoOneRun_marked_eq_inf_of_protectedStates T hm C Γs I₀ hP hdisj hI₀ ⟨n, hlt⟩)

section Loop

variable (T : MarkedTriple k) (hm : T.m = 1) (C : Finset T.X.left.IdealSheafData)
  (hinv : InvCE T.I T.E C) (h : ∃ n, HasAbsorptionAt T hm C n)

open Classical in
include hinv in
/-- At the absorbing stage, the transports of the protected components and the strict transforms
of the newly absorbed members are protected for the isolated state (the persistence of CP5 for the
former, the entry of CP2 for the latter). -/
theorem protectedState_transported_of_absorbed (Γs : Finset T.X.left.IdealSheafData)
    (hP : ∀ γ ∈ Γs, ProtectedState T C γ) :
    ∀ γ' ∈ Γs.image
          (fun γ => ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq γ (Fin.last _)) ∪
        (C.filter fun c => CenterContains (bmoOneRun T hm) c (Nat.find h)).image
          (fun c => ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)),
      ProtectedState (isolatedTriple T hm C (Nat.find h))
        (remainingComponents T hm C (Nat.find h)) γ' := by
  intro γ' hγ'
  rcases Finset.mem_union.mp hγ' with hγ' | hγ'
  · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hγ'
    exact protectedState_isolatedTriple T hm C γ (hP γ hγ) h
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hγ'
    exact protectedState_isolatedTriple_of_absorbed T hm C hinv h (Finset.mem_filter.mp hc).1
      (Finset.mem_filter.mp hc).2

end Loop

open Classical in
/-- **The isolation step**: at the first absorbing stage `Nat.find h` of a round whose start
satisfies the invariant with the protected set `Γs`, the invariant is re-established with the
enlarged protected set (the transports of `Γs` and the strict transforms of the newly absorbed
members) and the isolated ideal `K⁺ = K⁻ : I_abs` — CP1 and CP2 for the absorbed members (they
miss each other and the `Γ̃`), and the isolation is the identity near the `Γ̃`
(`stalkIdeal_isolatedTriple_I_eq_of_protectedState`). -/
theorem isolatedTriple_marked_eq_inf_of_absorbed (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) (hinv : InvCE T.I T.E C)
    (Γs : Finset T.X.left.IdealSheafData)
    (I₀ : T.X.left.IdealSheafData) (hP : ∀ γ ∈ Γs, ProtectedState T C γ)
    (hdisj : (↑Γs : Set T.X.left.IdealSheafData).Pairwise fun a b => Disjoint a.support b.support)
    (hI₀ : I₀ = (⨅ γ ∈ Γs, γ) ⊓ T.I) (h : ∃ n, HasAbsorptionAt T hm C n) :
    ((bmoOneRun T hm).take (Nat.find h)).markedTransformSeq I₀ 1 (Fin.last _) =
      (⨅ γ ∈ Γs.image (fun γ => ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq γ
            (Fin.last _)) ∪
          (C.filter fun c => CenterContains (bmoOneRun T hm) c (Nat.find h)).image
            (fun c => ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)), γ) ⊓
        (isolatedTriple T hm C (Nat.find h)).I := by
  rw [markedTransformSeq_take_eq_inf_of_protectedStates T hm C Γs I₀ hP hdisj hI₀ (Nat.find h)
    (find_lt_length T hm C h).le, isolatedTriple_I_eq_colon_biInf T hm C hinv h, Finset.iInf_union,
    Finset.iInf_finset_image, Finset.iInf_finset_image, inf_assoc,
    ← markedTransformSeq_take_eq_biInf_inf_colon T hm C hinv h]

open Classical in
/-- **The loop separates**: from a state satisfying the invariant with pairwise disjoint protected
components, the final strict transforms of the protected components and of the members are
pairwise disjoint. Strong induction on the number of members along `bedAux`: at an absorbing stage
the transported protected set is pairwise disjoint and protected for the isolated state, two
distinct members not yet absorbed keep distinct strict transforms, and the induction hypothesis
separates everything at the end. -/
theorem bedAux_pairwise_disjoint_of_protectedStates (N : ℕ) : ∀ (T : MarkedTriple k) (hm : T.m = 1)
    (C Γs : Finset T.X.left.IdealSheafData), C.card = N → InvCE T.I T.E C →
    (∀ γ ∈ Γs, ProtectedState T C γ) →
    (↑Γs : Set T.X.left.IdealSheafData).Pairwise (fun a b => Disjoint a.support b.support) →
    (↑(Γs ∪ C) : Set T.X.left.IdealSheafData).Pairwise fun a b =>
      Disjoint ((bedAux T hm C).strictTransformSeq a (Fin.last _)).support
        ((bedAux T hm C).strictTransformSeq b (Fin.last _)).support := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro T hm C Γs hcard hinv hP hdisj
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  by_cases h : ∃ n, HasAbsorptionAt T hm C n
  · rw [bedAux_of_exists T hm C h]
    have hLN' : IsLocallyNoetherian (((bmoOneRun T hm).take (Nat.find h)).stage (Fin.last _)) :=
      isLocallyNoetherian_stage ((bmoOneRun T hm).take (Nat.find h)) (Fin.last _)
    have hcard' : ((C.filter fun c => ¬ CenterContains (bmoOneRun T hm) c (Nat.find h)).image
        (fun c => ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _))).card <
          N :=
      hcard ▸ card_remainingComponents_lt T hm C h
    have hIH := ih _ hcard' (isolatedTriple T hm C (Nat.find h)) hm
      ((C.filter fun c => ¬ CenterContains (bmoOneRun T hm) c (Nat.find h)).image
        (fun c => ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _))) _ rfl
      (invCE_isolatedTriple T hm C hinv h)
      (protectedState_transported_of_absorbed T hm C hinv h Γs hP)
      (pairwise_disjoint_transported_of_absorbed T hm C hinv h Γs hP hdisj)
    intro a ha b hb hab
    refine disjoint_of_heq (last_concat _ _)
      (heq_support (last_concat _ _) (strictTransformSeq_concat_last_heq _ _ a))
      (heq_support (last_concat _ _) (strictTransformSeq_concat_last_heq _ _ b)) ?_
    by_cases hg : ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq a (Fin.last _) =
        ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq b (Fin.last _)
    · -- the transported supports are disjoint at the absorbing stage
      have hd : Disjoint
          (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq a (Fin.last _)).support
          (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq b (Fin.last _)).support := by
        rcases Finset.mem_union.mp (Finset.mem_coe.mp ha) with ha' | ha' <;>
          rcases Finset.mem_union.mp (Finset.mem_coe.mp hb) with hb' | hb'
        · exact disjoint_strictTransformSeq_support_of_disjoint _ a b (hdisj ha' hb' hab) _
        · exact disjoint_strictTransformSeq_support_of_disjoint _ a b
            ((hP a ha').disjoint b hb').symm _
        · exact disjoint_strictTransformSeq_support_of_disjoint _ a b ((hP b hb').disjoint a ha') _
        · by_cases hca : CenterContains (bmoOneRun T hm) a (Nat.find h)
          · exact (disjoint_strictTransformSeq_of_absorbed T hm C hinv h ha' hca hb'
              (Ne.symm hab)).symm
          · by_cases hcb : CenterContains (bmoOneRun T hm) b (Nat.find h)
            · exact disjoint_strictTransformSeq_of_absorbed T hm C hinv h hb' hcb ha' hab
            · exact absurd (eq_of_take_strictTransformSeq_eq T hm C hinv h ha' hb' hg) hab
      exact disjoint_strictTransformSeq_support_of_disjoint _ _ _ hd _
    · exact hIH (Finset.mem_coe.mpr (mem_transported_of_absorbed T hm C h Γs a
        (Finset.mem_coe.mp ha))) (Finset.mem_coe.mpr (mem_transported_of_absorbed T hm C h Γs
        b (Finset.mem_coe.mp hb))) hg
  · rw [bedAux_of_not_exists T hm C h]
    have hC : C = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro c hc
      obtain ⟨η, -, rfl, -, -⟩ := hinv.mem c hc
      have := isIntegral_subscheme_vanishingIdeal_closure (X := T.X.left) η
      obtain ⟨n, hn⟩ := exists_centerContains_bmoOneRun_of_invCE T hm hinv hc
      exact h ⟨n, _, hc, hn⟩
    subst hC
    intro a ha b hb hab
    rw [Finset.union_empty] at ha hb
    exact disjoint_strictTransformSeq_support_of_disjoint _ a b (hdisj ha hb hab) _

open Classical in
/-- **The intersection form along the whole loop** (CP6, the sheaf form): from a state whose
members satisfy `InvCE`, protected components `Γs` (pairwise disjoint protected states) and the
un-isolated ideal `I₀ = (⨅ γ ∈ Γs, γ) ⊓ T.I`, the controlled transform of `I₀` along the loop is
the ideal of the disjoint union of the final strict transforms of the protected components AND of
the members — every member is absorbed by the end (exhaustiveness), and the isolated ideal of the
last round is `⊤` ([Kol07, Theorem 69 (1)]). Strong induction on `C.card` through
`bedAux_of_exists` and `bedAux_of_not_exists`: the intersection form along the round, the
isolation step, the protected states of CP5 for the enlarged set. -/
theorem bedAux_marked_eq_biInf_of_protectedStates (N : ℕ) : ∀ (T : MarkedTriple k) (hm : T.m = 1)
    (C Γs : Finset T.X.left.IdealSheafData) (I₀ : T.X.left.IdealSheafData), C.card = N →
    InvCE T.I T.E C → (∀ γ ∈ Γs, ProtectedState T C γ) →
    (↑Γs : Set T.X.left.IdealSheafData).Pairwise (fun a b => Disjoint a.support b.support) →
    I₀ = (⨅ γ ∈ Γs, γ) ⊓ T.I →
    (bedAux T hm C).markedTransformSeq I₀ 1 (Fin.last _) =
      ⨅ γ ∈ Γs ∪ C, (bedAux T hm C).strictTransformSeq γ (Fin.last _) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro T hm C Γs I₀ hcard hinv hP hdisj hI₀
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  by_cases h : ∃ n, HasAbsorptionAt T hm C n
  · rw [bedAux_of_exists T hm C h]
    have hcard' : ((C.filter fun c => ¬ CenterContains (bmoOneRun T hm) c (Nat.find h)).image
        (fun c => ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _))).card <
          N :=
      hcard ▸ card_remainingComponents_lt T hm C h
    have hIH := ih _ hcard' (isolatedTriple T hm C (Nat.find h)) hm
      ((C.filter fun c => ¬ CenterContains (bmoOneRun T hm) c (Nat.find h)).image
        (fun c => ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _))) _ _ rfl
      (invCE_isolatedTriple T hm C hinv h)
      (protectedState_transported_of_absorbed T hm C hinv h Γs hP)
      (pairwise_disjoint_transported_of_absorbed T hm C hinv h Γs hP hdisj) rfl
    refine eq_of_heq_of_heq (last_concat _ _) (markedTransformSeq_concat_last_heq _ _ I₀ 1)
      (heq_biInf (last_concat _ _) (Γs ∪ C) fun γ => strictTransformSeq_concat_last_heq _ _ γ) ?_
    rw [isolatedTriple_marked_eq_inf_of_absorbed T hm C hinv Γs I₀ hP hdisj hI₀ h]
    refine hIH.trans (le_antisymm (le_iInf₂ fun a ha => ?_) (le_iInf₂ fun γ' hγ' => ?_))
    · exact iInf₂_le _ (mem_transported_of_absorbed T hm C h Γs a ha)
    · obtain ⟨z, hz, rfl⟩ : ∃ z ∈ Γs ∪ C,
          ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq z (Fin.last _) = γ' := by
        rcases Finset.mem_union.mp hγ' with hγ' | hγ'
        · rcases Finset.mem_union.mp hγ' with hγ' | hγ'
          · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hγ'
            exact ⟨γ, Finset.mem_union_left _ hγ, rfl⟩
          · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hγ'
            exact ⟨c, Finset.mem_union_right _ (Finset.mem_filter.mp hc).1, rfl⟩
        · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hγ'
          exact ⟨c, Finset.mem_union_right _ (Finset.mem_filter.mp hc).1, rfl⟩
      exact iInf₂_le z hz
  · rw [bedAux_of_not_exists T hm C h]
    have hC : C = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro c hc
      obtain ⟨η, -, rfl, -, -⟩ := hinv.mem c hc
      have := isIntegral_subscheme_vanishingIdeal_closure (X := T.X.left) η
      obtain ⟨n, hn⟩ := exists_centerContains_bmoOneRun_of_invCE T hm hinv hc
      exact h ⟨n, _, hc, hn⟩
    subst hC
    rw [Finset.union_empty, bmoOneRun_marked_eq_inf_of_protectedStates T hm ∅ Γs I₀ hP hdisj hI₀
      (Fin.last _), markedTransformSeq_bmoOneRun_last_eq_top, inf_top_eq]

open Classical in
/-- **The end identity** (the `marked_eq` and `pairwise` clauses of the end data): along the whole
loop from a state satisfying `InvCE`, the final strict transforms of the members are pairwise
disjoint and the marked transform of the ideal is their PRODUCT — from the intersection form along
the loop at `Γs = ∅`, `K_end = ⊤` at the end (CP5), and `⨅ = ∏` for pairwise disjoint strict
transforms. The pair that the clauses consume (`strictTransformSeq_eq_prod_of_pairwise_disjoint`,
`hasSncWith_prod_of_pairwise_disjoint`; [Kol07, 72] for clause (e)). -/
theorem markedTransformSeq_bedAux_last_eq_prod (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) (hinv : InvCE T.I T.E C) :
    (↑C : Set T.X.left.IdealSheafData).Pairwise (fun a b =>
        Disjoint ((bedAux T hm C).strictTransformSeq a (Fin.last _)).support
          ((bedAux T hm C).strictTransformSeq b (Fin.last _)).support) ∧
      (bedAux T hm C).markedTransformSeq T.I 1 (Fin.last _) =
        ∏ c ∈ C, (bedAux T hm C).strictTransformSeq c (Fin.last _) := by
  have hL := bedAux_marked_eq_biInf_of_protectedStates C.card T hm C ∅ T.I rfl hinv (by simp)
    (by simp) (by simp)
  have hPw := bedAux_pairwise_disjoint_of_protectedStates C.card T hm C ∅ rfl hinv (by simp)
    (by simp)
  rw [Finset.empty_union] at hL hPw
  refine ⟨hPw, ?_⟩
  rw [hL, Scheme.IdealSheafData.prod_eq_inf_of_pairwise_disjoint _ C hPw, Finset.inf_eq_iInf]

end Hironaka.Resolution
