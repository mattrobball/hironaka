/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Main
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP2Entry
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Tools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedProtected
import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.FlatColon
import Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The isolation identity at the absorbing stage

The statement CP6 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) re-establishes the invariant `I = I_Γ
⊓ K` of the un-isolated ideal at the isolation step of the loop: at the first absorbing stage `n =
Nat.find h` of a round, the transform `K_n` of the ideal of the loop is `I_abs ⊓ (K_n : I_abs)`,
where `I_abs` is the reduced ideal of the union of the absorbed strict transforms and `K_n : I_abs`
the isolated ideal (`isolatedTriple T hm C n`, `Hironaka.Resolution.Algebraic.Wlo05.Embedded`). This
module proves that identity and its bookkeeping:

* `stageTriple_I` — the ideal of the stage triple is the mark-`1` transform along the truncated
  run (the mark is `1` by `hm`);
* the one-blow-up bridge `strictTransform_biInf_of_pairwise_disjoint` and the pairwise
  disjointness of the transported family `pairwise_disjoint_strictTransformSeq_support` (the ideal
  of a disjoint union along one blow-up);
* `vanishingIdeal_absorbed_eq_biInf` — `I_abs` is the intersection of the absorbed strict
  transforms (each integral by `isIntegral_take_strictTransformSeq_of_mem`);
  `isolatedTriple_I_eq_colon_biInf` — the isolated ideal is the colon by that intersection;
* **the isolation identity** `markedTransformSeq_take_eq_biInf_inf_colon` (and its form with the
  ideal of the isolated triple, `markedTransformSeq_take_eq_biInf_inf_isolatedTriple_I`):
  stalkwise, at a point of an absorbed `c̃` the transform is in chain form along `c̃` (CP1,
  `chainRelativeAt_of_absorbed`), so it is `c̃_p ⊓ (K_n : c̃)_p` by the intersection form
  (`stalkIdeal_eq_inf_colon_of_chainRelativeAt`), and `I_abs` has the stalk of `c̃` there (the
  absorbed transforms are pairwise disjoint, CP1); off the absorbed transforms `I_abs` is `𝒪` and
  the colon is `K_n` itself.

With the transport of the intersection form along the run
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Stage` under the protected states of CP5), the
isolation step of the loop becomes a rewrite: `(⨅ Γ̃) ⊓ K_n = (⨅ Γ̃) ⊓ (⨅ c̃) ⊓ (K_n : I_abs)`. This
is the isolation of the proof of [Wlo05, Theorem 4.7.1], proved from the chain form. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Loop`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Stage` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP5`.
-/

public section

universe u

open Ideal CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme IdealSheafData
  BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-- The ideal of the stage triple is the mark-1 transform of the loop's ideal along the truncated
run (the mark is `1` by `hm`). -/
theorem stageTriple_I (T : MarkedTriple k) (hm : T.m = 1) (n : ℕ) :
    (stageTriple T hm n).I = ((bmoOneRun T hm).take n).markedTransformSeq T.I 1 (Fin.last _) := by
  obtain ⟨T, m⟩ := T
  obtain rfl : m = 1 := hm
  rfl

section Bridge

variable {X : Scheme.{u}}

/-- The one-blow-up bridge: the strict transform of a disjoint union of reduced closed subschemes
along one blow-up is the intersection of the strict transforms
(`strictTransformSeq_biInf_of_pairwise_disjoint` on the one-step sequence). -/
theorem strictTransform_biInf_of_pairwise_disjoint [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (Γs : Finset X.IdealSheafData)
    (hred : ∀ γ ∈ Γs, IsReduced γ.subscheme)
    (hdisj : (↑Γs : Set X.IdealSheafData).Pairwise fun a b => Disjoint a.support b.support) :
    (⨅ γ ∈ Γs, γ).strictTransform D = ⨅ γ ∈ Γs, γ.strictTransform D :=
  strictTransformSeq_biInf_of_pairwise_disjoint (cons X D (nil _)) Γs hred hdisj (Fin.last 1)

open Classical in
/-- Pairwise disjointness of the supports of the strict transforms of a disjoint family. -/
theorem pairwise_disjoint_strictTransformSeq_support [IsLocallyNoetherian X]
    (S : BlowUpSequence X) (Γs : Finset X.IdealSheafData)
    (hdisj : (↑Γs : Set X.IdealSheafData).Pairwise fun a b => Disjoint a.support b.support)
    (i : Fin (S.length + 1)) :
    (↑(Γs.image fun γ => S.strictTransformSeq γ i) : Set (S.stage i).IdealSheafData).Pairwise
      fun a b => Disjoint a.support b.support := by
  rw [Finset.coe_image]
  exact Set.Pairwise.image fun a ha b hb hab =>
    disjoint_strictTransformSeq_support_of_disjoint S a b (hdisj ha hb hab) i

end Bridge

section Isolation

variable (T : MarkedTriple k) (hm : T.m = 1) (C : Finset T.X.left.IdealSheafData)
  (hinv : InvCE T.I T.E C) (h : ∃ n, HasAbsorptionAt T hm C n)

open Classical in
include hinv in
/-- The ideal of the absorbed strict transforms at the absorbing stage: the reduced ideal of their
union is their intersection (each is integral, `isIntegral_take_strictTransformSeq_of_mem`). -/
theorem vanishingIdeal_absorbed_eq_biInf :
    vanishingIdeal (⨆ c ∈ C.filter (fun c => CenterContains (bmoOneRun T hm) c (Nat.find h)),
        (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)).support) =
      ⨅ c ∈ C.filter (fun c => CenterContains (bmoOneRun T hm) c (Nat.find h)),
        ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _) := by
  have hred : ∀ γ ∈ (C.filter (fun c => CenterContains (bmoOneRun T hm) c (Nat.find h))).image
      (fun c => ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)),
      IsReduced γ.subscheme := by
    intro γ hγ
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hγ
    have := isIntegral_take_strictTransformSeq_of_mem T hm C hinv h (Finset.mem_filter.mp hc).1
    infer_instance
  have := biInf_eq_vanishingIdeal_biSup_support _ hred
  simp only [Finset.iInf_finset_image, Finset.iSup_finset_image] at this
  exact this.symm

open Classical in
include hinv in
/-- The isolated ideal is the colon of the transform of the ideal of the loop by the intersection
of the absorbed strict transforms (the definition of `isolatedTriple` with
`vanishingIdeal_absorbed_eq_biInf`). -/
theorem isolatedTriple_I_eq_colon_biInf :
    (isolatedTriple T hm C (Nat.find h)).I =
      (((bmoOneRun T hm).take (Nat.find h)).markedTransformSeq T.I 1 (Fin.last _)).colon
        (⨅ c ∈ C.filter (fun c => CenterContains (bmoOneRun T hm) c (Nat.find h)),
          ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)) := by
  rw [← vanishingIdeal_absorbed_eq_biInf T hm C hinv h, ← stageTriple_I]
  rfl

open Classical in
include hinv in
/-- **The isolation identity**, the colon form: at the first absorbing stage the transform `K` of
the ideal of the loop is `I_abs ⊓ (K : I_abs)` with `I_abs` the ideal of the absorbed strict
transforms. Stalkwise: at a point of an absorbed `c̃` the transform is in chain form along `c̃`
(CP1), so it is `c̃_p ⊓ (K : c̃)_p` (the intersection form), and `I_abs` has the stalk of `c̃`
there (CP1); off the absorbed transforms `I_abs` is `𝒪` and the colon is `K` itself. -/
theorem markedTransformSeq_take_eq_biInf_inf_colon :
    ((bmoOneRun T hm).take (Nat.find h)).markedTransformSeq T.I 1 (Fin.last _) =
      (⨅ c ∈ C.filter (fun c => CenterContains (bmoOneRun T hm) c (Nat.find h)),
        ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)) ⊓
        (((bmoOneRun T hm).take (Nat.find h)).markedTransformSeq T.I 1 (Fin.last _)).colon
          (⨅ c ∈ C.filter (fun c => CenterContains (bmoOneRun T hm) c (Nat.find h)),
            ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)) := by
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hLN' : IsLocallyNoetherian (((bmoOneRun T hm).take (Nat.find h)).stage (Fin.last _)) :=
    isLocallyNoetherian_stage ((bmoOneRun T hm).take (Nat.find h)) (Fin.last _)
  have hLN'' : IsLocallyNoetherian (stageTriple T hm (Nat.find h)).X.left := hLN'
  have hsm : Smooth ((stageTriple T hm (Nat.find h)).X.left ↘ Spec (CommRingCat.of k)) :=
    (stageTriple T hm (Nat.find h)).smooth
  have hdisj := pairwise_disjoint_take_strictTransformSeq_absorbed T hm C hinv h
  refine ext_stalkIdeal fun p => ?_
  rw [stalkIdeal_inf, stalkIdeal_colon_of_isLocallyNoetherian]
  by_cases hp : ∃ c ∈ C.filter (fun c => CenterContains (bmoOneRun T hm) c (Nat.find h)),
      p ∈ (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)).support
  · obtain ⟨c, hc, hpc⟩ := hp
    rw [stalkIdeal_biInf_eq_of_mem_of_pairwise_disjoint _ _ hdisj hc hpc]
    have hchain := chainRelativeAt_of_absorbed T hm C hinv h (Finset.mem_filter.mp hc).1
      (Finset.mem_filter.mp hc).2 p hpc
    have e := stalkIdeal_eq_inf_colon_of_chainRelativeAt
      ((stageTriple T hm (Nat.find h)).X.left ↘ Spec (CommRingCat.of k)) hchain
    rw [stageTriple_I] at e
    -- restate `e` on the run's stage (the stage triple's ambient is that stage by definition)
    have e' : (((bmoOneRun T hm).take (Nat.find h)).markedTransformSeq T.I 1
          (Fin.last _)).stalkIdeal p =
        (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)).stalkIdeal p ⊓
          ((((bmoOneRun T hm).take (Nat.find h)).markedTransformSeq T.I 1 (Fin.last _)).colon
            (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c
              (Fin.last _))).stalkIdeal p := e
    rw [stalkIdeal_colon_of_isLocallyNoetherian] at e'
    exact e'
  · rw [stalkIdeal_biInf_eq_top_of_forall_notMem _ _ fun c hc hpc => hp ⟨c, hc, hpc⟩,
      Submodule.top_coe, Submodule.colon_univ, top_inf_eq]

open Classical in
include hinv in
/-- The isolation identity with the ideal of the isolated triple:
`K_n = I_abs ⊓ (isolatedTriple).I`. -/
theorem markedTransformSeq_take_eq_biInf_inf_isolatedTriple_I :
    ((bmoOneRun T hm).take (Nat.find h)).markedTransformSeq T.I 1 (Fin.last _) =
      (⨅ c ∈ C.filter (fun c => CenterContains (bmoOneRun T hm) c (Nat.find h)),
        ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)) ⊓
        (isolatedTriple T hm C (Nat.find h)).I := by
  rw [isolatedTriple_I_eq_colon_biInf T hm C hinv h]
  exact markedTransformSeq_take_eq_biInf_inf_colon T hm C hinv h

end Isolation

end Hironaka.Resolution
