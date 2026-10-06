/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedBridge
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP2Entry
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Isolation
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedProtected
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRemaining
import Hironaka.Scheme.BlowUpSequence.TakeLast
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Tools for the loop of the un-isolated ideal

The loop theorem of the statement CP6 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`;
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Loop`) is a strong induction on the number of
members along `bedAux`: at an absorbing stage the goal transports across the concatenation, the
isolation identity re-establishes the invariant with the ENLARGED protected set — the transports of
the protected components and the strict transforms of the newly absorbed members — and the induction
hypothesis applies to the isolated triple. This module holds the bookkeeping of that step:

* `heq_inf`, `heq_biInf` — a meet, or a finite meet, of ideal sheaves transports across a cast of
  the ambient scheme (the casts of the concatenation and of the truncation);
* `forall_chainRelativeKAt_of_heq` — the K-shape along a closed subscheme transports across a cast
  (the bridge from the last stage of the truncation, where CP5 states the protected state, to the
  stage of the run);
* `eq_of_take_strictTransformSeq_eq` — two members with the same strict transform at the absorbing
  stage coincide (`eq_of_strictTransformSeq_eq` of
  `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRemaining` through the identification of the last
  stage of the truncation): the injectivity that the separation of the members not yet absorbed
  needs;
* `pairwise_disjoint_transported_of_absorbed` — the transported protected set at the absorbing
  stage is pairwise disjoint (transport of the disjointness of the protected components, CP1 for
  the absorbed members, the disjointness of the protected state from the members across the two
  families);
* `mem_transported_of_absorbed` — every protected component and every member has its strict
  transform in the transported protected set or among the remaining members.

Used in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Loop` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP5`.
-/

public section

universe u

open Ideal CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka BlowUpSequence
  Scheme.IdealSheafData

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

section Cast

variable {Y Y' : Scheme.{u}}

/-- A meet of two ideal sheaves transports across a cast of the ambient scheme. -/
theorem heq_inf (h : Y = Y') {a b : Y.IdealSheafData}
    {a' b' : Y'.IdealSheafData} (ha : HEq a a') (hb : HEq b b') : HEq (a ⊓ b) (a' ⊓ b') := by
  subst h
  rw [eq_of_heq ha, eq_of_heq hb]

/-- A finite meet of ideal sheaves transports across a cast of the ambient scheme. -/
theorem heq_biInf (h : Y = Y') {ι : Type*} (A : Finset ι)
    {f : ι → Y.IdealSheafData} {g : ι → Y'.IdealSheafData} (hfg : ∀ a, HEq (f a) (g a)) :
    HEq (⨅ a ∈ A, f a) (⨅ a ∈ A, g a) := by
  subst h
  exact heq_of_eq (iInf_congr fun a => iInf_congr fun _ => eq_of_heq (hfg a))

/-- The K-shape along a closed subscheme transports across a cast of the ambient scheme. -/
theorem forall_chainRelativeKAt_of_heq (h : Y = Y') {E : DivisorFamily Y} {E' : DivisorFamily Y'}
    (hE : HEq E E') {K Γ : Y.IdealSheafData} {K' Γ' : Y'.IdealSheafData} (hK : HEq K K')
    (hΓ : HEq Γ Γ') (hs : ∀ p ∈ Γ.support, ChainRelativeKAt E K Γ p) :
    ∀ p ∈ Γ'.support, ChainRelativeKAt E' K' Γ' p := by
  subst h
  rw [eq_of_heq hE, eq_of_heq hK, eq_of_heq hΓ] at hs
  exact hs

end Cast

section Loop

variable (T : MarkedTriple k) (hm : T.m = 1) (C : Finset T.X.left.IdealSheafData)
  (hinv : InvCE T.I T.E C) (h : ∃ n, HasAbsorptionAt T hm C n)

open Classical in
include hinv in
/-- Two members with the same strict transform at the absorbing stage coincide
(`eq_of_strictTransformSeq_eq` in the truncated form). -/
theorem eq_of_take_strictTransformSeq_eq {c₁ c₂ : T.X.left.IdealSheafData} (hc₁ : c₁ ∈ C)
    (hc₂ : c₂ ∈ C) (heq : ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c₁ (Fin.last _) =
      ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c₂ (Fin.last _)) :
    c₁ = c₂ :=
  eq_of_strictTransformSeq_eq hinv hc₁ hc₂
    (eq_of_heq_of_heq
      (stage_take_last (bmoOneRun T hm) (find_lt_length T hm C h).le).symm
      (strictTransformSeq_take_last_heq (bmoOneRun T hm) c₁
        (find_lt_length T hm C h).le).symm
      (strictTransformSeq_take_last_heq (bmoOneRun T hm) c₂
        (find_lt_length T hm C h).le).symm heq)

open Classical in
include hinv in
/-- The transported protected set at the absorbing stage is pairwise disjoint (transport of the
disjointness of the protected components, CP1 for the absorbed members, and the disjointness of
the protected state from the members across the two). -/
theorem pairwise_disjoint_transported_of_absorbed (Γs : Finset T.X.left.IdealSheafData)
    (hP : ∀ γ ∈ Γs, ProtectedState T C γ)
    (hdisj : (↑Γs : Set T.X.left.IdealSheafData).Pairwise fun a b => Disjoint a.support b.support) :
    (↑(Γs.image (fun γ => ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq γ (Fin.last _)) ∪
        (C.filter fun c => CenterContains (bmoOneRun T hm) c (Nat.find h)).image
          (fun c => ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _))) :
      Set (((bmoOneRun T hm).take (Nat.find h)).stage (Fin.last _)).IdealSheafData).Pairwise
      fun a b => Disjoint a.support b.support := by
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  rw [Finset.coe_union, Set.pairwise_union]
  refine ⟨pairwise_disjoint_strictTransformSeq_support _ Γs hdisj (Fin.last _), ?_, ?_⟩
  · rw [Finset.coe_image]
    exact Set.Pairwise.image (pairwise_disjoint_take_strictTransformSeq_absorbed T hm C hinv h)
  · intro a ha b hb _
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
    have hd := disjoint_strictTransformSeq_support_of_disjoint ((bmoOneRun T hm).take (Nat.find h))
      γ c ((hP γ hγ).disjoint c (Finset.mem_filter.mp hc).1).symm (Fin.last _)
    exact ⟨hd, hd.symm⟩

open Classical in
/-- Every protected component and every member has its strict transform at the absorbing stage in
the transported protected set or among the remaining members. -/
theorem mem_transported_of_absorbed (Γs : Finset T.X.left.IdealSheafData) :
    ∀ z ∈ Γs ∪ C, ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq z (Fin.last _) ∈
      Γs.image (fun γ => ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq γ (Fin.last _)) ∪
          (C.filter fun c => CenterContains (bmoOneRun T hm) c (Nat.find h)).image
            (fun c => ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)) ∪
        (C.filter fun c => ¬ CenterContains (bmoOneRun T hm) c (Nat.find h)).image
            (fun c => ((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)) := by
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hz))
  · by_cases habs : CenterContains (bmoOneRun T hm) z (Nat.find h)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hz, habs⟩)))
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hz, habs⟩))

end Loop

end Hironaka.Resolution
