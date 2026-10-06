/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Principalization.Disjoin
public import Hironaka.Resolution.Analytic.Principalization.IsoOff
public import Hironaka.Manifold.FiniteSuccession.Restrict.StrictTransformSeq
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Resolution.Analytic.MaximalContactLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The disjoining list: the final strict transforms and the centres

Alongside `disjoinList m F` this module carries the family the recursion ends with — the strict
transforms of the components along the whole list, `disjoinFinal m F` on the last stage — and
proves Kollár's conclusions in [Kol07, 72]:

* "After `(k − 1)` steps we get rid of all pairwise intersections as well": the final strict
  transforms form a simple normal crossings divisor whose members are pairwise disjoint (no point
  lies on two of them, `meetLocus 2 = ∅`), so that "we can just declare that `E` is a single
  divisor" (`Collapse.lean`);
* every centre lies over the multiple locus `Sing E` — the `m`-fold meet loci for `m ≥ 2` are
  inside `Sing`, and the multiple locus of the strict transforms lies over the multiple locus
  (`CentersOver F.sing`, the hypothesis of `isAnalyticIsoOver_stageMap` for clause (3) of
  [Kol07, Theorem 35] in `ClauseThree.lean`);
* the bridge to the boundary family: the member `j` of `disjoinFinal` is the strict transform
  `strictTransformSeq (F.hyp j)` at the last stage (the `cons` rule `cons_strictTransformSeq_succ`
  at every step) — the member `originalIdx j` of the boundary family `totalTransformSeqFrom F`
  there (`hyp_originalIdx`).

The `Hironaka` library has the corresponding statements in
`Hironaka/Resolution/Algebraic/Kol07/Thm35/Disjoin.lean`.
-/

@[expose] public section

universe u

open Set AnalyticManifold
open scoped Manifold ContDiff

namespace Manifold.HypersurfaceFamily

open _root_.Manifold
open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

variable {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M']
  [SecondCountableTopology M'] {π : M' → M} {Y : Set M} {c : ℕ} {F : HypersurfaceFamily M}

/-- A point on two distinct strict transforms lies over a point on the two members — the multiple
locus of the strict transforms lies over the multiple locus (the disjoining centres of [Kol07, 72]
stay over `Sing E`). -/
theorem singularLocus_strictTransforms_subset (h : IsBlowUp ψ Y c π) (hF : F.IsSnc ψ) :
    (F.strictTransforms π Y).singularLocus ⊆ π ⁻¹' F.singularLocus := by
  rintro p ⟨i, j, hij, hpi, hpj⟩
  exact ⟨i, j, hij, mem_hyp_of_mem_strictTransforms h hF hpi,
    mem_hyp_of_mem_strictTransforms h hF hpj⟩

end Manifold.HypersurfaceFamily

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

variable {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

section Next

variable {M : AnalyticManifold.{u} 𝕜 E}

/-- The strict transforms under the first disjoining blow-up — the family the recursion
`disjoinList` continues with at `m + 2`. -/
noncomputable abbrev disjoinNext (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀) {m : ℕ}
    (hm : F.meetLocus (m + 2 + 1) = ∅) :
    HypersurfaceFamily (blowUp ψ₀ (hF.isClosedSubmanifold_meetLocus hm)) :=
  F.strictTransforms (blowUpπ ψ₀ (hF.isClosedSubmanifold_meetLocus hm)) (F.meetLocus (m + 2))

theorem disjoinNext_isSnc (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀) {m : ℕ}
    (hm : F.meetLocus (m + 2 + 1) = ∅) : (disjoinNext F hF hm).IsSnc ψ₀ :=
  HypersurfaceFamily.isSnc_strictTransforms (hF.isClosedSubmanifold_meetLocus hm)
    (isBlowUp_blowUpπ ψ₀ (hF.isClosedSubmanifold_meetLocus hm)) hF (hF.hasSncWith_meetLocus hm)

theorem meetLocus_disjoinNext (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀) {m : ℕ}
    (hm : F.meetLocus (m + 2 + 1) = ∅) : (disjoinNext F hF hm).meetLocus (m + 1 + 1) = ∅ :=
  HypersurfaceFamily.meetLocus_strictTransforms_eq_empty hF hm
    (isBlowUp_blowUpπ ψ₀ (hF.isClosedSubmanifold_meetLocus hm))

/-- The computation rule of `disjoinList` at `m + 2` (definitional). -/
theorem disjoinList_succ_succ (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀) {m : ℕ}
    (hm : F.meetLocus (m + 2 + 1) = ∅) :
    disjoinList (ψ₀ := ψ₀) (m + 2) F hF hm =
      BlowUpSequence.cons (hF.isClosedSubmanifold_meetLocus hm)
        (disjoinList (m + 1) (disjoinNext F hF hm) (disjoinNext_isSnc F hF hm)
          (meetLocus_disjoinNext F hF hm)) :=
  rfl

end Next

/-- The strict transform of the component `j` along the whole disjoining list, on the last stage
(by the recursion of `disjoinList`). -/
noncomputable def disjoinFinalHyp :
    (m : ℕ) → ∀ {M : AnalyticManifold.{u} 𝕜 E} (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀)
    (hm : F.meetLocus (m + 1) = ∅),
    F.ι → Set ((disjoinList (ψ₀ := ψ₀) m F hF hm).stage (Fin.last _))
  | 0, _, F, _, _, j => F.hyp j
  | 1, _, F, _, _, j => F.hyp j
  | m + 2, _, F, hF, hm, j =>
    disjoinFinalHyp (m + 1) (disjoinNext F hF hm) (disjoinNext_isSnc F hF hm)
      (meetLocus_disjoinNext F hF hm) j

variable {M : AnalyticManifold.{u} 𝕜 E}

/-- The strict transforms of the components along the whole disjoining list — the family the
recursion `disjoinList` ends with, on the last stage; indexed by the components of `F`. -/
noncomputable def disjoinFinal (m : ℕ) (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀)
    (hm : F.meetLocus (m + 1) = ∅) :
    HypersurfaceFamily ((disjoinList (ψ₀ := ψ₀) m F hF hm).stage (Fin.last _)) where
  ι := F.ι
  countable := F.countable
  linearOrder := F.linearOrder
  hyp := disjoinFinalHyp m F hF hm

theorem disjoinFinal_hyp (m : ℕ) (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀)
    (hm : F.meetLocus (m + 1) = ∅) (j : F.ι) :
    (disjoinFinal (ψ₀ := ψ₀) m F hF hm).hyp j = disjoinFinalHyp m F hF hm j :=
  rfl

/-- The computation rule of `disjoinFinal` at `m + 2` (definitional). -/
theorem disjoinFinal_succ_succ (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀) {m : ℕ}
    (hm : F.meetLocus (m + 2 + 1) = ∅) :
    disjoinFinal (ψ₀ := ψ₀) (m + 2) F hF hm =
      disjoinFinal (m + 1) (disjoinNext F hF hm) (disjoinNext_isSnc F hF hm)
        (meetLocus_disjoinNext F hF hm) :=
  rfl

/-- The final family is a simple normal crossings divisor (`isSnc_strictTransforms` at every
step). -/
theorem disjoinFinal_isSnc : ∀ (m : ℕ) {M : AnalyticManifold.{u} 𝕜 E} (F : HypersurfaceFamily M)
    (hF : F.IsSnc ψ₀) (hm : F.meetLocus (m + 1) = ∅),
    (disjoinFinal (ψ₀ := ψ₀) m F hF hm).IsSnc ψ₀
  | 0, _, _, hF, _ => hF
  | 1, _, _, hF, _ => hF
  | m + 2, _, F, hF, hm => by
    rw [disjoinFinal_succ_succ]
    exact disjoinFinal_isSnc (m + 1) _ _ _

/-- Kollár's "after `(k − 1)` steps we get rid of all pairwise intersections" [Kol07, 72]: the
final strict transforms are pairwise disjoint — no point lies on two of them (the invariant
`meetLocus (m + 1) = ∅` carried down to `m = 1`). -/
theorem meetLocus_two_disjoinFinal_eq_empty : ∀ (m : ℕ) {M : AnalyticManifold.{u} 𝕜 E}
    (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀) (hm : F.meetLocus (m + 1) = ∅),
    (disjoinFinal (ψ₀ := ψ₀) m F hF hm).meetLocus 2 = ∅
  | 0, _, F, _, hm => by
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    have h1 : x ∈ F.meetLocus (0 + 1) := F.meetLocus_antitone (by norm_num) hx
    rw [hm] at h1
    exact h1
  | 1, _, _, _, hm => hm
  | m + 2, _, F, hF, hm => by
    rw [disjoinFinal_succ_succ]
    exact meetLocus_two_disjoinFinal_eq_empty (m + 1) _ _ _

/-- Every centre of the disjoining list of [Kol07, 72] lies over the multiple locus `Sing F` — the
`(m + 2)`-fold meet locus is inside `Sing F`, and the centres of the rest lie over the multiple
locus of the strict transforms, which lies over `Sing F`. -/
theorem centersOver_disjoinList : ∀ (m : ℕ) {M : AnalyticManifold.{u} 𝕜 E}
    (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀) (hm : F.meetLocus (m + 1) = ∅),
    (disjoinList (ψ₀ := ψ₀) m F hF hm).toSuccession.CentersOver F.singularLocus
  | 0, _, _, _, _ => fun i => i.elim0
  | 1, _, _, _, _ => fun i => i.elim0
  | m + 2, _, F, hF, hm => by
    rintro ⟨k, hk⟩ p hp
    cases k with
    | zero =>
      -- the first centre is the `(m + 2)`-fold meet locus, the composite the identity
      change p ∈ (hF.isClosedSubmanifold_meetLocus hm).idealSheaf.support at hp
      rw [(hF.isClosedSubmanifold_meetLocus hm).cosupport_idealSheaf] at hp
      exact F.meetLocus_subset_singularLocus (by omega) hp
    | succ k =>
      have ih := centersOver_disjoinList (m + 1) (disjoinNext F hF hm) (disjoinNext_isSnc F hF hm)
        (meetLocus_disjoinNext F hF hm) ⟨k, Nat.lt_of_succ_lt_succ hk⟩ hp
      have hsub := HypersurfaceFamily.singularLocus_strictTransforms_subset
        (isBlowUp_blowUpπ ψ₀ (hF.isClosedSubmanifold_meetLocus hm)) hF
      -- the bound, stated on the `cons` form so that the computation rule rewrites
      have hk' : k + 1 < (BlowUpSequence.cons (hF.isClosedSubmanifold_meetLocus hm)
          (disjoinList (m + 1) (disjoinNext F hF hm) (disjoinNext_isSnc F hF hm)
            (meetLocus_disjoinNext F hF hm))).toSuccession.length + 1 :=
        Nat.lt_succ_of_lt hk
      change (BlowUpSequence.cons (hF.isClosedSubmanifold_meetLocus hm)
        (disjoinList (m + 1) (disjoinNext F hF hm) (disjoinNext_isSnc F hF hm)
          (meetLocus_disjoinNext F hF hm))).toSuccession.stageMapAux (k + 1) hk' p ∈ F.singularLocus
      rw [BlowUpSequence.stageMapAux_cons_succ _ _ k hk' p]
      exact hsub ih

/-- The members of the final family are the strict transforms of the components along the list
(`strictTransformSeq` at the last stage; the `cons` rule is `cons_strictTransformSeq_succ`) —
hence, by `hyp_originalIdx`, the members `originalIdx j` of the boundary family
`totalTransformSeqFrom F` at the last stage. -/
theorem hyp_disjoinFinal : ∀ (m : ℕ) {M : AnalyticManifold.{u} 𝕜 E} (F : HypersurfaceFamily M)
    (hF : F.IsSnc ψ₀) (hm : F.meetLocus (m + 1) = ∅) (j : F.ι),
    (disjoinFinal (ψ₀ := ψ₀) m F hF hm).hyp j =
      (disjoinList (ψ₀ := ψ₀) m F hF hm).toSuccession.strictTransformSeq (F.hyp j) (Fin.last _)
  | 0, _, _, _, _, _ => rfl
  | 1, _, _, _, _, _ => rfl
  | m + 2, _, F, hF, hm, j => by
    have ih := hyp_disjoinFinal (m + 1) (disjoinNext F hF hm) (disjoinNext_isSnc F hF hm)
      (meetLocus_disjoinNext F hF hm) j
    exact ih.trans (FiniteSuccession.cons_strictTransformSeq_succ (F.hyp j)
      (hF.isClosedSubmanifold_meetLocus hm) _ (Fin.last _)).symm

end Hironaka.Manifold
