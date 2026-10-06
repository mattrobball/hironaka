/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Principalization.StrictTransforms
public import Hironaka.Resolution.Analytic.Principalization.MeetLocusChart
public import Hironaka.Manifold.FiniteSuccession.CenterList
import Hironaka.Manifold.Snc.Proper
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's disjoining blow-ups

The preliminary blow-ups of [Kol07, 72]: blow up the locus `Z_0` where all `k` members of the
boundary meet; the strict transforms have no `k`-fold intersection, so the next centre `Z_1` is
smooth, and "after `(k − 1)` steps we get rid of all pairwise intersections as well". This module
proves the
step — after blowing up the `m`-fold meet locus of an snc family with no `(m + 1)`-fold points,
the strict transforms have no `m`-fold point (`meetLocus_strictTransforms_eq_empty`, Kollár's
"do not have any `k`-fold intersections", by the chart computation: in the blow-up chart of index
`i` the strict transform of the member whose coordinate is the block coordinate `σ i` is empty,
and every member through a point of the centre is one of the block) — and defines the disjoining
list of centres `disjoinList m F` by recursion on the multiplicity `m = k, k − 1, …, 2`, with the
invariant carried as a hypothesis. Its properties (the final strict transforms are pairwise
disjoint, every centre lies over `Sing F`, the centres have snc with the running total transform,
compatibility with open inclusions) follow in `DisjoinLemmas.lean`, `DisjoinBoundary.lean` and
`DisjoinNatural.lean`. The `Hironaka` library has the same construction for schemes
(`Hironaka/Resolution/Algebraic/Kol07/Thm35/Disjoin.lean`).
-/

@[expose] public section

universe u

open Set AnalyticManifold
open scoped Manifold ContDiff

namespace Manifold.HypersurfaceFamily

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

variable {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M']
  [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M'] {π : M' → M}
  {F : HypersurfaceFamily M}

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The step of [Kol07, 72]: where no point lies on `m + 1` members, after blowing up the `m`-fold
meet locus no point lies on `m` of the strict transforms. Off the centre the strict transforms are
the preimages, so an `m`-fold point would map to a point of the centre; over a point `a` of the
centre the `m` members through `a` are exactly the block of the adapted chart, the blow-up chart of
index `i` through the point kills the strict transform of the member whose coordinate is `σ i`,
while every strict transform through the point comes from a member through `a` — so at most
`m − 1` of them pass. -/
theorem meetLocus_strictTransforms_eq_empty (hF : F.IsSnc ψ) {m : ℕ}
    (hm : F.meetLocus (m + 1) = ∅) (h : IsBlowUp ψ (F.meetLocus m) m π) :
    (F.strictTransforms π (F.meetLocus m)).meetLocus m = ∅ := by
  classical
  refine eq_empty_of_forall_notMem fun p hp => ?_
  by_cases hpY : π p ∈ F.meetLocus m
  · -- over the centre
    obtain ⟨s, hs, has⟩ := hpY
    obtain ⟨φ, σ, cidx, hφ, hc, hrange⟩ := hF.exists_adaptedChart_meetLocus hm ⟨s, hs, has⟩
    obtain ⟨i, Φ, hΦ, hpΦ⟩ := h.cover φ σ hφ p hc.mem_source
    -- the member of the block with coordinate `σ i`
    have hσi : σ i ∈ Set.range cidx := hrange ▸ Set.mem_range_self i
    obtain ⟨j₀, hj₀⟩ := hσi
    -- its strict transform misses the chart of index `i`
    have hempty : strictTransformSet π (F.meetLocus m) (F.hyp j₀.1) ∩ Φ.source = ∅ := by
      refine strictTransform_inter_source_eq_empty_of_subset hφ hΦ fun x hx hxj => ?_
      rw [← hj₀]
      exact (hc.mem_iff j₀ hx).mp hxj
    -- yet `p` lies on the strict transforms of all the members through `a`
    obtain ⟨t, ht, hpt⟩ := hp
    have hts : t ⊆ s := fun j hj =>
      mem_of_mem_hyp_of_meetLocus_succ_eq_empty hm hs has
        (mem_hyp_of_mem_strictTransforms h hF (hpt j hj))
    have hteq : t = s := Finset.eq_of_subset_of_card_le hts (hs.trans ht.symm).le
    have hj₀s : j₀.1 ∈ s := mem_of_mem_hyp_of_meetLocus_succ_eq_empty hm hs has j₀.2
    have hpj₀ : p ∈ strictTransformSet π (F.meetLocus m) (F.hyp j₀.1) := hpt j₀.1 (hteq ▸ hj₀s)
    exact Set.eq_empty_iff_forall_notMem.mp hempty p ⟨hpj₀, hpΦ⟩
  · -- off the centre the strict transforms are the preimages: `π p` would be an `m`-fold point
    exact hpY ((mem_meetLocus_strictTransforms_iff_of_notMem h hF hpY).mp hp)

end Manifold.HypersurfaceFamily

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

/-! ### The disjoining list of centres -/

variable {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- **The disjoining blow-ups** of [Kol07, 72] for an snc family with no `(m + 1)`-fold points, as
a list of centres — nothing for `m ≤ 1`; for `m + 2`, blow up the `(m + 2)`-fold meet locus (a
closed submanifold of codimension `m + 2`, `IsSnc.isClosedSubmanifold_meetLocus`) and continue
with the strict transforms, which have no `(m + 2)`-fold point
(`meetLocus_strictTransforms_eq_empty`). These are Kollár's `k − 1` steps from `m = k`; the empty
`m`-fold loci give empty centres, deleted by `eraseEmpty` afterwards ("ultimately the difference
is only in some empty blow ups, and we can forget about those at the end", [Kol07, 72];
[Kol07, 32]). -/
noncomputable def disjoinList :
    (m : ℕ) → ∀ {M : AnalyticManifold.{u} 𝕜 E} (F : HypersurfaceFamily M),
    F.IsSnc ψ₀ → F.meetLocus (m + 1) = ∅ → BlowUpSequence ψ₀ M
  | 0, M, _, _, _ => BlowUpSequence.nil M
  | 1, M, _, _, _ => BlowUpSequence.nil M
  | m + 2, _, F, hF, hm =>
    BlowUpSequence.cons (hF.isClosedSubmanifold_meetLocus hm)
      (disjoinList (m + 1)
        (F.strictTransforms (blowUpπ ψ₀ (hF.isClosedSubmanifold_meetLocus hm))
          (F.meetLocus (m + 2)))
        (HypersurfaceFamily.isSnc_strictTransforms (hF.isClosedSubmanifold_meetLocus hm)
          (isBlowUp_blowUpπ ψ₀ (hF.isClosedSubmanifold_meetLocus hm)) hF
          (hF.hasSncWith_meetLocus hm))
        (HypersurfaceFamily.meetLocus_strictTransforms_eq_empty hF hm
          (isBlowUp_blowUpπ ψ₀ (hF.isClosedSubmanifold_meetLocus hm))))

variable {M : AnalyticManifold.{u} 𝕜 E} (F : HypersurfaceFamily M)

@[simp] theorem disjoinList_zero (hF : F.IsSnc ψ₀) (hm : F.meetLocus 1 = ∅) :
    disjoinList (ψ₀ := ψ₀) 0 F hF hm = BlowUpSequence.nil M :=
  rfl

@[simp] theorem disjoinList_one (hF : F.IsSnc ψ₀) (hm : F.meetLocus 2 = ∅) :
    disjoinList (ψ₀ := ψ₀) 1 F hF hm = BlowUpSequence.nil M :=
  rfl

/-- Kollár's "`k − 1` steps" from `m = k`: the list at `m + 2` has `m + 1` centres. -/
theorem length_disjoinList : ∀ (m : ℕ) {M : AnalyticManifold.{u} 𝕜 E} (F : HypersurfaceFamily M)
    (hF : F.IsSnc ψ₀) (hm : F.meetLocus (m + 1) = ∅),
    (disjoinList (ψ₀ := ψ₀) m F hF hm).length = m - 1
  | 0, _, _, _, _ => rfl
  | 1, _, _, _, _ => rfl
  | m + 2, _, F, hF, hm => by
    have ih : (disjoinList (ψ₀ := ψ₀) (m + 1)
        (F.strictTransforms (blowUpπ ψ₀ (hF.isClosedSubmanifold_meetLocus hm))
          (F.meetLocus (m + 2)))
        (HypersurfaceFamily.isSnc_strictTransforms (hF.isClosedSubmanifold_meetLocus hm)
          (isBlowUp_blowUpπ ψ₀ (hF.isClosedSubmanifold_meetLocus hm)) hF
          (hF.hasSncWith_meetLocus hm))
        (HypersurfaceFamily.meetLocus_strictTransforms_eq_empty hF hm
          (isBlowUp_blowUpπ ψ₀ (hF.isClosedSubmanifold_meetLocus hm)))).toSuccession.length =
        m + 1 - 1 :=
      length_disjoinList (m + 1) _ _ _
    change (BlowUpSequence.cons (hF.isClosedSubmanifold_meetLocus hm) _).toSuccession.length =
      m + 2 - 1
    rw [BlowUpSequence.toSuccession_cons, FiniteSuccession.cons_length]
    omega

end Hironaka.Manifold
