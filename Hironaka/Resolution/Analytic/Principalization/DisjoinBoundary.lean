/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.BoundaryFamily
public import Hironaka.Resolution.Analytic.Principalization.Collapse
public import Hironaka.Resolution.Analytic.Principalization.Disjoin
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.Snc.TotalTransform
import Hironaka.Manifold.Submanifold.CodimUnique
import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
import Hironaka.Resolution.Analytic.Principalization.DisjoinLemmas
import Hironaka.Resolution.Analytic.Principalization.MeetLocusSubfamily
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The disjoining list against the running total transform

Clause (1) of [Kol07, Theorem 35] for the disjoining blow-ups of [Kol07, 72]: every centre has
simple normal crossings with the current divisor — the TOTAL transform of the boundary so far
(the strict transforms of the components of `E` together with the exceptional divisors), so that
the end result `(X', π^* I, ∑ E^i)` "satisfies the assumptions of (68)" (Kollár's `Z_1` "is smooth
since the `(π_0)^{-1}_* E_i` do not have any `k`-fold intersections"). Clause (1) asks this of
every centre of the value against `totalTransformSeqFrom (F|U)` at its stage, in the given
codimension. This module proves it for the disjoining list: carrying along the recursion any snc
family `G` that contains the members of `F` (an injective relabelling `e` with
`G.hyp (e j) = F.hyp j` — at the start `G = F`, `e = id`; after a step `G' = G.totalTransform π Y`,
`e' = toLex ∘ inl ∘ e`), the boundary family `totalTransformSeqFrom G` is snc at every stage and
every centre — the meet locus of the `F`-members, which is the meet locus of the `e`-subfamily of
`G` — has snc with it (`disjoinList_boundary`), the given codimension matched by
`IsClosedSubmanifold.codim_eq_of_nonempty` (an empty centre satisfies the clause vacuously;
[Kol07, 32]). Used by `DisjoinInput.lean` (the disjoined boundary is snc) and `ClauseOne.lean`.
The `Hironaka` library has the corresponding statement in
`Hironaka/Resolution/Algebraic/Kol07/Thm35/Disjoin.lean`.
-/

public section

universe u

open Set AnalyticManifold
open scoped Manifold ContDiff

namespace Manifold.HypersurfaceFamily

open _root_.Manifold
open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

section Relabel

variable {M : Type u}

/-- The meet loci of the subfamily indexed by the range of an injective relabelling with the same
members are those of the relabelled family. -/
theorem meetLocus_subfamily_range_eq {G F : HypersurfaceFamily M} (e : F.ι → G.ι)
    (he : Function.Injective e) (hhyp : ∀ j, G.hyp (e j) = F.hyp j) (k : ℕ) :
    (G.subfamily (fun g => g ∈ Set.range e)).meetLocus k = F.meetLocus k := by
  ext x
  constructor
  · rintro ⟨s, hs, hxs⟩
    -- the chosen preimage of each member of the subfamily
    have hinj : Function.Injective
        (fun g : (G.subfamily (fun g => g ∈ Set.range e)).ι => Classical.choose g.2) := by
      intro g g' hgg'
      have h1 : g.1 = g'.1 := by
        rw [← Classical.choose_spec g.2, ← Classical.choose_spec g'.2]
        exact congrArg e hgg'
      exact Subtype.ext h1
    refine ⟨s.map ⟨_, hinj⟩, by rw [Finset.card_map, hs], fun j hj => ?_⟩
    obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp hj
    have hxg : x ∈ G.hyp g.1 := hxs g hg
    change x ∈ F.hyp (Classical.choose g.2)
    rw [← hhyp, Classical.choose_spec g.2]
    exact hxg
  · rintro ⟨s, hs, hxs⟩
    have hinj : Function.Injective
        (fun j : F.ι => (⟨e j, ⟨j, rfl⟩⟩ : (G.subfamily (fun g => g ∈ Set.range e)).ι)) :=
      fun j j' hjj' => he (Subtype.mk.inj hjj')
    refine ⟨s.map ⟨_, hinj⟩, by rw [Finset.card_map, hs], fun g hg => ?_⟩
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hg
    change x ∈ G.hyp (e j)
    exact (hhyp j).symm ▸ hxs j hj

end Relabel

variable {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- Simple normal crossings with a closed submanifold does not depend on the codimension given
for it — for a nonempty `Y` the codimension is unique (`codim_eq_of_nonempty`), for an empty `Y`
the clause is vacuous (the empty blow-up convention, [Kol07, 32]). -/
theorem HasSncWith.of_codim {F : HypersurfaceFamily M} {Y : Set M} {c c' : ℕ} {n' : ℕ}
    {ψ' : E ≃L[𝕜] (Fin n' → 𝕜)} (h : F.HasSncWith ψ Y c) (hY : IsClosedSubmanifold ψ Y c)
    (hY' : IsClosedSubmanifold ψ' Y c') : F.HasSncWith ψ Y c' := by
  rcases Y.eq_empty_or_nonempty with hY0 | hne
  · intro a ha
    rw [hY0] at ha
    exact absurd ha (Set.notMem_empty a)
  · obtain rfl := hY.codim_eq_of_nonempty hY' hne
    exact h

end Manifold.HypersurfaceFamily

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

variable {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- Clause (1) of [Kol07, Theorem 35] for the disjoining blow-ups of [Kol07, 72]: along the
disjoining list, for any snc family `G` containing the members of `F` (an injective relabelling
`e` with the same members), the boundary family `totalTransformSeqFrom G` is snc at every stage,
and every centre has snc with it at its stage, in the given codimension. -/
theorem disjoinList_boundary : ∀ (m : ℕ) {M : AnalyticManifold.{u} 𝕜 E}
    (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀) (hm : F.meetLocus (m + 1) = ∅)
    (G : HypersurfaceFamily M) (e : F.ι → G.ι), G.IsSnc ψ₀ → Function.Injective e →
    (∀ j, G.hyp (e j) = F.hyp j) →
    (∀ i : Fin ((disjoinList (ψ₀ := ψ₀) m F hF hm).toSuccession.length + 1),
      ((disjoinList (ψ₀ := ψ₀) m F hF hm).toSuccession.totalTransformSeqFrom G i).IsSnc ψ₀) ∧
    ∀ i : Fin (disjoinList (ψ₀ := ψ₀) m F hF hm).toSuccession.length,
      ((disjoinList (ψ₀ := ψ₀) m F hF hm).toSuccession.totalTransformSeqFrom G
        i.castSucc).HasSncWith ψ₀
        ((disjoinList (ψ₀ := ψ₀) m F hF hm).toSuccession.center i).support
        ((disjoinList (ψ₀ := ψ₀) m F hF hm).toSuccession.codim i)
  | 0, _, _, _, _, G, _, hG, _, _ =>
    ⟨fun i => by
      obtain ⟨k, hk⟩ := i
      cases k with
      | zero => exact hG
      | succ k => exact absurd hk (by change ¬ (k + 1 < 0 + 1); omega), fun i => i.elim0⟩
  | 1, _, _, _, _, G, _, hG, _, _ =>
    ⟨fun i => by
      obtain ⟨k, hk⟩ := i
      cases k with
      | zero => exact hG
      | succ k => exact absurd hk (by change ¬ (k + 1 < 0 + 1); omega), fun i => i.elim0⟩
  | m + 2, _, F, hF, hm, G, e, hG, he, hhyp => by
    -- the first centre has snc with `G`: the `e`-subfamily's meet locus is `F`'s
    have hYm : (G.subfamily (fun g => g ∈ Set.range e)).meetLocus (m + 2 + 1) = ∅ := by
      rw [HypersurfaceFamily.meetLocus_subfamily_range_eq e he hhyp]
      exact hm
    have hsw : G.HasSncWith ψ₀ (F.meetLocus (m + 2)) (m + 2) := by
      have h := hG.hasSncWith_meetLocus_subfamily hYm
      rwa [HypersurfaceFamily.meetLocus_subfamily_range_eq e he hhyp] at h
    -- the rest, with the total transform of `G` and the relabelling through `inl`
    have ih := disjoinList_boundary (m + 1) (disjoinNext F hF hm) (disjoinNext_isSnc F hF hm)
      (meetLocus_disjoinNext F hF hm)
      (G.totalTransform (blowUpπ ψ₀ (hF.isClosedSubmanifold_meetLocus hm)) (F.meetLocus (m + 2)))
      (fun j => toLex (Sum.inl (e j)))
      (HypersurfaceFamily.isSnc_totalTransform (hF.isClosedSubmanifold_meetLocus hm)
        (isBlowUp_blowUpπ ψ₀ (hF.isClosedSubmanifold_meetLocus hm)) hG hsw)
      (fun j j' h => he (Sum.inl.inj (toLex.injective h)))
      (fun j => congrArg
        (strictTransformSet (blowUpπ ψ₀ (hF.isClosedSubmanifold_meetLocus hm))
          (F.meetLocus (m + 2))) (hhyp j))
    refine ⟨fun i => ?_, fun i => ?_⟩
    · obtain ⟨k, hk⟩ := i
      cases k with
      | zero => exact hG
      | succ k =>
        have hk' : k + 1 < (FiniteSuccession.cons ψ₀ (hF.isClosedSubmanifold_meetLocus hm)
            (disjoinList (m + 1) (disjoinNext F hF hm) (disjoinNext_isSnc F hF hm)
              (meetLocus_disjoinNext F hF hm)).toSuccession).length + 1 := hk
        have heq := FiniteSuccession.cons_totalTransformSeqFromAux_succ
          (hF.isClosedSubmanifold_meetLocus hm)
          (disjoinList (m + 1) (disjoinNext F hF hm) (disjoinNext_isSnc F hF hm)
            (meetLocus_disjoinNext F hF hm)).toSuccession G k hk'
        rw [(hF.isClosedSubmanifold_meetLocus hm).cosupport_idealSheaf] at heq
        change ((FiniteSuccession.cons ψ₀ (hF.isClosedSubmanifold_meetLocus hm)
          (disjoinList (m + 1) (disjoinNext F hF hm) (disjoinNext_isSnc F hF hm)
            (meetLocus_disjoinNext F hF hm)).toSuccession).totalTransformSeqFromAux G (k + 1)
              hk').IsSnc ψ₀
        rw [heq]
        exact ih.1 ⟨k, Nat.lt_of_succ_lt_succ hk⟩
    · obtain ⟨k, hk⟩ := i
      cases k with
      | zero =>
        -- the first centre: `F.meetLocus (m + 2)`, in the chosen codimension
        have hZ := (disjoinList (ψ₀ := ψ₀) (m + 2) F hF hm).toSuccession.isClosedSubmanifold_center
          ⟨0, hk⟩
        have hY0 : ((disjoinList (ψ₀ := ψ₀) (m + 2) F hF hm).toSuccession.center ⟨0, hk⟩).support =
            F.meetLocus (m + 2) :=
          (hF.isClosedSubmanifold_meetLocus hm).cosupport_idealSheaf
        rw [hY0] at hZ
        change G.HasSncWith ψ₀ _ _
        rw [hY0]
        exact hsw.of_codim (hF.isClosedSubmanifold_meetLocus hm) hZ
      | succ k =>
        have hk' : k + 1 < (FiniteSuccession.cons ψ₀ (hF.isClosedSubmanifold_meetLocus hm)
            (disjoinList (m + 1) (disjoinNext F hF hm) (disjoinNext_isSnc F hF hm)
              (meetLocus_disjoinNext F hF hm)).toSuccession).length + 1 := Nat.lt_succ_of_lt hk
        have heq := FiniteSuccession.cons_totalTransformSeqFromAux_succ
          (hF.isClosedSubmanifold_meetLocus hm)
          (disjoinList (m + 1) (disjoinNext F hF hm) (disjoinNext_isSnc F hF hm)
            (meetLocus_disjoinNext F hF hm)).toSuccession G k hk'
        rw [(hF.isClosedSubmanifold_meetLocus hm).cosupport_idealSheaf] at heq
        change ((FiniteSuccession.cons ψ₀ (hF.isClosedSubmanifold_meetLocus hm)
          (disjoinList (m + 1) (disjoinNext F hF hm) (disjoinNext_isSnc F hF hm)
            (meetLocus_disjoinNext F hF hm)).toSuccession).totalTransformSeqFromAux G (k + 1)
              hk').HasSncWith ψ₀
          ((disjoinList (m + 1) (disjoinNext F hF hm) (disjoinNext_isSnc F hF hm)
            (meetLocus_disjoinNext F hF hm)).toSuccession.center
              ⟨k, Nat.lt_of_succ_lt_succ hk⟩).support
          ((disjoinList (m + 1) (disjoinNext F hF hm) (disjoinNext_isSnc F hF hm)
            (meetLocus_disjoinNext F hF hm)).toSuccession.codim ⟨k, Nat.lt_of_succ_lt_succ hk⟩)
        rw [heq]
        exact ih.2 ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- Clause (1) of [Kol07, Theorem 35] for the disjoining list from its own family `F`
(`e = id`). -/
theorem disjoinList_center_hasSncWith (m : ℕ) {M : AnalyticManifold.{u} 𝕜 E}
    (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀) (hm : F.meetLocus (m + 1) = ∅)
    (i : Fin (disjoinList (ψ₀ := ψ₀) m F hF hm).toSuccession.length) :
    ((disjoinList (ψ₀ := ψ₀) m F hF hm).toSuccession.totalTransformSeqFrom F
      i.castSucc).HasSncWith ψ₀
      ((disjoinList (ψ₀ := ψ₀) m F hF hm).toSuccession.center i).support
      ((disjoinList (ψ₀ := ψ₀) m F hF hm).toSuccession.codim i) :=
  (disjoinList_boundary m F hF hm F id hF Function.injective_id fun _ => rfl).2 i

/-- The boundary family from `F` along the disjoining list is snc at every stage. -/
theorem disjoinList_isSnc_totalTransformSeqFrom (m : ℕ) {M : AnalyticManifold.{u} 𝕜 E}
    (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀) (hm : F.meetLocus (m + 1) = ∅)
    (i : Fin ((disjoinList (ψ₀ := ψ₀) m F hF hm).toSuccession.length + 1)) :
    ((disjoinList (ψ₀ := ψ₀) m F hF hm).toSuccession.totalTransformSeqFrom F i).IsSnc ψ₀ :=
  (disjoinList_boundary m F hF hm F id hF Function.injective_id fun _ => rfl).1 i

end Hironaka.Manifold
