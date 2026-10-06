/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# A blow-up sequence is an isomorphism off the images of its centres

Kollár's principalization theorem asserts that the composite `Π : X_r → X` "is an isomorphism
over `X ∖ cosupp I`" [Kol07, Theorem 35 (3)]. For a triple with a boundary `E` the isomorphism
holds over the complement of `cosupp I ∪ Sing E`, because the preliminary blow-ups that make the
components of the boundary disjoint have their centres in the multiple locus of `E` [Kol07, 72];
the real-analytic principalization theorem
(`exists_extensionCompatibleFamily_isNormalCrossingsDivisor_jacobianIdeal_mul_pullback`,
`Hironaka/Resolution/Analytic/BM97/JacobianAssembly.lean`) has `E = ∅` and asserts it off
`cosupp I`. The mechanism is that each `π_i` is a blow-up with centre `Z_i` [Kol07, Definition 29],
hence an analytic isomorphism off `Z_i` (condition (1) of [BM88, Definition 4.1],
`IsBlowUp.isLocalDiffeomorphOn_compl` and `IsBlowUp.bijOn_compl`). This module iterates that along
a finite succession whose centres all lie over a set `Z ⊆ X` (`CentersOver Z`: `Z_i ⊆ Π_i⁻¹(Z)`):
every partial composite `Π_i = π_0 ∘ ⋯ ∘ π_{i-1}` is an analytic isomorphism over `X ∖ Z`
(`isAnalyticIsoOver_stageMap`), by induction on `i` — off `Π_{i+1}⁻¹(Z)` the blow-up `π_i` lands
off `Z_i`, where it is a local diffeomorphism and a bijection onto `Π_i⁻¹(X ∖ Z)`, and the
composite of local diffeomorphisms (Mathlib's `IsLocalDiffeomorphAt.comp`) and of bijections
(`Set.BijOn.comp`) is one. The isomorphism clauses of the principalization and resolution theorems
are this with `Z = cosupp I ∪ Sing E`, once the centres are so placed
(`Hironaka/Resolution/Analytic/Wlo09/IsoOverReg.lean`).
-/

@[expose] public section

universe u

open Set
open scoped Manifold ContDiff

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- The centres of the succession all lie over `Z`: `Z_i ⊆ Π_i⁻¹(Z)` for every `i` (for the
principalization, `Z = cosupp I ∪ Sing E`, the set over which nothing is blown up). -/
def CentersOver (Z : Set M) : Prop :=
  ∀ i : Fin S.length, (S.center i).support ⊆ S.stageMap i.castSucc ⁻¹' Z

variable {S}

/-- [Kol07, Theorem 35 (3)] along the partial composites (condition (1) of [BM88, Definition 4.1]
iterated): when every centre lies over `Z`, the composite `Π_i : X_i → X` is an analytic
isomorphism over `X ∖ Z` — stated on the auxiliary composite indexed by `ℕ`, by induction. -/
theorem isAnalyticIsoOver_stageMapAux {Z : Set M} (hZ : S.CentersOver Z) :
    ∀ (i : ℕ) (hi : i < S.length + 1), (S.stageMapAux i hi).IsIsoOver Zᶜ
  | 0, _ => by
    refine ⟨fun x => ?_, ?_⟩
    · have h := (Diffeomorph.refl 𝓘(𝕜, E) M ω).isLocalDiffeomorph x.1
      rw [Diffeomorph.coe_refl] at h
      exact h
    · exact Set.bijOn_id _
  | i + 1, hi => by
    have ih := isAnalyticIsoOver_stageMapAux hZ i (Nat.lt_of_succ_lt hi)
    have hb := S.isBlowUp_map ⟨i, Nat.lt_of_succ_lt_succ hi⟩
    have hY : (S.center ⟨i, Nat.lt_of_succ_lt_succ hi⟩).support ⊆
        S.stageMapAux i (Nat.lt_of_succ_lt hi) ⁻¹' Z :=
      hZ ⟨i, Nat.lt_of_succ_lt_succ hi⟩
    -- a point of `X_i` over `X ∖ Z` lies off the centre `Z_i`
    have hsub : S.stageMapAux i (Nat.lt_of_succ_lt hi) ⁻¹' Zᶜ ⊆
        ((S.center ⟨i, Nat.lt_of_succ_lt_succ hi⟩).support)ᶜ :=
      fun y hy hyY => hy (hY hyY)
    refine ⟨fun x => ?_, ?_⟩
    · exact (hb.isLocalDiffeomorphOn_compl ⟨x.1, hsub x.2⟩).comp 𝓘(𝕜, E) _
        (ih.1 ⟨S.map ⟨i, Nat.lt_of_succ_lt_succ hi⟩ x.1, x.2⟩)
    · have hbf := hb.bijOn_compl.subset_right hsub
      rw [Set.inter_eq_right.mpr (Set.preimage_mono hsub)] at hbf
      exact ih.2.comp hbf

/-- [Kol07, Theorem 35 (3)] along the partial composites: when every centre lies over `Z`, the
composite `Π_i : X_i → X` is an analytic isomorphism over `X ∖ Z`. -/
theorem isAnalyticIsoOver_stageMap {Z : Set M} (hZ : S.CentersOver Z) (i : Fin (S.length + 1)) :
    (S.stageMap i).IsIsoOver Zᶜ :=
  isAnalyticIsoOver_stageMapAux hZ i.1 i.2

/-- Centres over a smaller set are over a larger one. -/
theorem CentersOver.mono {Z Z' : Set M} (hZ : S.CentersOver Z) (h : Z ⊆ Z') : S.CentersOver Z' :=
  fun i => (hZ i).trans (Set.preimage_mono h)

end AnalyticManifold.FiniteSuccession
