/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Snc.Basic
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
import Hironaka.Resolution.Analytic.Principalization.MonomialStalk
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# One step of the monomial formula: a boundary monomial pulled back along a blow-up

The intrinsic, chart-free form of Kollár's `Π^* I = 𝒪(−∑ Π^*_{r,j+1} F_j)` [Kol07, 72] at a point
`x`: **`J` is a boundary monomial at `x` with residual `R`** —
`J_x = (∏_{j ∈ s} I(E^j)_x^{α_j}) · R_x` for finitely many members `E^j` of the boundary family
through `x` (`HypersurfaceFamily.IsBoundaryMonomialAt`). The monomial clause of the
principalization is this predicate at the last stage with the unit residual.

`isBoundaryMonomialAt_pullback`: the form is preserved by one blowing-up `π` along a centre `Y`
with simple normal crossings with the family, provided the residual is divided exactly by a power
of the exceptional ideal (`R_{π p}` pulls back to `I_{F,p}^e · R'_p`): each member through `π p`
pulls back to `I_{F,p}^ε · I(strict transform)_p` (`MonomialStalk.lean`), the exponents on the
exceptional member add up, and the members of the total transform not through `p` (strict
transforms missing `p`; the exceptional divisor when `π p ∉ Y`) contribute the unit ideal and are
dropped from the index set. The total transform of a divisor is that of [Kol07, Definition 25];
the marked transform with its exact division is [Kol07, (60.1)]. Used stage by stage in
`MonomialSeq.lean` and in the monomial step of the order reduction.
-/

@[expose] public section

universe u

open TopologicalSpace Filter Topology
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

/-- `Ideal.map` of a finite product of ideals is the product of the images. -/
theorem Ideal.map_finset_prod {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {ι : Type*}
    (s : Finset ι) (g : ι → Ideal R) :
    Ideal.map f (∏ i ∈ s, g i) = ∏ i ∈ s, Ideal.map f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Ideal.one_eq_top, Ideal.map_top]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Ideal.map_mul, ih]

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The intrinsic reading of Kollár's explicit formula at a point [Kol07, 72]: **`J` is at `x` a
monomial in the vanishing ideals of finitely many members of `G` through `x`, times the residual
`R`** — `J_x = (∏_{j ∈ s} I(G^j)_x^{α j}) · R_x` with `x ∈ G^j` for `j ∈ s`. -/
def _root_.Manifold.HypersurfaceFamily.IsBoundaryMonomialAt {X : AnalyticManifold.{u} 𝕜 E}
    (G : HypersurfaceFamily X) (J R : AnalyticManifold.IdealSheaf X) (x : X) : Prop :=
  ∃ (s : Finset G.ι) (α : G.ι → ℕ), (∀ j ∈ s, x ∈ G.hyp j) ∧
    J.stalkIdeal x =
      (∏ j ∈ s, vanishingStalk (𝕜 := 𝕜) (E := E) (G.hyp j) x ^ α j) * R.stalkIdeal x

variable {M M' : AnalyticManifold.{u} 𝕜 E} {π : M' → M} {Y : Set M} {c : ℕ}
  {F : HypersurfaceFamily M}

/-- The strict-transform index `j ↦ inl j` of the total transform, as an embedding. -/
def _root_.Manifold.HypersurfaceFamily.inlTotalEmb (F : HypersurfaceFamily M) (π : M' → M)
    (Y : Set M) :
    F.ι ↪ (F.totalTransform π Y).ι :=
  ⟨fun j => toLex (Sum.inl j), fun _ _ hab => Sum.inl_injective (toLex.injective hab)⟩

/-- Kollár's formula, one step ([Kol07, 72]; the exact division of [Kol07, (60.1)]): if `J` is a
boundary monomial at `π p` with residual `R`, and the residual pulls back to `I_{F,p}^e · R'_p`,
then the pull-back `π⁻¹(J)` is a boundary monomial at `p` for the total transform of the family
with residual `R'` — the members through `π p` pull back to `I_F^ε` times their strict transforms
(`exists_map_germMap_vanishingStalk_hyp_eq'`), the exceptional exponents add, and the members of
the total transform not through `p` are dropped (their vanishing ideal at `p` is the unit
ideal). -/
theorem isBoundaryMonomialAt_pullback (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
    (hF : F.IsSnc ψ) (hsnc : F.HasSncWith ψ Y c) {J R : AnalyticManifold.IdealSheaf M}
    {R' : AnalyticManifold.IdealSheaf M'} {p : M'} (hJ : F.IsBoundaryMonomialAt J R (π p))
        {e : ℕ}
    (hR : Ideal.map (germMap π h.contMDiff p) (R.stalkIdeal (π p)) =
      vanishingStalk (𝕜 := 𝕜) (E := E) (π ⁻¹' Y) p ^ e * R'.stalkIdeal p) :
    (F.totalTransform π Y).IsBoundaryMonomialAt (J.pullback π h.contMDiff) R' p := by
  classical
  obtain ⟨s, α, hs, hJx⟩ := hJ
  have hclosed : ∀ k, IsClosed ((F.totalTransform π Y).hyp k) :=
    HypersurfaceFamily.isClosed_hyp_totalTransform h.contMDiff.continuous hY.isClosed F
  -- the transported product: the exponents on the exceptional divisor add up
  have key : ∀ t : Finset F.ι, (∀ j ∈ t, π p ∈ F.hyp j) → ∃ N : ℕ,
      Ideal.map (germMap π h.contMDiff p)
          (∏ j ∈ t, vanishingStalk (𝕜 := 𝕜) (E := E) (F.hyp j) (π p) ^ α j) =
        vanishingStalk (𝕜 := 𝕜) (E := E) (π ⁻¹' Y) p ^ N *
          ∏ j ∈ t, vanishingStalk (𝕜 := 𝕜) (E := E)
            ((F.totalTransform π Y).hyp (toLex (Sum.inl j))) p ^ α j := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨0, by simp only [Finset.prod_empty, pow_zero, Ideal.one_eq_top, Ideal.map_top,
        Ideal.top_mul]⟩
    | insert j t hj ih =>
      intro ht
      obtain ⟨N, hN⟩ := ih fun k hk => ht k (Finset.mem_insert_of_mem hk)
      obtain ⟨ε, -, hε⟩ := exists_map_germMap_vanishingStalk_hyp_eq' hY h hF hsnc p
        ⟨j, ht j (Finset.mem_insert_self j t)⟩
      refine ⟨ε * α j + N, ?_⟩
      rw [Finset.prod_insert hj, Finset.prod_insert hj, Ideal.map_mul, Ideal.map_pow, hε, hN]
      ring
  obtain ⟨N, hN⟩ := key s hs
  have hpull : (J.pullback π h.contMDiff).stalkIdeal p =
      vanishingStalk (𝕜 := 𝕜) (E := E) (π ⁻¹' Y) p ^ (N + e) *
        ((∏ j ∈ s, vanishingStalk (𝕜 := 𝕜) (E := E)
          ((F.totalTransform π Y).hyp (toLex (Sum.inl j))) p ^ α j) * R'.stalkIdeal p) := by
    rw [IdealSheaf.stalkIdeal_pullback, hJx, Ideal.map_mul, hN, hR]
    ring
  -- drop the strict transforms missing `p`
  set s₀ := s.filter (fun j => p ∈ (F.totalTransform π Y).hyp (toLex (Sum.inl j))) with hs₀
  have hprod : ∏ j ∈ s, vanishingStalk (𝕜 := 𝕜) (E := E)
        ((F.totalTransform π Y).hyp (toLex (Sum.inl j))) p ^ α j =
      ∏ j ∈ s₀, vanishingStalk (𝕜 := 𝕜) (E := E)
        ((F.totalTransform π Y).hyp (toLex (Sum.inl j))) p ^ α j := by
    rw [← Finset.prod_filter_mul_prod_filter_not s
      (fun j => p ∈ (F.totalTransform π Y).hyp (toLex (Sum.inl j)))]
    have hone : ∏ j ∈ s.filter (fun j => ¬ p ∈ (F.totalTransform π Y).hyp (toLex (Sum.inl j))),
        vanishingStalk (𝕜 := 𝕜) (E := E)
          ((F.totalTransform π Y).hyp (toLex (Sum.inl j))) p ^ α j = 1 := by
      refine Finset.prod_eq_one fun j hj => ?_
      rw [vanishingStalk_eq_top_of_notMem (hclosed _) (Finset.mem_filter.mp hj).2, Ideal.top_pow]
      exact Ideal.one_eq_top.symm
    rw [hone, mul_one]
  -- the exponent on the total transform: `α` on the strict transforms, `N + e` on the exceptional
  let g : (F.totalTransform π Y).ι → Ideal ((structureSheaf 𝕜 E M').presheaf.stalk p) := fun k =>
    vanishingStalk (𝕜 := 𝕜) (E := E) ((F.totalTransform π Y).hyp k) p ^
      Sum.elim α (fun _ => N + e) (ofLex k)
  have hm : ∏ x ∈ s₀.map (F.inlTotalEmb π Y), g x = ∏ j ∈ s₀, g (F.inlTotalEmb π Y j) :=
    Finset.prod_map _ _ _
  by_cases hpY : π p ∈ Y
  · have hnotin : (toLex (Sum.inr PUnit.unit) : (F.totalTransform π Y).ι) ∉
        s₀.map (F.inlTotalEmb π Y) := fun hk => by
      obtain ⟨j, -, hj⟩ := Finset.mem_map.mp hk
      exact Sum.inl_ne_inr (toLex.injective hj)
    have hc : ∏ x ∈ Finset.cons (toLex (Sum.inr PUnit.unit) : (F.totalTransform π Y).ι)
        (s₀.map (F.inlTotalEmb π Y)) hnotin, g x =
        g (toLex (Sum.inr PUnit.unit)) * ∏ x ∈ s₀.map (F.inlTotalEmb π Y), g x :=
      Finset.prod_cons hnotin
    refine ⟨Finset.cons (toLex (Sum.inr PUnit.unit) : (F.totalTransform π Y).ι)
        (s₀.map (F.inlTotalEmb π Y)) hnotin,
      fun k => Sum.elim α (fun _ => N + e) (ofLex k), ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_cons.mp hk with hk | hk
      · subst hk
        exact hpY
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hk
        exact (Finset.mem_filter.mp hj).2
    · change _ = (∏ x ∈ Finset.cons (toLex (Sum.inr PUnit.unit) : (F.totalTransform π Y).ι)
        (s₀.map (F.inlTotalEmb π Y)) hnotin, g x) * R'.stalkIdeal p
      rw [hpull, hprod, hc, hm]
      change _ = vanishingStalk (𝕜 := 𝕜) (E := E) (π ⁻¹' Y) p ^ (N + e) *
        (∏ j ∈ s₀, vanishingStalk (𝕜 := 𝕜) (E := E)
          ((F.totalTransform π Y).hyp (toLex (Sum.inl j))) p ^ α j) * R'.stalkIdeal p
      ring
  · refine ⟨s₀.map (F.inlTotalEmb π Y), fun k => Sum.elim α (fun _ => N + e) (ofLex k), ?_, ?_⟩
    · intro k hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hk
      exact (Finset.mem_filter.mp hj).2
    · change _ = (∏ x ∈ s₀.map (F.inlTotalEmb π Y), g x) * R'.stalkIdeal p
      rw [hpull, hprod, hm]
      change vanishingStalk (𝕜 := 𝕜) (E := E) (π ⁻¹' Y) p ^ (N + e) *
        ((∏ j ∈ s₀, vanishingStalk (𝕜 := 𝕜) (E := E)
          ((F.totalTransform π Y).hyp (toLex (Sum.inl j))) p ^ α j) * R'.stalkIdeal p) =
        (∏ j ∈ s₀, vanishingStalk (𝕜 := 𝕜) (E := E)
          ((F.totalTransform π Y).hyp (toLex (Sum.inl j))) p ^ α j) * R'.stalkIdeal p
      rw [vanishingStalk_eq_top_of_notMem (h.isClosedSubmanifold_preimage hY).isClosed hpY,
        Ideal.top_pow, ← Ideal.one_eq_top, one_mul]

end Hironaka.Manifold
