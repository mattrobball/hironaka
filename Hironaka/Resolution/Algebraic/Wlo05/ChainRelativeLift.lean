/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
import Hironaka.Algebra.Local.Regular
import Hironaka.Resolution.Algebraic.Wlo05.ChainIdealColon
import Hironaka.Scheme.Snc.ParameterSubset
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Lifting chain-relative data across a hypersurface

The induction step of the statement CP1 of the embedded desingularization (the local form of the
ideal at the absorbing stage, `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) descends
one level of the maximal-contact chain: the run one dimension down, on the hypersurface `H = V(h)`,
knows the local form of the restricted ideal `J|_H` along `Γ̃ ⊆ H`, and the ideal `J` on the ambient
contains `h` (maximal contact persists for the round's ideal). At the ring level this is the step
`R/(h) → R`: given a regular system of parameters `w` of `R' = R/(h)` realising the boundary
members through the point, chain coordinates `w ∘ σ'` and exponent data on `R'` with
`Γ.map φ = (w ∘ σ')` and `J.map φ = M⁰ · chainIdeal (w ∘ σ') M`, one lifts `w` to `R` (units times
the members' own generators on the members' coordinates, arbitrary preimages elsewhere), prepends
`h`, and reads `Γ = (h) + (lifts)` and
`J = (h) + M⁰ · chainIdeal (lifts) M = chainIdeal (h, lifts) (M⁰, M)` (`chainIdeal_succ`): the top
monomial of the level becomes the level-`1` factor of the chain, and the new top monomial is `1`.
The lifted family is a regular system of parameters of `R` because it generates `𝔪_R` modulo
`ker φ = (h)` and has `dim R' + 1 = dim R` members
(`AlgebraicGeometry.natCast_sub_card_eq_ringKrullDim_of_ker`). The coordinates are those of
[Kol07, Definition 24]. The lift is used by `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainLift`.
-/

public section

universe u v

open Ideal IsLocalRing

namespace Hironaka.Resolution

variable {R : Type u} [CommRing R]

/-- A monomial in `Fin.cons x l` with exponent vector `Fin.cons 0 b` is the monomial in `l`. -/
theorem monomialOf_cons_zero {n : ℕ} (x : R) (l : Fin n → R) (b : Fin n → ℕ) :
    monomialOf (Fin.cons x l) (Fin.cons 0 b : Fin (n + 1) → ℕ) = monomialOf l b := by
  simp [monomialOf, Fin.prod_univ_succ]

/-- Monomials are compatible with ring homomorphisms. -/
theorem monomialOf_map {S : Type v} [CommRing S] (φ : R →+* S) {n : ℕ} (l : Fin n → R)
    (b : Fin n → ℕ) : φ (monomialOf l b) = monomialOf (φ ∘ l) b := by
  simp [monomialOf, map_prod φ]

/-- An ideal containing the kernel of a surjection is the preimage of its image. -/
theorem comap_map_eq_of_ker_le {S : Type v} [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) {K : Ideal R} (hK : RingHom.ker φ ≤ K) :
    (K.map φ).comap φ = K := by
  rw [Ideal.comap_map_of_surjective φ hφ, sup_eq_left]
  exact hK

/-- The ring core of the induction step of CP1: chain-relative data on `R' = R/(h)` lift to `R`
with the chain `(h, lifts)`, the level's top monomial becoming the first chain factor and the new
top monomial `1`. -/
theorem exists_chain_lift {R' : Type u} [IsRegularLocalRing R] [CommRing R']
    [IsRegularLocalRing R'] (φ : R →+* R') (hφ : Function.Surjective φ) {n : ℕ} {z : Fin n → R}
    (hz : IsRegularSystemOfParameters z) {j₀ : Fin n} (hker : RingHom.ker φ = span {z j₀})
    {ι : Type v} (e : ι → R) {n' : ℕ} (w : Fin n' → R') (hw : IsRegularSystemOfParameters w)
    (c' : ι → Fin n') (hc' : Function.Injective c') (hce : ∀ j, span {w (c' j)} = span {φ (e j)})
    {r : ℕ} (σ' : Fin (r + 1) → Fin n') (hσ' : Function.Injective σ') (hσc : ∀ i j, σ' i ≠ c' j)
    (a' : Fin (r + 1) → Fin n' → ℕ) (ha' : ∀ i k, a' i k ≠ 0 → k ∈ Set.range c')
    (b' : Fin n' → ℕ) (hb' : ∀ k, b' k ≠ 0 → k ∈ Set.range c')
    (J Γ : Ideal R) (hJh : z j₀ ∈ J) (hΓh : z j₀ ∈ Γ)
    (hΓ : Γ.map φ = span (Set.range (w ∘ σ')))
    (hJ : J.map φ = span {monomialOf w b'} * chainIdeal (w ∘ σ') fun i => monomialOf w (a' i)) :
    ∃ (zz : Fin (n' + 1) → R) (c : ι → Fin (n' + 1)) (σ : Fin (r + 2) → Fin (n' + 1))
      (a : Fin (r + 2) → Fin (n' + 1) → ℕ),
      IsRegularSystemOfParameters zz ∧ Function.Injective c ∧
        (∀ j, span {e j} = span {zz (c j)}) ∧ Function.Injective σ ∧ (∀ i j, σ i ≠ c j) ∧
        (∀ i k, a i k ≠ 0 → k ∈ Set.range c) ∧ Γ = span (Set.range (zz ∘ σ)) ∧
        J = chainIdeal (zz ∘ σ) fun i => monomialOf zz (a i) := by
  classical
  have : IsLocalHom φ := IsLocalHom.of_surjective φ hφ
  have hkerle : ∀ {K : Ideal R}, z j₀ ∈ K → RingHom.ker φ ≤ K := fun hK => by
    rw [hker, span_le, Set.singleton_subset_iff]
    exact hK
  -- the lifts of the level coordinates: units times the members' generators on the members'
  -- coordinates, arbitrary preimages elsewhere
  have hlift : ∀ k : Fin n', ∃ x : R, φ x = w k ∧ ∀ j, c' j = k → span {x} = span {e j} := by
    intro k
    by_cases hk : ∃ j, c' j = k
    · obtain ⟨j, rfl⟩ := hk
      obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp (hce j)
      -- `w (c' j) * u = φ (e j)`, so `w (c' j) = u⁻¹ * φ (e j)`
      obtain ⟨v, hv⟩ := hφ ((u⁻¹ : R'ˣ) : R')
      refine ⟨v * e j, ?_, fun j' hj' => ?_⟩
      · rw [map_mul, hv, ← hu, mul_comm (w (c' j)) (u : R'), ← mul_assoc, Units.inv_mul, one_mul]
      · have : j' = j := hc' hj'
        subst this
        have hvu : IsUnit v := (isUnit_map_iff φ v).mp (hv ▸ (u⁻¹).isUnit)
        exact Ideal.span_singleton_mul_left_unit hvu _
    · obtain ⟨x, hx⟩ := hφ (w k)
      exact ⟨x, hx, fun j hj => (hk ⟨j, hj⟩).elim⟩
  choose l hl using hlift
  have hφl : φ ∘ l = w := funext fun k => (hl k).1
  -- the lifted system of parameters
  set zz : Fin (n' + 1) → R := Fin.cons (z j₀) l with hzz_def
  have hmemR : ∀ x : R, x ∈ IsLocalRing.maximalIdeal R ↔ φ x ∈ IsLocalRing.maximalIdeal R' := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, isUnit_map_iff]
  have hzz : IsRegularSystemOfParameters zz := by
    refine ⟨le_antisymm ?_ ?_, ?_⟩
    · rw [span_le]
      rintro _ ⟨k, rfl⟩
      refine Fin.cases ?_ (fun k' => ?_) k
      · rw [hzz_def, Fin.cons_zero, ← hz.1]
        exact subset_span ⟨j₀, rfl⟩
      · rw [hzz_def, Fin.cons_succ, SetLike.mem_coe, hmemR, (hl k').1, ← hw.1]
        exact subset_span ⟨k', rfl⟩
    · intro x hx
      rw [hmemR, ← hw.1] at hx
      obtain ⟨d, hd⟩ := mem_span_range_iff_exists_fun.mp hx
      choose dl hdl using fun k => hφ (d k)
      have hmem : x - ∑ k, dl k * l k ∈ RingHom.ker φ := by
        rw [RingHom.mem_ker, map_sub, map_sum, sub_eq_zero]
        simp_rw [map_mul, hdl, (hl _).1]
        rw [← hd]
      rw [hker] at hmem
      have hsum : ∑ k, dl k * l k ∈ span (Set.range zz) := by
        refine sum_mem fun k _ => mul_mem_left _ _ (subset_span ⟨k.succ, ?_⟩)
        rw [hzz_def, Fin.cons_succ]
      have h0 : x - ∑ k, dl k * l k ∈ span (Set.range zz) := by
        refine span_mono ?_ hmem
        rw [Set.singleton_subset_iff]
        exact ⟨0, by rw [hzz_def, Fin.cons_zero]⟩
      simpa using add_mem h0 hsum
    · have hdim := AlgebraicGeometry.natCast_sub_card_eq_ringKrullDim_of_ker hz.1.symm hz.2 hφ
        (s := {j₀}) (by rw [hker, Finset.coe_singleton, Set.image_singleton])
      rw [Finset.card_singleton, ← hw.2] at hdim
      have hn : n - 1 = n' := by exact_mod_cast hdim
      have hn' : n' + 1 = n := by
        have := j₀.pos
        omega
      rw [← hz.2, ← hn']
  set σσ : Fin (r + 2) → Fin (n' + 1) := Fin.cons 0 (fun i => (σ' i).succ) with hσσ
  set aa : Fin (r + 2) → Fin (n' + 1) → ℕ := Fin.cons (Fin.cons 0 b') (fun i => Fin.cons 0 (a' i))
    with haa
  have hcomp : zz ∘ σσ = Fin.cons (z j₀) (l ∘ σ') := by
    funext i
    refine Fin.cases ?_ (fun i' => ?_) i
    · rw [Function.comp_apply, hσσ, Fin.cons_zero, hzz_def, Fin.cons_zero, Fin.cons_zero]
    · rw [Function.comp_apply, hσσ, Fin.cons_succ, hzz_def, Fin.cons_succ, Fin.cons_succ]
      rfl
  have hφlσ : φ ∘ (l ∘ σ') = w ∘ σ' := by rw [← Function.comp_assoc, hφl]
  have hφM : φ ∘ (fun i => monomialOf l (a' i)) = fun i => monomialOf w (a' i) :=
    funext fun i => by rw [Function.comp_apply, monomialOf_map, hφl]
  refine ⟨zz, fun j => (c' j).succ, σσ, aa, hzz, fun j j' h => hc' (Fin.succ_injective _ h),
    fun j => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hzz_def, Fin.cons_succ]
    exact ((hl (c' j)).2 j rfl).symm
  · rw [hσσ, Fin.cons_injective_iff]
    refine ⟨?_, fun i i' h => hσ' (Fin.succ_injective _ h)⟩
    rintro ⟨i, hi⟩
    exact Fin.succ_ne_zero _ hi
  · intro i j
    refine Fin.cases ?_ (fun i' => ?_) i
    · rw [hσσ, Fin.cons_zero]
      exact (Fin.succ_ne_zero _).symm
    · rw [hσσ, Fin.cons_succ]
      exact fun h => hσc i' j (Fin.succ_injective _ h)
  · intro i k
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun k' => ?_) k <;> intro hik
    · simp [haa] at hik
    · rw [haa, Fin.cons_zero, Fin.cons_succ] at hik
      obtain ⟨j, hj⟩ := hb' k' hik
      exact ⟨j, by simp [hj]⟩
    · simp [haa] at hik
    · rw [haa, Fin.cons_succ, Fin.cons_succ] at hik
      obtain ⟨j, hj⟩ := ha' i' k' hik
      exact ⟨j, by simp [hj]⟩
  · -- `Γ = (h) + (lifts)`
    have h1 : span (Set.range (w ∘ σ')) = (span (Set.range (l ∘ σ'))).map φ := by
      rw [map_span, ← Set.range_comp, hφlσ]
    rw [hcomp, Fin.range_cons, span_insert, ← comap_map_eq_of_ker_le φ hφ (hkerle hΓh), hΓ, h1,
      Ideal.comap_map_of_surjective φ hφ, ← RingHom.ker_eq_comap_bot, hker, sup_comm]
  · -- `J = chainIdeal (h, lifts) (M⁰, M)`
    have hM : (fun i : Fin (r + 2) => monomialOf zz (aa i)) =
        Fin.cons (monomialOf l b') (fun i => monomialOf l (a' i)) := by
      funext i
      refine Fin.cases ?_ (fun i' => ?_) i
      · rw [haa, Fin.cons_zero, Fin.cons_zero, hzz_def, monomialOf_cons_zero]
      · rw [haa, Fin.cons_succ, Fin.cons_succ, hzz_def, monomialOf_cons_zero]
    have hmapJ : (span {monomialOf l b'} * chainIdeal (l ∘ σ') fun i => monomialOf l (a' i)).map φ
        = span {monomialOf w b'} * chainIdeal (w ∘ σ') fun i => monomialOf w (a' i) := by
      rw [Ideal.map_mul, map_span, Set.image_singleton, monomialOf_map, hφl, ← chainIdeal_comp,
        hφlσ, hφM]
    rw [hcomp, hM, chainIdeal_succ, Fin.cons_zero, Fin.cons_zero, Fin.tail_cons, Fin.tail_cons,
      ← comap_map_eq_of_ker_le φ hφ (hkerle hJh), hJ, ← hmapJ, Ideal.comap_map_of_surjective φ hφ,
      ← RingHom.ker_eq_comap_bot, hker, sup_comm]

end Hironaka.Resolution
