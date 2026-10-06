/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Algebra
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainLift
import Hironaka.Scheme.Snc.ParameterSubset
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP3: re-basing the flag and transferring the strata

The second ring-level part of the statement CP3 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`): re-basing the flag of a K-shape or an
un-isolated form to an element `x` of the ideal of order `1` whose hypersurface has simple normal
crossings with the members — the hypersurface of maximal contact chosen in Step 2.2 of the proof of
[Kol07, Theorem 103] — by replacing a flag member of the block of trivial monomials by `x`, the
ideal and the exponents unchanged (`exists_update_chainKIdeal_eq`, `exists_update_chainIdeal_eq`);
and the transfer of admissible, terminal-normal and absorbing strata from the re-based coordinate
system back to the given one (`stratumIn_of_stratumIn_update_chainKIdeal`,
`stratumIn_of_stratumIn_update_chainIdeal`, `terminalIn_of_terminalIn_update`). The mechanism is
the coefficient argument: writing `x = ∑ c_i g_i` over the generators, outside `(z_C) + 𝔪²` some
coefficient in the trivial block is a unit (`exists_unit_coeff_of_notMem`), and conversely a unit
coefficient is what the regularity of the updated system forces (`isUnit_coeff_of_update_rsp`).
Not in the literature; used by `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Chain`.
-/

@[expose] public section

universe u

open IsLocalRing

namespace Hironaka.Resolution

section Rebase

variable {R : Type*} [CommRing R]

/-- A coordinate of a regular system lies outside the
span of the others plus `𝔪²`. -/
theorem notMem_span_compl_sup_sq [IsRegularLocalRing R] {n : ℕ} {w : Fin n → R}
    (hw : IsRegularSystemOfParameters w) (j : Fin n) :
    w j ∉ Ideal.span (w '' {k | k ≠ j}) ⊔ IsLocalRing.maximalIdeal R ^ 2 := by
  classical
  intro hmem
  set s : Finset (Fin n) := Finset.univ.erase j with hs
  have hI : Ideal.span (w '' {k | k ≠ j}) = Ideal.span (w '' ↑s) := by
    congr 2
    ext k
    simp [hs]
  rw [hI] at hmem
  have : IsRegularLocalRing (R ⧸ Ideal.span (w '' ↑s)) :=
    AlgebraicGeometry.isRegularLocalRing_quotient_span_image_finset hw.1.symm hw.2 s
  have hnot := AlgebraicGeometry.apply_notMem_maximalIdeal_sq
    (φ := Ideal.Quotient.mk (Ideal.span (w '' ↑s))) hw.1.symm hw.2 Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]) (Finset.notMem_erase j _)
  apply hnot
  rw [← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, ← Ideal.map_pow]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  rw [← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
  exact Ideal.mem_map_of_mem _ hb

/-- A monomial not involving `z k₀` is unchanged when
`z k₀` is replaced. -/
theorem monomialOf_update_of_apply_eq_zero {n : ℕ} (z : Fin n → R) (k₀ : Fin n) (x : R)
    (a : Fin n → ℕ) (ha : a k₀ = 0) : monomialOf (Function.update z k₀ x) a = monomialOf z a := by
  unfold monomialOf
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : k = k₀
  · subst hk
    simp [ha]
  · rw [Function.update_of_ne hk]

/-- A monomial with a positive exponent at `k` lies
in `(z k)`. -/
theorem monomialOf_mem_span_singleton {n : ℕ} (z : Fin n → R) (a : Fin n → ℕ) {k : Fin n}
    (hk : a k ≠ 0) : monomialOf z a ∈ Ideal.span {z k} := by
  unfold monomialOf
  rw [Ideal.mem_span_singleton]
  exact (dvd_pow_self (z k) hk).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))

/-- The core of the re-basing: for generators `g`
agreeing with coordinates on a block `P` and lying in `(z_C)` off it, an element `∑ c i • g i`
outside `(z_C) + 𝔪²` has a unit coefficient in the block. -/
theorem exists_unit_coeff_of_notMem [IsLocalRing R] {ι : Type*} [Fintype ι] {n : ℕ}
    {z : Fin n → R} (hzm : ∀ k, z k ∈ IsLocalRing.maximalIdeal R) (C : Set (Fin n))
    (f : ι → Fin n) (g : ι → R) (P : ι → Prop) (hg1 : ∀ i, P i → g i = z (f i))
    (hg2 : ∀ i, ¬ P i → g i ∈ Ideal.span (z '' C)) (c : ι → R) {x : R}
    (hc : ∑ i, c i • g i = x)
    (hx2 : x ∉ Ideal.span (z '' C) ⊔ IsLocalRing.maximalIdeal R ^ 2) :
    ∃ i, P i ∧ IsUnit (c i) := by
  classical
  by_contra hcon
  have hall : ∀ i, P i → c i ∈ IsLocalRing.maximalIdeal R := fun i hi => by
    by_contra hu
    exact hcon ⟨i, hi, IsLocalRing.notMem_maximalIdeal.mp hu⟩
  apply hx2
  rw [← hc]
  refine Ideal.sum_mem _ fun i _ => ?_
  by_cases hi : P i
  · rw [smul_eq_mul, hg1 i hi, pow_two]
    exact Ideal.mem_sup_right (Ideal.mul_mem_mul (hall i hi) (hzm (f i)))
  · exact Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (hg2 i hi))

/-- Replacing the coordinate `z j` by an element `x =
∑ c i • g i` with `g t = z j`, `c t` a unit and the other `g i` in the span of the other coordinates
gives a regular system of parameters. -/
theorem isRegularSystemOfParameters_update_of_unit [IsRegularLocalRing R] {n : ℕ}
    {z : Fin n → R} (hz : IsRegularSystemOfParameters z) (j : Fin n) {x : R}
    (hxm : x ∈ IsLocalRing.maximalIdeal R) {ι : Type*} [Fintype ι] (g c : ι → R)
    (t : ι) (hc : ∑ i, c i • g i = x) (hgt : g t = z j) (hu : IsUnit (c t))
    (hg : ∀ i, i ≠ t → g i ∈ Ideal.span (z '' {k | k ≠ j})) :
    IsRegularSystemOfParameters (Function.update z j x) := by
  classical
  refine ⟨?_, hz.2⟩
  have hsub : Ideal.span (z '' {k | k ≠ j}) ≤ Ideal.span (Set.range (Function.update z j x)) := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k ≠ j := hk
    exact Ideal.subset_span ⟨k, Function.update_of_ne hk' _ _⟩
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self]
      exact hxm
    · rw [Function.update_of_ne hk]
      exact x_mem_maximalIdeal_of_span_eq z hz.1.symm k
  · rw [← hz.1]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    by_cases hk : k = j
    · subst hk
      have hx' : x ∈ Ideal.span (Set.range (Function.update z k x)) :=
        Ideal.subset_span ⟨k, Function.update_self k x z⟩
      have hrest : ∑ i ∈ Finset.univ.erase t, c i • g i ∈
          Ideal.span (Set.range (Function.update z k x)) :=
        Ideal.sum_mem _ fun i hi =>
          Ideal.mul_mem_left _ _ (hsub (hg i (Finset.ne_of_mem_erase hi)))
      have hdec : c t * z k = x - ∑ i ∈ Finset.univ.erase t, c i • g i := by
        rw [← hc, ← Finset.add_sum_erase _ _ (Finset.mem_univ t), smul_eq_mul, hgt]
        ring
      obtain ⟨u, hu⟩ := hu
      have : z k = ↑u⁻¹ * (c t * z k) := by
        rw [← mul_assoc, ← hu, Units.inv_mul, one_mul]
      rw [this, hdec]
      exact Ideal.mul_mem_left _ _ (Ideal.sub_mem _ hx' hrest)
    · exact Ideal.subset_span ⟨k, Function.update_of_ne hk _ _⟩

/-- The span of the generators is unchanged when a
generator with a unit coefficient in `x = ∑ c i • g i` is replaced by `x`. -/
theorem span_range_update_eq_of_unit {ι : Type*} [Fintype ι] [DecidableEq ι] (g c : ι → R)
    (t : ι) {x : R} (hc : ∑ i, c i • g i = x) (hu : IsUnit (c t)) :
    Ideal.span (Set.range (Function.update g t x)) = Ideal.span (Set.range g) := by
  have hx : x ∈ Ideal.span (Set.range g) := by
    rw [← hc]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = t
    · subst hi
      rw [Function.update_self]
      exact hx
    · rw [Function.update_of_ne hi]
      exact Ideal.subset_span ⟨i, rfl⟩
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = t
    · subst hi
      have hx' : x ∈ Ideal.span (Set.range (Function.update g i x)) :=
        Ideal.subset_span ⟨i, Function.update_self i x g⟩
      have hrest : ∑ i' ∈ Finset.univ.erase i, c i' • g i' ∈
          Ideal.span (Set.range (Function.update g i x)) :=
        Ideal.sum_mem _ fun i' hi' => Ideal.mul_mem_left _ _
          (Ideal.subset_span ⟨i', Function.update_of_ne (Finset.ne_of_mem_erase hi') _ _⟩)
      have hdec : c i * g i = x - ∑ i' ∈ Finset.univ.erase i, c i' • g i' := by
        rw [← hc, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), smul_eq_mul]
        ring
      obtain ⟨u, hu⟩ := hu
      have : g i = ↑u⁻¹ * (c i * g i) := by
        rw [← mul_assoc, ← hu, Units.inv_mul, one_mul]
      rw [this, hdec]
      exact Ideal.mul_mem_left _ _ (Ideal.sub_mem _ hx' hrest)
    · exact Ideal.subset_span ⟨i, Function.update_of_ne hi _ _⟩

/-- The unit coefficient from the regularity of the
updated system: if `update z j x` is a regular system, `x = ∑ c i • g i` with `g t = z j` and the
other `g i` in the span of the other coordinates, then `c t` is a unit. -/
theorem isUnit_coeff_of_update_rsp [IsRegularLocalRing R] {n : ℕ} {z : Fin n → R}
    (hz : IsRegularSystemOfParameters z) (j : Fin n) {x : R}
    (hupd : IsRegularSystemOfParameters (Function.update z j x)) {ι : Type*} [Fintype ι]
    (g c : ι → R) (t : ι) (hc : ∑ i, c i • g i = x) (hgt : g t = z j)
    (hg : ∀ i, i ≠ t → g i ∈ Ideal.span (z '' {k | k ≠ j})) : IsUnit (c t) := by
  classical
  by_contra hu
  have hct : c t ∈ IsLocalRing.maximalIdeal R := by
    by_contra h
    exact hu (IsLocalRing.notMem_maximalIdeal.mp h)
  have hnot := notMem_span_compl_sup_sq hupd j
  rw [Function.update_self] at hnot
  have himg : Function.update z j x '' {k | k ≠ j} = z '' {k | k ≠ j} :=
    Set.image_congr fun k hk => Function.update_of_ne hk _ _
  rw [himg] at hnot
  apply hnot
  rw [← hc, ← Finset.add_sum_erase _ _ (Finset.mem_univ t), smul_eq_mul, hgt, add_comm]
  refine Submodule.add_mem_sup ?_ ?_
  · exact Ideal.sum_mem _ fun i hi =>
      Ideal.mul_mem_left _ _ (hg i (Finset.ne_of_mem_erase hi))
  · rw [pow_two]
    exact Ideal.mul_mem_mul hct (x_mem_maximalIdeal_of_span_eq z hz.1.symm j)

/-- The generators of the K-shape. -/
def kGen {n : ℕ} (z : Fin n → R) {r : ℕ} (σ : Fin (r + 1) → Fin n) (a : Fin (r + 1) → Fin n → ℕ)
    (i : Fin (r + 1)) : R :=
  (∏ i' ∈ Finset.univ.filter (fun i' : Fin (r + 1) => i' < i), monomialOf z (a i')) *
    Function.update (z ∘ σ) (Fin.last r) 1 i

/-- The K-shape is the span of its generators. -/
theorem chainKIdeal_eq_span_range_kGen {n : ℕ} (z : Fin n → R) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (a : Fin (r + 1) → Fin n → ℕ) :
    chainKIdeal (z ∘ σ) (fun i => monomialOf z (a i)) = Ideal.span (Set.range (kGen z σ a)) := rfl

/-- The generators of the un-isolated form. -/
def iGen {n : ℕ} (z : Fin n → R) {r : ℕ} (σ : Fin (r + 1) → Fin n) (a : Fin (r + 1) → Fin n → ℕ)
    (i : Fin (r + 1)) : R :=
  (∏ i' ∈ Finset.univ.filter (fun i' : Fin (r + 1) => i' < i), monomialOf z (a i')) * z (σ i)

/-- The un-isolated form is the span of its
generators. -/
theorem chainIdeal_eq_span_range_iGen {n : ℕ} (z : Fin n → R) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (a : Fin (r + 1) → Fin n → ℕ) :
    chainIdeal (z ∘ σ) (fun i => monomialOf z (a i)) = Ideal.span (Set.range (iGen z σ a)) := rfl

/-- Below the first level carrying a nontrivial monomial the K-generator is the chain coordinate. -/
theorem kGen_eq_of_le {n : ℕ} (z : Fin n → R) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (a : Fin (r + 1) → Fin n → ℕ) {t₀ : ℕ} (ht₀ : t₀ < r)
    (hmin : ∀ i : Fin (r + 1), i.val < t₀ → a i = 0) {i : Fin (r + 1)} (hi : i.val ≤ t₀) :
    kGen z σ a i = z (σ i) := by
  have hne : i ≠ Fin.last r := by
    intro h
    rw [h, Fin.val_last] at hi
    omega
  unfold kGen
  rw [Function.update_of_ne hne, Function.comp_apply, Finset.prod_eq_one, one_mul]
  intro i' hi'
  have := (Finset.mem_filter.mp hi').2
  rw [Fin.lt_def] at this
  rw [hmin i' (by omega), monomialOf_zero]

/-- Below the first nontrivial level the generator of
the un-isolated form is the chain coordinate. -/
theorem iGen_eq_of_le {n : ℕ} (z : Fin n → R) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (a : Fin (r + 1) → Fin n → ℕ) {t₀ : ℕ} (hmin : ∀ i : Fin (r + 1), i.val < t₀ → a i = 0)
    {i : Fin (r + 1)} (hi : i.val ≤ t₀) : iGen z σ a i = z (σ i) := by
  unfold iGen
  rw [Finset.prod_eq_one, one_mul]
  intro i' hi'
  have := (Finset.mem_filter.mp hi').2
  rw [Fin.lt_def] at this
  rw [hmin i' (by omega), monomialOf_zero]

/-- Beyond a level whose monomial is nontrivial the
generators lie in `(z_C)`. -/
theorem prod_mem_span_of_lt {n : ℕ} (z : Fin n → R) {r : ℕ} (a : Fin (r + 1) → Fin n → ℕ)
    (C : Set (Fin n)) (ha : ∀ i k, a i k ≠ 0 → k ∈ C) {t₀ : Fin (r + 1)} (ha₀ : a t₀ ≠ 0)
    {i : Fin (r + 1)} (hi : t₀ < i) :
    (∏ i' ∈ Finset.univ.filter (fun i' : Fin (r + 1) => i' < i), monomialOf z (a i')) ∈
      Ideal.span (z '' C) := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp ha₀
  have hsub : ({z k} : Set R) ⊆ z '' C := Set.singleton_subset_iff.mpr ⟨k, ha _ k hk, rfl⟩
  have hM : monomialOf z (a t₀) ∈ Ideal.span (z '' C) :=
    Ideal.span_mono hsub (monomialOf_mem_span_singleton z _ hk)
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun i' => monomialOf z (a i'))
    (s := Finset.univ.filter (fun i' : Fin (r + 1) => i' < i))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ t₀, hi⟩)
  rw [hq]
  exact Ideal.mul_mem_right _ _ hM

/-- Beyond a nontrivial level the K-generators lie in
`(z_C)`. -/
theorem kGen_mem_span_of_lt {n : ℕ} (z : Fin n → R) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (a : Fin (r + 1) → Fin n → ℕ) (C : Set (Fin n)) (ha : ∀ i k, a i k ≠ 0 → k ∈ C)
    {t₀ : Fin (r + 1)} (ha₀ : a t₀ ≠ 0) {i : Fin (r + 1)} (hi : t₀ < i) :
    kGen z σ a i ∈ Ideal.span (z '' C) :=
  Ideal.mul_mem_right _ _ (prod_mem_span_of_lt z a C ha ha₀ hi)

/-- Beyond a nontrivial level the generators of the
un-isolated form lie in `(z_C)`. -/
theorem iGen_mem_span_of_lt {n : ℕ} (z : Fin n → R) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (a : Fin (r + 1) → Fin n → ℕ) (C : Set (Fin n)) (ha : ∀ i k, a i k ≠ 0 → k ∈ C)
    {t₀ : Fin (r + 1)} (ha₀ : a t₀ ≠ 0) {i : Fin (r + 1)} (hi : t₀ < i) :
    iGen z σ a i ∈ Ideal.span (z '' C) :=
  Ideal.mul_mem_right _ _ (prod_mem_span_of_lt z a C ha ha₀ hi)

/-- Re-basing the flag to an element `x ∈ K` of order
`1` whose hypersurface has snc with the members. -/
theorem exists_update_chainKIdeal_eq [IsRegularLocalRing R] {n : ℕ}
    {z : Fin n → R} (hz : IsRegularSystemOfParameters z) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (hσ : Function.Injective σ) (C : Set (Fin n)) (hCσ : ∀ k ∈ C, k ∉ Set.range σ)
    (a : Fin (r + 1) → Fin n → ℕ) (ha : ∀ i k, a i k ≠ 0 → k ∈ C)
    (hne : ∃ i : Fin (r + 1), i.val < r ∧ a i ≠ 0) {x : R}
    (hx : x ∈ chainKIdeal (z ∘ σ) (fun i => monomialOf z (a i)))
    (hx2 : x ∉ Ideal.span (z '' C) ⊔ IsLocalRing.maximalIdeal R ^ 2) :
    ∃ t : Fin (r + 1), t.val < r ∧ (∀ i : Fin (r + 1), i.val < t.val → a i = 0) ∧
      IsRegularSystemOfParameters (Function.update z (σ t) x) ∧
      chainKIdeal (z ∘ σ) (fun i => monomialOf z (a i)) =
        chainKIdeal (Function.update z (σ t) x ∘ σ)
          (fun i => monomialOf (Function.update z (σ t) x) (a i)) := by
  classical
  have hex : ∃ m : ℕ, ∃ _ : m < r, a ⟨m, by omega⟩ ≠ 0 := by
    obtain ⟨i, hi, hai⟩ := hne
    exact ⟨i.val, hi, by simpa using hai⟩
  set t₀ := Nat.find hex with ht₀def
  have ht₀ : t₀ < r := (Nat.find_spec hex).1
  have ha₀ : a ⟨t₀, by omega⟩ ≠ 0 := (Nat.find_spec hex).2
  have hmin : ∀ i : Fin (r + 1), i.val < t₀ → a i = 0 := by
    intro i hi
    by_contra h
    exact Nat.find_min hex hi ⟨by omega, by simpa using h⟩
  have hzm : ∀ k, z k ∈ IsLocalRing.maximalIdeal R := fun k =>
    x_mem_maximalIdeal_of_span_eq z hz.1.symm k
  rw [chainKIdeal_eq_span_range_kGen] at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hx
  have hgen1 : ∀ i : Fin (r + 1), i.val ≤ t₀ → kGen z σ a i = z (σ i) :=
    fun i hi => kGen_eq_of_le z σ a ht₀ hmin hi
  have hgen2 : ∀ i : Fin (r + 1), ¬ i.val ≤ t₀ → kGen z σ a i ∈ Ideal.span (z '' C) :=
    fun i hi => kGen_mem_span_of_lt z σ a C ha ha₀ (Fin.lt_def.mpr (not_le.mp hi))
  obtain ⟨t, ht, hu⟩ := exists_unit_coeff_of_notMem hzm C σ (kGen z σ a) (fun i => i.val ≤ t₀)
    hgen1 hgen2 c hc hx2
  have hspanC : Ideal.span (z '' C) ≤ IsLocalRing.maximalIdeal R :=
    Ideal.span_le.mpr (by rintro _ ⟨k, -, rfl⟩; exact hzm k)
  have hxm : x ∈ IsLocalRing.maximalIdeal R := by
    rw [← hc]
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ?_
    by_cases hi : i.val ≤ t₀
    · rw [hgen1 i hi]
      exact hzm _
    · exact hspanC (hgen2 i hi)
  have hgoth : ∀ i, i ≠ t → kGen z σ a i ∈ Ideal.span (z '' {k | k ≠ σ t}) := by
    intro i hi
    by_cases hib : i.val ≤ t₀
    · rw [hgen1 i hib]
      exact Ideal.subset_span ⟨σ i, fun h => hi (hσ h), rfl⟩
    · refine Ideal.span_mono ?_ (hgen2 i hib)
      rintro _ ⟨k, hkC, rfl⟩
      exact ⟨k, fun h => hCσ k hkC ⟨t, h.symm⟩, rfl⟩
  have htl : t ≠ Fin.last r := by
    intro h
    rw [h, Fin.val_last] at ht
    omega
  refine ⟨t, by omega, fun i hi => hmin i (by omega), ?_, ?_⟩
  · exact isRegularSystemOfParameters_update_of_unit hz (σ t) hxm (kGen z σ a) c t hc
      (hgen1 t ht) hu hgoth
  · have hcomp : Function.update z (σ t) x ∘ σ = Function.update (z ∘ σ) t x :=
      Function.update_comp_eq_of_injective z hσ t x
    have hM : ∀ i, monomialOf (Function.update z (σ t) x) (a i) = monomialOf z (a i) := fun i =>
      monomialOf_update_of_apply_eq_zero z (σ t) x (a i) (by
        by_contra h
        exact hCσ _ (ha i _ h) ⟨t, rfl⟩)
    have hgen : chainKIdeal (Function.update (z ∘ σ) t x) (fun i => monomialOf z (a i)) =
        Ideal.span (Set.range (Function.update (kGen z σ a) t x)) := by
      unfold chainKIdeal chainIdeal
      refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
      by_cases hi : i = t
      · subst hi
        rw [Function.update_self, Function.update_comm htl, Function.update_self,
          Finset.prod_eq_one, one_mul]
        intro i' hi'
        have := (Finset.mem_filter.mp hi').2
        rw [Fin.lt_def] at this
        rw [hmin i' (by omega), monomialOf_zero]
      · rw [Function.update_of_ne hi]
        unfold kGen
        congr 1
        by_cases hil : i = Fin.last r
        · subst hil
          rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hil, Function.update_of_ne hil, Function.update_of_ne hi]
    simp_rw [hcomp, hM]
    rw [hgen, span_range_update_eq_of_unit (kGen z σ a) c t hc hu,
      chainKIdeal_eq_span_range_kGen]

/-- A chain product beyond a level with a nontrivial
exponent at `k` lies in `(z k)`. -/
theorem prod_mem_span_singleton_of_lt {n : ℕ} (z : Fin n → R) {r : ℕ}
    (a : Fin (r + 1) → Fin n → ℕ) {t₀ : Fin (r + 1)} {k : Fin n} (hak : a t₀ k ≠ 0)
    {i : Fin (r + 1)} (hi : t₀ < i) :
    (∏ i' ∈ Finset.univ.filter (fun i' : Fin (r + 1) => i' < i), monomialOf z (a i')) ∈
      Ideal.span {z k} := by
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun i' => monomialOf z (a i'))
    (s := Finset.univ.filter (fun i' : Fin (r + 1) => i' < i))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ t₀, hi⟩)
  rw [hq]
  exact Ideal.mul_mem_right _ _ (monomialOf_mem_span_singleton z _ hak)

/-- Re-basing for the un-isolated form (`t ≤ r`; `t =
r` is the normal parameter). -/
theorem exists_update_chainIdeal_eq [IsRegularLocalRing R] {n : ℕ}
    {z : Fin n → R} (hz : IsRegularSystemOfParameters z) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (hσ : Function.Injective σ) (C : Set (Fin n)) (hCσ : ∀ k ∈ C, k ∉ Set.range σ)
    (a : Fin (r + 1) → Fin n → ℕ) (ha : ∀ i k, a i k ≠ 0 → k ∈ C) {x : R}
    (hx : x ∈ chainIdeal (z ∘ σ) (fun i => monomialOf z (a i)))
    (hx2 : x ∉ Ideal.span (z '' C) ⊔ IsLocalRing.maximalIdeal R ^ 2) :
    ∃ t : Fin (r + 1), (∀ i : Fin (r + 1), i.val < t.val → a i = 0) ∧
      IsRegularSystemOfParameters (Function.update z (σ t) x) ∧
      chainIdeal (z ∘ σ) (fun i => monomialOf z (a i)) =
        chainIdeal (Function.update z (σ t) x ∘ σ)
          (fun i => monomialOf (Function.update z (σ t) x) (a i)) := by
  classical
  have hzm : ∀ k, z k ∈ IsLocalRing.maximalIdeal R := fun k =>
    x_mem_maximalIdeal_of_span_eq z hz.1.symm k
  rw [chainIdeal_eq_span_range_iGen] at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hx
  -- the block bound `B`: the first nontrivial level, or `r + 1` if none
  obtain ⟨B, hmin, hgen2⟩ : ∃ B : ℕ, (∀ i : Fin (r + 1), i.val < B → a i = 0) ∧
      ∀ i : Fin (r + 1), ¬ i.val ≤ B → iGen z σ a i ∈ Ideal.span (z '' C) := by
    by_cases hex : ∃ m : ℕ, ∃ _ : m < r + 1, a ⟨m, by omega⟩ ≠ 0
    · refine ⟨Nat.find hex, fun i hi => ?_, fun i hi => ?_⟩
      · by_contra h
        exact Nat.find_min hex hi ⟨i.isLt, by simpa using h⟩
      · exact iGen_mem_span_of_lt z σ a C ha (Nat.find_spec hex).2
          (Fin.lt_def.mpr (not_le.mp hi))
    · refine ⟨r + 1, fun i _ => ?_, fun i hi => (hi i.isLt.le).elim⟩
      by_contra h
      exact hex ⟨i.val, i.isLt, by simpa using h⟩
  have hgen1 : ∀ i : Fin (r + 1), i.val ≤ B → iGen z σ a i = z (σ i) :=
    fun i hi => iGen_eq_of_le z σ a hmin hi
  obtain ⟨t, ht, hu⟩ := exists_unit_coeff_of_notMem hzm C σ (iGen z σ a) (fun i => i.val ≤ B)
    hgen1 hgen2 c hc hx2
  have hspanC : Ideal.span (z '' C) ≤ IsLocalRing.maximalIdeal R :=
    Ideal.span_le.mpr (by rintro _ ⟨k, -, rfl⟩; exact hzm k)
  have hxm : x ∈ IsLocalRing.maximalIdeal R := by
    rw [← hc]
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ?_
    by_cases hi : i.val ≤ B
    · rw [hgen1 i hi]
      exact hzm _
    · exact hspanC (hgen2 i hi)
  have hgoth : ∀ i, i ≠ t → iGen z σ a i ∈ Ideal.span (z '' {k | k ≠ σ t}) := fun i hi =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨σ i, fun h => hi (hσ h), rfl⟩)
  refine ⟨t, fun i hi => hmin i (by omega), ?_, ?_⟩
  · exact isRegularSystemOfParameters_update_of_unit hz (σ t) hxm (iGen z σ a) c t hc
      (hgen1 t ht) hu hgoth
  · have hcomp : Function.update z (σ t) x ∘ σ = Function.update (z ∘ σ) t x :=
      Function.update_comp_eq_of_injective z hσ t x
    have hM : ∀ i, monomialOf (Function.update z (σ t) x) (a i) = monomialOf z (a i) := fun i =>
      monomialOf_update_of_apply_eq_zero z (σ t) x (a i) (by
        by_contra h
        exact hCσ _ (ha i _ h) ⟨t, rfl⟩)
    have hgen : chainIdeal (Function.update (z ∘ σ) t x) (fun i => monomialOf z (a i)) =
        Ideal.span (Set.range (Function.update (iGen z σ a) t x)) := by
      unfold chainIdeal
      refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
      by_cases hi : i = t
      · subst hi
        rw [Function.update_self, Function.update_self, Finset.prod_eq_one, one_mul]
        intro i' hi'
        have := (Finset.mem_filter.mp hi').2
        rw [Fin.lt_def] at this
        rw [hmin i' (by omega), monomialOf_zero]
      · rw [Function.update_of_ne hi]
        unfold iGen
        simp only [Function.update_of_ne hi, Function.comp_apply]
    simp_rw [hcomp, hM]
    rw [hgen, span_range_update_eq_of_unit (iGen z σ a) c t hc hu,
      chainIdeal_eq_span_range_iGen]

/-- The absorption transfer: with `x` in the un-
isolated form and `update z (σ t) x` a regular system, the chain's span is unchanged. -/
theorem span_range_update_eq_of_mem_chainIdeal [IsRegularLocalRing R] {n : ℕ}
    {z : Fin n → R} (hz : IsRegularSystemOfParameters z) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (hσ : Function.Injective σ) (a : Fin (r + 1) → Fin n → ℕ) {x : R}
    (hx : x ∈ chainIdeal (z ∘ σ) (fun i => monomialOf z (a i))) (t : Fin (r + 1))
    (hupd : IsRegularSystemOfParameters (Function.update z (σ t) x)) :
    Ideal.span (Set.range (Function.update z (σ t) x ∘ σ)) = Ideal.span (Set.range (z ∘ σ)) := by
  classical
  rw [chainIdeal_eq_span_range_iGen] at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hx
  -- `x` has a unit coefficient on `f_t`: the generator at `t` is `(∏) f_t`, a multiple of `f_t`
  have hgoth : ∀ i, i ≠ t → iGen z σ a i ∈ Ideal.span (z '' {k | k ≠ σ t}) := fun i hi =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨σ i, fun h => hi (hσ h), rfl⟩)
  -- the coefficient of `f_t` in `x`: `c t * (∏ M)`, a unit times the block product
  set P := ∏ i' ∈ Finset.univ.filter (fun i' : Fin (r + 1) => i' < t), monomialOf z (a i')
    with hP
  have hgt : iGen z σ a t = P * z (σ t) := rfl
  -- reorganise: `x = (c t * P) • z (σ t) + ∑_{i ≠ t} c i • iGen i`
  set c' : Fin (r + 1) → R := Function.update c t (c t * P) with hc'
  set g' : Fin (r + 1) → R := Function.update (iGen z σ a) t (z (σ t)) with hg'
  have hc'' : ∑ i, c' i • g' i = x := by
    rw [← hc, ← Finset.add_sum_erase _ _ (Finset.mem_univ t),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
    congr 1
    · simp only [hc', hg', Function.update_self, smul_eq_mul, hgt]
      ring
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≠ t := Finset.ne_of_mem_erase hi
      simp only [hc', hg', Function.update_of_ne hi']
  have hu : IsUnit (c' t) :=
    isUnit_coeff_of_update_rsp hz (σ t) hupd g' c' t hc'' (by simp [hg'])
      (fun i hi => by rw [hg', Function.update_of_ne hi]; exact hgoth i hi)
  -- conclude: both spans contain each other's generators
  have hcomp : Function.update z (σ t) x ∘ σ = Function.update (z ∘ σ) t x :=
    Function.update_comp_eq_of_injective z hσ t x
  rw [hcomp]
  have hxspan : x ∈ Ideal.span (Set.range (z ∘ σ)) := by
    rw [← hc]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = t
    · subst hi
      rw [Function.update_self]
      exact hxspan
    · rw [Function.update_of_ne hi]
      exact Ideal.subset_span ⟨i, rfl⟩
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = t
    · subst hi
      have hx' : x ∈ Ideal.span (Set.range (Function.update (z ∘ σ) i x)) :=
        Ideal.subset_span ⟨i, Function.update_self i x (z ∘ σ)⟩
      have hrest : ∑ i' ∈ Finset.univ.erase i, c' i' • g' i' ∈
          Ideal.span (Set.range (Function.update (z ∘ σ) i x)) := by
        refine Ideal.sum_mem _ fun i' hi' => Ideal.mul_mem_left _ _ ?_
        have hne := Finset.ne_of_mem_erase hi'
        rw [hg', Function.update_of_ne hne]
        exact Ideal.mul_mem_left _ _
          (Ideal.subset_span ⟨i', by rw [Function.update_of_ne hne]; rfl⟩)
      have hdec : c' i * z (σ i) = x - ∑ i' ∈ Finset.univ.erase i, c' i' • g' i' := by
        rw [← hc'', ← Finset.add_sum_erase _ _ (Finset.mem_univ i), smul_eq_mul]
        simp only [hg', Function.update_self]
        ring
      obtain ⟨u, hu⟩ := hu
      have : (z ∘ σ) i = ↑u⁻¹ * (c' i * z (σ i)) := by
        rw [← mul_assoc, ← hu, Units.inv_mul, one_mul]
        rfl
      rw [this, hdec]
      exact Ideal.mul_mem_left _ _ (Ideal.sub_mem _ hx' hrest)
    · exact Ideal.subset_span ⟨i, Function.update_of_ne hi _ _⟩

/-- The transfer back from the re-based system,
K-shape: a stratum in the coordinates `update z (σ t) x` is a stratum in `z`. -/
theorem stratumIn_of_stratumIn_update_chainKIdeal [IsRegularLocalRing R] {n : ℕ}
    {z : Fin n → R} (hz : IsRegularSystemOfParameters z) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (hσ : Function.Injective σ) (C : Set (Fin n)) (hCσ : ∀ k ∈ C, k ∉ Set.range σ)
    (a : Fin (r + 1) → Fin n → ℕ) (b : Fin n → ℕ) {x : R}
    (hx : x ∈ chainKIdeal (z ∘ σ) (fun i => monomialOf z (a i))) (t : Fin (r + 1))
    (ht : ∀ i : Fin (r + 1), i.val < t.val → a i = 0)
    (hupd : IsRegularSystemOfParameters (Function.update z (σ t) x)) {Z : Ideal R}
    (h : StratumIn (Function.update z (σ t) x) C σ a b Z) : StratumIn z C σ a b Z := by
  classical
  obtain ⟨l, hl, s, hsC, hZ, hl0, hlpos⟩ := h
  refine ⟨l, hl, s, hsC, ?_, hl0, hlpos⟩
  have hs : Function.update z (σ t) x '' ↑s = z '' ↑s :=
    Set.image_congr fun k hk => Function.update_of_ne (fun h => hCσ k (hsC hk) ⟨t, h.symm⟩) _ _
  rw [hs] at hZ
  by_cases hlt : l ≤ t.val
  · have hf : (Function.update z (σ t) x ∘ σ) '' {i | i.val < l} = (z ∘ σ) '' {i | i.val < l} :=
      Set.image_congr fun i hi => by
        have hi' : i.val < l := hi
        have hne : σ i ≠ σ t := fun h => by
          have := hσ h
          subst this
          omega
        simp only [Function.comp_apply, Function.update_of_ne hne]
    rw [hf] at hZ
    exact hZ
  · have hlt' : t.val < l := not_le.mp hlt
    obtain ⟨k, hks, hak⟩ := hlpos (by omega)
    rw [chainKIdeal_eq_span_range_kGen] at hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hx
    have hgt : kGen z σ a t = z (σ t) := kGen_eq_of_le z σ a (t₀ := t.val) (by omega) ht le_rfl
    have hsub : ({z k} : Set R) ⊆ z '' ↑s := Set.singleton_subset_iff.mpr ⟨k, hks, rfl⟩
    have hge : ∀ i : Fin (r + 1), l ≤ i.val → kGen z σ a i ∈ Ideal.span (z '' ↑s) := fun i hi =>
      Ideal.mul_mem_right _ _ (Ideal.span_mono hsub
        (prod_mem_span_singleton_of_lt z a (t₀ := ⟨l - 1, by omega⟩) hak
          (Fin.lt_def.mpr (by simp only; omega))))
    have hgoth : ∀ i, i ≠ t → kGen z σ a i ∈ Ideal.span (z '' {k' | k' ≠ σ t}) := by
      intro i hi
      by_cases hil : i = Fin.last r
      · subst hil
        refine Ideal.span_mono ?_ (hge _ (by rw [Fin.val_last]; omega))
        rintro _ ⟨k', hk', rfl⟩
        exact ⟨k', fun h => hCσ k' (hsC hk') ⟨t, h.symm⟩, rfl⟩
      · unfold kGen
        rw [Function.update_of_ne hil, Function.comp_apply]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨σ i, fun h => hi (hσ h), rfl⟩)
    have hu : IsUnit (c t) :=
      isUnit_coeff_of_update_rsp hz (σ t) hupd (kGen z σ a) c t hc hgt hgoth
    set J := Ideal.span ((z ∘ σ) '' {i | i.val < l}) ⊔ Ideal.span (z '' ↑s) with hJ
    set J' := Ideal.span ((Function.update z (σ t) x ∘ σ) '' {i | i.val < l}) ⊔
      Ideal.span (z '' ↑s) with hJ'
    have hlt_mem : ∀ i : Fin (r + 1), i.val < l → kGen z σ a i ∈ J := fun i hi => by
      have hne : i ≠ Fin.last r := by
        intro h
        rw [h, Fin.val_last] at hi
        omega
      unfold kGen
      rw [Function.update_of_ne hne, Function.comp_apply]
      exact Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, hi, rfl⟩))
    have hlt_mem' : ∀ i : Fin (r + 1), i.val < l → i ≠ t → kGen z σ a i ∈ J' := fun i hi hit => by
      have hne : i ≠ Fin.last r := by
        intro h
        rw [h, Fin.val_last] at hi
        omega
      unfold kGen
      rw [Function.update_of_ne hne, Function.comp_apply]
      refine Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, hi, ?_⟩))
      simp only [Function.comp_apply, Function.update_of_ne (hσ.ne hit)]
    have hxJ : x ∈ J := by
      rw [← hc]
      refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ?_
      by_cases hi : i.val < l
      · exact hlt_mem i hi
      · exact Ideal.mem_sup_right (hge i (not_lt.mp hi))
    have hxJ' : x ∈ J' := Ideal.mem_sup_left (Ideal.subset_span ⟨t, hlt', by simp⟩)
    have hft : z (σ t) ∈ J' := by
      have hrest : ∑ i ∈ Finset.univ.erase t, c i • kGen z σ a i ∈ J' := by
        refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ ?_
        have hit := Finset.ne_of_mem_erase hi
        by_cases hil : i.val < l
        · exact hlt_mem' i hil hit
        · exact Ideal.mem_sup_right (hge i (not_lt.mp hil))
      have hdec : c t * z (σ t) = x - ∑ i ∈ Finset.univ.erase t, c i • kGen z σ a i := by
        rw [← hc, ← Finset.add_sum_erase _ _ (Finset.mem_univ t), smul_eq_mul, hgt]
        ring
      obtain ⟨u, hu⟩ := hu
      have : z (σ t) = ↑u⁻¹ * (c t * z (σ t)) := by
        rw [← mul_assoc, ← hu, Units.inv_mul, one_mul]
      rw [this, hdec]
      exact Ideal.mul_mem_left _ _ (Ideal.sub_mem _ hxJ' hrest)
    have hJJ : J' = J := by
      apply le_antisymm
      · refine sup_le ?_ le_sup_right
        refine Ideal.span_le.mpr ?_
        rintro _ ⟨i, hi, rfl⟩
        by_cases hit : i = t
        · subst hit
          simp only [Function.comp_apply, Function.update_self]
          exact hxJ
        · simp only [Function.comp_apply, Function.update_of_ne (hσ.ne hit)]
          exact Ideal.mem_sup_left (Ideal.subset_span ⟨i, hi, rfl⟩)
      · refine sup_le ?_ le_sup_right
        refine Ideal.span_le.mpr ?_
        rintro _ ⟨i, hi, rfl⟩
        by_cases hit : i = t
        · subst hit
          exact hft
        · exact Ideal.mem_sup_left
            (Ideal.subset_span ⟨i, hi, by simp [Function.update_of_ne (hσ.ne hit)]⟩)
    rw [hZ]
    exact hJJ

/-- The transfer for the un-isolated form. -/
theorem stratumIn_of_stratumIn_update_chainIdeal [IsRegularLocalRing R] {n : ℕ}
    {z : Fin n → R} (hz : IsRegularSystemOfParameters z) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (hσ : Function.Injective σ) (C : Set (Fin n)) (hCσ : ∀ k ∈ C, k ∉ Set.range σ)
    (a : Fin (r + 1) → Fin n → ℕ) (b : Fin n → ℕ) {x : R}
    (hx : x ∈ chainIdeal (z ∘ σ) (fun i => monomialOf z (a i))) (t : Fin (r + 1))
    (ht : ∀ i : Fin (r + 1), i.val < t.val → a i = 0)
    (hupd : IsRegularSystemOfParameters (Function.update z (σ t) x)) {Z : Ideal R}
    (h : StratumIn (Function.update z (σ t) x) C σ a b Z) : StratumIn z C σ a b Z := by
  classical
  obtain ⟨l, hl, s, hsC, hZ, hl0, hlpos⟩ := h
  refine ⟨l, hl, s, hsC, ?_, hl0, hlpos⟩
  have hs : Function.update z (σ t) x '' ↑s = z '' ↑s :=
    Set.image_congr fun k hk => Function.update_of_ne (fun h => hCσ k (hsC hk) ⟨t, h.symm⟩) _ _
  rw [hs] at hZ
  by_cases hlt : l ≤ t.val
  · have hf : (Function.update z (σ t) x ∘ σ) '' {i | i.val < l} = (z ∘ σ) '' {i | i.val < l} :=
      Set.image_congr fun i hi => by
        have hi' : i.val < l := hi
        have hne : σ i ≠ σ t := fun h => by
          have := hσ h
          subst this
          omega
        simp only [Function.comp_apply, Function.update_of_ne hne]
    rw [hf] at hZ
    exact hZ
  · have hlt' : t.val < l := not_le.mp hlt
    obtain ⟨k, hks, hak⟩ := hlpos (by omega)
    rw [chainIdeal_eq_span_range_iGen] at hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hx
    have hgt : iGen z σ a t = z (σ t) := iGen_eq_of_le z σ a (t₀ := t.val) ht le_rfl
    have hsub : ({z k} : Set R) ⊆ z '' ↑s := Set.singleton_subset_iff.mpr ⟨k, hks, rfl⟩
    have hge : ∀ i : Fin (r + 1), l ≤ i.val → iGen z σ a i ∈ Ideal.span (z '' ↑s) := fun i hi =>
      Ideal.mul_mem_right _ _ (Ideal.span_mono hsub
        (prod_mem_span_singleton_of_lt z a (t₀ := ⟨l - 1, by omega⟩) hak
          (Fin.lt_def.mpr (by simp only; omega))))
    have hgoth : ∀ i, i ≠ t → iGen z σ a i ∈ Ideal.span (z '' {k' | k' ≠ σ t}) := fun i hi =>
      Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨σ i, fun h => hi (hσ h), rfl⟩)
    have hu : IsUnit (c t) :=
      isUnit_coeff_of_update_rsp hz (σ t) hupd (iGen z σ a) c t hc hgt hgoth
    set J := Ideal.span ((z ∘ σ) '' {i | i.val < l}) ⊔ Ideal.span (z '' ↑s) with hJ
    set J' := Ideal.span ((Function.update z (σ t) x ∘ σ) '' {i | i.val < l}) ⊔
      Ideal.span (z '' ↑s) with hJ'
    have hlt_mem : ∀ i : Fin (r + 1), i.val < l → iGen z σ a i ∈ J := fun i hi =>
      Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, hi, rfl⟩))
    have hlt_mem' : ∀ i : Fin (r + 1), i.val < l → i ≠ t → iGen z σ a i ∈ J' := fun i hi hit => by
      refine Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, hi, ?_⟩))
      simp only [Function.comp_apply, Function.update_of_ne (hσ.ne hit)]
    have hxJ : x ∈ J := by
      rw [← hc]
      refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ?_
      by_cases hi : i.val < l
      · exact hlt_mem i hi
      · exact Ideal.mem_sup_right (hge i (not_lt.mp hi))
    have hxJ' : x ∈ J' := Ideal.mem_sup_left (Ideal.subset_span ⟨t, hlt', by simp⟩)
    have hft : z (σ t) ∈ J' := by
      have hrest : ∑ i ∈ Finset.univ.erase t, c i • iGen z σ a i ∈ J' := by
        refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ ?_
        have hit := Finset.ne_of_mem_erase hi
        by_cases hil : i.val < l
        · exact hlt_mem' i hil hit
        · exact Ideal.mem_sup_right (hge i (not_lt.mp hil))
      have hdec : c t * z (σ t) = x - ∑ i ∈ Finset.univ.erase t, c i • iGen z σ a i := by
        rw [← hc, ← Finset.add_sum_erase _ _ (Finset.mem_univ t), smul_eq_mul, hgt]
        ring
      obtain ⟨u, hu⟩ := hu
      have : z (σ t) = ↑u⁻¹ * (c t * z (σ t)) := by
        rw [← mul_assoc, ← hu, Units.inv_mul, one_mul]
      rw [this, hdec]
      exact Ideal.mul_mem_left _ _ (Ideal.sub_mem _ hxJ' hrest)
    have hJJ : J' = J := by
      apply le_antisymm
      · refine sup_le ?_ le_sup_right
        refine Ideal.span_le.mpr ?_
        rintro _ ⟨i, hi, rfl⟩
        by_cases hit : i = t
        · subst hit
          simp only [Function.comp_apply, Function.update_self]
          exact hxJ
        · simp only [Function.comp_apply, Function.update_of_ne (hσ.ne hit)]
          exact Ideal.mem_sup_left (Ideal.subset_span ⟨i, hi, rfl⟩)
      · refine sup_le ?_ le_sup_right
        refine Ideal.span_le.mpr ?_
        rintro _ ⟨i, hi, rfl⟩
        by_cases hit : i = t
        · subst hit
          exact hft
        · exact Ideal.mem_sup_left
            (Ideal.subset_span ⟨i, hi, by simp [Function.update_of_ne (hσ.ne hit)]⟩)
    rw [hZ]
    exact hJJ

/-- The transfer for a terminal-normal stratum. -/
theorem terminalIn_of_terminalIn_update [IsRegularLocalRing R] {n : ℕ}
    {z : Fin n → R} (hz : IsRegularSystemOfParameters z) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (hσ : Function.Injective σ) (C : Set (Fin n)) (hCσ : ∀ k ∈ C, k ∉ Set.range σ)
    (a : Fin (r + 1) → Fin n → ℕ) {x : R}
    (hx : x ∈ chainIdeal (z ∘ σ) (fun i => monomialOf z (a i))) (t : Fin (r + 1))
    (hupd : IsRegularSystemOfParameters (Function.update z (σ t) x)) {Z : Ideal R}
    (h : TerminalIn (Function.update z (σ t) x) C σ Z) : TerminalIn z C σ Z := by
  obtain ⟨s, hsC, hne, hZ⟩ := h
  refine ⟨s, hsC, hne, ?_⟩
  have hs : Function.update z (σ t) x '' ↑s = z '' ↑s :=
    Set.image_congr fun k hk => Function.update_of_ne (fun h => hCσ k (hsC hk) ⟨t, h.symm⟩) _ _
  rw [hZ, hs, span_range_update_eq_of_mem_chainIdeal hz σ hσ a hx t hupd]

end Rebase

end Hironaka.Resolution
