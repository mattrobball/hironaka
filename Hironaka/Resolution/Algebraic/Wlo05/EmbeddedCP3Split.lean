/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Predicates
import Hironaka.Algebra.Local.Regular
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Split
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitMain
import Hironaka.Resolution.Algebraic.Snc.ComponentStalks
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Wlo05.ChainIdealColon
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Rebase
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Snc.TotalTransformData
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The fine split of a chain shape at the stalk

[Kol07, Definition–Lemma 110] writes `I = M(I) · N(I)` with `M(I)` the monomial part
`𝒪(−∑ cᵢ Eⁱ)` and `N(I)` the nonmonomial part, whose cosupport contains no `Eⁱ`; the library has
the split (`monomialPart_mul_nonmonomialPart`) and the vanishing of `ord N(I)` along the members
(`ord_nonmonomialPart_eq_zero`). The proof of the statement CP3 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) needs the split read in chain
coordinates at a point `p`: if `K_p = (∏ z_{c j}^{b_{c j}}) · C` with `C` the chain part (the
K-shape or the un-isolated form), then `N(K)_p = C`. Two facts make this a cancellation:

* `stalkIdeal_monomialPart_eq_span_prod` — the stalk of `M(K)` at `p` is the monomial in the
  coordinates of the members through `p`, with exponents the orders of `K` at their generic points
  ([Kol07, Definition 47]; `stalkIdeal_monomial`, `finprod_stalk_eq_of_specializes`; members not
  through `p` contribute the unit ideal);
* `eq_of_span_prod_pow_mul_eq` — in a regular local ring with a regular system `z`, if two
  monomials in the coordinates `z (c j)`, whose ideals `(z (c j))` are prime, times ideals lying in
  none of those primes agree, the exponents and the cofactors agree (compare exponent by exponent:
  cancel the common power, the remaining monomial in the other coordinates lies outside the prime,
  `Ideal.span_singleton_mul_right_inj`).

The nonmonomial part lies in no member's prime because its order at the member's generic point is
`0` ([Kol07, Definition–Lemma 110]; hence the hypothesis that the ideal is nonzero everywhere),
and the chain part contains the first equation `z_{σ 0}` of the chain, a coordinate off the
members (`notMem_span_singleton_of_ne`); with `r = 0` the K-shape is the unit ideal.
`stalkIdeal_nonmonomialPart_eq_of_eq_span_mul` is the common core;
`stalkIdeal_nonmonomialPart_of_kShape` and `stalkIdeal_nonmonomialPart_of_iShape` are its
instances. The chain coordinates are those of [Kol07, Definition 24]. These identities are not in
the literature. Used in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step3` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step1`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing Scheme IdealSheafData
  BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence Hironaka.BMO Hironaka.BMO.Snc

namespace Hironaka.Resolution

section Ring

variable {R : Type*} [CommRing R]

/-- A coordinate of a regular system lies outside the prime of another coordinate:
`AlgebraicGeometry.notMem_span_singleton_of_ne` read on `IsRegularSystemOfParameters`. -/
theorem notMem_span_singleton_of_ne [IsRegularLocalRing R] {n : ℕ} {z : Fin n → R}
    (hz : IsRegularSystemOfParameters z) {i j : Fin n} (hij : i ≠ j) :
    z i ∉ Ideal.span {z j} :=
  AlgebraicGeometry.notMem_span_singleton_of_ne hz.1 hz.2 hij.symm

/-- A coordinate of a regular system is nonzero. -/
theorem ne_zero_of_isRegularSystemOfParameters [IsRegularLocalRing R] {n : ℕ} {z : Fin n → R}
    (hz : IsRegularSystemOfParameters z) (i : Fin n) : z i ≠ 0 := fun h0 =>
  notMem_span_compl_sup_sq hz i (h0 ▸ zero_mem _)

/-- A monomial in the coordinates other than `z (c j₀)` lies outside the prime `(z (c j₀))`. -/
theorem prod_pow_notMem_span_singleton [IsRegularLocalRing R] {n : ℕ} {z : Fin n → R}
    (hz : IsRegularSystemOfParameters z) {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ι → Fin n}
    (hc : Function.Injective c) (e : ι → ℕ) (j₀ : ι) (hprime : (Ideal.span {z (c j₀)}).IsPrime) :
    ∏ j ∈ Finset.univ.erase j₀, z (c j) ^ e j ∉ Ideal.span {z (c j₀)} := by
  intro hmem
  have := hprime
  obtain ⟨j, hj, hmemj⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
  have hne : j ≠ j₀ := Finset.ne_of_mem_erase hj
  exact notMem_span_singleton_of_ne hz (fun h => hne (hc h)) (hprime.mem_of_pow_mem _ hmemj)

/-- One direction of the exponent comparison: a larger exponent on one side would put the other
side's cofactor into the prime. -/
theorem le_of_span_prod_pow_mul_eq [IsRegularLocalRing R] {n : ℕ} {z : Fin n → R}
    (hz : IsRegularSystemOfParameters z) {ι : Type*} [Fintype ι] {c : ι → Fin n}
    (hc : Function.Injective c) (hprime : ∀ j, (Ideal.span {z (c j)}).IsPrime) (e₁ e₂ : ι → ℕ)
    {N₁ N₂ : Ideal R} (h₁ : ∀ j, ¬ N₁ ≤ Ideal.span {z (c j)})
    (h : Ideal.span {∏ j, z (c j) ^ e₁ j} * N₁ = Ideal.span {∏ j, z (c j) ^ e₂ j} * N₂) (j : ι) :
    e₂ j ≤ e₁ j := by
  classical
  have : IsDomain R := isDomain_of_isRegularLocalRing R
  by_contra hlt'
  have hlt := not_le.mp hlt'
  have hz0 := ne_zero_of_isRegularSystemOfParameters hz (c j)
  have hsplit₁ : ∏ j', z (c j') ^ e₁ j' =
      z (c j) ^ e₁ j * ∏ j' ∈ Finset.univ.erase j, z (c j') ^ e₁ j' :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
  have hsplit₂ : ∏ j', z (c j') ^ e₂ j' =
      z (c j) ^ e₁ j *
        (z (c j) ^ (e₂ j - e₁ j) * ∏ j' ∈ Finset.univ.erase j, z (c j') ^ e₂ j') := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), ← mul_assoc, ← pow_add,
      Nat.add_sub_cancel' hlt.le]
  rw [hsplit₁, hsplit₂, ← Ideal.span_singleton_mul_span_singleton,
    ← Ideal.span_singleton_mul_span_singleton, mul_assoc, mul_assoc] at h
  have h' := (Ideal.span_singleton_mul_right_inj (pow_ne_zero _ hz0)).mp h
  have hle : Ideal.span {∏ j' ∈ Finset.univ.erase j, z (c j') ^ e₁ j'} * N₁ ≤
      Ideal.span {z (c j)} := by
    rw [h']
    refine Ideal.mul_le_left.trans (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_))
    exact Ideal.mul_mem_right _ _
      (Ideal.mem_span_singleton.mpr (dvd_pow_self _ (Nat.sub_ne_zero_of_lt hlt)))
  apply h₁ j
  intro x hx
  have hmem := hle (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hx)
  exact ((hprime j).mem_or_mem hmem).resolve_left
    (prod_pow_notMem_span_singleton hz hc e₁ j (hprime j))

/-- Uniqueness of the monomial factor: two factorizations `(monomial) · N` with the cofactors in
no coordinate prime have the same exponents and the same cofactor. -/
theorem eq_of_span_prod_pow_mul_eq [IsRegularLocalRing R] {n : ℕ} {z : Fin n → R}
    (hz : IsRegularSystemOfParameters z) {ι : Type*} [Fintype ι] {c : ι → Fin n}
    (hc : Function.Injective c) (hprime : ∀ j, (Ideal.span {z (c j)}).IsPrime) (e₁ e₂ : ι → ℕ)
    {N₁ N₂ : Ideal R} (h₁ : ∀ j, ¬ N₁ ≤ Ideal.span {z (c j)})
    (h₂ : ∀ j, ¬ N₂ ≤ Ideal.span {z (c j)})
    (h : Ideal.span {∏ j, z (c j) ^ e₁ j} * N₁ = Ideal.span {∏ j, z (c j) ^ e₂ j} * N₂) :
    e₁ = e₂ ∧ N₁ = N₂ := by
  classical
  have : IsDomain R := isDomain_of_isRegularLocalRing R
  have he : e₁ = e₂ := funext fun j => le_antisymm
    (le_of_span_prod_pow_mul_eq hz hc hprime e₂ e₁ h₂ h.symm j)
    (le_of_span_prod_pow_mul_eq hz hc hprime e₁ e₂ h₁ h j)
  subst he
  refine ⟨rfl, (Ideal.span_singleton_mul_right_inj ?_).mp h⟩
  exact Finset.prod_ne_zero_iff.mpr fun j _ =>
    pow_ne_zero _ (ne_zero_of_isRegularSystemOfParameters hz (c j))

/-- A monomial with exponents supported on the range of an injection is the product over the
domain of the injection. -/
theorem monomialOf_eq_prod_of_forall_mem_range {n : ℕ} (z : Fin n → R) {ι : Type*} [Fintype ι]
    {c : ι → Fin n} (hc : Function.Injective c) {b : Fin n → ℕ}
    (hb : ∀ κ, b κ ≠ 0 → κ ∈ Set.range c) : monomialOf z b = ∏ j, z (c j) ^ b (c j) := by
  classical
  unfold monomialOf
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image c)) (fun κ _ hκ => ?_),
    Finset.prod_image (fun j _ j' _ h => hc h)]
  have hκ0 : b κ = 0 := by
    by_contra hne
    obtain ⟨j, hj⟩ := hb κ hne
    exact hκ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)
  rw [hκ0, pow_zero]

end Ring

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}

omit [CharZero k] in
open Classical in
/-- [Kol07, Definition–Lemma 110] at the stalk: the stalk of the monomial part at `p` is the
monomial in the coordinates of the members through `p`, with the orders at their generic points
as exponents. -/
theorem stalkIdeal_monomialPart_eq_span_prod [IsNoetherian X] (f : X ⟶ Spec (CommRingCat.of k))
    (n₀ : ℕ) [SmoothOfRelativeDimension n₀ f] {E : DivisorFamily X} (hE : E.IsSnc)
    (K : X.IdealSheafData) {p : X} {n : ℕ} {z : Fin n → X.presheaf.stalk p}
    {c : {j : E.ι // p ∈ (E.component j).support} → Fin n}
    (hcmem : ∀ j, (E.component j.1).stalkIdeal p = Ideal.span {z (c j)})
    (η : {j : E.ι // p ∈ (E.component j).support} → X)
    (hη : ∀ j, η j ∈ (E.component j.1).support.genericPoints) (hηp : ∀ j, η j ⤳ p) :
    (monomialPart K E).stalkIdeal p = Ideal.span {∏ j, z (c j) ^ (K.ord (η j)).toNat} := by
  classical
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n₀ f
  rw [monomialPart_eq_monomial, stalkIdeal_monomial E (genericPoints_component_finite E) _ p]
  set F : E.ι → Ideal (X.presheaf.stalk p) := fun i =>
    ∏ᶠ η' ∈ (E.component i).support.genericPoints,
      ((vanishingIdeal (Closeds.closure {η'})).stalkIdeal p) ^ (K.ord η').toNat with hF
  have hoff : ∀ i ∈ Finset.univ, i ∉ Finset.univ.filter (fun i => p ∈ (E.component i).support) →
      F i = 1 := fun i _ hi => by
    rw [Finset.mem_filter, not_and] at hi
    exact finprod_stalk_eq_one_of_notMem E (hi (Finset.mem_univ i)) _
  have h1 : ∏ i, F i = ∏ i ∈ Finset.univ.filter (fun i => p ∈ (E.component i).support), F i :=
    (Finset.prod_subset (Finset.subset_univ _) hoff).symm
  have h2 : ∏ i ∈ Finset.univ.filter (fun i => p ∈ (E.component i).support), F i =
      ∏ j : {j : E.ι // p ∈ (E.component j).support}, F j.1 :=
    Finset.prod_subtype _ (fun i => by simp) F
  change ∏ i, F i = _
  rw [h1, h2, ← Ideal.prod_span_singleton]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hF]
  dsimp only
  rw [finprod_stalk_eq_of_specializes E hE (hη j) (hηp j), hcmem j, Ideal.span_singleton_pow]

/-- The common core of the fine split in chain coordinates: the nonmonomial part of an ideal
whose stalk is a monomial in the members' coordinates times an ideal lying in no member's prime
is that ideal. -/
theorem stalkIdeal_nonmonomialPart_eq_of_eq_span_mul [IsNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of k)) (n₀ : ℕ) [SmoothOfRelativeDimension n₀ f]
    {E : DivisorFamily X} (hE : E.IsSnc) {K : X.IdealSheafData} (hK0 : IsNonzeroEverywhere K)
    {p : X} {n : ℕ} {z : Fin n → X.presheaf.stalk p}
    {c : {j : E.ι // p ∈ (E.component j).support} → Fin n} {r : ℕ} {σ : Fin (r + 1) → Fin n}
    {a : Fin (r + 1) → Fin n → ℕ} (hc : ChainCoordsFree E p z c σ a) {b : Fin n → ℕ}
    (hb : ∀ κ, b κ ≠ 0 → κ ∈ Set.range c) {C : Ideal (X.presheaf.stalk p)}
    (hC : ∀ j, ¬ C ≤ Ideal.span {z (c j)})
    (hK : K.stalkIdeal p = Ideal.span {monomialOf z b} * C) :
    (nonmonomialPart K E).stalkIdeal p = C := by
  classical
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n₀ f
  have hreg := isRegularLocalRing_stalk f p
  obtain ⟨hz, hcinj, hcmem, -, -, -⟩ := hc
  have hex : ∀ j : {j : E.ι // p ∈ (E.component j).support},
      ∃ η ∈ (E.component j.1).support.genericPoints, η ⤳ p :=
    fun j => exists_genericPoint_specializes _ j.2
  choose η hη hηp using hex
  have hsplit : K.stalkIdeal p =
      (monomialPart K E).stalkIdeal p * (nonmonomialPart K E).stalkIdeal p := by
    rw [← stalkIdeal_mul, Snc.monomialPart_mul_nonmonomialPart f E hE K]
  rw [stalkIdeal_monomialPart_eq_span_prod f n₀ hE K hcmem η hη hηp] at hsplit
  rw [monomialOf_eq_prod_of_forall_mem_range z hcinj hb] at hK
  have hprime : ∀ j, (Ideal.span {z (c j)}).IsPrime := fun j => by
    rw [← hcmem j]
    exact isPrime_stalkIdeal_component_of_isSnc f E hE j.2
  have hN : ∀ j, ¬ (nonmonomialPart K E).stalkIdeal p ≤ Ideal.span {z (c j)} := by
    intro j hle
    have h0 := Snc.ord_nonmonomialPart_eq_zero f E hE hK0 (hη j)
    rw [IdealSheafData.ord_eq_zero_iff, mem_support_iff_stalkIdeal_le_maximalIdeal] at h0
    apply h0
    rw [stalkIdeal_specializes _ (hηp j), maximalIdeal_eq_stalkIdeal_component E hE (hη j),
      stalkIdeal_specializes (E.component j.1) (hηp j)]
    exact Ideal.map_mono (hle.trans_eq (hcmem j).symm)
  exact (eq_of_span_prod_pow_mul_eq hz hcinj hprime _ _ hN hC (hsplit.symm.trans hK)).2

/-- The fine split of [Kol07, Definition–Lemma 110] at the stalk: the nonmonomial part of a
K-shape is its chain part. -/
theorem stalkIdeal_nonmonomialPart_of_kShape [IsNoetherian X] (f : X ⟶ Spec (CommRingCat.of k))
    (n₀ : ℕ) [SmoothOfRelativeDimension n₀ f] {E : DivisorFamily X} (hE : E.IsSnc)
    {K : X.IdealSheafData} (hK0 : IsNonzeroEverywhere K) {p : X} {n : ℕ}
    {z : Fin n → X.presheaf.stalk p}
    {c : {j : E.ι // p ∈ (E.component j).support} → Fin n} {r : ℕ} {σ : Fin (r + 1) → Fin n}
    {a : Fin (r + 1) → Fin n → ℕ} {b : Fin n → ℕ} (hc : ChainCoordsFree E p z c σ a)
    (hb : ∀ κ, b κ ≠ 0 → κ ∈ Set.range c)
    (hK : K.stalkIdeal p =
      Ideal.span {monomialOf z b} * chainKIdeal (z ∘ σ) (fun i => monomialOf z (a i))) :
    (nonmonomialPart K E).stalkIdeal p = chainKIdeal (z ∘ σ) (fun i => monomialOf z (a i)) := by
  refine stalkIdeal_nonmonomialPart_eq_of_eq_span_mul f n₀ hE hK0 hc hb ?_ hK
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n₀ f
  have hreg := isRegularLocalRing_stalk f p
  obtain ⟨hz, -, -, -, hσc, -⟩ := hc
  intro j hle
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    rw [chainKIdeal_zero] at hle
    have hunit : IsUnit (z (c j)) := Ideal.span_singleton_eq_top.mp (top_le_iff.mp hle)
    have hmem : z (c j) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p) := by
      rw [← hz.1]
      exact Ideal.subset_span ⟨c j, rfl⟩
    exact (IsLocalRing.notMem_maximalIdeal.mpr hunit) hmem
  · have hmem : z (σ 0) ∈ chainKIdeal (z ∘ σ) (fun i => monomialOf z (a i)) := by
      rw [chainKIdeal_eq_span_range_kGen,
        ← kGen_eq_of_le z σ a hr (fun i hi => absurd hi (Nat.not_lt_zero _)) (le_refl _)]
      exact Ideal.subset_span ⟨0, rfl⟩
    exact notMem_span_singleton_of_ne hz (hσc 0 j) (hle hmem)

/-- The fine split at the stalk for the un-isolated form: the nonmonomial part of an I-shape is
its chain part. -/
theorem stalkIdeal_nonmonomialPart_of_iShape [IsNoetherian X] (f : X ⟶ Spec (CommRingCat.of k))
    (n₀ : ℕ) [SmoothOfRelativeDimension n₀ f] {E : DivisorFamily X} (hE : E.IsSnc)
    {I : X.IdealSheafData} (hI0 : IsNonzeroEverywhere I) {p : X} {n : ℕ}
    {z : Fin n → X.presheaf.stalk p}
    {c : {j : E.ι // p ∈ (E.component j).support} → Fin n} {r : ℕ} {σ : Fin (r + 1) → Fin n}
    {a : Fin (r + 1) → Fin n → ℕ} {b : Fin n → ℕ} (hc : ChainCoordsFree E p z c σ a)
    (hb : ∀ κ, b κ ≠ 0 → κ ∈ Set.range c)
    (hI : I.stalkIdeal p =
      Ideal.span {monomialOf z b} * chainIdeal (z ∘ σ) (fun i => monomialOf z (a i))) :
    (nonmonomialPart I E).stalkIdeal p = chainIdeal (z ∘ σ) (fun i => monomialOf z (a i)) := by
  refine stalkIdeal_nonmonomialPart_eq_of_eq_span_mul f n₀ hE hI0 hc hb ?_ hI
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n₀ f
  have hreg := isRegularLocalRing_stalk f p
  obtain ⟨hz, -, -, -, hσc, -⟩ := hc
  intro j hle
  have hmem : z (σ 0) ∈ chainIdeal (z ∘ σ) (fun i => monomialOf z (a i)) := by
    rw [chainIdeal_eq_span_range_iGen,
      ← iGen_eq_of_le z σ a (fun i hi => absurd hi (Nat.not_lt_zero _)) (le_refl _)]
    exact Ideal.subset_span ⟨0, rfl⟩
  exact notMem_span_singleton_of_ne hz (hσc 0 j) (hle hmem)

end Hironaka.Resolution
