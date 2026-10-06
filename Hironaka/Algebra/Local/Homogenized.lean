/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Tuning
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Włodarczyk's homogenized and coefficient ideals against Kollár's maximal coefficient ideals

A comparison, used nowhere else in the library. Włodarczyk [Wlo05, §2.9] sets `T(I) := D^{μ−1} I`
(Kollár's maximal-contact ideal `MC_μ(I)`, `Hironaka/Algebra/Local/MaximalContact.lean`) and defines
the **homogenized ideal** `H(I) := I + D(I)·T(I) + ⋯ + D^{μ−1}(I)·T(I)^{μ−1}`, with mark `μ`
(`homogenized`); the **coefficient ideal** [Wlo05, Definition 2.10.1] is the marked sum
`C(I, μ) := ∑ᵢ (Dⁱ I, μ − i)` (`coefficientIdeal`), where the sum of marked ideals with different
marks is Włodarczyk's `(I₁, μ₁) + ⋯ + (Iₘ, μₘ) := (∑ᵢ Iᵢ^{∏_{k ≠ i} μ_k}, ∏ μ_k)` [Wlo05, §2.8]
(`MarkedIdeal.wsum`).

Relation to Kollár's maximal coefficient ideals `W_s(I)` (`Hironaka/Algebra/Local/Tuning.lean`, with
parameter `m = μ`): each summand `Dⁱ I · (D^{μ−1} I)ⁱ` of `H(I)` has weight `(μ − i) + i = μ`, so
`H(I) ≤ W_μ(I)` (`homogenized_le_W`); each summand `(Dⁱ I)^{μ!/(μ−i)}` of `C(I, μ)` has weight
`μ!`, so `C(I, μ) ≤ W_{μ!}(I)` (`coefficientIdeal_I_le_W`). [Wlo05, Lemma 2.9.1] is verified at
the ideal level: `H(I) = I` for `μ = 1`; the series may run over all `i`; the marked form of the
summands; `D(H(I, μ)) ≤ H(D(I, μ))` for `μ > 1`; and `T(H(I)) = T(I)`, the analogue of
[Kol07, (99.4)]. The local halves of [Wlo05, Lemma 2.8.1 (1)] (the closed point lies in the
cosupport of a marked sum when it lies in the cosupport of every summand, `inCosupp_wsum`) and of
[Wlo05, Lemma 2.10.2] (`inCosupp_coefficientIdeal`) are included. His Lemmas 2.9.2, 2.10.2 and
2.10.4 otherwise concern multiple test blow-ups, the analogues of [Kol07, Theorem 100] and of the
going-up for D-balanced ideals, and are not treated here.

Włodarczyk's displayed range for the coefficient ideal is `i = 1, …, μ` in the arXiv text; the
proof of his Lemma 2.10.2 uses `0 ≤ i ≤ μ − 1`, which is the range under which the marked sum of
§2.8 is meaningful (a summand of mark `0` would make the product of marks `0`); that range is used
here.
-/

@[expose] public section

namespace IsLocalRing

namespace MarkedIdeal

variable {R : Type*} [CommRing R]

/-- Włodarczyk's sum of marked ideals with different marks [Wlo05, §2.8]:
`(I₁, μ₁) + ⋯ + (Iₖ, μₖ) := (∑ᵢ Iᵢ^{∏_{j ≠ i} μⱼ}, ∏ⱼ μⱼ)`. -/
def wsum {k : ℕ} (L : Fin k → MarkedIdeal R) : MarkedIdeal R :=
  ⟨∑ i, (L i).I ^ ∏ j ∈ Finset.univ.erase i, (L j).m, ∏ j, (L j).m⟩

@[simp] theorem wsum_I {k : ℕ} (L : Fin k → MarkedIdeal R) :
    (wsum L).I = ∑ i, (L i).I ^ ∏ j ∈ Finset.univ.erase i, (L j).m := rfl

@[simp] theorem wsum_m {k : ℕ} (L : Fin k → MarkedIdeal R) : (wsum L).m = ∏ j, (L j).m := rfl

/-- Włodarczyk's displayed binary case: `(I, μ_I) + (J, μ_J) = (I^{μ_J} + J^{μ_I}, μ_I μ_J)`. -/
theorem wsum_two (J K : MarkedIdeal R) : wsum ![J, K] = ⟨J.I ^ K.m + K.I ^ J.m, J.m * K.m⟩ := by
  have h0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have h1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  unfold wsum
  rw [Fin.sum_univ_two, Fin.prod_univ_two, h0, h1, Finset.prod_singleton, Finset.prod_singleton]
  rfl

/-- [Wlo05, Lemma 2.8.1 (1)], the local half, valid in every local ring: if the closed point lies
in every `cosupp (Iᵢ, μᵢ)`, it lies in `cosupp` of the sum. -/
theorem inCosupp_wsum [IsLocalRing R] {k : ℕ} {L : Fin k → MarkedIdeal R}
    (h : ∀ i, (L i).InCosupp) : (wsum L).InCosupp := by
  classical
  unfold InCosupp at *
  rw [wsum_I, wsum_m, le_ord_iff, Ideal.sum_eq_sup, Finset.sup_le_iff]
  intro i _
  have hi := le_ord_iff.mp (h i)
  calc (L i).I ^ ∏ j ∈ Finset.univ.erase i, (L j).m
      ≤ (IsLocalRing.maximalIdeal R ^ (L i).m) ^ ∏ j ∈ Finset.univ.erase i, (L j).m :=
        Ideal.pow_right_mono hi _
    _ = IsLocalRing.maximalIdeal R ^ ∏ j, (L j).m := by
        rw [← pow_mul]
        congr 1
        exact Finset.mul_prod_erase _ (fun j => (L j).m) (Finset.mem_univ i)

/-- Powers of marked ideals, `(I, m)ᵏ = (Iᵏ, m k)`: the iterated product of marked ideals of
[Kol07, Definition 59] and [Wlo05, §2.8]. -/
instance : Pow (MarkedIdeal R) ℕ := ⟨fun J k => ⟨J.I ^ k, J.m * k⟩⟩

@[simp] theorem pow_I (J : MarkedIdeal R) (k : ℕ) : (J ^ k).I = J.I ^ k := rfl

@[simp] theorem pow_m (J : MarkedIdeal R) (k : ℕ) : (J ^ k).m = J.m * k := rfl

end MarkedIdeal

namespace RegularCoords

open IsLocalRing

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ}
  (c : RegularCoords R n)

/-! ### The homogenized ideal ([Wlo05, §2.9]) -/

/-- Włodarczyk's **homogenized ideal** `H(I) := ∑_{i < μ} Dⁱ(I) · T(I)ⁱ` with `T(I) = D^{μ-1} I`
(Kollár's `MC_μ(I)`); the marked ideal is `(H(I), μ)`. -/
def homogenized (I : Ideal R) (μ : ℕ) : Ideal R :=
  ∑ i ∈ Finset.range μ, c.Dpow i I * c.MC I μ ^ i

theorem homogenized_le_iff {I J : Ideal R} {μ : ℕ} :
    c.homogenized I μ ≤ J ↔ ∀ i < μ, c.Dpow i I * c.MC I μ ^ i ≤ J := by
  unfold homogenized
  rw [Ideal.sum_eq_sup, Finset.sup_le_iff]
  simp only [Finset.mem_range]

theorem Dpow_mul_MC_pow_le_homogenized {I : Ideal R} {μ i : ℕ} (hi : i < μ) :
    c.Dpow i I * c.MC I μ ^ i ≤ c.homogenized I μ := by
  unfold homogenized
  rw [Ideal.sum_eq_sup]
  exact Finset.le_sup (f := fun i => c.Dpow i I * c.MC I μ ^ i) (Finset.mem_range.mpr hi)

theorem le_homogenized {I : Ideal R} {μ : ℕ} (hμ : 0 < μ) : I ≤ c.homogenized I μ := by
  have := c.Dpow_mul_MC_pow_le_homogenized (I := I) hμ
  simpa using this

/-- [Wlo05, Lemma 2.9.1 (1)]: `H(I, 1) = (I, 1)`. -/
theorem homogenized_one (I : Ideal R) : c.homogenized I 1 = I := by
  simp [homogenized]

/-- [Wlo05, Lemma 2.9.1 (2)]: the series `∑ᵢ Dⁱ(I) · T(I)ⁱ` may run over all `i`; the terms with
`i ≥ μ` lie in `T(I)^μ = D^{μ−1}(I) · T(I)^{μ−1}`. -/
theorem Dpow_mul_MC_pow_le_homogenized' {I : Ideal R} {μ : ℕ} (hμ : 1 ≤ μ) (i : ℕ) :
    c.Dpow i I * c.MC I μ ^ i ≤ c.homogenized I μ := by
  rcases Nat.lt_or_ge i μ with hi | hi
  · exact c.Dpow_mul_MC_pow_le_homogenized hi
  · calc c.Dpow i I * c.MC I μ ^ i ≤ c.MC I μ ^ i := Ideal.mul_le_right
      _ ≤ c.MC I μ ^ μ := Ideal.pow_le_pow_right hi
      _ = c.Dpow (μ - 1) I * c.MC I μ ^ (μ - 1) := by
        change c.MC I μ ^ μ = c.MC I μ * c.MC I μ ^ (μ - 1)
        rw [← pow_succ', Nat.sub_add_cancel hμ]
      _ ≤ c.homogenized I μ := c.Dpow_mul_MC_pow_le_homogenized (by omega)

theorem homogenized_eq_iSup {I : Ideal R} {μ : ℕ} (hμ : 1 ≤ μ) :
    c.homogenized I μ = ⨆ i : ℕ, c.Dpow i I * c.MC I μ ^ i :=
  le_antisymm (c.homogenized_le_iff.mpr fun i _ => le_iSup (fun i => c.Dpow i I * c.MC I μ ^ i) i)
    (iSup_le fun i => c.Dpow_mul_MC_pow_le_homogenized' hμ i)

/-- The relation to Kollár's maximal coefficient ideal: each summand `Dⁱ I · (D^{μ−1} I)ⁱ` has
weight `(μ − i) + i = μ`, so `H(I) ≤ W_μ(I)` (with parameter `m = μ`). -/
theorem homogenized_le_W {I : Ideal R} {μ : ℕ} (hμ : 1 ≤ μ) : c.homogenized I μ ≤ c.W μ μ I := by
  refine c.homogenized_le_iff.mpr fun i hi => ?_
  calc c.Dpow i I * c.MC I μ ^ i ≤ c.W μ (μ - i) I * c.W μ i I :=
        Ideal.mul_mono (c.Dpow_le_W_of_le hi.le I) (c.MC_pow_le_W hμ i I)
    _ ≤ c.W μ (μ - i + i) I := c.W_mul_le μ (μ - i) i I
    _ = c.W μ μ I := by rw [Nat.sub_add_cancel hi.le]

/-- [Wlo05, Lemma 2.9.1 (3)], the summands: `Dⁱ(I, μ) · (T(I), 1)ⁱ = (Dⁱ I · T(I)ⁱ, μ)` for
`i ≤ μ`. -/
theorem markedD_mul_MC_pow (I : Ideal R) {μ i : ℕ} (hi : i ≤ μ) :
    c.markedD ⟨I, μ⟩ i hi * (⟨c.MC I μ, 1⟩ : MarkedIdeal R) ^ i =
      ⟨c.Dpow i I * c.MC I μ ^ i, μ⟩ := by
  rw [MarkedIdeal.mul_def]
  simp only [markedD_I, markedD_m, MarkedIdeal.pow_I, MarkedIdeal.pow_m, one_mul]
  congr 1
  omega

/-- [Wlo05, Lemma 2.9.1 (3)]: `(H(I), μ) = ∑_{i < μ} Dⁱ(I, μ) · (T(I), 1)ⁱ`, a sum of marked
ideals all of mark `μ` (the sum of equally marked ideals of [Kol07, Definition 59]). -/
theorem homogenized_marked (I : Ideal R) (μ : ℕ) :
    (⟨c.homogenized I μ, μ⟩ : MarkedIdeal R) =
      ⟨∑ i : Fin μ, (c.markedD ⟨I, μ⟩ i i.isLt.le * (⟨c.MC I μ, 1⟩ : MarkedIdeal R) ^ (i : ℕ)).I,
        μ⟩ := by
  congr 1
  unfold homogenized
  rw [← Fin.sum_univ_eq_sum_range (fun i => c.Dpow i I * c.MC I μ ^ i) μ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [c.markedD_mul_MC_pow I i.isLt.le]

/-- `T(D(I), μ - 1) = T(I, μ)` for `μ > 1`: the maximal-contact ideal of
`D(I, μ) = (D I, μ - 1)`. -/
theorem MC_D {I : Ideal R} {μ : ℕ} (hμ : 1 < μ) : c.MC (c.D I) (μ - 1) = c.MC I μ := by
  unfold MC
  rw [← Dpow_one, Dpow_Dpow]
  congr 1
  omega

theorem D_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Ideal R) :
    c.D (∑ i ∈ s, f i) = ∑ i ∈ s, c.D (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [D_bot]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Ideal.add_eq_sup, D_sup, ih,
      Ideal.add_eq_sup]

/-- [Wlo05, Lemma 2.9.1 (4)]: for `μ > 1`, `D(H(I, μ)) ≤ H(D(I, μ))`, that is,
`D(H_μ(I)) ≤ H_{μ−1}(D I)`. -/
theorem D_homogenized_le {I : Ideal R} {μ : ℕ} (hμ : 1 < μ) :
    c.D (c.homogenized I μ) ≤ c.homogenized (c.D I) (μ - 1) := by
  have key : ∀ j : ℕ, c.Dpow (j + 1) I * c.MC I μ ^ j ≤ c.homogenized (c.D I) (μ - 1) := by
    intro j
    have := c.Dpow_mul_MC_pow_le_homogenized' (I := c.D I) (μ := μ - 1) (by omega) j
    rwa [c.MC_D hμ, ← Dpow_succ'] at this
  unfold homogenized
  rw [D_finset_sum, Ideal.sum_eq_sup, Finset.sup_le_iff]
  intro i _
  refine (c.D_mul_le _ _).trans (sup_le ?_ ?_)
  · rw [← Dpow_succ]
    exact key i
  · rcases i with _ | j
    · simp only [pow_zero, Ideal.one_eq_top, D_top, Dpow_zero, Ideal.mul_top]
      exact (c.le_D I).trans (c.le_homogenized (by omega))
    · calc c.Dpow (j + 1) I * c.D (c.MC I μ ^ (j + 1))
          ≤ c.Dpow (j + 1) I * (c.D (c.MC I μ) * c.MC I μ ^ (j + 1 - 1)) :=
            Ideal.mul_mono le_rfl (c.D_pow_le _ (by omega))
        _ ≤ c.Dpow (j + 1) I * c.MC I μ ^ j := by
            rw [Nat.add_sub_cancel]
            exact Ideal.mul_mono le_rfl Ideal.mul_le_right
        _ ≤ c.homogenized (c.D I) (μ - 1) := key j

/-- `Dⁱ(W_s(I)) ≤ W_{s−i}(I)` for `i ≤ s` (iterating `D_W_succ_le`). -/
theorem Dpow_W_le {m : ℕ} (I : Ideal R) {i s : ℕ} (hi : i ≤ s) :
    c.Dpow i (c.W m s I) ≤ c.W m (s - i) I := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Dpow_succ]
    refine (c.D_mono (ih (by omega))).trans ?_
    have h := c.D_W_succ_le m (s - (i + 1)) I
    rwa [show s - (i + 1) + 1 = s - i by omega] at h

/-- `W_1(I) ≤ MC_μ(I)`: a product of positive weight contains a factor `Dʲ I` with `j < μ`. -/
theorem W_one_le_MC {μ : ℕ} (I : Ideal R) : c.W μ 1 I ≤ c.MC I μ := by
  classical
  refine c.W_le_iff.mpr fun e he => ?_
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun j : Fin (μ + 1) => (μ - (j : ℕ)) * e j) (by
      unfold wt at he
      exact Nat.pos_iff_ne_zero.mp he)
  rw [mul_ne_zero_iff] at hj
  calc ∏ l : Fin (μ + 1), c.Dpow l I ^ e l ≤ c.Dpow j I ^ e j := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
        exact Ideal.mul_le_left
    _ ≤ c.Dpow j I := Ideal.pow_le_self hj.2
    _ ≤ c.MC I μ := c.Dpow_mono_left (by have := hj.1; omega) I

/-- [Wlo05, Lemma 2.9.1 (5)], the analogue of [Kol07, (99.4)]: `T(H(I, μ)) = T(I, μ)`. -/
theorem MC_homogenized {I : Ideal R} {μ : ℕ} (hμ : 1 ≤ μ) :
    c.MC (c.homogenized I μ) μ = c.MC I μ := by
  refine le_antisymm ?_ (c.Dpow_mono _ (c.le_homogenized hμ))
  calc c.MC (c.homogenized I μ) μ ≤ c.Dpow (μ - 1) (c.W μ μ I) :=
        c.Dpow_mono _ (c.homogenized_le_W hμ)
    _ ≤ c.W μ (μ - (μ - 1)) I := c.Dpow_W_le I (by omega)
    _ = c.W μ 1 I := by rw [show μ - (μ - 1) = 1 by omega]
    _ ≤ c.MC I μ := c.W_one_le_MC I

/-! ### The coefficient ideal ([Wlo05, Definition 2.10.1]) -/

/-- Włodarczyk's **coefficient ideal** `C(I, μ) := ∑_{i < μ} (Dⁱ I, μ − i)`, the marked sum
([Wlo05, §2.8]) of the marked derivatives `Dⁱ(I, μ)` (`markedD`,
`Hironaka/Algebra/Local/Derivative.lean`). -/
def coefficientIdeal (I : Ideal R) (μ : ℕ) : MarkedIdeal R :=
  MarkedIdeal.wsum fun i : Fin μ => c.markedD ⟨I, μ⟩ i i.isLt.le

theorem prod_fin_sub_eq_factorial (μ : ℕ) : ∏ i : Fin μ, (μ - (i : ℕ)) = μ.factorial := by
  rw [Fin.prod_univ_eq_prod_range (fun i => μ - i) μ, ← Finset.prod_range_add_one_eq_factorial,
    ← Finset.prod_range_reflect (fun i => i + 1) μ]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  omega

/-- The mark of `C(I, μ)` is `μ! = ∏_{i < μ} (μ - i)`. -/
theorem coefficientIdeal_m (I : Ideal R) (μ : ℕ) : (c.coefficientIdeal I μ).m = μ.factorial := by
  unfold coefficientIdeal
  rw [MarkedIdeal.wsum_m]
  simpa using prod_fin_sub_eq_factorial μ

/-- The ideal of `C(I, μ)` is `∑_{i < μ} (Dⁱ I)^{μ!/(μ-i)}` (Villamayor's form). -/
theorem coefficientIdeal_I (I : Ideal R) (μ : ℕ) :
    (c.coefficientIdeal I μ).I = ∑ i : Fin μ, c.Dpow i I ^ (μ.factorial / (μ - (i : ℕ))) := by
  classical
  unfold coefficientIdeal
  rw [MarkedIdeal.wsum_I]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [markedD_I, markedD_m]
  congr 1
  refine (Nat.div_eq_of_eq_mul_left (by have := i.isLt; omega) ?_).symm
  rw [← prod_fin_sub_eq_factorial μ]
  exact (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm

/-- The relation to Kollár's maximal coefficient ideal: each summand `(Dⁱ I)^{μ!/(μ−i)}` has
weight `(μ − i) · μ!/(μ−i) = μ!`, so `C(I, μ) ≤ W_{μ!}(I)` (with parameter `m = μ`). -/
theorem coefficientIdeal_I_le_W (I : Ideal R) (μ : ℕ) :
    (c.coefficientIdeal I μ).I ≤ c.W μ μ.factorial I := by
  rw [c.coefficientIdeal_I, Ideal.sum_eq_sup, Finset.sup_le_iff]
  intro i _
  have hi := i.isLt
  have hdvd : μ - (i : ℕ) ∣ μ.factorial := Nat.dvd_factorial (by omega) (by omega)
  have := c.Dpow_pow_le_W μ ⟨i, by omega⟩ (μ.factorial / (μ - (i : ℕ))) I
  rwa [Fin.val_mk, Nat.mul_div_cancel' hdvd] at this

/-- The local half of [Wlo05, Lemma 2.10.2]: if `μ ≤ ord I` then the closed point lies in
`cosupp C(I, μ)`, since each `Dⁱ I` has order `≥ μ − i` (`le_ord_Dpow`). -/
theorem inCosupp_coefficientIdeal {I : Ideal R} {μ : ℕ} (hI : (μ : ℕ∞) ≤ ord I) :
    (c.coefficientIdeal I μ).InCosupp :=
  MarkedIdeal.inCosupp_wsum fun i => by
    change ((μ - (i : ℕ) : ℕ) : ℕ∞) ≤ ord (c.Dpow i I)
    exact c.le_ord_Dpow hI i.isLt.le

end RegularCoords

end IsLocalRing
