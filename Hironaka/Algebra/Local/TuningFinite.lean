/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Tuning

/-!
# The maximal coefficient ideal as a finite sum

[Kol07, Definition 98] writes `W_s(I) = ∑_{wt(e) ≥ s} ∏ⱼ (Dʲ I)^{eⱼ}` as a sum over all exponent
vectors `e : Fin (m + 1) → ℕ` of weight `wt e = ∑ⱼ (m − j) eⱼ ≥ s`; `RegularCoords.W` of
`Hironaka/Algebra/Local/Tuning.lean` is that supremum. On an analytic manifold the sum has to be a
locally finitely generated ideal sheaf, so this module shows that the supremum is a finite sum: it
suffices to take the exponent vectors with `eⱼ ≤ s` for `j < m` and `e_m = 0` (`tuningExponents m
s`, `iSup_wt_eq_sum_tuningExponents`). Indeed, clamping `e` to `e' = (min (eⱼ, s))_{j<m}`, `e'_m =
0` (`clampExponent`) keeps the weight `≥ s` (if some `eⱼ ≥ s` with `j < m`, the single term
`(m − j) s ≥ s` does; otherwise only the weightless `e_m` changed) and enlarges the product, since
`Pᵃ ⊆ Pᵇ` for `b ≤ a`. The lemma holds for any family `P : Fin (m + 1) → Ideal R` of ideals of a
commutative semiring; the `Dʲ I` play no role.

Used for the maximal coefficient ideal sheaf on manifolds
(`Hironaka/Manifold/IdealSheaf/Tuning.lean`, `Hironaka/Manifold/IdealSheaf/TuningLemmas.lean`,
`Hironaka/Manifold/BlowUp/Transform/TuningTransform.lean`). The statement is not in the sources.
-/

@[expose] public section

namespace IsLocalRing

/-- The exponent vectors that carry `W_s`: `eⱼ ≤ s` for `j < m`, `e_m = 0`, and `wt e ≥ s`. -/
def tuningExponents (m s : ℕ) : Finset (Fin (m + 1) → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (s + 1)).filter fun e => s ≤ wt m e ∧ e (Fin.last m) = 0

theorem mem_tuningExponents {m s : ℕ} {e : Fin (m + 1) → ℕ} :
    e ∈ tuningExponents m s ↔ (∀ j, e j ≤ s) ∧ s ≤ wt m e ∧ e (Fin.last m) = 0 := by
  simp only [tuningExponents, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
    Nat.lt_succ_iff]

/-- The clamp of an exponent vector at `s`, with the weightless last exponent set to `0`. -/
def clampExponent (m s : ℕ) (e : Fin (m + 1) → ℕ) : Fin (m + 1) → ℕ :=
  fun j => if j = Fin.last m then 0 else min (e j) s

theorem clampExponent_le (m s : ℕ) (e : Fin (m + 1) → ℕ) (j : Fin (m + 1)) :
    clampExponent m s e j ≤ e j := by
  unfold clampExponent
  split_ifs
  · exact Nat.zero_le _
  · exact min_le_left _ _

theorem wt_clampExponent_ge {m s : ℕ} {e : Fin (m + 1) → ℕ} (he : s ≤ wt m e) :
    s ≤ wt m (clampExponent m s e) := by
  by_cases h : ∃ j : Fin (m + 1), j ≠ Fin.last m ∧ s ≤ e j
  · obtain ⟨j, hj, hje⟩ := h
    have hj' : (j : ℕ) < m := by
      have := j.isLt
      have : (j : ℕ) ≠ m := fun h' => hj (Fin.ext (by simp [h']))
      omega
    have h1 : (m - (j : ℕ)) * clampExponent m s e j ≤ wt m (clampExponent m s e) :=
      Finset.single_le_sum (f := fun j : Fin (m + 1) => (m - (j : ℕ)) * clampExponent m s e j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h2 : clampExponent m s e j = s := by
      simp [clampExponent, hj, min_eq_right hje]
    rw [h2] at h1
    exact le_trans (Nat.le_mul_of_pos_left s (by omega)) h1
  · push Not at h
    have : wt m (clampExponent m s e) = wt m e := by
      unfold wt
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j = Fin.last m
      · subst hj
        simp
      · have := h j hj
        simp [clampExponent, hj, min_eq_left this.le]
    rw [this]
    exact he

theorem clampExponent_mem_tuningExponents {m s : ℕ} {e : Fin (m + 1) → ℕ} (he : s ≤ wt m e) :
    clampExponent m s e ∈ tuningExponents m s := by
  refine mem_tuningExponents.mpr ⟨fun j => ?_, wt_clampExponent_ge he, by simp [clampExponent]⟩
  unfold clampExponent
  split_ifs
  · exact Nat.zero_le _
  · exact min_le_right _ _

variable {R : Type*} [CommSemiring R]

/-- Products of powers of ideals are antitone in the exponents. -/
theorem prod_pow_le_prod_pow_of_le {ι : Type*} [Fintype ι] (P : ι → Ideal R) {e e' : ι → ℕ}
    (h : ∀ j, e' j ≤ e j) : ∏ j, P j ^ e j ≤ ∏ j, P j ^ e' j := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Ideal.mul_mono (Ideal.pow_le_pow_right (h a)) ih

/-- Kollár's sum over all exponent vectors of weight `≥ s` is the finite sum over
`tuningExponents m s`, for any family `P` of ideals. -/
theorem iSup_wt_eq_sum_tuningExponents (m s : ℕ) (P : Fin (m + 1) → Ideal R) :
    (⨆ (e : Fin (m + 1) → ℕ) (_ : s ≤ wt m e), ∏ j, P j ^ e j) =
      ∑ e ∈ tuningExponents m s, ∏ j, P j ^ e j := by
  refine le_antisymm (iSup₂_le fun e he => ?_) ?_
  · calc ∏ j, P j ^ e j ≤ ∏ j, P j ^ clampExponent m s e j :=
          prod_pow_le_prod_pow_of_le P (clampExponent_le m s e)
      _ ≤ ∑ e ∈ tuningExponents m s, ∏ j, P j ^ e j := by
          rw [Ideal.sum_eq_sup]
          exact Finset.le_sup (f := fun e => ∏ j, P j ^ e j) (clampExponent_mem_tuningExponents he)
  · rw [Ideal.sum_eq_sup]
    exact Finset.sup_le fun e he => le_iSup₂_of_le e (mem_tuningExponents.mp he).2.1 le_rfl

end IsLocalRing
