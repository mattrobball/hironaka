/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.ChartRing
public import Hironaka.Scheme.BlowUp.Defs
public import Hironaka.Scheme.IdealSheaf.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Algebra.Local.Regular
import Hironaka.Scheme.Snc.ChartDerivations
import Hironaka.Scheme.Snc.LocalBlowUpPoint
import Hironaka.Scheme.Snc.StalkDerivations
import Hironaka.Scheme.Snc.TotalTransformData
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The induced coordinates of a chart at a point

[Hau14, Proposition 5.4 (6)] in its coordinate content at an arbitrary point: at a point `a'` of the
exceptional divisor over `a`, in the chart of `x_j` (`F_{a'} = (π^* z_j)`), the **induced
coordinates** are `π^* z_i` for `i ≤ n − k` and `i = j`, and `w_i = π^* z_i / π^* z_j` for the other
centre coordinates; those vanishing at `a'` extend to a regular system of parameters of `𝒪_{B,a'}`
(`exists_isRegularSystemOfParameters_induced`). At a rational point all of them vanish and they are
Hauser's coordinates; at a general point the vanishing ones are part of a system, as in
`Hironaka.Scheme.Snc.EtaleParameters`.

The proof transports to Kollár's chart ring [Kol07, Definition 60]. The reindexing `kollarReindex`
sends Hauser's positions (centre `n − k, …, n − 1`, chart index `j`) to Kollár's (centre
`0, …, k − 1`, chart index `ρ = k − 1`); `exists_stalk_equiv_localization_atPrime` of
`Hironaka.Scheme.Snc.LocalBlowUpPoint` identifies `𝒪_{B,a'}` with `R'_𝔮`, `R' = chartRing y ρ`,
compatibly with `π^*`, and under this identification the induced coordinates are the chart functions
`y_l/y_ρ`, `y_ρ`, `y_m` — for a fibre coordinate by cancelling the nonzero `π^* z_j` in the domain
`𝒪_{B,a'}` (`ringEquiv_apply_eq_of_mul`). The chart functions vanishing at `𝔮` extend to a regular
system of parameters of `R'_𝔮` (`exists_span_eq_maximalIdeal_extend_chartYR` of
`Hironaka.Scheme.Snc.ChartDerivations`, from the derivations of `𝒪_{X,a}` dual to `y`,
`exists_derivation_dual` of `Hironaka.Scheme.Snc.StalkDerivations`), and the equivalence carries
this back to `𝒪_{B,a'}`.

Sources: [Hau14, Proposition 5.4 (6)]; [Hau03, Appendix C (7)]; [Kol07, Definition 60].
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing Ideal Scheme.IdealSheafData

namespace AlgebraicGeometry

section Reindex

variable {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (j : Fin n)

/-- Kollár's chart index `ρ = k − 1` (zero-based: the last of the `k` centre coordinates). -/
def kollarIdx : Fin n := ⟨k - 1, by omega⟩

theorem kollarIdx_val : (kollarIdx hk hkn).val = k - 1 := rfl

/-- Kollár's indexing from Hauser's: the reversal `i ↦ n − 1 − i` sends the last `k` positions
onto the first `k`, followed by the transposition putting `j` at `k − 1`. -/
noncomputable def kollarReindex : Fin n ≃ Fin n :=
  Fin.revPerm.trans (Equiv.swap (Fin.rev j) (kollarIdx hk hkn))

theorem kollarReindex_apply_self : kollarReindex hk hkn j j = kollarIdx hk hkn := by
  change Equiv.swap (Fin.rev j) (kollarIdx hk hkn) (Fin.rev j) = _
  exact Equiv.swap_apply_left _ _

theorem lt_kollarReindex_iff (hj : n - k ≤ j.val) (i : Fin n) :
    (kollarReindex hk hkn j i).val < k ↔ n - k ≤ i.val := by
  have hi := i.2
  have hjn := j.2
  have hri : (Fin.rev i).val = n - (i.val + 1) := Fin.val_rev i
  have hrj : (Fin.rev j).val = n - (j.val + 1) := Fin.val_rev j
  have hρ : (kollarIdx hk hkn).val = k - 1 := rfl
  change (Equiv.swap (Fin.rev j) (kollarIdx hk hkn) (Fin.rev i)).val < k ↔ _
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · have := congrArg Fin.val h1
    omega
  · have := congrArg Fin.val h2
    omega
  · omega

theorem image_kollarReindex (hj : n - k ≤ j.val) :
    kollarReindex hk hkn j '' {i : Fin n | n - k ≤ i.val} = {i : Fin n | i.val < k} := by
  ext i
  constructor
  · rintro ⟨i', hi', rfl⟩
    exact (lt_kollarReindex_iff hk hkn j hj i').mpr hi'
  · intro hi
    refine ⟨(kollarReindex hk hkn j).symm i, ?_, Equiv.apply_symm_apply _ _⟩
    change n - k ≤ ((kollarReindex hk hkn j).symm i).val
    rw [← lt_kollarReindex_iff hk hkn j hj, Equiv.apply_symm_apply]
    exact hi

end Reindex

variable {X : Scheme.{u}}

section Transport

variable {R : Type u} [CommRing R] {n : ℕ} (y : Fin n → R) (ρ : Fin n) (𝔮 : Ideal (chartRing y ρ))
  [𝔮.IsPrime]

/-- The chart function `y_l`, `l ≥ ρ`, is the constant `y_l` in the chart ring. -/
theorem chartYR_of_not_lt {l : Fin n} (hl : ¬ l < ρ) :
    chartYR y ρ l = algebraMap R (chartRing y ρ) (y l) := by
  apply Subtype.ext
  rw [coe_chartYROf, chartYOf_of_not_lt y ρ (y ρ) hl]
  rfl

/-- `y_l · y_ρ = y_l` in the chart ring, for the fibre coordinate `y_l = y_l/y_ρ`, `l < ρ`. -/
theorem chartYR_mul_algebraMap {l : Fin n} (hl : l < ρ) :
    chartYR y ρ l * algebraMap R (chartRing y ρ) (y ρ) = algebraMap R (chartRing y ρ) (y l) := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, coe_chartYROf, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap]
  exact chartY_mul_algebraMap y ρ hl

end Transport

section Generic

variable {R S R' L : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing L]

/-- Transport of a constant along `e ∘ π = h ∘ g`. -/
theorem ringEquiv_apply_eq_of_const (e : S ≃+* L) (π : R →+* S) (g : R →+* R') (h : R' →+* L)
    (hcompat : ∀ c, e (π c) = h (g c)) {w : S} {c : R} (hw : w = π c) {u : R'} (hu : u = g c) :
    e w = h u := by
  subst hw hu
  exact hcompat c

/-- Transport of a ratio along `e ∘ π = h ∘ g`, cancelling the nonzero denominator. -/
theorem ringEquiv_apply_eq_of_mul [IsDomain L] (e : S ≃+* L) (π : R →+* S) (g : R →+* R')
    (h : R' →+* L) (hcompat : ∀ c, e (π c) = h (g c)) {w : S} {ci cj : R} (hT : h (g cj) ≠ 0)
    (h1 : π ci = w * π cj) {u : R'} (h2 : u * g cj = g ci) : e w = h u := by
  have h1' := congrArg e h1
  rw [map_mul, hcompat, hcompat] at h1'
  have h2' := congrArg h h2
  rw [map_mul] at h2'
  exact mul_right_cancel₀ hT (h1'.symm.trans h2'.symm)

end Generic

/-- A reindexing sending the last `k` positions onto the first `k` maps the centre's index set
onto `{i | i < k}`. -/
theorem image_eq_of_lt_iff {n kk : ℕ} (σ : Fin n ≃ Fin n)
    (hσ : ∀ i, (σ i).val < kk ↔ n - kk ≤ i.val) :
    σ '' {i : Fin n | n - kk ≤ i.val} = {i : Fin n | i.val < kk} := by
  ext i
  constructor
  · rintro ⟨i', hi', rfl⟩
    exact (hσ i').mpr hi'
  · intro hi
    refine ⟨σ.symm i, ?_, Equiv.apply_symm_apply _ _⟩
    change n - kk ≤ (σ.symm i).val
    rw [← hσ, Equiv.apply_symm_apply]
    exact hi

section Induced

variable {k : Type u} [Field k] [PerfectField k] (f : X ⟶ Spec (.of k)) [Smooth f]
  (Z : X.IdealSheafData) (a' : blowUp Z) [IsRegularLocalRing ((blowUp Z).presheaf.stalk a')]
  {n kk : ℕ} (hk : 1 ≤ kk) (hkn : kk ≤ n) {z : Fin n → X.presheaf.stalk (blowUpπ Z a')}
  (hz : span (Set.range z) = maximalIdeal (X.presheaf.stalk (blowUpπ Z a')) ∧
    (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk (blowUpπ Z a')))
  (hZa : Z.stalkIdeal (blowUpπ Z a') = span (z '' {i | n - kk ≤ i.val})) {j : Fin n}
  (hj : n - kk ≤ j.val)
  (hF : (Z.comap (blowUpπ Z)).stalkIdeal a' = span {(blowUpπ Z).stalkMap a' (z j)})
  (hne : (blowUpπ Z).stalkMap a' (z j) ≠ 0)

include hk hkn hz hZa hj hF hne

omit hz hj hkn in
/-- The chart-ring model of the point `a'`: for a reindexing `σ` of the coordinates sending the
centre's positions `n − k, …, n − 1` onto `0, …, k − 1` and `j` to `ρ = k − 1` (Kollár's indexing;
`kollarReindex`), and `y = z ∘ σ⁻¹`, the stalk `𝒪_{B,a'}` is `(chartRing y ρ)_𝔮` for a prime `𝔮`
over `𝔪_a`, compatibly with `π^*`, and the induced coordinates `w` of the `z_j`-chart correspond
to the chart functions `y_{σ i}`. -/
theorem exists_chartRing_model (σ : Fin n ≃ Fin n) (hσ : ∀ i, (σ i).val < kk ↔ n - kk ≤ i.val)
    (ρ : Fin n) (hρ : ρ.val = kk - 1) (hσj : σ j = ρ)
    (w : Fin n → (blowUp Z).presheaf.stalk a')
    (hw : ∀ i : Fin n, i.val < n - kk ∨ i = j → w i = (blowUpπ Z).stalkMap a' (z i))
    (hw' : ∀ i : Fin n, n - kk ≤ i.val → i ≠ j →
      (blowUpπ Z).stalkMap a' (z i) = w i * (blowUpπ Z).stalkMap a' (z j)) :
    ∃ (𝔮 : Ideal (chartRing (z ∘ σ.symm) ρ)) (_ : 𝔮.IsPrime)
      (e : (blowUp Z).presheaf.stalk a' ≃+* Localization.AtPrime 𝔮),
      𝔮.comap (algebraMap (X.presheaf.stalk (blowUpπ Z a')) (chartRing (z ∘ σ.symm) ρ)) =
        maximalIdeal (X.presheaf.stalk (blowUpπ Z a')) ∧
      (∀ c : X.presheaf.stalk (blowUpπ Z a'), e ((blowUpπ Z).stalkMap a' c) =
        algebraMap (chartRing (z ∘ σ.symm) ρ) (Localization.AtPrime 𝔮) (algebraMap _ _ c)) ∧
      ∀ i, e (w i) = algebraMap (chartRing (z ∘ σ.symm) ρ) (Localization.AtPrime 𝔮)
        (chartYR (z ∘ σ.symm) ρ (σ i)) := by
  classical
  have hyσ : ∀ i, (z ∘ σ.symm) (σ i) = z i :=
    fun i => by simp only [Function.comp_apply, Equiv.symm_apply_apply]
  have hyρ : (z ∘ σ.symm) ρ = z j := by rw [← hσj, hyσ]
  have hZ' : Z.stalkIdeal (blowUpπ Z a') = span ((z ∘ σ.symm) '' {i | i.val < kk}) := by
    rw [hZa, ← image_eq_of_lt_iff σ hσ, Set.image_image]
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  have hF' : (Z.comap (blowUpπ Z)).stalkIdeal a' =
      span {(blowUpπ Z).stalkMap a' ((z ∘ σ.symm) ρ)} := by
    rw [hyρ]
    exact hF
  have hρ' : ρ.val + 1 = kk := by omega
  obtain ⟨𝔮, h𝔮, e, hcomap, hcompat⟩ :=
    exists_stalk_equiv_localization_atPrime Z a' (z ∘ σ.symm) hZ' ρ hρ' hF'
  refine ⟨𝔮, h𝔮, e, hcomap, hcompat, fun i => ?_⟩
  by_cases hi : i.val < n - kk ∨ i = j
  · -- `w_i = π^* z_i` and `y_{σ i}` is a constant chart function
    have hlt : ¬ σ i < ρ := by
      rcases hi with hi | rfl
      · intro hlt
        have h1 := (hσ i).mp (lt_of_lt_of_le hlt (by omega))
        omega
      · rw [hσj]
        exact lt_irrefl _
    refine ringEquiv_apply_eq_of_const e ((blowUpπ Z).stalkMap a').hom _ _ hcompat (hw i hi) ?_
    rw [chartYR_of_not_lt _ _ hlt, hyσ]
  · push Not at hi
    have hlt : σ i < ρ := by
      have h1 := (hσ i).mpr hi.1
      have h2 : σ i ≠ ρ := fun h => hi.2 (σ.injective (h.trans hσj.symm))
      rw [Fin.lt_def]
      have h3 := Fin.val_ne_of_ne h2
      omega
    -- cancel the nonzero `π^* z_j`
    have hreg : IsRegularLocalRing (Localization.AtPrime 𝔮) := IsRegularLocalRing.of_ringEquiv e
    have hT : e ((blowUpπ Z).stalkMap a' (z j)) ≠ 0 :=
      fun h => hne (e.injective (by rw [h, map_zero]))
    rw [hcompat, ← hyρ] at hT
    have h1 := hw' i hi.1 hi.2
    rw [← hyσ i, ← hyρ] at h1
    exact ringEquiv_apply_eq_of_mul e ((blowUpπ Z).stalkMap a').hom _ _ hcompat hT h1
      (chartYR_mul_algebraMap (z ∘ σ.symm) ρ hlt)

include f in
/-- [Hau14, Proposition 5.4 (6)], the coordinate content at an arbitrary (not necessarily rational)
point: the induced coordinates of the `z_j`-chart vanishing at `a'` extend to a regular system of
parameters of `𝒪_{B,a'}`. -/
theorem exists_isRegularSystemOfParameters_induced (w : Fin n → (blowUp Z).presheaf.stalk a')
    (hw : ∀ i : Fin n, i.val < n - kk ∨ i = j → w i = (blowUpπ Z).stalkMap a' (z i))
    (hw' : ∀ i : Fin n, n - kk ≤ i.val → i ≠ j →
      (blowUpπ Z).stalkMap a' (z i) = w i * (blowUpπ Z).stalkMap a' (z j)) :
    ∃ (m : ℕ) (z' : Fin m → (blowUp Z).presheaf.stalk a'),
      (span (Set.range z') = maximalIdeal ((blowUp Z).presheaf.stalk a') ∧
        (m : WithBot ℕ∞) = ringKrullDim ((blowUp Z).presheaf.stalk a')) ∧
      ∃ σ : {i : Fin n // w i ∈ maximalIdeal ((blowUp Z).presheaf.stalk a')} → Fin m,
        Function.Injective σ ∧ ∀ i, z' (σ i) = w i.1 := by
  classical
  have hσ1 := lt_kollarReindex_iff hk hkn j hj
  have hσ2 := kollarReindex_apply_self hk hkn j
  have hρ1 := kollarIdx_val hk hkn
  generalize kollarReindex hk hkn j = σ at hσ1 hσ2
  generalize kollarIdx hk hkn = ρ at hσ2 hρ1
  obtain ⟨𝔮, h𝔮, e, -, hcompat, hE⟩ :=
    exists_chartRing_model Z a' hk hZa hF hne σ hσ1 ρ hρ1 hσ2 w hw hw'
  have hyspan : maximalIdeal (X.presheaf.stalk (blowUpπ Z a')) =
      span (Set.range (z ∘ σ.symm)) := by
    rw [← hz.1, Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
  have hreg : IsRegularLocalRing (Localization.AtPrime 𝔮) := IsRegularLocalRing.of_ringEquiv e
  -- the derivations dual to `y` and the chart-ring parameters
  let _ := f.stalkAlgebra (blowUpπ Z a')
  obtain ⟨D, hD⟩ := exists_derivation_dual f (blowUpπ Z a') (z ∘ σ.symm) hyspan hz.2
  obtain ⟨m, z'', hz'', σ'', hσ''inj, hσ''⟩ :=
    exists_span_eq_maximalIdeal_extend_chartYR (z ∘ σ.symm) ρ D hD 𝔮
  -- transport back along `e`
  refine ⟨m, fun l => e.symm (z'' l), ⟨?_, ?_⟩, ?_⟩
  · rw [Set.range_comp', ← Ideal.map_span, hz''.1, map_maximalIdeal_ringEquiv e]
  · rw [hz''.2, ringKrullDim_eq_of_ringEquiv e]
  · have hmem : ∀ i : {i : Fin n // w i ∈ maximalIdeal ((blowUp Z).presheaf.stalk a')},
        algebraMap (chartRing (z ∘ σ.symm) ρ) (Localization.AtPrime 𝔮)
          (chartYR (z ∘ σ.symm) ρ (σ i.1)) ∈ maximalIdeal (Localization.AtPrime 𝔮) := by
      rintro ⟨i₀, hi₀⟩
      rw [← map_maximalIdeal_ringEquiv e, Ideal.map_symm, Ideal.mem_comap, hE i₀] at hi₀
      exact hi₀
    refine ⟨fun i => σ'' ⟨σ i.1, hmem i⟩, fun i₁ i₂ h => ?_, fun i => ?_⟩
    · have := hσ''inj h
      rw [Subtype.mk.injEq] at this
      exact Subtype.ext (σ.injective this)
    · change e.symm (z'' (σ'' ⟨σ i.1, hmem i⟩)) = w i.1
      rw [hσ'' ⟨σ i.1, hmem i⟩, ← hE i.1, e.symm_apply_apply]

end Induced

end AlgebraicGeometry
