/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bPhase
public import Hironaka.Resolution.Analytic.OrderReduction.Step21Defs
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.Snc.TotalTransform
import Hironaka.Resolution.Analytic.OrderReduction.Induced
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bExponent
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bLocal
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bTools
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The monomial phase terminates: the measure `Σ_D a_D`

The monomial phase at the mark `1` terminates because each step lowers `Σ_D a_D`, the sum of the
exponents of `𝓘` along the boundary components ([Wlo09, §6, Step 2b]: "the invariant `ν` drops",
and the remarks after [Wlo09, Theorem 2.0.3]; [Kol07, Definition–Lemma 110]). The measure of a
triple `S` is

  `step2bMeasure S = Σ_{k, E^k ≠ ∅} sup_{x ∈ E^k} ord_{E^k} 𝓘 (x)`   (in `ℕ∞`),

the sum over the finitely many nonempty members (the finiteness clause of `BMOClass`) of the
supremum along the member of the order of `𝓘` along it (the supremum over the points of a member
is the maximum of the exponents of its components, the order along a member being constant on its
connected components). The exponents after one step (`Step2bExponent.lean`) give: the supremum of
the new member is one less than that of the top member (`memberSup_inr_add_one_le`), the suprema
of the other members are unchanged (`memberSup_inl_le`), the strict transform of the top member has
supremum `0`; so `step2bMeasure S' + 1 ≤ step2bMeasure S` (`step2bMeasure_stepTriple_add_one_le`).
The measure is finite when the order of `𝓘` is bounded (on a relatively compact open,
`bddAbove_ord_on_compact`: `step2bMeasure_le`), and it is at least `1` while a member is active
(`one_le_step2bMeasure_of_nonempty`). Hence the phase **stabilises** at the fuel `step2bMeasure S`
(`step2bPhase_succ_eq_of_step2bMeasure_le`, `step2bPhase_eq_of_step2bMeasure_le`): the complete
phase is `step2bPhase k` for any `k ≥ step2bMeasure S`.
-/

@[expose] public section

noncomputable section

open Set Topology Filter
open scoped Manifold ContDiff BigOperators

universe u

namespace Hironaka.Manifold

open _root_.Manifold

/-- The order along `D` depends only on the stalk of `D` at the point. -/
theorem _root_.Manifold.IdealSheaf.ordAlongIdeal_congr_stalk_left {X : TopCat}
    {𝒪 : TopCat.Sheaf CommRingCat X}
    (D D' J : IdealSheaf 𝒪) {a : X} (h : D.stalkIdeal a = D'.stalkIdeal a) :
    IdealSheaf.ordAlongIdeal D J a = IdealSheaf.ordAlongIdeal D' J a := by
  simp only [IdealSheaf.ordAlongIdeal, h]

namespace BMOmod

open _root_.Manifold

open Hironaka.Manifold.BD

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The measure -/

section Measure

variable {M : AnalyticManifold.{u} 𝕜 E} (S : AnalyticTriple ψ₀ M)

/-- The supremum along the member `E^k` of the order of `𝓘` along `E^k`: the maximal exponent of the
components of `E^k` (`0` for an empty member). -/
def memberSup (k : S.F.ι) : ℕ∞ :=
  ⨆ x : S.F.hyp k, IdealSheaf.ordAlongIdeal (S.isSnc.1 k).idealSheaf S.I x

/-- **The measure `Σ_D a_D`** of a triple: the sum over its nonempty members of the maximal exponent
along the member ([Wlo09, §6, Step 2b]). -/
def step2bMeasure (hS : AnalyticTriple.BMOClass 1 S) : ℕ∞ :=
  ∑ k ∈ S.F.nonemptyFinset hS.2, memberSup S k

theorem ordAlong_le_memberSup {k : S.F.ι} {x : M} (hx : x ∈ S.F.hyp k) :
    IdealSheaf.ordAlongIdeal (S.isSnc.1 k).idealSheaf S.I x ≤ memberSup S k :=
  le_iSup (fun y : S.F.hyp k => IdealSheaf.ordAlongIdeal (S.isSnc.1 k).idealSheaf S.I y) ⟨x, hx⟩

theorem memberSup_le_step2bMeasure (hS : AnalyticTriple.BMOClass 1 S) {k : S.F.ι}
    (hk : k ∈ S.F.nonemptyFinset hS.2) : memberSup S k ≤ step2bMeasure S hS :=
  Finset.single_le_sum (fun _ _ => zero_le) hk

/-- On a triple whose order is bounded by `A` (every triple restricted to a relatively compact open,
`bddAbove_ord_on_compact`) the measure is at most `(number of nonempty members) · A`; in particular
it is finite. -/
theorem step2bMeasure_le (hS : AnalyticTriple.BMOClass 1 S) {A : ℕ}
    (hA : ∀ x, S.I.ord x ≤ (A : ℕ∞)) :
    step2bMeasure S hS ≤ (S.F.nonemptyFinset hS.2).card • (A : ℕ∞) := by
  refine Finset.sum_le_card_nsmul _ _ _ fun k _ => ?_
  exact iSup_le fun x => (ordAlong_le_ord (S.isSnc.1 k) S.I x.2).trans (hA x)

theorem step2bMeasure_ne_top (hS : AnalyticTriple.BMOClass 1 S) {A : ℕ}
    (hA : ∀ x, S.I.ord x ≤ (A : ℕ∞)) : step2bMeasure S hS ≠ ⊤ := by
  have h : (S.F.nonemptyFinset hS.2).card • (A : ℕ∞) =
      (((S.F.nonemptyFinset hS.2).card * A : ℕ) : ℕ∞) := by
    rw [nsmul_eq_mul, Nat.cast_mul]
  exact ne_top_of_le_ne_top (h ▸ ENat.natCast_ne_top _) (step2bMeasure_le S hS hA)

end Measure

variable [FiniteDimensional 𝕜 E]

/-- While a member is active the measure is at least `1` (the active member is nonempty and carries
a point of order `≥ 1` along it). -/
theorem one_le_step2bMeasure_of_nonempty {M : AnalyticManifold.{u} 𝕜 E} (S : AnalyticTriple ψ₀ M)
    (hS : AnalyticTriple.BMOClass 1 S) (hne : (activeMembers S).Nonempty) :
    1 ≤ step2bMeasure S hS := by
  obtain ⟨j, y, hy⟩ := hne
  have hyj : y ∈ S.F.hyp j := positiveLocus_subset S j hy
  have h1 : ((1 : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (S.isSnc.1 j).idealSheaf S.I y :=
    ((mem_positiveLocus_iff_one_le_ordAlong S).mp hy).2
  have hj : j ∈ S.F.nonemptyFinset hS.2 :=
    (S.F.mem_nonemptyFinset hS.2 _).mpr (Set.nonempty_iff_ne_empty.mp ⟨y, hyj⟩)
  calc (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) := by simp
    _ ≤ _ := h1
    _ ≤ memberSup S j := ordAlong_le_memberSup S hyj
    _ ≤ step2bMeasure S hS := memberSup_le_step2bMeasure S hS hj

/-! ### One step lowers the measure -/

section Step

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hfin : (activeMembers T).Finite)
  (hne : (activeMembers T).Nonempty)

theorem stepTriple_isSnc : (stepTriple T hfin hne).isSnc = isSnc_stepFamily T hfin hne := rfl

/-- The index of a strict transform in the family after the step. -/
def inlIdx (k : T.F.ι) : (stepTriple T hfin hne).F.ι := toLex (Sum.inl k)

/-- The index of the new member in the family after the step. -/
def inrIdx : (stepTriple T hfin hne).F.ι := toLex (Sum.inr PUnit.unit)

theorem inlIdx_def (k : T.F.ι) : inlIdx T hfin hne k = toLex (Sum.inl k) := rfl

theorem inrIdx_def : inrIdx T hfin hne = toLex (Sum.inr PUnit.unit) := rfl

/-- At a point of the centre `Z` the order along `Z` is the order along the top member `E^j`
(they agree near the point, `Z` being open in `E^j`). -/
theorem ordAlong_stepCenter_eq {y : M} (hy : y ∈ step2bCenter T hfin hne) :
    IdealSheaf.ordAlongIdeal (stepCenter T hfin hne).idealSheaf T.I y =
      IdealSheaf.ordAlongIdeal (T.isSnc.1 (topMember T hfin hne)).idealSheaf T.I y := by
  obtain ⟨U, hU, hyU, hsub⟩ := exists_isOpen_inter_subset_positiveLocus T hy
  refine IdealSheaf.ordAlongIdeal_congr_stalk_left _ _ _
    (IsClosedSubmanifold.stalkIdeal_idealSheaf_congr_nhds _ _ hy hU hyU ?_)
  refine Set.Subset.antisymm (Set.inter_subset_inter_left _ (step2bCenter_subset T hfin hne))
    fun z hz => ⟨hsub ⟨hz.2, hz.1⟩, hz.2⟩

/-- The new member's sup is one less than the top member's: `sup_{D'} + 1 ≤ sup_{E^j}`
(`ordAlong_stepIdeal_inr_add_one` at each point of `D' = π⁻¹(Z)`). -/
theorem memberSup_inr_add_one_le :
    memberSup (stepTriple T hfin hne) (inrIdx T hfin hne) + 1 ≤
      memberSup T (topMember T hfin hne) := by
  have hpt : ∀ x' : (stepTriple T hfin hne).F.hyp (inrIdx T hfin hne),
      IdealSheaf.ordAlongIdeal
          ((stepTriple T hfin hne).isSnc.1 (inrIdx T hfin hne)).idealSheaf
          (stepTriple T hfin hne).I x' + 1 ≤ memberSup T (topMember T hfin hne) := by
    intro x'
    have hx' : stepπ T hfin hne x' ∈ step2bCenter T hfin hne := x'.2
    exact (ordAlong_stepIdeal_inr_add_one T hfin hne hx').trans_le
      ((ordAlong_stepCenter_eq T hfin hne hx').trans_le
        (ordAlong_le_memberSup T (step2bCenter_subset T hfin hne hx')))
  by_cases hD : Nonempty ((stepTriple T hfin hne).F.hyp (inrIdx T hfin hne))
  · unfold memberSup
    rw [ENat.iSup_add]
    exact iSup_le hpt
  · have h0 : memberSup (stepTriple T hfin hne) (inrIdx T hfin hne) = 0 := by
      unfold memberSup
      rw [not_nonempty_iff] at hD
      exact iSup_of_empty _
    rw [h0, zero_add]
    obtain ⟨y, hy⟩ := step2bCenter_nonempty T hfin hne
    calc (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) := by simp
      _ ≤ IdealSheaf.ordAlongIdeal (stepCenter T hfin hne).idealSheaf T.I y :=
          one_le_ordAlong_step2bCenter T hfin hne y hy
      _ = _ := ordAlong_stepCenter_eq T hfin hne hy
      _ ≤ _ := ordAlong_le_memberSup T (step2bCenter_subset T hfin hne hy)

/-- The sup of a strict transform is at most the sup of its member (`ordAlong_stepIdeal_inl_of_ne`
for `k ≠ j`; for the top member the strict transform's orders are those of `E^j` off `Z`). -/
theorem memberSup_inl_le (k : T.F.ι) :
    memberSup (stepTriple T hfin hne) (inlIdx T hfin hne k) ≤ memberSup T k := by
  refine iSup_le fun x' => ?_
  have hxk : stepπ T hfin hne x' ∈ T.F.hyp k :=
    HypersurfaceFamily.mem_hyp_of_mem_strictTransform (isBlowUp_blowUpπ ψ₀ _) T.isSnc x'.2
  by_cases hk : k = topMember T hfin hne
  · subst hk
    exact (ordAlong_stepIdeal_inl_top T hfin hne x'.2).trans_le (ordAlong_le_memberSup T hxk)
  · exact (ordAlong_stepIdeal_inl_of_ne T hfin hne hk hxk).trans_le (ordAlong_le_memberSup T hxk)

/-- The strict transform of the top member has sup `0`: its points lie off the positive locus. -/
theorem memberSup_inl_top :
    memberSup (stepTriple T hfin hne) (inlIdx T hfin hne (topMember T hfin hne)) = 0 := by
  refine le_antisymm (iSup_le fun x' => ?_) zero_le
  have hZ := notMem_step2bCenter_of_mem_stepFamily_top T hfin hne x'.2
  have hxj : stepπ T hfin hne x' ∈ T.F.hyp (topMember T hfin hne) :=
    HypersurfaceFamily.mem_hyp_of_mem_strictTransform (isBlowUp_blowUpπ ψ₀ _) T.isSnc x'.2
  exact (ordAlong_stepIdeal_inl_top T hfin hne x'.2).trans_le
    (ordAlong_eq_zero_of_notMem_positiveLocus T hxj hZ).le

/-- A nonempty strict transform lies over a nonempty member. -/
theorem nonemptyFinset_stepTriple_subset (hT : AnalyticTriple.BMOClass 1 T) :
    (stepTriple T hfin hne).F.nonemptyFinset (bmoClass_stepTriple T hfin hne hT).2 ⊆
      (T.F.nonemptyFinset hT.2).image (inlIdx T hfin hne) ∪ {inrIdx T hfin hne} := by
  intro k' hk'
  rw [HypersurfaceFamily.mem_nonemptyFinset] at hk'
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
  rcases hk'' : ofLex k' with k | u
  · left
    have hk'eq : k' = inlIdx T hfin hne k := by rw [inlIdx_def, ← hk'']; rfl
    refine ⟨k, ?_, hk'eq.symm⟩
    rw [HypersurfaceFamily.mem_nonemptyFinset]
    intro hk
    apply hk'
    rw [hk'eq, inlIdx_def]
    change strictTransformSet _ _ (T.F.hyp k) = ∅
    rw [hk, strictTransformSet_empty]
  · right
    rw [inrIdx_def, ← hk'']
    rfl

theorem inlIdx_injective : Function.Injective (inlIdx T hfin hne) := fun _ _ h =>
  Sum.inl.inj (congrArg ofLex h)

/-- **One step of the monomial phase lowers the measure by at least one**:
`step2bMeasure (stepTriple) + 1 ≤ step2bMeasure T` ([Wlo09, §6, Step 2b];
[Kol07, Definition–Lemma 110]). -/
theorem step2bMeasure_stepTriple_add_one_le (hT : AnalyticTriple.BMOClass 1 T) :
    step2bMeasure (stepTriple T hfin hne) (bmoClass_stepTriple T hfin hne hT) + 1 ≤
      step2bMeasure T hT := by
  have hjN : topMember T hfin hne ∈ T.F.nonemptyFinset hT.2 := by
    rw [HypersurfaceFamily.mem_nonemptyFinset]
    obtain ⟨y, hy⟩ := step2bCenter_nonempty T hfin hne
    exact Set.nonempty_iff_ne_empty.mp ⟨y, step2bCenter_subset T hfin hne hy⟩
  have hdisj : Disjoint ((T.F.nonemptyFinset hT.2).image (inlIdx T hfin hne))
      ({inrIdx T hfin hne} : Finset (stepTriple T hfin hne).F.ι) := by
    rw [Finset.disjoint_singleton_right, Finset.mem_image]
    rintro ⟨k, -, hk⟩
    exact Sum.inl_ne_inr (congrArg ofLex hk)
  calc step2bMeasure (stepTriple T hfin hne) (bmoClass_stepTriple T hfin hne hT) + 1
      ≤ (∑ k' ∈ (T.F.nonemptyFinset hT.2).image (inlIdx T hfin hne) ∪ {inrIdx T hfin hne},
          memberSup (stepTriple T hfin hne) k') + 1 :=
        add_le_add (Finset.sum_le_sum_of_subset
          (nonemptyFinset_stepTriple_subset T hfin hne hT)) le_rfl
    _ = (∑ k ∈ T.F.nonemptyFinset hT.2, memberSup (stepTriple T hfin hne) (inlIdx T hfin hne k)) +
          memberSup (stepTriple T hfin hne) (inrIdx T hfin hne) + 1 := by
        rw [Finset.sum_union hdisj, Finset.sum_singleton,
          Finset.sum_image fun _ _ _ _ h => inlIdx_injective T hfin hne h]
    _ = (memberSup (stepTriple T hfin hne) (inlIdx T hfin hne (topMember T hfin hne)) +
          ∑ k ∈ (T.F.nonemptyFinset hT.2).erase (topMember T hfin hne),
            memberSup (stepTriple T hfin hne) (inlIdx T hfin hne k)) +
          memberSup (stepTriple T hfin hne) (inrIdx T hfin hne) + 1 := by
        rw [← Finset.add_sum_erase _ _ hjN]
    _ = (∑ k ∈ (T.F.nonemptyFinset hT.2).erase (topMember T hfin hne),
            memberSup (stepTriple T hfin hne) (inlIdx T hfin hne k)) +
          (memberSup (stepTriple T hfin hne) (inrIdx T hfin hne) + 1) := by
        rw [memberSup_inl_top, zero_add, add_assoc]
    _ ≤ (∑ k ∈ (T.F.nonemptyFinset hT.2).erase (topMember T hfin hne), memberSup T k) +
          memberSup T (topMember T hfin hne) :=
        add_le_add (Finset.sum_le_sum fun k _ => memberSup_inl_le T hfin hne k)
          (memberSup_inr_add_one_le T hfin hne)
    _ = ∑ k ∈ T.F.nonemptyFinset hT.2, memberSup T k := by
        rw [add_comm, Finset.add_sum_erase _ _ hjN]

end Step

/-! ### Stabilisation: the phase is complete at the fuel `step2bMeasure` -/

/-- Termination: once the fuel reaches the measure the phase does not grow,
`step2bPhase (k + 1) = step2bPhase k` for `step2bMeasure T ≤ k`. Induction on `k`: at `k = 0` no
member is active (`one_le_step2bMeasure_of_nonempty`); otherwise the step lowers the measure by
one (`step2bMeasure_stepTriple_add_one_le`). -/
theorem step2bPhase_succ_eq_of_step2bMeasure_le :
    ∀ (k : ℕ) {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
      (hT : AnalyticTriple.BMOClass 1 T), step2bMeasure T hT ≤ k →
      step2bPhase (k + 1) T hT = step2bPhase k T hT
  | 0, M, T, hT, hle => by
    have hne : ¬ (activeMembers T).Nonempty := fun hne => by
      have := (one_le_step2bMeasure_of_nonempty T hT hne).trans hle
      simp at this
    rw [step2bPhase_succ_of_not_nonempty T hT 0 hne, step2bPhase_zero]
  | k + 1, M, T, hT, hle => by
    by_cases hne : (activeMembers T).Nonempty
    · rw [step2bPhase_succ_of_nonempty T hT (k + 1) hne, step2bPhase_succ_of_nonempty T hT k hne]
      congr 1
      refine step2bPhase_succ_eq_of_step2bMeasure_le k _ _ ?_
      have h := (step2bMeasure_stepTriple_add_one_le T (activeMembers_finite T hT) hne hT).trans hle
      rw [Nat.cast_succ] at h
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h
    · rw [step2bPhase_succ_of_not_nonempty T hT (k + 1) hne,
        step2bPhase_succ_of_not_nonempty T hT k hne]

/-- The complete phase: `step2bPhase k` is the same list for every fuel `k ≥ step2bMeasure T`. -/
theorem step2bPhase_eq_of_step2bMeasure_le {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BMOClass 1 T) {k : ℕ} (hk : step2bMeasure T hT ≤ k) (m : ℕ) :
    step2bPhase (k + m) T hT = step2bPhase k T hT := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← add_assoc, step2bPhase_succ_eq_of_step2bMeasure_le (k + m) T hT
      (hk.trans (by exact_mod_cast Nat.le_add_right k m)), ih]

end BMOmod

end Hironaka.Manifold

end
