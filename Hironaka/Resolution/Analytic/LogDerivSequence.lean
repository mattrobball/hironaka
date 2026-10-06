/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Order
public import Hironaka.Manifold.FiniteSuccession.Restrict.CongrChart
public import Hironaka.Manifold.FiniteSuccession.Restrict.Restrict
public import Hironaka.Manifold.IdealSheaf.Deriv
public import Hironaka.Manifold.IdealSheaf.LogDeriv
public import Hironaka.Manifold.IdealSheaf.Monoid
import Hironaka.Manifold.BlowUp.Transform.DerivTransform
import Hironaka.Manifold.BlowUp.Transform.LogDerivBlowUp
import Hironaka.Manifold.BlowUp.Transform.LogDerivTransform
import Hironaka.Manifold.BlowUp.Transform.MarkedAlgebra
import Hironaka.Manifold.FiniteSuccession.DerivTransform
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.CosupportDeriv
import Hironaka.Manifold.IdealSheaf.DerivLemmas
import Hironaka.Manifold.IdealSheaf.LogDerivLemmas
import Hironaka.Manifold.IdealSheaf.LogDerivRestrict
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Algebraic.Kol07.Theorem88Sequence
import Hironaka.Resolution.Analytic.MaximalContact.MarkedOneLemmas
import Hironaka.Resolution.Analytic.Restrict.GoingDown
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Logarithmic derivatives along a blow-up sequence: Kollár's (87.3), Theorem 88 and Corollary 89

For a smooth hypersurface `S` and a sequence `Π` of blowings-up of order `≥ m` for `(I, m)` whose
centres lie in the strict transforms `S_i` of `S`, the logarithmic derivatives `D(−log S_i)` (the
derivations preserving the ideal of `S_i`, [Kol07, 87]) interact with the marked transforms as
follows:

* `markedTransformSeq_logDerivIter_le`: the inclusion (87.3) of [Kol07, 87] along the sequence,
  `Π_*^{-1}(D^j(−log S)(I), m − j) ⊆ D^j(−log S_i)(Π_*^{-1}(I, m))`, by induction on the stage
  with the one-blowing-up inclusion (`birationalTransform_logDerivIter_le`) and the monotonicity of
  the marked transform, as Kollár's Theorem 76 is iterated in
  `Hironaka/Manifold/FiniteSuccession/DerivTransform.lean`;
* `iteratedDeriv_markedTransformSeq_eq_sum`: **Theorem 88** [Kol07, Theorem 88] along the sequence,
  `D^s(Π_*^{-1}(I, m)) = ∑_{j=0}^{s} D^{s−j}(−log S_r)(Π_*^{-1}(D^j I, m − j))`, by Kollár's
  induction on the number of blowings-up: at the stage `i + 1` the one-blowing-up formula for `π_i`
  expresses `D^s(Π_{i+1})` by the `D^{s−j}(−log S_{i+1})(π_{i*}^{-1}(D^j Π_i, m − j))`; the
  induction hypothesis writes `D^j Π_i` as a sum, the marked transform of a sum is the sum of the
  marked transforms, each `π_{i*}^{-1}(D^{j−l}(−log S_i)(·), m − j)` lies in
  `D^{j−l}(−log S_{i+1})(π_{i*}^{-1}(·, m − l))` by (87.3), and
  `D^{s−j}(−log S_{i+1}) D^{j−l}(−log S_{i+1}) = D^{s−l}(−log S_{i+1})` collapses the double sum;
  the reverse inclusion is Theorem 76 with the containment `D^t(−log S) ⊆ D^t`. A prefix-bounded
  form (`iteratedDeriv_markedTransformSeq_eq_sum_of_forall_lt`) assumes the order clause only at
  the stages before the one considered;
* `cosupp_markedTransformSeq_inter_eq_iInter`: **Corollary 89** [Kol07, Corollary 89],
  `S_r ∩ cosupp(Π_*^{-1}(I, m), m) = ⋂_{j<m} cosupp((Π|_{S_r})_*^{-1}((D^j I)|_S, m − j), m − j)`:
  Theorem 88 at `s = m − 1` restricted to `S_r` through (87.1) (restriction carries `D(−log S)`
  to `D`) and the restriction of the marked transforms to the strict transforms
  (`markedTransformSeq_pullback_restrictIncl`, Kollár's Lemma 62 along the sequence), read through
  `cosupp(I, m) = cosupp(D^{m−1}(I), 1)` [Kol07, Lemma 74 (3)] on both sides, with the cosupport
  of a restriction the preimage of the cosupport and the cosupport of a finite sum the intersection
  of the cosupports (the stalks being local rings).

Corollary 89 is the identity by which the going-up theorem [Kol07, Theorem 84] recognizes the
points of order `≥ m` on a hypersurface of maximal contact.
-/

public section

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

/-! ### Finite sums of ideals and of ideal sheaves -/

namespace Ideal

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- In a local ring a finite sup of ideals is the unit ideal iff one of them is (the stalk form of
"the cosupport of a sum is the intersection of the cosupports", property (4) of the cosupport in
[Kol07, Definition 59]). -/
theorem finset_sup_eq_top_iff_of_isLocalRing {ι : Type*} (F : Finset ι) (f : ι → Ideal R) :
    F.sup f = ⊤ ↔ ∃ j ∈ F, f j = ⊤ := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have hle : F.sup f ≤ IsLocalRing.maximalIdeal R :=
      Finset.sup_le fun j hj => IsLocalRing.le_maximalIdeal (hne j hj)
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ hle))
  · rintro ⟨j, hj, hjt⟩
    exact top_le_iff.mp (hjt ▸ Finset.le_sup (f := f) hj)

end Ideal

namespace Manifold.IdealSheaf

variable {X : TopCat} {𝒪 : TopCat.Sheaf CommRingCat X}

/-- A finite sum of ideal sheaves lies in `K` when every summand does (the sum of ideal sheaves is
the stalkwise sup; the summands lie in the sum by Mathlib's `Finset.single_le_sum`). -/
theorem finset_sum_le {ι : Type*} {F : Finset ι} {G : ι → IdealSheaf 𝒪} {K : IdealSheaf 𝒪}
    (h : ∀ j ∈ F, G j ≤ K) : ∑ i ∈ F, G i ≤ K := by
  rw [le_def]
  intro x
  rw [stalkIdeal_finset_sum, Ideal.sum_eq_sup]
  exact Finset.sup_le fun j hj => le_def.mp (h j hj) x

/-- `1 ≤ ord_x J` iff `x` lies in the cosupport of `J`. -/
theorem one_le_ord_iff_mem_support [∀ x : X, IsLocalRing (𝒪.presheaf.stalk x)]
    (J : IdealSheaf 𝒪) (x : X) : (1 : ℕ∞) ≤ J.ord x ↔ x ∈ J.support := by
  rw [Order.one_le_iff_ne_zero, Ne, ord_eq_zero_iff, not_not]

/-- The cosupport of a finite sum is the intersection of the cosupports (property (4) of the
cosupport in [Kol07, Definition 59]), read at a point: the stalks are local rings. -/
theorem mem_support_finset_sum_iff [∀ x : X, IsLocalRing (𝒪.presheaf.stalk x)] {ι : Type*}
    (F : Finset ι) (G : ι → IdealSheaf 𝒪) (x : X) :
    x ∈ (∑ i ∈ F, G i).support ↔ ∀ j ∈ F, x ∈ (G j).support := by
  simp only [mem_support, stalkIdeal_finset_sum, Ideal.sum_eq_sup, Ne,
    Ideal.finset_sup_eq_top_iff_of_isLocalRing]
  push Not
  rfl

end Manifold.IdealSheaf

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M]

/-! ### The logarithmic derivative of a finite sum; pull-backs of finite sums -/

/-- `D^t(−log S)` of a finite sum lies in the sum of the `D^t(−log S)`s
(`Ideal.logDerivativeIter_iSup_le`, stalkwise). -/
theorem IdealSheaf.logDerivIter_finset_sum_le {S : Set M} (hS : IsClosedSubmanifold ψ S 1)
    {ι : Type*} (F : Finset ι) (G : ι → IdealSheaf (structureSheaf 𝕜 E M)) (t : ℕ) :
    IdealSheaf.logDerivIter E ψ hS t (∑ i ∈ F, G i) ≤
      ∑ i ∈ F, IdealSheaf.logDerivIter E ψ hS t (G i) := by
  rw [IdealSheaf.le_def]
  intro a
  rw [IdealSheaf.stalkIdeal_logDerivIter, IdealSheaf.stalkIdeal_finset_sum,
    IdealSheaf.stalkIdeal_finset_sum, Ideal.sum_eq_sup, Ideal.sum_eq_sup, Finset.sup_eq_iSup,
    Finset.sup_eq_iSup]
  refine (Ideal.logDerivativeIter_iSup_le _ _ _).trans (iSup_mono fun i =>
    (Ideal.logDerivativeIter_iSup_le _ _ _).trans (iSup_mono fun _ => ?_))
  rw [IdealSheaf.stalkIdeal_logDerivIter]

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- `cosupp(I, m) = cosupp(D^{m−1}(I), 1)` [Kol07, Lemma 74 (3)] at the level of orders:
`ord_a J ≥ m` iff `ord_a D^{m−1} J ≥ 1`, for `1 ≤ m`. -/
theorem IdealSheaf.le_ord_iff_one_le_ord_iteratedDeriv [IsManifold 𝓘(𝕜, E) ω M]
    [FiniteDimensional 𝕜 E] (J : IdealSheaf (structureSheaf 𝕜 E M)) {m : ℕ} (hm : 1 ≤ m) (a : M) :
    (m : ℕ∞) ≤ J.ord a ↔ (1 : ℕ∞) ≤ (J.iteratedDeriv (m - 1)).ord a := by
  rw [one_le_ord_iff_mem_support, support_iteratedDeriv (J := J) hm]
  rfl

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {N : Type u} [TopologicalSpace N]
  [ChartedSpace E' N] [IsManifold 𝓘(𝕜, E') ω N] (φ : N → M) (hφ : ContMDiff 𝓘(𝕜, E') 𝓘(𝕜, E) ω φ)

omit [IsManifold 𝓘(𝕜, E) ω M] [IsManifold 𝓘(𝕜, E') ω N] in
/-- Pull-back commutes with finite sums. -/
theorem IdealSheaf.pullback_finset_sum {ι : Type*} (F : Finset ι)
    (G : ι → IdealSheaf (structureSheaf 𝕜 E M)) :
    (∑ i ∈ F, G i).pullback φ hφ = ∑ i ∈ F, (G i).pullback φ hφ := by
  refine IdealSheaf.ext fun b => ?_
  rw [IdealSheaf.stalkIdeal_pullback, IdealSheaf.stalkIdeal_finset_sum,
    IdealSheaf.stalkIdeal_finset_sum, Ideal.sum_eq_sup, Ideal.sum_eq_sup, Finset.sup_eq_iSup,
    Finset.sup_eq_iSup, Ideal.map_iSup]
  refine iSup_congr fun i => ?_
  rw [Ideal.map_iSup]
  exact iSup_congr fun _ => (IdealSheaf.stalkIdeal_pullback φ hφ _ b).symm

end Manifold

/-! ### Along a succession -/

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} [FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E}
  (B : FiniteSuccession M) {S : Set M} (hS : IsClosedSubmanifold ψ S 1) (hc : B.CentersIn S)
  {I E₀ : IdealSheaf M} {m : ℕ}

omit [FiniteDimensional 𝕜 E] hS hc in
/-- The order clause (4′) of [Kol07, Definition 66] at a stage, for the centre read in the chart
`ψ`. -/
theorem le_ordAlong_congr_chart_of_le_ordAlong (i : Fin B.length)
    (h4 : ∀ a ∈ (B.center i).support, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (B.center i)
      (B.markedTransformSeq I m i.castSucc) a) :
    ∀ a ∈ (B.center i).support, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
      ((B.isClosedSubmanifold_center i).congr_chart ψ).idealSheaf
      (B.markedTransformSeq I m i.castSucc) a := by
  intro a ha
  rw [((B.isClosedSubmanifold_center i).congr_chart ψ).idealSheaf_eq_of_set
    (B.isClosedSubmanifold_center i), B.idealSheaf_center]
  exact h4 a ha

omit [FiniteDimensional 𝕜 E] hS hc in
/-- The order hypothesis of [Kol07, Definition 66] at a stage, for the centre read in the chart `ψ`
(`le_ordAlong_congr_chart_of_le_ordAlong` with the order clause (4′) of `hge`). -/
theorem IsOfOrderGe.le_ordAlong_congr_chart (hge : B.IsOfOrderGe I m E₀) (i : Fin B.length) :
    ∀ a ∈ (B.center i).support, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
      ((B.isClosedSubmanifold_center i).congr_chart ψ).idealSheaf
      (B.markedTransformSeq I m i.castSucc) a :=
  le_ordAlong_congr_chart_of_le_ordAlong (ψ := ψ) B i fun _ ha => hge.le_ordAlong i ha

omit [FiniteDimensional 𝕜 E] hS hc in
/-- The marked transform at a step, with the centre read in the chart `ψ`
(`MarkedIdealSheaf.birationalTransform_congr`). -/
theorem birationalTransform_step_congr_chart (i : Fin B.length)
    (J : IdealSheaf (B.stage i.castSucc)) (k : ℕ) :
    (MarkedIdealSheaf.birationalTransform (B.isClosedSubmanifold_center i) (B.isBlowUp_map i)
        ⟨J, k⟩).I =
      (MarkedIdealSheaf.birationalTransform ((B.isClosedSubmanifold_center i).congr_chart ψ)
        ((B.isBlowUp_map i).congr_chart ψ) ⟨J, k⟩).I := by
  rw [MarkedIdealSheaf.birationalTransform_congr (B.isClosedSubmanifold_center i)
    ((B.isClosedSubmanifold_center i).congr_chart ψ) rfl (B.isBlowUp_map i)
    ((B.isBlowUp_map i).congr_chart ψ)]

/-- The inclusion (87.3) of [Kol07, 87] along a sequence: for `Π` of order `≥ m` for `(I, m)` whose
centres lie in the strict transforms `S_i` of the hypersurface `S`, and `j ≤ m`,
`Π_*^{-1}(D^j(−log S)(I), m − j) ⊆ D^j(−log S_i)(Π_*^{-1}(I, m))` at every stage `i`. The
algebraic counterpart is `markedTransformSeq_logDerivativeIter_le`. -/
theorem markedTransformSeq_logDerivIter_le (hge : B.IsOfOrderGe I m E₀) {j : ℕ} (hj : j ≤ m)
    (i : Fin (B.length + 1)) :
    B.markedTransformSeq (IdealSheaf.logDerivIter E ψ hS j I) (m - j) i ≤
      IdealSheaf.logDerivIter E ψ (B.isClosedSubmanifold_strictTransformSeq S hS hc i) j
        (B.markedTransformSeq I m i) := by
  induction i using Fin.induction with
  | zero => exact le_rfl
  | succ i ih =>
    have hZ := (B.isClosedSubmanifold_center i).congr_chart ψ
    have hπ := (B.isBlowUp_map i).congr_chart ψ
    have hS' : IsClosedSubmanifold ψ
        (strictTransformSet (B.map i) (B.center i).support (B.strictTransformSeq S i.castSucc)) 1 :=
      B.isClosedSubmanifold_strictTransformSeq S hS hc i.succ
    rw [markedTransformSeq_succ, markedTransformSeq_succ,
      B.birationalTransform_step_congr_chart (ψ := ψ),
      B.birationalTransform_step_congr_chart (ψ := ψ)]
    have hmI := IsOfOrderGe.le_ordAlong_congr_chart (ψ := ψ) B hge i
    have hmL : ∀ a ∈ (B.center i).support, ((m - j : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
        ((B.isClosedSubmanifold_center i).congr_chart ψ).idealSheaf
        (IdealSheaf.logDerivIter E ψ (B.isClosedSubmanifold_strictTransformSeq S hS hc i.castSucc)
          j (B.markedTransformSeq I m i.castSucc)) a :=
      fun a ha => IdealSheaf.le_ordAlongIdeal_of_le
        (IdealSheaf.logDerivIter_le_iteratedDeriv E ψ _ j _)
        (le_ordAlongIdeal_iteratedDeriv _ _ ha hj (hmI a ha))
    exact (birationalTransform_mono hZ hπ ih hmL).trans
      (birationalTransform_logDerivIter_le hZ hπ
        (B.isClosedSubmanifold_strictTransformSeq S hS hc i.castSucc) (hc i) hS' _ hmI hj)

/-- **Theorem 88** [Kol07, Theorem 88] along a sequence, in prefix-bounded form: for `Π` whose
centres lie in the strict transforms `S_i` of the hypersurface `S`, a stage `i` such that the
marked transforms of `(I, m)` have order `≥ m` along the centres of the steps before `i` (the
order clause (4′) on the prefix, with no normal-crossings clause), and `s ≤ m`,
`D^s(Π_*^{-1}(I, m)) = ∑_{j=0}^{s} D^{s−j}(−log S_i)(Π_*^{-1}(D^j I, m − j))` at the stage `i`.
Kollár's induction on the number of blowings-up; the step from `i` to `i + 1` uses (4′) at the
step `i` only, through the prefix-bounded form of Corollary 77. -/
theorem iteratedDeriv_markedTransformSeq_eq_sum_of_forall_lt {s : ℕ} (hs : s ≤ m)
    (i : Fin (B.length + 1))
    (h4 : ∀ i' : Fin B.length, i'.1 < i.1 → ∀ a ∈ (B.center i').support,
      (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (B.center i') (B.markedTransformSeq I m i'.castSucc) a) :
    (B.markedTransformSeq I m i).iteratedDeriv s =
      ∑ j ∈ Finset.range (s + 1),
        IdealSheaf.logDerivIter E ψ (B.isClosedSubmanifold_strictTransformSeq S hS hc i) (s - j)
          (B.markedTransformSeq (I.iteratedDeriv j) (m - j) i) := by
  induction i using Fin.induction generalizing s with
  | zero =>
    -- stage `0`: the `j = s` summand is `D^s I` and every summand lies in `D^s I`
    refine le_antisymm (le_trans (le_of_eq ?_)
      (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_range_succ_iff.mpr le_rfl)))
      (IdealSheaf.finset_sum_le fun j hj => ?_)
    · rw [Nat.sub_self, IdealSheaf.logDerivIter_zero]
      rfl
    · have hj' := Finset.mem_range_succ_iff.mp hj
      refine (IdealSheaf.logDerivIter_le_iteratedDeriv E ψ _ _ _).trans (le_of_eq ?_)
      change (I.iteratedDeriv j).iteratedDeriv (s - j) = I.iteratedDeriv s
      rw [← IdealSheaf.iteratedDeriv_add, Nat.sub_add_cancel hj']
  | succ i ih =>
    have h4i : ∀ a ∈ (B.center i).support, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (B.center i)
        (B.markedTransformSeq I m i.castSucc) a :=
      h4 i (by rw [Fin.val_succ]; exact Nat.lt_succ_self _)
    have h4lt : ∀ i' : Fin B.length, i'.1 < i.castSucc.1 → ∀ a ∈ (B.center i').support,
        (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (B.center i')
          (B.markedTransformSeq I m i'.castSucc) a :=
      fun i' hi' => h4 i' (by rw [Fin.val_succ]; rw [Fin.val_castSucc] at hi'; omega)
    have hmI := le_ordAlong_congr_chart_of_le_ordAlong (ψ := ψ) B i h4i
    have hmD : ∀ l ≤ m, ∀ a ∈ (B.center i).support, ((m - l : ℕ) : ℕ∞) ≤
        IdealSheaf.ordAlongIdeal ((B.isClosedSubmanifold_center i).congr_chart ψ).idealSheaf
          (B.markedTransformSeq (I.iteratedDeriv l) (m - l) i.castSucc) a :=
      fun l hl => le_ordAlong_congr_chart_of_le_ordAlong (ψ := ψ) B i
        (le_ordAlong_iteratedDeriv_of_le_of_le_ordAlong hl i h4i
          (markedTransformSeq_iteratedDeriv_le_of_forall_lt hl i.castSucc h4lt))
    have hS' : IsClosedSubmanifold ψ
        (strictTransformSet (B.map i) (B.center i).support (B.strictTransformSeq S i.castSucc)) 1 :=
      B.isClosedSubmanifold_strictTransformSeq S hS hc i.succ
    -- the one-blowing-up Theorem 88 at the step, its right side read on `S_{i+1}` as a set
    have h88 := iteratedDeriv_birationalTransform_eq_sum
      ((B.isClosedSubmanifold_center i).congr_chart ψ) ((B.isBlowUp_map i).congr_chart ψ)
      (B.isClosedSubmanifold_strictTransformSeq S hS hc i.castSucc) (hc i) hS'
      (B.markedTransformSeq I m i.castSucc) hmI hs
    replace h88 := (id h88 : _ = ∑ j ∈ Finset.range (s + 1),
      IdealSheaf.logDerivIter E ψ (B.isClosedSubmanifold_strictTransformSeq S hS hc i.succ) (s - j)
        (MarkedIdealSheaf.birationalTransform ((B.isClosedSubmanifold_center i).congr_chart ψ)
          ((B.isBlowUp_map i).congr_chart ψ)
          ⟨(B.markedTransformSeq I m i.castSucc).iteratedDeriv j, m - j⟩).I)
    simp only [markedTransformSeq_succ, B.birationalTransform_step_congr_chart (ψ := ψ)]
    rw [h88]
    refine le_antisymm (IdealSheaf.finset_sum_le fun j hj => ?_)
      (IdealSheaf.finset_sum_le fun l hl => ?_)
    · -- the `j`-th summand of the one-blowing-up formula, with `D^j Π_i` expanded by induction
      have hj' : j ≤ s := Finset.mem_range_succ_iff.mp hj
      have hjm : j ≤ m := hj'.trans hs
      have hsum := birationalTransform_finset_sum
        ((B.isClosedSubmanifold_center i).congr_chart ψ) ((B.isBlowUp_map i).congr_chart ψ)
        (Finset.range (j + 1))
        (fun l => IdealSheaf.logDerivIter E ψ
          (B.isClosedSubmanifold_strictTransformSeq S hS hc i.castSucc) (j - l)
          (B.markedTransformSeq (I.iteratedDeriv l) (m - l) i.castSucc)) (m - j)
        (fun l hl a ha => by
          have hl' : l ≤ j := Finset.mem_range_succ_iff.mp hl
          have := IdealSheaf.le_ordAlongIdeal_of_le
            (IdealSheaf.logDerivIter_le_iteratedDeriv E ψ
              (B.isClosedSubmanifold_strictTransformSeq S hS hc i.castSucc) (j - l) _)
            (le_ordAlongIdeal_iteratedDeriv _ _ ha (Nat.sub_le_sub_right hjm l)
              (hmD l (hl'.trans hjm) a ha))
          rwa [show m - l - (j - l) = m - j by omega] at this)
      rw [ih hjm h4lt, hsum]
      refine (IdealSheaf.logDerivIter_finset_sum_le _ _ _ _).trans
        (IdealSheaf.finset_sum_le fun l hl => ?_)
      have hl' : l ≤ j := Finset.mem_range_succ_iff.mp hl
      -- (87.3) at the step for `(Π_i(D^l I, m − l), m − l)` and `j − l`
      have h873 := birationalTransform_logDerivIter_le
        ((B.isClosedSubmanifold_center i).congr_chart ψ) ((B.isBlowUp_map i).congr_chart ψ)
        (B.isClosedSubmanifold_strictTransformSeq S hS hc i.castSucc) (hc i) hS'
        (B.markedTransformSeq (I.iteratedDeriv l) (m - l) i.castSucc) (hmD l (hl'.trans hjm))
        (Nat.sub_le_sub_right hjm l)
      rw [show m - l - (j - l) = m - j by omega] at h873
      replace h873 := (id h873 : _ ≤ IdealSheaf.logDerivIter E ψ
        (B.isClosedSubmanifold_strictTransformSeq S hS hc i.succ) (j - l) _)
      refine (IdealSheaf.logDerivIter_mono E ψ
        (B.isClosedSubmanifold_strictTransformSeq S hS hc i.succ) (s - j) h873).trans ?_
      rw [IdealSheaf.logDerivIter_logDerivIter, show s - j + (j - l) = s - l by omega]
      exact Finset.single_le_sum (fun _ _ => bot_le) (f := fun j => IdealSheaf.logDerivIter E ψ
        (B.isClosedSubmanifold_strictTransformSeq S hS hc i.succ) (s - j)
        (MarkedIdealSheaf.birationalTransform ((B.isClosedSubmanifold_center i).congr_chart ψ)
          ((B.isBlowUp_map i).congr_chart ψ)
          ⟨B.markedTransformSeq (I.iteratedDeriv j) (m - j) i.castSucc, m - j⟩).I)
        (Finset.mem_range_succ_iff.mpr (hl'.trans hj'))
    · -- the reverse inclusion: Theorem 76 at the stage `i`, summand by summand
      have hl' : l ≤ s := Finset.mem_range_succ_iff.mp hl
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => bot_le) hl)
      exact IdealSheaf.logDerivIter_mono E ψ
        (B.isClosedSubmanifold_strictTransformSeq S hS hc i.succ) (s - l)
        (birationalTransform_mono ((B.isClosedSubmanifold_center i).congr_chart ψ)
        ((B.isBlowUp_map i).congr_chart ψ)
        (markedTransformSeq_iteratedDeriv_le_of_forall_lt (hl'.trans hs) i.castSucc h4lt)
        fun a ha => le_ordAlongIdeal_iteratedDeriv _ _ ha (hl'.trans hs) (hmI a ha))

/-- **Theorem 88** [Kol07, Theorem 88] along a sequence: for `Π` of order `≥ m` for `(I, m)` whose
centres lie in the strict transforms `S_i` of the hypersurface `S`, and `s ≤ m`,
`D^s(Π_*^{-1}(I, m)) = ∑_{j=0}^{s} D^{s−j}(−log S_i)(Π_*^{-1}(D^j I, m − j))` at every stage `i`
(`iteratedDeriv_markedTransformSeq_eq_sum_of_forall_lt` with the order clause (4′) of `hge`). The
algebraic counterpart is `derivativeIter_markedTransformSeq_eq_iSup`. -/
theorem iteratedDeriv_markedTransformSeq_eq_sum (hge : B.IsOfOrderGe I m E₀) {s : ℕ} (hs : s ≤ m)
    (i : Fin (B.length + 1)) :
    (B.markedTransformSeq I m i).iteratedDeriv s =
      ∑ j ∈ Finset.range (s + 1),
        IdealSheaf.logDerivIter E ψ (B.isClosedSubmanifold_strictTransformSeq S hS hc i) (s - j)
          (B.markedTransformSeq (I.iteratedDeriv j) (m - j) i) :=
  B.iteratedDeriv_markedTransformSeq_eq_sum_of_forall_lt hS hc hs i fun i' _ _ ha =>
    hge.le_ordAlong i' ha

omit [FiniteDimensional 𝕜 E] in
/-- The identity (87.1) of [Kol07, 87] along the inclusions `S_i ↪ X_i` of the restricted sequence:
the restriction of `D^r(−log S_i)(J)` to `S_i` is the `r`-th derivative of the restriction. -/
theorem logDerivIter_pullback_restrictIncl (i : Fin (B.length + 1)) (r : ℕ)
    (J : IdealSheaf (B.stage i)) :
    (IdealSheaf.logDerivIter E ψ (B.isClosedSubmanifold_strictTransformSeq S hS hc i) r J).pullback
        ⇑(B.restrictIncl hS hc i) (B.restrictIncl hS hc i).contMDiff =
      (J.pullback ⇑(B.restrictIncl hS hc i) (B.restrictIncl hS hc i).contMDiff).iteratedDeriv
        r := by
  obtain ⟨i, hi⟩ := i
  cases i
  · exact logDerivIter_pullback_inclusionMap
      (B.isClosedSubmanifold_strictTransformSeqAux _ hS hc 0 hi) r
      J
  · exact logDerivIter_pullback_inclusionMap
      (B.isClosedSubmanifold_strictTransformSeqAux _ hS hc (_ + 1) hi) r J

/-- **Corollary 89** [Kol07, Corollary 89]: with the assumptions of Theorem 88 and `1 ≤ m`, on the
last strict transform `S_r` (read as the preimage under its embedding into the last stage),
`S_r ∩ cosupp(Π_*^{-1}(I, m), m) = ⋂_{j<m} cosupp((Π|_{S_r})_*^{-1}((D^j I)|_S, m − j), m − j)`.
The algebraic counterpart carries the same name. -/
theorem cosupp_markedTransformSeq_inter_eq_iInter (hge : B.IsOfOrderGe I m E₀) (hm : 1 ≤ m) :
    ⇑(B.restrictIncl hS hc (Fin.last B.length)) ⁻¹'
        {x | (m : ℕ∞) ≤ (B.markedTransformSeq I m (Fin.last B.length)).ord x} =
      ⋂ j, ⋂ (_ : j < m), {y | ((m - j : ℕ) : ℕ∞) ≤
        ((B.restrictSubmanifold hS hc).markedTransformSeq
          ((I.iteratedDeriv j).pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) (m - j)
          (Fin.last B.length)).ord y} := by
  set r := Fin.last B.length with hr
  set ι := B.restrictIncl hS hc r with hι
  have h88 := B.iteratedDeriv_markedTransformSeq_eq_sum hS hc hge (Nat.sub_le m 1) r
  -- the summands, restricted to `S_r`: (87.1) and the restriction of the marked transforms
  have hsummand : ∀ j, j < m →
      ((IdealSheaf.logDerivIter E ψ (B.isClosedSubmanifold_strictTransformSeq S hS hc r) (m - 1 - j)
        (B.markedTransformSeq (I.iteratedDeriv j) (m - j) r)).pullback ⇑ι ι.contMDiff) =
      ((B.restrictSubmanifold hS hc).markedTransformSeq
        ((I.iteratedDeriv j).pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) (m - j)
        r).iteratedDeriv (m - 1 - j) := fun j hj => by
    rw [B.logDerivIter_pullback_restrictIncl hS hc r,
      B.markedTransformSeq_pullback_restrictIncl hS hc (hge.isOfOrderGe_iteratedDeriv hj.le) r]
  ext y
  rw [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iInter₂]
  simp only [Set.mem_ofPred_eq]
  rw [IdealSheaf.le_ord_iff_one_le_ord_iteratedDeriv _ hm, IdealSheaf.one_le_ord_iff_mem_support,
    ← Set.mem_preimage, ← IdealSheaf.support_pullback ι ι.contMDiff, h88, Nat.sub_add_cancel hm,
    IdealSheaf.pullback_finset_sum, IdealSheaf.mem_support_finset_sum_iff]
  refine forall_congr' fun j => ?_
  rw [Finset.mem_range]
  refine imp_congr_right fun hj => ?_
  rw [hsummand j hj, ← IdealSheaf.one_le_ord_iff_mem_support,
    show m - 1 - j = m - j - 1 by omega,
    ← IdealSheaf.le_ord_iff_one_le_ord_iteratedDeriv _ (Nat.sub_pos_of_lt hj)]

end AnalyticManifold.FiniteSuccession

end
