/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Monoid
public import Hironaka.Manifold.BlowUp.Transform.Basic
public import Hironaka.Manifold.IdealSheaf.Deriv
public import Hironaka.Manifold.IdealSheaf.LogDeriv
import Hironaka.Algebra.Local.TransformDerivNormalForm
import Hironaka.Algebra.Local.TransformLogDerivMap
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.DerivTransform
import Hironaka.Manifold.BlowUp.Transform.LogDerivTransform
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.DerivTransform
import Hironaka.Manifold.IdealSheaf.DerivLemmas
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.LogDerivLemmas
import Hironaka.Scheme.BlowUpSequence.Theorem88Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The logarithmic derivative rule and Kollár's Theorem 88 for one blowing-up

For a blowing-up `π : M' → M` with centre `Y ⊆ S`, `S` a smooth hypersurface with strict
transform `S'`, and a marked ideal sheaf `(J, m)` of order `≥ m` along `Y`:

* `birationalTransform_logDerivIter_le`, the logarithmic version of the derivative rule
  [Kol07, 87, (87.3)] ("a logarithmic version of (76), proved the same way using (75.4)"):
  `π_*^{-1}(D^j(−log S)(J), m − j) ⊆ D^j(−log S')(π_*^{-1}(J, m))` for `j ≤ m`;
* `iteratedDeriv_birationalTransform_eq_sum`, [Kol07, Theorem 88] for one blowing-up:
  `D^s(π_*^{-1}(J, m)) = ∑_{j ≤ s} D^{s−j}(−log S')(π_*^{-1}(D^j J, m − j))` for `s ≤ m`.

Both are proved stalk by stalk at a point `a'` of `M'`, in three cases:

* `a' ∉ S'`: `D(−log S')` is the full derivative there (`I_{S',a'} = (1)`), and the statements
reduce to the derivative rule of `Hironaka.Manifold.BlowUp.Transform.DerivTransform`; for (88.1)
the `j = 0` summand alone is `D^s(π_*^{-1}(J, m))_{a'}`;
* `a' ∈ S'` over the centre: Kollár's good chart (`exists_kollarChartData_of_mem_strictTransform`)
  reads both sides through the chart-ring map `χ`, where the chart-level statements for schemes
  hold (`transform_Dlogpow_le_chartDlogpow` for (87.3), `iterate_chartD_transformIdeal_le` for the
  `⊆` of (88.1)), and the rule (75.1) carries `D'`, `D'(−log y_{h₀})` into `D`, `D(−log S')`
  (`map_chartDlogpow_le_logDerivativeIter`, `derivativeIter_map_le_map_iterate_chartD_of_span`);
* `a' ∈ S'` off the centre: `π` is a local isomorphism, both birational transforms are total
  transforms and `D(−log S)`, `D` commute with local isomorphisms
  (`stalkIdeal_logDerivIter_pullback_of_bijective`,
  `stalkIdeal_iteratedDeriv_pullback_of_bijective`); for (88.1) the `j = s` summand.

The `⊇` of (88.1) is the derivative rule with `D^{s−j}(−log S') ⊆ D^{s−j}` and
`D^{s−j} D^j = D^s`. The counterparts for schemes are in
`Hironaka.Scheme.BlowUpSequence.Theorem88Basic`; this is the one-step form from which the theorem
along a sequence of blowings-up is assembled.
-/

public section

noncomputable section

open TopologicalSpace IsLocalRing
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] [FiniteDimensional 𝕜 E] {S Y : Set M} {c : ℕ} {M' : Type u}
  [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M']
  [SecondCountableTopology M'] {π : M' → M}
  (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π) (hS : IsClosedSubmanifold ψ S 1)
  (hYS : Y ⊆ S) (hS' : IsClosedSubmanifold ψ (strictTransformSet π Y S) 1)

include hYS in
/-- The logarithmic derivative rule [Kol07, 87, (87.3)] for one blowing-up: for a blowing-up `π`
with centre `Y ⊆ S`, `m ≤ ord_Y J`
at every point of `Y` and `j ≤ m`,
`π_*^{-1}(D^j(−log S)(J), m − j) ⊆ D^j(−log S')(π_*^{-1}(J, m))`, `S'` the strict transform of
`S`. -/
theorem birationalTransform_logDerivIter_le (J : IdealSheaf (structureSheaf 𝕜 E M)) {m j : ℕ}
    (hm : ∀ a ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J a) (hj : j ≤ m) :
    (MarkedIdealSheaf.birationalTransform hY h ⟨IdealSheaf.logDerivIter E ψ hS j J, m - j⟩).I ≤
      IdealSheaf.logDerivIter E ψ hS' j (MarkedIdealSheaf.birationalTransform hY h ⟨J, m⟩).I := by
  have hmD : ∀ a ∈ Y, ((m - j : ℕ) : ℕ∞) ≤
      IdealSheaf.ordAlongIdeal hY.idealSheaf (J.iteratedDeriv j) a :=
    fun a ha => le_ordAlongIdeal_iteratedDeriv hY J ha hj (hm a ha)
  have hmL : ∀ a ∈ Y, ((m - j : ℕ) : ℕ∞) ≤
      IdealSheaf.ordAlongIdeal hY.idealSheaf (IdealSheaf.logDerivIter E ψ hS j J) a :=
    fun a ha => IdealSheaf.le_ordAlongIdeal_of_le
      (IdealSheaf.logDerivIter_le_iteratedDeriv E ψ hS j J) (hmD a ha)
  rw [IdealSheaf.le_def]
  intro a'
  by_cases haS' : a' ∈ strictTransformSet π Y S
  · by_cases haY : π a' ∈ Y
    · -- over the centre: (87.3) in the chart ring, in Kollár's good chart, through `χ`
      obtain ⟨κ, r, h₀, χ, δ, hk, hs, hh₀, hP, hSa, hS'a, hδ, hpres, -, hbt⟩ :=
        exists_kollarChartData_of_mem_strictTransform hY h hS hYS hS' haS' haY
      have hI : J.stalkIdeal (π a') ≤ chartCenter κ.x r ^ (m - j + j) := by
        rw [Nat.sub_add_cancel hj, hP]
        exact (IdealSheaf.le_ordAlongIdeal_iff _ _ _ _).mp (hm _ haY)
      have h1 := κ.transform_Dlogpow_le_chartDlogpow r hh₀ hI
      rw [Nat.sub_add_cancel hj] at h1
      rw [hbt _ hmL, IdealSheaf.stalkIdeal_logDerivIter_eq_Dlogpow E ψ hS κ hk hs h₀ hSa j J,
        IdealSheaf.stalkIdeal_logDerivIter hS' j, hS'a, hbt J hm]
      exact (Ideal.map_mono h1).trans
        (κ.map_chartDlogpow_le_logDerivativeIter r χ δ hδ h₀ hpres j _)
    · -- off the centre: `π` is a local isomorphism and `D(−log S)` commutes with it
      have hb := germMap_bijective_of_isLocalDiffeomorphAt π h.contMDiff
        (h.isLocalDiffeomorphOn_compl ⟨a', haY⟩)
      refine le_of_eq ?_
      rw [birationalTransform_stalkIdeal_of_notMem hY h hmL haY,
        IdealSheaf.stalkIdeal_logDerivIter hS' j,
        birationalTransform_stalkIdeal_of_notMem hY h hm haY,
        ← IdealSheaf.stalkIdeal_logDerivIter hS' j (J.pullback π h.contMDiff) a',
        stalkIdeal_logDerivIter_pullback_of_bijective π h.contMDiff hS hS' J hb
          (stalkIdeal_idealSheaf_strictTransform_of_notMem hY h hS hYS hS' haY) j]
  · -- off `S'`: `D(−log S')` is `D` there, and the claim is Theorem 76
    rw [IdealSheaf.stalkIdeal_logDerivIter, hS'.stalkIdeal_idealSheaf_of_notMem haS',
      Ideal.logDerivativeIter_top, ← IdealSheaf.stalkIdeal_iteratedDeriv]
    exact IdealSheaf.le_def.mp
      ((birationalTransform_mono hY h (IdealSheaf.logDerivIter_le_iteratedDeriv E ψ hS j J)
        hmD).trans (markedTransform_iteratedDeriv_le hY h J hm hj)) a'

include hS hYS in
/-- **Kollár's Theorem 88** for one blowing-up [Kol07, Theorem 88]: for a blowing-up `π` with
centre `Y ⊆ S`, `m ≤ ord_Y J`
at every point of `Y` and `s ≤ m`,
`D^s(π_*^{-1}(J, m)) = ∑_{j=0}^{s} D^{s−j}(−log S')(π_*^{-1}(D^j J, m − j))`: the order of
restricting to `x₁ = 0` and transforming "does not matter" (the proof of [Kol07, Lemma 62]); (87.2)
applied to `π_*^{-1}(J, m)` in the good charts, where `∂/∂y₁` commutes with the transform by
(75.1); the `⊇` is the derivative rule (`markedTransform_iteratedDeriv_le`) with the filtration. -/
theorem iteratedDeriv_birationalTransform_eq_sum (J : IdealSheaf (structureSheaf 𝕜 E M)) {m s : ℕ}
    (hm : ∀ a ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J a) (hs : s ≤ m) :
    (MarkedIdealSheaf.birationalTransform hY h ⟨J, m⟩).I.iteratedDeriv s =
      ∑ j ∈ Finset.range (s + 1), IdealSheaf.logDerivIter E ψ hS' (s - j)
        (MarkedIdealSheaf.birationalTransform hY h ⟨J.iteratedDeriv j, m - j⟩).I := by
  have hmD : ∀ j ≤ s, ∀ a ∈ Y, ((m - j : ℕ) : ℕ∞) ≤
      IdealSheaf.ordAlongIdeal hY.idealSheaf (J.iteratedDeriv j) a :=
    fun j hj a ha => le_ordAlongIdeal_iteratedDeriv hY J ha (hj.trans hs) (hm a ha)
  refine le_antisymm ?_ ?_
  · rw [IdealSheaf.le_def]
    intro a'
    rw [IdealSheaf.stalkIdeal_finset_sum, Ideal.sum_eq_sup]
    by_cases haS' : a' ∈ strictTransformSet π Y S
    · by_cases haY : π a' ∈ Y
      · -- over the centre: the chart-ring inclusion in Kollár's good chart, through `χ`
        obtain ⟨κ, r, h₀, χ, δ, hk, hs', hh₀, hP, hSa, hS'a, hδ, hpres, hspan, hbt⟩ :=
          exists_kollarChartData_of_mem_strictTransform hY h hS hYS hS' haS' haY
        have hI : J.stalkIdeal (π a') ≤ chartCenter κ.x r ^ m := by
          rw [hP]
          exact (IdealSheaf.le_ordAlongIdeal_iff _ _ _ _).mp (hm _ haY)
        rw [IdealSheaf.stalkIdeal_iteratedDeriv, hbt J hm]
        refine (κ.derivativeIter_map_le_map_iterate_chartD_of_span r χ δ hδ hspan s _).trans ?_
        refine (Ideal.map_mono (κ.iterate_chartD_transformIdeal_le r hh₀ hI hs)).trans ?_
        rw [Ideal.map_iSup]
        refine iSup_le fun j => ?_
        rw [Ideal.map_iSup]
        refine iSup_le fun hj => ?_
        refine (κ.map_chartDlogpow_le_logDerivativeIter r χ δ hδ h₀ hpres (s - j) _).trans
          (le_of_eq_of_le ?_ (Finset.le_sup (f := fun j => (IdealSheaf.logDerivIter E ψ hS' (s - j)
            (MarkedIdealSheaf.birationalTransform hY h ⟨J.iteratedDeriv j, m - j⟩).I).stalkIdeal a')
            (Finset.mem_range_succ_iff.mpr hj)))
        rw [IdealSheaf.stalkIdeal_logDerivIter, hS'a, hbt (J.iteratedDeriv j) (hmD j hj),
          J.stalkIdeal_iteratedDeriv_eq_Dpow κ hk hs' j]
      · -- off the centre: everything is a total transform along a local isomorphism (`j = s`)
        have hb := germMap_bijective_of_isLocalDiffeomorphAt π h.contMDiff
          (h.isLocalDiffeomorphOn_compl ⟨a', haY⟩)
        refine le_of_eq_of_le ?_ (Finset.le_sup (f := fun j => (IdealSheaf.logDerivIter E ψ hS'
          (s - j) (MarkedIdealSheaf.birationalTransform hY h
            ⟨J.iteratedDeriv j, m - j⟩).I).stalkIdeal a') (Finset.mem_range_succ_iff.mpr le_rfl))
        rw [Nat.sub_self, IdealSheaf.logDerivIter_zero, IdealSheaf.stalkIdeal_iteratedDeriv,
          birationalTransform_stalkIdeal_of_notMem hY h hm haY,
          birationalTransform_stalkIdeal_of_notMem hY h (hmD s le_rfl) haY,
          ← IdealSheaf.stalkIdeal_iteratedDeriv,
          stalkIdeal_iteratedDeriv_pullback_of_bijective π h.contMDiff J hb s]
    · -- off `S'`: `D(−log S')` is `D` there and the `j = 0` summand is the left side
      refine le_of_eq_of_le ?_ (Finset.le_sup (f := fun j => (IdealSheaf.logDerivIter E ψ hS'
        (s - j) (MarkedIdealSheaf.birationalTransform hY h
          ⟨J.iteratedDeriv j, m - j⟩).I).stalkIdeal a')
        (Finset.mem_range_succ_iff.mpr (Nat.zero_le s)))
      rw [IdealSheaf.stalkIdeal_logDerivIter, hS'.stalkIdeal_idealSheaf_of_notMem haS',
        Ideal.logDerivativeIter_top]
      simp only [Nat.sub_zero, IdealSheaf.iteratedDeriv_zero, IdealSheaf.stalkIdeal_iteratedDeriv]
  · -- `⊇`: Theorem 76 with `D^{s−j}(−log S') ⊆ D^{s−j}` and `D^{s−j} D^j = D^s`
    rw [IdealSheaf.le_def]
    intro a'
    rw [IdealSheaf.stalkIdeal_finset_sum, Ideal.sum_eq_sup]
    refine Finset.sup_le fun j hj => ?_
    have hj' : j ≤ s := Finset.mem_range_succ_iff.mp hj
    refine IdealSheaf.le_def.mp ?_ a'
    calc IdealSheaf.logDerivIter E ψ hS' (s - j)
          (MarkedIdealSheaf.birationalTransform hY h ⟨J.iteratedDeriv j, m - j⟩).I
        ≤ (MarkedIdealSheaf.birationalTransform hY h ⟨J.iteratedDeriv j, m - j⟩).I.iteratedDeriv
            (s - j) :=
          IdealSheaf.logDerivIter_le_iteratedDeriv E ψ hS' _ _
      _ ≤ ((MarkedIdealSheaf.birationalTransform hY h ⟨J, m⟩).I.iteratedDeriv j).iteratedDeriv
            (s - j) :=
          IdealSheaf.iteratedDeriv_mono
            (markedTransform_iteratedDeriv_le hY h J hm (hj'.trans hs)) _
      _ = (MarkedIdealSheaf.birationalTransform hY h ⟨J, m⟩).I.iteratedDeriv s := by
          rw [← IdealSheaf.iteratedDeriv_add, Nat.sub_add_cancel hj']

end Manifold

end
