/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Transform.StrictCharts
public import Hironaka.Manifold.Germ.StalkNoetherian
public import Hironaka.Manifold.IdealSheaf.Basic
public import Hironaka.Manifold.IdealSheaf.Deriv
import Hironaka.Algebra.Local.TransformDerivMap
import Hironaka.Algebra.Local.TransformLogDeriv
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.DerivChart
import Hironaka.Manifold.BlowUp.Transform.KollarChart
import Hironaka.Manifold.BlowUp.Transform.KollarPerm
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.StrictIdeal
import Hironaka.Manifold.Germ.CoordDerivCoords
import Hironaka.Manifold.IdealSheaf.DerivLemmas
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The derivative of a birational transform under one blowing-up

For one blowing-up `π : M' → M` with centre `Y` and a marked ideal sheaf `(I, m)` with
`ord_Y I ≥ m`, `π_*^{-1}(D^j(I), m − j) ⊆ D^j(π_*^{-1}(I, m))` for `j ≤ m`
(`markedTransform_iteratedDeriv_le`): the case of one blow-up of [Kol07, Theorem 76] (for `j = 1`
and one blow-up the statement is the content of the formulas (75.1)–(75.3), and "the rest follows
by induction on `j`"), also [Wlo05, Lemma 2.6.3]. The proof is stalkwise:

* over the centre, the stalk of the birational transform is the image under the chart-ring map
  `χ` of the algebraic transform `transformIdeal`
  (`birationalTransform_stalkIdeal_eq_map_transformIdeal`), the stalk of `D(I)` is the coordinate
  derivative `κ.D I_a` in regular coordinates of the stalk (`stalkIdeal_deriv_eq_D`, taken in
  Kollár's order `τ`), the version for schemes gives `π_*^{-1}(D(I), m) ⊆ D'(π_*^{-1}(I, m + 1))` in
  the chart ring (`transform_D_le_chartD`), and the formulas (75.1)–(75.3) carry `D'` into `D`
  (`chartRingHom_chartDerivRing_eq_coordDerivStalk`, `map_chartD_le_derivative`);
* off the centre both birational transforms are total transforms along the local isomorphism `π`,
  and `D` commutes with local isomorphisms (`stalkIdeal_deriv_pullback_of_isLocalDiffeomorphAt`).

The order bookkeeping `ord_Y D^j(I) ≥ m − j` (the step "(74.3)" in the proof of
[Kol07, Corollary 77]) is `le_ordAlongIdeal_iteratedDeriv`, the stalk form of the algebraic
`Dpow_le_chartCenter_pow`.

The strict transform of a smooth hypersurface `H ⊇ Y` has ideal sheaf `π_*^{-1}(I_H, 1)`
(`idealSheaf_strictTransform_eq_markedTransform_one`): `isIdealSheafOf_strictTransform` of
`Hironaka.Manifold.BlowUp.Transform.StrictIdeal` read through the uniqueness of the ideal
sheaf of a closed submanifold; [Wlo05, Lemma 2.7.4], and the proof of [Kol07, Theorem 80].

These results feed the derivative rules along a sequence of blowings-up
(`Hironaka.Manifold.FiniteSuccession.DerivTransform`).
-/

public section

noncomputable section

open TopologicalSpace IsLocalRing
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

section DerivativeBot

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- The derivative ideal of the zero ideal is zero. -/
theorem Ideal.derivative_bot : Ideal.derivative k (⊥ : Ideal A) = ⊥ :=
  le_bot_iff.mp (Ideal.derivative_le_iff.mpr ⟨le_rfl, fun δ f hf => by
    rw [Ideal.mem_bot.mp hf, map_zero]
    exact Ideal.zero_mem _⟩)

/-- The iterated derivative ideals of the zero ideal are zero. -/
theorem Ideal.derivativeIter_bot (r : ℕ) : Ideal.derivativeIter k r (⊥ : Ideal A) = ⊥ := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Ideal.derivativeIter_succ, ih, Ideal.derivative_bot]

end DerivativeBot

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] [FiniteDimensional 𝕜 E]

/-- The derivative ideal sheaf is monotone. -/
theorem IdealSheaf.deriv_mono {J K : IdealSheaf (structureSheaf 𝕜 E M)} (h : J ≤ K) :
    J.deriv ≤ K.deriv := by
  rw [IdealSheaf.le_def]
  intro a
  rw [IdealSheaf.stalkIdeal_deriv, IdealSheaf.stalkIdeal_deriv]
  exact Ideal.derivative_mono (IdealSheaf.le_def.mp h a)

/-- The iterated derivative ideal sheaves are monotone. -/
theorem IdealSheaf.iteratedDeriv_mono {J K : IdealSheaf (structureSheaf 𝕜 E M)} (h : J ≤ K)
    (j : ℕ) : J.iteratedDeriv j ≤ K.iteratedDeriv j := by
  induction j with
  | zero => exact h
  | succ j ih =>
    rw [IdealSheaf.iteratedDeriv_succ, IdealSheaf.iteratedDeriv_succ]
    exact IdealSheaf.deriv_mono ih

/-- Regular coordinates of the stalk (`exists_regularCoords_stalk`) taken in
a prescribed order `τ` of the chart coordinates (Kollár's order at a point of the centre):
`x_j = coord (τ j) − coord (τ j)(a)`, `∂_j = ∂_{τ j}`, `𝕜`-linear and spanning. -/
theorem exists_regularCoords_reindex (φ : OpenPartialHomeomorph M E)
    (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {a : M} (ha : a ∈ φ.source) (τ : Fin n ≃ Fin n) :
    ∃ κ : RegularCoords ((structureSheaf 𝕜 E M).presheaf.stalk a) n,
      (∀ j, κ.x j = coord E ψ φ hφ ha (τ j) -
        const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hφ ha (τ j)))) ∧
      (∀ j, κ.pderiv j = (coordDerivStalk E ψ φ hφ ha (τ j)).restrictScalars ℚ) ∧
      κ.IsLinearOver 𝕜 ∧ κ.SpansDerivations 𝕜 := by
  have hdim : (n : WithBot ℕ∞) = ringKrullDim ((structureSheaf 𝕜 E M).presheaf.stalk a) := by
    rw [ringKrullDim_stalk E a, ψ.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  obtain ⟨c₀, hcx, hcp, hk, hs⟩ := exists_regularCoords_stalk E ψ φ hφ ha hdim
  exact ⟨c₀.reindex τ, fun j => hcx (τ j), fun j => hcp (τ j), c₀.reindex_isLinearOver hk τ,
    c₀.reindex_spansDerivations hs τ⟩

variable {Y : Set M} {c : ℕ}

/-- At a point `a` of the closed submanifold `Y`, if `I` has order `≥ m` along `Y` at `a`, then
`D^j(I)` has order `≥ m − j` along `Y` at `a` for `j ≤ m` ([Kol07, Lemma 74, (3)]; the step
"(74.3)" in the proof of [Kol07, Corollary 77]). -/
theorem le_ordAlongIdeal_iteratedDeriv (hY : IsClosedSubmanifold ψ Y c)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) {a : M} (ha : a ∈ Y) {m j : ℕ} (hj : j ≤ m)
    (hm : (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I a) :
    ((m - j : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf (I.iteratedDeriv j) a := by
  rw [IdealSheaf.le_ordAlongIdeal_iff] at hm ⊢
  obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart a ha
  rcases Nat.eq_zero_or_pos c with hc | hc
  · -- a centre of codimension `0`: its ideal sheaf is zero at the points of `Y`
    subst hc
    have hbot : hY.idealSheaf.stalkIdeal a = ⊥ := by
      rw [hY.stalkIdeal_idealSheaf_eq_span ha hφ haφ, Set.range_eq_empty, Ideal.span_empty]
    rw [hbot] at hm ⊢
    rw [IdealSheaf.stalkIdeal_iteratedDeriv]
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      obtain rfl : j = 0 := Nat.le_zero.mp hj
      simp
    · have hpow : (⊥ : Ideal ((structureSheaf 𝕜 E M).presheaf.stalk a)) ^ m = ⊥ := by
        rw [← Submodule.zero_eq_bot, zero_pow hm0.ne']
      rw [hpow] at hm
      rw [le_bot_iff.mp hm, Ideal.derivativeIter_bot]
      exact bot_le
  · obtain ⟨r, τ, hτr, hlt⟩ := exists_kollarPerm σ ⟨0, hc⟩
    obtain ⟨κ, hτ, -, hk, hs⟩ := exists_regularCoords_reindex (ψ := ψ) φ hφ.1 haφ τ
    have hP := chartCenter_eq_stalkIdeal_idealSheaf hY hφ ha haφ κ.x r τ hτr hτ hlt
    rw [← hP] at hm ⊢
    rw [IdealSheaf.stalkIdeal_iteratedDeriv_eq_Dpow I κ hk hs j]
    exact κ.Dpow_le_chartCenter_pow r (by rwa [Nat.sub_add_cancel hj])

section OneBlowUp

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M} (hY : IsClosedSubmanifold ψ Y c)
  (h : IsBlowUp ψ Y c π) (I : IdealSheaf (structureSheaf 𝕜 E M))

omit h in
/-- The order bookkeeping for one derivative: `ord_Y I ≥ m + 1` gives `ord_Y D(I) ≥ m`. -/
theorem le_ordAlongIdeal_deriv {m : ℕ}
    (hm : ∀ a ∈ Y, ((m + 1 : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I a) :
    ∀ a ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I.deriv a := fun a ha => by
  have := le_ordAlongIdeal_iteratedDeriv hY I ha (j := 1) (Nat.succ_pos m) (hm a ha)
  simpa only [IdealSheaf.iteratedDeriv_succ, IdealSheaf.iteratedDeriv_zero, Nat.succ_sub_one,
    Nat.add_sub_cancel] using this

omit [IsManifold 𝓘(𝕜, E) ω M] [FiniteDimensional 𝕜 E] I in
/-- Off the centre the marked transform is the total transform: the exceptional ideal sheaf is
the unit ideal there and the colon by the unit ideal is the identity. -/
theorem birationalTransform_stalkIdeal_of_notMem {J : IdealSheaf (structureSheaf 𝕜 E M)} {k : ℕ}
    (hk : ∀ a ∈ Y, (k : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J a) {a' : M'}
    (ha' : π a' ∉ Y) :
    (MarkedIdealSheaf.birationalTransform hY h ⟨J, k⟩).I.stalkIdeal a' =
      (J.pullback π h.contMDiff).stalkIdeal a' := by
  have hcol := isDivExceptional_birationalTransform hY h ⟨J, k⟩ hk a'
  dsimp only at hcol
  rw [hcol, stalkIdeal_exceptionalIdealSheaf_of_notMem hY h ha', Ideal.top_pow, Submodule.top_coe,
    Submodule.colon_univ]

/-- For a
blowing-up `π` with centre `Y` and `ord_Y I ≥ m + 1` at every point of `Y`,
`π_*^{-1}(D(I), m) ⊆ D(π_*^{-1}(I, m + 1))` [Kol07, Theorem 76]. -/
theorem markedTransform_deriv_le {m : ℕ}
    (hm : ∀ a ∈ Y, ((m + 1 : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I a) :
    (MarkedIdealSheaf.birationalTransform hY h ⟨I.deriv, m⟩).I ≤
      (MarkedIdealSheaf.birationalTransform hY h ⟨I, m + 1⟩).I.deriv := by
  have hmD := le_ordAlongIdeal_deriv hY I hm
  rw [IdealSheaf.le_def]
  intro a'
  rw [IdealSheaf.stalkIdeal_deriv]
  by_cases haY : π a' ∈ Y
  · -- over the centre: the chart-ring computation in Kollár's coordinates, through `χ`
    obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart _ haY
    obtain ⟨i, Φ, hΦ, ha'⟩ := h.cover φ σ hφ a' haφ
    obtain ⟨r, τ, hτr, hlt⟩ := exists_kollarPerm σ i
    obtain ⟨κ, hτ, hpd, hk, hs⟩ :=
      exists_regularCoords_reindex (ψ := ψ) φ hφ.1 (hΦ.source_subset ha') τ
    obtain ⟨χ, hχ, hχy, -⟩ := exists_chartRing_hom h hφ hΦ ha' haY κ.x r τ hτr hτ hlt
    have hP := chartCenter_eq_stalkIdeal_idealSheaf hY hφ haY (hΦ.source_subset ha') κ.x r τ hτr
      hτ hlt
    have hI : I.stalkIdeal (π a') ≤ chartCenter κ.x r ^ (m + 1) := by
      rw [hP]
      exact (IdealSheaf.le_ordAlongIdeal_iff _ _ _ _).mp (hm _ haY)
    rw [birationalTransform_stalkIdeal_eq_map_transformIdeal hY h hφ hΦ ha' haY κ.x r τ hτr hτ hlt
        χ hχ I.deriv hmD,
      birationalTransform_stalkIdeal_eq_map_transformIdeal hY h hφ hΦ ha' haY κ.x r τ hτr hτ hlt
        χ hχ I hm,
      IdealSheaf.stalkIdeal_deriv_eq_D I κ hk hs]
    calc Ideal.map χ (transformIdeal κ.x r (κ.D (I.stalkIdeal (π a'))) m)
        ≤ Ideal.map χ (κ.chartD r (transformIdeal κ.x r (I.stalkIdeal (π a')) (m + 1))) :=
          Ideal.map_mono (κ.transform_D_le_chartD r hI)
      _ ≤ Ideal.derivative 𝕜 (Ideal.map χ (transformIdeal κ.x r (I.stalkIdeal (π a')) (m + 1))) :=
          κ.map_chartD_le_derivative r χ
            (fun j => coordDerivStalk E ψ Φ hΦ.mem_maximalAtlas ha' (τ j))
            (fun j g => chartRingHom_chartDerivRing_eq_coordDerivStalk h hφ hΦ ha' haY κ r τ hτr hτ
              hpd hlt χ hχ hχy j g) _
  · -- off the centre: `π` is a local isomorphism and `D` commutes with it
    have hb : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω π a' :=
      h.isLocalDiffeomorphOn_compl ⟨a', haY⟩
    refine le_of_eq ?_
    rw [birationalTransform_stalkIdeal_of_notMem hY h hmD haY,
      birationalTransform_stalkIdeal_of_notMem hY h hm haY, ← IdealSheaf.stalkIdeal_deriv,
      stalkIdeal_deriv_pullback_of_isLocalDiffeomorphAt π h.contMDiff I hb]

/-- One blowing-up in [Kol07, Theorem 76] ("the rest follows by induction on `j`"), also
[Wlo05, Lemma 2.6.3]; the form along a sequence of blowings-up is
`markedTransform_derivativeIter_le`. For a blowing-up `π` with centre `Y`, `ord_Y I ≥ m` at every
point of `Y` and `j ≤ m`, `π_*^{-1}(D^j(I), m − j) ⊆ D^j(π_*^{-1}(I, m))`. -/
theorem markedTransform_iteratedDeriv_le {m : ℕ}
    (hm : ∀ a ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I a) {j : ℕ} (hj : j ≤ m) :
    (MarkedIdealSheaf.birationalTransform hY h ⟨I.iteratedDeriv j, m - j⟩).I ≤
      (MarkedIdealSheaf.birationalTransform hY h ⟨I, m⟩).I.iteratedDeriv j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    have hj' : j ≤ m := Nat.le_of_succ_le hj
    have hmj : m - j = m - (j + 1) + 1 := by omega
    have hmD : ∀ a ∈ Y, ((m - (j + 1) + 1 : ℕ) : ℕ∞) ≤
        IdealSheaf.ordAlongIdeal hY.idealSheaf (I.iteratedDeriv j) a := fun a ha => by
      rw [← hmj]
      exact le_ordAlongIdeal_iteratedDeriv hY I ha hj' (hm a ha)
    calc (MarkedIdealSheaf.birationalTransform hY h ⟨I.iteratedDeriv (j + 1), m - (j + 1)⟩).I
        = (MarkedIdealSheaf.birationalTransform hY h
            ⟨(I.iteratedDeriv j).deriv, m - (j + 1)⟩).I := by
          rw [IdealSheaf.iteratedDeriv_succ]
      _ ≤ (MarkedIdealSheaf.birationalTransform hY h
            ⟨I.iteratedDeriv j, m - (j + 1) + 1⟩).I.deriv :=
          markedTransform_deriv_le hY h (I.iteratedDeriv j) hmD
      _ = (MarkedIdealSheaf.birationalTransform hY h ⟨I.iteratedDeriv j, m - j⟩).I.deriv := by
          rw [← hmj]
      _ ≤ ((MarkedIdealSheaf.birationalTransform hY h ⟨I, m⟩).I.iteratedDeriv j).deriv :=
          IdealSheaf.deriv_mono (ih hj')
      _ = (MarkedIdealSheaf.birationalTransform hY h ⟨I, m⟩).I.iteratedDeriv (j + 1) :=
          (IdealSheaf.iteratedDeriv_succ _ _).symm

omit [FiniteDimensional 𝕜 E] I in
/-- For a blowing-up `π` with centre `Y ⊆ H`, `H` a smooth
hypersurface, the strict transform `H'` is a smooth hypersurface of `M'` whose ideal sheaf is the
marked transform of `(I_H, 1)` ([Wlo05, Lemma 2.7.4]; the proof of [Kol07, Theorem 80]). -/
theorem idealSheaf_strictTransform_eq_markedTransform_one {H : Set M}
    (hH : IsClosedSubmanifold ψ H 1) (hYH : Y ⊆ H) :
    (isClosedSubmanifold_strictTransform hY h hH hYH).idealSheaf =
      (MarkedIdealSheaf.birationalTransform hY h ⟨hH.idealSheaf, 1⟩).I :=
  (IsIdealSheafOf.eq_idealSheaf (isClosedSubmanifold_strictTransform hY h hH hYH)
    (isIdealSheafOf_strictTransform hY h hH hYH)).symm

end OneBlowUp

end Manifold

end
