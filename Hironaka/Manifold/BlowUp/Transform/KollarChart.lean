/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.BirationalTransform
public import Hironaka.Manifold.BlowUp.Transform.Basic
public import Hironaka.Manifold.StructureSheaf
import Hironaka.Manifold.BlowUp.Divisor
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.Division
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's chart formula and the map from the chart ring to the germ ring

In a blow-up chart `Φ` of index `i` over an adapted chart `φ`, a section `f` composed with the
blowing-up reads, in the chart coordinates, as `f ∘ φ⁻¹ ∘ ψ⁻¹` composed with the substitution
`blowUpChartMap σ i`: Kollár's `f(y_1 y_r, …, y_{r−1} y_r, y_r, …, y_n)` [Kol07, Definition 60,
(60.2)–(60.3)], Bierstone–Milman's formal substitution in the Taylor expansion [BM97, §3,
"Blowing-up"] (`totalTransform_rep`, from `IsBlowUpChart.comm`). When `f ∈ I_Y^m` along the
centre, the transform `u_i^{-m} f(…)` is an analytic function on the chart (`exists_rep_div`: the
pulled-back germs lie in `(u_i^m)` at the points of the exceptional divisor, so the iterated
canonical quotient of `Hironaka.Manifold.BlowUp.Transform.Division` is analytic and satisfies
`u_i^m · g = f ∘ π`). Two blow-up charts at a point give representatives differing by a unit
(`rep_div_unit`: both scaling coordinates generate the stalk of `I_F`, hence are associated in the
domain stalk), as Kollár remarks after (60.3). The chart ring `R' = R[x_j / x_r : j < r]` of the
algebraic strand (`IsLocalRing.chartRing`, for the centred adapted coordinates `x` in Kollár's
order: the scaling coordinate at position `r`, the other centre coordinates before it) maps to
the germ ring at a point `a'` of the chart over the centre: the stalk map
`germMap π : 𝒪_{M,a} → 𝒪_{M',a'}` sends `x_r` to the scaling coordinate `u_i` and `x_j` (`j < r`)
to `u_i u_j`, so it extends by `IsLocalization.lift` to `R[1/x_r]` with values in the fraction
field of the domain `𝒪_{M',a'}`, and on the subalgebra `R'` the values are the germs `u_j` and
`germMap π (·)` themselves, hence lie in `𝒪_{M',a'}` (`exists_chartRing_hom`, with
`χ ∘ algebraMap = germMap π`, `x_j / x_r ↦ u_j`, `x_r ↦ u_i`). Through any such `χ`, the stalk of
the birational transform `π_*^{-1}(I, m)` is the image of the algebraic transform
`transformIdeal x r I_a m` (`birationalTransform_stalkIdeal_eq_map_transformIdeal`): the colon
`(π⁻¹(I)_{a'} : u_i^m)` is spanned by the `u_i^{-m}(f_j ∘ π) = χ(f_j / x_r^m)` for local
generators `f_j ∈ I_a ⊆ (x_1, …, x_r)^m` (`chartCenter_eq_stalkIdeal_idealSheaf`,
`exists_algebraMap_pow_mul_eq`), and conversely every generator of the algebraic transform maps
into the colon.

This identification connects the analytic birational transform with the algebraic one of
`Hironaka.Algebra.Local.BirationalTransform`; it is used for the derivative rule of
`Hironaka.Manifold.BlowUp.Transform.DerivChart`.
-/

public section

open TopologicalSpace Opposite CategoryTheory Filter Topology IsLocalRing Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M}
  {c : ℕ} {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M} {φ : OpenPartialHomeomorph M E}
  {σ : Fin c ↪ Fin n} {i : Fin c} {Φ : OpenPartialHomeomorph M' E}

omit [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M'] in
/-- `f ∘ π` at a point of a
blow-up chart is `f ∘ φ⁻¹ ∘ ψ⁻¹` composed with the substitution `blowUpChartMap σ i`
[Kol07, Definition 60, (60.2)–(60.3)]. -/
theorem totalTransform_rep (hΦ : IsBlowUpChart ψ π φ σ i Φ) {U : Opens M}
    (f : (structureSheaf 𝕜 E M).presheaf.obj (op U)) {p : M'} (hp : p ∈ Φ.source) :
    extendSection 𝕜 E f (π p) =
      extendSection 𝕜 E f (φ.symm (ψ.symm (blowUpChartMap σ i (ψ (Φ p))))) := by
  rw [← hΦ.comm p hp, ψ.symm_apply_apply, φ.left_inv (hΦ.source_subset hp)]

/-- For `f ∈ I_Y^m` along `Y`, the transform
`u_i^{-m} · f(y_1 y_r, …)` is an analytic function `g` on the blow-up chart with
`u_i^m · g = f ∘ π ∘ Φ⁻¹` [Kol07, Definition 60, (60.3)]. -/
theorem exists_rep_div (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
    (hφ : IsAdaptedChart ψ Y φ σ) (hΦ : IsBlowUpChart ψ π φ σ i Φ) {U : Opens M}
    (f : (structureSheaf 𝕜 E M).presheaf.obj (op U)) {m : ℕ}
    (hf : ∀ a ∈ Y, ∀ (ha : a ∈ U),
      (structureSheaf 𝕜 E M).presheaf.germ U a ha f ∈ hY.idealSheaf.stalkIdeal a ^ m) :
    ∃ g : E → 𝕜, AnalyticOnNhd 𝕜 g (Φ.target ∩ {v | π (Φ.symm v) ∈ U}) ∧
      ∀ v ∈ Φ.target ∩ {v | π (Φ.symm v) ∈ U},
        (ψ v (σ i)) ^ m * g v = extendSection 𝕜 E f (π (Φ.symm v)) := by
  have hπc : Continuous π := h.contMDiff.continuous
  set T : Set E := Φ.target ∩ {v | π (Φ.symm v) ∈ U} with hT
  have hTo : IsOpen T := Φ.isOpen_inter_preimage_symm (U.2.preimage hπc)
  set N : Set (Fin n → 𝕜) := ψ '' T with hN
  have hNo : IsOpen N := ψ.isOpenMap _ hTo
  set F : (Fin n → 𝕜) → 𝕜 := fun w =>
    extendSection 𝕜 E (comapSection π h.contMDiff f) (Φ.symm (ψ.symm w)) with hF
  have h2 : ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, E) ω (fun w => Φ.symm (ψ.symm w)) N := by
    refine (contMDiffOn_symm_of_mem_maximalAtlas hΦ.mem_maximalAtlas).comp
      ((ψ.symm : (Fin n → 𝕜) →L[𝕜] E).contMDiff.contMDiffOn) ?_
    rintro _ ⟨v, hv, rfl⟩
    change ψ.symm (ψ v) ∈ Φ.target
    rw [ψ.symm_apply_apply]
    exact hv.1
  have hFan : AnalyticOnNhd 𝕜 F N := by
    have h3 : ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜) ω F N := by
      refine (contMDiffOn_extendSection (comapSection π h.contMDiff f)).comp h2 ?_
      rintro _ ⟨v, hv, rfl⟩
      change Φ.symm (ψ.symm (ψ v)) ∈ (preimageOpens π h.contMDiff U : Set M')
      rw [ψ.symm_apply_apply]
      exact hv.2
    exact fun w hw => ((contMDiffOn_iff_contDiffOn.mp h3).contDiffAt (hNo.mem_nhds hw)).analyticAt
  have hdiv : ∀ w ∈ N, w (σ i) = 0 → ∃ N' : Set (Fin n → 𝕜), IsOpen N' ∧ w ∈ N' ∧
      ∃ G : (Fin n → 𝕜) → 𝕜, AnalyticOnNhd 𝕜 G N' ∧ ∀ w' ∈ N', F w' = w' (σ i) ^ m * G w' := by
    rintro _ ⟨v, hv, rfl⟩ hvk
    have hbΦ : Φ.symm v ∈ Φ.source := Φ.map_target hv.1
    have hΦb : Φ (Φ.symm v) = v := Φ.right_inv hv.1
    have hbF : π (Φ.symm v) ∈ Y :=
      (IsBlowUpChart.mem_preimage_iff hφ hΦ hbΦ).mpr (by rw [hΦb]; exact hvk)
    have hbU : Φ.symm v ∈ preimageOpens π h.contMDiff U := hv.2
    have hmem : (structureSheaf 𝕜 E M').presheaf.germ (preimageOpens π h.contMDiff U) (Φ.symm v)
        hbU (comapSection π h.contMDiff f) ∈
          Ideal.span {coord E ψ Φ hΦ.mem_maximalAtlas hbΦ (σ i) ^ m} := by
      rw [← germMap_germ π h.contMDiff hbU f, ← Ideal.span_singleton_pow,
        ← stalkIdeal_exceptionalIdealSheaf_eq_span_coord hY h hφ hΦ hbΦ,
            IdealSheaf.stalkIdeal_pullback, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (hf (π (Φ.symm v)) hbF hbU)
    obtain ⟨N', hN'o, hvN', G, hGan, hG⟩ := exists_eq_pow_mul_of_mem_span_pow_coord
      hΦ.mem_maximalAtlas hbΦ (σ i) m hbU (comapSection π h.contMDiff f) hmem
    refine ⟨N', hN'o, ?_, G, hGan, hG⟩
    rwa [hΦb] at hvN'
  obtain ⟨hQan, hQ⟩ := coordQuot_iterate_spec hNo (σ i) m F hFan hdiv
  refine ⟨fun v => (coordQuot (σ i))^[m] F (ψ v), fun v hv => ?_, fun v hv => ?_⟩
  · exact (hQan (ψ v) ⟨v, hv, rfl⟩).comp ((ψ : E →L[𝕜] (Fin n → 𝕜)).analyticAt v)
  · rw [hQ (ψ v) ⟨v, hv, rfl⟩]
    change extendSection 𝕜 E (comapSection π h.contMDiff f) (Φ.symm (ψ.symm (ψ v))) = _
    rw [ψ.symm_apply_apply, extendSection_of_mem 𝕜 E (comapSection π h.contMDiff f)
      (show Φ.symm v ∈ preimageOpens π h.contMDiff U from hv.2), comapSection_apply,
      extendSection_of_mem 𝕜 E f hv.2]

/-- The representatives of the transform of a germ in two
blow-up charts at a point differ by a unit (the remark after (60.3) in [Kol07, Definition 60]). -/
theorem rep_div_unit (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
    {φ₁ φ₂ : OpenPartialHomeomorph M E} {σ₁ σ₂ : Fin c ↪ Fin n} {i₁ i₂ : Fin c}
    {Φ₁ Φ₂ : OpenPartialHomeomorph M' E} (hφ₁ : IsAdaptedChart ψ Y φ₁ σ₁)
    (hΦ₁ : IsBlowUpChart ψ π φ₁ σ₁ i₁ Φ₁) (hφ₂ : IsAdaptedChart ψ Y φ₂ σ₂)
    (hΦ₂ : IsBlowUpChart ψ π φ₂ σ₂ i₂ Φ₂) {a' : M'} (ha₁ : a' ∈ Φ₁.source) (ha₂ : a' ∈ Φ₂.source)
    {m : ℕ} (s : (structureSheaf 𝕜 E M).presheaf.stalk (π a'))
    {g₁ g₂ : (structureSheaf 𝕜 E M').presheaf.stalk a'}
    (hg₁ : coord E ψ Φ₁ hΦ₁.mem_maximalAtlas ha₁ (σ₁ i₁) ^ m * g₁ = germMap π h.contMDiff a' s)
    (hg₂ : coord E ψ Φ₂ hΦ₂.mem_maximalAtlas ha₂ (σ₂ i₂) ^ m * g₂ = germMap π h.contMDiff a' s) :
    ∃ w : (structureSheaf 𝕜 E M').presheaf.stalk a', IsUnit w ∧ g₁ = w * g₂ := by
  have := isDomain_stalk ψ hΦ₁.mem_maximalAtlas ha₁
  have hspan : Ideal.span {coord E ψ Φ₁ hΦ₁.mem_maximalAtlas ha₁ (σ₁ i₁)} =
      Ideal.span {coord E ψ Φ₂ hΦ₂.mem_maximalAtlas ha₂ (σ₂ i₂)} := by
    rw [← stalkIdeal_exceptionalIdealSheaf_eq_span_coord hY h hφ₁ hΦ₁ ha₁,
      ← stalkIdeal_exceptionalIdealSheaf_eq_span_coord hY h hφ₂ hΦ₂ ha₂]
  obtain ⟨w, hw⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  refine ⟨↑(w ^ m), (w ^ m).isUnit, ?_⟩
  have hne : coord E ψ Φ₁ hΦ₁.mem_maximalAtlas ha₁ (σ₁ i₁) ^ m ≠ 0 :=
    pow_ne_zero m (coord_ne_zero hΦ₁.mem_maximalAtlas ha₁ (σ₁ i₁))
  apply mul_left_cancel₀ hne
  rw [hg₁, ← hg₂, ← hw, mul_pow, Units.val_pow_eq_pow_val]
  ring

/-- At a point of the centre, the centred adapted coordinates in Kollár's order are
the adapted coordinates, and the chart centre `chartCenter x r` of the algebraic strand is the
stalk of `I_Y`. -/
theorem chartCenter_eq_stalkIdeal_idealSheaf (hY : IsClosedSubmanifold ψ Y c)
    (hφ : IsAdaptedChart ψ Y φ σ) {a : M} (ha : a ∈ Y) (haφ : a ∈ φ.source)
    (x : Fin n → (structureSheaf 𝕜 E M).presheaf.stalk a) (r : Fin n) (τ : Fin n ≃ Fin n)
    (hτr : τ r = σ i)
    (hτ : ∀ j, x j = coord E ψ φ hφ.1 haφ (τ j) -
      const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hφ.1 haφ (τ j))))
    (hlt : ∀ j, j < r ↔ ∃ k, k ≠ i ∧ τ j = σ k) :
    chartCenter x r = hY.idealSheaf.stalkIdeal a := by
  have hcen : ∀ j k, τ j = σ k → x j = coord E ψ φ hφ.1 haφ (σ k) := by
    intro j k hjk
    rw [hτ j, hjk, eval_coord, (hφ.2 a haφ).1 ha k, map_zero, sub_zero]
  rw [hY.stalkIdeal_idealSheaf_eq_span ha hφ haφ, chartCenter]
  congr 1
  ext s
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases lt_or_eq_of_le (show j ≤ r from hj) with hj' | rfl
    · obtain ⟨k, -, hτj⟩ := (hlt j).mp hj'
      exact ⟨k, (hcen j k hτj).symm⟩
    · exact ⟨i, (hcen j i hτr).symm⟩
  · rintro ⟨k, rfl⟩
    by_cases hk : k = i
    · refine ⟨r, show r ≤ r from le_rfl, ?_⟩
      rw [hk]
      exact hcen r i hτr
    · exact ⟨τ.symm (σ k), show τ.symm (σ k) ≤ r from
        ((hlt _).mpr ⟨k, hk, τ.apply_symm_apply _⟩).le, hcen _ k (τ.apply_symm_apply _)⟩

/-- The chart ring `IsLocalRing.chartRing` maps to the germ ring at a point of the chart over
the centre, with `χ ∘ algebraMap = germMap π`, `x_j / x_r ↦ u_j` (`j < r`) and `x_r ↦ u_i`. -/
theorem exists_chartRing_hom (h : IsBlowUp ψ Y c π) (hφ : IsAdaptedChart ψ Y φ σ)
    (hΦ : IsBlowUpChart ψ π φ σ i Φ) {a' : M'} (ha' : a' ∈ Φ.source) (haY : π a' ∈ Y)
    (x : Fin n → (structureSheaf 𝕜 E M).presheaf.stalk (π a')) (r : Fin n)
    (τ : Fin n ≃ Fin n) (hτr : τ r = σ i)
    (hτ : ∀ j, x j = coord E ψ φ hφ.1 (hΦ.source_subset ha') (τ j) -
      const 𝕜 E M (π a') (eval 𝕜 E M (π a') (coord E ψ φ hφ.1 (hΦ.source_subset ha') (τ j))))
    (hlt : ∀ j, j < r ↔ ∃ k, k ≠ i ∧ τ j = σ k) :
    ∃ χ : chartRing x r →+* (structureSheaf 𝕜 E M').presheaf.stalk a',
      (∀ s, χ (algebraMap _ _ s) = germMap π h.contMDiff a' s) ∧
      (∀ j, j < r →
        χ (chartYR x r j) = coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ j)) ∧
      χ (algebraMap _ _ (x r)) = coord E ψ Φ hΦ.mem_maximalAtlas ha' (σ i) := by
  have haφ : π a' ∈ φ.source := hΦ.source_subset ha'
  have hcen : ∀ j k, τ j = σ k → x j = coord E ψ φ hφ.1 haφ (σ k) := by
    intro j k hjk
    rw [hτ j, hjk, eval_coord, (hφ.2 _ haφ).1 haY k, map_zero, sub_zero]
  have hxr : x r = coord E ψ φ hφ.1 haφ (σ i) := hcen r i hτr
  have hρr : germMap π h.contMDiff a' (x r) = coord E ψ Φ hΦ.mem_maximalAtlas ha' (σ i) := by
    rw [hxr]
    exact IsBlowUpChart.germMap_coord_self h.contMDiff hφ.1 hΦ ha'
  have hρj : ∀ j, j < r → germMap π h.contMDiff a' (x j) =
      coord E ψ Φ hΦ.mem_maximalAtlas ha' (σ i) * coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ j) := by
    intro j hj
    obtain ⟨k, hk, hτj⟩ := (hlt j).mp hj
    rw [hcen j k hτj, hτj]
    exact IsBlowUpChart.germMap_coord_of_ne h.contMDiff hφ.1 hΦ ha' hk
  have hdom := isDomain_stalk ψ hΦ.mem_maximalAtlas ha'
  let L := FractionRing ((structureSheaf 𝕜 E M').presheaf.stalk a')
  let ι : (structureSheaf 𝕜 E M').presheaf.stalk a' →+* L := algebraMap _ L
  have hι : Function.Injective ι := IsFractionRing.injective _ L
  have hu0 : coord E ψ Φ hΦ.mem_maximalAtlas ha' (σ i) ≠ 0 :=
    coord_ne_zero hΦ.mem_maximalAtlas ha' (σ i)
  have hunit : ∀ y : Submonoid.powers (x r), IsUnit ((ι.comp (germMap π h.contMDiff a')) y) := by
    rintro ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hy
    change IsUnit (ι (germMap π h.contMDiff a' (x r ^ k)))
    rw [map_pow, hρr, map_pow]
    refine (isUnit_iff_ne_zero.mpr ?_).pow k
    exact (IsFractionRing.to_map_eq_zero_iff (K := L)).not.mpr hu0
  let Λ : Localization.Away (x r) →+* L := IsLocalization.lift hunit
  have hΛalg : ∀ s, Λ (algebraMap _ _ s) = ι (germMap π h.contMDiff a' s) := fun s =>
    IsLocalization.lift_eq hunit s
  have hΛmk : ∀ j, j < r → Λ (Localization.mk (x j) ⟨x r, Submonoid.mem_powers _⟩) =
      ι (coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ j)) := by
    intro j hj
    rw [Localization.mk_eq_mk'_apply, IsLocalization.lift_mk'_spec]
    change ι (germMap π h.contMDiff a' (x j)) = ι (germMap π h.contMDiff a' (x r)) * _
    rw [hρj j hj, hρr, map_mul]
  have hrange : ∀ s : chartRing x r, ∃ b, ι b = Λ (s : Localization.Away (x r)) := by
    intro s
    have hs : (s : Localization.Away (x r)) ∈
        Algebra.adjoin ((structureSheaf 𝕜 E M).presheaf.stalk (π a'))
          ((fun j : Fin n => Localization.mk (x j) ⟨x r, Submonoid.mem_powers (x r)⟩) ''
            {j | j < r}) :=
      s.2
    refine Algebra.adjoin_induction (p := fun z _ => ∃ b, ι b = Λ z) ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨j, hj, rfl⟩
      exact ⟨_, (hΛmk j hj).symm⟩
    · intro r'
      exact ⟨_, (hΛalg r').symm⟩
    · rintro a b _ _ ⟨a', ha'⟩ ⟨b', hb'⟩
      exact ⟨a' + b', by rw [map_add, ha', hb', map_add]⟩
    · rintro a b _ _ ⟨a', ha'⟩ ⟨b', hb'⟩
      exact ⟨a' * b', by rw [map_mul, ha', hb', map_mul]⟩
  choose χ₀ hχ₀ using hrange
  let χ : chartRing x r →+* (structureSheaf 𝕜 E M').presheaf.stalk a' :=
    { toFun := χ₀
      map_one' := hι (by rw [hχ₀, OneMemClass.coe_one, map_one, map_one])
      map_mul' := fun a b => hι (by rw [hχ₀, MulMemClass.coe_mul, map_mul, map_mul, hχ₀, hχ₀])
      map_zero' := hι (by rw [hχ₀, ZeroMemClass.coe_zero, map_zero, map_zero])
      map_add' := fun a b => hι (by rw [hχ₀, AddMemClass.coe_add, map_add, map_add, hχ₀, hχ₀]) }
  have hχ : ∀ (z : chartRing x r) b,
      χ z = b ↔ Λ (z : Localization.Away (x r)) = ι b := by
    intro z b
    constructor
    · intro hz
      rw [← hz]
      exact (hχ₀ z).symm
    · intro hz
      exact hι ((hχ₀ z).trans hz)
  refine ⟨χ, fun s => (hχ _ _).mpr ?_, fun j hj => (hχ _ _).mpr ?_, (hχ _ _).mpr ?_⟩
  · rw [Subalgebra.coe_algebraMap, hΛalg]
  · rw [chartYR, coe_chartYROf,
      chartYOf_of_lt _ _ _ hj]
    exact hΛmk j hj
  · rw [Subalgebra.coe_algebraMap, hΛalg, hρr]

/-- Through any chart-ring map `χ` compatible with the
germ map, the stalk of the marked transform of `(I, m)` is the image of the algebraic transform
`transformIdeal x r I_a m`. -/
theorem birationalTransform_stalkIdeal_eq_map_transformIdeal (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) (hφ : IsAdaptedChart ψ Y φ σ) (hΦ : IsBlowUpChart ψ π φ σ i Φ)
    {a' : M'} (ha' : a' ∈ Φ.source) (haY : π a' ∈ Y)
    (x : Fin n → (structureSheaf 𝕜 E M).presheaf.stalk (π a')) (r : Fin n)
    (τ : Fin n ≃ Fin n) (hτr : τ r = σ i)
    (hτ : ∀ j, x j = coord E ψ φ hφ.1 (hΦ.source_subset ha') (τ j) -
      const 𝕜 E M (π a') (eval 𝕜 E M (π a') (coord E ψ φ hφ.1 (hΦ.source_subset ha') (τ j))))
    (hlt : ∀ j, j < r ↔ ∃ k, k ≠ i ∧ τ j = σ k)
    (χ : chartRing x r →+* (structureSheaf 𝕜 E M').presheaf.stalk a')
    (hχ : ∀ s, χ (algebraMap _ _ s) = germMap π h.contMDiff a' s)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) {m : ℕ}
    (hm : ∀ a ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I a) :
    (MarkedIdealSheaf.birationalTransform hY h ⟨I, m⟩).I.stalkIdeal a' =
      Ideal.map χ (transformIdeal x r (I.stalkIdeal (π a')) m) := by
  have haφ : π a' ∈ φ.source := hΦ.source_subset ha'
  have hxr : x r = coord E ψ φ hφ.1 haφ (σ i) := by
    have := hτ r
    rwa [hτr, eval_coord, (hφ.2 _ haφ).1 haY i, map_zero, sub_zero] at this
  have hχr : χ (algebraMap _ _ (x r)) = coord E ψ Φ hΦ.mem_maximalAtlas ha' (σ i) := by
    rw [hχ, hxr]
    exact IsBlowUpChart.germMap_coord_self h.contMDiff hφ.1 hΦ ha'
  have hdom := isDomain_stalk ψ hΦ.mem_maximalAtlas ha'
  have hu0 : coord E ψ Φ hΦ.mem_maximalAtlas ha' (σ i) ≠ 0 :=
    coord_ne_zero hΦ.mem_maximalAtlas ha' (σ i)
  have hcolon := isDivExceptional_birationalTransform hY h ⟨I, m⟩ hm a'
  rw [hcolon]
  dsimp only
  rw [stalkIdeal_exceptionalIdealSheaf_eq_span_coord hY h hφ hΦ ha', Ideal.span_singleton_pow,
    Submodule.colon_span, IdealSheaf.stalkIdeal_pullback]
  obtain ⟨U, hU, k, f₀, -, hf₀⟩ := I.exists_generators (π a')
  set f : Fin k → (structureSheaf 𝕜 E M).presheaf.stalk (π a') := fun j =>
    (structureSheaf 𝕜 E M).presheaf.germ U (π a') hU (f₀ j) with hfdef
  have hf : Ideal.span (Set.range f) = I.stalkIdeal (π a') := (hf₀ (π a') hU).symm
  have hJle : I.stalkIdeal (π a') ≤ chartCenter x r ^ m := by
    rw [chartCenter_eq_stalkIdeal_idealSheaf hY hφ haY haφ x r τ hτr hτ hlt]
    exact (IdealSheaf.le_ordAlongIdeal_iff _ _ _ _).mp (hm _ haY)
  have hfJ : ∀ j, f j ∈ I.stalkIdeal (π a') := fun j => hf ▸ Ideal.subset_span ⟨j, rfl⟩
  choose g hg using fun j => exists_algebraMap_pow_mul_eq x r (hJle (hfJ j))
  have hgT : ∀ j, g j ∈ transformIdeal x r (I.stalkIdeal (π a')) m := fun j =>
    Ideal.subset_span ⟨f j, hfJ j, hg j⟩
  have hρf : ∀ j, germMap π h.contMDiff a' (f j) =
      coord E ψ Φ hΦ.mem_maximalAtlas ha' (σ i) ^ m * χ (g j) := by
    intro j
    rw [← hχ, ← hg j, map_mul, map_pow, hχr]
  have hmap : Ideal.map (germMap π h.contMDiff a') (I.stalkIdeal (π a')) = Ideal.span
      (Set.range fun j => coord E ψ Φ hΦ.mem_maximalAtlas ha' (σ i) ^ m * χ (g j)) := by
    rw [← hf, Ideal.map_span, ← Set.range_comp]
    exact congrArg Ideal.span (congrArg Set.range (funext hρf))
  rw [hmap, Ideal.colon_span_range_pow_mul hu0 m]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact Ideal.mem_map_of_mem _ (hgT j)
  · rw [Ideal.map_le_iff_le_comap, transformIdeal, Ideal.span_le]
    rintro g' ⟨f', hf', hg'⟩
    have hmem' : coord E ψ Φ hΦ.mem_maximalAtlas ha' (σ i) ^ m * χ g' =
        germMap π h.contMDiff a' f' := by
      rw [← hχr, ← map_pow, ← map_mul, hg', hχ]
    rw [SetLike.mem_coe, Ideal.mem_comap, ← Ideal.colon_span_range_pow_mul hu0 m,
      Submodule.mem_colon_singleton, smul_eq_mul, mul_comm, hmem', ← hmap]
    exact Ideal.mem_map_of_mem _ hf'

end Manifold
