/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Transform.Basic
import Hironaka.Manifold.BlowUp.Divisor
import Hironaka.Manifold.BlowUp.Restrict
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.BlowUp.Transform.Weak
import Hironaka.Manifold.BlowUp.Unique
import Hironaka.Manifold.Germ.StalkNoetherian
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.LocalDiffeomorph
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The birational transform is the weak transform iff the mark is the order

For a nowhere-zero ideal sheaf `I` and a nonempty connected centre `Y`, the birational transform
`π_*^{-1}(I, m) = I_F^{-m} π⁻¹(I)` (`m ≤ ν_Y(I)`) coincides with Hironaka's weak transform
`I_F^{-ν} π⁻¹(I)` exactly when `m = ν_Y(I)` [Kol07, Definition 48]. The direction (←) is the
uniqueness of the colon specification (`Hironaka.Manifold.BlowUp.Transform.Colon`) once the
exponents agree stalkwise: over the exceptional divisor the weak exponent is the generic order
along the component through the point, which is the order `ν` at every point of the connected
centre (`Hironaka.Manifold.BlowUp.Transform.OrderAlong`); off `F` the stalk of `I_F` is the
unit ideal and every colon is `π⁻¹(I)` itself.

The direction (→) is where the hypotheses `I ≠ 0` and `m ≤ ν` are used. Krull's intersection
theorem in the Noetherian local stalk makes `ν` finite (`ordAlong_ne_top`). If `m < ν`, pick `a'`
over `a` in a blow-up chart with scaling coordinate `u` (the stalk of `I_F` is `(u)`; the centre
has positive codimension, otherwise `I_{Y,a} = 0` and `ν = 0`). Equality of the transforms says
`(π⁻¹(I)_{a'} : u^m) = (π⁻¹(I)_{a'} : u^ν)`; since `π⁻¹(I)_{a'} ⊆ (u^ν)`, every element of this
colon is `u^{ν-m}` times another one, so the colon lies in `𝔪` times itself and vanishes by
Nakayama, whence `π⁻¹(I)_{a'} = 0` (`Ideal.eq_bot_of_colon_pow_eq`, in the domain stalk). Finally
the germ map `𝒪_{M, π a'} → 𝒪_{M', a'}` of a blowing-up is injective
(`IsBlowUp.germMap_injective`): a germ vanishing near `a'` vanishes on the open image of a
neighbourhood of a point off `F` (where `π` is a local diffeomorphism; such points are dense),
and the identity theorem on a chart ball of `M` finishes; so `I_a = 0`, a contradiction. The
source states the coincidence without proof.
-/

public section

open TopologicalSpace Opposite CategoryTheory Filter Topology IsLocalRing Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

section Algebra

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]

/-- The algebraic core of the comparison of the
marked and the weak transform. In a Noetherian local domain, if `J ⊆ (u^k)`, `u ∈ 𝔪`, and the
colons `(J : u^m)` and `(J : u^k)` agree for some `m < k`, then `J = 0`: every `x ∈ (J : u^k)`
satisfies `x u^m ∈ J ⊆ (u^k)`, so `x = u^{k-m} y` with `y ∈ (J : u^k)`; hence
`(J : u^k) ⊆ 𝔪 (J : u^k)` vanishes by Nakayama, and `J = u^k (J : u^k) = 0`. -/
theorem _root_.Ideal.eq_bot_of_colon_pow_eq {u : R} (hu : u ∈ maximalIdeal R) (hu0 : u ≠ 0)
    {J : Ideal R} {m k : ℕ} (hmk : m < k) (hle : J ≤ Ideal.span {u} ^ k)
    (hcol : J.colon ↑(Ideal.span {u} ^ m) = J.colon ↑(Ideal.span {u} ^ k)) : J = ⊥ := by
  have hkm : u ^ k = u ^ m * u ^ (k - m) := by rw [← pow_add, Nat.add_sub_cancel' hmk.le]
  have hpow : u ^ (k - m) ∈ maximalIdeal R := Ideal.pow_mem_of_mem _ hu _ (Nat.sub_pos_of_lt hmk)
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, Submodule.colon_span,
    Submodule.colon_span] at hcol
  rw [Ideal.span_singleton_pow] at hle
  have hC : J.colon {u ^ k} = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) _
      (IsNoetherian.noetherian _) ?_ (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    intro x hx
    have hx' : x ∈ J.colon {u ^ m} := by rw [hcol]; exact hx
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hx hx'
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (hle hx')
    have hx2 : x = u ^ (k - m) * y := by
      apply mul_left_cancel₀ (pow_ne_zero m hu0)
      rw [mul_comm (u ^ m) x, ← hy, hkm]
      ring
    have hyJ : y ∈ J.colon {u ^ k} := by
      rw [Submodule.mem_colon_singleton, smul_eq_mul, hy]
      exact hx'
    rw [hx2]
    exact Submodule.smul_mem_smul hpow hyJ
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (hle hz)
  have hwC : w ∈ J.colon {u ^ k} := by
    rw [Submodule.mem_colon_singleton, smul_eq_mul, hw]
    exact hz
  rw [hC, Ideal.mem_bot] at hwC
  rw [Ideal.mem_bot, ← hw, hwC, zero_mul]

end Algebra

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] {Y : Set M} {c : ℕ}

/-- The order of `I`
along `Y` at `a ∈ Y` is finite when `I_a ≠ 0` — Krull's intersection theorem in the Noetherian local
stalk: `⋂_p I_{Y,a}^p = 0`, so `I_a ⊆ I_{Y,a}^p` for every `p` would force `I_a = 0`. -/
theorem IsClosedSubmanifold.ordAlong_ne_top (hY : IsClosedSubmanifold ψ Y c)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) {a : M} (ha : a ∈ Y) (hne : I.stalkIdeal a ≠ ⊥) :
    IdealSheaf.ordAlongIdeal hY.idealSheaf I a ≠ ⊤ := by
  intro htop
  have : FiniteDimensional 𝕜 E := LinearEquiv.finiteDimensional ψ.symm.toLinearEquiv
  have hD : hY.idealSheaf.stalkIdeal a ≠ ⊤ := by
    have : a ∈ hY.idealSheaf.support := by rw [hY.cosupport_idealSheaf]; exact ha
    exact this
  have hle : ∀ p : ℕ, I.stalkIdeal a ≤ hY.idealSheaf.stalkIdeal a ^ p := fun p =>
    (IdealSheaf.le_ordAlongIdeal_iff hY.idealSheaf I a p).mp (by rw [htop]; exact le_top)
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (I := hY.idealSheaf.stalkIdeal a) hD
  exact hne (le_bot_iff.mp (by rw [← hK]; exact le_iInf hle))

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M}

/-- **The germ map of a blowing-up is
injective**. A germ at `π a'` whose pull-back vanishes near `a'` vanishes on the open image of a
neighbourhood of a point `b` off the exceptional divisor (`π` is a local diffeomorphism
there, and such points are dense), hence — by the identity theorem on a chart ball of `M` around
`π a'` containing `π b` — near `π a'`. -/
theorem IsBlowUp.germMap_injective (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) (a' : M') : Function.Injective (germMap π h.contMDiff a') := by
  refine (injective_iff_map_eq_zero _).mpr fun s hs => ?_
  obtain ⟨V, haV, f, rfl⟩ := (structureSheaf 𝕜 E M).presheaf.exists_germ_eq s
  have hπc : Continuous π := h.contMDiff.continuous
  have h1 : ∀ᶠ b in 𝓝 a', extendSection 𝕜 E f (π b) = 0 := by
    have := congrArg (stalkToGerm 𝓘(𝕜, E) ω M' a') hs
    rw [stalkToGerm_germMap, stalkToGerm_structureSheaf_germ, map_zero, Germ.coe_compTendsto,
      ← Germ.coe_zero, Germ.coe_eq] at this
    exact this
  obtain ⟨N, hNsub, hNo, haN⟩ := mem_nhds_iff.mp h1
  set a : M := π a' with hadef
  set χ : OpenPartialHomeomorph M E := chartAt E a with hχdef
  have hχ : χ ∈ maximalAtlas 𝓘(𝕜, E) ω M :=
    IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, E)) (n := ω) a
  have haχ : a ∈ χ.source := mem_chart_source E a
  set T : Set (Fin n → 𝕜) := ψ '' (χ.target ∩ χ.symm ⁻¹' (V : Set M)) with hTdef
  have hTo : IsOpen T := ψ.isOpenMap _ (χ.isOpen_inter_preimage_symm V.2)
  have haT : ψ (χ a) ∈ T :=
    ⟨χ a, ⟨χ.map_source haχ, by rw [Set.mem_preimage, χ.left_inv haχ]; exact haV⟩, rfl⟩
  obtain ⟨r, hr0, hball⟩ := Metric.isOpen_iff.mp hTo _ haT
  set F : (Fin n → 𝕜) → 𝕜 := fun w => extendSection 𝕜 E f (χ.symm (ψ.symm w)) with hFdef
  have hFan : AnalyticOnNhd 𝕜 F (Metric.ball (ψ (χ a)) r) := by
    have h2 : ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, E) ω (fun w => χ.symm (ψ.symm w)) T := by
      refine (contMDiffOn_symm_of_mem_maximalAtlas hχ).comp
        ((ψ.symm : (Fin n → 𝕜) →L[𝕜] E).contMDiff.contMDiffOn) ?_
      rintro _ ⟨v, hv, rfl⟩
      change ψ.symm (ψ v) ∈ χ.target
      rw [ψ.symm_apply_apply]
      exact hv.1
    have h3 : ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜) ω F T := by
      refine (contMDiffOn_extendSection f).comp h2 ?_
      rintro _ ⟨v, hv, rfl⟩
      change χ.symm (ψ.symm (ψ v)) ∈ (V : Set M)
      rw [ψ.symm_apply_apply]
      exact hv.2
    exact fun w hw => ((contMDiffOn_iff_contDiffOn.mp (h3.mono hball)).contDiffAt
      (Metric.isOpen_ball.mem_nhds hw)).analyticAt
  have hopen : IsOpen (N ∩ π ⁻¹' (χ.source ∩ χ ⁻¹' (ψ ⁻¹' Metric.ball (ψ (χ a)) r))) :=
    hNo.inter ((χ.continuousOn.isOpen_inter_preimage χ.open_source
      (Metric.isOpen_ball.preimage ψ.continuous)).preimage hπc)
  have hmem : a' ∈ N ∩ π ⁻¹' (χ.source ∩ χ ⁻¹' (ψ ⁻¹' Metric.ball (ψ (χ a)) r)) :=
    ⟨haN, haχ, Metric.mem_ball_self hr0⟩
  obtain ⟨b, ⟨hbN, hbχ, hbball⟩, hbY⟩ :=
    (h.dense_preimage_compl hY).inter_open_nonempty _ hopen ⟨a', hmem⟩
  obtain ⟨Ψ, hbΨ, hEq⟩ := (h.isLocalDiffeomorphOn_compl ⟨b, hbY⟩).exists_partialDiffeomorph
  set W : Set M := Ψ.toPartialEquiv '' (Ψ.source ∩ N) with hWdef
  have hWo : IsOpen W := by
    rw [hWdef, Ψ.toPartialEquiv.image_source_inter_eq']
    exact Ψ.toOpenPartialHomeomorph.isOpen_inter_preimage_symm hNo
  have hbW : π b ∈ W := ⟨b, ⟨hbΨ, hbN⟩, (hEq hbΨ).symm⟩
  have hfW : ∀ y ∈ W, extendSection 𝕜 E f y = 0 := by
    rintro _ ⟨x, ⟨hxΨ, hxN⟩, rfl⟩
    rw [← hEq hxΨ]
    exact hNsub hxN
  have hev : F =ᶠ[𝓝 (ψ (χ (π b)))] 0 := by
    have hcont : ContinuousAt (fun w => χ.symm (ψ.symm w)) (ψ (χ (π b))) := by
      have h4 : ContinuousAt χ.symm (ψ.symm (ψ (χ (π b)))) := by
        rw [ψ.symm_apply_apply]
        exact χ.continuousAt_symm (χ.map_source hbχ)
      exact h4.comp ψ.symm.continuous.continuousAt
    have hW' : (fun w => χ.symm (ψ.symm w)) ⁻¹' W ∈ 𝓝 (ψ (χ (π b))) := by
      refine hcont.preimage_mem_nhds ?_
      rw [ψ.symm_apply_apply, χ.left_inv hbχ]
      exact hWo.mem_nhds hbW
    filter_upwards [hW'] with w hw
    exact hfW _ hw
  have hEqOn := hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected hbball hev
  apply stalkToGerm_injective 𝓘(𝕜, E) ω M a
  rw [stalkToGerm_structureSheaf_germ, map_zero, ← Germ.coe_zero, Germ.coe_eq]
  filter_upwards [((ψ.continuous.comp_continuousOn χ.continuousOn).continuousWithinAt haχ
      |>.continuousAt (χ.open_source.mem_nhds haχ)).preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr0)), χ.open_source.mem_nhds haχ]
    with x hx hxs
  have := hEqOn hx
  change extendSection 𝕜 E f (χ.symm (ψ.symm (ψ (χ x)))) = 0 at this
  rwa [ψ.symm_apply_apply, χ.left_inv hxs] at this

/-- The one-step form at exact order: if the order
of `I` along the centre is `m` at every point of `Y`, the marked transform of `(I, m)` is the weak
transform — the two colon specifications agree stalkwise (over `Y` the weak exponent is the generic
order, which is `m`; off the exceptional divisor both colons are by the unit ideal) and the colon
stalks determine the sheaf. This is the converse half of
`birationalTransform_eq_weakTransformOf_iff` below, in the form used along a succession of
blowings-up. -/
theorem birationalTransform_eq_weakTransformOf_of_ordAlong_eq [T2Space M]
    [SecondCountableTopology M] (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π) (I :
        IdealSheaf (structureSheaf 𝕜 E M)) {m : ℕ}
    (hord : ∀ a ∈ Y, IdealSheaf.ordAlongIdeal hY.idealSheaf I a = m) :
    (MarkedIdealSheaf.birationalTransform hY h ⟨I, m⟩).I = IdealSheaf.weakTransformOf hY h I := by
  have hm' : ∀ y ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I y := fun y hy =>
    (hord y hy).ge
  have hexp : ∀ a' : M', π a' ∈ Y →
      (IdealSheaf.genericOrdAlong hY.idealSheaf I (π a')).toNat = m := fun a' ha' => by
    rw [genericOrdAlong_eq_ordAlong hY I ha', hord _ ha', ENat.toNat_natCast]
  refine IsDivExceptional.unique (isDivExceptional_birationalTransform hY h ⟨I, m⟩ hm') ?_
  intro a'
  have h2 := isDivExceptional_weakTransformOf hY h I a'
  dsimp only at h2 ⊢
  rw [h2]
  by_cases ha' : π a' ∈ Y
  · rw [hexp a' ha']
  · rw [stalkIdeal_exceptionalIdealSheaf_of_notMem hY h ha', Ideal.top_pow, Ideal.top_pow]

/-- On a nonempty connected centre and for nowhere-zero `I`,
**the birational transform of `(I, m)` is the weak transform iff `m` is the (generic) order `ν`
of `I` along `Y`** [Kol07, Definition 48]. (←) The two colon specifications agree stalkwise — over
`Y` the weak exponent is the generic order, equal to `ν = m` by the constancy of the order along
the connected centre (`ordAlong_eq_of_isPreconnected`), and off `F` both colons are by the unit
ideal — and the colon stalks determine the sheaf. (→) If `m < ν` (finite by Krull,
`ordAlong_ne_top`), take `a'` over `a` (the centre has positive codimension, else `I_{Y,a} = 0` and
`ν = 0`) in a blow-up chart with scaling coordinate `u`: the colons `(π⁻¹(I)_{a'} : u^m)` and
`(π⁻¹(I)_{a'} : u^ν)` agree, so `π⁻¹(I)_{a'} = 0` by Nakayama in the domain stalk
(`Ideal.eq_bot_of_colon_pow_eq`), hence `I_a = 0` by the injectivity of the germ map — against `I ≠
0`. -/
theorem birationalTransform_eq_weakTransformOf_iff [T2Space M] [SecondCountableTopology M]
    (hY : IsClosedSubmanifold ψ Y c) (hconn : IsPreconnected Y) (h : IsBlowUp ψ Y c π) (I :
        IdealSheaf (structureSheaf 𝕜 E M))
    (hne : ∀ a ∈ Y, I.stalkIdeal a ≠ ⊥) {a : M} (ha : a ∈ Y) {m : ℕ}
    (hm : (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I a) :
    (MarkedIdealSheaf.birationalTransform hY h ⟨I, m⟩).I = IdealSheaf.weakTransformOf hY h I ↔
      (m : ℕ∞) = IdealSheaf.ordAlongIdeal hY.idealSheaf I a := by
  have hconst : ∀ y ∈ Y,
      IdealSheaf.ordAlongIdeal hY.idealSheaf I y = IdealSheaf.ordAlongIdeal hY.idealSheaf I a :=
    fun y hy => ordAlong_eq_of_isPreconnected hY I (subset_refl Y) hconn hy ha
  have hm' : ∀ y ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I y := fun y hy => by
    rw [hconst y hy]; exact hm
  obtain ⟨k, hk⟩ : ∃ k : ℕ, IdealSheaf.ordAlongIdeal hY.idealSheaf I a = k :=
    ⟨_, (ENat.natCast_toNat_eq_self.mpr (hY.ordAlong_ne_top I ha (hne a ha))).symm⟩
  have hbt := isDivExceptional_birationalTransform hY h ⟨I, m⟩ hm'
  have hwk := isDivExceptional_weakTransformOf hY h I
  have hexp : ∀ a' : M', π a' ∈ Y →
      (IdealSheaf.genericOrdAlong hY.idealSheaf I (π a')).toNat = k := fun a' ha' => by
    rw [genericOrdAlong_eq_ordAlong hY I ha', hconst _ ha', hk, ENat.toNat_natCast]
  constructor
  · intro heq
    by_contra hne'
    have hlt : m < k := by
      rw [hk] at hm hne'
      exact lt_of_le_of_ne (by exact_mod_cast hm) (by exact_mod_cast hne')
    obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart a ha
    have hc : Nonempty (Fin c) := by
      by_contra hemp
      have : IsEmpty (Fin c) := not_nonempty_iff.mp hemp
      have hD : hY.idealSheaf.stalkIdeal a = ⊥ := by
        rw [hY.stalkIdeal_idealSheaf_eq_span ha hφ haφ, Set.range_eq_empty, Ideal.span_empty]
      have h1 : I.stalkIdeal a ≤ hY.idealSheaf.stalkIdeal a ^ k :=
        (IdealSheaf.le_ordAlongIdeal_iff hY.idealSheaf I a k).mp hk.ge
      rw [hD, ← Ideal.zero_eq_bot, zero_pow (by omega)] at h1
      exact hne a ha (le_bot_iff.mp h1)
    obtain ⟨i₀⟩ := hc
    obtain ⟨a', ha'eq⟩ := IsBlowUp.surjective hY h i₀ a
    have ha' : π a' ∈ Y := by rw [ha'eq]; exact ha
    obtain ⟨i, Φ, hΦ, hp⟩ := h.cover φ σ hφ a' (by rw [ha'eq]; exact haφ)
    have : FiniteDimensional 𝕜 E := LinearEquiv.finiteDimensional ψ.symm.toLinearEquiv
    have hdom := isDomain_stalk ψ hΦ.mem_maximalAtlas hp
    have hu : coord E ψ Φ hΦ.mem_maximalAtlas hp (σ i) ∈
        maximalIdeal ((structureSheaf 𝕜 E M').presheaf.stalk a') := by
      rw [mem_maximalIdeal_iff_eval, eval_coord]
      exact (IsBlowUpChart.mem_preimage_iff hφ hΦ hp).mp ha'
    have hle := IsBlowUp.totalTransform_stalkIdeal_le hY h I (m := k) (a' := a')
      (le_of_eq (by rw [ha'eq, hk]))
    rw [stalkIdeal_exceptionalIdealSheaf_eq_span_coord hY h hφ hΦ hp] at hle
    have h1 := hbt a'
    have h2 := hwk a'
    dsimp only at h1 h2
    rw [heq, h2, hexp a' ha', stalkIdeal_exceptionalIdealSheaf_eq_span_coord hY h hφ hΦ hp] at h1
    have hbot := Ideal.eq_bot_of_colon_pow_eq hu (coord_ne_zero hΦ.mem_maximalAtlas hp (σ i)) hlt
      hle h1.symm
    rw [IdealSheaf.stalkIdeal_pullback,
      Ideal.map_eq_bot_iff_of_injective (h.germMap_injective hY a')] at hbot
    exact hne _ ha' hbot
  · intro hmk
    exact birationalTransform_eq_weakTransformOf_of_ordAlong_eq hY h I fun y hy =>
      (hconst y hy).trans hmk.symm

end Manifold
