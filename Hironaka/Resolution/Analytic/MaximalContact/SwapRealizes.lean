/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Germ.TaylorCompletion
public import Hironaka.Resolution.Analytic.LocalIsoEquiv
public import Hironaka.Manifold.Chart.Basic
public import Hironaka.Manifold.IdealSheaf.Basic
import Hironaka.Algebra.Local.CohenDerivation
import Hironaka.Algebra.Local.PowerSeriesEndomorphism
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.Chart.MaximalContact
import Hironaka.Manifold.Chart.Swap
import Hironaka.Manifold.Completion
import Hironaka.Manifold.Germ.TaylorIdeal
import Hironaka.Manifold.IdealSheaf.Vanishing
import Hironaka.Manifold.Snc.Basic
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Resolution.Analytic.MaximalContact.CommonCharts
import Hironaka.Resolution.Analytic.MaximalContact.CoordCriterion
import Hironaka.Resolution.Analytic.MaximalContact.TaylorTransport
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init

/-!
# The coordinate swap realises the formal equivalence

The formal half of Kollár's uniqueness of maximal contact [Kol07, 95], on the analytic stalk. At
`p` with `ord_p I = m ≥ 1`, take the charts `e = (x₁, y)`, `e' = (x₁', y)` of `exists_commonCharts`
(`Hironaka/Resolution/Analytic/MaximalContact/CommonCharts.lean`: `H = {x₁ = 0}`, `H' = {x₁' = 0}`,
the components of `E` through `p` among the shared coordinates `y`), the coordinate swap
`Φ = e'⁻¹ ∘ e` (`Hironaka/Manifold/Chart/Swap.lean`) and its pullback of germs `r = Φ^*`, with
`T_e ∘ r = T_{e'}` (`IsPullbackStalk.taylorHom_eq'`). Then:

* `r x₁' = x₁` and `r y_j = y_j` (the Taylor identity and the injectivity of `T_e`), so `r` carries
  the vanishing ideal of `H'` onto that of `H` and fixes those of the components of `E`;
* Kollár's formal automorphism `G = T_e ∘ T_{e'}⁻¹` of `𝕜⟦X⟧` (`taylorAut`) is
  `X_{i₀} ↦ X_{i₀} + T_e(x₁' − x₁)`, `X_j ↦ X_j` — of the form `1 + T_e(MC(I)_p)` since
  `x₁, x₁' ∈ MC(I)_p` (`IsOnePlus`, through `eq_substAlgHom_of_forall_X_mem`); by Kollár's
  Proposition 94 (`isInvariantOnePlus_map_taylorHom`,
  `Hironaka/Resolution/Analytic/MaximalContact/TaylorTransport.lean`) `G` maps `Î = T_e(I_p)𝕜⟦X⟧`
  into itself, hence onto itself (`Ideal.map_eq_of_map_le`, Noetherian), and reading
  `T_{e'} = G⁻¹ ∘ T_e` gives `T_e(r(I_p)) 𝕜⟦X⟧ = T_e(I_p) 𝕜⟦X⟧`; through the completion
  isomorphism `𝒪̂_p ≅ 𝕜⟦X⟧` and Krull's intersection theorem (`Ideal.eq_of_map_adicCompletion_eq`)
  this is `r(I_p) = I_p`;
* `s − r s ∈ MC(I)_p` for every germ `s`: on the coordinates of `e'` the defect is `0` or
  `x₁' − x₁ ∈ MC(I)_p`, and the coordinate criterion `sub_mem_of_forall_coord_sub_mem` extends it.

The result (`exists_realizing_swap`; `coordinateSwapAutomorphism_realizes_formal` is the same
statement without the last clause) is propagated to a neighbourhood in
`Hironaka/Resolution/Analytic/MaximalContact/Propagation.lean`. The `Hironaka` library has the same
argument for the completed local ring of a scheme
(`Hironaka/Resolution/Algebraic/MaximalContact/FormalEquivExists.lean`).
-/

@[expose] public section

noncomputable section

open TopologicalSpace IsLocalRing MvPowerSeries AnalyticManifold
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : AnalyticManifold.{u} 𝕜 E}

/-- A point of order exactly `m ≥ 1` lies on every hypersurface of maximal contact (its ideal sheaf
is contained in `MC(I)`, whose stalk at `p` is proper). -/
theorem mem_of_idealSheaf_le_iteratedDeriv (I : AnalyticManifold.IdealSheaf M) {m : ℕ}
    (hm : 1 ≤ m)
    {H : Set M} (hH : IsClosedSubmanifold ψ H 1) (hHmc : hH.idealSheaf ≤ I.iteratedDeriv (m - 1))
    {p : M} (hp : I.ord p = m) : p ∈ H := by
  by_contra hpH
  have h1 := ord_iteratedDeriv_eq_one (E := E) (I := I) hm hp
  have h2 : (I.iteratedDeriv (m - 1)).stalkIdeal p = ⊤ :=
    top_le_iff.mp ((hH.stalkIdeal_idealSheaf_of_notMem hpH).symm.trans_le
      (IdealSheaf.le_def.mp hHmc p))
  have h3 : (I.iteratedDeriv (m - 1)).ord p = 0 :=
    (IdealSheaf.ord_eq_zero_iff (J := I.iteratedDeriv (m - 1))).mpr fun h => h h2
  rw [h1] at h3
  exact one_ne_zero h3

/-- Kollár's formal automorphism `φ^* = T_e ∘ T_{e'}⁻¹` of `𝒪̂_p ≅ 𝕜⟦X⟧` [Kol07, 95], explicitly:
the composite of the two completion isomorphisms (`exists_taylor_automorphism'` of
`Hironaka/Manifold/Chart/Swap.lean`, made a definition so that its action on the whole
completion is available). -/
def taylorAut (e e' : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M)
    (he' : e' ∈ maximalAtlas 𝓘(𝕜, E) ω M) {p : M} (hpe : p ∈ e.source) (hpe' : p ∈ e'.source) :
    MvPowerSeries (Fin n) 𝕜 ≃+* MvPowerSeries (Fin n) 𝕜 :=
  (taylorCompletionEquiv E ψ e' hpe' he').symm.trans (taylorCompletionEquiv E ψ e hpe he)

section TaylorAut

variable {e e' : OpenPartialHomeomorph M E} {he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M}
  {he' : e' ∈ maximalAtlas 𝓘(𝕜, E) ω M} {p : M} {hpe : p ∈ e.source} {hpe' : p ∈ e'.source}

omit [FiniteDimensional 𝕜 E] in
/-- The formal automorphism carries the `e'`-expansion of every germ to its `e`-expansion. -/
theorem taylorAut_apply_taylorHom (s : (structureSheaf 𝕜 E M).presheaf.stalk p) :
    taylorAut ψ e e' he he' hpe hpe' (taylorHom E ψ e' hpe' he' s) = taylorHom E ψ e hpe he s := by
  rw [taylorAut, RingEquiv.trans_apply, ← taylorCompletionEquiv_algebraMap E ψ e' hpe' he' s,
    RingEquiv.symm_apply_apply, taylorCompletionEquiv_algebraMap]

omit [FiniteDimensional 𝕜 E] in
/-- The formal automorphism on the whole completion: `φ^* ∘ T̂_{e'} = T̂_e`. -/
theorem taylorAut_apply_taylorCompletionEquiv
    (h : AdicCompletion (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk p))
      ((structureSheaf 𝕜 E M).presheaf.stalk p)) :
    taylorAut ψ e e' he he' hpe hpe' (taylorCompletionEquiv E ψ e' hpe' he' h) =
      taylorCompletionEquiv E ψ e hpe he h := by
  rw [taylorAut, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]

end TaylorAut

/-- **The coordinate swap realises the formal equivalence** [Kol07, 95], the working form, with
Kollár's formal automorphism `T_e ∘ T_{e'}⁻¹` written as `1 + T_e(MC(I)_p)` on the whole of
`𝕜⟦X⟧`. For `I` MC-invariant, `p` of order exactly `m ≥ 1`, and hypersurfaces of maximal contact
`H, H'` with `E + H`, `E + H'` snc, there are centred charts `e, e'` at `p`, the coordinate swap
`Φ = e'⁻¹ ∘ e` and its pullback of germs `r` with `T_e ∘ r = T_{e'}`, such that `r` carries the
vanishing ideal of `H'` onto that of `H`, fixes `I_p` and the vanishing ideals of the components
of `E`, and moves every germ by an element of `MC(I)_p`. -/
theorem exists_realizing_swap (I : AnalyticManifold.IdealSheaf M) {m : ℕ}
    (hm : 1 ≤ m) (hI : I.iteratedDeriv (m - 1) * I.deriv ≤ I) {F : HypersurfaceFamily M}
    (hF : F.IsSnc ψ)
    {H H' : Set M} (hH : IsClosedSubmanifold ψ H 1) (hH' : IsClosedSubmanifold ψ H' 1)
    (hHmc : hH.idealSheaf ≤ I.iteratedDeriv (m - 1))
    (hH'mc : hH'.idealSheaf ≤ I.iteratedDeriv (m - 1))
    (hHF : (F.append H).IsSnc ψ) (hH'F : (F.append H').IsSnc ψ) (p : M) (hp : I.ord p = (m : ℕ∞)) :
    ∃ (e e' : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M)
      (he' : e' ∈ maximalAtlas 𝓘(𝕜, E) ω M) (hpe : p ∈ e.source) (hpe' : p ∈ e'.source)
      (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M M ω)
      (r : IdealSheaf.stalkRing M p →+* IdealSheaf.stalkRing M p),
      e p = 0 ∧ e' p = 0 ∧ IsCoordinateSwap E M e e' p Φ ∧ IsPullbackStalk E M (⇑Φ) r ∧
        (∀ s, taylorHom E ψ e hpe he (r s) = taylorHom E ψ e' hpe' he' s) ∧
        Ideal.map r (vanishingStalk (E := E) H' p) = vanishingStalk (E := E) H p ∧
        Ideal.map r (I.stalkIdeal p) = I.stalkIdeal p ∧
        (∀ j, Ideal.map r (vanishingStalk (E := E) (F.hyp j) p) =
          vanishingStalk (E := E) (F.hyp j) p) ∧
        (∀ s, s - r s ∈ (I.iteratedDeriv (m - 1)).stalkIdeal p) ∧
        ∀ G : MvPowerSeries (Fin n) 𝕜, taylorAut ψ e e' he he' hpe hpe' G - G ∈
          ((I.iteratedDeriv (m - 1)).stalkIdeal p).map (taylorHom E ψ e hpe he) := by
  classical
  have hpH : p ∈ H := mem_of_idealSheaf_le_iteratedDeriv ψ I hm hH hHmc hp
  have hpH' : p ∈ H' := mem_of_idealSheaf_le_iteratedDeriv ψ I hm hH' hH'mc hp
  obtain ⟨e, e', he, he', hpe, hpe', i₀, he0, he'0, hshared, hvH, hvH', hvE⟩ :=
    exists_commonCharts E hF hH hH' hHF hH'F hpH hpH'
  obtain ⟨Φ, hΦ⟩ := exists_isCoordinateSwap' E M he he' hpe hpe' he0 he'0
  obtain ⟨r, hr⟩ := hΦ.exists_isPullbackStalk' hpe' he0 he'0
  have hT : ∀ s, taylorHom E ψ e hpe he (r s) = taylorHom E ψ e' hpe' he' s :=
    IsPullbackStalk.taylorHom_eq' ψ hΦ he he' hpe hpe' he0 he'0 hr
  have hTinj : Function.Injective (taylorHom E ψ e hpe he) :=
    IsTaylorHom.injective' E ψ e hpe (isTaylorHom_taylorHom E ψ e hpe he)
  -- `r` pulls the coordinates of `e'` back to those of `e`, fixes the constants, and is local
  have hrcoord : ∀ j, r (coord E ψ e' he' hpe' j) = coord E ψ e he hpe j := fun j => hTinj (by
    rw [hT, taylorHom_coord, taylorHom_coord, he0, he'0])
  have hrconst : ∀ c : 𝕜, r (const 𝕜 E M p c) = const 𝕜 E M p c := fun c => hTinj (by
    rw [hT, taylorHom_const, taylorHom_const])
  have hrlocal : IsLocalHom r := ⟨fun a ha => by
    rw [← IsLocalRing.notMem_maximalIdeal] at ha ⊢
    intro h
    apply ha
    rw [← pow_one (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk p)),
      ← taylorHom_mem_maximalIdeal_pow_iff E ψ e hpe he, hT,
      taylorHom_mem_maximalIdeal_pow_iff E ψ e' hpe' he', pow_one]
    exact h⟩
  -- `x₁, x₁' ∈ MC(I)_p`
  have hMC : (I.iteratedDeriv (m - 1)).stalkIdeal p ≤
      maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk p) := by
    have h := ord_iteratedDeriv_eq_one (E := E) (I := I) hm hp
    have h2 : ((1 : ℕ) : ℕ∞) ≤ (I.iteratedDeriv (m - 1)).ord p := by rw [h]; rfl
    rwa [Manifold.IdealSheaf.ord, le_ord_iff, pow_one] at h2
  have hvHI : vanishingStalk (E := E) H p = hH.idealSheaf.stalkIdeal p :=
    (hH.ker_restrictStalk_eq_vanishingStalk hpH).symm.trans
      (hH.stalkIdeal_idealSheaf_of_mem hpH).symm
  have hvH'I : vanishingStalk (E := E) H' p = hH'.idealSheaf.stalkIdeal p :=
    (hH'.ker_restrictStalk_eq_vanishingStalk hpH').symm.trans
      (hH'.stalkIdeal_idealSheaf_of_mem hpH').symm
  have hx₁ : coord E ψ e he hpe i₀ ∈ (I.iteratedDeriv (m - 1)).stalkIdeal p :=
    IdealSheaf.le_def.mp hHmc p (hvHI ▸ hvH ▸ Ideal.mem_span_singleton_self _)
  have hx₁' : coord E ψ e' he' hpe' i₀ ∈ (I.iteratedDeriv (m - 1)).stalkIdeal p :=
    IdealSheaf.le_def.mp hH'mc p (hvH'I ▸ hvH' ▸ Ideal.mem_span_singleton_self _)
  -- Kollár's formal automorphism `G = T_e ∘ T_{e'}⁻¹`, of the form `1 + T_e(MC(I)_p)`
  set G := taylorAut ψ e e' he he' hpe hpe' with hG_def
  have hG : ∀ s, G (taylorHom E ψ e' hpe' he' s) = taylorHom E ψ e hpe he s := fun s =>
    taylorAut_apply_taylorHom ψ s
  set B := ((I.iteratedDeriv (m - 1)).stalkIdeal p).map (taylorHom E ψ e hpe he) with hB_def
  set Î := (I.stalkIdeal p).map (taylorHom E ψ e hpe he) with hÎ_def
  let Ga : MvPowerSeries (Fin n) 𝕜 ≃ₐ[𝕜] MvPowerSeries (Fin n) 𝕜 :=
    AlgEquiv.ofRingEquiv (f := G) fun c => by
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      conv_lhs => rw [← taylorHom_const E ψ e' hpe' he' c]
      rw [hG, taylorHom_const]
  have hGa : ∀ F, Ga F = G F := fun F => rfl
  have hGX : ∀ j, Ga (X j) = taylorHom E ψ e hpe he (coord E ψ e' he' hpe' j) := fun j => by
    rw [hGa, ← hG]
    congr 1
    rw [taylorHom_coord, he'0, map_zero, Pi.zero_apply, map_zero, add_zero]
  have hGmem : ∀ j, Ga (X j) ∈ maximalIdeal (MvPowerSeries (Fin n) 𝕜) := fun j => by
    rw [hGX, ← pow_one (maximalIdeal (MvPowerSeries (Fin n) 𝕜)), taylorHom_mem_maximalIdeal_pow_iff,
      pow_one, mem_maximalIdeal_iff_eval, eval_coord, he'0, map_zero, Pi.zero_apply]
  have hGsub : ∀ j, Ga (X j) - X j ∈ B := fun j => by
    by_cases hj : j = i₀
    · rw [hj]
      have : Ga (X i₀) - X i₀ =
          taylorHom E ψ e hpe he (coord E ψ e' he' hpe' i₀ - coord E ψ e he hpe i₀) := by
        rw [map_sub, hGX, taylorHom_coord, he0, map_zero, Pi.zero_apply, map_zero, add_zero]
      rw [this]
      exact Ideal.mem_map_of_mem _ (Ideal.sub_mem _ hx₁' hx₁)
    · rw [hGX, ← hshared j hj, taylorHom_coord, he0, map_zero, Pi.zero_apply, map_zero, add_zero,
        sub_self]
      exact zero_mem _
  let GaA : MvPowerSeries (Fin n) 𝕜 →ₐ[𝕜] MvPowerSeries (Fin n) 𝕜 := Ga
  have hGaA : ∀ j, GaA (X j) ∈ maximalIdeal (MvPowerSeries (Fin n) 𝕜) := hGmem
  have hOne : IsOnePlus B Ga :=
    ⟨⟨fun i => GaA (X i), hasSubst_of_forall_X_mem GaA hGaA,
      AlgHom.ext fun F => eq_substAlgHom_of_forall_X_mem GaA hGaA F⟩, hGsub⟩
  -- Proposition 94: `G` maps `Î` onto itself
  have hinv := isInvariantOnePlus_map_taylorHom E ψ I e he hpe hm hI hp
  have hcoe : ((Ga : MvPowerSeries (Fin n) 𝕜 →+* MvPowerSeries (Fin n) 𝕜)) = G.toRingHom :=
    RingHom.ext fun _ => rfl
  have hle : Î.map G.toRingHom ≤ Î := by
    rw [← hcoe]
    exact hinv Ga hOne
  have := isRegularLocalRing_mvPowerSeries (K := 𝕜) n
  have hmapG : Î.map G.toRingHom = Î := Ideal.map_eq_of_map_le G Î hle
  have hTe' : ∀ s, taylorHom E ψ e' hpe' he' s = G.symm (taylorHom E ψ e hpe he s) := fun s => by
    rw [← hG s, RingEquiv.symm_apply_apply]
  -- descend `Î.map G = Î` through the completion `Ô_p ≅ 𝕜⟦X⟧` and Krull: `r(I_p) = I_p`
  have hrI : Ideal.map r (I.stalkIdeal p) = I.stalkIdeal p := by
    set Te := taylorCompletionEquiv E ψ e hpe he with hTe_def
    refine Ideal.eq_of_map_adicCompletion_eq ?_
    have hbij : Function.Bijective Te.toRingHom := Te.bijective
    have h1 : (((I.stalkIdeal p).map r).map (algebraMap _ _)).map Te.toRingHom =
        Î.map G.symm.toRingHom := by
      rw [Ideal.map_map, Ideal.map_map, hÎ_def, Ideal.map_map]
      congr 1
      ext s
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [hTe_def, taylorCompletionEquiv_algebraMap, hT, hTe' s]
    have h2 : ((I.stalkIdeal p).map (algebraMap _ _)).map Te.toRingHom = Î := by
      rw [Ideal.map_map, hÎ_def]
      congr 1
      ext s
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [hTe_def, taylorCompletionEquiv_algebraMap]
    have h3 : Î.map G.symm.toRingHom = Î := by
      conv_lhs => rw [← hmapG]
      rw [Ideal.map_map, RingEquiv.symm_toRingHom_comp_toRingHom, Ideal.map_id]
    have h4 := congrArg (Ideal.comap Te.toRingHom) (h1.trans (h3.trans h2.symm))
    rwa [Ideal.comap_map_of_bijective _ hbij, Ideal.comap_map_of_bijective _ hbij] at h4
  -- the vanishing ideals
  have hrH : Ideal.map r (vanishingStalk (E := E) H' p) = vanishingStalk (E := E) H p := by
    rw [hvH', hvH, Ideal.map_span, Set.image_singleton, hrcoord]
  have hrE : ∀ j, Ideal.map r (vanishingStalk (E := E) (F.hyp j) p) =
      vanishingStalk (E := E) (F.hyp j) p := by
    intro j
    by_cases hpj : p ∈ F.hyp j
    · obtain ⟨l, hl, hvj⟩ := hvE j hpj
      have hrl : r (coord E ψ e he hpe l) = coord E ψ e he hpe l := by
        rw [hshared l hl, hrcoord]
        exact hshared l hl
      rw [hvj, Ideal.map_span, Set.image_singleton, hrl]
    · rw [vanishingStalk_eq_top_of_notMem_closure
        (by rwa [(hF.isClosedSubmanifold j).isClosed.closure_eq]), Ideal.map_top]
  -- the defect of every germ lies in `MC(I)_p`
  have hdef : ∀ s, s - r s ∈ (I.iteratedDeriv (m - 1)).stalkIdeal p := by
    intro s
    have := sub_mem_of_forall_coord_sub_mem E ψ e' hpe' he' (RingHom.id _) r (fun _ => rfl)
      hrconst ((I.iteratedDeriv (m - 1)).stalkIdeal p) (fun j => ?_) s
    · simpa using this
    · by_cases hj : j = i₀
      · rw [hj, RingHom.id_apply, hrcoord]
        exact Ideal.sub_mem _ hx₁' hx₁
      · rw [RingHom.id_apply, hrcoord, hshared j hj, sub_self]
        exact zero_mem _
  -- the formal automorphism moves every power series by an element of `T_e(MC(I)_p)`
  have hBle : B ≤ maximalIdeal (MvPowerSeries (Fin n) 𝕜) :=
    map_taylorHom_MC_le_maximalIdeal E ψ I e he hpe hm hp
  have hdefG : ∀ F, G F - F ∈ B := fun F => sub_map_mem_of_forall_sub_X_mem GaA B hBle hGsub F
  exact ⟨e, e', he, he', hpe, hpe', Φ, r, he0, he'0, hΦ, hr, hT, hrH, hrI, hrE, hdef, hdefG⟩

/-- **The coordinate swap realises the formal equivalence** [Kol07, 95]: `exists_realizing_swap`
without its last clause. -/
theorem coordinateSwapAutomorphism_realizes_formal (I : AnalyticManifold.IdealSheaf M) {m : ℕ}
    (hm : 1 ≤ m) (hI : I.iteratedDeriv (m - 1) * I.deriv ≤ I) {F : HypersurfaceFamily M}
    (hF : F.IsSnc ψ)
    {H H' : Set M} (hH : IsClosedSubmanifold ψ H 1) (hH' : IsClosedSubmanifold ψ H' 1)
    (hHmc : hH.idealSheaf ≤ I.iteratedDeriv (m - 1))
    (hH'mc : hH'.idealSheaf ≤ I.iteratedDeriv (m - 1))
    (hHF : (F.append H).IsSnc ψ) (hH'F : (F.append H').IsSnc ψ) (p : M) (hp : I.ord p = (m : ℕ∞)) :
    ∃ (e e' : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M)
      (he' : e' ∈ maximalAtlas 𝓘(𝕜, E) ω M) (hpe : p ∈ e.source) (hpe' : p ∈ e'.source)
      (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M M ω)
      (r : IdealSheaf.stalkRing M p →+* IdealSheaf.stalkRing M p),
      e p = 0 ∧ e' p = 0 ∧ IsCoordinateSwap E M e e' p Φ ∧ IsPullbackStalk E M (⇑Φ) r ∧
        (∀ s, taylorHom E ψ e hpe he (r s) = taylorHom E ψ e' hpe' he' s) ∧
        Ideal.map r (vanishingStalk (E := E) H' p) = vanishingStalk (E := E) H p ∧
        Ideal.map r (I.stalkIdeal p) = I.stalkIdeal p ∧
        (∀ j, Ideal.map r (vanishingStalk (E := E) (F.hyp j) p) =
          vanishingStalk (E := E) (F.hyp j) p) ∧
        ∀ s, s - r s ∈ (I.iteratedDeriv (m - 1)).stalkIdeal p := by
  obtain ⟨e, e', he, he', hpe, hpe', Φ, r, he0, he'0, hΦ, hr, hT, hrH, hrI, hrE, hdef, -⟩ :=
    exists_realizing_swap ψ I hm hI hF hH hH' hHmc hH'mc hHF hH'F p hp
  exact ⟨e, e', he, he', hpe, hpe', Φ, r, he0, he'0, hΦ, hr, hT, hrH, hrI, hrE, hdef⟩

end Hironaka.Manifold

end
