/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.Lift
public import Hironaka.Manifold.FiniteSuccession.Restrict.Restrict
public import Hironaka.Manifold.StructureSheaf
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.StrictFlag
import Hironaka.Manifold.FiniteSuccession.Restrict.GermRestrict
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Submanifold.Ideal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's Lemma 62 for one blowing-up

For `Z ⊆ H ⊂ X` and `π : B_Z X → X` with `π_H : B_Z H → H` the restricted blow-down,
`(π_H)_*^{-1}(I|_H, m) = π_*^{-1}(I, m)|_{B_Z H}` when `m ≤ ord_Z I` [Kol07, Lemma 62]. The proof
here is stalkwise and coordinate-free, like that of the algebraic form in `Hironaka/`: at a point
`p'` of the strict transform `S'`, both marked transforms are colon ideals (`IsDivExceptional`),
the total transforms and the exceptional ideal sheaves correspond under the restriction of germs
`ρ = 𝒪_{M', p'} → 𝒪_{S', p'}` (pull-back functoriality; `exceptionalIdealSheaf_restrictMap`,
`idealSheaf_preimageVal_eq_pullback`), and the colon by `u^m` commutes with `ρ`
(`Ideal.map_colon_singleton_pow_eq`): the total transform is divisible by `u^m` and `ρ(u) ≠ 0`
because the exceptional coordinate `u = u_{σ i}` does not vanish identically on `S'` — at a point
of `S'` the blow-up chart is a good chart (`i ∉ range τ`),
where `S' = {u_{σ (τ j)} = 0}` and `u_{σ i}` lies outside the ideal of `S'`
(`coord_notMem_span_coord_sub_const`). Off the centre both sides are plain pull-backs. This is
Kollár's argument: it does not matter whether one first sets `x_1 = 0` and computes the transform
or first computes the transform and then sets `y_1 = 0`, and the bad chart contains no point of
`B_Z H` [Kol07, Lemma 62, proof].

Also: the order can only go up under restriction (the opening remark of [Kol07, §9];
`ord_le_ord_pullback` at the closed embedding), and the centres of a succession with centres in the
strict transforms of `H` are recovered from those of its restriction to `H` (the injection of the
going-down property of maximal contact [Kol07, 51.1], read on `FiniteSuccession`).
-/

public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] {Y S : Set M} {c s : ℕ}
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M']
  [SecondCountableTopology M'] {π : M' → M}

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The order can only go up under restriction to a closed submanifold (`ord_le_ord_pullback` at
the closed embedding `S ↪ M`; the opening remark of [Kol07, §9]). -/
theorem ord_pullback_inclusionMap_ge (hS : IsClosedSubmanifold ψ S s)
    (J : IdealSheaf (structureSheaf 𝕜 E M)) (p : hS.toAnalyticManifold) :
    J.ord (hS.inclusionMap p) ≤ (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff).ord p :=
  IdealSheaf.ord_le_ord_pullback _ _ J p

variable (hS : IsClosedSubmanifold ψ S s) (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
  (hYS : Y ⊆ S)

/-- The two closed embeddings and the two blow-downs commute: `ι_S ∘ π|_{S'} = π ∘ ι_{S'}`
(`restrictMap_apply`, `rfl`). -/
theorem inclusionMap_comp_restrictMap :
    ⇑hS.inclusionMap ∘ ⇑((hS.strictTransform hY h hYS).restrictMap hS π h.contMDiff
        (strictTransform_subset_preimage h.contMDiff.continuous hS.isClosed)) =
      π ∘ ⇑(hS.strictTransform hY h hYS).inclusionMap :=
  funext fun _ => rfl

/-- The total transform of the restriction is the restriction of the total transform (pull-back
functoriality along `ι_S ∘ π|_{S'} = π ∘ ι_{S'}`). -/
theorem totalTransform_pullback_restrictMap (J : IdealSheaf (structureSheaf 𝕜 E M)) :
    (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff).pullback _
        (isBlowUp_restrictMap hS hY h hYS).contMDiff =
      (J.pullback π h.contMDiff).pullback ⇑(hS.strictTransform hY h hYS).inclusionMap
        (hS.strictTransform hY h hYS).inclusionMap.contMDiff := by
  rw [IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback]
  exact IdealSheaf.pullback_congr J _ _ (inclusionMap_comp_restrictMap hS hY h hYS)

/-- The exceptional ideal sheaf of `π|_{S'}` is the restriction to `S'` of the exceptional ideal
sheaf `I_F` of `π` (the exceptional divisor of the restricted blowing-up is the trace of `F`; in
Kollár's chart the birational transform of `H` is `(y_1 = 0)`, [Kol07, Lemma 62, proof]). -/
theorem exceptionalIdealSheaf_restrictMap :
    (hS.preimage_val_of_subset hY hYS).idealSheaf.pullback _
        (isBlowUp_restrictMap hS hY h hYS).contMDiff =
      (hY.idealSheaf.pullback π h.contMDiff).pullback ⇑(hS.strictTransform hY h hYS).inclusionMap
        (hS.strictTransform hY h hYS).inclusionMap.contMDiff := by
  rw [idealSheaf_preimageVal_eq_pullback hS hY hYS, IdealSheaf.pullback_pullback,
    IdealSheaf.pullback_pullback]
  exact IdealSheaf.pullback_congr _ _ _ (inclusionMap_comp_restrictMap hS hY h hYS)

/-- The mark `m ≤ ord_Y J` is legitimate for the restriction `(J|_S, m)` along `Y ⊆ S`
(restriction is a ring map, so `J_a ⊆ I_{Y,a}^m` restricts). -/
theorem le_ordAlongIdeal_pullback_inclusionMap (J : IdealSheaf (structureSheaf 𝕜 E M)) {m : ℕ}
    (hm : ∀ a ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J a) :
    ∀ a ∈ hS.preimageVal Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
      (hS.preimage_val_of_subset hY hYS).idealSheaf
      (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) a := by
  intro a ha
  rw [idealSheaf_preimageVal_eq_pullback hS hY hYS, IdealSheaf.le_ordAlongIdeal_iff,
    IdealSheaf.stalkIdeal_pullback, IdealSheaf.stalkIdeal_pullback, ← Ideal.map_pow]
  exact Ideal.map_mono ((IdealSheaf.le_ordAlongIdeal_iff _ _ _ _).mp (hm _ ha))

omit [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] [IsManifold 𝓘(𝕜, E) ω M'] in
/-- The exceptional coordinate `u = u_{σ i}` of a good blow-up chart does not vanish identically on
the strict transform `S'` near its points: `S' = {u_{σ (τ j)} = 0}` there and `u_{σ i}` lies outside
the ideal spanned by the `u_{σ (τ j)}`, the kernel of the restriction of germs. -/
theorem germMap_inclusionMap_coord_ne_zero
    (hS' : IsClosedSubmanifold ψ (strictTransformSet π Y S) s) {φ : OpenPartialHomeomorph M E}
    {σ : Fin c ↪ Fin n} {τ : Fin s ↪ Fin c} (hφ : IsAdaptedChart ψ Y φ σ)
    (hSflag : ∀ x ∈ φ.source, x ∈ S ↔ ∀ j, ψ (φ x) (σ (τ j)) = 0) {i : Fin c}
    {Φ : OpenPartialHomeomorph M' E} (hΦ : IsBlowUpChart ψ π φ σ i Φ) (hi : i ∉ Set.range τ)
    (p' : hS'.toAnalyticManifold) (hp' : (hS'.inclusionMap p' : M') ∈ Φ.source) :
    germMap ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff p'
      (coord E ψ Φ hΦ.mem_maximalAtlas hp' (σ i)) ≠ 0 := by
  intro h0
  have hker := hS'.ker_restrictStalk p'
    (isAdaptedChart_strictTransform_of_not_mem_range hφ hΦ hSflag hi) hp'
  have h0' : coord E ψ Φ hΦ.mem_maximalAtlas hp' (σ i) ∈ RingHom.ker (hS'.restrictStalk p') :=
    RingHom.mem_ker.mpr ((hS'.germMap_inclusionMap_eq_restrictStalk p' _).symm.trans h0)
  exact coord_notMem_span_coord_sub_const ψ hΦ.mem_maximalAtlas hp' (fun j => (τ.trans σ) j)
    (fun j hj => hi ⟨j, σ.injective hj⟩) ((SetLike.ext_iff.mp hker _).mp h0')

/-- **Kollár's Lemma 62** for one blowing-up [Kol07, Lemma 62]: the marked transform of `(J|_S, m)`
under the restricted blow-down `π|_{S'} : S' → S` is the restriction to `S'` of the marked
transform `π_*^{-1}(J, m)`. -/
theorem birationalTransform_pullback_restrictMap (J : IdealSheaf (structureSheaf 𝕜 E M)) {m : ℕ}
    (hm : ∀ a ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J a) :
    (MarkedIdealSheaf.birationalTransform (hS.preimage_val_of_subset hY hYS)
        (isBlowUp_restrictMap hS hY h hYS)
        ⟨J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff, m⟩).I =
      (MarkedIdealSheaf.birationalTransform hY h ⟨J, m⟩).I.pullback
        ⇑(hS.strictTransform hY h hYS).inclusionMap
        (hS.strictTransform hY h hYS).inclusionMap.contMDiff := by
  have hS' := hS.strictTransform hY h hYS
  have hm' := le_ordAlongIdeal_pullback_inclusionMap hS hY hYS J hm
  refine IdealSheaf.ext fun (p' : hS'.toAnalyticManifold) => ?_
  have h1 := isDivExceptional_birationalTransform (hS.preimage_val_of_subset hY hYS)
    (isBlowUp_restrictMap hS hY h hYS)
    ⟨J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff, m⟩ hm' p'
  have h2 := isDivExceptional_birationalTransform hY h ⟨J, m⟩ hm (hS'.inclusionMap p')
  dsimp only at h1 h2
  -- the total transforms and the exceptional ideal sheaves correspond stalkwise
  have eT : ((J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff).pullback _
      (isBlowUp_restrictMap hS hY h hYS).contMDiff).stalkIdeal p' =
      Ideal.map (germMap ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff p')
        ((J.pullback π h.contMDiff).stalkIdeal (hS'.inclusionMap p')) := by
    rw [totalTransform_pullback_restrictMap hS hY h hYS]
    exact IdealSheaf.stalkIdeal_pullback _ _ _ _
  have eF : ((hS.preimage_val_of_subset hY hYS).idealSheaf.pullback _
      (isBlowUp_restrictMap hS hY h hYS).contMDiff).stalkIdeal p' =
      Ideal.map (germMap ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff p')
        ((hY.idealSheaf.pullback π h.contMDiff).stalkIdeal (hS'.inclusionMap p')) := by
    rw [exceptionalIdealSheaf_restrictMap hS hY h hYS]
    exact IdealSheaf.stalkIdeal_pullback _ _ _ _
  have eR : ((MarkedIdealSheaf.birationalTransform hY h ⟨J, m⟩).I.pullback ⇑hS'.inclusionMap
      hS'.inclusionMap.contMDiff).stalkIdeal p' =
      Ideal.map (germMap ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff p')
        ((MarkedIdealSheaf.birationalTransform hY h ⟨J, m⟩).I.stalkIdeal (hS'.inclusionMap p')) :=
    IdealSheaf.stalkIdeal_pullback _ _ _ _
  rw [h1, eT, eF, eR, h2]
  by_cases hπ : π (hS'.inclusionMap p') ∈ Y
  · -- over the centre: a good blow-up chart at the point
    obtain ⟨φ, σ, τ, haφ, hφ, hSflag⟩ := exists_adaptedChart_flag hY hS hYS hπ
    obtain ⟨i, Φ, hΦ, hpΦ⟩ := h.cover φ σ hφ (hS'.inclusionMap p') haφ
    have hi : i ∉ Set.range τ := fun hi => by
      have hE := strictTransform_inter_source_of_mem_range hφ hΦ hSflag hi
      exact Set.eq_empty_iff_forall_notMem.mp hE (hS'.inclusionMap p') ⟨p'.2, hpΦ⟩
    have : IsDomain
        ((structureSheaf 𝕜 (Fin (n - s) → 𝕜) hS'.toAnalyticManifold).presheaf.stalk p') :=
      isDomain_stalk (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
        (IsManifold.chart_mem_maximalAtlas p') (mem_chart_source _ p')
    have hA : (J.pullback π h.contMDiff).stalkIdeal (hS'.inclusionMap p') ≤
        Ideal.span {coord E ψ Φ hΦ.mem_maximalAtlas hpΦ (σ i) ^ m} := by
      have := h.totalTransform_stalkIdeal_le hY J (hm _ hπ)
      rwa [stalkIdeal_exceptionalIdealSheaf_eq_span_coord hY h hφ hΦ hpΦ,
        Ideal.span_singleton_pow] at this
    rw [stalkIdeal_exceptionalIdealSheaf_eq_span_coord hY h hφ hΦ hpΦ, Ideal.map_span,
      Set.image_singleton, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
      Submodule.colon_span, Submodule.colon_span]
    exact Ideal.map_colon_singleton_pow_eq _ hA
      (germMap_inclusionMap_coord_ne_zero hS' hφ hSflag hΦ hi p' hpΦ)
  · -- off the centre: both sides are the plain pull-back
    rw [stalkIdeal_exceptionalIdealSheaf_of_notMem hY h hπ, Ideal.map_top]
    simp only [Ideal.top_pow, Submodule.top_coe, Submodule.colon_univ]

end Hironaka.Manifold

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M) {H : Set M}
  {s : ℕ} (hH : IsClosedSubmanifold ψ H s) (hc : S.CentersIn H)

include hc in
/-- Every centre `Z_i` of a succession with centres in the strict transforms of `H` is the image
of the centre `Z_i ∩ H_i` of the restricted succession under the embedding `H_i ↪ M_i`: the
injection of the going-down property of maximal contact [Kol07, 51.1], on `FiniteSuccession`. -/
theorem support_center_eq_image_restrictIncl (i : Fin S.length) :
    (S.center i).support =
      ⇑(S.restrictIncl hH hc i.castSucc) '' ((S.restrictSubmanifold hH hc).center i).support := by
  rw [support_center_restrictSubmanifold]
  exact (Set.image_preimage_eq_of_subset (by rw [range_restrictIncl]; exact hc i)).symm

end AnalyticManifold.FiniteSuccession

end
