/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Chart.Transport
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.Germ.ChartTransport
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.LocalDiffeomorph
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial
/-!
# The pull-back of the ideal sheaf of a closed submanifold along a local analytic isomorphism

For a local analytic isomorphism `h : N → M` and a closed submanifold `Y ⊆ M`, the pull-back
`h^*I_Y` of the ideal sheaf of `Y` is the ideal sheaf of the preimage submanifold `h⁻¹(Y)`
(`IsClosedSubmanifold.preimage_of_isLocalDiffeomorph`):
`comap h hY.idealSheaf = (hY.preimage_of_isLocalDiffeomorph hh).idealSheaf`
(`comap_idealSheaf_of_isLocalDiffeomorph`). This is Kollár's pull-back of a blow-up centre along
a smooth morphism [Kol07, 30.1] and the reducedness of the pulled-back centre used in the chart
computation of his proof of the uniqueness of blow-up sequences [Kol07, Theorem 97, proof]; it is
the centre clause of the one-step descent lemma (`agreeOnSubspace_blowUpLift`) for the lifts of
local isomorphisms along a blow-up sequence.

Proof: both sides have cosupport `h⁻¹(Y)`; at `a ∈ h⁻¹(Y)` the stalk of the pull-back is the
image of the stalk `I_{Y, h a} = (x_{σ i})` under `h^*` (`isIdealSheafOf_idealSheaf`), and the
germs `x_{σ i} ∘ h` are the adapted coordinates of the transported chart `φ ∘ h` of `h⁻¹(Y)` at `a`
(`transportChart` along a local inverse `Φ` of `h`, `isAdaptedChart_transportChart`), which
generate `I_{h⁻¹Y, a}` by the same specification; off `h⁻¹(Y)` both stalks are the unit ideal.
Also `stalkIdeal_comap_eq_map_germMap`: the stalk of a pull-back is the image of the stalk under
the stalk map.
-/

public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory Set Filter
  Topology
open scoped Manifold ContDiff

universe u v

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M N : AnalyticManifold.{u} 𝕜 E}

/-- The stalk of the pull-back at `a` is the image of the stalk at `h a`. -/
theorem stalkIdeal_comap_eq_map_germMap (h : AnalyticMap N M)
    (J : AnalyticManifold.IdealSheaf M)
    (a : N) :
    (J.pullback h h.contMDiff).stalkIdeal a =
      Ideal.map (germMap (⇑h) h.contMDiff a) (J.stalkIdeal (h a)) :=
  IdealSheaf.stalkIdeal_pullback (⇑h) h.contMDiff J a

/-- The coordinate germ of the transported chart `φ ∘ Φ` at `a` is the pull-back along `h` of the
coordinate germ of `φ` at `h a`, when `h = Φ` near `a`. -/
theorem germMap_coord_eq_coord_transportChart (h : AnalyticMap N M)
    (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N M ω) (hΦ : EqOn h Φ Φ.source) {a : N}
    (ha : a ∈ Φ.source) (φ : OpenPartialHomeomorph M E)
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω M)
    (hφa : h a ∈ φ.source)
    (hφ' : transportChart Φ.symm φ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω N)
    (ha' : a ∈ (transportChart Φ.symm φ).source) (i : Fin n) :
    germMap (⇑h) h.contMDiff a (coord E ψ φ hφ hφa i) =
      coord E ψ (transportChart Φ.symm φ) hφ' ha' i := by
  unfold coord
  rw [germMap_germ]
  apply stalkToGerm_injective
  rw [stalkToGerm_structureSheaf_germ, stalkToGerm_structureSheaf_germ]
  refine Germ.coe_eq.mpr ?_
  have hopen : IsOpen (Φ.source ∩ (⇑h) ⁻¹' φ.source) :=
    Φ.open_source.inter (φ.open_source.preimage h.contMDiff.continuous)
  have hmem : a ∈ Φ.source ∩ (⇑h) ⁻¹' φ.source := ⟨ha, hφa⟩
  filter_upwards [hopen.mem_nhds hmem] with x hx
  have hx1 : x ∈ preimageOpens (⇑h) h.contMDiff ⟨φ.source, φ.open_source⟩ := hx.2
  have hx2 : x ∈ (transportChart Φ.symm φ).source := by
    rw [transportChart_source]
    refine ⟨hx.1, ?_⟩
    change Φ x ∈ φ.source
    rw [← hΦ hx.1]
    exact hx.2
  rw [extendSection_of_mem 𝕜 E _ hx1, extendSection_of_mem 𝕜 E _ hx2, comapSection_apply]
  change ψ (φ (h x)) i = ψ ((transportChart Φ.symm φ) x) i
  rw [transportChart_apply]
  change ψ (φ (h x)) i = ψ (φ (Φ x)) i
  rw [hΦ hx.1]

/-- The pull-back of the ideal sheaf of a closed submanifold along a local analytic isomorphism is
the ideal sheaf of the preimage submanifold ([Kol07, 30.1]; the centre clause of
`agreeOnSubspace_blowUpLift` for the lifts of local isomorphisms — Kollár's
`ψ_i^* I_{Z_i} = I_{Z_i^U}` for étale `ψ_i`). -/
theorem comap_idealSheaf_of_isLocalDiffeomorph (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ Y c) :
    hY.idealSheaf.pullback h h.contMDiff =
      (hY.preimage_of_isLocalDiffeomorph hh).idealSheaf := by
  have hZ := hY.preimage_of_isLocalDiffeomorph hh
  have hY' := hY.isIdealSheafOf_idealSheaf
  have hZ' := hZ.isIdealSheafOf_idealSheaf
  refine IdealSheaf.ext fun a => ?_
  by_cases ha : h a ∈ Y
  · -- a local inverse of `h` at `a` and an adapted chart of `Y` at `h a`
    obtain ⟨Φ, haΦ, hΦ⟩ := (hh a).exists_partialDiffeomorph
    obtain ⟨φ, σ, hφa, hφ⟩ := hY.exists_adaptedChart (h a) ha
    have hg : Φ.symm '' (Y ∩ Φ.symm.source) = (⇑h) ⁻¹' Y ∩ Φ.symm.target :=
      image_symm_eq_of_image_eq Φ (image_preimage_eq_of_eqOn Φ hΦ)
    have hφ'ad : IsAdaptedChart ψ ((⇑h) ⁻¹' Y) (transportChart Φ.symm φ) σ :=
      isAdaptedChart_transportChart Φ.symm hg hφ
    have ha' : a ∈ (transportChart Φ.symm φ).source := by
      rw [transportChart_source]
      refine ⟨haΦ, ?_⟩
      change Φ a ∈ φ.source
      rw [← hΦ haΦ]
      exact hφa
    rw [stalkIdeal_comap_eq_map_germMap, hY'.2 φ σ hφ (h a) hφa ha, hZ'.2 _ σ hφ'ad a ha' ha,
      Ideal.map_span, ← Set.range_comp]
    refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
    exact germMap_coord_eq_coord_transportChart ψ h Φ hΦ haΦ φ hφ.1 hφa hφ'ad.1 ha' (σ i)
  · rw [stalkIdeal_comap_eq_map_germMap, hY'.stalkIdeal_of_notMem ha, Ideal.map_top,
      hZ'.stalkIdeal_of_notMem ha]

end Manifold

end
