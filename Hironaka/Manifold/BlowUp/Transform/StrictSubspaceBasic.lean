/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Restrict
public import Hironaka.Manifold.BlowUp.Transform.Defs
public import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.StrictSubspace
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Basic properties of the strict transform: off the centre, restriction to opens

The field-independent properties of the strict transform of a closed subspace
(`saturationStalk`, `strictTransformSubspace`).

* **Off the exceptional divisor `F` the strict transform is the total transform** (immediate from
  the definition; cf. [BM97, Remark 3.15]). The saturation at `a' ∉ F` is the total transform's
  stalk (`I_{F,a'} = 𝒪`, `saturationStalk_of_notMem_cosupport`), which is the image of `I_{π(a')}`
  under the stalk map of `π` (`IdealSheaf.stalkIdeal_pullback`); on points, `|X'| ∖ |F| =
  π⁻¹(|X|) ∖ |F|` (`cosupport_pullback`), and since `|X'|` is closed it contains `closure(π⁻¹(|X| ∖
  Y))`; the points of the exceptional divisor are `π⁻¹(Y)`
  (`IsBlowUp.cosupport_exceptionalIdealSheaf`). The statements about `strictTransformSubspace` take
  the finite type of the saturation as the explicit hypothesis `hex`
  (`saturationStalk_hasLocalGenerators` supplies it).
* **The saturation stalks commute with restriction to an open `U ⊆ M`**
  (`saturationStalk_restrict`; the case of an open inclusion of [Wlo09, Proposition 3.4.1, (2)]):
  the total transform and the exceptional ideal of the restricted blowing-up are the pullbacks of
  those of `π` along the inclusion `π⁻¹(U) ⊆ M'`, the two pullbacks composing as in
  `birationalTransform_restrict`; the colon by a power transports along the stalk isomorphism of
  the inclusion (`Ideal.map_colon_pow_of_bijective`, `germMap_val_bijective`), and `Ideal.map`
  commutes with the union over `k` (`Ideal.map_iSup`).
-/

public section

open TopologicalSpace Opposite CategoryTheory Set
open scoped Manifold ContDiff

universe u

namespace Manifold

section OffCentre

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M}
  {c : ℕ} {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M}
  (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π) (I : IdealSheaf (structureSheaf 𝕜 E M))

/-- The points of the exceptional divisor are the preimages of the points of the centre,
`|F| = π⁻¹(Y)` (`cosupport_pullback` and `|I_Y| = Y`). -/
theorem IsBlowUp.cosupport_exceptionalIdealSheaf :
    (hY.idealSheaf.pullback π h.contMDiff).support = π ⁻¹' Y := by
  rw [IdealSheaf.support_pullback, hY.cosupport_idealSheaf]

/-- Given the finite type of the saturation: off the exceptional divisor
the stalk of the strict transform is the image of the stalk of `X` under the stalk map of `π`. -/
theorem stalkIdeal_strictTransformSubspace_of_notMem_cosupport_of_hasLocalGenerators
    (hex : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M') (saturationStalk hY h I))
    {a' : M'} (ha' : a' ∉ (hY.idealSheaf.pullback π h.contMDiff).support) :
    (strictTransformSubspace hY h I).stalkIdeal a' =
      Ideal.map (germMap π h.contMDiff a') (I.stalkIdeal (π a')) := by
  rw [stalkIdeal_strictTransformSubspace_of_hasLocalGenerators hY h I hex,
    saturationStalk_of_notMem_cosupport hY h I ha', IdealSheaf.stalkIdeal_pullback π h.contMDiff]

/-- Given the finite type of the saturation: on points, off the
exceptional divisor the strict transform is the preimage of `X`. -/
theorem cosupport_strictTransformSubspace_diff_of_hasLocalGenerators
    (hex : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M') (saturationStalk hY h I)) :
    (strictTransformSubspace hY h I).support \ (hY.idealSheaf.pullback π h.contMDiff).support =
      π ⁻¹' I.support \ (hY.idealSheaf.pullback π h.contMDiff).support := by
  ext a'
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [← IdealSheaf.support_pullback π h.contMDiff I]
    rw [IdealSheaf.mem_support,
      stalkIdeal_strictTransformSubspace_of_hasLocalGenerators hY h I hex,
      saturationStalk_of_notMem_cosupport hY h I h2] at h1
    exact h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [← IdealSheaf.support_pullback π h.contMDiff I] at h1
    rw [IdealSheaf.mem_support,
      stalkIdeal_strictTransformSubspace_of_hasLocalGenerators hY h I hex,
      saturationStalk_of_notMem_cosupport hY h I h2]
    exact h1

/-- Given the finite type of the saturation: `|X'|`
contains the closure of `π⁻¹(|X| ∖ Y)`. -/
theorem closure_subset_cosupport_strictTransformSubspace_of_hasLocalGenerators
    (hex : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M') (saturationStalk hY h I)) :
    closure (π ⁻¹' (I.support \ Y)) ⊆ (strictTransformSubspace hY h I).support := by
  refine (IdealSheaf.isClosed_support (strictTransformSubspace hY h I)).closure_subset_iff.mpr
    fun a' ha' => ?_
  have hF : a' ∉ (hY.idealSheaf.pullback π h.contMDiff).support := by
    rw [IsBlowUp.cosupport_exceptionalIdealSheaf hY h]
    exact ha'.2
  have hmem : a' ∈ (strictTransformSubspace hY h I).support \
      (hY.idealSheaf.pullback π h.contMDiff).support := by
    rw [cosupport_strictTransformSubspace_diff_of_hasLocalGenerators hY h I hex]
    exact ⟨ha'.1, hF⟩
  exact hmem.1

end OffCentre

section Restrict

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] {Y : Set M} {c : ℕ} {M' : Type u} [TopologicalSpace M']
  [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M']
  {π : M' → M} {U : Opens M} {U' : Opens M'} (hU' : (U' : Set M') = π ⁻¹' U) {π' : U' → U}
  (hπ' : ∀ p, (π' p : M) = π p)

/-- **The saturation commutes with restriction to an open
subset** — on the restricted blowing-up `π' : π⁻¹(U) → U`, the saturation stalk of `I|_U` at `q` is
the saturation stalk of `I` at `q` transported along the stalk isomorphism of the inclusion
`π⁻¹(U) ⊆ M'` (`birationalTransform_restrict`). -/
theorem saturationStalk_restrict (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) (q : U') :
    saturationStalk (hY.preimage_val U) (IsBlowUp.restrictOpens' hU' hπ' hY h)
        (I.pullback (Subtype.val : U → M) (contMDiff_subtype_val (I := 𝓘(𝕜, E)))) q =
      Ideal.map (germMap (Subtype.val : U' → M') (contMDiff_subtype_val (I := 𝓘(𝕜, E))) q)
        (saturationStalk hY h I q.1) := by
  have e1 : (I.pullback (Subtype.val : U → M) (contMDiff_subtype_val (I := 𝓘(𝕜, E)))).pullback _
      (IsBlowUp.restrictOpens' hU' hπ' hY h).contMDiff =
      (I.pullback π h.contMDiff).pullback (Subtype.val : U' → M')
        (contMDiff_subtype_val (I := 𝓘(𝕜, E))) := by
    rw [IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback]
    exact IdealSheaf.pullback_congr I _ _ (funext hπ')
  have e2 : (hY.preimage_val U).idealSheaf.pullback _ (IsBlowUp.restrictOpens' hU' hπ' hY
      h).contMDiff =
      (hY.idealSheaf.pullback π h.contMDiff).pullback (Subtype.val : U' → M')
        (contMDiff_subtype_val (I := 𝓘(𝕜, E))) := by
    rw [hY.idealSheaf_preimage_val U (hY.preimage_val U), IdealSheaf.pullback_pullback,
      IdealSheaf.pullback_pullback]
    exact IdealSheaf.pullback_congr _ _ _ (funext hπ')
  unfold saturationStalk
  rw [e1, e2, Ideal.map_iSup]
  refine iSup_congr fun k => ?_
  rw [IdealSheaf.stalkIdeal_pullback (φ := (Subtype.val : U' → M')),
    IdealSheaf.stalkIdeal_pullback (φ := (Subtype.val : U' → M')),
    Ideal.map_colon_pow_of_bijective _ (germMap_val_bijective (𝕜 := 𝕜) (E := E) U' q)]

end Restrict

end Manifold
