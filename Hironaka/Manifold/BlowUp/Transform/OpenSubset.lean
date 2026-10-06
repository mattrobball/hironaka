/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Transform.Basic
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The birational transform commutes with restriction to an open subset

For the blowing-up `π' : π⁻¹(U) → U` restricted over an open subset `U ⊆ M`
(`Hironaka.Manifold.BlowUp.Restrict`), the birational transform of the restriction of `(I, m)`
to `U` is the restriction to `π⁻¹(U)` of the birational transform of `(I, m)`
(`birationalTransform_restrict`); this is the compatibility of the birational transform with
restriction to open subsets [Kol07, Definition 30, 30.1]. The trace `Y ∩ U` of the centre is a
closed submanifold of `U`, and its ideal sheaf is the pullback of `I_Y` along the inclusion
(`Hironaka.Manifold.BlowUp.Transform.Object`). Hence the total transform and the exceptional ideal
on `π⁻¹(U)` are the restrictions of those on `M'` (pullbacks compose, and `π ∘ val = val ∘ π'`),
and the colon stalks of the birational transform on `π⁻¹(U)` are the images of the colon stalks on
`M'` under the stalk isomorphism of the inclusion
(`Hironaka.Manifold.BlowUp.Transform.GermIso`), so the two ideal sheaves have the same colon
specification and coincide (`IsDivExceptional.unique`).
-/

public section

open TopologicalSpace Opposite CategoryTheory Filter Topology IsLocalRing Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] {Y : Set M} {c : ℕ}

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M}

/-- **The birational transform commutes with restriction to an open subset**
[Kol07, Definition 30, 30.1]: for the restricted blowing-up `π' : π⁻¹(U) → U` of
`Hironaka.Manifold.BlowUp.Restrict`, the birational transform of the restriction of `(I, m)`
to `U` is the restriction to `π⁻¹(U)` of the birational transform of `(I, m)`. The total
transform and the exceptional ideal restrict (pullbacks compose and `π ∘ val = val ∘ π'`), the
colon stalks restrict along the stalk isomorphism of the inclusion,
and the colon specification determines the sheaf. -/
theorem birationalTransform_restrict (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
    {U : Opens M} {U' : Opens M'} (_hU' : (U' : Set M') = π ⁻¹' U) {π' : U' → U}
    (hπ' : ∀ p, (π' p : M) = π p) (hY' : IsClosedSubmanifold ψ ((Subtype.val : U → M) ⁻¹' Y) c)
    (h' : IsBlowUp ψ ((Subtype.val : U → M) ⁻¹' Y) c π')
    (I : IdealSheaf (structureSheaf 𝕜 E M))
    {m : ℕ} (hm : ∀ a ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I a) :
    (MarkedIdealSheaf.birationalTransform hY' h'
        ⟨IdealSheaf.pullback (Subtype.val : U → M) (contMDiff_subtype_val (I := 𝓘(𝕜, E))) I,
          m⟩).I =
      IdealSheaf.pullback (Subtype.val : U' → M') (contMDiff_subtype_val (I := 𝓘(𝕜, E)))
        (MarkedIdealSheaf.birationalTransform hY h ⟨I, m⟩).I := by
  have hm' : ∀ a ∈ (Subtype.val : U → M) ⁻¹' Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY'.idealSheaf
      (IdealSheaf.pullback (Subtype.val : U → M) (contMDiff_subtype_val (I := 𝓘(𝕜, E))) I) a := by
    intro a ha
    rw [hY.idealSheaf_preimage_val U hY', IdealSheaf.le_ordAlongIdeal_iff,
      IdealSheaf.stalkIdeal_pullback, IdealSheaf.stalkIdeal_pullback, ← Ideal.map_pow]
    exact Ideal.map_mono ((IdealSheaf.le_ordAlongIdeal_iff hY.idealSheaf I a m).mp (hm a ha))
  refine IsDivExceptional.unique (isDivExceptional_birationalTransform hY' h' ⟨_, m⟩ hm') ?_
  intro p
  have hbt := isDivExceptional_birationalTransform hY h ⟨I, m⟩ hm (p : M')
  dsimp only at hbt ⊢
  have e1 : (IdealSheaf.pullback (Subtype.val : U → M) (contMDiff_subtype_val (I := 𝓘(𝕜, E)))
      I).pullback π' h'.contMDiff =
      (I.pullback π h.contMDiff).pullback (Subtype.val : U' → M')
        (contMDiff_subtype_val (I := 𝓘(𝕜, E))) := by
    rw [IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback]
    exact IdealSheaf.pullback_congr I _ _ (funext hπ')
  have e2 : hY'.idealSheaf.pullback π' h'.contMDiff =
      (hY.idealSheaf.pullback π h.contMDiff).pullback (Subtype.val : U' → M')
        (contMDiff_subtype_val (I := 𝓘(𝕜, E))) := by
    rw [hY.idealSheaf_preimage_val U hY', IdealSheaf.pullback_pullback,
      IdealSheaf.pullback_pullback]
    exact IdealSheaf.pullback_congr _ _ _ (funext hπ')
  rw [e1, e2, IdealSheaf.stalkIdeal_pullback (φ := (Subtype.val : U' → M')),
    IdealSheaf.stalkIdeal_pullback (φ := (Subtype.val : U' → M')),
    IdealSheaf.stalkIdeal_pullback (φ := (Subtype.val : U' → M')), hbt]
  exact Ideal.map_colon_pow_of_bijective _ (germMap_val_bijective (𝕜 := 𝕜) (E := E) U' p) _ _ m

end Manifold
