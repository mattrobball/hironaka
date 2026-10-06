/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.BaseTransport
public import Hironaka.Manifold.BlowUp.Transform.Basic
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Restrict.GoingDown
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Going up: naturality of the marked transform under diffeomorphisms

The two naturality statements of the marked transform `π_*^{-1}(I, m)` [Kol07, Definition 60]
from which the identity "the restriction of the push-forward is the given sequence" (Kollár's
natural inclusions `j_i : S_i ↪ X_i`, [Kol07, 30.2–30.3];
`markedTransformSeq_pullback_pushforwardIncl` in `GoingUp/PushforwardTransform.lean`) is
assembled step by step:

* `birationalTransform_pullback_of_comp_eq` (**invariance**): for two blowings-up `π₁ : M₁' → M`,
  `π₂ : M₂' → M` of the same centre `Y` and a diffeomorphism `e : M₁' ≃ M₂'` over `M`
  (`π₂ ∘ e = π₁`; the unique diffeomorphism between two blowings-up of one centre
  [BM88, Definition 4.1], `IsBlowUp.diffeomorph`), the marked transform along `π₂` pulls back
  along `e` to the marked transform along `π₁`. The total transform and the exceptional ideal
  sheaf are pullbacks (`pullback_pullback`), the colon stalks characterizing the marked transform
  correspond along the bijective stalk maps of `e` (`Ideal.map_colon_pow_of_bijective`), and the
  uniqueness of the colon characterization (`IsDivExceptional.unique`) concludes.
* `idealSheaf_image_diffeomorph_pullback`, `birationalTransform_image_diffeomorph` (**base
  change**): for a diffeomorphism `g : M₁ ≃ M₂` of the base, the ideal sheaf of `g(Y)` pulls back
  to the ideal sheaf of `Y` (`comap_idealSheaf_of_isLocalDiffeomorph` and the congruence of the
  ideal sheaves of one set), and the marked transform of `(J, k)` along the blowing-up
  `g ∘ π : M' → M₂` of `g(Y)` (`IsBlowUp.diffeomorph_comp`) is the marked transform of
  `(g^* J, k)` along `π`.

In the step of the push-forward identity, `j_{i+1} = ι_{S_{i+1}} ∘ e_{i+1}` with `e_{i+1}` the
unique diffeomorphism between the given blowing-up `e_i ∘ π_i^T : T_{i+1} → S_i` and the
restricted blow-down `S_{i+1} → S_i` (`blowUpStep`); the one-blowing-up Lemma 62
[Kol07, Lemma 62] handles `ι_{S_{i+1}}`, the invariance handles `e_{i+1}`, the base change
handles `e_i`.
-/

public section

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### Invariance under a diffeomorphism over the base -/

section Invariance

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M}
  {c : ℕ} {M₁' M₂' : Type u} [TopologicalSpace M₁'] [ChartedSpace E M₁'] [IsManifold 𝓘(𝕜, E) ω M₁']
  [T2Space M₁'] [SecondCountableTopology M₁'] [TopologicalSpace M₂'] [ChartedSpace E M₂']
  [IsManifold 𝓘(𝕜, E) ω M₂'] [T2Space M₂'] [SecondCountableTopology M₂'] {π₁ : M₁' → M}
  {π₂ : M₂' → M}

/-- The marked transform [Kol07, Definition 60] is invariant under a diffeomorphism `e : M₁' ≃ M₂'`
over `M` between two blowings-up of the centre `Y` (the unique diffeomorphism of
[BM88, Definition 4.1]): the marked transform along `π₂` pulls back along `e` to the marked
transform along `π₁`. The total transform and the exceptional ideal sheaf pull back to each other
(`pullback_pullback`, `π₂ ∘ e = π₁`), the colon stalks correspond along the bijective stalk maps
of `e`, and the uniqueness of the colon characterization concludes. Not in the sources; an
auxiliary lemma. -/
theorem birationalTransform_pullback_of_comp_eq (hY : IsClosedSubmanifold ψ Y c)
    (h₁ : IsBlowUp ψ Y c π₁) (h₂ : IsBlowUp ψ Y c π₂) (e : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M₁' M₂' ω)
    (he : π₂ ∘ e = π₁) (J : MarkedIdealSheaf (structureSheaf 𝕜 E M))
    (hm : ∀ a ∈ Y, (J.m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J.I a) :
    (MarkedIdealSheaf.birationalTransform hY h₂ J).I.pullback ⇑e e.contMDiff =
      (MarkedIdealSheaf.birationalTransform hY h₁ J).I := by
  have htot : (J.I.pullback π₂ h₂.contMDiff).pullback ⇑e e.contMDiff =
      J.I.pullback π₁ h₁.contMDiff := by
    rw [IdealSheaf.pullback_pullback]
    exact IdealSheaf.pullback_congr _ _ _ he
  have hexc : (hY.idealSheaf.pullback π₂ h₂.contMDiff).pullback ⇑e e.contMDiff =
      hY.idealSheaf.pullback π₁ h₁.contMDiff := by
    rw [IdealSheaf.pullback_pullback]
    exact IdealSheaf.pullback_congr _ _ _ he
  have h2 := isDivExceptional_birationalTransform hY h₂ J hm
  refine IsDivExceptional.unique ?_ (isDivExceptional_birationalTransform hY h₁ J hm)
  intro p
  have hbij := germMap_bijective_of_isLocalDiffeomorphAt ⇑e e.contMDiff (e.isLocalDiffeomorph p)
  rw [IdealSheaf.stalkIdeal_pullback, h2 (e p), Ideal.map_colon_pow_of_bijective _ hbij,
    ← IdealSheaf.stalkIdeal_pullback ⇑e e.contMDiff,
    ← IdealSheaf.stalkIdeal_pullback ⇑e e.contMDiff, htot, hexc]

end Invariance

/-! ### Base change along a diffeomorphism -/

section BaseChange

variable {M₁ M₂ M' : AnalyticManifold.{u} 𝕜 E} (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M₁ M₂ ω)
  {Y : Set M₁} {c : ℕ}

/-- The ideal sheaf of the image `g(Y)` of a closed submanifold under a diffeomorphism pulls back
along `g` to the ideal sheaf of `Y` (by the uniqueness of the ideal sheaf of a closed
submanifold): `comap_idealSheaf_of_isLocalDiffeomorph` for the preimage `g⁻¹(g(Y)) = Y`. -/
theorem idealSheaf_image_diffeomorph_pullback (hY : IsClosedSubmanifold ψ Y c) :
    (hY.image_diffeomorph g).idealSheaf.pullback ⇑g g.contMDiff = hY.idealSheaf :=
  (comap_idealSheaf_of_isLocalDiffeomorph ψ (⟨⇑g, g.contMDiff⟩ : AnalyticMap M₁ M₂)
    g.isLocalDiffeomorph (hY.image_diffeomorph g)).trans
    (IsClosedSubmanifold.idealSheaf_congr _ hY ((EquivLike.injective g).preimage_image Y))

/-- Base change of the marked transform [Kol07, Definition 60] along a diffeomorphism
`g : M₁ ≃ M₂` (the centres `Z_i^X = (j_i)_* Z_i^S` of [Kol07, 30.3]): the marked transform of
`(J, k)` along the blowing-up `g ∘ π` of `g(Y)` is the marked transform of `(g^* J, k)` along the
blowing-up `π` of `Y`. The total transforms agree (`pullback_pullback`), the exceptional ideal
sheaves agree by `idealSheaf_image_diffeomorph_pullback`, and the uniqueness of the colon
characterization concludes; the marking is legitimate for `(g^* J, k)` by
`le_ordAlongIdeal_pullback`. -/
theorem birationalTransform_image_diffeomorph {π : M' → M₁} (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) (J : AnalyticManifold.IdealSheaf M₂) (k : ℕ)
    (hk : ∀ a ∈ ⇑g '' Y,
      (k : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (hY.image_diffeomorph g).idealSheaf J a) :
    (MarkedIdealSheaf.birationalTransform (hY.image_diffeomorph g) (h.diffeomorph_comp g)
        ⟨J, k⟩).I =
      (MarkedIdealSheaf.birationalTransform hY h ⟨J.pullback ⇑g g.contMDiff, k⟩).I := by
  have hD := idealSheaf_image_diffeomorph_pullback g hY
  have hk' : ∀ a ∈ Y,
      (k : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf (J.pullback ⇑g g.contMDiff) a := by
    intro a ha
    rw [← hD]
    exact le_ordAlongIdeal_pullback _ _ (hk (g a) ⟨a, ha, rfl⟩)
  have htot : J.pullback _ (h.diffeomorph_comp g).contMDiff =
      (J.pullback ⇑g g.contMDiff).pullback π h.contMDiff := by
    simp
  have hexc : (hY.image_diffeomorph g).idealSheaf.pullback _ (h.diffeomorph_comp g).contMDiff =
      hY.idealSheaf.pullback π h.contMDiff := by
    rw [← hD, IdealSheaf.pullback_pullback]
  refine IsDivExceptional.unique (isDivExceptional_birationalTransform _ _ ⟨J, k⟩ hk) ?_
  rw [htot, hexc]
  exact isDivExceptional_birationalTransform hY h ⟨J.pullback ⇑g g.contMDiff, k⟩ hk'

end BaseChange

end Hironaka.Manifold

end
