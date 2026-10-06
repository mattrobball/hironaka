/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.SigmaIdealSheaf
public import Hironaka.AnalyticSpace.ClosedSubspace
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceIndependence
import Hironaka.AnalyticSpace.LocalIso
import Hironaka.AnalyticSpace.Manifold.Comap
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Kol07Thm45.ClosedSubspaceHom
import Hironaka.Resolution.Analytic.Kol07Thm45.RestrictInclusion
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The `homOfPullbackEq` calculus across two models

Generic identities for the morphism of closed subspaces
`IdealSheaf.homOfPullbackEq f hf h : Sp(J') → Sp(J)` over an analytic map `f` between
standard-model manifolds of possibly different dimensions with `J' = f^* J`
(`ClosedSubspaceHom.lean`), for the padding identity at the coproduct of the pieces
(`CoproductPadIdentity.lean`; the weak commutation with closed embeddings, [Kol07, 34.4]); none of
them mentions an embedding datum or a blow-up run:

* `IdealSheaf.sigmaOf_mono`: the coproduct ideal sheaf is monotone summand by summand;
* `IsClosedSubmanifold.pullback_idealSheaf_diffeomorph_of_eq`: the cast form (`k = n`) of
  `comap_idealSheaf_of_isLocalDiffeomorph` — the ideal sheaf of a closed submanifold pulled back
  along a diffeomorphism across a model cast is the ideal sheaf of its preimage;
* `comap_homOfPullbackEq_comap_toAnalyticSpaceι_idealSheaf`: the member transport — when the
  ideal sheaf of a closed submanifold `Y` of the target pulls back along `f` to that of `Y'`, the
  closed subspaces of `Sp(J)` and `Sp(J')` they trace correspond under `homOfPullbackEq`;
* `IdealSheaf.homOfPullbackEq_comp_fun`: `homOfPullbackEq` along a composite is the composite of
  the `homOfPullbackEq`s (the raw-function, two-models-per-step form of `homOfPullbackEq_comp`,
  `QuotientHomSquares.lean`);
* `quotientMap_toSpaceHom_comp_homOfPullbackEq`: the quotient square — for `σ₁ ∘ f = g ∘ σ₂` on
  the ambient manifolds with `K₂ = f^* K₁` and `J₂ = g^* J₁`, the quotient maps along `Sp(σᵢ)`
  commute with the `homOfPullbackEq`s along `f` and `g` (the mechanism of
  `localResolutionHomOn_comp_map`, `LocalResolutionOn.lean`: `Hom.ext_of_comp_quotientι`,
  `quotientMap_comp_quotientι`, `homOfPullbackEq_comp_toAnalyticSpaceι`, `ofManifoldHom_comp`).

Not in the sources; bookkeeping.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set AnalyticSpace
open KLocallyRingedSpace Hironaka.Manifold AnalyticManifold.BlowUpSequence
open scoped Manifold ContDiff

universe u

namespace Manifold

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜]

/-- `IdealSheaf.sigmaOf` is monotone summand by summand (stalkwise, through `stalkIdeal_sigmaOf_mk`
and `Ideal.map_mono`). -/
theorem IdealSheaf.sigmaOf_mono {σ : Type u} [Countable σ] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
        (N : σ → AnalyticManifold.{u} 𝕜 E)
    {J K : ∀ i, AnalyticManifold.IdealSheaf (N i)} (h : ∀ i, J i ≤ K i) :
    IdealSheaf.sigmaOf N J ≤ IdealSheaf.sigmaOf N K := by
  refine IdealSheaf.le_def.mpr fun p => ?_
  refine (Sigma.forall (p := fun p : Σ i, (N i : Type u) =>
    (IdealSheaf.sigmaOf N J).stalkIdeal p ≤ (IdealSheaf.sigmaOf N K).stalkIdeal p)).mpr
    (fun i y => ?_) p
  change (IdealSheaf.sigmaOf N J).stalkIdeal (sigmaMk N i y) ≤
    (IdealSheaf.sigmaOf N K).stalkIdeal (sigmaMk N i y)
  rw [IdealSheaf.stalkIdeal_sigmaOf_mk, IdealSheaf.stalkIdeal_sigmaOf_mk,
    IdealSheaf.stalkIdeal_pullback, IdealSheaf.stalkIdeal_pullback]
  exact Ideal.map_mono (IdealSheaf.le_def.mp (h i) _)

/-- The cast form of `comap_idealSheaf_of_isLocalDiffeomorph`: the ideal sheaf of a closed
submanifold pulled back along a DIFFEOMORPHISM across a model cast `k = n` is the ideal sheaf of
its preimage. -/
theorem IsClosedSubmanifold.pullback_idealSheaf_diffeomorph_of_eq {k n : ℕ} (hk : k = n)
    {M : AnalyticManifold.{u} 𝕜 (Fin k → 𝕜)}
    {M' : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (G : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin k → 𝕜) M' M ω) {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin k → 𝕜)) Y c) {Y' : Set M'}
    (hY' : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) Y' c)
    (hYY' : ⇑G ⁻¹' Y = Y') :
    hY.idealSheaf.pullback ⇑G G.contMDiff = hY'.idealSheaf := by
  subst hk
  exact (comap_idealSheaf_of_isLocalDiffeomorph (ContinuousLinearEquiv.refl 𝕜 (Fin k → 𝕜))
    (Diffeomorph.toAnalyticMap G) G.isLocalDiffeomorph hY).trans
    (IsClosedSubmanifold.idealSheaf_congr _ _ hYY')

/-- The member transport along `homOfPullbackEq`: for `J' = f^* J` and a member `Y` of the target
whose ideal sheaf pulls back along `f` to
the ideal sheaf of a member `Y'` of the source, the closed subspace of `Sp(J)` traced by `Y` pulls
back along `homOfPullbackEq f` to the closed subspace of `Sp(J')` traced by `Y'` (`comap_comp_hom`,
`homOfPullbackEq_comp_toAnalyticSpaceι`, `comap_ofManifoldHom_eq_pullback`). -/
theorem _root_.Hironaka.Manifold.comap_homOfPullbackEq_comap_toAnalyticSpaceι_idealSheaf {n k : ℕ}
    {A : AnalyticManifold.{u} 𝕜 (Fin k → 𝕜)}
    {A' : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (f : A' → A)
    (hf : ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin k → 𝕜) ω f)
    {J : AnalyticManifold.IdealSheaf A} {J' : AnalyticManifold.IdealSheaf A'}
        (h : J' = J.pullback f hf)
    {Y : Set A} {c : ℕ} (hY : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin k → 𝕜)) Y c)
    {Y' : Set A'} {c' : ℕ}
    (hY' : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) Y' c')
    (hYY : hY.idealSheaf.pullback f hf = hY'.idealSheaf) :
    (AnalyticSpace.ClosedSubspace.comap
        (X := toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin k → 𝕜)) A) hY.idealSheaf
        J.toAnalyticSpaceι).comap (IdealSheaf.homOfPullbackEq f hf h) =
      AnalyticSpace.ClosedSubspace.comap
        (X := toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) A') hY'.idealSheaf
        J'.toAnalyticSpaceι := by
  refine (ClosedSubspace.comap_comp_hom _ _ _).symm.trans ?_
  refine (congrArg (fun m => AnalyticSpace.ClosedSubspace.comap _ m)
    (homOfPullbackEq_comp_toAnalyticSpaceι f hf h)).trans ?_
  refine (ClosedSubspace.comap_comp_hom _ _ _).trans ?_
  exact congrArg (AnalyticSpace.ClosedSubspace.comap · J'.toAnalyticSpaceι)
    ((comap_ofManifoldHom_eq_pullback f hf hY.idealSheaf).trans hYY)

/-- The raw-function form of `homOfPullbackEq_comp` (`QuotientHomSquares.lean`), any two models per
step: `homOfPullbackEq` along a composite is the composite of the `homOfPullbackEq`s. -/
theorem IdealSheaf.homOfPullbackEq_comp_fun {n₁ n₂ n₃ : ℕ}
    {A₁ : AnalyticManifold.{u} 𝕜 (Fin n₁ → 𝕜)}
    {A₂ : AnalyticManifold.{u} 𝕜 (Fin n₂ → 𝕜)}
    {A₃ : AnalyticManifold.{u} 𝕜 (Fin n₃ → 𝕜)}
    (f₁ : A₁ → A₂) (hf₁ : ContMDiff 𝓘(𝕜, Fin n₁ → 𝕜) 𝓘(𝕜, Fin n₂ → 𝕜) ω f₁)
    (f₂ : A₂ → A₃) (hf₂ : ContMDiff 𝓘(𝕜, Fin n₂ → 𝕜) 𝓘(𝕜, Fin n₃ → 𝕜) ω f₂)
    {J₁ : AnalyticManifold.IdealSheaf A₁} {J₂ : AnalyticManifold.IdealSheaf A₂}
        {J₃ : AnalyticManifold.IdealSheaf A₃}
    (h₁ : J₁ = J₂.pullback f₁ hf₁) (h₂ : J₂ = J₃.pullback f₂ hf₂)
    (h₁₂ : J₁ = J₃.pullback (f₂ ∘ f₁) (hf₂.comp hf₁)) :
    IdealSheaf.homOfPullbackEq f₁ hf₁ h₁ ≫ IdealSheaf.homOfPullbackEq f₂ hf₂ h₂ =
      IdealSheaf.homOfPullbackEq (f₂ ∘ f₁) (hf₂.comp hf₁) h₁₂ := by
  refine Hom.ext_of_comp_quotientι _ ?_
  have e₂ : IdealSheaf.homOfPullbackEq f₂ hf₂ h₂ ≫ J₃.toAnalyticSpaceι =
      J₂.toAnalyticSpaceι ≫ ofManifoldHom f₂ hf₂ :=
    homOfPullbackEq_comp_toAnalyticSpaceι f₂ hf₂ h₂
  have e₁ : IdealSheaf.homOfPullbackEq f₁ hf₁ h₁ ≫ J₂.toAnalyticSpaceι =
      J₁.toAnalyticSpaceι ≫ ofManifoldHom f₁ hf₁ :=
    homOfPullbackEq_comp_toAnalyticSpaceι f₁ hf₁ h₁
  have e₁₂ : IdealSheaf.homOfPullbackEq (f₂ ∘ f₁) (hf₂.comp hf₁) h₁₂ ≫ J₃.toAnalyticSpaceι =
      J₁.toAnalyticSpaceι ≫ ofManifoldHom (f₂ ∘ f₁) (hf₂.comp hf₁) :=
    homOfPullbackEq_comp_toAnalyticSpaceι (f₂ ∘ f₁) (hf₂.comp hf₁) h₁₂
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => IdealSheaf.homOfPullbackEq f₁ hf₁ h₁ ≫ k) e₂).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ ofManifoldHom f₂ hf₂) e₁).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun k => J₁.toAnalyticSpaceι ≫ k)
              (ofManifoldHom_comp f₁ hf₁ f₂ hf₂).symm).trans e₁₂.symm)))))

/-- Composition in the category of `𝕜`-locally ringed spaces, pinned (the device of
`QuotientHomSquares.lean`: one spelling along the chain keeps the elaborator from unifying two
spellings under pending metavariables). -/
local infixr:80 " ≫ₖ " => @CategoryStruct.comp (KLocallyRingedSpace 𝕜) _ _ _ _

/-- The generic QUOTIENT SQUARE (the mechanism of `localResolutionHomOn_comp_map`,
`LocalResolutionOn.lean`): for `σ₁ ∘ f = g ∘ σ₂` on the ambient manifolds (any two models),
with `K₂ = f^* K₁` and `J₂ = g^* J₁`, the quotient maps along `Sp(σᵢ)` commute with the
`homOfPullbackEq`s along `f` and `g`. -/
theorem _root_.Hironaka.Manifold.quotientMap_toSpaceHom_comp_homOfPullbackEq {n k : ℕ}
    {M₁ N₁ : AnalyticManifold.{u} 𝕜 (Fin k → 𝕜)}
    {M₂ N₂ : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (σ₁ : AnalyticMap M₁ N₁) (σ₂ : AnalyticMap M₂ N₂)
    (f : M₂ → M₁) (hf : ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin k → 𝕜) ω f)
    (g : N₂ → N₁) (hg : ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin k → 𝕜) ω g)
    (hcomm : ⇑σ₁ ∘ f = g ∘ ⇑σ₂)
    {K₁ : AnalyticManifold.IdealSheaf M₁} {J₁ : AnalyticManifold.IdealSheaf N₁}
    (c₁ : QuotientSpace.Compat
      (toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin k → 𝕜)) σ₁).1 K₁ J₁)
    {K₂ : AnalyticManifold.IdealSheaf M₂} {J₂ : AnalyticManifold.IdealSheaf N₂}
    (c₂ : QuotientSpace.Compat
      (toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) σ₂).1 K₂ J₂)
    (hK : K₂ = K₁.pullback f hf) (hJ : J₂ = J₁.pullback g hg) :
    IdealSheaf.homOfPullbackEq f hf hK ≫ quotientMap (toSpaceHom
        (ContinuousLinearEquiv.refl 𝕜 (Fin k → 𝕜)) σ₁) K₁ J₁ c₁ =
      quotientMap (toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          σ₂) K₂ J₂ c₂ ≫ IdealSheaf.homOfPullbackEq g hg hJ := by
  refine Hom.ext_of_comp_quotientι _ ?_
  have s₁ : quotientMap (toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin k → 𝕜)) σ₁)
        K₁ J₁ c₁ ≫ₖ J₁.toAnalyticSpaceι =
      K₁.toAnalyticSpaceι ≫ₖ ofManifoldHom ⇑σ₁ σ₁.contMDiff :=
    quotientMap_comp_quotientι _ _ _ _
  have s₂ : quotientMap (toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) σ₂)
        K₂ J₂ c₂ ≫ₖ J₂.toAnalyticSpaceι =
      K₂.toAnalyticSpaceι ≫ₖ ofManifoldHom ⇑σ₂ σ₂.contMDiff :=
    quotientMap_comp_quotientι _ _ _ _
  have e₁ : IdealSheaf.homOfPullbackEq f hf hK ≫ₖ K₁.toAnalyticSpaceι =
      K₂.toAnalyticSpaceι ≫ₖ ofManifoldHom f hf :=
    homOfPullbackEq_comp_toAnalyticSpaceι f hf hK
  have e₂ : IdealSheaf.homOfPullbackEq g hg hJ ≫ₖ J₁.toAnalyticSpaceι =
      J₂.toAnalyticSpaceι ≫ₖ ofManifoldHom g hg :=
    homOfPullbackEq_comp_toAnalyticSpaceι g hg hJ
  have hsq₀ : ∀ (k' : M₂ → N₁) (hk : ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin k → 𝕜) ω k')
      (_ : ⇑σ₁ ∘ f = k'),
      ofManifoldHom (⇑σ₁ ∘ f) (σ₁.contMDiff.comp hf) = ofManifoldHom k' hk := by
    intro k' hk e
    subst e
    rfl
  have hsq : ofManifoldHom f hf ≫ₖ ofManifoldHom ⇑σ₁ σ₁.contMDiff =
      ofManifoldHom ⇑σ₂ σ₂.contMDiff ≫ₖ ofManifoldHom g hg :=
    (ofManifoldHom_comp _ _ _ _).symm.trans
      ((hsq₀ _ (hg.comp σ₂.contMDiff) hcomm).trans (ofManifoldHom_comp _ _ _ _))
  have key : (IdealSheaf.homOfPullbackEq f hf hK ≫ₖ
        quotientMap (toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin k → 𝕜)) σ₁)
          K₁ J₁ c₁) ≫ₖ J₁.toAnalyticSpaceι =
      (quotientMap (toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) σ₂)
          K₂ J₂ c₂ ≫ₖ IdealSheaf.homOfPullbackEq g hg hJ) ≫ₖ J₁.toAnalyticSpaceι :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => IdealSheaf.homOfPullbackEq f hf hK ≫ₖ k) s₁).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ₖ ofManifoldHom ⇑σ₁ σ₁.contMDiff) e₁).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun k => K₂.toAnalyticSpaceι ≫ₖ k) hsq).trans
                ((Category.assoc _ _ _).symm.trans
                  ((congrArg (fun k => k ≫ₖ ofManifoldHom g hg) s₂.symm).trans
                    ((Category.assoc _ _ _).trans
                      ((congrArg (fun k => quotientMap (toSpaceHom
                        (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) σ₂) K₂ J₂ c₂ ≫ₖ k) e₂.symm).trans
                        (Category.assoc _ _ _).symm)))))))))
  exact key

end Manifold

end
