/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.AmbientEmb
public import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionOn
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceRestrict
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Resolution.Analytic.Kol07Thm45.QuotientHomSquares
import Hironaka.Resolution.Analytic.OrderReduction.Step22Pullback
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Hironaka.Resolution.Analytic.Kol07Thm45.PadRestrict

/-!
# The over-`X` core of the mixed-pair transition

The mixed-pair transition (`CoproductMixedTransition.lean`) identifies the parts over a common
base open `P` of the local resolutions of two padded pieces `E₁⁺ = E₁.padAlong σ₁`,
`E₂⁺ = E₂.padAlong σ₂` through the common admissible input `T₀` on the shear's domain
`N₀ = Sp(𝕊⁺.G)|W₁'` (the pieces restricted to `O' ⊆ V₁ ∩ V₂`, padded: `𝕊⁺`, `𝕋⁺`) and its two
open embeddings `u = ι₁⁺ ∘ ι_{W₁'}`, `v = ι₂⁺ ∘ ι_{W₂'} ∘ g` into the two padded ambients. Its
over-`X` clause reduces (through the maps of the local resolutions to the closed subspaces of the
ambients, `localResolutionHomOn_comp_map`) to the statement of THIS module: **the two read-down
maps of `Sp(T₀.I|W₀)` to `X`** — along `u` into `Sp(E₁⁺.I|W)` and then `pieceOverHom`, along `v`
into `Sp(E₂⁺.I|W')` and then `pieceOverHom` — **agree**. The proof is the shear's morphism
identity `hmor` ([Kol07, Lemma 39]; the shear of `exists_padded_equivalence_hom_point`) conjugated
by the squares of `QuotientHomSquares.lean`: `homOfPullbackEq` along a composite is the composite
(functoriality), the inverse embedding of a padded restricted piece is carried to the inverse
embedding of the padded piece over the inclusion of the pieces, and `restrictIncl ≫ ofRestrict`.

Two bookkeeping lemmas open the module: the congruence of `homOfPullbackEq` in the function, and
the composite form of `homOfPullbackEq_comp` with the composite function given by name. A generic
category lemma (`comp_leg_eq`) does the associativity bookkeeping of one leg. Not in the sources
beyond Lemma 39; bookkeeping.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set AnalyticSpace
open KLocallyRingedSpace
open scoped Manifold ContDiff

universe u

namespace CategoryTheory

variable {𝒞 : Type*} [Category 𝒞]

/-- The associativity bookkeeping of one leg of the over-`X` identity, in any category — a map `H`
followed by three maps, rewritten through five identities into `ρ ≫ (r₀ ≫ e₀) ≫ o₀`. -/
theorem comp_leg_eq {A₀ B C X' Z C₀ X₀ B₀ : 𝒞} (H : A₀ ⟶ B) (r : B ⟶ C) (eI : C ⟶ X') (o : X' ⟶ Z)
    (K₁ : A₀ ⟶ C) (s1 : H ≫ r = K₁) (K₀ : A₀ ⟶ C₀) (hI : C₀ ⟶ C) (s2 : K₁ = K₀ ≫ hI)
    (e₀ : C₀ ⟶ X₀) (rI : X₀ ⟶ X') (s3 : hI ≫ eI = e₀ ≫ rI) (o₀ : X₀ ⟶ Z) (s4 : rI ≫ o = o₀)
    (ρ : A₀ ⟶ B₀) (r₀ : B₀ ⟶ C₀) (s5 : K₀ = ρ ≫ r₀) :
    H ≫ r ≫ eI ≫ o = ρ ≫ (r₀ ≫ e₀) ≫ o₀ := by
  rw [← Category.assoc H, s1, s2, Category.assoc, ← Category.assoc hI, s3, Category.assoc, s4, s5,
    Category.assoc, ← Category.assoc r₀]

end CategoryTheory

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜]

section Congr

variable {k n : ℕ} {A : AnalyticManifold.{u} 𝕜 (Fin k → 𝕜)}
  {A' : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  {J' : AnalyticManifold.IdealSheaf A'} {J : AnalyticManifold.IdealSheaf A}

/-- `homOfPullbackEq` depends on the function only — two equal functions give the same morphism
(the proofs are irrelevant). -/
theorem _root_.Manifold.IdealSheaf.homOfPullbackEq_congr_fun {f f' : A' → A} (hff' : f = f')
    (hf : ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin k → 𝕜) ω f)
    (hf' : ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin k → 𝕜) ω f')
    (h : J' = J.pullback f hf) (h' : J' = J.pullback f' hf') :
    IdealSheaf.homOfPullbackEq f hf h = IdealSheaf.homOfPullbackEq f' hf' h' := by
  subst hff'
  rfl

end Congr

section CompEq

variable {n : ℕ} {A₁ A₂ A₃ : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  {J₁ : AnalyticManifold.IdealSheaf A₁} {J₂ : AnalyticManifold.IdealSheaf A₂}
      {J₃ : AnalyticManifold.IdealSheaf A₃}

/-- `homOfPullbackEq_comp` with the composite function given by name — `f₂ ∘ f₁ = f₁₂` as
functions, the three pull-back identities as stated. -/
theorem _root_.Manifold.IdealSheaf.homOfPullbackEq_comp_of_comp_eq (f₁ : AnalyticMap A₁ A₂)
    (f₂ : AnalyticMap A₂ A₃) (f₁₂ : AnalyticMap A₁ A₃)
    (hf : ⇑f₂ ∘ ⇑f₁ = ⇑f₁₂) (h₁ : J₁ = J₂.pullback ⇑f₁ f₁.contMDiff)
    (h₂ : J₂ = J₃.pullback ⇑f₂ f₂.contMDiff) (h₁₂ : J₁ = J₃.pullback ⇑f₁₂ f₁₂.contMDiff) :
    IdealSheaf.homOfPullbackEq ⇑f₁ f₁.contMDiff h₁ ≫ IdealSheaf.homOfPullbackEq ⇑f₂ f₂.contMDiff h₂
        =
      IdealSheaf.homOfPullbackEq ⇑f₁₂ f₁₂.contMDiff h₁₂ :=
  (IdealSheaf.homOfPullbackEq_comp f₁ f₂ h₁ h₂ (h₁₂.trans
      (IdealSheaf.pullback_congr J₃ f₁₂.contMDiff (f₂.contMDiff.comp f₁.contMDiff) hf.symm))).trans
    (IdealSheaf.homOfPullbackEq_congr_fun hf _ _ _ _)

end CompEq

section Ambient

variable {n k : ℕ} {X : AnalyticSpace.{u} 𝕜} {V V' : Set X}
  (E : PieceEmbedding 𝕜 n X V) (hV' : IsOpen V') (hsub : V' ⊆ V) (σ : Fin n ↪ Fin k)

/-- The ambient of a piece restricted to `V'` and padded along `σ` (named: a local notation cannot
carry the universe). -/
abbrev PieceEmbedding.padRestrictAmbient :
    AnalyticManifold.{u} 𝕜 (Fin k → 𝕜) :=
  pieceAmbient.{u} 𝕜 ((E.restrictPiece hV' hsub).padAlong σ).G

/-- The padded inclusion of ambients `Sp((E|V')⁺.G) → Sp(E⁺.G)`. -/
abbrev PieceEmbedding.padRestrictIncl :
    AnalyticMap (E.padRestrictAmbient hV' hsub σ)
      (pieceAmbient.{u} 𝕜 (E.padAlong σ).G) :=
  pieceAmbientIncl (padOpens_mono σ (E.restrictAmbient_le hV'))

variable (W₁' : Opens (E.padRestrictAmbient hV' hsub σ))

/-- The shear's domain `N₀ = Sp((E|V')⁺.G)|W₁'`. -/
abbrev PieceEmbedding.shearDomain : AnalyticManifold.{u} 𝕜 (Fin k → 𝕜) :=
  (E.padRestrictAmbient hV' hsub σ).restrict W₁'

/-- The common admissible input `T₀` on the shear's domain — the padded restricted piece's ambient
triple pulled back along the inclusion of `W₁'`. -/
abbrev PieceEmbedding.shearInput :
    AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin k → 𝕜)) (E.shearDomain hV' hsub σ W₁') :=
  ((E.restrictPiece hV' hsub).padAlong σ).ambientTriple.pullback
    (AnalyticManifold.inclusion _ W₁') (isLocalDiffeomorph_inclusion _ W₁')

end Ambient

section OverX

variable {n₁ n₂ k : ℕ} {X : AnalyticSpace.{u} 𝕜} {V₁ V₂ : Set X}
  (E₁ : PieceEmbedding 𝕜 n₁ X V₁) (E₂ : PieceEmbedding 𝕜 n₂ X V₂)
  {O' : Set X} (hO' : IsOpen O') (hO'₁ : O' ⊆ V₁) (hO'₂ : O' ⊆ V₂)
  (σ₁ : Fin n₁ ↪ Fin k) (σ₂ : Fin n₂ ↪ Fin k)
  (W₁' : Opens (E₁.padRestrictAmbient hO' hO'₁ σ₁))
  (W₂' : Opens (E₂.padRestrictAmbient hO' hO'₂ σ₂))
  (g :
      AnalyticMap (E₁.shearDomain hO' hO'₁ σ₁ W₁')
          (E₂.shearDomain hO' hO'₂ σ₂ W₂'))
  (W₀ : Opens (E₁.shearDomain hO' hO'₁ σ₁ W₁'))

/-- The common input `T₀` is the pull-back of the first padded piece's ambient triple along
`ι₁⁺ ∘ ι_{W₁'}` (`isPullbackOf_ambientTriple_padAlong_restrictPiece` of `PadRestrict.lean` composed
with the restriction). -/
theorem isPullbackOf_shearInput_padAlong :
    (E₁.shearInput hO' hO'₁ σ₁ W₁').IsPullbackOf (E₁.padAlong σ₁).ambientTriple
      ((E₁.padRestrictIncl hO' hO'₁ σ₁).comp
          (AnalyticManifold.inclusion _ W₁')) :=
  (isPullbackOf_ambientTriple_padAlong_restrictPiece σ₁ E₁ hO' hO'₁).comp
    (AnalyticTriple.isPullbackOf_pullback _ _ _)

/-- Through the shear `g` with its ideal identity `hI`, the common input `T₀` is the pull-back of
the second padded piece's ambient triple along `ι₂⁺ ∘ ι_{W₂'} ∘ g` (the boundary families are
empty on both sides). -/
theorem isPullbackOf_shearInput_shear
    (hI : ((E₁.restrictPiece hO' hO'₁).padAlong σ₁).restrictedIdeal W₁' =
      (((E₂.restrictPiece hO' hO'₂).padAlong σ₂).restrictedIdeal W₂').pullback ⇑g g.contMDiff) :
    (E₁.shearInput hO' hO'₁ σ₁ W₁').IsPullbackOf (E₂.padAlong σ₂).ambientTriple
      ((E₂.padRestrictIncl hO' hO'₂ σ₂).comp
        ((AnalyticManifold.inclusion _ W₂').comp g)) :=
  (isPullbackOf_ambientTriple_padAlong_restrictPiece σ₂ E₂ hO' hO'₂).comp
    ((AnalyticTriple.isPullbackOf_pullback ((E₂.restrictPiece hO' hO'₂).padAlong σ₂).ambientTriple
      (AnalyticManifold.inclusion _ W₂')
          (isLocalDiffeomorph_inclusion _ W₂')).comp
      ⟨hI, (HypersurfaceFamily.empty_comap _).trans
        ((HypersurfaceFamily.empty_comap ⇑g).symm.trans
          (congrArg (fun F => HypersurfaceFamily.comap ⇑g F)
            (HypersurfaceFamily.empty_comap _).symm))⟩)

variable (Wᵢ : Opens (pieceAmbient.{u} 𝕜 (E₁.padAlong σ₁).G))
  (Wⱼ : Opens (pieceAmbient.{u} 𝕜 (E₂.padAlong σ₂).G))
  (hleᵢ :
      ⇑((E₁.padRestrictIncl hO' hO'₁ σ₁).comp
          (AnalyticManifold.inclusion _ W₁')) ''
      (W₀ : Set (E₁.shearDomain hO' hO'₁ σ₁ W₁')) ⊆
    (Wᵢ : Set (pieceAmbient.{u} 𝕜 (E₁.padAlong σ₁).G)))
  (hleⱼ : ⇑((E₂.padRestrictIncl hO' hO'₂ σ₂).comp
      ((AnalyticManifold.inclusion _ W₂').comp g)) ''
      (W₀ : Set (E₁.shearDomain hO' hO'₁ σ₁ W₁')) ⊆
    (Wⱼ : Set (pieceAmbient.{u} 𝕜 (E₂.padAlong σ₂).G)))

/-- Composition in the category of `𝕜`-locally ringed spaces with the category instance fixed (see
`QuotientHomSquares.lean`). -/
local infixr:80 " ≫ₖ " => @CategoryStruct.comp (KLocallyRingedSpace 𝕜) _ _ _ _

/-- **The two read-down maps of the common closed subspace agree** (the uniqueness step of
[Kol07, Theorem 36, proof], through the automorphism of [Kol07, Lemma 39]) — `Sp(T₀.I|W₀)` mapped
into the first padded piece's closed subspace along `ι₁⁺ ∘ ι_{W₁'}` and then to `X` by
`pieceOverHom`, or into the second's along `ι₂⁺ ∘ ι_{W₂'} ∘ g` and then to `X`, is the same
morphism. The shear's `hmor` conjugated by the squares of `QuotientHomSquares.lean`. -/
theorem homOfPullbackEq_restrictMap_comp_pieceOverHom_eq_of_shear
    (hI : ((E₁.restrictPiece hO' hO'₁).padAlong σ₁).restrictedIdeal W₁' =
      (((E₂.restrictPiece hO' hO'₂).padAlong σ₂).restrictedIdeal W₂').pullback ⇑g g.contMDiff)
    (hmor :
        (IdealSheaf.homOfPullbackEq ⇑g g.contMDiff hI ≫
            ((E₂.restrictPiece hO' hO'₂).padAlong σ₂).restrictedIdealHom W₂') ≫
            ((E₂.restrictPiece hO' hO'₂).padAlong σ₂).embInv =
          ((E₁.restrictPiece hO' hO'₁).padAlong σ₁).restrictedIdealHom W₁' ≫
            ((E₁.restrictPiece hO' hO'₁).padAlong σ₁).embInv) :
    (IdealSheaf.homOfPullbackEq _ _
        (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap (E₁.padAlong σ₁).ambientTriple Wᵢ
          (E₁.shearInput hO' hO'₁ σ₁ W₁')
          ((E₁.padRestrictIncl hO' hO'₁ σ₁).comp
              (AnalyticManifold.inclusion _ W₁'))
          W₀ hleᵢ (isPullbackOf_shearInput_padAlong E₁ hO' hO'₁ σ₁ W₁')) :
        (BEDanFamStar.restrictedIdealOn (E₁.shearInput hO' hO'₁ σ₁ W₁')
          W₀).toAnalyticSpace.toKLocallyRingedSpace ⟶
          ((E₁.padAlong σ₁).restrictedIdeal Wᵢ).toAnalyticSpace.toKLocallyRingedSpace) ≫
        (E₁.padAlong σ₁).pieceOverHom Wᵢ =
      (IdealSheaf.homOfPullbackEq _ _
        (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap (E₂.padAlong σ₂).ambientTriple Wⱼ
          (E₁.shearInput hO' hO'₁ σ₁ W₁')
          ((E₂.padRestrictIncl hO' hO'₂ σ₂).comp
            ((AnalyticManifold.inclusion _ W₂').comp g))
          W₀ hleⱼ (isPullbackOf_shearInput_shear E₁ E₂ hO' hO'₁ hO'₂ σ₁ σ₂ W₁' W₂' g hI)) :
        (BEDanFamStar.restrictedIdealOn (E₁.shearInput hO' hO'₁ σ₁ W₁')
          W₀).toAnalyticSpace.toKLocallyRingedSpace ⟶
          ((E₂.padAlong σ₂).restrictedIdeal Wⱼ).toAnalyticSpace.toKLocallyRingedSpace) ≫
        (E₂.padAlong σ₂).pieceOverHom Wⱼ := by
  -- names for the pieces and the maps
  let S := (E₁.restrictPiece hO' hO'₁).padAlong σ₁
  let T := (E₂.restrictPiece hO' hO'₂).padAlong σ₂
  let a₁ := E₁.padRestrictIncl hO' hO'₁ σ₁
  let a₂ := E₂.padRestrictIncl hO' hO'₂ σ₂
  let j₁ := AnalyticManifold.inclusion (E₁.padRestrictAmbient hO' hO'₁ σ₁) W₁'
  let j₂ := AnalyticManifold.inclusion (E₂.padRestrictAmbient hO' hO'₂ σ₂) W₂'
  let j₀ := AnalyticManifold.inclusion (E₁.shearDomain hO' hO'₁ σ₁ W₁') W₀
  -- the padded ideals of the restricted pieces are the pull-backs of the padded pieces' ideals
  have hpad₁ : S.ideal = (E₁.padAlong σ₁).ideal.pullback ⇑a₁ a₁.contMDiff :=
    padIdeal_comap σ₁ (E₁.restrictAmbient_le hO') E₁.ideal
  have hpad₂ : T.ideal = (E₂.padAlong σ₂).ideal.pullback ⇑a₂ a₂.contMDiff :=
    padIdeal_comap σ₂ (E₂.restrictAmbient_le hO') E₂.ideal
  -- the pull-back identities of the composite maps out of the device's ambient
  have hK₀ : BEDanFamStar.restrictedIdealOn (E₁.shearInput hO' hO'₁ σ₁ W₁') W₀ =
      S.ideal.pullback ⇑(j₁.comp j₀) (j₁.comp j₀).contMDiff :=
    IdealSheaf.pullback_pullback _ _ _ _ _
  have hK₁ : BEDanFamStar.restrictedIdealOn (E₁.shearInput hO' hO'₁ σ₁ W₁') W₀ =
      (E₁.padAlong σ₁).ideal.pullback ⇑(a₁.comp (j₁.comp j₀)) (a₁.comp (j₁.comp j₀)).contMDiff :=
    hK₀.trans
        ((congrArg (fun K : AnalyticManifold.IdealSheaf (E₁.padRestrictAmbient hO' hO'₁ σ₁) =>
      K.pullback ⇑(j₁.comp j₀) (j₁.comp j₀).contMDiff) hpad₁).trans
      (IdealSheaf.pullback_pullback _ _ _ _ _))
  have hKc : BEDanFamStar.restrictedIdealOn (E₁.shearInput hO' hO'₁ σ₁ W₁') W₀ =
      (T.restrictedIdeal W₂').pullback ⇑(g.comp j₀) (g.comp j₀).contMDiff :=
    (congrArg (fun K : AnalyticManifold.IdealSheaf (E₁.shearDomain hO' hO'₁ σ₁ W₁') =>
      K.pullback ⇑j₀ j₀.contMDiff) hI).trans (IdealSheaf.pullback_pullback _ _ _ _ _)
  have hK₂' : BEDanFamStar.restrictedIdealOn (E₁.shearInput hO' hO'₁ σ₁ W₁') W₀ =
      T.ideal.pullback ⇑(j₂.comp (g.comp j₀)) (j₂.comp (g.comp j₀)).contMDiff :=
    hKc.trans (IdealSheaf.pullback_pullback _ _ _ _ _)
  have hK₂ : BEDanFamStar.restrictedIdealOn (E₁.shearInput hO' hO'₁ σ₁ W₁') W₀ =
      (E₂.padAlong σ₂).ideal.pullback ⇑(a₂.comp (j₂.comp (g.comp j₀)))
        (a₂.comp (j₂.comp (g.comp j₀))).contMDiff :=
    hK₂'.trans
        ((congrArg (fun K : AnalyticManifold.IdealSheaf (E₂.padRestrictAmbient hO' hO'₂ σ₂) =>
      K.pullback ⇑(j₂.comp (g.comp j₀)) (j₂.comp (g.comp j₀)).contMDiff) hpad₂).trans
      (IdealSheaf.pullback_pullback _ _ _ _ _))
  -- leg 1: `H₁ ≫ r_i = K₁ = K₀ ≫ (ι₁⁺)^♯`, `K₀ = ρ₀ ≫ r_𝕊`
  have s1₁ : IdealSheaf.homOfPullbackEq _ _
        (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap (E₁.padAlong σ₁).ambientTriple Wᵢ
          (E₁.shearInput hO' hO'₁ σ₁ W₁') (a₁.comp j₁) W₀ hleᵢ
          (isPullbackOf_shearInput_padAlong E₁ hO' hO'₁ σ₁ W₁')) ≫ₖ
        (E₁.padAlong σ₁).restrictedIdealHom Wᵢ =
      IdealSheaf.homOfPullbackEq _ _ hK₁ :=
    IdealSheaf.homOfPullbackEq_comp_of_comp_eq _
        (AnalyticManifold.inclusion _ Wᵢ) _
      (funext fun _ => rfl) _ rfl hK₁
  have s2₁ : IdealSheaf.homOfPullbackEq _ _ hK₁ =
      IdealSheaf.homOfPullbackEq _ _ hK₀ ≫ₖ IdealSheaf.homOfPullbackEq _ _ hpad₁ :=
    (IdealSheaf.homOfPullbackEq_comp_of_comp_eq (j₁.comp j₀) a₁ _ rfl hK₀ hpad₁ hK₁).symm
  have s3₁ : IdealSheaf.homOfPullbackEq _ _ hpad₁ ≫ₖ (E₁.padAlong σ₁).embInv =
      S.embInv ≫ₖ KLocallyRingedSpace.restrictIncl X.toKLocallyRingedSpace
        (PieceEmbedding.openOf_le_openOf hO' hO'₁) :=
    E₁.embInv_comp_homOfPullbackEq_padAlong_restrictPiece hO' hO'₁ σ₁
  have s4₁ : KLocallyRingedSpace.restrictIncl X.toKLocallyRingedSpace
        (PieceEmbedding.openOf_le_openOf hO' hO'₁) ≫ₖ
        ofRestrict X.toKLocallyRingedSpace (openOf X V₁) =
      ofRestrict X.toKLocallyRingedSpace (openOf X O') :=
    KLocallyRingedSpace.restrictIncl_comp_ofRestrict _ _
  have s5₁ : IdealSheaf.homOfPullbackEq _ _ hK₀ =
      IdealSheaf.homOfPullbackEq ⇑j₀ j₀.contMDiff rfl ≫ₖ S.restrictedIdealHom W₁' :=
    (IdealSheaf.homOfPullbackEq_comp_of_comp_eq j₀ j₁ _ rfl rfl rfl hK₀).symm
  -- leg 2: the same with the shear inserted
  have s1₂ : IdealSheaf.homOfPullbackEq _ _
        (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap (E₂.padAlong σ₂).ambientTriple Wⱼ
          (E₁.shearInput hO' hO'₁ σ₁ W₁') (a₂.comp (j₂.comp g)) W₀ hleⱼ
          (isPullbackOf_shearInput_shear E₁ E₂ hO' hO'₁ hO'₂ σ₁ σ₂ W₁' W₂' g hI)) ≫ₖ
        (E₂.padAlong σ₂).restrictedIdealHom Wⱼ =
      IdealSheaf.homOfPullbackEq _ _ hK₂ :=
    IdealSheaf.homOfPullbackEq_comp_of_comp_eq _
        (AnalyticManifold.inclusion _ Wⱼ) _
      (funext fun _ => rfl) _ rfl hK₂
  have s2₂ : IdealSheaf.homOfPullbackEq _ _ hK₂ =
      IdealSheaf.homOfPullbackEq _ _ hK₂' ≫ₖ IdealSheaf.homOfPullbackEq _ _ hpad₂ :=
    (IdealSheaf.homOfPullbackEq_comp_of_comp_eq (j₂.comp (g.comp j₀)) a₂ _ rfl hK₂' hpad₂
      hK₂).symm
  have s3₂ : IdealSheaf.homOfPullbackEq _ _ hpad₂ ≫ₖ (E₂.padAlong σ₂).embInv =
      T.embInv ≫ₖ KLocallyRingedSpace.restrictIncl X.toKLocallyRingedSpace
        (PieceEmbedding.openOf_le_openOf hO' hO'₂) :=
    E₂.embInv_comp_homOfPullbackEq_padAlong_restrictPiece hO' hO'₂ σ₂
  have s4₂ : KLocallyRingedSpace.restrictIncl X.toKLocallyRingedSpace
        (PieceEmbedding.openOf_le_openOf hO' hO'₂) ≫ₖ
        ofRestrict X.toKLocallyRingedSpace (openOf X V₂) =
      ofRestrict X.toKLocallyRingedSpace (openOf X O') :=
    KLocallyRingedSpace.restrictIncl_comp_ofRestrict _ _
  have s5c : IdealSheaf.homOfPullbackEq _ _ hKc =
      IdealSheaf.homOfPullbackEq ⇑j₀ j₀.contMDiff rfl ≫ₖ
        IdealSheaf.homOfPullbackEq ⇑g g.contMDiff hI :=
    (IdealSheaf.homOfPullbackEq_comp_of_comp_eq j₀ g _ rfl rfl hI hKc).symm
  have s5₂ : IdealSheaf.homOfPullbackEq _ _ hK₂' =
      IdealSheaf.homOfPullbackEq ⇑j₀ j₀.contMDiff rfl ≫ₖ
        (IdealSheaf.homOfPullbackEq ⇑g g.contMDiff hI ≫ₖ T.restrictedIdealHom W₂') :=
    ((IdealSheaf.homOfPullbackEq_comp_of_comp_eq (g.comp j₀) j₂ _ rfl hKc rfl hK₂').symm.trans
      (congrArg (fun k => k ≫ₖ T.restrictedIdealHom W₂') s5c)).trans (Category.assoc _ _ _)
  -- the shear's morphism identity, with the category instance fixed
  have hmor' : (IdealSheaf.homOfPullbackEq ⇑g g.contMDiff hI ≫ₖ T.restrictedIdealHom W₂') ≫ₖ
        T.embInv =
      S.restrictedIdealHom W₁' ≫ₖ S.embInv := hmor
  -- assemble
  have hL := CategoryTheory.comp_leg_eq (𝒞 := KLocallyRingedSpace.{u} 𝕜) _ _ _ _ _ s1₁ _ _ s2₁ _ _
    s3₁ _ s4₁ _ _ s5₁
  have hR := CategoryTheory.comp_leg_eq (𝒞 := KLocallyRingedSpace.{u} 𝕜) _ _ _ _ _ s1₂ _ _ s2₂ _ _
    s3₂ _ s4₂ _ _ s5₂
  exact hL.trans ((congrArg (fun k => IdealSheaf.homOfPullbackEq ⇑j₀ j₀.contMDiff rfl ≫ₖ k ≫ₖ
      ofRestrict X.toKLocallyRingedSpace (openOf X O'))
    hmor'.symm).trans hR.symm)

end OverX

end Hironaka.Manifold

end
