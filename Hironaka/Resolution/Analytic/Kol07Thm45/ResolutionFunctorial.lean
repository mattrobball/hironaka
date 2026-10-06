/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.RestrictIsoOpen
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueProof
public import Hironaka.Resolution.Analytic.Kol07Thm45.Resolution
public import Hironaka.AnalyticSpace.Resolution.Defs
import Hironaka.AnalyticSpace.ChartLift
import Hironaka.AnalyticSpace.Exhaustion
import Hironaka.AnalyticSpace.Glue.GlueIsoOver
import Hironaka.AnalyticSpace.Glue.Normalize
import Hironaka.AnalyticSpace.RestrictOverLemmas
import Hironaka.AnalyticSpace.SigmaLemmas
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalModel
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionIndependent
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueIndep
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceTransition
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Functoriality of the resolution for isomorphisms of open subspaces

Kollár's resolution functor commutes with smooth morphisms [Kol07, Theorem 45(5)], through the
functoriality half of the proof of Theorem 36 (transport the local embedding along the
isomorphism, then the canonical isomorphism) [Kol07, Theorem 36, proof]; Włodarczyk's canonical
desingularization is functorial with respect to local analytic isomorphisms
[Wlo09, Theorem 2.0.1(3)] (the gluing commutes with them, [Wlo09, §4, (3)⇒(4)]). An isomorphism
`φ : X|U ≅ Y|V` of open subspaces of reduced spaces lifts to an isomorphism
`ψ : R(X)|Π_X⁻¹U ≅ R(Y)|Π_Y⁻¹V` with `Π_Y|V ∘ ψ = φ ∘ Π_X|U` — clause (5) of
`exists_functorial_resolution` (`ResolutionAssembly.lean`).

**The argument (untwisted over `X`).** `R(Y)|Π_Y⁻¹V` is viewed as a space over `X` through
`Π_Y|V ≫ φ⁻¹ ≫ (X|U → X)` (`resolutionOverMap`), so that the gluing of local isomorphisms over `X`,
`exists_isIso_over_of_cover`, glues LOCAL isomorphisms on a cover of `U`
(`exists_localIsoOver_resolution`) with UNIQUENESS from the triviality of the automorphisms of
`R(X)` over `X` (`resolution_isoOver_eq_id`; `LocalModel.lean`). The local isomorphism at `x ∈ U`:
a piece embedding `F'` of `Y` near `φ x` over an open `O' ⊆ V`, the restriction `φ' := φ|O'`, the
transported embedding `F'ᵗ := F'.transportAlongIso φ'`, ONE ambient open `W`; the local models
(`exists_localModel`) of `R(X)` at `F'ᵗ` and of `R(Y)` at `F'` are parts of the SAME local
resolution (same ambient, same ideal), whose maps to `X` and to `Y` differ by `φ'`
(`comp_localResolutionToPiece_transportAlongIso`); `Q := φ(P)` makes the two parts the same open
(`toFun_restrictIsoTo_mem_imageOpen_iff`,
`Hironaka/Resolution/Analytic/Kol07Thm45/RestrictIsoOpen.lean`). The independence of the local
resolution enters for `X` and for `Y` (`hind`, `hindY`).

**Uniqueness of the lift** (`resolution_lift_unique`). Two lifts `ψ, ψ'` of the same `φ` differ
by the automorphism `ψ ≫ ψ'⁻¹` of `R(X)|Π_X⁻¹U`, which lies over `X|U` (cancel the isomorphism
`φ`), hence is the identity by `resolution_isoOver_eq_id`. So the lift is unique, and the lifts
respect identities and composition
(`ResolutionAssignment.LiftsLocalIsomorphisms.lift_id_restrictSet`,
`ResolutionAssignment.LiftsLocalIsomorphisms.lift_comp_restrictSet`, which use only the uniqueness
in the statement).

Not in the sources beyond the statements cited; bookkeeping.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace KLocallyRingedSpace

universe u w

namespace CategoryTheory

variable {C : Type*} [Category C]

/-- **The twist algebra of the local isomorphism**, in any category: the
Y-side local model `sY`, the identification `βinv` of the part of `R(Y)|V` over `P` (through `φ⁻¹`)
with the part of `R(Y)` over `φ(P)`, and the structure maps related by `Π_{F'ᵗ} ≫ φ' = Π_{F'}` and
`φ' ≫ (Y|O' → Y|V) = (X|φ⁻¹O' → X|U) ≫ φ` give: the part of the common local resolution over the
X-open, mapped to `X`, is the composite `inv sY ≫ βinv` followed by the view over `X` through
`φ⁻¹` — the inverse of `φ` is cancelled after the monomorphism `Y|V → Y`. -/
theorem twist_over_eq {A' Bp Bf YV Y A'' F L YO XO XU X : C}
    (βinv : A' ⟶ Bp) (κB : Bp ⟶ Bf) (rst : Bf ⟶ YV) (ofV : YV ⟶ Y) (ofB : Bf ⟶ A'')
    (dY : A'' ⟶ Y) (κ : A' ⟶ A'') (sY : A' ⟶ F) [IsIso sY] (ρ' : F ⟶ L) (pF : L ⟶ YO)
    (ofO : YO ⟶ Y) (pFt : L ⟶ XO) (φ' : XO ⟶ YO) (inclY : YO ⟶ YV) (inclX : XO ⟶ XU)
    (φ : XU ⟶ YV) [IsIso φ] (ofOx : XO ⟶ X) (ofU : XU ⟶ X)
    (hcancel : ∀ {Z : C} (f g : Z ⟶ YV), f ≫ ofV = g ≫ ofV → f = g)
    (h9 : rst ≫ ofV = ofB ≫ dY) (h4 : βinv ≫ κB ≫ ofB = κ)
    (h3 : κ ≫ dY = (sY ≫ ρ') ≫ pF ≫ ofO) (h6 : pFt ≫ φ' = pF)
    (h8Y : inclY ≫ ofV = ofO) (h7 : φ' ≫ inclY = inclX ≫ φ) (h8X : inclX ≫ ofU = ofOx) :
    ρ' ≫ pFt ≫ ofOx = ((inv sY ≫ βinv) ≫ κB) ≫ rst ≫ inv φ ≫ ofU := by
  have hstar : βinv ≫ κB ≫ rst = sY ≫ ρ' ≫ pFt ≫ inclX ≫ φ := by
    apply hcancel
    calc (βinv ≫ κB ≫ rst) ≫ ofV = βinv ≫ κB ≫ ofB ≫ dY := by
          simp only [Category.assoc, h9]
      _ = κ ≫ dY := by rw [← h4]; simp only [Category.assoc]
      _ = sY ≫ ρ' ≫ pFt ≫ φ' ≫ inclY ≫ ofV := by
          rw [h3, ← h6, h8Y]; simp only [Category.assoc]
      _ = (sY ≫ ρ' ≫ pFt ≫ inclX ≫ φ) ≫ ofV := by
          rw [← Category.assoc φ' inclY, h7]; simp only [Category.assoc]
  have hstar2 : (inv sY ≫ βinv ≫ κB ≫ rst) ≫ inv φ = ρ' ≫ pFt ≫ inclX := by
    rw [hstar, IsIso.inv_hom_id_assoc]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  calc ρ' ≫ pFt ≫ ofOx = (ρ' ≫ pFt ≫ inclX) ≫ ofU := by rw [← h8X]; simp only [Category.assoc]
    _ = ((inv sY ≫ βinv ≫ κB ≫ rst) ≫ inv φ) ≫ ofU := by rw [hstar2]
    _ = ((inv sY ≫ βinv) ≫ κB) ≫ rst ≫ inv φ ≫ ofU := by simp only [Category.assoc]

/-- **The final square**, in any category: the glued isomorphism `s` over `X` between the parts
over `U` (read through the identifications `h1`, `h2 ≫ ofBt` of the parts with the restrictions),
followed by `Π_Y|V`, is `Π_X|U` followed by `φ` — after cancelling `φ⁻¹` and the monomorphism
`X|U → X`. -/
theorem final_square_eq {Ar Ac A Bc Bt B X XU YV : C} (h1 : Ar ⟶ Ac) (ofAc : Ac ⟶ A)
    (ofAr : Ar ⟶ A) (hh1 : h1 ≫ ofAc = ofAr) (s : Ac ⟶ Bc) (h2 : Bc ⟶ Bt) (ofBt : Bt ⟶ B)
    (ofBc : Bc ⟶ B) (hh2 : h2 ≫ ofBt = ofBc) (pX : A ⟶ X) (rX : Ar ⟶ XU) (ofU : XU ⟶ X)
    (hrX : rX ≫ ofU = ofAr ≫ pX) (rY : B ⟶ YV) (φ : XU ⟶ YV) [IsIso φ]
    (hs : ofAc ≫ pX = (s ≫ ofBc) ≫ rY ≫ inv φ ≫ ofU)
    (hcancel : ∀ {Z : C} (f g : Z ⟶ XU), f ≫ ofU = g ≫ ofU → f = g) :
    (h1 ≫ s ≫ h2 ≫ ofBt) ≫ rY = rX ≫ φ := by
  have key : (h1 ≫ s ≫ h2 ≫ ofBt) ≫ rY ≫ inv φ = rX := by
    apply hcancel
    calc ((h1 ≫ s ≫ h2 ≫ ofBt) ≫ rY ≫ inv φ) ≫ ofU
        = h1 ≫ (s ≫ ofBc) ≫ rY ≫ inv φ ≫ ofU := by
          rw [← hh2]; simp only [Category.assoc]
      _ = h1 ≫ ofAc ≫ pX := by rw [hs]
      _ = rX ≫ ofU := by rw [hrX, ← hh1]; simp only [Category.assoc]
  calc (h1 ≫ s ≫ h2 ≫ ofBt) ≫ rY = ((h1 ≫ s ≫ h2 ≫ ofBt) ≫ rY ≫ inv φ) ≫ φ := by
        simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    _ = rX ≫ φ := by rw [key]

/-- **The automorphism `ψ ≫ ψ'⁻¹` lies over the base**, in any category: if `ψ` and `ψ'` both lie
over the monomorphism `φ` (`ψ ≫ r_Y = r ≫ φ`, `ψ' ≫ r_Y = r ≫ φ`), then `(ψ ≫ ψ'⁻¹) ≫ r = r`. -/
theorem comp_inv_over_of_over {A B P Q : C} (ψ ψ' : A ⟶ B) [IsIso ψ'] (r : A ⟶ P) (rY : B ⟶ Q)
    (φ : P ⟶ Q) [Mono φ] (hc : ψ ≫ rY = r ≫ φ) (hc' : ψ' ≫ rY = r ≫ φ) :
    (ψ ≫ inv ψ') ≫ r = r := by
  rw [← cancel_mono φ, Category.assoc, Category.assoc, ← hc', IsIso.inv_hom_id_assoc, hc, hc']

/-- **Conjugating an endomorphism over the base**, in any category: if `α ≫ r = r`,
`r ≫ oX = oA ≫ π` and `e : A ≅ A'` lies over `R` (`e.hom ≫ oA' = oA`, `e.inv ≫ oA = oA'`), then
the conjugate `e.inv ≫ α ≫ e.hom` lies over `X` through `oA' ≫ π`. -/
theorem conj_over_of_over {A A' R X XU : C} (einv : A' ⟶ A) (ehom : A ⟶ A') (α : A ⟶ A)
    (oA' : A' ⟶ R) (oA : A ⟶ R) (π : R ⟶ X) (r : A ⟶ XU) (oX : XU ⟶ X) (h1 : ehom ≫ oA' = oA)
    (h2 : einv ≫ oA = oA') (hα : α ≫ r = r) (hover : r ≫ oX = oA ≫ π) :
    oA' ≫ π = ((einv ≫ α ≫ ehom) ≫ oA') ≫ π := by
  simp only [Category.assoc, reassoc_of% h1]
  rw [← hover, reassoc_of% hα, hover, ← Category.assoc, h2]

/-- An endomorphism whose conjugate by an isomorphism is the identity is the identity. -/
theorem eq_id_of_conj_eq_id {A A' : C} (e : A ≅ A') (α : A ⟶ A)
    (h : e.inv ≫ α ≫ e.hom = 𝟙 _) : α = 𝟙 _ := by
  calc α = e.hom ≫ (e.inv ≫ α ≫ e.hom) ≫ e.inv := by simp
    _ = 𝟙 _ := by rw [h]; simp

/-- Two morphisms `ψ, ψ'` with `ψ ≫ ψ'⁻¹ = 𝟙` are equal. -/
theorem eq_of_comp_inv_eq_id {A B : C} (ψ ψ' : A ⟶ B) [IsIso ψ'] (h : ψ ≫ inv ψ' = 𝟙 A) :
    ψ = ψ' := by
  simpa using congrArg (· ≫ ψ') h

end CategoryTheory

namespace AnalyticSpace

variable {K : Type} [RCLike K] {X Y : AnalyticSpace.{u} K} {U : Set X} {V : Set Y}

/-- The image of the preimage of `S` lies in `S`. -/
theorem Hom.imageOpen_preimageOpen_subset (φ : X.restrictSet U ⟶ Y.restrictSet V) (S : Set Y) :
    Hom.imageOpen φ (Hom.preimageOpen φ S) ⊆ S := by
  rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  obtain ⟨p', hp', hpp⟩ := hp
  exact (Subtype.ext hpp : p' = p) ▸ hp'

/-- The image is monotone. -/
theorem Hom.imageOpen_mono (φ : X.restrictSet U ⟶ Y.restrictSet V) {P P' : Set X} (h : P ⊆ P') :
    Hom.imageOpen φ P ⊆ Hom.imageOpen φ P' := by
  rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  exact ⟨_, ⟨p, h hp, rfl⟩, rfl⟩

/-- **A space over `Y|V` viewed over `X` through `φ⁻¹`**: for `Π : R → Y`, the
part `R|Π⁻¹V` maps to `X` by `Π|V ≫ φ⁻¹ ≫ (X|U → X)`. -/
def Hom.overMap {R : AnalyticSpace.{u} K} (pr : R ⟶ Y) (φ : X.restrictSet U ⟶ Y.restrictSet V)
    (hφ : IsIso φ) :
    (R.restrictSet (KLocallyRingedSpace.Hom.toFun pr ⁻¹' V)).toKLocallyRingedSpace ⟶
      X.toKLocallyRingedSpace :=
  Hom.restrictSetTo pr V ≫
    @inv (KLocallyRingedSpace.{u} K) _ _ _ φ
      ((Hom.isIso_iff_isIso_toKLocallyRingedSpace φ).mp hφ) ≫
    KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X U)

/-- **The part of `R|Π⁻¹V` over `P` through `φ⁻¹` is the part of `R` over
`φ(P)`**: the open immersion `(R|Π⁻¹V)|_{…} → R|Π⁻¹V → R` has range the part of `R` over the image
open `φ(P)`. -/
theorem Hom.range_ofRestrict_comp_overMap {R : AnalyticSpace.{u} K} (pr : R ⟶ Y)
    (φ : X.restrictSet U ⟶ Y.restrictSet V) (hφ : IsIso φ) (hV : IsOpen V) (P : Opens X) :
    Set.range (KLocallyRingedSpace.Hom.toFun
      (KLocallyRingedSpace.ofRestrict _
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (Hom.overMap pr φ hφ),
            KLocallyRingedSpace.Hom.continuous_toFun (Hom.overMap pr φ hφ)⟩ P) ≫
        KLocallyRingedSpace.ofRestrict R.toKLocallyRingedSpace
          (openOf R (KLocallyRingedSpace.Hom.toFun pr ⁻¹' V)))) =
      ((Opens.comap ⟨KLocallyRingedSpace.Hom.toFun pr, KLocallyRingedSpace.Hom.continuous_toFun pr⟩
        ⟨Hom.imageOpen φ P, Hom.isOpen_imageOpen φ hφ P P.isOpen⟩ :
          Opens R.toKLocallyRingedSpace) : Set R.toKLocallyRingedSpace) := by
  have hK : @CategoryTheory.IsIso (KLocallyRingedSpace.{u} K) _ _ _ φ :=
    (Hom.isIso_iff_isIso_toKLocallyRingedSpace φ).mp hφ
  ext r
  constructor
  · rintro ⟨⟨⟨r', hr'⟩, hmem⟩, rfl⟩
    change KLocallyRingedSpace.Hom.toFun pr r' ∈ Hom.imageOpen φ P
    have hz : KLocallyRingedSpace.Hom.toFun φ (KLocallyRingedSpace.Hom.toFun
        (@inv (KLocallyRingedSpace.{u} K) _ _ _ φ hK)
          (KLocallyRingedSpace.Hom.toFun (Hom.restrictSetTo pr V) ⟨r', hr'⟩)) =
        KLocallyRingedSpace.Hom.toFun (Hom.restrictSetTo pr V) ⟨r', hr'⟩ :=
      congrArg (fun k => KLocallyRingedSpace.Hom.toFun k
        (KLocallyRingedSpace.Hom.toFun (Hom.restrictSetTo pr V) ⟨r', hr'⟩))
        (@CategoryTheory.IsIso.inv_hom_id (KLocallyRingedSpace.{u} K) _ _ _ φ hK)
    refine (Hom.mem_imageOpen_iff φ P _).mpr ⟨_, hmem, ?_⟩
    exact (congrArg (fun q => q.1) hz).trans (Hom.toFun_restrictSetTo pr V ⟨r', hr'⟩)
  · intro hr
    obtain ⟨p, hp, hpr⟩ := (Hom.mem_imageOpen_iff φ P _).mp hr
    have hr' : r ∈ openOf R (KLocallyRingedSpace.Hom.toFun pr ⁻¹' V) :=
      (mem_openOf_iff_of_isOpen R (hV.preimage (KLocallyRingedSpace.Hom.continuous_toFun pr))
        r).mpr ((congrArg (· ∈ V) hpr).mp
          ((mem_openOf_iff_of_isOpen Y hV _).mp (KLocallyRingedSpace.Hom.toFun φ p).2))
    refine ⟨⟨⟨r, hr'⟩, ?_⟩, rfl⟩
    have hz : KLocallyRingedSpace.Hom.toFun (Hom.restrictSetTo pr V) ⟨r, hr'⟩ =
        KLocallyRingedSpace.Hom.toFun φ p :=
      Subtype.ext ((Hom.toFun_restrictSetTo pr V ⟨r, hr'⟩).trans hpr.symm)
    have hp' : KLocallyRingedSpace.Hom.toFun (@inv (KLocallyRingedSpace.{u} K) _ _ _ φ hK)
        (KLocallyRingedSpace.Hom.toFun φ p) = p :=
      congrArg (fun k => KLocallyRingedSpace.Hom.toFun k p)
        (@CategoryTheory.IsIso.hom_inv_id (KLocallyRingedSpace.{u} K) _ _ _ φ hK)
    exact (congrArg (fun z => (KLocallyRingedSpace.Hom.toFun
      (@inv (KLocallyRingedSpace.{u} K) _ _ _ φ hK) z).1 ∈ P) hz).mpr
      ((congrArg (fun q => q.1 ∈ P) hp').mpr hp)

end AnalyticSpace

namespace Hironaka.Manifold.BEDanFamStar

variable {𝕜 : Type} [RCLike 𝕜] (bed : BEDanFamStar.{u} 𝕜)

/-- **The part of `R(Y)` over `V`, viewed over `X` through `φ⁻¹`**: `Π_Y|V` followed by the
inverse of `φ : X|U ≅ Y|V` and the open immersion `X|U → X`. -/
def resolutionOverMap {X Y : AnalyticSpace.{u} 𝕜} (U : Set X) (V : Set Y)
    (φ : X.restrictSet U ⟶ Y.restrictSet V) (hφ : IsIso φ) :
    ((bed.resolution Y).restrictSet (bed.resolutionMap Y ⁻¹' V)).toKLocallyRingedSpace ⟶
      X.toKLocallyRingedSpace :=
  ((bed.resolutionMap Y).restrictSet V :
      ((bed.resolution Y).restrictSet (bed.resolutionMap Y ⁻¹' V)).toKLocallyRingedSpace ⟶
        (Y.restrictSet V).toKLocallyRingedSpace) ≫
    @inv (KLocallyRingedSpace.{u} 𝕜) _ _ _
      (φ : (X.restrictSet U).toKLocallyRingedSpace ⟶ (Y.restrictSet V).toKLocallyRingedSpace)
      ((Hom.isIso_iff_isIso_toKLocallyRingedSpace φ).mp hφ) ≫
    ofRestrict X.toKLocallyRingedSpace (openOf X U)

/-- Unfolding lemma: the view over `X` is the generic `Hom.overMap` at `Π_Y`. -/
theorem resolutionOverMap_eq_overMap {X Y : AnalyticSpace.{u} 𝕜} (U : Set X)
    (V : Set Y) (φ : X.restrictSet U ⟶ Y.restrictSet V)
        (hφ : IsIso φ) :
    bed.resolutionOverMap U V φ hφ =
      Hom.overMap (R := bed.resolution Y) (bed.resolutionMap Y)
        φ hφ :=
  rfl

/-- **The local isomorphism over `φ`**, on the gluings: at every `x ∈ U` a small open `P ∋ x`,
`P ⊆ U`, and an isomorphism over `X` from the part of the glued space of `X` over `P` to the part
of the glued space of `Y` over `V` (viewed over `X` through `φ⁻¹`) over `P` — the local models
(`exists_localModel`, `LocalModel.lean`) of both sides at the same local resolution (`F'` of `Y`
near `φ x` over
`O' ⊆ V`, transported along `φ' := φ|O'` to `X`), identified through
`Π_{F'ᵗ} ≫ φ' = Π_{F'}` (`comp_localResolutionToPiece_transportAlongIso`) at `Q := φ(P)`, and the
part of `R(Y)|V` over `P` read as the part of `R(Y)` over `Q` (`range_ofRestrict_comp_overMap`). -/
theorem ExhaustionGluing.exists_localIsoOver {X Y : AnalyticSpace.{u} 𝕜}
    (Ξ : bed.ExhaustionGluing X) (Ξ' : bed.ExhaustionGluing Y) (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) (hindY : LocalResolutionIndependentOn Y bed)
    (U : Set X) (V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (φ : X.restrictSet U ⟶ Y.restrictSet V) (hφ : IsIso φ)
        (x : X)
    (hx : x ∈ U) :
    ∃ (P : Opens X) (_ : x ∈ P) (_ : (P : Set X) ⊆ U),
      ∃ s : Ξ.glue.gluedOver.toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun Ξ.glue.descMap,
                Hom.continuous_toFun Ξ.glue.descMap⟩ P) ⟶
          (Ξ'.glue.gluedOver.restrictSet
              (KLocallyRingedSpace.Hom.toFun Ξ'.glue.descMap ⁻¹'
                  V)).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (Hom.overMap
                (R := Ξ'.glue.gluedOver) Ξ'.glue.descMap φ hφ),
              Hom.continuous_toFun _⟩ P),
        IsIso s ∧
          ofRestrict _ _ ≫ Ξ.glue.descMap =
            (s ≫ ofRestrict _ _) ≫ Hom.overMap
              (R := Ξ'.glue.gluedOver) Ξ'.glue.descMap φ hφ := by
  have hK : @CategoryTheory.IsIso (KLocallyRingedSpace.{u} 𝕜) _ _ _ φ :=
    (Hom.isIso_iff_isIso_toKLocallyRingedSpace φ).mp hφ
  have hxU' : x ∈ openOf X U :=
    (mem_openOf_iff_of_isOpen X hU x).mpr hx
  obtain ⟨y, hy⟩ : ∃ y : Y.restrictSet V, y = KLocallyRingedSpace.Hom.toFun φ ⟨x, hxU'⟩ := ⟨_, rfl⟩
  have hyV : y.1 ∈ V :=
    (mem_openOf_iff_of_isOpen Y hV _).mp y.2
  -- a piece embedding `F'` of `Y` near `y`, over the open `O' := piece j ∩ V ⊆ V`
  obtain ⟨m, hym⟩ : ∃ m, y.1 ∈ Ξ'.U m :=
    Set.mem_iUnion.mp ((Set.ext_iff.mp Ξ'.iUnion_U y.1).mpr (Set.mem_univ _))
  obtain ⟨j, hyj⟩ : ∃ j, y.1 ∈ (Ξ'.D m).inner j :=
    Set.mem_iUnion.mp ((Ξ'.D m).subset_iUnion_inner hym)
  obtain ⟨O', hO'def⟩ : ∃ O' : Set Y, O' = (Ξ'.D m).piece j ∩ V := ⟨_, rfl⟩
  have hO' : IsOpen O' := hO'def ▸ ((Ξ'.D m).isOpen_piece j).inter hV
  have hO'V : O' ⊆ V := hO'def ▸ Set.inter_subset_right
  have hyO' : y.1 ∈ O' :=
    hO'def ▸ ⟨(Ξ'.D m).closure_inner_subset j (subset_closure hyj), hyV⟩
  obtain ⟨F', -⟩ : ∃ F' : PieceEmbedding 𝕜 (Ξ'.D m).n Y O',
      F' = ((Ξ'.D m).embedding j).restrictPiece hO' (hO'def ▸ Set.inter_subset_left) := ⟨_, rfl⟩
  have hyO'' : y.1 ∈ openOf Y O' :=
    (mem_openOf_iff_of_isOpen Y hO' _).mpr hyO'
  -- one ambient open `W` with compact closure around the ambient point of `y`
  have : LocallyCompactSpace (pieceAmbient.{u} 𝕜 F'.G) :=
    ChartedSpace.locallyCompactSpace (H := Fin (Ξ'.D m).n → 𝕜) (M := pieceAmbient.{u} 𝕜 F'.G)
  obtain ⟨W, hptW, hW⟩ := exists_opens_isCompact_closure_superset
    (isCompact_singleton (x := F'.ambientPoint ⟨y.1, hyO''⟩))
  have hyW : y.1 ∈ F'.domOpens W := ⟨⟨y.1, hyO''⟩, hptW (Set.mem_singleton _), rfl⟩
  -- `φ' := φ|O'` and the transported embedding `F'ᵗ` over `Oₓ := φ⁻¹O'`
  have hOₓ : IsOpen (Hom.preimageOpen φ O') :=
    Hom.isOpen_preimageOpen φ O' hO'
  have hOₓU : Hom.preimageOpen φ O' ⊆ U :=
    Hom.preimageOpen_subset φ hU O'
  let φ' : X.restrictSet (Hom.preimageOpen φ O') ⟶ Y.restrictSet O' :=
    Hom.restrictIsoTo φ hU O' hO'
  have hφ'K : @CategoryTheory.IsIso (KLocallyRingedSpace.{u} 𝕜) _ _ _ φ' :=
    Hom.isIso_restrictIsoTo φ hφ hU O' hO' hO'V
  have hφ'iso : IsIso φ' :=
    (Hom.isIso_iff_isIso_toKLocallyRingedSpace φ').mpr hφ'K
  let Ft : PieceEmbedding 𝕜 (Ξ'.D m).n X (Hom.preimageOpen φ O') :=
    F'.transportAlongIso φ' hφ'iso
  have hxOₓ : x ∈ Hom.preimageOpen φ O' :=
    (Hom.mem_preimageOpen_iff φ O' x).mpr
      ⟨⟨x, hxU'⟩, rfl, hy ▸ hyO'⟩
  have hxOₓ' : x ∈ openOf X
      (Hom.preimageOpen φ O') :=
    (mem_openOf_iff_of_isOpen X hOₓ x).mpr hxOₓ
  have hincl : KLocallyRingedSpace.Hom.toFun (restrictSetIncl X
      hOₓ hOₓU) ⟨x, hxOₓ'⟩ = ⟨x, hxU'⟩ :=
    Subtype.ext (toFun_restrictSetIncl X hOₓ hOₓU ⟨x, hxOₓ'⟩)
  have hφ'x : KLocallyRingedSpace.Hom.toFun φ' ⟨x, hxOₓ'⟩ = ⟨y.1, hyO''⟩ :=
    Subtype.ext ((Hom.toFun_restrictIsoTo φ hU O' hO'
      ⟨x, hxOₓ'⟩).trans ((congrArg (fun q => (KLocallyRingedSpace.Hom.toFun φ q).1) hincl).trans
        (congrArg Subtype.val hy).symm))
  have hxdom : x ∈ Ft.domOpens W := by
    refine ⟨⟨x, hxOₓ'⟩, ?_, rfl⟩
    change KLocallyRingedSpace.Hom.toFun φ' ⟨x, hxOₓ'⟩ ∈ F'.embPreimage W
    rw [hφ'x]
    exact hptW (Set.mem_singleton _)
  -- the two local models, at the same local resolution
  obtain ⟨P₁, hxP₁, hP₁, sX, hsX, hsXc⟩ :=
    ExhaustionGluing.exists_localModel bed X Ξ hbed hind Ft hOₓ W hW x hxdom
  obtain ⟨Q₁, hyQ₁, hQ₁, sY, hsY, hsYc⟩ :=
    ExhaustionGluing.exists_localModel bed Y Ξ' hbed hindY F' hO' W hW y.1 hyW
  -- shrink to `P := P₁ ⊓ φ⁻¹Q₁`, and `Q := φ(P) ≤ Q₁`
  obtain ⟨P, hPdef⟩ : ∃ P : Opens X,
      P = P₁ ⊓ ⟨Hom.preimageOpen φ (Q₁ : Set Y),
        Hom.isOpen_preimageOpen φ (Q₁ : Set Y) Q₁.isOpen⟩ :=
    ⟨_, rfl⟩
  have hPP₁ : P ≤ P₁ := hPdef ▸ inf_le_left
  have hPpre : (P : Set X) ⊆ Hom.preimageOpen φ (Q₁ : Set Y) :=
    fun z hz => ((Opens.mem_inf).mp (hPdef ▸ hz)).2
  have hxP : x ∈ P := hPdef ▸ (Opens.mem_inf).mpr ⟨hxP₁,
    (Hom.mem_preimageOpen_iff φ (Q₁ : Set Y) x).mpr
      ⟨⟨x, hxU'⟩, rfl, hy ▸ hyQ₁⟩⟩
  have hdomOₓ : (Ft.domOpens W : Set X) ⊆
      Hom.preimageOpen φ O' := by
    rintro _ ⟨q, -, rfl⟩
    exact (mem_openOf_iff_of_isOpen X hOₓ _).mp q.2
  have hPU : (P : Set X) ⊆ U := fun z hz => hOₓU (hdomOₓ (hP₁ (hPP₁ hz)))
  obtain ⟨Q, hQdef⟩ : ∃ Q : Opens Y,
      Q = ⟨Hom.imageOpen φ (P : Set X),
        Hom.isOpen_imageOpen φ hφ (P : Set X) P.isOpen⟩ :=
    ⟨_, rfl⟩
  have hQQ₁ : Q ≤ Q₁ := fun z hz =>
    Hom.imageOpen_preimageOpen_subset φ (Q₁ : Set Y)
      (Hom.imageOpen_mono φ hPpre
        ((congrArg (fun O : Opens Y => z ∈ O) hQdef).mp hz))
  -- the restricted local models
  have := hsX
  have := hsY
  have hsX'c := restrictOver_over Ξ.glue.descMap (Ft.toSpaceMap bed W hW) hPP₁ sX hsXc
  have hsY'c := restrictOver_over Ξ'.glue.descMap (F'.toSpaceMap bed W hW) hQQ₁ sY hsYc
  have hsX' : IsIso (restrictOver Ξ.glue.descMap (Ft.toSpaceMap bed W hW) hPP₁ sX hsXc) :=
    isIso_restrictOver _ _ hPP₁ sX hsXc
  have hsY' : IsIso (restrictOver Ξ'.glue.descMap (F'.toSpaceMap bed W hW) hQQ₁ sY hsYc) :=
    isIso_restrictOver _ _ hQQ₁ sY hsYc
  -- the two parts of the common local resolution are the same open (the twist): the
  -- Y-side maps read on `F'ᵗ`'s local resolution (the SAME space: same ambient, same ideal)
  let tF' : (Ft.localResolution bed W hW).toKLocallyRingedSpace ⟶ Y.toKLocallyRingedSpace :=
    F'.toSpaceMap bed W hW
  let pF : (Ft.localResolution bed W hW).toKLocallyRingedSpace ⟶
      (Y.restrictSet O').toKLocallyRingedSpace :=
    F'.localResolutionToPiece bed W hW
  have hset : ((Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (Ft.toSpaceMap bed W hW),
        Hom.continuous_toFun (Ft.toSpaceMap bed W hW)⟩ P :
        Opens (Ft.localResolution bed W hW).toKLocallyRingedSpace) :
        Set (Ft.localResolution bed W hW).toKLocallyRingedSpace) =
      ((Opens.comap ⟨KLocallyRingedSpace.Hom.toFun tF', Hom.continuous_toFun tF'⟩ Q :
        Opens (Ft.localResolution bed W hW).toKLocallyRingedSpace) :
        Set (Ft.localResolution bed W hW).toKLocallyRingedSpace) := by
    ext r
    change (KLocallyRingedSpace.Hom.toFun (Ft.localResolutionToPiece bed W hW) r).1 ∈ P ↔
        (KLocallyRingedSpace.Hom.toFun pF r).1 ∈ Q
    have hPi : KLocallyRingedSpace.Hom.toFun pF r =
        KLocallyRingedSpace.Hom.toFun φ' (KLocallyRingedSpace.Hom.toFun
            (Ft.localResolutionToPiece bed W hW) r) :=
      (congrArg (fun k => k r)
        (PieceEmbedding.comp_localResolutionToPiece_transportAlongIso φ' hφ'iso F' bed W hW)).symm
    rw [hPi, hQdef]
    exact (Hom.toFun_restrictIsoTo_mem_imageOpen_iff φ hφ hU O'
      hO' (P : Set X) _).symm
  -- the part of `R(Y)|V` over `P` through `φ⁻¹` is the part of `R(Y)` over `Q`
  have hβ : Set.range (KLocallyRingedSpace.Hom.toFun (ofRestrict _ (Opens.comap
      ⟨KLocallyRingedSpace.Hom.toFun
        (Hom.overMap (R := Ξ'.glue.gluedOver) Ξ'.glue.descMap φ hφ),
        Hom.continuous_toFun _⟩ P) ≫
      ofRestrict Ξ'.glue.gluedOver.toKLocallyRingedSpace (openOf _
        (KLocallyRingedSpace.Hom.toFun Ξ'.glue.descMap ⁻¹' V)))) =
      Set.range (KLocallyRingedSpace.Hom.toFun (ofRestrict Ξ'.glue.gluedOver.toKLocallyRingedSpace
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun Ξ'.glue.descMap,
            Hom.continuous_toFun Ξ'.glue.descMap⟩ Q))) :=
    (Hom.range_ofRestrict_comp_overMap (R := Ξ'.glue.gluedOver)
      Ξ'.glue.descMap φ hφ hV P).trans (by rw [hQdef]; exact (range_toFun_ofRestrict _ _).symm)
  have hinst := isOpenImmersion_ofRestrict_comp_ofRestrict
    (X := Ξ'.glue.gluedOver.toKLocallyRingedSpace)
    (openOf _ (KLocallyRingedSpace.Hom.toFun Ξ'.glue.descMap ⁻¹' V))
    (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
      (Hom.overMap (R := Ξ'.glue.gluedOver) Ξ'.glue.descMap φ hφ),
      Hom.continuous_toFun _⟩ P)
  obtain ⟨β, hβinv⟩ : ∃ β : (Ξ'.glue.gluedOver.restrictSet
        (KLocallyRingedSpace.Hom.toFun Ξ'.glue.descMap ⁻¹' V)).toKLocallyRingedSpace.restrictOpen
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (Hom.overMap
            (R := Ξ'.glue.gluedOver) Ξ'.glue.descMap φ hφ), Hom.continuous_toFun _⟩ P) ≅
      Ξ'.glue.gluedOver.toKLocallyRingedSpace.restrictOpen
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun Ξ'.glue.descMap,
            Hom.continuous_toFun Ξ'.glue.descMap⟩ Q),
      β.inv ≫ ofRestrict _ _ ≫ ofRestrict Ξ'.glue.gluedOver.toKLocallyRingedSpace
        (openOf _ (KLocallyRingedSpace.Hom.toFun Ξ'.glue.descMap ⁻¹' V)) =
        ofRestrict _ _ :=
    ⟨@isoOfRangeEq _ _ _ _ _ _ _ hinst inferInstance hβ,
      @Glue.isoOfRangeEq_inv_comp _ _ _ _ _ _ _ hinst inferInstance hβ⟩
  -- the local isomorphism over `X`
  refine ⟨P, hxP, hPU, restrictOver Ξ.glue.descMap (Ft.toSpaceMap bed W hW) hPP₁ sX hsXc ≫
    (restrictOpenIsoOfSetEq hset).hom ≫
    (@inv _ _ _ _ (restrictOver Ξ'.glue.descMap (F'.toSpaceMap bed W hW) hQQ₁ sY hsYc) hsY' ≫
      β.inv), ?_, ?_⟩
  · exact @IsIso.comp_isIso _ _ _ _ _ _ _ hsX' (@IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _)
      (@IsIso.comp_isIso _ _ _ _ _ _ _ (@IsIso.inv_isIso _ _ _ _ _ hsY') (Iso.isIso_inv _)))
  · have := hsY'
    refine over_comp₃ _ _ _ _ _ _ _ _ _ _ _ hsX'c
      (congrArg (fun k => k ≫ Ft.toSpaceMap bed W hW) (restrictOpenIsoOfSetEq_hom_comp hset)).symm
      ?_
    have hK' : @CategoryTheory.IsIso (KLocallyRingedSpace.{u} 𝕜) _
        (X.toKLocallyRingedSpace.restrictOpen (openOf X U))
        (Y.toKLocallyRingedSpace.restrictOpen (openOf Y V)) φ := hK
    exact twist_over_eq β.inv _ _ (ofRestrict Y.toKLocallyRingedSpace
      (openOf Y V)) _ Ξ'.glue.descMap _
      (restrictOver Ξ'.glue.descMap (F'.toSpaceMap bed W hW) hQQ₁ sY hsYc) _
      pF _ (Ft.localResolutionToPiece bed W hW) φ'
      (restrictSetIncl Y hO' hO'V)
      (restrictSetIncl X hOₓ hOₓU) φ _ _
      (fun f g h => Hom.ext_of_comp_ofRestrict h)
      (Hom.restrictSetTo_comp_ofRestrict Ξ'.glue.descMap V) hβinv
      hsY'c (PieceEmbedding.comp_localResolutionToPiece_transportAlongIso φ' hφ'iso F' bed W hW)
      (restrictSetIncl_comp_ofRestrict Y hO' hO'V)
      (Hom.restrictIsoTo_comp_restrictSetIncl φ hU O' hO' hO'V)
      (restrictSetIncl_comp_ofRestrict X hOₓ hOₓU)

/-- **`R(X)` has no non-trivial automorphism over `X` on any part** (`X` reduced, under `hbed` and
the independence `hind`) — `ExhaustionGluing.isoOver_eq_id` (`LocalModel.lean`) on the resolution
(`resolutionPair_eq_of_glues`). -/
theorem resolution_isoOver_eq_id (hbed : bed.IsEmbeddedDesing)
    {X : AnalyticSpace.{u} 𝕜}
    (hX : X.IsReduced) (hind : LocalResolutionIndependentOn X bed) (O : Opens X)
    (t : (bed.resolution X).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (bed.resolutionMap X),
            Hom.continuous_toFun (bed.resolutionMap X)⟩ O) ⟶
        (bed.resolution X).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (bed.resolutionMap X),
            Hom.continuous_toFun (bed.resolutionMap X)⟩ O))
    (ht : IsIso t)
    (hc : ofRestrict _ _ ≫ bed.resolutionMap X = (t ≫ ofRestrict _ _) ≫ bed.resolutionMap X) :
    t = 𝟙 _ := by
  have h := resolutionGlues_of_isEmbeddedDesing_of_independent X hX bed hbed hind
  revert t
  suffices key : ∀ p : Σ R :
      AnalyticSpace.{u} 𝕜, (R ⟶ X),
      p = bed.resolutionPair X →
      ∀ t : p.1.toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun p.2, Hom.continuous_toFun p.2⟩ O) ⟶
          p.1.toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun p.2, Hom.continuous_toFun p.2⟩ O),
        IsIso t → ofRestrict _ _ ≫ p.2 = (t ≫ ofRestrict _ _) ≫ p.2 → t = 𝟙 _ from key _ rfl
  intro p hp
  rw [bed.resolutionPair_eq_of_glues X hX h] at hp
  subst hp
  exact ExhaustionGluing.isoOver_eq_id bed X h.some hbed hind O

/-- **The lift of an isomorphism of open subspaces is unique** (`X` reduced, under `hbed` and the
independence `hind`): two isomorphisms `ψ, ψ' : R(X)|Π_X⁻¹U ≅ R(Y)|Π_Y⁻¹V` over the same
isomorphism `φ : X|U ≅ Y|V` are equal — `ψ ≫ ψ'⁻¹` is an automorphism of `R(X)|Π_X⁻¹U` over
`X|U` (`comp_inv_over_of_over`), read on the part over `U` in the `Opens.comap` spelling, hence the
identity (`resolution_isoOver_eq_id`). -/
theorem resolution_lift_unique (hbed : bed.IsEmbeddedDesing) {X Y : AnalyticSpace.{u} 𝕜}
    (hX : X.IsReduced) (hind : LocalResolutionIndependentOn X bed) (U : Set X) (V : Set Y)
    (hU : IsOpen U)
    (φ : X.restrictSet U ⟶ Y.restrictSet V) (hφ : IsIso φ)
    (ψ ψ' : (bed.resolution X).restrictSet (bed.resolutionMap X ⁻¹' U) ⟶
        (bed.resolution Y).restrictSet (bed.resolutionMap Y ⁻¹' V))
    (hψ : IsIso ψ) (hψ' : IsIso ψ')
    (hc : ψ ≫ (bed.resolutionMap Y).restrictSet V = (bed.resolutionMap X).restrictSet U ≫ φ)
    (hc' : ψ' ≫ (bed.resolutionMap Y).restrictSet V = (bed.resolutionMap X).restrictSet U ≫ φ) :
    ψ = ψ' := by
  have hφK : @IsIso (KLocallyRingedSpace.{u} 𝕜) _ _ _ φ :=
    (Hom.isIso_iff_isIso_toKLocallyRingedSpace φ).mp hφ
  have hψK : @IsIso (KLocallyRingedSpace.{u} 𝕜) _ _ _ ψ :=
    (Hom.isIso_iff_isIso_toKLocallyRingedSpace ψ).mp hψ
  have hψ'K : @IsIso (KLocallyRingedSpace.{u} 𝕜) _ _ _ ψ' :=
    (Hom.isIso_iff_isIso_toKLocallyRingedSpace ψ').mp hψ'
  -- `ψ ≫ ψ'⁻¹` lies over `X|U`
  have hα : (@CategoryStruct.comp (KLocallyRingedSpace.{u} 𝕜) _ _ _ _ ψ
      (@inv (KLocallyRingedSpace.{u} 𝕜) _ _ _ ψ' hψ'K)) ≫
        Hom.restrictSetTo (bed.resolutionMap X) U =
      Hom.restrictSetTo (bed.resolutionMap X) U :=
    @comp_inv_over_of_over (KLocallyRingedSpace.{u} 𝕜) _ _ _ _ _ ψ ψ' hψ'K _ _ φ
      (@IsIso.mono_of_iso (KLocallyRingedSpace.{u} 𝕜) _ _ _ φ hφK) hc hc'
  -- the part of `R(X)` over `U`, in the `Opens.comap` spelling of `resolution_isoOver_eq_id`
  have hset : ((openOf (bed.resolution X)
        (bed.resolutionMap X ⁻¹' U) : Opens (bed.resolution X).toKLocallyRingedSpace) :
        Set (bed.resolution X).toKLocallyRingedSpace) =
      ((Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (bed.resolutionMap X), Hom.continuous_toFun
          (bed.resolutionMap X)⟩
        ⟨U, hU⟩ : Opens (bed.resolution X).toKLocallyRingedSpace) :
        Set (bed.resolution X).toKLocallyRingedSpace) :=
    (congrArg (fun W : Opens (bed.resolution X).toKLocallyRingedSpace =>
        (W : Set (bed.resolution X).toKLocallyRingedSpace))
      (openOf_of_isOpen (bed.resolution X)
        (hU.preimage (Hom.continuous_toFun (bed.resolutionMap X))))).trans
      (Set.ext fun _ => Iff.rfl)
  have hiso : IsIso ((restrictOpenIsoOfSetEq hset).inv ≫
      (@CategoryStruct.comp (KLocallyRingedSpace.{u} 𝕜) _ _ _ _ ψ
        (@inv (KLocallyRingedSpace.{u} 𝕜) _ _ _ ψ' hψ'K)) ≫ (restrictOpenIsoOfSetEq hset).hom) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv _)
      (@IsIso.comp_isIso _ _ _ _ _ _ _ (@IsIso.comp_isIso _ _ _ _ _ _ _ hψK IsIso.inv_isIso)
        (Iso.isIso_hom _))
  have ht := bed.resolution_isoOver_eq_id hbed hX hind ⟨U, hU⟩ _ hiso
    (conj_over_of_over _ _ _ _ _ _ _ _ (restrictOpenIsoOfSetEq_hom_comp hset)
      (restrictOpenIsoOfSetEq_inv_comp hset) hα
      (Hom.restrictSetTo_comp_ofRestrict (bed.resolutionMap X) U))
  exact @eq_of_comp_inv_eq_id (KLocallyRingedSpace.{u} 𝕜) _ _ _ ψ ψ' hψ'K
    (eq_id_of_conj_eq_id (restrictOpenIsoOfSetEq hset) _ ht)

/-- **The local isomorphism over `φ` on the resolutions** (`X`, `Y` reduced, under `hbed` and the
independences `hind`, `hindY`; `φ` an isomorphism of the open subspaces `X|U ≅ Y|V`, `x ∈ U`):
`ExhaustionGluing.exists_localIsoOver` for the chosen gluings of `X` and of `Y`
(`resolutionPair_eq_of_glues`). -/
theorem exists_localIsoOver_resolution (hbed : bed.IsEmbeddedDesing)
    {X Y : AnalyticSpace.{u} 𝕜} (hX : X.IsReduced) (hY : Y.IsReduced)
    (hind : LocalResolutionIndependentOn X bed) (hindY : LocalResolutionIndependentOn Y bed)
    (U : Set X) (V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (φ : X.restrictSet U ⟶ Y.restrictSet V) (hφ : IsIso φ)
        (x : X)
    (hx : x ∈ U) :
    ∃ (P : Opens X) (_ : x ∈ P) (_ : (P : Set X) ⊆ U),
      ∃ s : (bed.resolution X).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (bed.resolutionMap X),
              Hom.continuous_toFun (bed.resolutionMap X)⟩ P) ⟶
          ((bed.resolution Y).restrictSet
              (bed.resolutionMap Y ⁻¹' V)).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (bed.resolutionOverMap U V φ hφ),
              Hom.continuous_toFun (bed.resolutionOverMap U V φ hφ)⟩ P),
        IsIso s ∧
          ofRestrict _ _ ≫ bed.resolutionMap X =
            (s ≫ ofRestrict _ _) ≫ bed.resolutionOverMap U V φ hφ := by
  have h := resolutionGlues_of_isEmbeddedDesing_of_independent X hX bed hbed hind
  have h' := resolutionGlues_of_isEmbeddedDesing_of_independent Y hY bed hbed hindY
  suffices key :
      ∀ (p : Σ R : AnalyticSpace.{u} 𝕜, (R ⟶ X)) (q : Σ R : AnalyticSpace.{u} 𝕜, (R ⟶ Y)),
      p = bed.resolutionPair X → q = bed.resolutionPair Y →
      ∃ (P : Opens X) (_ : x ∈ P) (_ : (P : Set X) ⊆ U),
        ∃ s : p.1.toKLocallyRingedSpace.restrictOpen
              (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun p.2, Hom.continuous_toFun p.2⟩ P) ⟶
            (q.1.restrictSet (KLocallyRingedSpace.Hom.toFun q.2 ⁻¹'
                V)).toKLocallyRingedSpace.restrictOpen
              (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (Hom.overMap (R := q.1) q.2
                  φ hφ), Hom.continuous_toFun _⟩ P),
          IsIso s ∧
            ofRestrict _ _ ≫ p.2 = (s ≫ ofRestrict _ _) ≫
              Hom.overMap (R := q.1) q.2 φ hφ from
    key _ _ rfl rfl
  intro p q hp hq
  rw [bed.resolutionPair_eq_of_glues X hX h] at hp
  rw [bed.resolutionPair_eq_of_glues Y hY h'] at hq
  subst hp
  subst hq
  exact ExhaustionGluing.exists_localIsoOver bed h.some h'.some hbed hind hindY U V hU hV φ hφ x hx

/-- **The functoriality for isomorphisms of open subspaces** (clause (5) of
`exists_functorial_resolution`; [Kol07, Theorem 45(5)] through [Kol07, Theorem 36, proof];
[Wlo09, Theorem 2.0.1(3)]), with the independence of the local resolution for `X` and for `Y` as
the hypotheses `hind`, `hindY`: an isomorphism `φ : X|U ≅ Y|V` of open subspaces of reduced spaces
lifts to an isomorphism `ψ` of the resolutions over `U` and `V` with `Π_Y|V ∘ ψ = φ ∘ Π_X|U` — the
local isomorphisms `exists_localIsoOver_resolution` on a cover of `U`, unique by
`resolution_isoOver_eq_id` and `isoOver_unique_of_aut`, glued by `exists_isIso_over_of_cover` over
`X`, read into the restrictions. -/
theorem resolution_functorial_of_independent (X : AnalyticSpace.{u} 𝕜)
    (hX : X.IsReduced) (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) (Y : AnalyticSpace.{u} 𝕜)
    (hY : Y.IsReduced) (hindY : LocalResolutionIndependentOn Y bed) (U : Set X) (V : Set Y)
    (hU : IsOpen U) (hV : IsOpen V)
    (φ : X.restrictSet U ⟶ Y.restrictSet V) (hφ : IsIso φ) :
    ∃ ψ : (bed.resolution X).restrictSet (bed.resolutionMap X ⁻¹' U) ⟶
        (bed.resolution Y).restrictSet (bed.resolutionMap Y ⁻¹' V),
      IsIso ψ ∧ ψ ≫ (bed.resolutionMap Y).restrictSet V =
        (bed.resolutionMap X).restrictSet U ≫ φ := by
  have hK : @CategoryTheory.IsIso (KLocallyRingedSpace.{u} 𝕜) _ _ _ φ :=
    (Hom.isIso_iff_isIso_toKLocallyRingedSpace φ).mp hφ
  -- the gluing of local isomorphisms over `X` on the cover of `U` by the opens carrying one
  obtain ⟨s, hs, hsc⟩ := exists_isIso_over_of_cover
    (bed.resolutionMap X : (bed.resolution X).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace)
    (bed.resolutionOverMap U V φ hφ) ⟨U, hU⟩
    (fun i : {P : Opens X // (P : Set X) ⊆ U ∧
        ∃ s : (bed.resolution X).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (bed.resolutionMap X),
              Hom.continuous_toFun (bed.resolutionMap X)⟩ P) ⟶
          ((bed.resolution Y).restrictSet
              (bed.resolutionMap Y ⁻¹' V)).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (bed.resolutionOverMap U V φ hφ),
              Hom.continuous_toFun (bed.resolutionOverMap U V φ hφ)⟩ P),
          IsIso s ∧ ofRestrict _ _ ≫ bed.resolutionMap X =
            (s ≫ ofRestrict _ _) ≫ bed.resolutionOverMap U V φ hφ} => i.1)
    (fun i => i.2.1)
    (fun z hz => by
      obtain ⟨P, hzP, hPU, s, hs, hsc⟩ :=
        bed.exists_localIsoOver_resolution hbed hX hY hind hindY U V hU hV φ hφ z hz
      exact ⟨⟨P, hPU, s, hs, hsc⟩, hzP⟩)
    (fun i => i.2.2)
    (fun O' _ s s' hs hs' hc hc' => isoOver_unique_of_aut _ _ O'
      (fun t ht htc => bed.resolution_isoOver_eq_id hbed hX hind O' t ht htc) s s' hs hs' hc hc')
  -- the parts over `U` are the restriction and the whole of `R(Y)|V`
  have hset₁ : ((openOf (bed.resolution X)
        (bed.resolutionMap X ⁻¹' U) : Opens (bed.resolution X).toKLocallyRingedSpace) :
        Set (bed.resolution X).toKLocallyRingedSpace) =
      ((Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (bed.resolutionMap X), Hom.continuous_toFun
          (bed.resolutionMap X)⟩
        ⟨U, hU⟩ : Opens (bed.resolution X).toKLocallyRingedSpace) :
        Set (bed.resolution X).toKLocallyRingedSpace) :=
    (congrArg (fun W : Opens (bed.resolution X).toKLocallyRingedSpace =>
        (W : Set (bed.resolution X).toKLocallyRingedSpace))
      (openOf_of_isOpen (bed.resolution X)
        (hU.preimage (Hom.continuous_toFun (bed.resolutionMap X))))).trans
      (Set.ext fun _ => Iff.rfl)
  have hset₂ : ((Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (bed.resolutionOverMap U V φ hφ),
        Hom.continuous_toFun (bed.resolutionOverMap U V φ hφ)⟩ ⟨U, hU⟩ :
        Opens ((bed.resolution Y).restrictSet
          (bed.resolutionMap Y ⁻¹' V)).toKLocallyRingedSpace) :
        Set ((bed.resolution Y).restrictSet (bed.resolutionMap Y ⁻¹' V)).toKLocallyRingedSpace) =
      ((⊤ : Opens ((bed.resolution Y).restrictSet
          (bed.resolutionMap Y ⁻¹' V)).toKLocallyRingedSpace) :
        Set ((bed.resolution Y).restrictSet (bed.resolutionMap Y ⁻¹' V)).toKLocallyRingedSpace) :=
    Set.eq_univ_of_forall fun b =>
      (mem_openOf_iff_of_isOpen X hU _).mp
        (KLocallyRingedSpace.Hom.toFun
          (@inv (KLocallyRingedSpace.{u} 𝕜) _ _ _ φ hK)
          (KLocallyRingedSpace.Hom.toFun
            (Hom.restrictSetTo (bed.resolutionMap Y) V) b)).2
  have hK' : @CategoryTheory.IsIso (KLocallyRingedSpace.{u} 𝕜) _
      (X.toKLocallyRingedSpace.restrictOpen (openOf X U))
      (Y.toKLocallyRingedSpace.restrictOpen (openOf Y V)) φ := hK
  have hKψ : IsIso (C := KLocallyRingedSpace.{u} 𝕜)
      ((restrictOpenIsoOfSetEq hset₁).hom ≫ s ≫ (restrictOpenIsoOfSetEq hset₂).hom ≫
        (restrictOpenTopIso _).hom) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _)
      (@IsIso.comp_isIso _ _ _ _ _ _ _ hs
        (@IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) (Iso.isIso_hom _)))
  refine ⟨((restrictOpenIsoOfSetEq hset₁).hom ≫ s ≫ (restrictOpenIsoOfSetEq hset₂).hom ≫
      (restrictOpenTopIso _).hom :
      ((bed.resolution X).restrictSet (bed.resolutionMap X ⁻¹' U)).toKLocallyRingedSpace ⟶
        ((bed.resolution Y).restrictSet (bed.resolutionMap Y ⁻¹' V)).toKLocallyRingedSpace),
    isIso_of_isIso_toKLocallyRingedSpace _ hKψ, ?_⟩
  change ((restrictOpenIsoOfSetEq hset₁).hom ≫ s ≫ (restrictOpenIsoOfSetEq hset₂).hom ≫
      (restrictOpenTopIso _).hom) ≫
      Hom.restrictSetTo (bed.resolutionMap Y) V =
    Hom.restrictSetTo (bed.resolutionMap X) U ≫ φ
  exact final_square_eq (restrictOpenIsoOfSetEq hset₁).hom _ _
    (restrictOpenIsoOfSetEq_hom_comp hset₁) s (restrictOpenIsoOfSetEq hset₂).hom _ _
    ((congrArg (fun k => (restrictOpenIsoOfSetEq hset₂).hom ≫ k) (restrictOpenTopIso_hom _)).trans
      (restrictOpenIsoOfSetEq_hom_comp hset₂))
    (bed.resolutionMap X)
    (Hom.restrictSetTo (bed.resolutionMap X) U) _
    (Hom.restrictSetTo_comp_ofRestrict (bed.resolutionMap X) U)
    (Hom.restrictSetTo (bed.resolutionMap Y) V) φ hsc
    (fun f g h => Hom.ext_of_comp_ofRestrict h)

end Hironaka.Manifold.BEDanFamStar


namespace AnalyticSpace.ResolutionAssignment

variable {K : Type} [RCLike K] {C : Type w} [HasUnderlyingSpace.{u, w} C K]

/-- **The lifts of isomorphisms between open subspaces respect composition**: for a resolution
assignment `R` lifting local analytic isomorphisms (uniquely, `LiftsLocalIsomorphisms`), the lift
of a composite `φ₁ ≫ φ₂` of isomorphisms `X|U ≅ Y|V ≅ Z|W` between open subspaces of inputs is the
composite of the lifts — `ψ₁ ≫ ψ₂` lies over `φ₁ ≫ φ₂`, and the lift is the only morphism over
it. -/
theorem LiftsLocalIsomorphisms.lift_comp_restrictSet {R : ResolutionAssignment C}
    (hR : R.LiftsLocalIsomorphisms) {X Y Z : C} {U : Set (toAnalyticSpace X)}
    {V : Set (toAnalyticSpace Y)} {W : Set (toAnalyticSpace Z)} (hU : IsOpen U) (hW : IsOpen W)
    (φ₁ : (toAnalyticSpace X).restrictSet U ⟶ (toAnalyticSpace Y).restrictSet V)
    (φ₂ : (toAnalyticSpace Y).restrictSet V ⟶ (toAnalyticSpace Z).restrictSet W)
    (h₁₂ : IsIso (φ₁ ≫ φ₂))
    (ψ₁ : (R.space X).restrictSet (R.map X ⁻¹' U) ⟶ (R.space Y).restrictSet (R.map Y ⁻¹' V))
    (ψ₂ : (R.space Y).restrictSet (R.map Y ⁻¹' V) ⟶ (R.space Z).restrictSet (R.map Z ⁻¹' W))
    (hc₁ : ψ₁ ≫ (R.map Y).restrictSet V = (R.map X).restrictSet U ≫ φ₁)
    (hc₂ : ψ₂ ≫ (R.map Z).restrictSet W = (R.map Y).restrictSet V ≫ φ₂)
    (ψ : (R.space X).restrictSet (R.map X ⁻¹' U) ⟶ (R.space Z).restrictSet (R.map Z ⁻¹' W))
    (hc : ψ ≫ (R.map Z).restrictSet W = (R.map X).restrictSet U ≫ φ₁ ≫ φ₂) :
    ψ = ψ₁ ≫ ψ₂ := by
  obtain ⟨_, -, hlift⟩ := hR.exists_lift_of_isIso X Z U W hU hW (φ₁ ≫ φ₂) h₁₂
  have huniq := fun ψ' => (hlift ψ').1
  refine (huniq ψ hc).trans (huniq (ψ₁ ≫ ψ₂) ?_).symm
  rw [Category.assoc, hc₂, ← Category.assoc, hc₁, Category.assoc]

/-- **The lifts of isomorphisms between open subspaces respect identities**: for a resolution
assignment `R` lifting local analytic isomorphisms (uniquely, `LiftsLocalIsomorphisms`), the lift
of the identity of `X|U` is the identity. -/
theorem LiftsLocalIsomorphisms.lift_id_restrictSet {R : ResolutionAssignment C}
    (hR : R.LiftsLocalIsomorphisms) {X : C} {U : Set (toAnalyticSpace X)} (hU : IsOpen U)
    (ψ : (R.space X).restrictSet (R.map X ⁻¹' U) ⟶ (R.space X).restrictSet (R.map X ⁻¹' U))
    (hc : ψ ≫ (R.map X).restrictSet U = (R.map X).restrictSet U) : ψ = 𝟙 _ := by
  obtain ⟨_, -, hlift⟩ := hR.exists_lift_of_isIso X X U U hU hU (𝟙 _)
    (inferInstance : IsIso (𝟙 _))
  have huniq := fun ψ' => (hlift ψ').1
  exact (huniq ψ (hc.trans (Category.comp_id _).symm)).trans
    (huniq (𝟙 _) ((Category.id_comp _).trans (Category.comp_id _).symm)).symm

end AnalyticSpace.ResolutionAssignment

end
