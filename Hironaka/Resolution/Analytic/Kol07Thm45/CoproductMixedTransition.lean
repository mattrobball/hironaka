/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductSumData
public import Hironaka.Resolution.Analytic.Kol07Thm45.AmbientLift
import Hironaka.AnalyticSpace.Glue.Normalize
import Hironaka.Manifold.Exhaustion
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Resolution.Analytic.Kol07Thm45.FixedRunDevice
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionRestrict
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionShear
import Hironaka.Resolution.Analytic.Kol07Thm45.MixedTransitionOpens
import Hironaka.Resolution.Analytic.Kol07Thm45.RestrictSetIncl
import Hironaka.Resolution.Analytic.Kol07Thm45.ShearBaseOpens
import Hironaka.Resolution.Analytic.Kol07Thm45.ShearOverX
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The mixed-pair transition of the common datum

Two adjacent levels `D₁`, `D₂` of the exhaustion are read on ONE common datum
`S := sumPadData D₁ D₂` (the pieces of `D₁` padded on the right by `D₂.n` coordinates, the pieces
of `D₂` padded on the left by `D₁.n`, summed; `CoproductSumData.lean`), whose single run carries
the common labels ([Kol07, Proposition 37, proof]). At a point `x` of the domains of a piece `i`
of the first level and a piece `j` of the second, **the mixed-pair transition** is an isomorphism
over `X` between the parts over an open `P ∋ x` of the two padded pieces' local resolutions, under
which the common run's member of EVERY label on piece `j` pulls back to its member of the SAME
label on piece `i` — the agreement of the centres on the overlaps, (37.2) in
[Kol07, Proposition 37, proof].

The construction: restrict both pieces to the common open `O' = pieceDom i ⊓ pieceDom j`, take the
shear `g` of [Kol07, Lemma 39] between the padded restricted pieces at `x`
(`exists_padded_equivalence_hom_point`, `LocalResolutionShear.lean`, with its ideal identity `hI`,
its morphism identity `hmor` and its point clause `hpt`), read the shear's domain `N₀` as ONE
admissible input `T₀` with two open embeddings `u = sigmaMk (inl i) ∘ ι₁⁺ ∘ ι_{W₁'}` and
`v = sigmaMk (inr j) ∘ ι₂⁺ ∘ ι_{W₂'} ∘ g` into the sum's coproduct ambient — both pull the
coproduct triple back to `T₀` (by `hI`) — and shrink to a relatively compact `W₀ ∋ p₀`. The
fixed-run device (`FixedRunDevice.lean`) identifies the local resolution `Y₀` of `T₀|W₀` with the
parts of the two pieces' local resolutions over `P := domOpens (ι₁⁺ ι_{W₁'} W₀)` through the two
open immersions `localResolutionHomOn` (`isoOfRangeEq`, the ranges by
`MixedTransitionOpens.lean`), the two spellings of the base open agree by `ShearBaseOpens.lean`,
and the members correspond by the device's synchronisation. The over-`X` clause is the
closed-subspace identity of `ShearOverX.lean` read through `resIn_comp_localResolutionMapOn` and
`localResolutionHomOn_comp_map`, the monomorphism `homOfPullbackEq (restrictMap (sigmaMk …))`
cancelled.

Three generic category lemmas do the associativity bookkeeping (`comp_eq_of_over_ambient`,
`transition_over_eq_of_parts`, `comp_ofRestrict_eq_of_inv_comp`). The transition is used by
`CoproductGluedFamilyCompat.lean`, `CoproductLevelPair.lean` and `DoubledDatumLabels.lean`. Not in
the sources beyond Kollár's proof; bookkeeping.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set AnalyticSpace
open KLocallyRingedSpace
open scoped Manifold ContDiff

universe u

namespace CategoryTheory

variable {𝒞 : Type*} [Category 𝒞]

/-- The compatibility of a device identification with the maps to the ambient closed subspaces,
before cancelling the monomorphism `Hi` — in any category. -/
theorem comp_eq_of_over_ambient {Y₀ A Yi Ci C₀ Y₁ B₀ : 𝒞} (e : Y₀ ⟶ A) (ofR : A ⟶ Yi)
    (mapi : Yi ⟶ Ci) (Hi : Ci ⟶ C₀) (res : Yi ⟶ Y₁) (map₁ : Y₁ ⟶ C₀)
    (hsq : res ≫ map₁ = mapi ≫ Hi) (φ : Y₀ ⟶ Y₁) (hφ : e ≫ ofR ≫ res = φ) (map₀ : Y₀ ⟶ B₀)
    (Hu : B₀ ⟶ C₀) (hcm : φ ≫ map₁ = map₀ ≫ Hu) (H₁ : B₀ ⟶ Ci) (hHu : Hu = H₁ ≫ Hi) :
    ((e ≫ ofR) ≫ mapi) ≫ Hi = (map₀ ≫ H₁) ≫ Hi := by
  simp only [Category.assoc]
  rw [← hsq, ← Category.assoc ofR res, ← Category.assoc e (ofR ≫ res), hφ, hcm, hHu]

/-- The transition followed by the restriction and the open immersion is the first identification
followed by the second device map. -/
theorem comp_ofRestrict_eq_of_inv_comp {A Y₀ Aj' Aj Yj Y₁ : 𝒞} (e₁h : A ⟶ Y₀) (e₂i : Y₀ ⟶ Aj')
    (ρh : Aj' ⟶ Aj) (ofRj : Aj ⟶ Yj) (ofRj' : Aj' ⟶ Yj) (hρ : ρh ≫ ofRj = ofRj') (res : Yj ⟶ Y₁)
    (φ : Y₀ ⟶ Y₁) (hφ : e₂i ≫ ofRj' ≫ res = φ) :
    (e₁h ≫ e₂i ≫ ρh) ≫ ofRj ≫ res = e₁h ≫ φ := by
  simp only [Category.assoc]
  rw [← Category.assoc ρh, hρ, hφ]

/-- The over-`X` clause of a transition assembled from two identifications of the parts with a
common space, the two maps to the ambient closed subspaces and the agreement of the read-down maps
— in any category. -/
theorem transition_over_eq_of_parts {A Y₀ Yi Yj Aj' Aj Ci Cj B₀ Z : 𝒞}
    (e₁h : A ⟶ Y₀) (e₁i : Y₀ ⟶ A) (he₁ : e₁h ≫ e₁i = 𝟙 A)
    (e₂i : Y₀ ⟶ Aj') (ρh : Aj' ⟶ Aj) (ofRj : Aj ⟶ Yj) (ofRj' : Aj' ⟶ Yj) (hρ : ρh ≫ ofRj = ofRj')
    (ofRi : A ⟶ Yi) (mapi : Yi ⟶ Ci) (POHi : Ci ⟶ Z) (πi : Yi ⟶ Z) (hπi : πi = mapi ≫ POHi)
    (mapj : Yj ⟶ Cj) (POHj : Cj ⟶ Z) (πj : Yj ⟶ Z) (hπj : πj = mapj ≫ POHj)
    (map₀ : Y₀ ⟶ B₀) (H₁ : B₀ ⟶ Ci) (H₂ : B₀ ⟶ Cj)
    (hA₁ : (e₁i ≫ ofRi) ≫ mapi = map₀ ≫ H₁) (hA₂ : (e₂i ≫ ofRj') ≫ mapj = map₀ ≫ H₂)
    (hX₀ : H₁ ≫ POHi = H₂ ≫ POHj) :
    ofRi ≫ πi = ((e₁h ≫ e₂i ≫ ρh) ≫ ofRj) ≫ πj := by
  have hA₁' : e₁i ≫ ofRi ≫ mapi = map₀ ≫ H₁ := (Category.assoc _ _ _).symm.trans hA₁
  have hA₂' : e₂i ≫ ofRj' ≫ mapj = map₀ ≫ H₂ := (Category.assoc _ _ _).symm.trans hA₂
  calc ofRi ≫ πi = (e₁h ≫ e₁i) ≫ ofRi ≫ πi := by rw [he₁, Category.id_comp]
    _ = e₁h ≫ (e₁i ≫ ofRi ≫ mapi) ≫ POHi := by rw [hπi]; simp only [Category.assoc]
    _ = e₁h ≫ (map₀ ≫ H₂) ≫ POHj := by
        rw [hA₁', Category.assoc, hX₀, ← Category.assoc map₀]
    _ = e₁h ≫ (e₂i ≫ ofRj' ≫ mapj) ≫ POHj := by rw [hA₂']
    _ = ((e₁h ≫ e₂i ≫ ρh) ≫ ofRj) ≫ πj := by rw [hπj, ← hρ]; simp only [Category.assoc]

end CategoryTheory

namespace Hironaka.Manifold.LocalEmbeddingData

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜}

section Mixed

variable {U₁ U₂ : Set X} (D₁ : LocalEmbeddingData 𝕜 X U₁) (D₂ : LocalEmbeddingData 𝕜 X U₂)
  (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
  (W₁ : ∀ i : D₁.ι, Opens (pieceAmbient.{u} 𝕜 ((D₁.padLeftData D₂.n).embedding i).G))
  (hW₁ : ∀ i, IsCompact (closure (W₁ i : Set (pieceAmbient.{u} 𝕜
    ((D₁.padLeftData D₂.n).embedding i).G))))
  (W₂ : ∀ j : D₂.ι, Opens (pieceAmbient.{u} 𝕜 ((D₂.padRightData D₁.n).embedding j).G))
  (hW₂ : ∀ j, IsCompact (closure (W₂ j : Set (pieceAmbient.{u} 𝕜
    ((D₂.padRightData D₁.n).embedding j).G))))

/-- **The mixed-pair transition of the common datum** ((37.2) in [Kol07, Proposition 37, proof];
[Kol07, Lemma 39] for the shear): at a point of the domains of a piece of the first level and a
piece of the second, an open `P` and an isomorphism over `X` between the parts over `P` of the two
padded pieces' local resolutions under which the common run's member of EVERY label on the second
piece pulls back to its member of the SAME label on the first. -/
theorem exists_mixedTransition_sumPadData (i : D₁.ι) (j : D₂.ι) (x : X)
    (hxi : x ∈ (sumPadData D₁ D₂).pieceDom (Sum.inl i) (W₁ i))
    (hxj : x ∈ (sumPadData D₁ D₂).pieceDom (Sum.inr j) (W₂ j)) :
    ∃ P : Opens X, x ∈ P ∧ P ≤ (sumPadData D₁ D₂).pieceDom (Sum.inl i) (W₁ i) ∧
      P ≤ (sumPadData D₁ D₂).pieceDom (Sum.inr j) (W₂ j) ∧
      ∃ θ : (((sumPadData D₁ D₂).embedding (Sum.inl i)).localResolution bed (W₁ i)
              (hW₁ i)).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((sumPadData D₁ D₂).pieceToSpace bed
                (Sum.inl i) (W₁ i)
              (hW₁ i)), Hom.continuous_toFun _⟩ P) ⟶
          (((sumPadData D₁ D₂).embedding (Sum.inr j)).localResolution bed (W₂ j)
              (hW₂ j)).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((sumPadData D₁ D₂).pieceToSpace bed
                (Sum.inr j) (W₂ j)
              (hW₂ j)), Hom.continuous_toFun _⟩ P),
        IsIso θ ∧
        ofRestrict _ _ ≫ (sumPadData D₁ D₂).pieceToSpace bed (Sum.inl i) (W₁ i) (hW₁ i) =
          (θ ≫ ofRestrict _ _) ≫ (sumPadData D₁ D₂).pieceToSpace bed (Sum.inr j) (W₂ j) (hW₂ j) ∧
        ∀ σ : (sumPadData D₁ D₂).sigmaIndex bed (sumPadOpens D₁ D₂ W₁ W₂)
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂),
          QuotientSpace.comap θ.1
              (QuotientSpace.comap (ofRestrict (((sumPadData D₁ D₂).embedding
                  (Sum.inr j)).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace
                  (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((sumPadData D₁ D₂).pieceToSpace bed
                      (Sum.inr j) (W₂ j)
                    (hW₂ j)), Hom.continuous_toFun _⟩ P)).1
                (QuotientSpace.comap ((sumPadData D₁ D₂).resIn bed (sumPadOpens D₁ D₂ W₁ W₂)
                    (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed (Sum.inr j)).1
                  ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
                    (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ))) =
            QuotientSpace.comap (ofRestrict (((sumPadData D₁ D₂).embedding
                (Sum.inl i)).localResolution bed (W₁ i) (hW₁ i)).toKLocallyRingedSpace
                (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((sumPadData D₁ D₂).pieceToSpace bed
                    (Sum.inl i) (W₁ i)
                  (hW₁ i)), Hom.continuous_toFun _⟩ P)).1
              (QuotientSpace.comap ((sumPadData D₁ D₂).resIn bed (sumPadOpens D₁ D₂ W₁ W₂)
                  (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed (Sum.inl i)).1
                ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
                  (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ)) := by
  -- first, the common open `O'` inside both pieces; the pieces restricted to it
  let O' : Opens X := (sumPadData D₁ D₂).pieceDom (Sum.inl i) (W₁ i) ⊓
    (sumPadData D₁ D₂).pieceDom (Sum.inr j) (W₂ j)
  have hO' : IsOpen (O' : Set X) := O'.isOpen
  have hxO' : x ∈ (O' : Set X) := Opens.mem_inf.mpr ⟨hxi, hxj⟩
  have hO'₁ : (O' : Set X) ⊆ D₁.piece i := fun z hz =>
    ((sumPadData D₁ D₂).embedding (Sum.inl i)).domOpens_subset
      ((sumPadData D₁ D₂).isOpen_piece (Sum.inl i)) (W₁ i) (Opens.mem_inf.mp hz).1
  have hO'₂ : (O' : Set X) ⊆ D₂.piece j := fun z hz =>
    ((sumPadData D₁ D₂).embedding (Sum.inr j)).domOpens_subset
      ((sumPadData D₁ D₂).isOpen_piece (Sum.inr j)) (W₂ j) (Opens.mem_inf.mp hz).2
  let E₁ := D₁.embedding i
  let E₂ := D₂.embedding j
  let σ₁ : Fin D₁.n ↪ Fin (D₁.n + D₂.n) := Fin.castAddEmb D₂.n
  let σ₂ : Fin D₂.n ↪ Fin (D₁.n + D₂.n) := Fin.natAddEmb D₁.n
  let x' : X.restrictSet (O' : Set X) :=
    ⟨x, (mem_openOf_iff_of_isOpen X hO' x).mpr hxO'⟩
  -- second, the shear of [Kol07, Lemma 39] between the padded restricted pieces at `x`
  obtain ⟨W₁', W₂', g, hxW₁, hloc, hbij, ⟨hI, hmor⟩, hpt⟩ :=
    exists_padded_equivalence_hom_point (E₁.restrictPiece hO' hO'₁) (E₂.restrictPiece hO' hO'₂) x'
  -- third, the two open embeddings of the shear's domain into the sum's coproduct ambient
  let Sp := (E₁.restrictPiece hO' hO'₁).padAlong σ₁
  let Tp := (E₂.restrictPiece hO' hO'₂).padAlong σ₂
  let ι₁ := AnalyticManifold.inclusion (E₁.padRestrictAmbient hO' hO'₁ σ₁) W₁'
  let ι₂ := AnalyticManifold.inclusion (E₂.padRestrictAmbient hO' hO'₂ σ₂) W₂'
  let g' : AnalyticMap ((E₁.padRestrictAmbient hO' hO'₁ σ₁).restrict W₁')
    ((E₂.padRestrictAmbient hO' hO'₂ σ₂).restrict W₂') := g
  let a₁ := E₁.padRestrictIncl hO' hO'₁ σ₁
  let a₂ := E₂.padRestrictIncl hO' hO'₂ σ₂
  let m₁ : AnalyticMap (pieceAmbient.{u} 𝕜 (E₁.padAlong σ₁).G)
      (sumPadData D₁ D₂).sigmaAmbient :=
    sigmaMk (fun k => pieceAmbient.{u} 𝕜 ((sumPadData D₁ D₂).embedding k).G) (Sum.inl i)
  let m₂ : AnalyticMap (pieceAmbient.{u} 𝕜 (E₂.padAlong σ₂).G)
      (sumPadData D₁ D₂).sigmaAmbient :=
    sigmaMk (fun k => pieceAmbient.{u} 𝕜 ((sumPadData D₁ D₂).embedding k).G) (Sum.inr j)
  let Wi : Opens (pieceAmbient.{u} 𝕜 (E₁.padAlong σ₁).G) := W₁ i
  let Wj : Opens (pieceAmbient.{u} 𝕜 (E₂.padAlong σ₂).G) := W₂ j
  let u := m₁.comp (a₁.comp ι₁)
  let v := m₂.comp (a₂.comp (ι₂.comp g'))
  have hinju : Function.Injective ⇑u :=
    (isAnalyticOpenEmbedding_sigmaMk
        (fun k => pieceAmbient.{u} 𝕜 ((sumPadData D₁ D₂).embedding k).G) (Sum.inl i)).2.comp
      ((isAnalyticOpenEmbedding_pieceAmbientIncl
        (padOpens_mono σ₁ (E₁.restrictAmbient_le hO'))).2.comp Subtype.val_injective)
  have hinjv : Function.Injective ⇑v :=
    (isAnalyticOpenEmbedding_sigmaMk
        (fun k => pieceAmbient.{u} 𝕜 ((sumPadData D₁ D₂).embedding k).G) (Sum.inr j)).2.comp
      ((isAnalyticOpenEmbedding_pieceAmbientIncl
        (padOpens_mono σ₂ (E₂.restrictAmbient_le hO'))).2.comp
        (Subtype.val_injective.comp hbij.1))
  have hu : IsAnalyticOpenEmbedding u :=
    ⟨AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp (isAnalyticOpenEmbedding_sigmaMk _ _).1
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
            (isAnalyticOpenEmbedding_pieceAmbientIncl _).1
          (isLocalDiffeomorph_inclusion _ W₁')), hinju⟩
  have hv : IsAnalyticOpenEmbedding v :=
    ⟨AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp (isAnalyticOpenEmbedding_sigmaMk _ _).1
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
            (isAnalyticOpenEmbedding_pieceAmbientIncl _).1
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
              (isLocalDiffeomorph_inclusion _ W₂') hloc)), hinjv⟩
  -- the common input on the shear's domain, pulled back from the coproduct triple along `u`, `v`
  let T₀ := E₁.shearInput hO' hO'₁ σ₁ W₁'
  have hT₀ : DomBEDan 𝕜 T₀ := Sp.domBEDan_ambientTriple_pullback_inclusion W₁'
  have hpu : T₀.IsPullbackOf (sumPadData D₁ D₂).sigmaTriple u :=
    ((sumPadData D₁ D₂).isPullbackOf_ambientTriple_sigmaTriple (Sum.inl i)).comp
      (isPullbackOf_shearInput_padAlong E₁ hO' hO'₁ σ₁ W₁')
  have hpv : T₀.IsPullbackOf (sumPadData D₁ D₂).sigmaTriple v :=
    ((sumPadData D₁ D₂).isPullbackOf_ambientTriple_sigmaTriple (Sum.inr j)).comp
      (isPullbackOf_shearInput_shear E₁ E₂ hO' hO'₁ hO'₂ σ₁ σ₂ W₁' W₂' g hI)
  -- fourth, the point `p₀` and a relatively compact reading open `W₀ ∋ p₀` inside both preimages
  have hxV₁ : x ∈ openOf X (D₁.piece i) :=
    (mem_openOf_iff_of_isOpen X (D₁.isOpen_piece i) x).mpr
      (hO'₁ hxO')
  have hxV₂ : x ∈ openOf X (D₂.piece j) :=
    (mem_openOf_iff_of_isOpen X (D₂.isOpen_piece j) x).mpr
      (hO'₂ hxO')
  let y₁ : X.restrictSet (D₁.piece i) := ⟨x, hxV₁⟩
  let y₂ : X.restrictSet (D₂.piece j) := ⟨x, hxV₂⟩
  let p₀ : (E₁.padRestrictAmbient hO' hO'₁ σ₁).restrict W₁' := ⟨Sp.ambientPoint x', hxW₁⟩
  have hamb₁ : a₁ (ι₁ p₀) = (E₁.padAlong σ₁).ambientPoint y₁ :=
    (congrArg (pieceAmbientIncl (padOpens_mono σ₁ (E₁.restrictAmbient_le hO')))
      ((E₁.restrictPiece hO' hO'₁).ambientPoint_padAlong σ₁ x')).trans
      ((pieceAmbientIncl_padExt σ₁ (E₁.restrictAmbient_le hO') _).trans
        ((congrArg (padExt σ₁ E₁.G)
          (E₁.pieceAmbientIncl_ambientPoint_restrictPiece hO' hO'₁ x')).trans
          (E₁.ambientPoint_padAlong σ₁ _).symm))
  have hamb₂ : a₂ (ι₂ (g' p₀)) = (E₂.padAlong σ₂).ambientPoint y₂ :=
    (congrArg (pieceAmbientIncl (padOpens_mono σ₂ (E₂.restrictAmbient_le hO')))
      (hpt x' hxW₁)).trans
      ((congrArg (pieceAmbientIncl (padOpens_mono σ₂ (E₂.restrictAmbient_le hO')))
        ((E₂.restrictPiece hO' hO'₂).ambientPoint_padAlong σ₂ x')).trans
        ((pieceAmbientIncl_padExt σ₂ (E₂.restrictAmbient_le hO') _).trans
          ((congrArg (padExt σ₂ E₂.G)
            (E₂.pieceAmbientIncl_ambientPoint_restrictPiece hO' hO'₂ x')).trans
            (E₂.ambientPoint_padAlong σ₂ _).symm)))
  have hx₁ : (E₁.padAlong σ₁).ambientPoint y₁ ∈ W₁ i :=
    ((sumPadData D₁ D₂).embedding (Sum.inl i)).mem_embPreimage_of_val_mem_domOpens (W₁ i) y₁ hxi
  have hx₂ : (E₂.padAlong σ₂).ambientPoint y₂ ∈ W₂ j :=
    ((sumPadData D₁ D₂).embedding (Sum.inr j)).mem_embPreimage_of_val_mem_domOpens (W₂ j) y₂ hxj
  let A₁ : Opens ((E₁.padRestrictAmbient hO' hO'₁ σ₁).restrict W₁') :=
    preimageOpens (a₁.comp ι₁) (a₁.comp ι₁).contMDiff Wi
  let A₂ : Opens ((E₁.padRestrictAmbient hO' hO'₁ σ₁).restrict W₁') :=
    preimageOpens (a₂.comp (ι₂.comp g')) (a₂.comp (ι₂.comp g')).contMDiff Wj
  have hp₀ : p₀ ∈ A₁ ⊓ A₂ :=
    Opens.mem_inf.mpr ⟨show (a₁.comp ι₁) p₀ ∈ Wi from Set.mem_of_eq_of_mem hamb₁ hx₁,
      show (a₂.comp (ι₂.comp g')) p₀ ∈ Wj from Set.mem_of_eq_of_mem hamb₂ hx₂⟩
  have : LocallyCompactSpace ((E₁.padRestrictAmbient hO' hO'₁ σ₁).restrict W₁') :=
    locallyCompactSpace_of_finiteDimensional 𝕜 (Fin (D₁.n + D₂.n) → 𝕜) _
  obtain ⟨W₀, hp₀W₀, hW₀le, hW₀⟩ := exists_opens_isCompact_closure_mem_le _ hp₀
  have hle₁ : ⇑(a₁.comp ι₁) '' (W₀ : Set _) ⊆ (Wi : Set _) := by
    rintro _ ⟨q, hq, rfl⟩
    exact (Opens.mem_inf.mp (hW₀le hq)).1
  have hle₂ : ⇑(a₂.comp (ι₂.comp g')) '' (W₀ : Set _) ⊆ (Wj : Set _) := by
    rintro _ ⟨q, hq, rfl⟩
    exact (Opens.mem_inf.mp (hW₀le hq)).2
  -- the reading open of the common run; both images land in it
  let V₀ : Opens (sumPadData D₁ D₂).sigmaAmbient :=
    (sumPadData D₁ D₂).ambImage (sumPadOpens D₁ D₂ W₁ W₂)
  have hV₀ : IsCompact (closure (V₀ : Set (sumPadData D₁ D₂).sigmaAmbient)) :=
    (sumPadData D₁ D₂).isCompact_closure_ambImage _
      (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂)
  have huV : ⇑u '' (W₀ : Set _) ⊆ (V₀ : Set _) := by
    rintro _ ⟨q, hq, rfl⟩
    exact (sumPadData D₁ D₂).image_subset_ambImage (sumPadOpens D₁ D₂ W₁ W₂) (Sum.inl i)
      ⟨(a₁.comp ι₁) q, hle₁ ⟨q, hq, rfl⟩, rfl⟩
  have hvV : ⇑v '' (W₀ : Set _) ⊆ (V₀ : Set _) := by
    rintro _ ⟨q, hq, rfl⟩
    exact (sumPadData D₁ D₂).image_subset_ambImage (sumPadOpens D₁ D₂ W₁ W₂) (Sum.inr j)
      ⟨(a₂.comp (ι₂.comp g')) q, hle₂ ⟨q, hq, rfl⟩, rfl⟩
  -- fifth, the device: the two open immersions of `Y₀` into the common run's local resolution
  let Ystar := bed.localResolutionOn (sumPadData D₁ D₂).sigmaTriple
    (sumPadData D₁ D₂).domBEDan_sigmaTriple V₀ hV₀
  let Y₀ := bed.localResolutionOn T₀ hT₀ W₀ hW₀
  let φu : Y₀.toKLocallyRingedSpace ⟶ Ystar.toKLocallyRingedSpace :=
    bed.localResolutionHomOn (sumPadData D₁ D₂).sigmaTriple (sumPadData D₁ D₂).domBEDan_sigmaTriple
      V₀ hV₀ T₀ hT₀ u hu hpu W₀ hW₀ huV hbed
  let φv : Y₀.toKLocallyRingedSpace ⟶ Ystar.toKLocallyRingedSpace :=
    bed.localResolutionHomOn (sumPadData D₁ D₂).sigmaTriple (sumPadData D₁ D₂).domBEDan_sigmaTriple
      V₀ hV₀ T₀ hT₀ v hv hpv W₀ hW₀ hvV hbed
  have hmem : ∀ σ, QuotientSpace.comap φu.1 (bed.runMembers (sumPadData D₁ D₂).sigmaTriple
        (sumPadData D₁ D₂).domBEDan_sigmaTriple V₀ hV₀ hbed σ) =
      QuotientSpace.comap φv.1 (bed.runMembers (sumPadData D₁ D₂).sigmaTriple
        (sumPadData D₁ D₂).domBEDan_sigmaTriple V₀ hV₀ hbed σ) :=
    fun σ => bed.comap_localResolutionHomOn_runMembers_eq_of_isPullbackOf
      (sumPadData D₁ D₂).sigmaTriple (sumPadData D₁ D₂).domBEDan_sigmaTriple hbed V₀ hV₀ T₀ hT₀
      u v hu hv hpu hpv W₀ hW₀ huV hvV σ
  -- sixth, the base open `P` and its two spellings
  let Q₁' : Opens (E₁.padRestrictAmbient hO' hO'₁ σ₁) :=
    AnalyticMap.imageOpens ι₁ (isLocalDiffeomorph_inclusion _ W₁') W₀
  let Q₁ : Opens (pieceAmbient.{u} 𝕜 (E₁.padAlong σ₁).G) :=
    pieceAmbientImageOpens (padOpens_mono σ₁ (E₁.restrictAmbient_le hO')) Q₁'
  let Q₂' : Opens (E₂.padRestrictAmbient hO' hO'₂ σ₂) :=
    AnalyticMap.imageOpens (ι₂.comp g')
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
          (isLocalDiffeomorph_inclusion _ W₂') hloc) W₀
  let Q₂ : Opens (pieceAmbient.{u} 𝕜 (E₂.padAlong σ₂).G) :=
    pieceAmbientImageOpens (padOpens_mono σ₂ (E₂.restrictAmbient_le hO')) Q₂'
  have hQ₁ : Q₁ ≤ Wi := by
    intro w hw
    obtain ⟨_, ⟨q, hq, rfl⟩, rfl⟩ := hw
    exact hle₁ ⟨q, hq, rfl⟩
  have hQ₂ : Q₂ ≤ Wj := by
    intro w hw
    obtain ⟨_, ⟨q, hq, rfl⟩, rfl⟩ := hw
    exact hle₂ ⟨q, hq, rfl⟩
  let P : Opens X := (E₁.padAlong σ₁).domOpens Q₁
  have hP : (E₂.padAlong σ₂).domOpens Q₂ = P :=
    (E₂.domOpens_padAlong_pieceAmbientImageOpens hO' hO'₂ σ₂ Q₂').trans
      ((Sp.domOpens_imageOpens_eq_of_shear Tp W₁' W₂' g hbij hloc hI hmor hpt W₀).symm.trans
        (E₁.domOpens_padAlong_pieceAmbientImageOpens hO' hO'₁ σ₁ Q₁').symm)
  have hxP : x ∈ P :=
    (E₁.padAlong σ₁).mem_domOpens.mpr
      ⟨y₁, ⟨ι₁ p₀, ⟨p₀, hp₀W₀, rfl⟩, hamb₁⟩, rfl⟩
  have hP₁ : P ≤ (sumPadData D₁ D₂).pieceDom (Sum.inl i) (W₁ i) := fun z hz => by
    obtain ⟨y, hy, rfl⟩ := (E₁.padAlong σ₁).mem_domOpens.mp hz
    exact ((sumPadData D₁ D₂).embedding _).mem_domOpens.mpr ⟨y, hQ₁ hy, rfl⟩
  have hP₂ : P ≤ (sumPadData D₁ D₂).pieceDom (Sum.inr j) (W₂ j) := fun z hz => by
    have hz' : z ∈ (E₂.padAlong σ₂).domOpens Q₂ := by rw [hP]; exact hz
    obtain ⟨y, hy, rfl⟩ := (E₂.padAlong σ₂).mem_domOpens.mp hz'
    exact ((sumPadData D₁ D₂).embedding _).mem_domOpens.mpr ⟨y, hQ₂ hy, rfl⟩
  -- seventh, the parts over `P` and their identifications with `Y₀`
  let Yi := ((sumPadData D₁ D₂).embedding (Sum.inl i)).localResolution bed (W₁ i) (hW₁ i)
  let Yj := ((sumPadData D₁ D₂).embedding (Sum.inr j)).localResolution bed (W₂ j) (hW₂ j)
  let πi := (sumPadData D₁ D₂).pieceToSpace bed (Sum.inl i) (W₁ i) (hW₁ i)
  let πj := (sumPadData D₁ D₂).pieceToSpace bed (Sum.inr j) (W₂ j) (hW₂ j)
  let Oi : Opens Yi.toKLocallyRingedSpace := Opens.comap ⟨KLocallyRingedSpace.Hom.toFun πi,
      Hom.continuous_toFun _⟩ P
  let Oj : Opens Yj.toKLocallyRingedSpace := Opens.comap ⟨KLocallyRingedSpace.Hom.toFun πj,
      Hom.continuous_toFun _⟩ P
  let Oj' : Opens Yj.toKLocallyRingedSpace :=
    Opens.comap ⟨KLocallyRingedSpace.Hom.toFun πj, Hom.continuous_toFun _⟩
        ((E₂.padAlong σ₂).domOpens Q₂)
  let ofRi := ofRestrict Yi.toKLocallyRingedSpace Oi
  let ofRj := ofRestrict Yj.toKLocallyRingedSpace Oj
  let ofRj' := ofRestrict Yj.toKLocallyRingedSpace Oj'
  let resi := (sumPadData D₁ D₂).resIn bed (sumPadOpens D₁ D₂ W₁ W₂)
    (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed (Sum.inl i)
  let resj := (sumPadData D₁ D₂).resIn bed (sumPadOpens D₁ D₂ W₁ W₂)
    (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed (Sum.inr j)
  let stagept : Ystar → (sumPadData D₁ D₂).sigmaAmbient := fun y =>
    ((bed.seqOn (sumPadData D₁ D₂).sigmaTriple (sumPadData D₁ D₂).domBEDan_sigmaTriple V₀
        hV₀).toSuccession.stageMap (Fin.last _)
      ((bed.lastIdealOn (sumPadData D₁ D₂).sigmaTriple
          (sumPadData D₁ D₂).domBEDan_sigmaTriple V₀ hV₀).toAnalyticSpaceι y)).1
  have hQ₁s : (Q₁ : Set (pieceAmbient.{u} 𝕜 (E₁.padAlong σ₁).G)) =
      ⇑a₁ '' (⇑ι₁ '' (W₀ : Set _)) := rfl
  have hQ₂s : (Q₂ : Set (pieceAmbient.{u} 𝕜 (E₂.padAlong σ₂).G)) =
      ⇑a₂ '' (⇑(ι₂.comp g') '' (W₀ : Set _)) := rfl
  have himg₁ : ⇑m₁ '' (Q₁ : Set _) = ⇑u '' (W₀ : Set _) :=
    (congrArg (fun s => ⇑m₁ '' s) hQ₁s).trans
      ((Set.image_image _ _ _).trans (Set.image_image _ _ _))
  have himg₂ : ⇑m₂ '' (Q₂ : Set _) = ⇑v '' (W₀ : Set _) :=
    (congrArg (fun s => ⇑m₂ '' s) hQ₂s).trans
      ((Set.image_image _ _ _).trans (Set.image_image _ _ _))
  have hr₁ : Set.range (KLocallyRingedSpace.Hom.toFun (ofRi ≫ resi)) = Set.range
      (KLocallyRingedSpace.Hom.toFun φu) :=
    (((sumPadData D₁ D₂).embedding (Sum.inl i)).range_ofRestrict_comp_localResolutionHomOn bed
        (sumPadData D₁ D₂).sigmaTriple (sumPadData D₁ D₂).domBEDan_sigmaTriple V₀ hV₀ m₁
        (isAnalyticOpenEmbedding_sigmaMk _ _)
        ((sumPadData D₁ D₂).isPullbackOf_ambientTriple_sigmaTriple (Sum.inl i)) (W₁ i) (hW₁ i)
        ((sumPadData D₁ D₂).image_subset_ambImage (sumPadOpens D₁ D₂ W₁ W₂) (Sum.inl i)) hbed Q₁
        hQ₁).trans
      ((congrArg (fun s : Set (sumPadData D₁ D₂).sigmaAmbient => {y : Ystar | stagept y ∈ s})
        himg₁).trans
        (bed.range_toFun_localResolutionHomOn (sumPadData D₁ D₂).sigmaTriple
          (sumPadData D₁ D₂).domBEDan_sigmaTriple V₀ hV₀ T₀ hT₀ u hu hpu W₀ hW₀ huV hbed).symm)
  have hr₂ : Set.range (KLocallyRingedSpace.Hom.toFun (ofRj' ≫ resj)) = Set.range
      (KLocallyRingedSpace.Hom.toFun φv) :=
    (((sumPadData D₁ D₂).embedding (Sum.inr j)).range_ofRestrict_comp_localResolutionHomOn bed
        (sumPadData D₁ D₂).sigmaTriple (sumPadData D₁ D₂).domBEDan_sigmaTriple V₀ hV₀ m₂
        (isAnalyticOpenEmbedding_sigmaMk _ _)
        ((sumPadData D₁ D₂).isPullbackOf_ambientTriple_sigmaTriple (Sum.inr j)) (W₂ j) (hW₂ j)
        ((sumPadData D₁ D₂).image_subset_ambImage (sumPadOpens D₁ D₂ W₁ W₂) (Sum.inr j)) hbed Q₂
        hQ₂).trans
      ((congrArg (fun s : Set (sumPadData D₁ D₂).sigmaAmbient => {y : Ystar | stagept y ∈ s})
        himg₂).trans
        (bed.range_toFun_localResolutionHomOn (sumPadData D₁ D₂).sigmaTriple
          (sumPadData D₁ D₂).domBEDan_sigmaTriple V₀ hV₀ T₀ hT₀ v hv hpv W₀ hW₀ hvV hbed).symm)
  have hoi₁ : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion (ofRi ≫ resi).1 :=
    @AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _ inferInstance _
      ((sumPadData D₁ D₂).isOpenImmersion_resIn bed _ _ hbed (Sum.inl i))
  have hoi₂ : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion (ofRj' ≫ resj).1 :=
    @AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _ inferInstance _
      ((sumPadData D₁ D₂).isOpenImmersion_resIn bed _ _ hbed (Sum.inr j))
  have hoiu : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion φu.1 :=
    bed.isOpenImmersion_localResolutionHomOn (sumPadData D₁ D₂).sigmaTriple
      (sumPadData D₁ D₂).domBEDan_sigmaTriple V₀ hV₀ T₀ hT₀ u hu hpu W₀ hW₀ huV hbed
  have hoiv : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion φv.1 :=
    bed.isOpenImmersion_localResolutionHomOn (sumPadData D₁ D₂).sigmaTriple
      (sumPadData D₁ D₂).domBEDan_sigmaTriple V₀ hV₀ T₀ hT₀ v hv hpv W₀ hW₀ hvV hbed
  let e₁ := @isoOfRangeEq _ _ _ _ _ (ofRi ≫ resi) φu hoi₁ hoiu hr₁
  let e₂ := @isoOfRangeEq _ _ _ _ _ (ofRj' ≫ resj) φv hoi₂ hoiv hr₂
  have hset : ((Oj' : Opens Yj.toKLocallyRingedSpace) : Set Yj.toKLocallyRingedSpace) =
      (Oj : Set Yj.toKLocallyRingedSpace) :=
    congrArg (fun O : Opens X => ((Opens.comap ⟨KLocallyRingedSpace.Hom.toFun πj,
        Hom.continuous_toFun _⟩ O :
      Opens Yj.toKLocallyRingedSpace) : Set Yj.toKLocallyRingedSpace)) hP
  let ρ := restrictOpenIsoOfSetEq hset
  let θ : Yi.toKLocallyRingedSpace.restrictOpen Oi ⟶ Yj.toKLocallyRingedSpace.restrictOpen Oj :=
    e₁.hom ≫ e₂.inv ≫ ρ.hom
  have k₁ : θ ≫ ofRj ≫ resj = e₁.hom ≫ φv :=
    CategoryTheory.comp_ofRestrict_eq_of_inv_comp (𝒞 := KLocallyRingedSpace.{u} 𝕜) e₁.hom e₂.inv
      ρ.hom ofRj ofRj' (restrictOpenIsoOfSetEq_hom_comp hset) resj φv
          (Glue.isoOfRangeEq_inv_comp _ _ _)
  have k₂ : e₁.hom ≫ φu = ofRi ≫ resi := isoOfRangeEq_hom_comp _ _ _
  refine ⟨P, hxP, hP₁, hP₂, θ, ?_, ?_, ?_⟩
  · -- the transition is an isomorphism
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _)
      (@IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv _) (Iso.isIso_hom _))
  · -- the transition lies over `X`: the closed-subspace identity of `ShearOverX.lean`, read through
    -- maps of the local resolutions to the ambient closed subspaces
    let mapi : Yi.toKLocallyRingedSpace ⟶
        (((sumPadData D₁ D₂).embedding (Sum.inl i)).restrictedIdeal
          (W₁ i)).toAnalyticSpace.toKLocallyRingedSpace :=
      ((sumPadData D₁ D₂).embedding (Sum.inl i)).localResolutionMap bed (W₁ i) (hW₁ i)
    let mapj : Yj.toKLocallyRingedSpace ⟶
        (((sumPadData D₁ D₂).embedding (Sum.inr j)).restrictedIdeal
          (W₂ j)).toAnalyticSpace.toKLocallyRingedSpace :=
      ((sumPadData D₁ D₂).embedding (Sum.inr j)).localResolutionMap bed (W₂ j) (hW₂ j)
    let mapstar : Ystar.toKLocallyRingedSpace ⟶
        (BEDanFamStar.restrictedIdealOn (sumPadData D₁ D₂).sigmaTriple
          V₀).toAnalyticSpace.toKLocallyRingedSpace :=
      bed.localResolutionMapOn (sumPadData D₁ D₂).sigmaTriple
        (sumPadData D₁ D₂).domBEDan_sigmaTriple V₀ hV₀
    let map₀ : Y₀.toKLocallyRingedSpace ⟶
        (BEDanFamStar.restrictedIdealOn T₀ W₀).toAnalyticSpace.toKLocallyRingedSpace :=
      bed.localResolutionMapOn T₀ hT₀ W₀ hW₀
    let hleV₁ := (sumPadData D₁ D₂).image_subset_ambImage (sumPadOpens D₁ D₂ W₁ W₂) (Sum.inl i)
    let hleV₂ := (sumPadData D₁ D₂).image_subset_ambImage (sumPadOpens D₁ D₂ W₁ W₂) (Sum.inr j)
    let hpbi := (sumPadData D₁ D₂).isPullbackOf_ambientTriple_sigmaTriple (Sum.inl i)
    let hpbj := (sumPadData D₁ D₂).isPullbackOf_ambientTriple_sigmaTriple (Sum.inr j)
    let Hi : (((sumPadData D₁ D₂).embedding (Sum.inl i)).restrictedIdeal
          (W₁ i)).toAnalyticSpace.toKLocallyRingedSpace ⟶
        (BEDanFamStar.restrictedIdealOn (sumPadData D₁ D₂).sigmaTriple
          V₀).toAnalyticSpace.toKLocallyRingedSpace :=
      IdealSheaf.homOfPullbackEq _ _ (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap
        (sumPadData D₁ D₂).sigmaTriple V₀ ((sumPadData D₁ D₂).embedding (Sum.inl i)).ambientTriple
        m₁ (W₁ i) hleV₁ hpbi)
    let Hj : (((sumPadData D₁ D₂).embedding (Sum.inr j)).restrictedIdeal
          (W₂ j)).toAnalyticSpace.toKLocallyRingedSpace ⟶
        (BEDanFamStar.restrictedIdealOn (sumPadData D₁ D₂).sigmaTriple
          V₀).toAnalyticSpace.toKLocallyRingedSpace :=
      IdealSheaf.homOfPullbackEq _ _ (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap
        (sumPadData D₁ D₂).sigmaTriple V₀ ((sumPadData D₁ D₂).embedding (Sum.inr j)).ambientTriple
        m₂ (W₂ j) hleV₂ hpbj)
    let H₁ : (BEDanFamStar.restrictedIdealOn T₀ W₀).toAnalyticSpace.toKLocallyRingedSpace ⟶
        ((E₁.padAlong σ₁).restrictedIdeal (W₁ i)).toAnalyticSpace.toKLocallyRingedSpace :=
      IdealSheaf.homOfPullbackEq _ _ (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap
        (E₁.padAlong σ₁).ambientTriple (W₁ i) T₀ (a₁.comp ι₁) W₀ hle₁
        (isPullbackOf_shearInput_padAlong E₁ hO' hO'₁ σ₁ W₁'))
    let H₂ : (BEDanFamStar.restrictedIdealOn T₀ W₀).toAnalyticSpace.toKLocallyRingedSpace ⟶
        ((E₂.padAlong σ₂).restrictedIdeal (W₂ j)).toAnalyticSpace.toKLocallyRingedSpace :=
      IdealSheaf.homOfPullbackEq _ _ (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap
        (E₂.padAlong σ₂).ambientTriple (W₂ j) T₀ (a₂.comp (ι₂.comp g')) W₀ hle₂
        (isPullbackOf_shearInput_shear E₁ E₂ hO' hO'₁ hO'₂ σ₁ σ₂ W₁' W₂' g hI))
    let Hu : (BEDanFamStar.restrictedIdealOn T₀ W₀).toAnalyticSpace.toKLocallyRingedSpace ⟶
        (BEDanFamStar.restrictedIdealOn (sumPadData D₁ D₂).sigmaTriple
          V₀).toAnalyticSpace.toKLocallyRingedSpace :=
      IdealSheaf.homOfPullbackEq _ _ (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap
        (sumPadData D₁ D₂).sigmaTriple V₀ T₀ u W₀ huV hpu)
    let Hv : (BEDanFamStar.restrictedIdealOn T₀ W₀).toAnalyticSpace.toKLocallyRingedSpace ⟶
        (BEDanFamStar.restrictedIdealOn (sumPadData D₁ D₂).sigmaTriple
          V₀).toAnalyticSpace.toKLocallyRingedSpace :=
      IdealSheaf.homOfPullbackEq _ _ (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap
        (sumPadData D₁ D₂).sigmaTriple V₀ T₀ v W₀ hvV hpv)
    -- the squares of the open immersions
    have hsq₁ : resi ≫ mapstar = mapi ≫ Hi :=
      (sumPadData D₁ D₂).resIn_comp_localResolutionMapOn bed _ _ hbed (Sum.inl i)
    have hsq₂ : resj ≫ mapstar = mapj ≫ Hj :=
      (sumPadData D₁ D₂).resIn_comp_localResolutionMapOn bed _ _ hbed (Sum.inr j)
    have hφ₁ : e₁.inv ≫ ofRi ≫ resi = φu := Glue.isoOfRangeEq_inv_comp _ _ _
    have hφ₂ : e₂.inv ≫ ofRj' ≫ resj = φv := Glue.isoOfRangeEq_inv_comp _ _ _
    have hcm₁ : φu ≫ mapstar = map₀ ≫ Hu :=
      bed.localResolutionHomOn_comp_map (sumPadData D₁ D₂).sigmaTriple
        (sumPadData D₁ D₂).domBEDan_sigmaTriple V₀ hV₀ T₀ hT₀ u hu hpu W₀ hW₀ huV hbed
    have hcm₂ : φv ≫ mapstar = map₀ ≫ Hv :=
      bed.localResolutionHomOn_comp_map (sumPadData D₁ D₂).sigmaTriple
        (sumPadData D₁ D₂).domBEDan_sigmaTriple V₀ hV₀ T₀ hT₀ v hv hpv W₀ hW₀ hvV hbed
    have hHu : Hu = H₁ ≫ Hi :=
      (IdealSheaf.homOfPullbackEq_comp_of_comp_eq
        (AnalyticMap.restrictMap (a₁.comp ι₁) W₀ (W₁ i) hle₁)
        (AnalyticMap.restrictMap m₁ (W₁ i) V₀ hleV₁) (AnalyticMap.restrictMap u W₀ V₀ huV)
        (funext fun _ => rfl)
        (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap (E₁.padAlong σ₁).ambientTriple
          (W₁ i) T₀ (a₁.comp ι₁) W₀ hle₁ (isPullbackOf_shearInput_padAlong E₁ hO' hO'₁ σ₁ W₁'))
        (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap (sumPadData D₁ D₂).sigmaTriple V₀
          ((sumPadData D₁ D₂).embedding (Sum.inl i)).ambientTriple m₁ (W₁ i) hleV₁ hpbi)
        (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap (sumPadData D₁ D₂).sigmaTriple V₀
          T₀ u W₀ huV hpu)).symm
    have hHv : Hv = H₂ ≫ Hj :=
      (IdealSheaf.homOfPullbackEq_comp_of_comp_eq
        (AnalyticMap.restrictMap (a₂.comp (ι₂.comp g')) W₀ (W₂ j) hle₂)
        (AnalyticMap.restrictMap m₂ (W₂ j) V₀ hleV₂) (AnalyticMap.restrictMap v W₀ V₀ hvV)
        (funext fun _ => rfl)
        (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap (E₂.padAlong σ₂).ambientTriple
          (W₂ j) T₀ (a₂.comp (ι₂.comp g')) W₀ hle₂
          (isPullbackOf_shearInput_shear E₁ E₂ hO' hO'₁ hO'₂ σ₁ σ₂ W₁' W₂' g hI))
        (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap (sumPadData D₁ D₂).sigmaTriple V₀
          ((sumPadData D₁ D₂).embedding (Sum.inr j)).ambientTriple m₂ (W₂ j) hleV₂ hpbj)
        (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap (sumPadData D₁ D₂).sigmaTriple V₀
          T₀ v W₀ hvV hpv)).symm
    -- the two `H`'s are open immersions, hence monomorphisms
    have hoe₁ := isAnalyticOpenEmbedding_sigmaMk
      (fun k => pieceAmbient.{u} 𝕜 ((sumPadData D₁ D₂).embedding k).G) (Sum.inl i)
    have hoe₂ := isAnalyticOpenEmbedding_sigmaMk
      (fun k => pieceAmbient.{u} 𝕜 ((sumPadData D₁ D₂).embedding k).G) (Sum.inr j)
    have hinj₁ : Function.Injective (AnalyticMap.restrictMap m₁ (W₁ i) V₀ hleV₁) :=
      fun p q h => Subtype.ext (hoe₁.2 (congrArg Subtype.val h))
    have hinj₂ : Function.Injective (AnalyticMap.restrictMap m₂ (W₂ j) V₀ hleV₂) :=
      fun p q h => Subtype.ext (hoe₂.2 (congrArg Subtype.val h))
    have hmi : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion Hi.1 :=
      isOpenImmersion_homOfPullbackEq_of_injective _
        (AnalyticMap.isLocalDiffeomorph_restrictMap hoe₁.1 (W₁ i) V₀ hleV₁) hinj₁ _
    have hmj : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion Hj.1 :=
      isOpenImmersion_homOfPullbackEq_of_injective _
        (AnalyticMap.isLocalDiffeomorph_restrictMap hoe₂.1 (W₂ j) V₀ hleV₂) hinj₂ _
    have hA₁ : (e₁.inv ≫ ofRi) ≫ mapi = map₀ ≫ H₁ :=
      Hom.ext ((cancel_mono Hi.1).mp (congrArg Subtype.val
        (CategoryTheory.comp_eq_of_over_ambient (𝒞 := KLocallyRingedSpace.{u} 𝕜) e₁.inv ofRi mapi
          Hi resi mapstar hsq₁ φu hφ₁ map₀ Hu hcm₁ H₁ hHu)))
    have hA₂ : (e₂.inv ≫ ofRj') ≫ mapj = map₀ ≫ H₂ :=
      Hom.ext ((cancel_mono Hj.1).mp (congrArg Subtype.val
        (CategoryTheory.comp_eq_of_over_ambient (𝒞 := KLocallyRingedSpace.{u} 𝕜) e₂.inv ofRj' mapj
          Hj resj mapstar hsq₂ φv hφ₂ map₀ Hv hcm₂ H₂ hHv)))
    -- the read-down maps agree (`ShearOverX.lean`)
    have hX₀ : H₁ ≫ (E₁.padAlong σ₁).pieceOverHom (W₁ i) =
        H₂ ≫ (E₂.padAlong σ₂).pieceOverHom (W₂ j) :=
      homOfPullbackEq_restrictMap_comp_pieceOverHom_eq_of_shear E₁ E₂ hO' hO'₁ hO'₂ σ₁ σ₂ W₁' W₂' g
        W₀ (W₁ i) (W₂ j) hle₁ hle₂ hI hmor
    exact CategoryTheory.transition_over_eq_of_parts (𝒞 := KLocallyRingedSpace.{u} 𝕜) e₁.hom e₁.inv
      e₁.hom_inv_id e₂.inv ρ.hom ofRj ofRj' (restrictOpenIsoOfSetEq_hom_comp hset) ofRi mapi
      ((E₁.padAlong σ₁).pieceOverHom (W₁ i)) πi
      (((sumPadData D₁ D₂).embedding (Sum.inl i)).toSpaceMap_eq_comp_pieceOverHom bed (W₁ i)
        (hW₁ i))
      mapj ((E₂.padAlong σ₂).pieceOverHom (W₂ j)) πj
      (((sumPadData D₁ D₂).embedding (Sum.inr j)).toSpaceMap_eq_comp_pieceOverHom bed (W₂ j)
        (hW₂ j))
      map₀ H₁ H₂ hA₁ hA₂ hX₀
  · -- the members: the device's synchronisation read through the two identifications
    intro σ
    have c₁ : QuotientSpace.comap ofRj.1 (QuotientSpace.comap resj.1
          ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ)) =
        QuotientSpace.comap (ofRj ≫ resj).1
          ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ) :=
      (QuotientSpace.comap_comp _ _ _).symm
    have c₂ : QuotientSpace.comap θ.1 (QuotientSpace.comap (ofRj ≫ resj).1
          ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ)) =
        QuotientSpace.comap (θ ≫ ofRj ≫ resj).1
          ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ) :=
      (QuotientSpace.comap_comp _ _ _).symm
    have c₃ : QuotientSpace.comap (θ ≫ ofRj ≫ resj).1
          ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ) =
        QuotientSpace.comap (e₁.hom ≫ φu).1
          ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ) :=
      (congrArg (fun k : Yi.toKLocallyRingedSpace.restrictOpen Oi ⟶ Ystar.toKLocallyRingedSpace =>
          QuotientSpace.comap k.1 ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ)) k₁).trans
        (((QuotientSpace.comap_comp _ _ _).trans
          (congrArg (QuotientSpace.comap e₁.hom.1) (hmem σ).symm)).trans
          (QuotientSpace.comap_comp _ _ _).symm)
    have c₄ : QuotientSpace.comap (e₁.hom ≫ φu).1
          ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ) =
        QuotientSpace.comap ofRi.1 (QuotientSpace.comap resi.1
          ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ)) :=
      (congrArg (fun k : Yi.toKLocallyRingedSpace.restrictOpen Oi ⟶ Ystar.toKLocallyRingedSpace =>
          QuotientSpace.comap k.1 ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ)) k₂).trans
        (QuotientSpace.comap_comp _ _ _)
    exact ((congrArg (QuotientSpace.comap θ.1) c₁).trans c₂).trans (c₃.trans c₄)

end Mixed

end Hironaka.Manifold.LocalEmbeddingData

end
