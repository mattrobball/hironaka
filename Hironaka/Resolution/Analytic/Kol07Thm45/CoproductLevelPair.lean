/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductPadIdentity
public import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductGluedFamily
public import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductSumData
import Hironaka.AnalyticSpace.Glue.GlueIsoOver
import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductMixedTransition
import Hironaka.Resolution.Analytic.Kol07Thm45.Glue.OverFamilyChain
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalModel
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionHomOnComp
import Hironaka.Resolution.Analytic.Kol07Thm45.ResolutionOnMembers
import Hironaka.Resolution.Analytic.Kol07Thm45.RestrictSetIncl
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # The two-level comparison at the reading opens of the gluing

The padding identity `PadIdentityOn D σ Wp hWp bed hbed` (`CoproductPadIdentity.lean`; Kollár's
commutation with closed embeddings [Kol07, 34.4], the padding of [Kol07, Lemma 39]) compares the
coproduct local resolution of the padded datum `D.padAlongData σ` over padded reading opens `Wp`
with that of `D` over the PREIMAGE reading opens `padPreimageOpens σ Wp` (the zero extension pulled
back). The assembly of the exhaustion's chain families meets the datum's local resolution at the
reading opens `W` of the gluing datum, so it needs the identity read at any `W` equal to those
preimages (`PadReadingOpens.lean` chooses padded opens with prescribed preimages):
`exists_padIdentity_of_padPreimageOpens_eq` is the identity with `W` in place of
`padPreimageOpens σ Wp`, by substitution. `pieceDom_padAlongData` is the bookkeeping that the padded
piece's base open over `Wp i` is the datum's over the preimage open (`ambientPoint_padAlong`: the
padded ambient point is the zero extension of the ambient point).

* `LocalEmbeddingData.pieceDom_padAlongData`;
* `LocalEmbeddingData.exists_padIdentity_of_padPreimageOpens_eq`;
* `LocalEmbeddingData.exists_isoOver_resolutionOn_padPiece_of_members` — the leg at one level:
  the part of `resolutionOn` over a base open inside a piece's domain is the part of the PADDED
  piece's local resolution, over `X`, members carried along;
* `LocalEmbeddingData.exists_isoOver_resolutionOn_pair_of_forall_label` — the local pair identity
  of two adjacent levels: `leg₁ ≫ θ|P ≫ leg₂⁻¹` with the mixed-pair transition `θ`
  (`CoproductMixedTransition.lean`), label by label of the common padded run.
  `isIso_restrictTo_of_isIso` lives in `ResolutionOnMembers.lean`.

Used by `ExhaustionChainFamilies.lean`, `DoubledDatumLabels.lean` and
`CoproductGluedFamilyCompat.lean`. Not in the sources beyond the statements cited; bookkeeping.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set AnalyticSpace
open KLocallyRingedSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.LocalEmbeddingData

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜}

section PadTransport

variable {U : Set X} (D : LocalEmbeddingData 𝕜 X U) {n' : ℕ} (σ : Fin D.n ↪ Fin n')
  (Wp : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G))
  (hWp : ∀ i, IsCompact (closure (Wp i : Set (pieceAmbient.{u} 𝕜
    ((D.padAlongData σ).embedding i).G))))
  (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
  (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
  (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))

/-- **The padded piece's base open over the padded reading open is the datum's over the preimage
reading open** —
the padded ambient point of `y` is the zero extension of its ambient point
(`ambientPoint_padAlong`), so it lies in `Wp i` iff the ambient point lies in the preimage. -/
theorem pieceDom_padAlongData (i : D.ι) :
    (D.padAlongData σ).pieceDom i (Wp i) = D.pieceDom i (D.padPreimageOpens σ Wp i) := by
  apply Opens.ext
  change Subtype.val '' ((D.embedding i).padAlong σ).embPreimage (Wp i) =
    Subtype.val '' (D.embedding i).embPreimage (D.padPreimageOpens σ Wp i)
  congr 1
  ext y
  change ((D.embedding i).padAlong σ).ambientPoint y ∈ Wp i ↔
    (D.embedding i).ambientPoint y ∈ D.padPreimageOpens σ Wp i
  rw [PieceEmbedding.ambientPoint_padAlong]
  exact Iff.rfl

/-- **The padding identity read at ANY datum reading opens `W` equal to the preimages of the padded
ones** ([Kol07, 34.4]; `PadReadingOpens.lean` chooses such `Wp` for a given `W`): the data of
`PadIdentityOn` with `W` in place of
`padPreimageOpens σ Wp` — the order isomorphism of the label sets, the isomorphism `ψ` of the
coproduct local resolutions carrying the members label by label, and on every piece an
isomorphism over the piece with `resIn⁺ i ≫ ψ = ψᵢ ≫ resIn i`. -/
theorem exists_padIdentity_of_padPreimageOpens_eq (hpad : D.PadIdentityOn σ Wp hWp bed hbed)
    (hpre : D.padPreimageOpens σ Wp = W) :
    ∃ (o : (D.padAlongData σ).sigmaIndex bed Wp hWp ≃o D.sigmaIndex bed W hW)
      (ψ : bed.localResolutionOn (D.padAlongData σ).sigmaTriple
          (D.padAlongData σ).domBEDan_sigmaTriple ((D.padAlongData σ).ambImage Wp)
          ((D.padAlongData σ).isCompact_closure_ambImage Wp hWp) ⟶
          bed.localResolutionOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
          (D.isCompact_closure_ambImage W hW)),
      IsIso ψ ∧
      (∀ σp, QuotientSpace.comap ψ.1 (D.sigmaMembers bed W hW hbed (o σp)) =
        (D.padAlongData σ).sigmaMembers bed Wp hWp hbed σp) ∧
      ∀ i, ∃ ψᵢ : ((D.padAlongData σ).embedding i).localResolution bed (Wp i) (hWp i) ⟶
          (D.embedding i).localResolution bed (W i) (hW i),
        IsIso ψᵢ ∧
        ψᵢ ≫ (D.embedding i).localResolutionToPiece bed (W i) (hW i) =
          ((D.padAlongData σ).embedding i).localResolutionToPiece bed (Wp i) (hWp i) ∧
        (D.padAlongData σ).resIn bed Wp hWp hbed i ≫ ψ = ψᵢ ≫ D.resIn bed W hW hbed i := by
  subst hpre
  exact hpad

end PadTransport

section Leg

variable {U : Set X} (D : LocalEmbeddingData 𝕜 X U) {n' : ℕ} (σ : Fin D.n ↪ Fin n')
  (Wp : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G))
  (hWp : ∀ i, IsCompact (closure (Wp i : Set (pieceAmbient.{u} 𝕜
    ((D.padAlongData σ).embedding i).G))))
  (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing) (h : D.ResolutionGluesOn bed)

/-- **The leg of the two-level comparison at one level**: over a base open `P ⊆ U` inside the
domain of a piece `i`, an isomorphism over `X` from the part of `resolutionOn` over `P` to the
part of the PADDED piece's local resolution over `P`, carrying — for every label `l` of a labelled
family `Sm` on a space `Z` reached from the padded coproduct by `ρ` (the clauses `hlab`, `hlab'` of
a label embedding, `RunFamilyRestrict.lean`) — the trace of `Sm l` on the padded piece (along
`resIn⁺ i ≫ ρ`) to the member `A l` of the glued family (`A (lab k) = H (o k)`, `⊤` off the range):
the identification of the part with the part of the piece's local resolution
(`exists_isoOver_resolutionOn_localResolution`) followed by the restriction of the inverse of the
padding identity's piece isomorphism, with the members through the padding identity's member
clause `hmem`, its square, and the piece-compatibility clause `hH`. -/
theorem exists_isoOver_resolutionOn_padPiece_of_members
    (o : (D.padAlongData σ).sigmaIndex bed Wp hWp ≃o
      D.sigmaIndex bed h.some.W h.some.isCompact_closure_W)
    (ψ : bed.localResolutionOn (D.padAlongData σ).sigmaTriple
        (D.padAlongData σ).domBEDan_sigmaTriple ((D.padAlongData σ).ambImage Wp)
        ((D.padAlongData σ).isCompact_closure_ambImage Wp hWp) ⟶
        bed.localResolutionOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage h.some.W)
        (D.isCompact_closure_ambImage h.some.W h.some.isCompact_closure_W))
    (hmem : ∀ σp, QuotientSpace.comap ψ.1
        (D.sigmaMembers bed h.some.W h.some.isCompact_closure_W hbed (o σp)) =
      (D.padAlongData σ).sigmaMembers bed Wp hWp hbed σp)
    (hpiece : ∀ i, ∃ ψᵢ :
        ((D.padAlongData σ).embedding i).localResolution bed (Wp i) (hWp i) ⟶
        (D.embedding i).localResolution bed (h.some.W i) (h.some.isCompact_closure_W i),
      IsIso ψᵢ ∧
      ψᵢ ≫ (D.embedding i).localResolutionToPiece bed (h.some.W i) (h.some.isCompact_closure_W i) =
        ((D.padAlongData σ).embedding i).localResolutionToPiece bed (Wp i) (hWp i) ∧
      (D.padAlongData σ).resIn bed Wp hWp hbed i ≫ ψ =
        ψᵢ ≫ D.resIn bed h.some.W h.some.isCompact_closure_W hbed i)
    {Z : AnalyticSpace.{u} 𝕜}
    (ρ : bed.localResolutionOn (D.padAlongData σ).sigmaTriple
        (D.padAlongData σ).domBEDan_sigmaTriple ((D.padAlongData σ).ambImage Wp)
        ((D.padAlongData σ).isCompact_closure_ambImage Wp hWp) ⟶ Z)
    {Λ : Type u} (Sm : Λ → ClosedSubspace Z)
    (lab : (D.padAlongData σ).sigmaIndex bed Wp hWp → Λ)
    (hlab : ∀ k, QuotientSpace.comap ρ.1 (Sm (lab k)) =
      (D.padAlongData σ).sigmaMembers bed Wp hWp hbed k)
    (hlab' : ∀ l, l ∉ Set.range lab → QuotientSpace.comap ρ.1 (Sm l) = ⊤)
    (H : D.sigmaIndex bed h.some.W h.some.isCompact_closure_W →
      ClosedSubspace (D.resolutionOn bed))
    (hH : ∀ (i : D.ι) (P : Opens X), (P : Set X) ⊆ U → P ≤ D.pieceDom i (h.some.W i) →
      ∀ s : (D.resolutionOn bed).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
              Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P) ⟶
          ((D.embedding i).localResolution bed (h.some.W i)
              (h.some.isCompact_closure_W i)).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i)),
              Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i))⟩ P),
        IsIso s →
        ofRestrict _ _ ≫ D.resolutionOnToSpace bed =
          (s ≫ ofRestrict _ _) ≫
            (D.embedding i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i) →
        ∀ σ, QuotientSpace.comap s.1 (QuotientSpace.comap (ofRestrict _ _).1
            (pieceTrace D bed h.some hbed i σ)) =
          QuotientSpace.comap (ofRestrict _ _).1 (H σ))
    (A : Λ → ClosedSubspace (D.resolutionOn bed))
    (hA : ∀ k, A (lab k) = H (o k)) (hA' : ∀ l, l ∉ Set.range lab → A l = ⊤)
    (i : D.ι) (P : Opens X) (hPU : (P : Set X) ⊆ U) (hPi : P ≤ D.pieceDom i (h.some.W i)) :
    ∃ leg : (D.resolutionOn bed).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
            Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P) ⟶
        (((D.padAlongData σ).embedding i).localResolution bed (Wp i)
            (hWp i)).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.padAlongData σ).pieceToSpace bed i (Wp i)
              (hWp i)),
            Hom.continuous_toFun ((D.padAlongData σ).pieceToSpace bed i (Wp i) (hWp i))⟩ P),
      IsIso leg ∧
      ofRestrict _ _ ≫ D.resolutionOnToSpace bed =
        (leg ≫ ofRestrict _ _) ≫ (D.padAlongData σ).pieceToSpace bed i (Wp i) (hWp i) ∧
      ∀ l, QuotientSpace.comap (leg ≫ ofRestrict _ _).1
          (QuotientSpace.comap ((D.padAlongData σ).resIn bed Wp hWp hbed i ≫ ρ).1 (Sm l)) =
        QuotientSpace.comap (ofRestrict _ _).1 (A l) := by
  obtain ⟨s, hs, hsover⟩ := D.exists_isoOver_resolutionOn_localResolution bed h i P hPU hPi
  obtain ⟨ψᵢ, hψᵢ, hψpi, hψsq⟩ := hpiece i
  have hsK : IsIso s := hs
  obtain ⟨φ, hφ₁, hφ₂⟩ : ∃ φ : ((D.embedding i).localResolution bed (h.some.W i)
      (h.some.isCompact_closure_W i)).toKLocallyRingedSpace ⟶ (((D.padAlongData σ).embedding
      i).localResolution bed (Wp i) (hWp i)).toKLocallyRingedSpace,
      (ψᵢ : (((D.padAlongData σ).embedding i).localResolution bed (Wp i) (hWp
          i)).toKLocallyRingedSpace ⟶ ((D.embedding i).localResolution bed (h.some.W i)
          (h.some.isCompact_closure_W i)).toKLocallyRingedSpace) ≫ φ = 𝟙 _ ∧ φ ≫ (ψᵢ :
          (((D.padAlongData σ).embedding i).localResolution bed (Wp i) (hWp
          i)).toKLocallyRingedSpace ⟶ ((D.embedding i).localResolution bed (h.some.W i)
          (h.some.isCompact_closure_W i)).toKLocallyRingedSpace) = 𝟙 _ :=
    have hψK : @IsIso (KLocallyRingedSpace.{u} 𝕜) _ _ _ ψᵢ :=
      (Hom.isIso_iff_isIso_toKLocallyRingedSpace ψᵢ).mp hψᵢ
    ⟨@inv (KLocallyRingedSpace.{u} 𝕜) _ _ _ ψᵢ hψK,
      @IsIso.hom_inv_id (KLocallyRingedSpace.{u} 𝕜) _ _ _ ψᵢ hψK,
      @IsIso.inv_hom_id (KLocallyRingedSpace.{u} 𝕜) _ _ _ ψᵢ hψK⟩
  have hφiso : IsIso φ := ⟨⟨(ψᵢ : (((D.padAlongData σ).embedding i).localResolution bed (Wp i) (hWp
      i)).toKLocallyRingedSpace ⟶ ((D.embedding i).localResolution bed (h.some.W i)
      (h.some.isCompact_closure_W i)).toKLocallyRingedSpace), hφ₂, hφ₁⟩⟩
  have hpi : (ψᵢ : (((D.padAlongData σ).embedding i).localResolution bed (Wp i) (hWp
      i)).toKLocallyRingedSpace ⟶ ((D.embedding i).localResolution bed (h.some.W i)
      (h.some.isCompact_closure_W i)).toKLocallyRingedSpace) ≫ (D.embedding i).toSpaceMap bed
      (h.some.W i) (h.some.isCompact_closure_W i) = (D.padAlongData σ).pieceToSpace bed i (Wp i)
      (hWp i) :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun k :
        (((D.padAlongData σ).embedding i).localResolution bed (Wp i) (hWp i)).toKLocallyRingedSpace
            ⟶ (X.restrictSet (D.piece i)).toKLocallyRingedSpace =>
        k ≫ ofRestrict X.toKLocallyRingedSpace (openOf X (D.piece
            i)))
      hψpi)
  have hinvpi : φ ≫ (D.padAlongData σ).pieceToSpace bed i (Wp i) (hWp i) = (D.embedding
      i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i) := by
    rw [← hpi]
    exact (Category.assoc φ (ψᵢ : (((D.padAlongData σ).embedding i).localResolution bed (Wp i) (hWp
        i)).toKLocallyRingedSpace ⟶ ((D.embedding i).localResolution bed (h.some.W i)
        (h.some.isCompact_closure_W i)).toKLocallyRingedSpace) _).symm.trans
      (by rw [hφ₂]; exact Category.id_comp _)
  have hmap : ∀ a ∈ Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed
      (h.some.W i)
      (h.some.isCompact_closure_W i)), Hom.continuous_toFun ((D.embedding i).toSpaceMap bed
      (h.some.W i) (h.some.isCompact_closure_W i))⟩ P,
      KLocallyRingedSpace.Hom.toFun φ a ∈ Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
          ((D.padAlongData σ).pieceToSpace bed i (Wp i) (hWp
          i)), Hom.continuous_toFun ((D.padAlongData σ).pieceToSpace bed i (Wp i) (hWp i))⟩ P := by
    intro a ha
    change KLocallyRingedSpace.Hom.toFun ((D.padAlongData σ).pieceToSpace bed i (Wp i) (hWp i))
        (KLocallyRingedSpace.Hom.toFun φ a) ∈ P
    exact Set.mem_of_eq_of_mem (congrArg (fun k => KLocallyRingedSpace.Hom.toFun k a) hinvpi) ha
  have hmap' : ∀ b ∈ Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
      ((D.padAlongData σ).pieceToSpace bed i (Wp i) (hWp i)),
      Hom.continuous_toFun ((D.padAlongData σ).pieceToSpace bed i (Wp i) (hWp i))⟩ P,
      KLocallyRingedSpace.Hom.toFun (inv φ) b ∈ Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
          ((D.embedding i).toSpaceMap bed (h.some.W i)
          (h.some.isCompact_closure_W i)), Hom.continuous_toFun ((D.embedding i).toSpaceMap bed
          (h.some.W i) (h.some.isCompact_closure_W i))⟩ P := by
    intro b hb
    rw [IsIso.inv_eq_of_hom_inv_id hφ₂]
    change KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
        (h.some.isCompact_closure_W i))
        (KLocallyRingedSpace.Hom.toFun (ψᵢ : (((D.padAlongData σ).embedding i).localResolution bed
            (Wp i) (hWp
        i)).toKLocallyRingedSpace ⟶ ((D.embedding i).localResolution bed (h.some.W i)
        (h.some.isCompact_closure_W i)).toKLocallyRingedSpace) b) ∈ P
    exact Set.mem_of_eq_of_mem (congrArg (fun k => KLocallyRingedSpace.Hom.toFun k b) hpi) hb
  obtain ⟨r, hr⟩ : ∃ r : ((D.embedding i).localResolution bed (h.some.W i)
      (h.some.isCompact_closure_W i)).toKLocallyRingedSpace.restrictOpen (Opens.comap
          ⟨KLocallyRingedSpace.Hom.toFun
      ((D.embedding i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i)),
      Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W
      i))⟩ P) ⟶
      (((D.padAlongData σ).embedding i).localResolution bed (Wp i) (hWp
          i)).toKLocallyRingedSpace.restrictOpen (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
              ((D.padAlongData
          σ).pieceToSpace bed i (Wp i) (hWp i)), Hom.continuous_toFun ((D.padAlongData
          σ).pieceToSpace bed i (Wp i) (hWp i))⟩ P),
      r = Hom.restrictTo φ _ _ hmap := ⟨_, rfl⟩
  have hr_ofR : ∀ {Z : KLocallyRingedSpace.{u} 𝕜} (g : (((D.padAlongData σ).embedding
      i).localResolution bed (Wp i) (hWp i)).toKLocallyRingedSpace ⟶ Z),
      r ≫ ofRestrict (((D.padAlongData σ).embedding i).localResolution bed (Wp i) (hWp
          i)).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
              ((D.padAlongData σ).pieceToSpace bed i
          (Wp i) (hWp i)), Hom.continuous_toFun ((D.padAlongData σ).pieceToSpace bed i (Wp i) (hWp
          i))⟩ P) ≫ g = ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
          (h.some.isCompact_closure_W i)).toKLocallyRingedSpace (Opens.comap
              ⟨KLocallyRingedSpace.Hom.toFun
          ((D.embedding i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i)),
          Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
          (h.some.isCompact_closure_W i))⟩ P) ≫ φ ≫ g := fun g => by
    rw [hr, ← Category.assoc, Hom.restrictTo_comp_ofRestrict, Category.assoc]
  have hr_iso : IsIso r := by
    rw [hr]
    exact isIso_restrictTo_of_isIso φ _ _ hmap hmap'
  refine ⟨s ≫ r, @IsIso.comp_isIso _ _ _ _ _ s r hsK hr_iso, ?_, ?_⟩
  · -- over `X`
    have h_a : (s ≫ ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
        (h.some.isCompact_closure_W i)).toKLocallyRingedSpace (Opens.comap
            ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding
        i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i)), Hom.continuous_toFun
        ((D.embedding i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i))⟩ P)) ≫
        (D.embedding i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i) = s ≫ ofRestrict
        ((D.embedding i).localResolution bed (h.some.W i) (h.some.isCompact_closure_W
        i)).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
            ((D.embedding i).toSpaceMap bed (h.some.W
        i) (h.some.isCompact_closure_W i)), Hom.continuous_toFun ((D.embedding i).toSpaceMap bed
        (h.some.W i) (h.some.isCompact_closure_W i))⟩ P) ≫ φ ≫ (D.padAlongData σ).pieceToSpace bed
        i (Wp i) (hWp i) := by
      rw [Category.assoc, hinvpi]
    have h_b : s ≫ ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
        (h.some.isCompact_closure_W i)).toKLocallyRingedSpace (Opens.comap
            ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding
        i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i)), Hom.continuous_toFun
        ((D.embedding i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i))⟩ P) ≫ φ ≫
        (D.padAlongData σ).pieceToSpace bed i (Wp i) (hWp i) = ((s ≫ r) ≫ ofRestrict
        (((D.padAlongData σ).embedding i).localResolution bed (Wp i) (hWp i)).toKLocallyRingedSpace
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.padAlongData σ).pieceToSpace bed i (Wp i)
            (hWp i)),
        Hom.continuous_toFun ((D.padAlongData σ).pieceToSpace bed i (Wp i) (hWp i))⟩ P)) ≫
        (D.padAlongData σ).pieceToSpace bed i (Wp i) (hWp i) := by
      simp only [Category.assoc]
      rw [hr_ofR]
    exact hsover.trans (h_a.trans h_b)
  · intro l
    by_cases hl : l ∈ Set.range lab
    · obtain ⟨k, rfl⟩ := hl
      have h1 : QuotientSpace.comap ((D.padAlongData σ).resIn bed Wp hWp hbed i ≫ ρ).1 (Sm (lab k))
          = QuotientSpace.comap (ψᵢ : (((D.padAlongData σ).embedding i).localResolution bed (Wp i)
          (hWp i)).toKLocallyRingedSpace ⟶ ((D.embedding i).localResolution bed (h.some.W i)
          (h.some.isCompact_closure_W i)).toKLocallyRingedSpace).1 (pieceTrace D bed h.some hbed i
          (o k)) :=
        calc QuotientSpace.comap ((D.padAlongData σ).resIn bed Wp hWp hbed i ≫ ρ).1 (Sm (lab k))
            = QuotientSpace.comap ((D.padAlongData σ).resIn bed Wp hWp hbed i).1
                (QuotientSpace.comap ρ.1 (Sm (lab k))) :=
              QuotientSpace.comap_comp ρ.1 (Sm (lab k)) ((D.padAlongData σ).resIn bed Wp hWp hbed
                  i).1
          _ = QuotientSpace.comap ((D.padAlongData σ).resIn bed Wp hWp hbed i).1
              (QuotientSpace.comap ψ.1
                (D.sigmaMembers bed h.some.W h.some.isCompact_closure_W hbed (o k))) := by
              rw [hlab k, hmem k]
          _ = QuotientSpace.comap ((D.padAlongData σ).resIn bed Wp hWp hbed i ≫ ψ).1
                (D.sigmaMembers bed h.some.W h.some.isCompact_closure_W hbed (o k)) :=
              (QuotientSpace.comap_comp ψ.1
                (D.sigmaMembers bed h.some.W h.some.isCompact_closure_W hbed (o k))
                    ((D.padAlongData σ).resIn bed Wp hWp hbed i).1).symm
          _ = QuotientSpace.comap ((ψᵢ : (((D.padAlongData σ).embedding i).localResolution bed (Wp
              i) (hWp i)).toKLocallyRingedSpace ⟶ ((D.embedding i).localResolution bed (h.some.W i)
              (h.some.isCompact_closure_W i)).toKLocallyRingedSpace) ≫ D.resIn bed h.some.W
              h.some.isCompact_closure_W hbed i).1
                (D.sigmaMembers bed h.some.W h.some.isCompact_closure_W hbed (o k)) := by
              rw [hψsq]
          _ = QuotientSpace.comap (ψᵢ : (((D.padAlongData σ).embedding i).localResolution bed (Wp
              i) (hWp i)).toKLocallyRingedSpace ⟶ ((D.embedding i).localResolution bed (h.some.W i)
              (h.some.isCompact_closure_W i)).toKLocallyRingedSpace).1 (pieceTrace D bed h.some
              hbed i (o k)) :=
              QuotientSpace.comap_comp (D.resIn bed h.some.W h.some.isCompact_closure_W hbed i).1
                (D.sigmaMembers bed h.some.W h.some.isCompact_closure_W hbed (o k)) (ψᵢ :
                    (((D.padAlongData σ).embedding i).localResolution bed (Wp i) (hWp
                    i)).toKLocallyRingedSpace ⟶ ((D.embedding i).localResolution bed (h.some.W i)
                    (h.some.isCompact_closure_W i)).toKLocallyRingedSpace).1
      have hr₀ : r ≫ ofRestrict (((D.padAlongData σ).embedding i).localResolution bed (Wp i) (hWp
          i)).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
              ((D.padAlongData σ).pieceToSpace bed i
          (Wp i) (hWp i)), Hom.continuous_toFun ((D.padAlongData σ).pieceToSpace bed i (Wp i) (hWp
          i))⟩ P) = ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
          (h.some.isCompact_closure_W i)).toKLocallyRingedSpace (Opens.comap
              ⟨KLocallyRingedSpace.Hom.toFun
          ((D.embedding i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i)),
          Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
          (h.some.isCompact_closure_W i))⟩ P) ≫ φ := by
        rw [hr]
        exact Hom.restrictTo_comp_ofRestrict φ _ _ hmap
      have hleg : (s ≫ r) ≫ ofRestrict (((D.padAlongData σ).embedding i).localResolution bed (Wp i)
          (hWp i)).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
              ((D.padAlongData σ).pieceToSpace
          bed i (Wp i) (hWp i)), Hom.continuous_toFun ((D.padAlongData σ).pieceToSpace bed i (Wp i)
          (hWp i))⟩ P) = s ≫ ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
          (h.some.isCompact_closure_W i)).toKLocallyRingedSpace (Opens.comap
              ⟨KLocallyRingedSpace.Hom.toFun
          ((D.embedding i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i)),
          Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
          (h.some.isCompact_closure_W i))⟩ P) ≫ φ :=
        (Category.assoc s r (ofRestrict (((D.padAlongData σ).embedding i).localResolution bed (Wp
            i) (hWp i)).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
                ((D.padAlongData
            σ).pieceToSpace bed i (Wp i) (hWp i)), Hom.continuous_toFun ((D.padAlongData
            σ).pieceToSpace bed i (Wp i) (hWp i))⟩ P))).trans (congrArg (fun k => s ≫ k) hr₀)
      have hR' : (s ≫ ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
          (h.some.isCompact_closure_W i)).toKLocallyRingedSpace (Opens.comap
              ⟨KLocallyRingedSpace.Hom.toFun
          ((D.embedding i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i)),
          Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
          (h.some.isCompact_closure_W i))⟩ P) ≫ φ) ≫ (ψᵢ : (((D.padAlongData σ).embedding
          i).localResolution bed (Wp i) (hWp i)).toKLocallyRingedSpace ⟶ ((D.embedding
          i).localResolution bed (h.some.W i) (h.some.isCompact_closure_W
          i)).toKLocallyRingedSpace) = s ≫ ofRestrict ((D.embedding i).localResolution bed
          (h.some.W i) (h.some.isCompact_closure_W i)).toKLocallyRingedSpace (Opens.comap
          ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
              (h.some.isCompact_closure_W i)),
          Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
          (h.some.isCompact_closure_W i))⟩ P) :=
        (Category.assoc s (ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
            (h.some.isCompact_closure_W i)).toKLocallyRingedSpace (Opens.comap
                ⟨KLocallyRingedSpace.Hom.toFun
            ((D.embedding i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i)),
            Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
            (h.some.isCompact_closure_W i))⟩ P) ≫ φ) (ψᵢ : (((D.padAlongData σ).embedding
            i).localResolution bed (Wp i) (hWp i)).toKLocallyRingedSpace ⟶ ((D.embedding
            i).localResolution bed (h.some.W i) (h.some.isCompact_closure_W
            i)).toKLocallyRingedSpace)).trans
          ((congrArg (fun k => s ≫ k) (Category.assoc (ofRestrict ((D.embedding i).localResolution
              bed (h.some.W i) (h.some.isCompact_closure_W i)).toKLocallyRingedSpace (Opens.comap
              ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                  (h.some.isCompact_closure_W
              i)), Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
              (h.some.isCompact_closure_W i))⟩ P)) φ (ψᵢ : (((D.padAlongData σ).embedding
              i).localResolution bed (Wp i) (hWp i)).toKLocallyRingedSpace ⟶ ((D.embedding
              i).localResolution bed (h.some.W i) (h.some.isCompact_closure_W
              i)).toKLocallyRingedSpace))).trans
            ((congrArg (fun k => s ≫ ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
                (h.some.isCompact_closure_W i)).toKLocallyRingedSpace (Opens.comap
                    ⟨KLocallyRingedSpace.Hom.toFun
                ((D.embedding i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i)),
                Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i))⟩ P) ≫ k) hφ₂).trans
              (congrArg (fun k => s ≫ k) (Category.comp_id (ofRestrict ((D.embedding
                  i).localResolution bed (h.some.W i) (h.some.isCompact_closure_W
                  i)).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
                      ((D.embedding i).toSpaceMap bed
                  (h.some.W i) (h.some.isCompact_closure_W i)), Hom.continuous_toFun ((D.embedding
                  i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i))⟩ P))))))
      have hval : (((s ≫ r) ≫ ofRestrict (((D.padAlongData σ).embedding i).localResolution bed (Wp
          i) (hWp i)).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
              ((D.padAlongData
          σ).pieceToSpace bed i (Wp i) (hWp i)), Hom.continuous_toFun ((D.padAlongData
          σ).pieceToSpace bed i (Wp i) (hWp i))⟩ P)) ≫ (ψᵢ : (((D.padAlongData σ).embedding
          i).localResolution bed (Wp i) (hWp i)).toKLocallyRingedSpace ⟶ ((D.embedding
          i).localResolution bed (h.some.W i) (h.some.isCompact_closure_W
          i)).toKLocallyRingedSpace)).1 = (s ≫ ofRestrict ((D.embedding i).localResolution bed
          (h.some.W i) (h.some.isCompact_closure_W i)).toKLocallyRingedSpace (Opens.comap
          ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
              (h.some.isCompact_closure_W i)),
          Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
          (h.some.isCompact_closure_W i))⟩ P)).1 :=
        congrArg Subtype.val ((congrArg (fun k : (D.resolutionOn
            bed).toKLocallyRingedSpace.restrictOpen (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
                (D.resolutionOnToSpace
            bed), Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P) ⟶ (((D.padAlongData
            σ).embedding i).localResolution bed (Wp i) (hWp i)).toKLocallyRingedSpace => k ≫ (ψᵢ :
            (((D.padAlongData σ).embedding i).localResolution bed (Wp i) (hWp
            i)).toKLocallyRingedSpace ⟶ ((D.embedding i).localResolution bed (h.some.W i)
            (h.some.isCompact_closure_W i)).toKLocallyRingedSpace)) hleg).trans hR')
      exact (congrArg (fun J => QuotientSpace.comap ((s ≫ r) ≫ ofRestrict (((D.padAlongData
          σ).embedding i).localResolution bed (Wp i) (hWp i)).toKLocallyRingedSpace (Opens.comap
          ⟨KLocallyRingedSpace.Hom.toFun ((D.padAlongData σ).pieceToSpace bed i (Wp i) (hWp i)),
              Hom.continuous_toFun
          ((D.padAlongData σ).pieceToSpace bed i (Wp i) (hWp i))⟩ P)).1 J) h1).trans
        ((QuotientSpace.comap_comp (ψᵢ : (((D.padAlongData σ).embedding i).localResolution bed (Wp
            i) (hWp i)).toKLocallyRingedSpace ⟶ ((D.embedding i).localResolution bed (h.some.W i)
            (h.some.isCompact_closure_W i)).toKLocallyRingedSpace).1 (pieceTrace D bed h.some hbed
            i (o k)) ((s ≫ r) ≫ ofRestrict (((D.padAlongData σ).embedding i).localResolution bed
            (Wp i) (hWp i)).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
                ((D.padAlongData
            σ).pieceToSpace bed i (Wp i) (hWp i)), Hom.continuous_toFun ((D.padAlongData
            σ).pieceToSpace bed i (Wp i) (hWp i))⟩ P)).1).symm.trans
          ((congrArg (fun m => QuotientSpace.comap m (pieceTrace D bed h.some hbed i (o k)))
              hval).trans
            ((QuotientSpace.comap_comp (ofRestrict ((D.embedding i).localResolution bed (h.some.W
                i) (h.some.isCompact_closure_W i)).toKLocallyRingedSpace (Opens.comap
                    ⟨KLocallyRingedSpace.Hom.toFun
                ((D.embedding i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i)),
                Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i))⟩ P)).1 (pieceTrace D bed h.some hbed i (o k))
                s.1).trans
              ((hH i P hPU hPi s hs hsover (o k)).trans
                (congrArg (QuotientSpace.comap (ofRestrict (D.resolutionOn
                    bed).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
                        (D.resolutionOnToSpace bed),
                    Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P)).1) (hA k).symm)))))
    · -- off the range: both sides are the unit ideal
      have h2 : QuotientSpace.comap ((D.padAlongData σ).resIn bed Wp hWp hbed i ≫ ρ).1 (Sm l) = ⊤ :=
        (QuotientSpace.comap_comp ρ.1 (Sm l) ((D.padAlongData σ).resIn bed Wp hWp hbed i).1).trans
          (by rw [hlab' l hl]; exact QuotientSpace.comap_top _)
      rw [h2, hA' l hl, QuotientSpace.comap_top, QuotientSpace.comap_top]

end Leg

section LocalPair

variable {U₁ U₂ : Set X} (D₁ : LocalEmbeddingData 𝕜 X U₁) (D₂ : LocalEmbeddingData 𝕜 X U₂)
  (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
  (hind : LocalResolutionIndependentOn X bed)
  (h₁ : D₁.ResolutionGluesOn bed) (h₂ : D₂.ResolutionGluesOn bed)
  (W₁ : ∀ i : D₁.ι, Opens (pieceAmbient.{u} 𝕜 ((D₁.padLeftData D₂.n).embedding i).G))
  (hW₁ : ∀ i, IsCompact (closure (W₁ i : Set (pieceAmbient.{u} 𝕜
    ((D₁.padLeftData D₂.n).embedding i).G))))
  (W₂ : ∀ j : D₂.ι, Opens (pieceAmbient.{u} 𝕜 ((D₂.padRightData D₁.n).embedding j).G))
  (hW₂ : ∀ j, IsCompact (closure (W₂ j : Set (pieceAmbient.{u} 𝕜
    ((D₂.padRightData D₁.n).embedding j).G))))
  (o₁ : (D₁.padLeftData D₂.n).sigmaIndex bed W₁ hW₁ ≃o
    D₁.sigmaIndex bed h₁.some.W h₁.some.isCompact_closure_W)
  (ψ₁ : bed.localResolutionOn (D₁.padLeftData D₂.n).sigmaTriple
      (D₁.padLeftData D₂.n).domBEDan_sigmaTriple ((D₁.padLeftData D₂.n).ambImage W₁)
      ((D₁.padLeftData D₂.n).isCompact_closure_ambImage W₁ hW₁) ⟶
      bed.localResolutionOn D₁.sigmaTriple D₁.domBEDan_sigmaTriple (D₁.ambImage h₁.some.W)
      (D₁.isCompact_closure_ambImage h₁.some.W h₁.some.isCompact_closure_W))
  (hmem₁ : ∀ σp, QuotientSpace.comap ψ₁.1
      (D₁.sigmaMembers bed h₁.some.W h₁.some.isCompact_closure_W hbed (o₁ σp)) =
    (D₁.padLeftData D₂.n).sigmaMembers bed W₁ hW₁ hbed σp)
  (hpiece₁ : ∀ i, ∃ ψᵢ :
      ((D₁.padLeftData D₂.n).embedding i).localResolution bed (W₁ i) (hW₁ i) ⟶
      (D₁.embedding i).localResolution bed (h₁.some.W i) (h₁.some.isCompact_closure_W i),
    IsIso ψᵢ ∧
    ψᵢ ≫ (D₁.embedding i).localResolutionToPiece bed (h₁.some.W i) (h₁.some.isCompact_closure_W i) =
      ((D₁.padLeftData D₂.n).embedding i).localResolutionToPiece bed (W₁ i) (hW₁ i) ∧
    (D₁.padLeftData D₂.n).resIn bed W₁ hW₁ hbed i ≫ ψ₁ =
      ψᵢ ≫ D₁.resIn bed h₁.some.W h₁.some.isCompact_closure_W hbed i)
  (o₂ : (D₂.padRightData D₁.n).sigmaIndex bed W₂ hW₂ ≃o
    D₂.sigmaIndex bed h₂.some.W h₂.some.isCompact_closure_W)
  (ψ₂ : bed.localResolutionOn (D₂.padRightData D₁.n).sigmaTriple
      (D₂.padRightData D₁.n).domBEDan_sigmaTriple ((D₂.padRightData D₁.n).ambImage W₂)
      ((D₂.padRightData D₁.n).isCompact_closure_ambImage W₂ hW₂) ⟶
      bed.localResolutionOn D₂.sigmaTriple D₂.domBEDan_sigmaTriple (D₂.ambImage h₂.some.W)
      (D₂.isCompact_closure_ambImage h₂.some.W h₂.some.isCompact_closure_W))
  (hmem₂ : ∀ σp, QuotientSpace.comap ψ₂.1
      (D₂.sigmaMembers bed h₂.some.W h₂.some.isCompact_closure_W hbed (o₂ σp)) =
    (D₂.padRightData D₁.n).sigmaMembers bed W₂ hW₂ hbed σp)
  (hpiece₂ : ∀ j, ∃ ψⱼ :
      ((D₂.padRightData D₁.n).embedding j).localResolution bed (W₂ j) (hW₂ j) ⟶
      (D₂.embedding j).localResolution bed (h₂.some.W j) (h₂.some.isCompact_closure_W j),
    IsIso ψⱼ ∧
    ψⱼ ≫ (D₂.embedding j).localResolutionToPiece bed (h₂.some.W j) (h₂.some.isCompact_closure_W j) =
      ((D₂.padRightData D₁.n).embedding j).localResolutionToPiece bed (W₂ j) (hW₂ j) ∧
    (D₂.padRightData D₁.n).resIn bed W₂ hW₂ hbed j ≫ ψ₂ =
      ψⱼ ≫ D₂.resIn bed h₂.some.W h₂.some.isCompact_closure_W hbed j)
  (lab₁ : (D₁.padLeftData D₂.n).sigmaIndex bed W₁ hW₁ ↪o
    (sumPadData D₁ D₂).sigmaIndex bed (sumPadOpens D₁ D₂ W₁ W₂)
      (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂))
  (hlab₁ : ∀ k, QuotientSpace.comap (sumInlResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed).1
      ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
        (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed (lab₁ k)) =
    (D₁.padLeftData D₂.n).sigmaMembers bed W₁ hW₁ hbed k)
  (hlab₁' : ∀ σ, σ ∉ Set.range lab₁ →
    QuotientSpace.comap (sumInlResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed).1
      ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
        (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ) = ⊤)
  (lab₂ : (D₂.padRightData D₁.n).sigmaIndex bed W₂ hW₂ ↪o
    (sumPadData D₁ D₂).sigmaIndex bed (sumPadOpens D₁ D₂ W₁ W₂)
      (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂))
  (hlab₂ : ∀ k, QuotientSpace.comap (sumInrResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed).1
      ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
        (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed (lab₂ k)) =
    (D₂.padRightData D₁.n).sigmaMembers bed W₂ hW₂ hbed k)
  (hlab₂' : ∀ σ, σ ∉ Set.range lab₂ →
    QuotientSpace.comap (sumInrResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed).1
      ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
        (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ) = ⊤)
  (hpre₁ : D₁.padPreimageOpens (Fin.castAddEmb D₂.n) W₁ = h₁.some.W)
  (hpre₂ : D₂.padPreimageOpens (Fin.natAddEmb D₁.n) W₂ = h₂.some.W)
  (H₁ : D₁.sigmaIndex bed h₁.some.W h₁.some.isCompact_closure_W →
    ClosedSubspace (D₁.resolutionOn bed))
  (hH₁ : ∀ (i : D₁.ι) (P : Opens X), (P : Set X) ⊆ U₁ → P ≤ D₁.pieceDom i (h₁.some.W i) →
    ∀ s : (D₁.resolutionOn bed).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D₁.resolutionOnToSpace bed),
            Hom.continuous_toFun (D₁.resolutionOnToSpace bed)⟩ P) ⟶
        ((D₁.embedding i).localResolution bed (h₁.some.W i)
            (h₁.some.isCompact_closure_W i)).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D₁.embedding i).toSpaceMap bed (h₁.some.W i)
              (h₁.some.isCompact_closure_W i)),
            Hom.continuous_toFun ((D₁.embedding i).toSpaceMap bed (h₁.some.W i)
              (h₁.some.isCompact_closure_W i))⟩ P),
      IsIso s →
      ofRestrict _ _ ≫ D₁.resolutionOnToSpace bed =
        (s ≫ ofRestrict _ _) ≫
          (D₁.embedding i).toSpaceMap bed (h₁.some.W i) (h₁.some.isCompact_closure_W i) →
      ∀ σ, QuotientSpace.comap s.1 (QuotientSpace.comap (ofRestrict _ _).1
          (pieceTrace D₁ bed h₁.some hbed i σ)) =
        QuotientSpace.comap (ofRestrict _ _).1 (H₁ σ))
  (H₂ : D₂.sigmaIndex bed h₂.some.W h₂.some.isCompact_closure_W →
    ClosedSubspace (D₂.resolutionOn bed))
  (hH₂ : ∀ (j : D₂.ι) (P : Opens X), (P : Set X) ⊆ U₂ → P ≤ D₂.pieceDom j (h₂.some.W j) →
    ∀ s : (D₂.resolutionOn bed).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D₂.resolutionOnToSpace bed),
            Hom.continuous_toFun (D₂.resolutionOnToSpace bed)⟩ P) ⟶
        ((D₂.embedding j).localResolution bed (h₂.some.W j)
            (h₂.some.isCompact_closure_W j)).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D₂.embedding j).toSpaceMap bed (h₂.some.W j)
              (h₂.some.isCompact_closure_W j)),
            Hom.continuous_toFun ((D₂.embedding j).toSpaceMap bed (h₂.some.W j)
              (h₂.some.isCompact_closure_W j))⟩ P),
      IsIso s →
      ofRestrict _ _ ≫ D₂.resolutionOnToSpace bed =
        (s ≫ ofRestrict _ _) ≫
          (D₂.embedding j).toSpaceMap bed (h₂.some.W j) (h₂.some.isCompact_closure_W j) →
      ∀ σ, QuotientSpace.comap s.1 (QuotientSpace.comap (ofRestrict _ _).1
          (pieceTrace D₂ bed h₂.some hbed j σ)) =
        QuotientSpace.comap (ofRestrict _ _).1 (H₂ σ))
  (A₁ : (sumPadData D₁ D₂).sigmaIndex bed (sumPadOpens D₁ D₂ W₁ W₂)
      (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) →
    ClosedSubspace (D₁.resolutionOn bed))
  (hA₁ : ∀ k, A₁ (lab₁ k) = H₁ (o₁ k)) (hA₁' : ∀ σ, σ ∉ Set.range lab₁ → A₁ σ = ⊤)
  (A₂ : (sumPadData D₁ D₂).sigmaIndex bed (sumPadOpens D₁ D₂ W₁ W₂)
      (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) →
    ClosedSubspace (D₂.resolutionOn bed))
  (hA₂ : ∀ k, A₂ (lab₂ k) = H₂ (o₂ k)) (hA₂' : ∀ σ, σ ∉ Set.range lab₂ → A₂ σ = ⊤)

include hbed h₁ h₂ o₁ ψ₁ hmem₁ hpiece₁ o₂ ψ₂ hmem₂ hpiece₂ lab₁ hlab₁ hlab₁' lab₂ hlab₂ hlab₂'
    hpre₁ hpre₂
  H₁ hH₁ H₂ hH₂ hA₁ hA₁' hA₂ hA₂' in
/-- **The local pair identity** — the per-point supply for the exhaustion's transitions
(`compatClosedSubspaces_pair_of_forall_exists_isoOver`): at a point `x` of the overlap of the two
levels, an open `P ∋ x` inside a prescribed open `O ⊆ U₁ ∩ U₂` and an isomorphism `θ` over `X`
between the parts of the two glued resolutions over `P` carrying, for EVERY common label, the
second level's member to the first's — the chain
`resolutionOn₁|P ≅ Y₁ᵢ|P ≅ Y₁ᵢ⁺|P ≅ Y₂ⱼ⁺|P ≅ Y₂ⱼ|P ≅ resolutionOn₂|P` (the piece-compatibility
clause, the padding identity's piece isomorphism, the mixed-pair transition, and back) with the
members traced through the padding identity's member clause, `comap_resIn_sumPadData_inl/_inr`
(`LocalResolutionHomOnComp.lean`) and the label embeddings (the `⊤` off-range clauses giving the
empty cases), and the transition's member clause; the two levels' padded reading opens read the
levels' reading opens (`hpre₁`, `hpre₂`). -/
theorem exists_isoOver_resolutionOn_pair_of_forall_label (O : Opens X)
    (hO : (O : Set X) ⊆ U₁ ∩ U₂) (x : X) (hx : x ∈ O) :
    ∃ (P : Opens X) (_ : P ≤ O), x ∈ P ∧
      ∃ θ : (D₁.resolutionOn bed).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D₁.resolutionOnToSpace bed),
              Hom.continuous_toFun (D₁.resolutionOnToSpace bed)⟩ P) ⟶
          (D₂.resolutionOn bed).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D₂.resolutionOnToSpace bed),
              Hom.continuous_toFun (D₂.resolutionOnToSpace bed)⟩ P),
        IsIso θ ∧
        ofRestrict (D₁.resolutionOn bed).toKLocallyRingedSpace _ ≫ D₁.resolutionOnToSpace bed =
          (θ ≫ ofRestrict (D₂.resolutionOn bed).toKLocallyRingedSpace _) ≫
            D₂.resolutionOnToSpace bed ∧
        ∀ σ, QuotientSpace.comap
            (θ ≫ ofRestrict (D₂.resolutionOn bed).toKLocallyRingedSpace _).1 (A₂ σ) =
          QuotientSpace.comap (ofRestrict (D₁.resolutionOn bed).toKLocallyRingedSpace _).1
            (A₁ σ) := by
  obtain ⟨i, hxi⟩ : ∃ i, x ∈ D₁.pieceDom i (h₁.some.W i) := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (D₁.subset_iUnion_inner (hO hx).1)
    exact ⟨i, h₁.some.closure_inner_subset_pieceDom i (subset_closure hi)⟩
  obtain ⟨j, hxj⟩ : ∃ j, x ∈ D₂.pieceDom j (h₂.some.W j) := by
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (D₂.subset_iUnion_inner (hO hx).2)
    exact ⟨j, h₂.some.closure_inner_subset_pieceDom j (subset_closure hj)⟩
  have hd₁ : ∀ i, (sumPadData D₁ D₂).pieceDom (Sum.inl i) (W₁ i) = D₁.pieceDom i (h₁.some.W i) :=
    fun i => (D₁.pieceDom_padAlongData (Fin.castAddEmb D₂.n) W₁ i).trans
      (congrArg (D₁.pieceDom i) (congrFun hpre₁ i))
  have hd₂ : ∀ j, (sumPadData D₁ D₂).pieceDom (Sum.inr j) (W₂ j) = D₂.pieceDom j (h₂.some.W j) :=
    fun j => (D₂.pieceDom_padAlongData (Fin.natAddEmb D₁.n) W₂ j).trans
      (congrArg (D₂.pieceDom j) (congrFun hpre₂ j))
  have hS2 : ∃ P₀ : Opens X, x ∈ P₀ ∧ P₀ ≤ D₁.pieceDom i (h₁.some.W i) ∧
      P₀ ≤ D₂.pieceDom j (h₂.some.W j) ∧
      ∃ θ : (((D₁.padAlongData (Fin.castAddEmb D₂.n)).embedding i).localResolution bed (W₁ i) (hW₁
          i)).toKLocallyRingedSpace.restrictOpen (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
              ((D₁.padAlongData
          (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i) (hW₁ i)), Hom.continuous_toFun
          ((D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i) (hW₁ i))⟩ P₀) ⟶
          (((D₂.padAlongData (Fin.natAddEmb D₁.n)).embedding j).localResolution bed (W₂ j) (hW₂
              j)).toKLocallyRingedSpace.restrictOpen (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
                  ((D₂.padAlongData
              (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j)), Hom.continuous_toFun
              ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j))⟩ P₀),
        IsIso θ ∧ ofRestrict (((D₁.padAlongData (Fin.castAddEmb D₂.n)).embedding i).localResolution
            bed (W₁ i) (hW₁ i)).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
                ((D₁.padAlongData
            (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i) (hW₁ i)), Hom.continuous_toFun
            ((D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i) (hW₁ i))⟩ P₀) ≫
            (D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i) (hW₁ i) = (θ ≫
            ofRestrict (((D₂.padAlongData (Fin.natAddEmb D₁.n)).embedding j).localResolution bed
            (W₂ j) (hW₂ j)).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
                ((D₂.padAlongData
            (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j)), Hom.continuous_toFun
            ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j))⟩ P₀)) ≫
            (D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j) ∧
        ∀ σ, QuotientSpace.comap θ.1 (QuotientSpace.comap (ofRestrict (((D₂.padAlongData
            (Fin.natAddEmb D₁.n)).embedding j).localResolution bed (W₂ j) (hW₂
            j)).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D₂.padAlongData
                (Fin.natAddEmb
            D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j)), Hom.continuous_toFun ((D₂.padAlongData
            (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j))⟩ P₀)).1
            (QuotientSpace.comap ((sumPadData D₁ D₂).resIn bed (sumPadOpens D₁ D₂ W₁ W₂)
                (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed (Sum.inr j)).1
                ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
                (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ))) =
          QuotientSpace.comap (ofRestrict (((D₁.padAlongData (Fin.castAddEmb D₂.n)).embedding
              i).localResolution bed (W₁ i) (hW₁ i)).toKLocallyRingedSpace (Opens.comap
                  ⟨KLocallyRingedSpace.Hom.toFun
              ((D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i) (hW₁ i)),
              Hom.continuous_toFun ((D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁
              i) (hW₁ i))⟩ P₀)).1 (QuotientSpace.comap ((sumPadData D₁ D₂).resIn bed (sumPadOpens
              D₁ D₂ W₁ W₂) (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed (Sum.inl i)).1
              ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
              (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ)) := by
    obtain ⟨P₀, hxP₀, hP₀i, hP₀j, θ, hθ, hθover, hθmem⟩ :=
      exists_mixedTransition_sumPadData D₁ D₂ bed hbed W₁ hW₁ W₂ hW₂ i j x
        (by rw [hd₁ i]; exact hxi) (by rw [hd₂ j]; exact hxj)
    exact ⟨P₀, hxP₀, le_of_le_of_eq hP₀i (hd₁ i), le_of_le_of_eq hP₀j (hd₂ j), θ, hθ, hθover,
      hθmem⟩
  obtain ⟨P₀, hxP₀, hP₀i, hP₀j, θ, hθ, hθover, hθmem⟩ := hS2
  have hPO : P₀ ⊓ O ≤ O := inf_le_right
  have hPU₁ : ((P₀ ⊓ O : Opens X) : Set X) ⊆ U₁ := fun y hy => (hO (hPO hy)).1
  have hPU₂ : ((P₀ ⊓ O : Opens X) : Set X) ⊆ U₂ := fun y hy => (hO (hPO hy)).2
  have hPi : P₀ ⊓ O ≤ D₁.pieceDom i (h₁.some.W i) := inf_le_left.trans hP₀i
  have hPj : P₀ ⊓ O ≤ D₂.pieceDom j (h₂.some.W j) := inf_le_left.trans hP₀j
  obtain ⟨leg₁, hleg₁, hleg₁over, hleg₁mem⟩ :=
    D₁.exists_isoOver_resolutionOn_padPiece_of_members (Fin.castAddEmb D₂.n) W₁ hW₁ bed hbed h₁
      o₁ ψ₁ hmem₁ hpiece₁ (sumInlResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed) ((sumPadData D₁
          D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂) (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂
          hW₁ hW₂) hbed) lab₁ hlab₁ hlab₁' H₁ hH₁ A₁ hA₁ hA₁' i (P₀ ⊓ O) hPU₁ hPi
  obtain ⟨leg₂, hleg₂, hleg₂over, hleg₂mem⟩ :=
    D₂.exists_isoOver_resolutionOn_padPiece_of_members (Fin.natAddEmb D₁.n) W₂ hW₂ bed hbed h₂
      o₂ ψ₂ hmem₂ hpiece₂ (sumInrResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed) ((sumPadData D₁
          D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂) (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂
          hW₁ hW₂) hbed) lab₂ hlab₂ hlab₂' H₂ hH₂ A₂ hA₂ hA₂' j (P₀ ⊓ O) hPU₂ hPj
  obtain ⟨g, hg₁, hg₂⟩ : ∃ g : (((D₂.padAlongData (Fin.natAddEmb D₁.n)).embedding
      j).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace.restrictOpen (Opens.comap
      ⟨KLocallyRingedSpace.Hom.toFun ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j
          (W₂ j) (hW₂ j)),
      Hom.continuous_toFun ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂
      j))⟩ (P₀ ⊓ O)) ⟶
      (D₂.resolutionOn bed).toKLocallyRingedSpace.restrictOpen (Opens.comap
          ⟨KLocallyRingedSpace.Hom.toFun
          (D₂.resolutionOnToSpace bed),
        Hom.continuous_toFun (D₂.resolutionOnToSpace bed)⟩ (P₀ ⊓ O)),
      leg₂ ≫ g = 𝟙 _ ∧ g ≫ leg₂ = 𝟙 _ :=
    ⟨@inv _ _ _ _ leg₂ hleg₂, @IsIso.hom_inv_id _ _ _ _ leg₂ hleg₂,
      @IsIso.inv_hom_id _ _ _ _ leg₂ hleg₂⟩
  have hgiso : IsIso g := ⟨⟨leg₂, hg₂, hg₁⟩⟩
  obtain ⟨θP, hθP⟩ : ∃ θP : (((D₁.padAlongData (Fin.castAddEmb D₂.n)).embedding i).localResolution
      bed (W₁ i) (hW₁ i)).toKLocallyRingedSpace.restrictOpen (Opens.comap
          ⟨KLocallyRingedSpace.Hom.toFun
      ((D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i) (hW₁ i)),
      Hom.continuous_toFun ((D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i) (hW₁
      i))⟩ (P₀ ⊓ O)) ⟶
      (((D₂.padAlongData (Fin.natAddEmb D₁.n)).embedding j).localResolution bed (W₂ j) (hW₂
          j)).toKLocallyRingedSpace.restrictOpen (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
              ((D₂.padAlongData
          (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j)), Hom.continuous_toFun
          ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j))⟩ (P₀ ⊓ O)),
      θP = restrictOver ((D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i) (hW₁ i))
          ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j)) (inf_le_left :
          P₀ ⊓ O ≤ P₀) θ hθover := ⟨_, rfl⟩
  have hθPiso : IsIso θP := by
    rw [hθP]
    exact isIso_restrictOver ((D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i)
        (hW₁ i)) ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j))
        (inf_le_left : P₀ ⊓ O ≤ P₀) θ hθover
  have hθPover : ofRestrict (((D₁.padAlongData (Fin.castAddEmb D₂.n)).embedding i).localResolution
      bed (W₁ i) (hW₁ i)).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
          ((D₁.padAlongData
      (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i) (hW₁ i)), Hom.continuous_toFun
      ((D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i) (hW₁ i))⟩ (P₀ ⊓ O)) ≫
      (D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i) (hW₁ i) = (θP ≫ ofRestrict
      (((D₂.padAlongData (Fin.natAddEmb D₁.n)).embedding j).localResolution bed (W₂ j) (hW₂
      j)).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D₂.padAlongData
          (Fin.natAddEmb
      D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j)), Hom.continuous_toFun ((D₂.padAlongData
      (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j))⟩ (P₀ ⊓ O))) ≫ (D₂.padAlongData
      (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j) := by
    rw [hθP]
    exact restrictOver_over ((D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i) (hW₁
        i)) ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j)) (inf_le_left
        : P₀ ⊓ O ≤ P₀) θ hθover
  have hθPofR : θP ≫ ofRestrict (((D₂.padAlongData (Fin.natAddEmb D₁.n)).embedding
      j).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace (Opens.comap
          ⟨KLocallyRingedSpace.Hom.toFun
      ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j)),
      Hom.continuous_toFun ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂
      j))⟩ (P₀ ⊓ O)) =
          KLocallyRingedSpace.restrictIncl (((D₁.padAlongData (Fin.castAddEmb D₂.n)).embedding
      i).localResolution bed (W₁ i) (hW₁ i)).toKLocallyRingedSpace (Opens.comap_mono _ (inf_le_left
      : P₀ ⊓ O ≤ P₀)) ≫ θ ≫ ofRestrict (((D₂.padAlongData (Fin.natAddEmb D₁.n)).embedding
      j).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace (Opens.comap
          ⟨KLocallyRingedSpace.Hom.toFun
      ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j)),
      Hom.continuous_toFun ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂
      j))⟩ P₀) := by
    rw [hθP]
    exact restrictOver_comp_ofRestrict ((D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i
        (W₁ i) (hW₁ i)) ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j))
        (inf_le_left : P₀ ⊓ O ≤ P₀) θ hθover
  refine ⟨P₀ ⊓ O, hPO, ⟨hxP₀, hx⟩, leg₁ ≫ θP ≫ g,
    @IsIso.comp_isIso _ _ _ _ _ leg₁ (θP ≫ g) hleg₁
      (@IsIso.comp_isIso _ _ _ _ _ θP g hθPiso hgiso), ?_, ?_⟩
  · -- over `X`
    have e_a : (leg₁ ≫ ofRestrict (((D₁.padAlongData (Fin.castAddEmb D₂.n)).embedding
        i).localResolution bed (W₁ i) (hW₁ i)).toKLocallyRingedSpace (Opens.comap
            ⟨KLocallyRingedSpace.Hom.toFun
        ((D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i) (hW₁ i)),
        Hom.continuous_toFun ((D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i)
        (hW₁ i))⟩ (P₀ ⊓ O))) ≫ (D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i)
        (hW₁ i) = leg₁ ≫ ((θP ≫ ofRestrict (((D₂.padAlongData (Fin.natAddEmb D₁.n)).embedding
        j).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace (Opens.comap
            ⟨KLocallyRingedSpace.Hom.toFun
        ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j)),
        Hom.continuous_toFun ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂
        j))⟩ (P₀ ⊓ O))) ≫ (D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j))
        :=
      (Category.assoc leg₁ (ofRestrict (((D₁.padAlongData (Fin.castAddEmb D₂.n)).embedding
          i).localResolution bed (W₁ i) (hW₁ i)).toKLocallyRingedSpace (Opens.comap
              ⟨KLocallyRingedSpace.Hom.toFun
          ((D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i) (hW₁ i)),
          Hom.continuous_toFun ((D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i)
          (hW₁ i))⟩ (P₀ ⊓ O))) ((D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i)
          (hW₁ i))).trans (congrArg (fun k => leg₁ ≫ k) hθPover)
    have e_b : g ≫ ofRestrict (D₂.resolutionOn bed).toKLocallyRingedSpace (Opens.comap
        ⟨KLocallyRingedSpace.Hom.toFun
        (D₂.resolutionOnToSpace bed), Hom.continuous_toFun (D₂.resolutionOnToSpace bed)⟩ (P₀ ⊓ O))
        ≫ D₂.resolutionOnToSpace bed = ofRestrict (((D₂.padAlongData (Fin.natAddEmb
        D₁.n)).embedding j).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace (Opens.comap
        ⟨KLocallyRingedSpace.Hom.toFun ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j
            (W₂ j) (hW₂ j)),
        Hom.continuous_toFun ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂
        j))⟩ (P₀ ⊓ O)) ≫ (D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j) :=
      (congrArg (fun k => g ≫ k) hleg₂over).trans
        ((Category.assoc g (leg₂ ≫ ofRestrict (((D₂.padAlongData (Fin.natAddEmb D₁.n)).embedding
            j).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace (Opens.comap
                ⟨KLocallyRingedSpace.Hom.toFun
            ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j)),
            Hom.continuous_toFun ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j)
            (hW₂ j))⟩ (P₀ ⊓ O))) ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j)
            (hW₂ j))).symm.trans
          ((congrArg (fun k => k ≫ (D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j)
              (hW₂ j)) (Category.assoc g leg₂ (ofRestrict (((D₂.padAlongData (Fin.natAddEmb
              D₁.n)).embedding j).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace
              (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D₂.padAlongData
                  (Fin.natAddEmb D₁.n)).pieceToSpace bed j
              (W₂ j) (hW₂ j)), Hom.continuous_toFun ((D₂.padAlongData (Fin.natAddEmb
              D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j))⟩ (P₀ ⊓ O)))).symm).trans
            ((congrArg (fun k => (k ≫ ofRestrict (((D₂.padAlongData (Fin.natAddEmb D₁.n)).embedding
                j).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace (Opens.comap
                ⟨KLocallyRingedSpace.Hom.toFun ((D₂.padAlongData
                    (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂
                j)), Hom.continuous_toFun ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed
                j (W₂ j) (hW₂ j))⟩ (P₀ ⊓ O))) ≫ (D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace
                bed j (W₂ j) (hW₂ j)) hg₂).trans
              (congrArg (fun k => k ≫ (D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂
                  j) (hW₂ j)) (Category.id_comp (ofRestrict (((D₂.padAlongData (Fin.natAddEmb
                  D₁.n)).embedding j).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace
                  (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D₂.padAlongData
                      (Fin.natAddEmb D₁.n)).pieceToSpace bed
                  j (W₂ j) (hW₂ j)), Hom.continuous_toFun ((D₂.padAlongData (Fin.natAddEmb
                  D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j))⟩ (P₀ ⊓ O))))))))
    have e_c : leg₁ ≫ ((θP ≫ ofRestrict (((D₂.padAlongData (Fin.natAddEmb D₁.n)).embedding
        j).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace (Opens.comap
            ⟨KLocallyRingedSpace.Hom.toFun
        ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j)),
        Hom.continuous_toFun ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂
        j))⟩ (P₀ ⊓ O))) ≫ (D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j))
        =
        ((leg₁ ≫ θP ≫ g) ≫ ofRestrict (D₂.resolutionOn bed).toKLocallyRingedSpace (Opens.comap
            ⟨KLocallyRingedSpace.Hom.toFun (D₂.resolutionOnToSpace bed), Hom.continuous_toFun
                (D₂.resolutionOnToSpace
            bed)⟩ (P₀ ⊓ O))) ≫ D₂.resolutionOnToSpace bed :=
      (congrArg (fun k => leg₁ ≫ k) ((Category.assoc θP (ofRestrict (((D₂.padAlongData
          (Fin.natAddEmb D₁.n)).embedding j).localResolution bed (W₂ j) (hW₂
          j)).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D₂.padAlongData
              (Fin.natAddEmb
          D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j)), Hom.continuous_toFun ((D₂.padAlongData
          (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j))⟩ (P₀ ⊓ O))) ((D₂.padAlongData
          (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j))).trans
        (congrArg (fun k => θP ≫ k) e_b.symm))).trans
        (((Category.assoc (leg₁ ≫ θP ≫ g) (ofRestrict (D₂.resolutionOn bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D₂.resolutionOnToSpace bed),
                Hom.continuous_toFun
            (D₂.resolutionOnToSpace bed)⟩ (P₀ ⊓ O))) (D₂.resolutionOnToSpace bed)).trans
          ((Category.assoc leg₁ (θP ≫ g) (ofRestrict (D₂.resolutionOn bed).toKLocallyRingedSpace
              (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D₂.resolutionOnToSpace bed),
                  Hom.continuous_toFun
              (D₂.resolutionOnToSpace bed)⟩ (P₀ ⊓ O)) ≫ D₂.resolutionOnToSpace bed)).trans
            (congrArg (fun k => leg₁ ≫ k)
              (Category.assoc θP g (ofRestrict (D₂.resolutionOn bed).toKLocallyRingedSpace
                  (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D₂.resolutionOnToSpace bed),
                      Hom.continuous_toFun
                  (D₂.resolutionOnToSpace bed)⟩ (P₀ ⊓ O)) ≫ D₂.resolutionOnToSpace bed))))).symm)
    exact hleg₁over.trans (e_a.trans e_c)
  · -- the members, label by label of the common label set
    intro σ
    have hT₁ : QuotientSpace.comap ((sumPadData D₁ D₂).resIn bed (sumPadOpens D₁ D₂ W₁ W₂)
        (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed (Sum.inl i)).1 ((sumPadData D₁
        D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂) (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂
        hW₁ hW₂) hbed σ) = QuotientSpace.comap ((D₁.padAlongData (Fin.castAddEmb D₂.n)).resIn bed
        W₁ hW₁ hbed i ≫ sumInlResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed).1 ((sumPadData D₁
        D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂) (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂
        hW₁ hW₂) hbed σ) :=
      (comap_resIn_sumPadData_inl D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed i ((sumPadData D₁ D₂).sigmaMembers
          bed (sumPadOpens D₁ D₂ W₁ W₂) (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed
          σ)).trans
        (QuotientSpace.comap_comp (sumInlResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed).1 ((sumPadData D₁
            D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂) (isCompact_closure_sumPadOpens D₁ D₂ W₁
            W₂ hW₁ hW₂) hbed σ) ((D₁.padAlongData (Fin.castAddEmb D₂.n)).resIn bed W₁ hW₁ hbed
            i).1).symm
    have hT₂ : QuotientSpace.comap ((sumPadData D₁ D₂).resIn bed (sumPadOpens D₁ D₂ W₁ W₂)
        (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed (Sum.inr j)).1 ((sumPadData D₁
        D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂) (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂
        hW₁ hW₂) hbed σ) = QuotientSpace.comap ((D₂.padAlongData (Fin.natAddEmb D₁.n)).resIn bed W₂
        hW₂ hbed j ≫ sumInrResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed).1 ((sumPadData D₁ D₂).sigmaMembers
        bed (sumPadOpens D₁ D₂ W₁ W₂) (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ) :=
      (comap_resIn_sumPadData_inr D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed j ((sumPadData D₁ D₂).sigmaMembers
          bed (sumPadOpens D₁ D₂ W₁ W₂) (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed
          σ)).trans
        (QuotientSpace.comap_comp (sumInrResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed).1 ((sumPadData D₁
            D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂) (isCompact_closure_sumPadOpens D₁ D₂ W₁
            W₂ hW₁ hW₂) hbed σ) ((D₂.padAlongData (Fin.natAddEmb D₁.n)).resIn bed W₂ hW₂ hbed
            j).1).symm
    have hmid : QuotientSpace.comap (θP ≫ ofRestrict (((D₂.padAlongData (Fin.natAddEmb
        D₁.n)).embedding j).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace (Opens.comap
        ⟨KLocallyRingedSpace.Hom.toFun ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j
            (W₂ j) (hW₂ j)),
        Hom.continuous_toFun ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂
        j))⟩ (P₀ ⊓ O))).1 (QuotientSpace.comap ((D₂.padAlongData (Fin.natAddEmb D₁.n)).resIn bed W₂
        hW₂ hbed j ≫ sumInrResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed).1 ((sumPadData D₁ D₂).sigmaMembers
        bed (sumPadOpens D₁ D₂ W₁ W₂) (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ))
        = QuotientSpace.comap (ofRestrict (((D₁.padAlongData (Fin.castAddEmb D₂.n)).embedding
        i).localResolution bed (W₁ i) (hW₁ i)).toKLocallyRingedSpace (Opens.comap
            ⟨KLocallyRingedSpace.Hom.toFun
        ((D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i) (hW₁ i)),
        Hom.continuous_toFun ((D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i)
        (hW₁ i))⟩ (P₀ ⊓ O))).1 (QuotientSpace.comap ((D₁.padAlongData (Fin.castAddEmb D₂.n)).resIn
        bed W₁ hW₁ hbed i ≫ sumInlResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed).1 ((sumPadData D₁
        D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂) (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂
        hW₁ hW₂) hbed σ)) :=
      (congrArg (fun m => QuotientSpace.comap m (QuotientSpace.comap ((D₂.padAlongData
          (Fin.natAddEmb D₁.n)).resIn bed W₂ hW₂ hbed j ≫ sumInrResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂
          hbed).1 ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
          (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ))) (congrArg Subtype.val
          hθPofR)).trans
        ((QuotientSpace.comap_comp (θ.1 ≫ (ofRestrict (((D₂.padAlongData (Fin.natAddEmb
            D₁.n)).embedding j).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D₂.padAlongData
                (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂
            j) (hW₂ j)), Hom.continuous_toFun ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace
            bed j (W₂ j) (hW₂ j))⟩ P₀)).1) (QuotientSpace.comap ((D₂.padAlongData (Fin.natAddEmb
            D₁.n)).resIn bed W₂ hW₂ hbed j ≫ sumInrResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed).1
            ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ))
                (KLocallyRingedSpace.restrictIncl
            (((D₁.padAlongData (Fin.castAddEmb D₂.n)).embedding i).localResolution bed (W₁ i) (hW₁
            i)).toKLocallyRingedSpace (Opens.comap_mono _ (inf_le_left : P₀ ⊓ O ≤ P₀))).1).trans
          ((congrArg
              (QuotientSpace.comap
                  (KLocallyRingedSpace.restrictIncl (((D₁.padAlongData (Fin.castAddEmb
              D₂.n)).embedding i).localResolution bed (W₁ i) (hW₁ i)).toKLocallyRingedSpace
              (Opens.comap_mono _ (inf_le_left : P₀ ⊓ O ≤ P₀))).1)
              (QuotientSpace.comap_comp (ofRestrict (((D₂.padAlongData (Fin.natAddEmb
                  D₁.n)).embedding j).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace
                  (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D₂.padAlongData
                      (Fin.natAddEmb D₁.n)).pieceToSpace bed
                  j (W₂ j) (hW₂ j)), Hom.continuous_toFun ((D₂.padAlongData (Fin.natAddEmb
                  D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j))⟩ P₀)).1 (QuotientSpace.comap
                  ((D₂.padAlongData (Fin.natAddEmb D₁.n)).resIn bed W₂ hW₂ hbed j ≫ sumInrResIn D₁
                  D₂ W₁ W₂ bed hW₁ hW₂ hbed).1 ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁
                  D₂ W₁ W₂) (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ)) θ.1)).trans
            ((congrArg
                (fun J => QuotientSpace.comap (KLocallyRingedSpace.restrictIncl (((D₁.padAlongData
                (Fin.castAddEmb D₂.n)).embedding i).localResolution bed (W₁ i) (hW₁
                i)).toKLocallyRingedSpace (Opens.comap_mono _ (inf_le_left : P₀ ⊓ O ≤ P₀))).1
                (QuotientSpace.comap θ.1
                (QuotientSpace.comap (ofRestrict (((D₂.padAlongData (Fin.natAddEmb D₁.n)).embedding
                    j).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace (Opens.comap
                    ⟨KLocallyRingedSpace.Hom.toFun ((D₂.padAlongData
                        (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j)
                    (hW₂ j)), Hom.continuous_toFun ((D₂.padAlongData (Fin.natAddEmb
                    D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j))⟩ P₀)).1 J))) hT₂.symm).trans
              ((congrArg
                  (QuotientSpace.comap
                      (KLocallyRingedSpace.restrictIncl (((D₁.padAlongData (Fin.castAddEmb
                  D₂.n)).embedding i).localResolution bed (W₁ i) (hW₁ i)).toKLocallyRingedSpace
                  (Opens.comap_mono _ (inf_le_left : P₀ ⊓ O ≤ P₀))).1) (hθmem σ)).trans
                ((congrArg
                    (fun J =>
                        QuotientSpace.comap (KLocallyRingedSpace.restrictIncl (((D₁.padAlongData
                    (Fin.castAddEmb D₂.n)).embedding i).localResolution bed (W₁ i) (hW₁
                    i)).toKLocallyRingedSpace (Opens.comap_mono _ (inf_le_left : P₀ ⊓ O ≤ P₀))).1
                    (QuotientSpace.comap (ofRestrict (((D₁.padAlongData (Fin.castAddEmb
                        D₂.n)).embedding i).localResolution bed (W₁ i) (hW₁
                        i)).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
                            ((D₁.padAlongData
                        (Fin.castAddEmb D₂.n)).pieceToSpace bed i (W₁ i) (hW₁ i)),
                        Hom.continuous_toFun ((D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceToSpace
                        bed i (W₁ i) (hW₁ i))⟩ P₀)).1 J)) hT₁).trans
                  ((QuotientSpace.comap_comp (ofRestrict (((D₁.padAlongData (Fin.castAddEmb
                      D₂.n)).embedding i).localResolution bed (W₁ i) (hW₁ i)).toKLocallyRingedSpace
                      (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D₁.padAlongData
                          (Fin.castAddEmb D₂.n)).pieceToSpace
                      bed i (W₁ i) (hW₁ i)), Hom.continuous_toFun ((D₁.padAlongData (Fin.castAddEmb
                      D₂.n)).pieceToSpace bed i (W₁ i) (hW₁ i))⟩ P₀)).1 (QuotientSpace.comap
                      ((D₁.padAlongData (Fin.castAddEmb D₂.n)).resIn bed W₁ hW₁ hbed i ≫
                      sumInlResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed).1 ((sumPadData D₁ D₂).sigmaMembers
                      bed (sumPadOpens D₁ D₂ W₁ W₂) (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁
                      hW₂) hbed σ))
                          (KLocallyRingedSpace.restrictIncl (((D₁.padAlongData (Fin.castAddEmb
                      D₂.n)).embedding i).localResolution bed (W₁ i) (hW₁ i)).toKLocallyRingedSpace
                      (Opens.comap_mono _ (inf_le_left : P₀ ⊓ O ≤ P₀))).1).symm.trans
                    (congrArg (fun m => QuotientSpace.comap m (QuotientSpace.comap
                        ((D₁.padAlongData (Fin.castAddEmb D₂.n)).resIn bed W₁ hW₁ hbed i ≫
                        sumInlResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed).1 ((sumPadData D₁
                        D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
                        (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ)))
                      (congrArg Subtype.val
                          (KLocallyRingedSpace.restrictIncl_comp_ofRestrict (((D₁.padAlongData
                          (Fin.castAddEmb D₂.n)).embedding i).localResolution bed (W₁ i) (hW₁
                          i)).toKLocallyRingedSpace
                        (Opens.comap_mono _ (inf_le_left : P₀ ⊓ O ≤ P₀)))))))))))
    have hm : (leg₁ ≫ θP ≫ g) ≫ leg₂ ≫ ofRestrict (((D₂.padAlongData (Fin.natAddEmb
        D₁.n)).embedding j).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace (Opens.comap
        ⟨KLocallyRingedSpace.Hom.toFun ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j
            (W₂ j) (hW₂ j)),
        Hom.continuous_toFun ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂
        j))⟩ (P₀ ⊓ O)) = leg₁ ≫ θP ≫ ofRestrict (((D₂.padAlongData (Fin.natAddEmb D₁.n)).embedding
        j).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace (Opens.comap
            ⟨KLocallyRingedSpace.Hom.toFun
        ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j)),
        Hom.continuous_toFun ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂
        j))⟩ (P₀ ⊓ O)) :=
      (Category.assoc leg₁ (θP ≫ g) (leg₂ ≫ ofRestrict (((D₂.padAlongData (Fin.natAddEmb
          D₁.n)).embedding j).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D₂.padAlongData
              (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j)
          (hW₂ j)), Hom.continuous_toFun ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j
          (W₂ j) (hW₂ j))⟩ (P₀ ⊓ O)))).trans
        (congrArg (fun k => leg₁ ≫ k) ((Category.assoc θP g (leg₂ ≫ ofRestrict (((D₂.padAlongData
            (Fin.natAddEmb D₁.n)).embedding j).localResolution bed (W₂ j) (hW₂
            j)).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D₂.padAlongData
                (Fin.natAddEmb
            D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j)), Hom.continuous_toFun ((D₂.padAlongData
            (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j))⟩ (P₀ ⊓ O)))).trans
          (congrArg (fun k => θP ≫ k) ((Category.assoc g leg₂ (ofRestrict (((D₂.padAlongData
              (Fin.natAddEmb D₁.n)).embedding j).localResolution bed (W₂ j) (hW₂
              j)).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
                  ((D₂.padAlongData (Fin.natAddEmb
              D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j)), Hom.continuous_toFun ((D₂.padAlongData
              (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j))⟩ (P₀ ⊓ O)))).symm.trans
            ((congrArg (fun k => k ≫ ofRestrict (((D₂.padAlongData (Fin.natAddEmb D₁.n)).embedding
                j).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace (Opens.comap
                ⟨KLocallyRingedSpace.Hom.toFun ((D₂.padAlongData
                    (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂
                j)), Hom.continuous_toFun ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed
                j (W₂ j) (hW₂ j))⟩ (P₀ ⊓ O))) hg₂).trans (Category.id_comp (ofRestrict
                (((D₂.padAlongData (Fin.natAddEmb D₁.n)).embedding j).localResolution bed (W₂ j)
                (hW₂ j)).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
                    ((D₂.padAlongData
                (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j)), Hom.continuous_toFun
                ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j))⟩ (P₀ ⊓
                O)))))))))
    exact (QuotientSpace.comap_comp (ofRestrict (D₂.resolutionOn bed).toKLocallyRingedSpace
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D₂.resolutionOnToSpace bed),
            Hom.continuous_toFun
        (D₂.resolutionOnToSpace bed)⟩ (P₀ ⊓ O))).1 (A₂ σ) (leg₁ ≫ θP ≫ g).1).trans
      ((congrArg (QuotientSpace.comap (leg₁ ≫ θP ≫ g).1) (hleg₂mem σ).symm).trans
        ((QuotientSpace.comap_comp (leg₂ ≫ ofRestrict (((D₂.padAlongData (Fin.natAddEmb
            D₁.n)).embedding j).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D₂.padAlongData
                (Fin.natAddEmb D₁.n)).pieceToSpace bed j (W₂
            j) (hW₂ j)), Hom.continuous_toFun ((D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceToSpace
            bed j (W₂ j) (hW₂ j))⟩ (P₀ ⊓ O))).1 (QuotientSpace.comap ((D₂.padAlongData
            (Fin.natAddEmb D₁.n)).resIn bed W₂ hW₂ hbed j ≫ sumInrResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂
            hbed).1 ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ)) (leg₁ ≫ θP ≫
            g).1).symm.trans
          ((congrArg (fun m => QuotientSpace.comap m (QuotientSpace.comap ((D₂.padAlongData
              (Fin.natAddEmb D₁.n)).resIn bed W₂ hW₂ hbed j ≫ sumInrResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂
              hbed).1 ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
              (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ))) (congrArg Subtype.val
              hm)).trans
            ((QuotientSpace.comap_comp (θP ≫ ofRestrict (((D₂.padAlongData (Fin.natAddEmb
                D₁.n)).embedding j).localResolution bed (W₂ j) (hW₂ j)).toKLocallyRingedSpace
                (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D₂.padAlongData
                    (Fin.natAddEmb D₁.n)).pieceToSpace bed j
                (W₂ j) (hW₂ j)), Hom.continuous_toFun ((D₂.padAlongData (Fin.natAddEmb
                D₁.n)).pieceToSpace bed j (W₂ j) (hW₂ j))⟩ (P₀ ⊓ O))).1 (QuotientSpace.comap
                ((D₂.padAlongData (Fin.natAddEmb D₁.n)).resIn bed W₂ hW₂ hbed j ≫ sumInrResIn D₁ D₂
                W₁ W₂ bed hW₁ hW₂ hbed).1 ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂
                W₁ W₂) (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ)) leg₁.1).trans
              ((congrArg (QuotientSpace.comap leg₁.1) hmid).trans
                ((QuotientSpace.comap_comp (ofRestrict (((D₁.padAlongData (Fin.castAddEmb
                    D₂.n)).embedding i).localResolution bed (W₁ i) (hW₁ i)).toKLocallyRingedSpace
                    (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D₁.padAlongData
                        (Fin.castAddEmb D₂.n)).pieceToSpace
                    bed i (W₁ i) (hW₁ i)), Hom.continuous_toFun ((D₁.padAlongData (Fin.castAddEmb
                    D₂.n)).pieceToSpace bed i (W₁ i) (hW₁ i))⟩ (P₀ ⊓ O))).1 (QuotientSpace.comap
                    ((D₁.padAlongData (Fin.castAddEmb D₂.n)).resIn bed W₁ hW₁ hbed i ≫ sumInlResIn
                    D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed).1 ((sumPadData D₁ D₂).sigmaMembers bed
                    (sumPadOpens D₁ D₂ W₁ W₂) (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂)
                    hbed σ)) leg₁.1).symm.trans
                  (hleg₁mem σ)))))))

end LocalPair

end Hironaka.Manifold.LocalEmbeddingData

end
