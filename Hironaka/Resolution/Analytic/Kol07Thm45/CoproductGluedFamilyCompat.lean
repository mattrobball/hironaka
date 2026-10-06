/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.DoubledDatumLabels
public import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductGluedFamily
import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductLevelPair
import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductMixedTransition
import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductPadIdentityPiece
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionHomOnComp
import Hironaka.Resolution.Analytic.Kol07Thm45.PadReadingOpens
import Hironaka.Resolution.Analytic.Kol07Thm45.RigidOverLocalResolution
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The compatibility of the piece traces along the gluing

Kollár's agreement of the centres on the overlaps, (37.2) in [Kol07, Proposition 37, proof]. The
coproduct member of a label is traced on every piece (`pieceTrace`), and `gluedMembersOn`
(`CoproductGluedFamily.lean`) glues the traces into a family on the glued local resolution once
they are compatible along the transitions with the identity labelling (`LabelledCompat`).
Compatibility of a pair of pieces is a POINTWISE matter
(`compatClosedSubspaces_pair_of_forall_exists_isoOver`,
`Hironaka/Resolution/Analytic/Kol07Thm45/Glue/OverRigidity.lean`): at each point of the gluing open
an isomorphism over `X` of the parts over a neighbourhood carrying the one trace to the other, with
the rigidity of the piece map over that neighbourhood (`rigidOver_pieceToSpace`, the only use of
`hind`).

* `exists_isoOver_pieces_of_sum` (the conjugation lemma): at a point of the domains of a piece of
  `D₁` and a piece of `D₂`, the mixed-pair transition of the doubled datum `sumPadData D₁ D₂` —
  an isomorphism over `X` between the parts over `P` of the two PADDED pieces' local resolutions
  carrying the doubled run's member of every label — conjugated by the piece isomorphisms of the
  padding identities (restricted over `P`, `Hom.restrictTo`) is an isomorphism over `X` between
  the parts over `P` of the two UNPADDED pieces' local resolutions carrying, for every label `σ`
  of the doubled run, the `⊤`-extended trace `sumLabelTrace` of `D₂` on the second piece to that
  of `D₁` on the first (`comap_resIn_sumPadData_inl/_inr`, the label embeddings' clauses, the
  padding identity's member clause and squares).
* `labelledCompat_pieceTrace`: the piece traces are compatible with the identity labelling — at
  the diagonal pair `(D, D)` with the padded reading opens `padReadingOpens`, the padding
  identities from `padIdentityOn` read at the reading opens of the gluing
  (`exists_padIdentity_of_padPreimageOpens_eq`), the two label embeddings, the conjugation lemma at
  a point of the gluing open, and the label coherence `label_route_eq_of_ne_top`
  (`DoubledDatumLabels.lean`) to read the doubled run's label `lab₁ (o₁.symm l)` as the label `l`
  on both pieces; a label whose member is the unit ideal has all its traces equal to the unit
  ideal and needs no coherence.

Not in the sources beyond Kollár's proof; bookkeeping.
-/

public noncomputable section

open CategoryTheory TopologicalSpace Set AnalyticSpace
open KLocallyRingedSpace Hironaka.Manifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.LocalEmbeddingData

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜}

section Conjugation

variable {U₁ U₂ : Set X} (D₁ : LocalEmbeddingData 𝕜 X U₁) (D₂ : LocalEmbeddingData 𝕜 X U₂)
  (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
  (W₁ : ∀ i : D₁.ι, Opens (pieceAmbient.{u} 𝕜 ((D₁.padLeftData D₂.n).embedding i).G))
  (hW₁ : ∀ i, IsCompact (closure (W₁ i : Set (pieceAmbient.{u} 𝕜
    ((D₁.padLeftData D₂.n).embedding i).G))))
  (W₂ : ∀ j : D₂.ι, Opens (pieceAmbient.{u} 𝕜 ((D₂.padRightData D₁.n).embedding j).G))
  (hW₂ : ∀ j, IsCompact (closure (W₂ j : Set (pieceAmbient.{u} 𝕜
    ((D₂.padRightData D₁.n).embedding j).G))))
  (V₁ : ∀ i : D₁.ι, Opens (pieceAmbient.{u} 𝕜 (D₁.embedding i).G))
  (hV₁ : ∀ i, IsCompact (closure (V₁ i : Set (pieceAmbient.{u} 𝕜 (D₁.embedding i).G))))
  (V₂ : ∀ j : D₂.ι, Opens (pieceAmbient.{u} 𝕜 (D₂.embedding j).G))
  (hV₂ : ∀ j, IsCompact (closure (V₂ j : Set (pieceAmbient.{u} 𝕜 (D₂.embedding j).G))))

/-- **The mixed-pair transition of the doubled datum, conjugated by the padding identities of the
two pieces** ((37.2) in [Kol07, Proposition 37, proof]) — at a point `x` of the domains of the
piece `i` of `D₁` and the piece `j` of `D₂` (read at the reading opens `V₁`, `V₂` carried by the
padded ones `W₁`, `W₂`: `hpre₁`, `hpre₂`), an open `P ∋ x` inside both domains and an isomorphism
over `X` between the parts over `P` of the two pieces' local resolutions carrying, for every label
`σ` of the doubled run, the `⊤`-extended trace of `D₂` on the piece `j` to that of `D₁` on the
piece `i`. The binders are the conjuncts of `exists_padIdentity_of_padPreimageOpens_eq` for the
two padded copies (`o`, `ψ` with the member clause `hmem`, and per piece an isomorphism over the
piece with the square `resIn⁺ i ≫ ψ = ψᵢ ≫ resIn i`) and the two label embeddings with their
clauses. -/
theorem exists_isoOver_pieces_of_sum
    (hpre₁ : D₁.padPreimageOpens (Fin.castAddEmb D₂.n) W₁ = V₁)
    (hpre₂ : D₂.padPreimageOpens (Fin.natAddEmb D₁.n) W₂ = V₂)
    (o₁ : (D₁.padLeftData D₂.n).sigmaIndex bed W₁ hW₁ ≃o D₁.sigmaIndex bed V₁ hV₁)
    (ψ₁ : bed.localResolutionOn (D₁.padLeftData D₂.n).sigmaTriple
        (D₁.padLeftData D₂.n).domBEDan_sigmaTriple ((D₁.padLeftData D₂.n).ambImage W₁)
        ((D₁.padLeftData D₂.n).isCompact_closure_ambImage W₁ hW₁) ⟶
        bed.localResolutionOn D₁.sigmaTriple D₁.domBEDan_sigmaTriple (D₁.ambImage V₁)
        (D₁.isCompact_closure_ambImage V₁ hV₁))
    (hmem₁ : ∀ σp, QuotientSpace.comap ψ₁.1 (D₁.sigmaMembers bed V₁ hV₁ hbed (o₁ σp)) =
      (D₁.padLeftData D₂.n).sigmaMembers bed W₁ hW₁ hbed σp)
    (hpiece₁ : ∀ i, ∃ ψᵢ :
        ((D₁.padLeftData D₂.n).embedding i).localResolution bed (W₁ i) (hW₁ i) ⟶
        (D₁.embedding i).localResolution bed (V₁ i) (hV₁ i),
      IsIso ψᵢ ∧
      ψᵢ ≫ (D₁.embedding i).localResolutionToPiece bed (V₁ i) (hV₁ i) =
        ((D₁.padLeftData D₂.n).embedding i).localResolutionToPiece bed (W₁ i) (hW₁ i) ∧
      (D₁.padLeftData D₂.n).resIn bed W₁ hW₁ hbed i ≫ ψ₁ = ψᵢ ≫ D₁.resIn bed V₁ hV₁ hbed i)
    (o₂ : (D₂.padRightData D₁.n).sigmaIndex bed W₂ hW₂ ≃o D₂.sigmaIndex bed V₂ hV₂)
    (ψ₂ : bed.localResolutionOn (D₂.padRightData D₁.n).sigmaTriple
        (D₂.padRightData D₁.n).domBEDan_sigmaTriple ((D₂.padRightData D₁.n).ambImage W₂)
        ((D₂.padRightData D₁.n).isCompact_closure_ambImage W₂ hW₂) ⟶
        bed.localResolutionOn D₂.sigmaTriple D₂.domBEDan_sigmaTriple (D₂.ambImage V₂)
        (D₂.isCompact_closure_ambImage V₂ hV₂))
    (hmem₂ : ∀ σp, QuotientSpace.comap ψ₂.1 (D₂.sigmaMembers bed V₂ hV₂ hbed (o₂ σp)) =
      (D₂.padRightData D₁.n).sigmaMembers bed W₂ hW₂ hbed σp)
    (hpiece₂ : ∀ j, ∃ ψⱼ :
        ((D₂.padRightData D₁.n).embedding j).localResolution bed (W₂ j) (hW₂ j) ⟶
        (D₂.embedding j).localResolution bed (V₂ j) (hV₂ j),
      IsIso ψⱼ ∧
      ψⱼ ≫ (D₂.embedding j).localResolutionToPiece bed (V₂ j) (hV₂ j) =
        ((D₂.padRightData D₁.n).embedding j).localResolutionToPiece bed (W₂ j) (hW₂ j) ∧
      (D₂.padRightData D₁.n).resIn bed W₂ hW₂ hbed j ≫ ψ₂ = ψⱼ ≫ D₂.resIn bed V₂ hV₂ hbed j)
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
    (i : D₁.ι) (j : D₂.ι) (x : X) (hxi : x ∈ D₁.pieceDom i (V₁ i)) (hxj : x ∈ D₂.pieceDom j (V₂
        j)) :
    ∃ P : Opens X, x ∈ P ∧ P ≤ D₁.pieceDom i (V₁ i) ⊓ D₂.pieceDom j (V₂ j) ∧
      ∃ θ' : ((D₁.embedding i).localResolution bed (V₁ i) (hV₁
          i)).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D₁.pieceToSpace bed i (V₁ i) (hV₁ i)),
              Hom.continuous_toFun _⟩ P) ⟶
          ((D₂.embedding j).localResolution bed (V₂ j) (hV₂ j)).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D₂.pieceToSpace bed j (V₂ j) (hV₂ j)),
              Hom.continuous_toFun _⟩ P),
        IsIso θ' ∧
        ofRestrict _ _ ≫ D₁.pieceToSpace bed i (V₁ i) (hV₁ i) =
          (θ' ≫ ofRestrict _ _) ≫ D₂.pieceToSpace bed j (V₂ j) (hV₂ j) ∧
        ∀ σ : (sumPadData D₁ D₂).sigmaIndex bed (sumPadOpens D₁ D₂ W₁ W₂)
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂),
          QuotientSpace.comap (θ' ≫ ofRestrict _ _).1
            (D₂.sumLabelTrace bed V₂ hV₂ hbed o₂ lab₂ j σ) =
          QuotientSpace.comap (ofRestrict _ _).1 (D₁.sumLabelTrace bed V₁ hV₁ hbed o₁ lab₁ i σ)
              := by
  -- the sum's domains are the data's
  have hdomi : (sumPadData D₁ D₂).pieceDom (Sum.inl i) (W₁ i) = D₁.pieceDom i (V₁ i) := by
    change (D₁.padAlongData (Fin.castAddEmb D₂.n)).pieceDom i (W₁ i) = _
    rw [D₁.pieceDom_padAlongData (Fin.castAddEmb D₂.n) W₁ i, hpre₁]
  have hdomj : (sumPadData D₁ D₂).pieceDom (Sum.inr j) (W₂ j) = D₂.pieceDom j (V₂ j) := by
    change (D₂.padAlongData (Fin.natAddEmb D₁.n)).pieceDom j (W₂ j) = _
    rw [D₂.pieceDom_padAlongData (Fin.natAddEmb D₁.n) W₂ j, hpre₂]
  have hxi' : x ∈ (sumPadData D₁ D₂).pieceDom (Sum.inl i) (W₁ i) := by rw [hdomi]; exact hxi
  have hxj' : x ∈ (sumPadData D₁ D₂).pieceDom (Sum.inr j) (W₂ j) := by rw [hdomj]; exact hxj
  obtain ⟨P, hxP, hPl, hPr, θ, hθ, hover, hcl⟩ :=
    exists_mixedTransition_sumPadData D₁ D₂ bed hbed W₁ hW₁ W₂ hW₂ i j x hxi' hxj'
  obtain ⟨ψᵢ, hψᵢ, hpᵢ, hsqᵢ⟩ := hpiece₁ i
  obtain ⟨ψⱼ, hψⱼ, hpⱼ, hsqⱼ⟩ := hpiece₂ j
  -- the K-typed piece isomorphisms, in the sum's spelling of the padded pieces
  let ψᵢK : (((sumPadData D₁ D₂).embedding (Sum.inl i)).localResolution bed (W₁ i)
      (hW₁ i)).toKLocallyRingedSpace ⟶
      ((D₁.embedding i).localResolution bed (V₁ i) (hV₁ i)).toKLocallyRingedSpace := ψᵢ
  let ψⱼK : (((sumPadData D₁ D₂).embedding (Sum.inr j)).localResolution bed (W₂ j)
      (hW₂ j)).toKLocallyRingedSpace ⟶
      ((D₂.embedding j).localResolution bed (V₂ j) (hV₂ j)).toKLocallyRingedSpace := ψⱼ
  let ψᵢ' : ((D₁.embedding i).localResolution bed (V₁ i) (hV₁ i)).toKLocallyRingedSpace ⟶
      (((sumPadData D₁ D₂).embedding (Sum.inl i)).localResolution bed (W₁ i)
        (hW₁ i)).toKLocallyRingedSpace :=
    @inv (AnalyticSpace.{u} 𝕜) _ _ _ ψᵢ hψᵢ
  let ψⱼ' : ((D₂.embedding j).localResolution bed (V₂ j) (hV₂ j)).toKLocallyRingedSpace ⟶
      (((sumPadData D₁ D₂).embedding (Sum.inr j)).localResolution bed (W₂ j)
        (hW₂ j)).toKLocallyRingedSpace :=
    @inv (AnalyticSpace.{u} 𝕜) _ _ _ ψⱼ hψⱼ
  have hψᵢ₁ : ψᵢK ≫ ψᵢ' = 𝟙 _ := @IsIso.hom_inv_id (AnalyticSpace.{u} 𝕜) _ _
      _ ψᵢ hψᵢ
  have hψᵢ₂ : ψᵢ' ≫ ψᵢK = 𝟙 _ := @IsIso.inv_hom_id (AnalyticSpace.{u} 𝕜) _ _
      _ ψᵢ hψᵢ
  have hψⱼ₁ : ψⱼK ≫ ψⱼ' = 𝟙 _ := @IsIso.hom_inv_id (AnalyticSpace.{u} 𝕜) _ _
      _ ψⱼ hψⱼ
  have hψⱼ₂ : ψⱼ' ≫ ψⱼK = 𝟙 _ := @IsIso.inv_hom_id (AnalyticSpace.{u} 𝕜) _ _
      _ ψⱼ hψⱼ
  -- the piece isomorphisms lie over `X`
  have hoverᵢ : ψᵢK ≫ D₁.pieceToSpace bed i (V₁ i) (hV₁ i) =
      (sumPadData D₁ D₂).pieceToSpace bed (Sum.inl i) (W₁ i) (hW₁ i) := by
    change ψᵢK ≫ ((D₁.embedding i).localResolutionToPiece bed (V₁ i) (hV₁ i) ≫ ofRestrict _ _) =
      ((D₁.padLeftData D₂.n).embedding i).localResolutionToPiece bed (W₁ i) (hW₁ i) ≫
        ofRestrict _ _
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun f => CategoryStruct.comp f
        (ofRestrict _ _)) hpᵢ)
  have hoverⱼ : ψⱼK ≫ D₂.pieceToSpace bed j (V₂ j) (hV₂ j) =
      (sumPadData D₁ D₂).pieceToSpace bed (Sum.inr j) (W₂ j) (hW₂ j) := by
    change ψⱼK ≫ ((D₂.embedding j).localResolutionToPiece bed (V₂ j) (hV₂ j) ≫ ofRestrict _ _) =
      ((D₂.padRightData D₁.n).embedding j).localResolutionToPiece bed (W₂ j) (hW₂ j) ≫
        ofRestrict _ _
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun f => CategoryStruct.comp f
        (ofRestrict _ _)) hpⱼ)
  have hoverᵢ' : ψᵢ' ≫ (sumPadData D₁ D₂).pieceToSpace bed (Sum.inl i) (W₁ i) (hW₁ i) =
      D₁.pieceToSpace bed i (V₁ i) (hV₁ i) := by
    rw [← hoverᵢ, ← Category.assoc, hψᵢ₂, Category.id_comp]
  -- the parts over `P` and the restricted isomorphisms
  have hmᵢ : ∀ a ∈ Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
        (D₁.pieceToSpace bed i (V₁ i) (hV₁ i)), Hom.continuous_toFun _⟩ P,
      KLocallyRingedSpace.Hom.toFun ψᵢ' a ∈ Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
        ((sumPadData D₁ D₂).pieceToSpace bed (Sum.inl i) (W₁ i) (hW₁ i)),
        Hom.continuous_toFun _⟩ P := fun a ha =>
    (congrArg (fun z => z ∈ (P : Set X))
      (congrFun (congrArg KLocallyRingedSpace.Hom.toFun hoverᵢ') a)).mpr ha
  have hmᵢp : ∀ a ∈ Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
        ((sumPadData D₁ D₂).pieceToSpace bed (Sum.inl i) (W₁ i) (hW₁ i)),
        Hom.continuous_toFun _⟩ P,
      KLocallyRingedSpace.Hom.toFun ψᵢK a ∈ Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
        (D₁.pieceToSpace bed i (V₁ i) (hV₁ i)), Hom.continuous_toFun _⟩ P := fun a ha =>
    (congrArg (fun z => z ∈ (P : Set X))
      (congrFun (congrArg KLocallyRingedSpace.Hom.toFun hoverᵢ) a)).mpr ha
  have hmⱼ : ∀ a ∈ Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
        ((sumPadData D₁ D₂).pieceToSpace bed (Sum.inr j) (W₂ j) (hW₂ j)),
        Hom.continuous_toFun _⟩ P,
      KLocallyRingedSpace.Hom.toFun ψⱼK a ∈ Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
        (D₂.pieceToSpace bed j (V₂ j) (hV₂ j)), Hom.continuous_toFun _⟩ P := fun a ha =>
    (congrArg (fun z => z ∈ (P : Set X))
      (congrFun (congrArg KLocallyRingedSpace.Hom.toFun hoverⱼ) a)).mpr ha
  have hmⱼ' : ∀ a ∈ Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
        (D₂.pieceToSpace bed j (V₂ j) (hV₂ j)), Hom.continuous_toFun _⟩ P,
      KLocallyRingedSpace.Hom.toFun ψⱼ' a ∈ Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
        ((sumPadData D₁ D₂).pieceToSpace bed (Sum.inr j) (W₂ j) (hW₂ j)),
        Hom.continuous_toFun _⟩ P := fun a ha => by
    have hoverⱼ' : ψⱼ' ≫ (sumPadData D₁ D₂).pieceToSpace bed (Sum.inr j) (W₂ j) (hW₂ j) =
        D₂.pieceToSpace bed j (V₂ j) (hV₂ j) := by
      rw [← hoverⱼ, ← Category.assoc, hψⱼ₂, Category.id_comp]
    exact (congrArg (fun z => z ∈ (P : Set X))
      (congrFun (congrArg KLocallyRingedSpace.Hom.toFun hoverⱼ') a)).mpr ha
  -- a restriction of a pair of mutually inverse morphisms is a pair of mutually inverse morphisms
  have hinv : ∀ {A B : KLocallyRingedSpace.{u} 𝕜} (f : A ⟶ B) (g : B ⟶ A) (hfg : f ≫ g = 𝟙 A)
      (U : Opens A) (U' : Opens B) (h : ∀ a ∈ U, KLocallyRingedSpace.Hom.toFun f a ∈ U')
      (h' : ∀ b ∈ U', KLocallyRingedSpace.Hom.toFun g b ∈ U),
      Hom.restrictTo f U U' h ≫ Hom.restrictTo g U' U h' = 𝟙 _ := by
    intro A B f g hfg U U' h h'
    have hK : (Hom.restrictTo f U U' h ≫ Hom.restrictTo g U' U h') ≫ ofRestrict A U =
        𝟙 _ ≫ ofRestrict A U := by
      rw [Category.assoc, Hom.restrictTo_comp_ofRestrict, ← Category.assoc,
        Hom.restrictTo_comp_ofRestrict, Category.assoc, hfg, Category.comp_id, Category.id_comp]
    have hmono : Mono (ofRestrict A U).1 :=
        AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.mono _
    exact KLocallyRingedSpace.Hom.ext ((@cancel_mono _ _ _ _ _ (ofRestrict A U).1 hmono _ _).mp
      (congrArg (·.1) hK))
  let rᵢ := Hom.restrictTo ψᵢ' _ _ hmᵢ
  let rᵢp := Hom.restrictTo ψᵢK _ _ hmᵢp
  let rⱼ := Hom.restrictTo ψⱼK _ _ hmⱼ
  let rⱼ' := Hom.restrictTo ψⱼ' _ _ hmⱼ'
  have hrᵢ : IsIso rᵢ := ⟨⟨rᵢp, hinv ψᵢ' ψᵢK hψᵢ₂ _ _ hmᵢ hmᵢp, hinv ψᵢK ψᵢ' hψᵢ₁ _ _ hmᵢp hmᵢ⟩⟩
  have hrⱼ : IsIso rⱼ := ⟨⟨rⱼ', hinv ψⱼK ψⱼ' hψⱼ₁ _ _ hmⱼ hmⱼ', hinv ψⱼ' ψⱼK hψⱼ₂ _ _ hmⱼ' hmⱼ⟩⟩
  have := hθ
  refine ⟨P, hxP, le_inf (hPl.trans_eq hdomi) (hPr.trans_eq hdomj), rᵢ ≫ θ ≫ rⱼ, inferInstance,
    ?_, ?_⟩
  · -- over `X`
    have eK1 : (rᵢ ≫ θ ≫ rⱼ) ≫ ofRestrict _ _ = rᵢ ≫ θ ≫ (ofRestrict _ _ ≫ ψⱼK) := by
      rw [Category.assoc, Category.assoc, Hom.restrictTo_comp_ofRestrict]
    rw [eK1]
    simp only [Category.assoc]
    rw [hoverⱼ, ← Category.assoc θ, ← hover, ← Category.assoc, Hom.restrictTo_comp_ofRestrict,
      Category.assoc, hoverᵢ']
  · -- the members of every sum label
    intro σ
    -- the member chase on each side
    have hT₁ : QuotientSpace.comap ψᵢK.1 (D₁.sumLabelTrace bed V₁ hV₁ hbed o₁ lab₁ i σ) =
        QuotientSpace.comap ((sumPadData D₁ D₂).resIn bed (sumPadOpens D₁ D₂ W₁ W₂)
          (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed (Sum.inl i)).1
          ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ) := by
      have hR := comap_resIn_sumPadData_inl D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed i
        ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
          (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ)
      by_cases h : σ ∈ Set.range lab₁
      · obtain ⟨k, rfl⟩ := h
        have s1 := D₁.sumLabelTrace_lab bed V₁ hV₁ hbed o₁ lab₁ i k
        have s2 := (QuotientSpace.comap_comp ((D₁.resIn bed V₁ hV₁ hbed i).1)
          (D₁.sigmaMembers bed V₁ hV₁ hbed (o₁ k)) ψᵢK.1).symm
        have s3 : ψᵢK.1 ≫ (D₁.resIn bed V₁ hV₁ hbed i).1 =
            ((D₁.padLeftData D₂.n).resIn bed W₁ hW₁ hbed i).1 ≫ ψ₁.1 :=
          (congrArg (·.1) hsqᵢ).symm
        have s4 := QuotientSpace.comap_comp ψ₁.1 (D₁.sigmaMembers bed V₁ hV₁ hbed (o₁ k))
          ((D₁.padLeftData D₂.n).resIn bed W₁ hW₁ hbed i).1
        exact (congrArg (QuotientSpace.comap ψᵢK.1) s1).trans (s2.trans
          ((congrArg (fun φ => QuotientSpace.comap φ (D₁.sigmaMembers bed V₁ hV₁ hbed (o₁ k)))
              s3).trans
          (s4.trans ((congrArg (QuotientSpace.comap ((D₁.padLeftData D₂.n).resIn bed W₁ hW₁
              hbed i).1)
            ((hmem₁ k).trans (hlab₁ k).symm)).trans hR.symm))))
      · have hT := D₁.sumLabelTrace_of_not_mem_range bed V₁ hV₁ hbed o₁ lab₁ i h
        have hR2 := (congrArg (QuotientSpace.comap ((D₁.padLeftData D₂.n).resIn bed W₁ hW₁ hbed
            i).1)
          (hlab₁' σ h)).trans (QuotientSpace.comap_top_idealSheaf _)
        exact ((congrArg (QuotientSpace.comap ψᵢK.1) hT).trans
            (QuotientSpace.comap_top_idealSheaf _)).trans
          (hR.trans hR2).symm
    have hT₂ : QuotientSpace.comap ψⱼK.1 (D₂.sumLabelTrace bed V₂ hV₂ hbed o₂ lab₂ j σ) =
        QuotientSpace.comap ((sumPadData D₁ D₂).resIn bed (sumPadOpens D₁ D₂ W₁ W₂)
          (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed (Sum.inr j)).1
          ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ) := by
      have hR := comap_resIn_sumPadData_inr D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed j
        ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
          (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ)
      by_cases h : σ ∈ Set.range lab₂
      · obtain ⟨k, rfl⟩ := h
        have s1 := D₂.sumLabelTrace_lab bed V₂ hV₂ hbed o₂ lab₂ j k
        have s2 := (QuotientSpace.comap_comp ((D₂.resIn bed V₂ hV₂ hbed j).1)
          (D₂.sigmaMembers bed V₂ hV₂ hbed (o₂ k)) ψⱼK.1).symm
        have s3 : ψⱼK.1 ≫ (D₂.resIn bed V₂ hV₂ hbed j).1 =
            ((D₂.padRightData D₁.n).resIn bed W₂ hW₂ hbed j).1 ≫ ψ₂.1 :=
          (congrArg (·.1) hsqⱼ).symm
        have s4 := QuotientSpace.comap_comp ψ₂.1 (D₂.sigmaMembers bed V₂ hV₂ hbed (o₂ k))
          ((D₂.padRightData D₁.n).resIn bed W₂ hW₂ hbed j).1
        exact (congrArg (QuotientSpace.comap ψⱼK.1) s1).trans (s2.trans
          ((congrArg (fun φ => QuotientSpace.comap φ (D₂.sigmaMembers bed V₂ hV₂ hbed (o₂ k)))
              s3).trans
          (s4.trans ((congrArg (QuotientSpace.comap ((D₂.padRightData D₁.n).resIn bed W₂ hW₂
              hbed j).1)
            ((hmem₂ k).trans (hlab₂ k).symm)).trans hR.symm))))
      · have hT := D₂.sumLabelTrace_of_not_mem_range bed V₂ hV₂ hbed o₂ lab₂ j h
        have hR2 := (congrArg (QuotientSpace.comap ((D₂.padRightData D₁.n).resIn bed W₂ hW₂
            hbed j).1)
          (hlab₂' σ h)).trans (QuotientSpace.comap_top_idealSheaf _)
        exact ((congrArg (QuotientSpace.comap ψⱼK.1) hT).trans
            (QuotientSpace.comap_top_idealSheaf _)).trans
          (hR.trans hR2).symm
    -- the chain
    have e1 : ((rᵢ ≫ θ ≫ rⱼ) ≫ ofRestrict _ _).1 =
        rᵢ.1 ≫ θ.1 ≫ (ofRestrict _ _).1 ≫ ψⱼK.1 := by
      have : (rᵢ ≫ θ ≫ rⱼ) ≫ ofRestrict _ _ = rᵢ ≫ θ ≫ (ofRestrict _ _ ≫ ψⱼK) := by
        rw [Category.assoc, Category.assoc, Hom.restrictTo_comp_ofRestrict]
      exact congrArg (·.1) this
    have e2 : (rᵢ ≫ ofRestrict _ _).1 ≫ ψᵢK.1 = (ofRestrict _ _).1 := by
      have : rᵢ ≫ ofRestrict _ _ ≫ ψᵢK = ofRestrict _ _ := by
        rw [← Category.assoc, Hom.restrictTo_comp_ofRestrict, Category.assoc, hψᵢ₂,
          Category.comp_id]
      exact congrArg (·.1) this
    have s1 := congrArg (fun φ => QuotientSpace.comap φ (D₂.sumLabelTrace bed V₂ hV₂ hbed o₂
        lab₂ j σ)) e1
    have s2 := (QuotientSpace.comap_comp (θ.1 ≫ (ofRestrict _ _).1 ≫ ψⱼK.1)
      (D₂.sumLabelTrace bed V₂ hV₂ hbed o₂ lab₂ j σ) rᵢ.1).trans
      (congrArg (QuotientSpace.comap rᵢ.1) ((QuotientSpace.comap_comp ((ofRestrict _ _).1 ≫ ψⱼK.1)
        (D₂.sumLabelTrace bed V₂ hV₂ hbed o₂ lab₂ j σ) θ.1).trans
        (congrArg (QuotientSpace.comap θ.1) (QuotientSpace.comap_comp ψⱼK.1
          (D₂.sumLabelTrace bed V₂ hV₂ hbed o₂ lab₂ j σ) (ofRestrict _ _).1))))
    have s3 := congrArg (QuotientSpace.comap rᵢ.1)
      ((congrArg (fun C => QuotientSpace.comap θ.1 (QuotientSpace.comap (ofRestrict _ _).1 C))
          hT₂).trans
        ((hcl σ).trans (congrArg (QuotientSpace.comap (ofRestrict _ _).1) hT₁.symm)))
    have s4 := (QuotientSpace.comap_comp (ofRestrict _ _).1
      (QuotientSpace.comap ψᵢK.1 (D₁.sumLabelTrace bed V₁ hV₁ hbed o₁ lab₁ i σ)) rᵢ.1).symm.trans
      (QuotientSpace.comap_comp ψᵢK.1 (D₁.sumLabelTrace bed V₁ hV₁ hbed o₁ lab₁ i σ)
        (rᵢ.1 ≫ (ofRestrict _ _).1)).symm
    have s5 := congrArg (fun φ => QuotientSpace.comap φ (D₁.sumLabelTrace bed V₁ hV₁ hbed o₁
        lab₁ i σ)) e2
    exact s1.trans (s2.trans (s3.trans (s4.trans s5)))

end Conjugation

section Compat

variable {U : Set X} (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
  (Γ : D.ResolutionGluing bed) (hbed : bed.IsEmbeddedDesing)

/-- **The piece traces of the coproduct members are compatible along the gluing with the identity
labelling** ((37.2) in [Kol07, Proposition 37, proof]) — the hypothesis `hc` of `gluedMembersOn`
and `exists_gluedMembers_resolutionOn` (`CoproductGluedFamily.lean`). `hind` enters only through
the rigidity of the piece maps (`rigidOver_pieceToSpace`). -/
theorem labelledCompat_pieceTrace (hind : LocalResolutionIndependentOn X bed) :
    Γ.glue.LabelledCompat (pieceTrace D bed Γ hbed) (fun _ σ => σ) := by
  apply labelledCompat_pieceTrace_of_compat
  intro l i j
  -- the padded reading opens of the doubled datum
  let W₁ : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 ((D.padLeftData D.n).embedding i).G) :=
    fun i => padReadingOpens (Fin.castAddEmb D.n) (D.embedding i).G (Γ.W i)
  let W₂ : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 ((D.padRightData D.n).embedding i).G) :=
    fun i => padReadingOpens (Fin.natAddEmb D.n) (D.embedding i).G (Γ.W i)
  have hW₁ : ∀ i, IsCompact (closure (W₁ i : Set (pieceAmbient.{u} 𝕜
      ((D.padLeftData D.n).embedding i).G))) :=
    fun i => isCompact_closure_padReadingOpens _ _ (Γ.W i) (Γ.isCompact_closure_W i)
  have hW₂ : ∀ i, IsCompact (closure (W₂ i : Set (pieceAmbient.{u} 𝕜
      ((D.padRightData D.n).embedding i).G))) :=
    fun i => isCompact_closure_padReadingOpens _ _ (Γ.W i) (Γ.isCompact_closure_W i)
  have hpre₁ : D.padPreimageOpens (Fin.castAddEmb D.n) W₁ = Γ.W :=
    funext fun i => preimageOpens_padExt_padReadingOpens _ _ (Γ.W i)
  have hpre₂ : D.padPreimageOpens (Fin.natAddEmb D.n) W₂ = Γ.W :=
    funext fun i => preimageOpens_padExt_padReadingOpens _ _ (Γ.W i)
  -- the padding identities read at `Γ.W`, and the label embeddings of the doubled run
  obtain ⟨o₁, ψ₁, hψ₁, hmem₁, hpiece₁⟩ := D.exists_padIdentity_of_padPreimageOpens_eq
    (Fin.castAddEmb D.n) W₁ hW₁ bed hbed Γ.W Γ.isCompact_closure_W
    (D.padIdentityOn (Fin.castAddEmb D.n) W₁ hW₁ bed hbed) hpre₁
  obtain ⟨o₂, ψ₂, hψ₂, hmem₂, hpiece₂⟩ := D.exists_padIdentity_of_padPreimageOpens_eq
    (Fin.natAddEmb D.n) W₂ hW₂ bed hbed Γ.W Γ.isCompact_closure_W
    (D.padIdentityOn (Fin.natAddEmb D.n) W₂ hW₂ bed hbed) hpre₂
  obtain ⟨lab₁, hlab₁, hlab₁'⟩ :=
    exists_orderEmbedding_comap_sumInlResIn_sigmaMembers D D W₁ W₂ bed hW₁ hW₂ hbed
  obtain ⟨lab₂, hlab₂, hlab₂'⟩ :=
    exists_orderEmbedding_comap_sumInrResIn_sigmaMembers D D W₁ W₂ bed hW₁ hW₂ hbed
  -- the pointwise criterion, supplied point by point by the conjugation lemma at the diagonal pair
  refine Γ.glue.compatClosedSubspaces_pair_of_forall_exists_isoOver
    (fun i => pieceTrace D bed Γ hbed i l) i j fun y hy => ?_
  have hy' : KLocallyRingedSpace.Hom.toFun (D.pieceToSpace bed i (Γ.W i)
        (Γ.isCompact_closure_W i)) y ∈ D.pieceDom i (Γ.W i) ∧
      KLocallyRingedSpace.Hom.toFun (D.pieceToSpace bed i (Γ.W i) (Γ.isCompact_closure_W i)) y ∈
        D.pieceDom j (Γ.W j) := hy
  obtain ⟨P, hxP, hP, θ', hθ', hover', hcl'⟩ := D.exists_isoOver_pieces_of_sum D bed hbed W₁ hW₁
    W₂ hW₂ Γ.W Γ.isCompact_closure_W Γ.W Γ.isCompact_closure_W hpre₁ hpre₂ o₁ ψ₁ hmem₁ hpiece₁
    o₂ ψ₂ hmem₂ hpiece₂ lab₁ hlab₁ hlab₁' lab₂ hlab₂ hlab₂' i j _ hy'.1 hy'.2
  refine ⟨P, hP, hxP, D.rigidOver_pieceToSpace bed Γ.W Γ.isCompact_closure_W hbed hind i P
    (hP.trans inf_le_left), θ', hθ', hover', ?_⟩
  by_cases hl : D.sigmaMembers bed Γ.W Γ.isCompact_closure_W hbed l = ⊤
  · -- a trivial label: every piece trace is the unit ideal
    have h1 : pieceTrace D bed Γ hbed j l = ⊤ :=
      (congrArg (QuotientSpace.comap _) hl).trans (QuotientSpace.comap_top_idealSheaf _)
    have h2 : pieceTrace D bed Γ hbed i l = ⊤ :=
      (congrArg (QuotientSpace.comap _) hl).trans (QuotientSpace.comap_top_idealSheaf _)
    exact (congrArg (QuotientSpace.comap _) h1).trans ((QuotientSpace.comap_top_idealSheaf _).trans
      ((congrArg (QuotientSpace.comap _) h2).trans (QuotientSpace.comap_top_idealSheaf _)).symm)
  · -- a non-trivial label: the two label routes agree (`label_route_eq_of_ne_top`)
    have hσ := D.label_route_eq_of_ne_top bed hbed W₁ hW₁ W₂ hW₂ Γ.W Γ.isCompact_closure_W hpre₁
      hpre₂ o₁ ψ₁ hψ₁ hmem₁ o₂ ψ₂ hψ₂ hmem₂ lab₁ hlab₁ hlab₁' lab₂ hlab₂ hlab₂' l hl
    have h1 : pieceTrace D bed Γ hbed i l =
        D.sumLabelTrace bed Γ.W Γ.isCompact_closure_W hbed o₁ lab₁ i (lab₁ (o₁.symm l)) :=
      ((D.sumLabelTrace_lab bed Γ.W Γ.isCompact_closure_W hbed o₁ lab₁ i (o₁.symm l)).trans
        (congrArg (fun m => QuotientSpace.comap (D.resIn bed Γ.W Γ.isCompact_closure_W hbed i).1
          (D.sigmaMembers bed Γ.W Γ.isCompact_closure_W hbed m)) (o₁.apply_symm_apply l))).symm
    have h2' : pieceTrace D bed Γ hbed j l =
        D.sumLabelTrace bed Γ.W Γ.isCompact_closure_W hbed o₂ lab₂ j (lab₂ (o₂.symm l)) :=
      ((D.sumLabelTrace_lab bed Γ.W Γ.isCompact_closure_W hbed o₂ lab₂ j (o₂.symm l)).trans
        (congrArg (fun m => QuotientSpace.comap (D.resIn bed Γ.W Γ.isCompact_closure_W hbed j).1
          (D.sigmaMembers bed Γ.W Γ.isCompact_closure_W hbed m)) (o₂.apply_symm_apply l))).symm
    have h2 : pieceTrace D bed Γ hbed j l =
        D.sumLabelTrace bed Γ.W Γ.isCompact_closure_W hbed o₂ lab₂ j (lab₁ (o₁.symm l)) :=
      h2'.trans (congrArg (D.sumLabelTrace bed Γ.W Γ.isCompact_closure_W hbed o₂ lab₂ j) hσ.symm)
    exact (congrArg (QuotientSpace.comap _) h2).trans ((hcl' _).trans
      (congrArg (QuotientSpace.comap _) h1.symm))

end Compat

end Hironaka.Manifold.LocalEmbeddingData
