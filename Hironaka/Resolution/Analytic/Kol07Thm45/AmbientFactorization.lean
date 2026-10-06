/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.OverPart
public import Hironaka.AnalyticSpace.Resolution.Defs
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceTransition
public import Hironaka.Resolution.Analytic.Kol07Thm45.Resolution
import Hironaka.AnalyticSpace.ChartLift
import Hironaka.AnalyticSpace.HomOfSections
import Hironaka.AnalyticSpace.IsoOverOpen
import Hironaka.AnalyticSpace.SigmaLemmas
import Hironaka.Resolution.Analytic.Kol07Thm45.AmbientFactorizationTransport
import Hironaka.Resolution.Analytic.Kol07Thm45.AmbientLift
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueIndep
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The resolution is a locally finite ambient blow-up composite

Kollár's resolution functor is projective over every compact subset [Kol07, Theorem 45(4)];
Włodarczyk's `res_{Y,M}` factors locally into a sequence of blow-ups at smooth centres, the
factorization `(∗)` of [Wlo09, Theorem 2.0.2]. Here: over every relatively compact open `V ⊆ X`
the resolution map `Π_X` is the composite of a finite sequence of blow-ups of the disjoint union of
the pieces' ambients, restricted to strict transforms (clause (4) of `exists_functorial_resolution`,
`ResolutionAssembly.lean`). The steps: an exhaustion member `Uₙ ⊇ closure V`, the datum
`Dₙ` over `Uₙ` with its gluing `Γₙ`, the factorization of `AmbientLift.lean` at the SHRUNK family
`Γₙ.W i ⊓ Aᵢ` (`Aᵢ` the trace of `Uₙ` on the ambient — every open of a piece is the preimage of an
open of its ambient under the closed embedding `ambientPoint`), so that the pieces lie inside
`Uₙ`, and the transport `ofIsoOver`
(`Hironaka/Resolution/Analytic/Kol07Thm45/AmbientFactorizationTransport.lean`) along the exhaustion
glue's identification of the part of `R(X)` over `Uₙ` with `resolutionOn Dₙ`.

Not in the sources beyond the statements cited; bookkeeping.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace KLocallyRingedSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜]

section Piece

variable {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}

/-- Every open of the piece `X|V` is, through the closed embedding `ambientPoint`, the trace of an
open of the ambient `Gᵢ` (`IsInducing.isOpen_iff`). -/
theorem PieceEmbedding.exists_opens_embPreimage_eq (E : PieceEmbedding 𝕜 n X V) (O : Set X)
    (hO : IsOpen O) :
    ∃ A : Opens (pieceAmbient.{u} 𝕜 E.G), E.embPreimage A = Subtype.val ⁻¹' O := by
  obtain ⟨t, ht, hts⟩ := E.isClosedEmbedding_ambientPoint.toIsEmbedding.toIsInducing.isOpen_iff.mp
    (hO.preimage continuous_subtype_val)
  exact ⟨⟨t, ht⟩, hts⟩

end Piece

namespace LocalEmbeddingData

variable {X : AnalyticSpace.{u} 𝕜} {U : Set X}

/-- Shrinking the ambient open to the trace of `O` shrinks the base open to `O`:
`pieceDom i (W ⊓ A) = pieceDom i W ∩ O` when `embPreimage A = val ⁻¹' O`. -/
theorem pieceDom_inf_eq_inter (D : LocalEmbeddingData 𝕜 X U) (i : D.ι)
    (W A : Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G)) (O : Set X)
    (hA : (D.embedding i).embPreimage A = Subtype.val ⁻¹' O) :
    (D.pieceDom i (W ⊓ A) : Set X) = (D.pieceDom i W : Set X) ∩ O := by
  have h0 : (D.embedding i).embPreimage (W ⊓ A) =
      (D.embedding i).embPreimage W ∩ (D.embedding i).embPreimage A := rfl
  have h : (D.embedding i).embPreimage (W ⊓ A) =
      (D.embedding i).embPreimage W ∩ Subtype.val ⁻¹' O :=
    h0.trans (congrArg (fun s => (D.embedding i).embPreimage W ∩ s) hA)
  exact (congrArg (fun s => Subtype.val '' s) h).trans (Set.image_inter_preimage _ _ _)

/-- **The ambient blow-up factorization at any open `V ⊆ U`, with the pieces inside a prescribed
open `O ⊇ V`** ([Kol07, Theorem 45(4)]): the factorization of the glued space's map at the gluing
datum with the shrunk family `Γ.W i ⊓ Aᵢ` (`Aᵢ` the trace of `O`), with the independence of the
local resolution as `hind`. -/
theorem exists_ambientBlowUpFactorization_resolutionOnFullMap_of_subset
    (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) (V O : Set X) (hO : IsOpen O) (hVO : V ⊆ O)
    (hVU : V ⊆ U) :
    ∃ F : (D.resolutionOnFullMap bed).AmbientBlowUpFactorization V,
      ∀ i, F.piece i ⊆ O := by
  have h : D.ResolutionGluesOn bed :=
    D.resolutionGluesOn_of_isEmbeddedDesing_of_independent bed hbed hind
  choose A hA using fun i => (D.embedding i).exists_opens_embPreimage_eq O hO
  have hW' : ∀ i, IsCompact (closure ((h.some.W i ⊓ A i : Opens (pieceAmbient.{u} 𝕜
      (D.embedding i).G)) : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))) := fun i =>
    (h.some.isCompact_closure_W i).of_isClosed_subset isClosed_closure
      (closure_mono fun _ hx => hx.1)
  have hle : ∀ i, h.some.W i ⊓ A i ≤ h.some.W i := fun i => inf_le_left
  have hpd : ∀ i, (D.pieceDom i (h.some.W i ⊓ A i) : Set X) =
      (D.pieceDom i (h.some.W i) : Set X) ∩ O :=
    fun i => D.pieceDom_inf_eq_inter i _ _ O (hA i)
  have hcov : V ⊆ ⋃ i, (D.pieceDom i (h.some.W i ⊓ A i) : Set X) := fun x hx => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (D.subset_iUnion_inner (hVU hx))
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [hpd i]
    exact ⟨h.some.closure_inner_subset_pieceDom i (subset_closure hi), hVO hx⟩
  have hpieces : ∀ i, (D.pieceDom i (h.some.W i ⊓ A i) : Set X) ⊆ O := fun i => by
    rw [hpd i]
    exact Set.inter_subset_right
  change ∃ F : ((D.resolutionOnFullPair bed).2).AmbientBlowUpFactorization V, ∀ i, F.piece i ⊆ O
  rw [D.resolutionOnFullPair_eq_of_glues bed h]
  exact ⟨D.ambientBlowUpFactorizationOfGluing bed h.some _ hW' hle hbed V hcov, hpieces⟩

end LocalEmbeddingData

namespace BEDanFamStar

variable (bed : BEDanFamStar.{u} 𝕜) (X : AnalyticSpace.{u} 𝕜)

/-- A relatively compact open lies in some member of the exhaustion
(`IsCompact.elim_directed_cover` on the increasing `Uₙ`). -/
theorem ExhaustionGluing.exists_closure_subset_U (Ξ : bed.ExhaustionGluing X) (V : Set X)
    (hV : IsCompact (closure V)) : ∃ n, closure V ⊆ Ξ.U n := by
  have hmono : Monotone fun n => (Ξ.U n : Set X) :=
    monotone_nat_of_le_succ fun n => subset_closure.trans (Ξ.closure_U_subset_succ n)
  exact hV.elim_directed_cover (fun n => (Ξ.U n : Set X)) (fun n => (Ξ.U n).isOpen)
    (by rw [Ξ.iUnion_U]; exact Set.subset_univ _) hmono.directed_le

/-- The two spellings of the part of `R(X)` over `Uₙ`. Internal. -/
theorem ExhaustionGluing.coe_openOf_preimage_U (Ξ : bed.ExhaustionGluing X) (n : ℕ) :
    ((openOf Ξ.glue.gluedOver
        (KLocallyRingedSpace.Hom.toFun Ξ.glue.descMap ⁻¹' (Ξ.U n : Set X)) :
      Opens Ξ.glue.gluedOver.toKLocallyRingedSpace) : Set Ξ.glue.gluedOver.toKLocallyRingedSpace) =
      (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun Ξ.glue.descMap, Hom.continuous_toFun _⟩
        (Ξ.U n) : Set Ξ.glue.gluedOver.toKLocallyRingedSpace) := by
  rw [openOf_of_isOpen _
    ((Ξ.U n).isOpen.preimage (Hom.continuous_toFun _))]
  rfl

/-- The part of the piece `resolutionOn Dₙ` over `Uₙ` is the whole piece (`range_subset`).
Internal. -/
theorem ExhaustionGluing.coe_comap_resolutionOnToSpace_U (Ξ : bed.ExhaustionGluing X) (n : ℕ) :
    ((Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((Ξ.D n).resolutionOnToSpace bed),
        Hom.continuous_toFun _⟩ (Ξ.U n) :
      Opens ((Ξ.D n).resolutionOn bed).toKLocallyRingedSpace) :
        Set ((Ξ.D n).resolutionOn bed).toKLocallyRingedSpace) =
      ((⊤ : Opens ((Ξ.D n).resolutionOn bed).toKLocallyRingedSpace) :
        Set ((Ξ.D n).resolutionOn bed).toKLocallyRingedSpace) :=
  Set.eq_univ_of_forall fun r => Ξ.glue.range_subset ⟨n⟩ ⟨r, rfl⟩

/-- **The part of `R(X)` over `Uₙ` IS `resolutionOn (D n) bed`**: the exhaustion glue's
`partIso` at `Uₙ = dom n` (the part of the piece over `Uₙ` is the whole piece, `range_subset`). -/
def ExhaustionGluing.resolutionOnIso (Ξ : bed.ExhaustionGluing X) (n : ℕ) :
    (restrictSet Ξ.glue.gluedOver
        (KLocallyRingedSpace.Hom.toFun Ξ.glue.descMap ⁻¹' (Ξ.U n : Set X))).toKLocallyRingedSpace ≅
      ((Ξ.D n).resolutionOn bed).toKLocallyRingedSpace :=
  (restrictOpenIsoOfSetEq (ExhaustionGluing.coe_openOf_preimage_U bed X Ξ n)).trans
    ((Ξ.glue.partIso ⟨n⟩ (Ξ.U n) le_rfl).symm.trans
      ((restrictOpenIsoOfSetEq (ExhaustionGluing.coe_comap_resolutionOnToSpace_U bed X Ξ n)).trans
        (restrictOpenTopIso _)))

/-- It lies over `X|Uₙ`: `Π_{Uₙ} ∘ e = des|Uₙ` (the hypothesis `hcomm` of the transport
`ofIsoOver`). -/
theorem ExhaustionGluing.resolutionOnMap_comp_resolutionOnIso (Ξ : bed.ExhaustionGluing X)
    (n : ℕ) :
    ((ExhaustionGluing.resolutionOnIso bed X Ξ n).hom : restrictSet Ξ.glue.gluedOver
        (KLocallyRingedSpace.Hom.toFun Ξ.glue.descMap ⁻¹'
        (Ξ.U n : Set X)) ⟶ (Ξ.D n).resolutionOn bed) ≫ (Ξ.D n).resolutionOnMap bed =
      AnalyticSpace.Hom.restrictSet (Ξ.glue.descMap : Ξ.glue.gluedOver ⟶ X) (Ξ.U n : Set X) := by
  obtain ⟨M, hM⟩ : ∃ M : ((Ξ.D n).resolutionOn bed).toKLocallyRingedSpace ⟶
      (X.restrictSet (Ξ.U n : Set X)).toKLocallyRingedSpace, M = (Ξ.D n).resolutionOnMap bed :=
    ⟨_, rfl⟩
  obtain ⟨dr, hdr⟩ : ∃ dr : (restrictSet Ξ.glue.gluedOver
        (KLocallyRingedSpace.Hom.toFun Ξ.glue.descMap ⁻¹' (Ξ.U n : Set X))).toKLocallyRingedSpace ⟶
      (X.restrictSet (Ξ.U n : Set X)).toKLocallyRingedSpace,
      dr = Hom.restrictSet Ξ.glue.descMap (Ξ.U n : Set X) :=
    ⟨_, rfl⟩
  have hdr' : dr ≫ ofRestrict X.toKLocallyRingedSpace
      (openOf X (Ξ.U n : Set X)) =
      ofRestrict Ξ.glue.gluedOver.toKLocallyRingedSpace
        (openOf _
          (KLocallyRingedSpace.Hom.toFun Ξ.glue.descMap ⁻¹' (Ξ.U n : Set X))) ≫
      Ξ.glue.descMap := by
    rw [hdr]
    exact Hom.restrictTo_comp_ofRestrict Ξ.glue.descMap _ _
      (Hom.mapsTo_openOf Ξ.glue.descMap _)
  -- the composite `e ≫ π_n`, with the piece map named as a `K`-morphism
  obtain ⟨p, hp⟩ : ∃ p : ((Ξ.D n).resolutionOn bed).toKLocallyRingedSpace ⟶
      X.toKLocallyRingedSpace, p = (Ξ.D n).resolutionOnToSpace bed := ⟨_, rfl⟩
  have hd : (restrictOpenTopIso ((Ξ.D n).resolutionOn bed).toKLocallyRingedSpace).hom =
      ofRestrict ((Ξ.D n).resolutionOn bed).toKLocallyRingedSpace ⊤ :=
    restrictOpenTopIso_hom _
  have hc : (restrictOpenIsoOfSetEq
        (ExhaustionGluing.coe_comap_resolutionOnToSpace_U bed X Ξ n)).hom ≫
      ofRestrict ((Ξ.D n).resolutionOn bed).toKLocallyRingedSpace ⊤ =
      ofRestrict ((Ξ.D n).resolutionOn bed).toKLocallyRingedSpace
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((Ξ.D n).resolutionOnToSpace bed),
          Hom.continuous_toFun _⟩ (Ξ.U n)) :=
    restrictOpenIsoOfSetEq_hom_comp _
  have hb : (Ξ.glue.partIso ⟨n⟩ (Ξ.U n) le_rfl).inv ≫
      ofRestrict ((Ξ.D n).resolutionOn bed).toKLocallyRingedSpace
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((Ξ.D n).resolutionOnToSpace bed),
          Hom.continuous_toFun _⟩ (Ξ.U n)) ≫ p =
      ofRestrict Ξ.glue.gluedOver.toKLocallyRingedSpace
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun Ξ.glue.descMap, Hom.continuous_toFun _⟩
          (Ξ.U n)) ≫ Ξ.glue.descMap := by
    rw [hp]
    exact Ξ.glue.partIso_inv_comp_over ⟨n⟩ (Ξ.U n) le_rfl
  have ha : (restrictOpenIsoOfSetEq (ExhaustionGluing.coe_openOf_preimage_U bed X Ξ n)).hom ≫
      ofRestrict Ξ.glue.gluedOver.toKLocallyRingedSpace
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun Ξ.glue.descMap, Hom.continuous_toFun _⟩
          (Ξ.U n)) =
      ofRestrict Ξ.glue.gluedOver.toKLocallyRingedSpace
        (openOf _
          (KLocallyRingedSpace.Hom.toFun Ξ.glue.descMap ⁻¹' (Ξ.U n : Set X))) :=
    restrictOpenIsoOfSetEq_hom_comp _
  have he : (ExhaustionGluing.resolutionOnIso bed X Ξ n).hom ≫ p =
      ofRestrict Ξ.glue.gluedOver.toKLocallyRingedSpace
        (openOf _
          (KLocallyRingedSpace.Hom.toFun Ξ.glue.descMap ⁻¹' (Ξ.U n : Set X))) ≫
      Ξ.glue.descMap := by
    unfold ExhaustionGluing.resolutionOnIso
    exact (Category.assoc _ _ _).trans ((congrArg
      (fun k => (restrictOpenIsoOfSetEq (ExhaustionGluing.coe_openOf_preimage_U bed X Ξ n)).hom ≫ k)
      ((Category.assoc _ _ _).trans ((congrArg
        (fun k => (Ξ.glue.partIso ⟨n⟩ (Ξ.U n) le_rfl).inv ≫ k)
        ((Category.assoc _ _ _).trans ((congrArg (fun k => (restrictOpenIsoOfSetEq
            (ExhaustionGluing.coe_comap_resolutionOnToSpace_U bed X Ξ n)).hom ≫ k)
            (congrArg (fun k => k ≫ p) hd)).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ p) hc))))).trans hb))).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ Ξ.glue.descMap) ha)))
  have hM' : M ≫ ofRestrict X.toKLocallyRingedSpace
      (openOf X (Ξ.U n : Set X)) = p := by
    rw [hM, hp]; rfl
  have hK : (ExhaustionGluing.resolutionOnIso bed X Ξ n).hom ≫ M = dr := by
    refine Hom.ext_of_comp_ofRestrict ?_
    exact (Category.assoc _ _ _).trans ((congrArg
      (fun k => (ExhaustionGluing.resolutionOnIso bed X Ξ n).hom ≫ k) hM').trans
      (he.trans hdr'.symm))
  subst hM hdr
  exact hK

/-- **`Π_X` is a locally finite ambient blow-up composite** (clause (4) of
`exists_functorial_resolution`; [Kol07, Theorem 45(4)]; the local factorization `(∗)` of
[Wlo09, Theorem 2.0.2]), with the independence of the local resolution as `hind`: over every
relatively compact open `V`, the factorization of the glued space over the exhaustion member
`Uₙ ⊇ closure V` with its pieces inside `Uₙ`, transported along the part identification
(`ofIsoOver`). -/
theorem isLocallyFiniteAmbientBlowUpComposite_resolutionMap_of_independent (hX : X.IsReduced)
    (hbed : bed.IsEmbeddedDesing) (hind : LocalResolutionIndependentOn X bed) :
    (bed.resolutionMap X).IsLocallyFiniteAmbientBlowUpComposite := by
  have h := resolutionGlues_of_isEmbeddedDesing_of_independent X hX bed hbed hind
  change ((bed.resolutionPair X).2).IsLocallyFiniteAmbientBlowUpComposite
  rw [bed.resolutionPair_eq_of_glues X hX h]
  intro V _ hVc
  obtain ⟨n, hn⟩ := ExhaustionGluing.exists_closure_subset_U bed X h.some V hVc
  have hVU : V ⊆ h.some.U n := subset_closure.trans hn
  obtain ⟨F, hpieces⟩ :=
    (h.some.D n).exists_ambientBlowUpFactorization_resolutionOnFullMap_of_subset bed hbed hind V
      (h.some.U n) (h.some.U n).isOpen hVU hVU
  exact ⟨AmbientBlowUpFactorization.ofIsoOver (h.some.U n).isOpen
    hVU (ExhaustionGluing.resolutionOnIso bed X h.some n).hom
    (isIso_of_isIso_toKLocallyRingedSpace _ (Iso.isIso_hom _))
    (ExhaustionGluing.resolutionOnMap_comp_resolutionOnIso bed X h.some n) F hpieces⟩

end BEDanFamStar

end Hironaka.Manifold

end
