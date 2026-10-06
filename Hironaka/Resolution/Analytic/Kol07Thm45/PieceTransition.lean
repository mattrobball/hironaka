/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueProof
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceRestrict
import Hironaka.AnalyticSpace.Exhaustion
import Hironaka.AnalyticSpace.Glue.Normalize
import Hironaka.AnalyticSpace.HomOfSections
import Hironaka.AnalyticSpace.IsoOverOpen
import Hironaka.AnalyticSpace.Lemmas
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceRestrictResolution
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Metrizable.Urysohn

/-!
# The transitions of the gluing datum: the local data

Włodarczyk glues the canonical desingularizations `Ṽ_i` of the local embeddings along the
isomorphisms over the overlaps `Ṽ_i ∩ Ṽ_j` [Wlo09, §4, (3)⇒(4)]; Kollár glues the local
resolutions of the affine pieces by a formal property of blow-up sequence functors
[Kol07, Theorem 36, proof]. Here the transition between two pieces of the gluing datum is
assembled LOCAL-TO-GLOBAL from the independence of the local resolution from the embedding
(`LocalResolutionIndependentOn`: the local resolutions of two embeddings of the same piece are
isomorphic over the piece by a unique isomorphism), applied to the two embeddings RESTRICTED
(`PieceRestrict.lean`) to small opens of the overlap, transported (`PieceRestrictResolution.lean`)
and glued. This module holds the topological data of one point of the overlap:

* `exists_nested_opens_of_isOpen`: two nested relatively compact opens `z ∈ N`,
  `closure N ⊆ N'`, `closure N' ⊆ O'` (Mathlib's `exists_open_between_and_isCompact_closure`, the
  space being locally compact Hausdorff);
* `PieceEmbedding.exists_restrictAmbientOpens`: for the embedding restricted to `N'`, a relatively
  compact ambient open `W' ⋐ G'_{N'}` whose image lies in the piece's ambient open `W` and which
  contains the compact ambient image of `closure N` (`exists_opens_isCompact_closure_superset`
  inside `G'_{N'} ⊓ g⁻¹(W)`);
* `PieceEmbedding.mem_embPreimage_restrictPiece_iff_mem_domOpens` and
  `domOpens_pieceAmbientImageOpens_subset`: the points of the restricted embedding over `W'` are
  the points of `X` in the base open `domOpens (g W')`, and that base open lies inside `N'` (the
  shrunk ambient sees no point outside `N'`);
* `LocalEmbeddingData.exists_transitionData`: the package for two pieces `i`, `j` and a point `z`
  of an open `O'` of their common base open;
* `exists_transition_over_pair` and `LocalEmbeddingData.exists_transition_over`: the local
  transition over the cover member `P_z`, unique among the isomorphisms over `X`.

Not in the sources beyond the gluing remarks; bookkeeping.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace KLocallyRingedSpace
open scoped Manifold ContDiff

universe u

namespace CategoryTheory

variable {C : Type*} [Category C]

/-- The compatibility over the base of a morphism obtained by transporting a morphism `ψ` over the
base along four identifications, in any category — the transport's associativity bookkeeping. -/
theorem transport_over_eq {A'i₀ A'i Ai A'j₀ A'j Aj Y'i Yi Y'j Yj Z : C}
    (αi_inv : Ai ⟶ A'i) (αi_hom : A'i ⟶ Ai) (hαi : αi_inv ≫ αi_hom = 𝟙 Ai)
    (ρi_inv : A'i ⟶ A'i₀) (ρj_hom : A'j₀ ⟶ A'j) (αj_hom : A'j ⟶ Aj) (ψ : A'i₀ ⟶ A'j₀)
    (ofRi : Ai ⟶ Yi) (ofRj : Aj ⟶ Yj) (ofR'i : A'i ⟶ Y'i) (ofR'j : A'j ⟶ Y'j)
    (ofR'i₀ : A'i₀ ⟶ Y'i) (ofR'j₀ : A'j₀ ⟶ Y'j)
    (πi : Yi ⟶ Z) (πj : Yj ⟶ Z) (π'i : Y'i ⟶ Z) (π'j : Y'j ⟶ Z)
    (hρi : ρi_inv ≫ ofR'i₀ = ofR'i) (hρj : ρj_hom ≫ ofR'j = ofR'j₀)
    (hαi_over : αi_hom ≫ ofRi ≫ πi = ofR'i ≫ π'i) (hαj_over : αj_hom ≫ ofRj ≫ πj = ofR'j ≫ π'j)
    (hψ : (ψ ≫ ofR'j₀) ≫ π'j = ofR'i₀ ≫ π'i) :
    ofRi ≫ πi = ((αi_inv ≫ ρi_inv ≫ ψ ≫ ρj_hom ≫ αj_hom) ≫ ofRj) ≫ πj := by
  simp only [Category.assoc]
  rw [hαj_over, ← Category.assoc ρj_hom, hρj, ← Category.assoc ψ, hψ, ← Category.assoc ρi_inv,
    hρi, ← hαi_over, ← Category.assoc αi_inv, hαi, Category.id_comp]

/-- A morphism whose transport is `ψ` is the transport of `ψ` back — the four identifications
being inverse pairs. -/
theorem eq_transport_of_transport_eq {A'i₀ A'i Ai A'j₀ A'j Aj : C}
    (αi_inv : Ai ⟶ A'i) (αi_hom : A'i ⟶ Ai) (hαi : αi_inv ≫ αi_hom = 𝟙 Ai)
    (αj_inv : Aj ⟶ A'j) (αj_hom : A'j ⟶ Aj) (hαj : αj_inv ≫ αj_hom = 𝟙 Aj)
    (ρi_inv : A'i ⟶ A'i₀) (ρi_hom : A'i₀ ⟶ A'i) (hρi : ρi_inv ≫ ρi_hom = 𝟙 A'i)
    (ρj_inv : A'j ⟶ A'j₀) (ρj_hom : A'j₀ ⟶ A'j) (hρj : ρj_inv ≫ ρj_hom = 𝟙 A'j)
    (s : Ai ⟶ Aj) (ψ : A'i₀ ⟶ A'j₀) (hψ : ρi_hom ≫ αi_hom ≫ s ≫ αj_inv ≫ ρj_inv = ψ) :
    s = αi_inv ≫ ρi_inv ≫ ψ ≫ ρj_hom ≫ αj_hom := by
  rw [← hψ]
  simp only [Category.assoc]
  rw [← Category.assoc ρi_inv, hρi, Category.id_comp, ← Category.assoc αi_inv, hαi,
    Category.id_comp, ← Category.assoc ρj_inv, hρj, Category.id_comp, hαj, Category.comp_id]

/-- The inverse of an identification over the base is over the base. -/
theorem inv_over_of_over {A' A Y' Y Z : C} (α_inv : A ⟶ A') (α_hom : A' ⟶ A)
    (hα : α_inv ≫ α_hom = 𝟙 A) (ofR : A ⟶ Y) (ofR' : A' ⟶ Y') (π : Y ⟶ Z) (π' : Y' ⟶ Z)
    (hα_over : α_hom ≫ ofR ≫ π = ofR' ≫ π') : α_inv ≫ ofR' ≫ π' = ofR ≫ π := by
  rw [← hα_over, ← Category.assoc, hα, Category.id_comp]

/-- A morphism over the base, transported BACK along the four identifications, is over the base —
the uniqueness step's bookkeeping. -/
theorem transport_back_over_eq {A'i₀ A'i Ai A'j₀ A'j Aj Y'i Yi Y'j Yj Z : C}
    (ρi_hom : A'i₀ ⟶ A'i) (αi_hom : A'i ⟶ Ai) (s : Ai ⟶ Aj) (αj_inv : Aj ⟶ A'j)
    (ρj_inv : A'j ⟶ A'j₀)
    (ofRi : Ai ⟶ Yi) (ofRj : Aj ⟶ Yj) (ofR'i : A'i ⟶ Y'i) (ofR'j : A'j ⟶ Y'j)
    (ofR'i₀ : A'i₀ ⟶ Y'i) (ofR'j₀ : A'j₀ ⟶ Y'j)
    (πi : Yi ⟶ Z) (πj : Yj ⟶ Z) (π'i : Y'i ⟶ Z) (π'j : Y'j ⟶ Z)
    (hρi : ρi_hom ≫ ofR'i = ofR'i₀) (hρj : ρj_inv ≫ ofR'j₀ = ofR'j)
    (hαi_over : αi_hom ≫ ofRi ≫ πi = ofR'i ≫ π'i) (hαj_inv_over : αj_inv ≫ ofR'j ≫ π'j = ofRj ≫ πj)
    (hs : ofRi ≫ πi = (s ≫ ofRj) ≫ πj) :
    ((ρi_hom ≫ αi_hom ≫ s ≫ αj_inv ≫ ρj_inv) ≫ ofR'j₀) ≫ π'j = ofR'i₀ ≫ π'i := by
  simp only [Category.assoc]
  rw [← Category.assoc ρj_inv, hρj, hαj_inv_over, ← Category.assoc s, ← hs, hαi_over,
    ← Category.assoc ρi_hom, hρi]

/-- A morphism over a piece `B` of the base (through the open immersion `o` of the part over `S`)
is over the base — the compatibility of the independence's `ψ` read after the open immersion
`p : B → Z`. -/
theorem comp_over_of_comp_restrict_eq {A'i₀ A'j₀ Y'i Y'j Rj B Z : C}
    (ψ : A'i₀ ⟶ A'j₀) (ri : A'i₀ ⟶ Rj) (rj : A'j₀ ⟶ Rj) (o : Rj ⟶ B)
    (ofi : A'i₀ ⟶ Y'i) (ofj : A'j₀ ⟶ Y'j) (fi : Y'i ⟶ B) (fj : Y'j ⟶ B) (p : B ⟶ Z)
    (hψ : ψ ≫ rj = ri) (hrj : rj ≫ o = ofj ≫ fj) (hri : ri ≫ o = ofi ≫ fi) :
    (ψ ≫ ofj) ≫ fj ≫ p = ofi ≫ fi ≫ p := by
  rw [← Category.assoc ofi, ← hri, ← hψ]
  simp only [Category.assoc]
  rw [← Category.assoc rj, hrj, Category.assoc]

end CategoryTheory

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- The open subspaces of two opens with the same underlying set are isomorphic — `isoOfRangeEq`
of the two open immersions (no `eqToIso`). -/
def restrictOpenIsoOfSetEq {X : KLocallyRingedSpace.{u} K} {U₁ U₂ : Opens X}
    (h : (U₁ : Set X) = U₂) : X.restrictOpen U₁ ≅ X.restrictOpen U₂ :=
  isoOfRangeEq (ofRestrict X U₁) (ofRestrict X U₂)
    ((range_toFun_ofRestrict X U₁).trans (h.trans (range_toFun_ofRestrict X U₂).symm))

/-- Its `hom` lies over `X`. -/
theorem restrictOpenIsoOfSetEq_hom_comp {X : KLocallyRingedSpace.{u} K} {U₁ U₂ : Opens X}
    (h : (U₁ : Set X) = U₂) :
    (restrictOpenIsoOfSetEq h).hom ≫ ofRestrict X U₂ = ofRestrict X U₁ :=
  isoOfRangeEq_hom_comp _ _ _

/-- Its `inv` lies over `X`. -/
theorem restrictOpenIsoOfSetEq_inv_comp {X : KLocallyRingedSpace.{u} K} {U₁ U₂ : Opens X}
    (h : (U₁ : Set X) = U₂) :
    (restrictOpenIsoOfSetEq h).inv ≫ ofRestrict X U₁ = ofRestrict X U₂ :=
  Glue.isoOfRangeEq_inv_comp _ _ _

end AnalyticSpace.KLocallyRingedSpace

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜]

/-! ### The two nested relatively compact opens -/

/-- Around a point `z` of an open `O'`, two nested opens with compact closures, `z ∈ N`,
`closure N ⊆ N'`, `closure N' ⊆ O'` (Mathlib's `exists_open_between_and_isCompact_closure` twice,
the analytic space being locally compact Hausdorff). -/
theorem exists_nested_opens_of_isOpen {X : AnalyticSpace.{u} 𝕜} {O' : Set X}
    (hO' : IsOpen O') {z : X} (hz : z ∈ O') :
    ∃ N' N : Set X, IsOpen N' ∧ IsCompact (closure N') ∧ closure N' ⊆ O' ∧
      IsOpen N ∧ z ∈ N ∧ IsCompact (closure N) ∧ closure N ⊆ N' := by
  have : LocallyCompactSpace X := locallyCompactSpace (X := X)
  have : T2Space X := t2 X
  obtain ⟨N', hN'o, hzN', hN'O', hN'c⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := z)) hO' (singleton_subset_iff.mpr hz)
  obtain ⟨N, hNo, hzN, hNN', hNc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := z)) hN'o hzN'
  exact ⟨N', N, hN'o, hN'c, hN'O', hNo, singleton_subset_iff.mp hzN, hNc, hNN'⟩

namespace PieceEmbedding

variable {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V)

/-! ### The base opens and the restricted embedding -/

/-- The base open of the piece over any ambient open lies in the piece (an open `V`). -/
theorem domOpens_subset (hV : IsOpen V) (W : Opens (pieceAmbient.{u} 𝕜 E.G)) :
    (E.domOpens W : Set X) ⊆ V := fun _ hx => by
  obtain ⟨y, -, rfl⟩ := (E.mem_domOpens).mp hx
  exact mem_of_mem_openOf hV y.2

/-- The base open of the piece over the image of an ambient open of the SHRUNK ambient `G'_{V'}`
lies in `V'` — the shrunk ambient sees no point of the piece outside `V'`
(`pieceCoord_ambientPoint_mem_restrictAmbient_iff`). -/
theorem domOpens_pieceAmbientImageOpens_subset {V' : Set X} (hV' : IsOpen V')
    (W' : Opens (pieceAmbient.{u} 𝕜 (E.restrictAmbient hV'))) :
    (E.domOpens (pieceAmbientImageOpens (E.restrictAmbient_le hV') W') : Set X) ⊆ V' :=
  fun _ hx => by
    obtain ⟨y, hy, rfl⟩ := (E.mem_domOpens).mp hx
    obtain ⟨w, -, hw⟩ := hy
    have hcoord : pieceCoord E.G (E.ambientPoint y) = pieceCoord (E.restrictAmbient hV') w :=
      (congrArg (pieceCoord E.G) hw).symm.trans
        (pieceCoord_pieceAmbientIncl (E.restrictAmbient_le hV') w)
    exact (E.pieceCoord_ambientPoint_mem_restrictAmbient_iff hV' y).mp
      (Set.mem_of_eq_of_mem hcoord (pieceCoord_mem (E.restrictAmbient hV') w))

/-- A point of the restricted piece `X|V'` lies over the ambient open `W'` of the shrunk ambient
iff, as a point of `X`, it lies in the base open of the piece over the image `g(W')`
(`embPreimage_restrictPiece`). -/
theorem mem_embPreimage_restrictPiece_iff_mem_domOpens {V' : Set X} (hV' : IsOpen V')
    (hsub : V' ⊆ V) (W' : Opens (pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')))
        (y' : X.restrictSet V') :
    y' ∈ (E.restrictPiece hV' hsub).embPreimage W' ↔
      Subtype.val y' ∈ E.domOpens (pieceAmbientImageOpens (E.restrictAmbient_le hV') W') :=
  (E.embPreimage_restrictPiece hV' hsub W' y').trans
    ⟨fun h => (E.mem_domOpens).mpr ⟨⟨Subtype.val y', val_mem_openOf hV' hsub y'⟩, h, rfl⟩,
      fun h => by
        obtain ⟨y, hy, hyv⟩ := (E.mem_domOpens).mp h
        exact Set.mem_of_eq_of_mem (congrArg E.ambientPoint (Subtype.ext hyv :
          y = (⟨Subtype.val y', val_mem_openOf hV' hsub y'⟩ : X.restrictSet V)).symm) hy⟩

/-! ### The ambient open of the restricted embedding around a compact -/

/-- For a compact `closure N ⊆ V'` whose points of the piece lie over `W`, a relatively compact
ambient open `W'` of the SHRUNK ambient whose image lies in `W` and over which every point of
`closure N` lies (Włodarczyk's `V̄_i ⊂ W_i` at the restricted embedding, [Wlo09, §4, (3)⇒(4)];
`exists_opens_isCompact_closure_superset` inside `G'_{V'} ⊓ g⁻¹(W)`). The compact is the ambient
image of `closure N` pulled into `X|V'` (`Subtype.isCompact_iff`, the closed embedding
`ambientPoint`). -/
theorem exists_restrictAmbientOpens {V' : Set X} (hV' : IsOpen V') (hsub : V' ⊆ V)
    (W : Opens (pieceAmbient.{u} 𝕜 E.G)) {N : Set X} (hNc : IsCompact (closure N))
    (hNV' : closure N ⊆ V')
    (hNW : ∀ y : X.restrictSet V, Subtype.val y ∈ closure N → y ∈ E.embPreimage W) :
    ∃ W' : Opens (pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')),
      IsCompact (closure (W' : Set (pieceAmbient 𝕜 (E.restrictAmbient hV')))) ∧
        pieceAmbientImageOpens (E.restrictAmbient_le hV') W' ≤ W ∧
        ∀ y' : X.restrictSet V', Subtype.val y' ∈ closure N →
          y' ∈ (E.restrictPiece hV' hsub).embPreimage W' := by
  -- the compact `closure N`, pulled into the restricted piece
  have hK₀ : IsCompact ((Subtype.val :
      {x // x ∈ openOf X V'} → X) ''
        (Subtype.val ⁻¹' closure N)) :=
    (congrArg IsCompact (Set.image_preimage_eq_of_subset fun x hx =>
      ⟨⟨x, mem_openOf_of_subset Set.Subset.rfl (hNV' hx)⟩,
        rfl⟩)).mpr hNc
  have hK : IsCompact ((E.restrictPiece hV' hsub).ambientPoint ''
      (Subtype.val ⁻¹' closure N : Set (X.restrictSet V')) :
        Set (pieceAmbient.{u} 𝕜 (E.restrictAmbient hV'))) :=
    IsCompact.image ((Subtype.isCompact_iff
        (p := fun x => x ∈ openOf X V')
        (s := Subtype.val ⁻¹' closure N)).mpr hK₀)
      (E.restrictPiece hV' hsub).isClosedEmbedding_ambientPoint.continuous
  -- a relatively compact open around it in the locally compact Hausdorff shrunk ambient
  have : LocallyCompactSpace (pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')) :=
    ChartedSpace.locallyCompactSpace (H := Fin n → 𝕜)
      (M := pieceAmbient.{u} 𝕜 (E.restrictAmbient hV'))
  obtain ⟨W₀, hKW₀, hW₀⟩ := exists_opens_isCompact_closure_superset hK
  -- cut down to the preimage of `W` under the inclusion
  refine ⟨W₀ ⊓ ⟨_, W.isOpen.preimage
      (pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff.continuous⟩, ?_, ?_, ?_⟩
  · exact hW₀.of_isClosed_subset isClosed_closure (closure_mono inf_le_left)
  · rintro _ ⟨w, hw, rfl⟩
    exact hw.2
  · intro y' hy'
    refine (Opens.mem_inf).mpr ⟨hKW₀ ⟨y', hy', rfl⟩, ?_⟩
    change pieceAmbientIncl (E.restrictAmbient_le hV')
      ((E.restrictPiece hV' hsub).ambientPoint y') ∈ (W : Set (pieceAmbient 𝕜 E.G))
    exact Set.mem_of_eq_of_mem (E.pieceAmbientIncl_ambientPoint_restrictPiece hV' hsub y')
      (hNW ⟨Subtype.val y', val_mem_openOf hV' hsub y'⟩ hy')

/-! ### The transport: the local resolution of the restricted embedding as an open part -/

section Transport

variable (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
  (W : Opens (pieceAmbient.{u} 𝕜 E.G)) (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G))))
  {V' : Set X} (hV' : IsOpen V') (hsub : V' ⊆ V)
  (W' : Opens (pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')))
  (hW' : IsCompact (closure (W' : Set (pieceAmbient 𝕜 (E.restrictAmbient hV')))))
  (hWW' : pieceAmbientImageOpens (E.restrictAmbient_le hV') W' ≤ W)

include hbed hWW' in
/-- The local resolution of the restricted embedding over `W'` maps by an OPEN IMMERSION over `X`
onto the part of the piece's local resolution over `W` lying over the base open `domOpens (g W')`
(`exists_localResolution_restrictPiece_iso` read as an open immersion). -/
theorem exists_openImmersion_localResolution_restrictPiece :
    ∃ χ : ((E.restrictPiece hV' hsub).localResolution bed W' hW').toKLocallyRingedSpace ⟶
        (E.localResolution bed W hW).toKLocallyRingedSpace,
      LocallyRingedSpace.IsOpenImmersion χ.1 ∧
        χ ≫ E.toSpaceMap bed W hW = (E.restrictPiece hV' hsub).toSpaceMap bed W' hW' ∧
        Set.range (KLocallyRingedSpace.Hom.toFun χ) = KLocallyRingedSpace.Hom.toFun
            (E.toSpaceMap bed W hW) ⁻¹'
          (E.domOpens (pieceAmbientImageOpens (E.restrictAmbient_le hV') W') : Set X) := by
  obtain ⟨e, he, heq⟩ :=
    E.exists_localResolution_restrictPiece_iso bed hbed W hW hV' hsub W' hW' hWW'
  have he1 : IsIso e.1 := (isIso_iff_isIso_val e).mp he
  refine ⟨e ≫ ofRestrict _ _,
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (e.1 ≫ (ofRestrict _ _).1)),
    (Category.assoc _ _ _).trans heq, ?_⟩
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact (KLocallyRingedSpace.Hom.toFun e y).2
  · intro hz
    refine ⟨KLocallyRingedSpace.Hom.toFun (@inv _ _ _ _ e he) (Subtype.mk z hz), ?_⟩
    exact congrArg Subtype.val
      (congrArg (fun k => KLocallyRingedSpace.Hom.toFun k (Subtype.mk z hz))
          (@IsIso.inv_hom_id _ _ _ _ e he))

include hbed hWW' in
/-- For an open `P` of `X` inside the base open `domOpens (g W')`, the parts over `P` of the local
resolution of the restricted embedding and of the piece's local resolution are isomorphic over `X`
(the mechanism of `exists_restrictSet_isIso_of_comp_eq_of_isOpenImmersion` read with
`isoOfRangeEq`). -/
theorem exists_iso_restrictOpen_comap (P : Opens X)
    (hP : P ≤ E.domOpens (pieceAmbientImageOpens (E.restrictAmbient_le hV') W')) :
    ∃ α : ((E.restrictPiece hV' hsub).localResolution bed W' hW').toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((E.restrictPiece hV' hsub).toSpaceMap bed W'
              hW'),
            Hom.continuous_toFun ((E.restrictPiece hV' hsub).toSpaceMap bed W' hW')⟩ P) ⟶
        (E.localResolution bed W hW).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (E.toSpaceMap bed W hW),
            Hom.continuous_toFun (E.toSpaceMap bed W hW)⟩ P),
      IsIso α ∧
        α ≫ ofRestrict _ _ ≫ E.toSpaceMap bed W hW =
          ofRestrict _ _ ≫ (E.restrictPiece hV' hsub).toSpaceMap bed W' hW' := by
  obtain ⟨χ, hχ, hχπ, hχr⟩ :=
    E.exists_openImmersion_localResolution_restrictPiece bed hbed W hW hV' hsub W' hW' hWW'
  have hoi : LocallyRingedSpace.IsOpenImmersion
      (ofRestrict ((E.restrictPiece hV' hsub).localResolution bed W' hW').toKLocallyRingedSpace
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((E.restrictPiece hV' hsub).toSpaceMap bed W'
            hW'),
          Hom.continuous_toFun ((E.restrictPiece hV' hsub).toSpaceMap bed W' hW')⟩ P) ≫ χ).1 :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion ((ofRestrict _ _).1 ≫ χ.1))
  have hrange : Set.range (KLocallyRingedSpace.Hom.toFun
      (ofRestrict ((E.restrictPiece hV' hsub).localResolution bed W' hW').toKLocallyRingedSpace
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((E.restrictPiece hV' hsub).toSpaceMap bed W'
            hW'),
          Hom.continuous_toFun ((E.restrictPiece hV' hsub).toSpaceMap bed W' hW')⟩ P) ≫ χ)) =
      Set.range (KLocallyRingedSpace.Hom.toFun (ofRestrict (E.localResolution bed W
          hW).toKLocallyRingedSpace
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (E.toSpaceMap bed W hW),
          Hom.continuous_toFun (E.toSpaceMap bed W hW)⟩ P))) := by
    rw [range_toFun_ofRestrict]
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      change KLocallyRingedSpace.Hom.toFun (E.toSpaceMap bed W hW) (KLocallyRingedSpace.Hom.toFun χ
          (Subtype.val q)) ∈ (P : Set X)
      exact Set.mem_of_eq_of_mem (congrArg (fun k => KLocallyRingedSpace.Hom.toFun k
          (Subtype.val q)) hχπ) q.2
    · intro hz
      obtain ⟨y, rfl⟩ := (Set.ext_iff.mp hχr z).mpr (hP hz)
      exact ⟨Subtype.mk y (show KLocallyRingedSpace.Hom.toFun
          ((E.restrictPiece hV' hsub).toSpaceMap bed W' hW') y ∈
        (P : Set X) from
        Set.mem_of_eq_of_mem (congrArg (fun k => KLocallyRingedSpace.Hom.toFun k y) hχπ).symm hz),
            rfl⟩
  refine ⟨(@isoOfRangeEq _ _ _ _ _ _ _ hoi inferInstance hrange).hom, Iso.isIso_hom _, ?_⟩
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ E.toSpaceMap bed W hW)
      (@isoOfRangeEq_hom_comp _ _ _ _ _ _ _ hoi inferInstance hrange)).trans
      ((Category.assoc _ _ _).trans (congrArg
        (fun k : ((E.restrictPiece hV' hsub).localResolution bed W' hW').toKLocallyRingedSpace ⟶
            X.toKLocallyRingedSpace =>
          ofRestrict _ _ ≫ k) hχπ)))

end Transport

/-! ### The pair forms: two embeddings of two pieces, the dimensions free -/

section Pair

variable {X : AnalyticSpace.{u} 𝕜} {n m : ℕ} {V V' : Set X}
  (E : PieceEmbedding 𝕜 n X V) (E' : PieceEmbedding 𝕜 m X V')

/-- A point of the piece over the base open lies over the ambient open. -/
theorem mem_embPreimage_of_val_mem_domOpens (W : Opens (pieceAmbient.{u} 𝕜 E.G))
    (y : X.restrictSet V) (hy : Subtype.val y ∈ E.domOpens W) : y ∈ E.embPreimage W := by
  obtain ⟨y₀, hy₀, hyv⟩ := (E.mem_domOpens).mp hy
  exact Set.mem_of_eq_of_mem (Subtype.ext hyv).symm hy₀

/-- **The local data of the transition at a point**, in the PAIR form (two embeddings
`E : PieceEmbedding 𝕜 n X V`, `E' : PieceEmbedding 𝕜 m X V'` of two pieces, the dimensions free;
[Wlo09, §4, (3)⇒(4)]) — for `z` in an open `O'` of the common base open of the two pieces: an open
`N' ⊆ V ∩ V'` with compact closure in `O'`, and for each of the two embeddings restricted to `N'` a
relatively compact ambient open of the shrunk ambient whose image lies in the piece's ambient open
and whose base open contains `z`. The intersection of the two base opens is the member `P_z` of the
cover of `O'` on which the independence of the local resolution is applied. -/
theorem exists_transitionData_pair (hV : IsOpen V) (hV' : IsOpen V')
    (W : Opens (pieceAmbient.{u} 𝕜 E.G)) (W' : Opens (pieceAmbient.{u} 𝕜 E'.G)) {O' : Set X}
    (hO' : IsOpen O') (hO'i : O' ⊆ E.domOpens W) (hO'j : O' ⊆ E'.domOpens W') {z : X}
    (hz : z ∈ O') :
    ∃ (N' : Set X) (hN' : IsOpen N') (_hN'i : N' ⊆ V) (_hN'j : N' ⊆ V')
      (W₁ : Opens (pieceAmbient.{u} 𝕜 (E.restrictAmbient hN')))
      (W₂ : Opens (pieceAmbient.{u} 𝕜 (E'.restrictAmbient hN'))),
      closure N' ⊆ O' ∧
      IsCompact (closure (W₁ : Set (pieceAmbient 𝕜 (E.restrictAmbient hN')))) ∧
      IsCompact (closure (W₂ : Set (pieceAmbient 𝕜 (E'.restrictAmbient hN')))) ∧
      pieceAmbientImageOpens (E.restrictAmbient_le hN') W₁ ≤ W ∧
      pieceAmbientImageOpens (E'.restrictAmbient_le hN') W₂ ≤ W' ∧
      z ∈ E.domOpens (pieceAmbientImageOpens (E.restrictAmbient_le hN') W₁) ∧
      z ∈ E'.domOpens (pieceAmbientImageOpens (E'.restrictAmbient_le hN') W₂) := by
  obtain ⟨N', N, hN'o, -, hN'O', -, hzN, hNc, hNN'⟩ := exists_nested_opens_of_isOpen hO' hz
  have hN'i : N' ⊆ V := fun x hx =>
    E.domOpens_subset hV W (hO'i (hN'O' (subset_closure hx)))
  have hN'j : N' ⊆ V' := fun x hx =>
    E'.domOpens_subset hV' W' (hO'j (hN'O' (subset_closure hx)))
  have hNN'' : closure N ⊆ N' := hNN'
  obtain ⟨W₁, hci, hle₁, hmemi⟩ := E.exists_restrictAmbientOpens hN'o hN'i W hNc
    hNN'' fun y hy => E.mem_embPreimage_of_val_mem_domOpens W y
      (hO'i (hN'O' (subset_closure (hNN'' hy))))
  obtain ⟨W₂, hcj, hle₂, hmemj⟩ := E'.exists_restrictAmbientOpens hN'o hN'j W' hNc
    hNN'' fun y hy => E'.mem_embPreimage_of_val_mem_domOpens W' y
      (hO'j (hN'O' (subset_closure (hNN'' hy))))
  have hzN' : z ∈ openOf X N' :=
    mem_openOf_of_subset Set.Subset.rfl (hNN'' (subset_closure hzN))
  refine ⟨N', hN'o, hN'i, hN'j, W₁, W₂, hN'O', hci, hcj, hle₁, hle₂, ?_, ?_⟩
  · exact (E.mem_embPreimage_restrictPiece_iff_mem_domOpens hN'o hN'i W₁
      ⟨z, hzN'⟩).mp (hmemi ⟨z, hzN'⟩ (subset_closure hzN))
  · exact (E'.mem_embPreimage_restrictPiece_iff_mem_domOpens hN'o hN'j W₂
      ⟨z, hzN'⟩).mp (hmemj ⟨z, hzN'⟩ (subset_closure hzN))


/-! ### The local transition over `P_z` for a pair of embeddings: existence, compatibility,
uniqueness (the independence transported) -/

section TransitionOverPair

variable (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
  (W : Opens (pieceAmbient.{u} 𝕜 E.G)) (W' : Opens (pieceAmbient.{u} 𝕜 E'.G))
  (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G))))
  (hW' : IsCompact (closure (W' : Set (pieceAmbient 𝕜 E'.G))))
  {N' : Set X} (hN' : IsOpen N') (hN'i : N' ⊆ V) (hN'j : N' ⊆ V')
  (W₁ : Opens (pieceAmbient.{u} 𝕜 (E.restrictAmbient hN')))
  (W₂ : Opens (pieceAmbient.{u} 𝕜 (E'.restrictAmbient hN')))

local notation "𝔓" => PieceEmbedding.domOpens E
    (pieceAmbientImageOpens (PieceEmbedding.restrictAmbient_le E hN') W₁) ⊓
  PieceEmbedding.domOpens E' (pieceAmbientImageOpens (PieceEmbedding.restrictAmbient_le E' hN') W₂)
local notation "𝕊ᶜ" => PieceEmbedding.restrictPiece E hN' hN'i
local notation "𝕋ᶜ" => PieceEmbedding.restrictPiece E' hN' hN'j
local notation "𝔖" =>
  PieceEmbedding.embPreimage (PieceEmbedding.restrictPiece E hN' hN'i) W₁ ∩
  PieceEmbedding.embPreimage (PieceEmbedding.restrictPiece E' hN' hN'j) W₂

include hbed hN'i hN'j in
/-- **The local transition over the cover member `P = domOpens_E (g W₁) ⊓ domOpens_E' (g W₂)`**,
in the PAIR form (`LocalEmbeddingData.exists_transition_over` is its instance;
[Wlo09, §4, (3)⇒(4)]; [Kol07, Theorem 36, proof]) — an isomorphism over `X` between the parts of
the two local resolutions over `P`, UNIQUE among such: it is the isomorphism of the independence
`hind` for the two embeddings restricted to `N'` at the ambient opens `(W₁, W₂)`, transported along
the identifications of `exists_iso_restrictOpen_comap` and the equality of sets `Π'⁻¹ S = π'⁻¹ P`
(`restrictOpenIsoOfSetEq`); any isomorphism over `X` on the parts over `P` transports back to one
of that kind on exactly `S`, so the uniqueness in `hind` applies verbatim. -/
theorem exists_transition_over_pair (hind : LocalResolutionIndependentOn X bed)
    (hW₁ : IsCompact (closure (W₁ : Set (pieceAmbient 𝕜 (E.restrictAmbient hN')))))
    (hW₂ : IsCompact (closure (W₂ : Set (pieceAmbient 𝕜 (E'.restrictAmbient hN')))))
    (hle₁ : pieceAmbientImageOpens (E.restrictAmbient_le hN') W₁ ≤ W)
    (hle₂ : pieceAmbientImageOpens (E'.restrictAmbient_le hN') W₂ ≤ W') :
    ∃ θ : (E.localResolution bed W hW).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (E.toSpaceMap bed W hW),
            Hom.continuous_toFun (E.toSpaceMap bed W hW)⟩ 𝔓) ⟶
        (E'.localResolution bed W' hW').toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (E'.toSpaceMap bed W' hW'),
            Hom.continuous_toFun (E'.toSpaceMap bed W' hW')⟩ 𝔓),
      IsIso θ ∧
        ofRestrict _ _ ≫ E.toSpaceMap bed W hW = (θ ≫ ofRestrict _ _) ≫ E'.toSpaceMap bed W' hW' ∧
        ∀ s : (E.localResolution bed W hW).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (E.toSpaceMap bed W hW),
              Hom.continuous_toFun (E.toSpaceMap bed W hW)⟩ 𝔓) ⟶
          (E'.localResolution bed W' hW').toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (E'.toSpaceMap bed W' hW'),
              Hom.continuous_toFun (E'.toSpaceMap bed W' hW')⟩ 𝔓),
          IsIso s →
            ofRestrict _ _ ≫ E.toSpaceMap bed W hW =
              (s ≫ ofRestrict _ _) ≫ E'.toSpaceMap bed W' hW' → s = θ := by
  -- the independence for the two restricted embeddings
  obtain ⟨ψ, ⟨hψiso, hψc⟩, huniq⟩ := hind (𝕊ᶜ) (𝕋ᶜ) W₁ hW₁ W₂ hW₂
  -- the identifications of `exists_iso_restrictOpen_comap` at `P`
  obtain ⟨αi, hαi, hαi_over⟩ := E.exists_iso_restrictOpen_comap bed hbed W hW
    hN' hN'i W₁ hW₁ hle₁ 𝔓 inf_le_left
  obtain ⟨αj, hαj, hαj_over⟩ := E'.exists_iso_restrictOpen_comap bed hbed W' hW'
    hN' hN'j W₂ hW₂ hle₂ 𝔓 inf_le_right
  -- the two spellings of the parts over `S`
  have hopen_i : IsOpen (⇑((𝕊ᶜ).localResolutionToPiece bed W₁ hW₁) ⁻¹' 𝔖) :=
    (((𝕊ᶜ).isOpen_embPreimage W₁).inter ((𝕋ᶜ).isOpen_embPreimage W₂)).preimage
      (Hom.continuous_toFun ((𝕊ᶜ).localResolutionToPiece bed W₁ hW₁ :
        ((𝕊ᶜ).localResolution bed W₁ hW₁).toKLocallyRingedSpace ⟶
          (X.restrictSet N').toKLocallyRingedSpace))
  have hopen_j : IsOpen (⇑((𝕋ᶜ).localResolutionToPiece bed W₂ hW₂) ⁻¹' 𝔖) :=
    (((𝕊ᶜ).isOpen_embPreimage W₁).inter ((𝕋ᶜ).isOpen_embPreimage W₂)).preimage
      (Hom.continuous_toFun ((𝕋ᶜ).localResolutionToPiece bed W₂ hW₂ :
        ((𝕋ᶜ).localResolution bed W₂ hW₂).toKLocallyRingedSpace ⟶
          (X.restrictSet N').toKLocallyRingedSpace))
  have hset_i : ((openOf ((𝕊ᶜ).localResolution bed W₁ hW₁)
        (⇑((𝕊ᶜ).localResolutionToPiece bed W₁ hW₁) ⁻¹' 𝔖) :
          Opens ((𝕊ᶜ).localResolution bed W₁ hW₁).toKLocallyRingedSpace) :
        Set ((𝕊ᶜ).localResolution bed W₁ hW₁).toKLocallyRingedSpace) =
      ((Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((𝕊ᶜ).toSpaceMap bed W₁ hW₁),
        Hom.continuous_toFun ((𝕊ᶜ).toSpaceMap bed W₁ hW₁)⟩ 𝔓 :
          Opens ((𝕊ᶜ).localResolution bed W₁ hW₁).toKLocallyRingedSpace) :
        Set ((𝕊ᶜ).localResolution bed W₁ hW₁).toKLocallyRingedSpace) :=
    (congrArg (fun U : Opens ((𝕊ᶜ).localResolution bed W₁ hW₁).toKLocallyRingedSpace =>
        (U : Set ((𝕊ᶜ).localResolution bed W₁ hW₁).toKLocallyRingedSpace))
      (openOf_of_isOpen
        ((𝕊ᶜ).localResolution bed W₁ hW₁) hopen_i)).trans
      (Set.ext fun q => Iff.and
        (E.mem_embPreimage_restrictPiece_iff_mem_domOpens hN' hN'i W₁
          (((𝕊ᶜ).localResolutionToPiece bed W₁ hW₁) q))
        (E'.mem_embPreimage_restrictPiece_iff_mem_domOpens hN' hN'j W₂
          (((𝕊ᶜ).localResolutionToPiece bed W₁ hW₁) q)))
  have hset_j : ((openOf ((𝕋ᶜ).localResolution bed W₂ hW₂)
        (⇑((𝕋ᶜ).localResolutionToPiece bed W₂ hW₂) ⁻¹' 𝔖) :
          Opens ((𝕋ᶜ).localResolution bed W₂ hW₂).toKLocallyRingedSpace) :
        Set ((𝕋ᶜ).localResolution bed W₂ hW₂).toKLocallyRingedSpace) =
      ((Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((𝕋ᶜ).toSpaceMap bed W₂ hW₂),
        Hom.continuous_toFun ((𝕋ᶜ).toSpaceMap bed W₂ hW₂)⟩ 𝔓 :
          Opens ((𝕋ᶜ).localResolution bed W₂ hW₂).toKLocallyRingedSpace) :
        Set ((𝕋ᶜ).localResolution bed W₂ hW₂).toKLocallyRingedSpace) :=
    (congrArg (fun U : Opens ((𝕋ᶜ).localResolution bed W₂ hW₂).toKLocallyRingedSpace =>
        (U : Set ((𝕋ᶜ).localResolution bed W₂ hW₂).toKLocallyRingedSpace))
      (openOf_of_isOpen
        ((𝕋ᶜ).localResolution bed W₂ hW₂) hopen_j)).trans
      (Set.ext fun q => Iff.and
        (E.mem_embPreimage_restrictPiece_iff_mem_domOpens hN' hN'i W₁
          (((𝕋ᶜ).localResolutionToPiece bed W₂ hW₂) q))
        (E'.mem_embPreimage_restrictPiece_iff_mem_domOpens hN' hN'j W₂
          (((𝕋ᶜ).localResolutionToPiece bed W₂ hW₂) q)))
  -- the independence's isomorphism as a `K`-isomorphism; its compatibility read over `X`
  have hψK : IsIso (C := KLocallyRingedSpace.{u} 𝕜) ψ := by
    obtain ⟨⟨g, h1, h2⟩⟩ := hψiso
    exact ⟨⟨g, h1, h2⟩⟩
  have hri :
      AnalyticSpace.Hom.restrictSet ((𝕊ᶜ).localResolutionToPiece bed W₁ hW₁) 𝔖 ≫
      ofRestrict (X.restrictSet N').toKLocallyRingedSpace
        (openOf (X.restrictSet N') 𝔖) =
      ofRestrict ((𝕊ᶜ).localResolution bed W₁ hW₁).toKLocallyRingedSpace
        (openOf ((𝕊ᶜ).localResolution bed W₁ hW₁)
          (⇑((𝕊ᶜ).localResolutionToPiece bed W₁ hW₁) ⁻¹' 𝔖)) ≫
        (𝕊ᶜ).localResolutionToPiece bed W₁ hW₁ :=
    Hom.restrictTo_comp_ofRestrict ((𝕊ᶜ).localResolutionToPiece bed W₁ hW₁ :
        ((𝕊ᶜ).localResolution bed W₁ hW₁).toKLocallyRingedSpace ⟶
          (X.restrictSet N').toKLocallyRingedSpace)
      (openOf ((𝕊ᶜ).localResolution bed W₁ hW₁)
        (KLocallyRingedSpace.Hom.toFun ((𝕊ᶜ).localResolutionToPiece bed W₁ hW₁) ⁻¹' 𝔖))
      (openOf (X.restrictSet N') 𝔖)
      (Hom.mapsTo_openOf
        ((𝕊ᶜ).localResolutionToPiece bed W₁ hW₁) 𝔖)
  have hrj :
      AnalyticSpace.Hom.restrictSet ((𝕋ᶜ).localResolutionToPiece bed W₂ hW₂) 𝔖 ≫
      ofRestrict (X.restrictSet N').toKLocallyRingedSpace
        (openOf (X.restrictSet N') 𝔖) =
      ofRestrict ((𝕋ᶜ).localResolution bed W₂ hW₂).toKLocallyRingedSpace
        (openOf ((𝕋ᶜ).localResolution bed W₂ hW₂)
          (⇑((𝕋ᶜ).localResolutionToPiece bed W₂ hW₂) ⁻¹' 𝔖)) ≫
        (𝕋ᶜ).localResolutionToPiece bed W₂ hW₂ :=
    Hom.restrictTo_comp_ofRestrict ((𝕋ᶜ).localResolutionToPiece bed W₂ hW₂ :
        ((𝕋ᶜ).localResolution bed W₂ hW₂).toKLocallyRingedSpace ⟶
          (X.restrictSet N').toKLocallyRingedSpace)
      (openOf ((𝕋ᶜ).localResolution bed W₂ hW₂)
        (KLocallyRingedSpace.Hom.toFun ((𝕋ᶜ).localResolutionToPiece bed W₂ hW₂) ⁻¹' 𝔖))
      (openOf (X.restrictSet N') 𝔖)
      (Hom.mapsTo_openOf
        ((𝕋ᶜ).localResolutionToPiece bed W₂ hW₂) 𝔖)
  have hC0 : (ψ ≫ ofRestrict ((𝕋ᶜ).localResolution bed W₂ hW₂).toKLocallyRingedSpace
        (openOf ((𝕋ᶜ).localResolution bed W₂ hW₂)
          (⇑((𝕋ᶜ).localResolutionToPiece bed W₂ hW₂) ⁻¹' 𝔖))) ≫ (𝕋ᶜ).toSpaceMap bed W₂ hW₂ =
      ofRestrict ((𝕊ᶜ).localResolution bed W₁ hW₁).toKLocallyRingedSpace
        (openOf ((𝕊ᶜ).localResolution bed W₁ hW₁)
          (⇑((𝕊ᶜ).localResolutionToPiece bed W₁ hW₁) ⁻¹' 𝔖)) ≫ (𝕊ᶜ).toSpaceMap bed W₁ hW₁ :=
    CategoryTheory.comp_over_of_comp_restrict_eq (C := KLocallyRingedSpace.{u} 𝕜) ψ _ _ _ _ _ _ _
      (ofRestrict X.toKLocallyRingedSpace (openOf X N')) hψc hrj hri
  -- the transition and its properties
  refine ⟨@inv _ _ _ _ αi hαi ≫ (restrictOpenIsoOfSetEq hset_i).inv ≫ ψ ≫
      (restrictOpenIsoOfSetEq hset_j).hom ≫ αj,
    @IsIso.comp_isIso _ _ _ _ _ _ _ (@IsIso.inv_isIso _ _ _ _ αi hαi)
      (@IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv _)
        (@IsIso.comp_isIso _ _ _ _ _ _ _ hψK
          (@IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) hαj))),
    CategoryTheory.transport_over_eq (C := KLocallyRingedSpace.{u} 𝕜) _ αi
      (@IsIso.inv_hom_id _ _ _ _ αi hαi) _ _ αj ψ _ _ _ _ _ _
      _ _ _ _ (restrictOpenIsoOfSetEq_inv_comp hset_i) (restrictOpenIsoOfSetEq_hom_comp hset_j)
      hαi_over hαj_over hC0, ?_⟩
  -- uniqueness: transport `s` back to one of the independence's kind
  intro s hs hs_over
  have hαj_inv_over := CategoryTheory.inv_over_of_over (C := KLocallyRingedSpace.{u} 𝕜)
    (@inv _ _ _ _ αj hαj) αj
    (@IsIso.inv_hom_id _ _ _ _ αj hαj) _ _ _ _ hαj_over
  have hψs_over := CategoryTheory.transport_back_over_eq (C := KLocallyRingedSpace.{u} 𝕜)
    (restrictOpenIsoOfSetEq hset_i).hom αi s
    (@inv _ _ _ _ αj hαj) (restrictOpenIsoOfSetEq hset_j).inv _ _ _ _ _ _ _ _ _ _
    (restrictOpenIsoOfSetEq_hom_comp hset_i) (restrictOpenIsoOfSetEq_inv_comp hset_j)
    hαi_over hαj_inv_over hs_over
  have hψsK : IsIso (C := KLocallyRingedSpace.{u} 𝕜) ((restrictOpenIsoOfSetEq hset_i).hom ≫ αi ≫
      s ≫ @inv _ _ _ _ αj hαj ≫ (restrictOpenIsoOfSetEq hset_j).inv) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _)
      (@IsIso.comp_isIso _ _ _ _ _ _ _ hαi
        (@IsIso.comp_isIso _ _ _ _ _ _ _ hs
          (@IsIso.comp_isIso _ _ _ _ _ _ _ (@IsIso.inv_isIso _ _ _ _ αj hαj) (Iso.isIso_inv _))))
  -- a morphism over `X` between the parts over `S` is compatible with the maps to the piece
  have key : ∀ ψs : ((𝕊ᶜ).localResolution bed W₁ hW₁).toKLocallyRingedSpace.restrictOpen
        (openOf ((𝕊ᶜ).localResolution bed W₁ hW₁)
          (⇑((𝕊ᶜ).localResolutionToPiece bed W₁ hW₁) ⁻¹' 𝔖)) ⟶
      ((𝕋ᶜ).localResolution bed W₂ hW₂).toKLocallyRingedSpace.restrictOpen
        (openOf ((𝕋ᶜ).localResolution bed W₂ hW₂)
          (⇑((𝕋ᶜ).localResolutionToPiece bed W₂ hW₂) ⁻¹' 𝔖)),
      (ψs ≫ ofRestrict _ _) ≫ (𝕋ᶜ).toSpaceMap bed W₂ hW₂ =
          ofRestrict _ _ ≫ (𝕊ᶜ).toSpaceMap bed W₁ hW₁ →
        ψs ≫
            AnalyticSpace.Hom.restrictSet ((𝕋ᶜ).localResolutionToPiece bed W₂ hW₂) 𝔖 =
          AnalyticSpace.Hom.restrictSet ((𝕊ᶜ).localResolutionToPiece bed W₁ hW₁) 𝔖 := by
    intro ψs hover
    apply Hom.ext_of_comp_ofRestrict
    refine (Category.assoc _ _ _).trans ((congrArg (fun k => ψs ≫ k) hrj).trans ?_)
    refine Eq.trans ?_ hri.symm
    apply Hom.ext_of_comp_ofRestrict
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => ψs ≫ k) (Category.assoc _ _ _)).trans
        (((Category.assoc _ _ _).symm.trans hover).trans (Category.assoc _ _ _).symm))
  have hψs_c := key _ hψs_over
  have hψs : (restrictOpenIsoOfSetEq hset_i).hom ≫ αi ≫ s ≫ @inv _ _ _ _ αj hαj ≫
      (restrictOpenIsoOfSetEq hset_j).inv = ψ :=
    huniq _ ⟨(show CategoryTheory.IsIso (C := AnalyticSpace.{u} 𝕜) _ from by
      obtain ⟨⟨g, h1, h2⟩⟩ := hψsK
      exact ⟨⟨g, h1, h2⟩⟩), hψs_c⟩
  exact CategoryTheory.eq_transport_of_transport_eq (C := KLocallyRingedSpace.{u} 𝕜) _ αi
    (@IsIso.inv_hom_id _ _ _ _ αi hαi) _ αj
    (@IsIso.inv_hom_id _ _ _ _ αj hαj) _ _ (restrictOpenIsoOfSetEq hset_i).inv_hom_id _ _
    (restrictOpenIsoOfSetEq hset_j).inv_hom_id s ψ hψs

end TransitionOverPair

end Pair

end PieceEmbedding

namespace LocalEmbeddingData

variable {X : AnalyticSpace.{u} 𝕜} {U : Set X} (D : LocalEmbeddingData 𝕜 X U)
  (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))

/-- **The local data of the transition at a point** ([Wlo09, §4, (3)⇒(4)]) — for `z` in an open
`O'` of the common base open of the pieces `i`, `j`: an open `N' ⊆ piece i ∩ piece j` with compact
closure in `O'`, and for each of the two embeddings restricted to `N'` a relatively compact ambient
open of the shrunk ambient whose image lies in the piece's ambient open and whose base open
contains `z`. The intersection of the two base opens is the member `P_z` of the cover of `O'` on
which the independence of the local resolution is applied. -/
theorem exists_transitionData (i j : D.ι) {O' : Set X} (hO' : IsOpen O')
    (hO'i : O' ⊆ D.pieceDom i (W i)) (hO'j : O' ⊆ D.pieceDom j (W j)) {z : X} (hz : z ∈ O') :
    ∃ (N' : Set X) (hN' : IsOpen N') (_hN'i : N' ⊆ D.piece i) (_hN'j : N' ⊆ D.piece j)
      (W'i : Opens (pieceAmbient.{u} 𝕜 ((D.embedding i).restrictAmbient hN')))
      (W'j : Opens (pieceAmbient.{u} 𝕜 ((D.embedding j).restrictAmbient hN'))),
      closure N' ⊆ O' ∧
      IsCompact (closure (W'i : Set (pieceAmbient 𝕜 ((D.embedding i).restrictAmbient hN')))) ∧
      IsCompact (closure (W'j : Set (pieceAmbient 𝕜 ((D.embedding j).restrictAmbient hN')))) ∧
      pieceAmbientImageOpens ((D.embedding i).restrictAmbient_le hN') W'i ≤ W i ∧
      pieceAmbientImageOpens ((D.embedding j).restrictAmbient_le hN') W'j ≤ W j ∧
      z ∈ (D.embedding i).domOpens
        (pieceAmbientImageOpens ((D.embedding i).restrictAmbient_le hN') W'i) ∧
      z ∈ (D.embedding j).domOpens
        (pieceAmbientImageOpens ((D.embedding j).restrictAmbient_le hN') W'j) :=
  (D.embedding i).exists_transitionData_pair (D.embedding j) (D.isOpen_piece i)
    (D.isOpen_piece j) (W i) (W j) hO' hO'i hO'j hz

/-! ### The local transition over `P_z`: existence, compatibility, uniqueness -/

section TransitionOver

variable (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
  (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient 𝕜 (D.embedding i).G))))
  (i j : D.ι) {N' : Set X} (hN' : IsOpen N') (hN'i : N' ⊆ D.piece i) (hN'j : N' ⊆ D.piece j)
  (W'i : Opens (pieceAmbient.{u} 𝕜 ((D.embedding i).restrictAmbient hN')))
  (W'j : Opens (pieceAmbient.{u} 𝕜 ((D.embedding j).restrictAmbient hN')))

local notation "𝔓" => PieceEmbedding.domOpens (D.embedding i)
    (pieceAmbientImageOpens (PieceEmbedding.restrictAmbient_le (D.embedding i) hN') W'i) ⊓
  PieceEmbedding.domOpens (D.embedding j)
    (pieceAmbientImageOpens (PieceEmbedding.restrictAmbient_le (D.embedding j) hN') W'j)
local notation "𝕊ᶜ" => PieceEmbedding.restrictPiece (D.embedding i) hN' hN'i
local notation "𝕋ᶜ" => PieceEmbedding.restrictPiece (D.embedding j) hN' hN'j
local notation "𝔖" =>
  PieceEmbedding.embPreimage (PieceEmbedding.restrictPiece (D.embedding i) hN' hN'i) W'i ∩
  PieceEmbedding.embPreimage (PieceEmbedding.restrictPiece (D.embedding j) hN' hN'j) W'j

include hbed hN'i hN'j in
/-- **The local transition over the cover member `P = domOpens_i (g W'i) ⊓ domOpens_j (g W'j)`**
([Wlo09, §4, (3)⇒(4)]; [Kol07, Theorem 36, proof]) — an isomorphism over `X` between the parts of
the two pieces' local resolutions over `P`, UNIQUE among such: it is the isomorphism of the
independence `hind` for the two embeddings restricted to `N'` at the ambient opens `(W'i, W'j)`,
transported along the identifications of `exists_iso_restrictOpen_comap` and the equality of sets
`Π'⁻¹ S = π'⁻¹ P` (`restrictOpenIsoOfSetEq`); any isomorphism over `X` on the parts over `P`
transports back to one of that kind on exactly `S`, so the uniqueness in `hind` applies
verbatim. -/
theorem exists_transition_over (hind : LocalResolutionIndependentOn X bed)
    (hW'i : IsCompact (closure (W'i : Set (pieceAmbient 𝕜 ((D.embedding i).restrictAmbient hN')))))
    (hW'j : IsCompact (closure (W'j : Set (pieceAmbient 𝕜 ((D.embedding j).restrictAmbient hN')))))
    (hlei : pieceAmbientImageOpens ((D.embedding i).restrictAmbient_le hN') W'i ≤ W i)
    (hlej : pieceAmbientImageOpens ((D.embedding j).restrictAmbient_le hN') W'j ≤ W j) :
    ∃ θ : (pieceR D bed W hW i).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (W i) (hW i)),
            Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (W i) (hW i))⟩ 𝔓) ⟶
        (pieceR D bed W hW j).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding j).toSpaceMap bed (W j) (hW j)),
            Hom.continuous_toFun ((D.embedding j).toSpaceMap bed (W j) (hW j))⟩ 𝔓),
      IsIso θ ∧
        ofRestrict _ _ ≫ (D.embedding i).toSpaceMap bed (W i) (hW i) =
          (θ ≫ ofRestrict _ _) ≫ (D.embedding j).toSpaceMap bed (W j) (hW j) ∧
        ∀ s : (pieceR D bed W hW i).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (W i)
                (hW i)),
              Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (W i) (hW i))⟩ 𝔓) ⟶
          (pieceR D bed W hW j).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding j).toSpaceMap bed (W j)
                (hW j)),
              Hom.continuous_toFun ((D.embedding j).toSpaceMap bed (W j) (hW j))⟩ 𝔓),
          IsIso s →
            ofRestrict _ _ ≫ (D.embedding i).toSpaceMap bed (W i) (hW i) =
              (s ≫ ofRestrict _ _) ≫ (D.embedding j).toSpaceMap bed (W j) (hW j) → s = θ :=
  (D.embedding i).exists_transition_over_pair (D.embedding j) bed hbed (W i) (W j) (hW i) (hW j)
    hN' hN'i hN'j W'i W'j hind hW'i hW'j hlei hlej

end TransitionOver

end LocalEmbeddingData

end Hironaka.Manifold

end
