/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.GlueIsoOver
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueProof
import Hironaka.AnalyticSpace.HomLocal
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceTransition
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The transitions of the gluing datum

Włodarczyk glues the canonical desingularizations along the isomorphisms over the overlaps
`Ṽ_i ∩ Ṽ_j` [Wlo09, §4, (3)⇒(4)]; Kollár glues the local resolutions by a formal property of
blow-up sequence functors [Kol07, Theorem 36, proof]. The transition of the gluing datum between
two pieces `i`, `j` is an isomorphism over `X` between the parts of their local resolutions over
the common base open `pieceDom i ⊓ pieceDom j`, and it is unique among such. Both are assembled
from the LOCAL transitions of `PieceTransition.lean` (the independence of the local resolution from
the embedding, transported to the cover members `P_z`) by the gluing of local isomorphisms over
`X`, `exists_isIso_over_of_cover` (`Hironaka/AnalyticSpace/Glue/GlueIsoOver.lean`), and by
`hom_ext_of_cover` (`Hironaka/AnalyticSpace/HomLocal.lean`):

* `LocalEmbeddingData.exists_localTransition`: at a point `z` of an open `O'` of the common base
  open, a cover member `P ∋ z`, `P ≤ O'`, with the unique local transition over `P`;
* `LocalEmbeddingData.transition_unique` (with the independence as the hypothesis `hind`): two
  isomorphisms over `X` between the parts over an open `O ≤ pieceDom i ⊓ pieceDom j` agree — their
  restrictions (`restrictOver`) to every cover member `P_z` are the unique local transition, and
  morphisms agreeing on a cover agree (`hom_ext_of_cover`);
* `LocalEmbeddingData.exists_transition` (with `hind`): the transition over
  `pieceDom i ⊓ pieceDom j` — `exists_isIso_over_of_cover` applied to the local transitions with
  `transition_unique` as its uniqueness hypothesis, read onto the gluing opens `pieceGlueOpens`
  (the two spellings of the same open, `restrictOpenIsoOfSetEq`).

Not in the sources beyond the gluing remarks; bookkeeping.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace.KLocallyRingedSpace
open scoped Manifold ContDiff

universe u

namespace CategoryTheory

variable {C : Type*} [Category C]

/-- Two morphisms whose restrictions along a common inclusion agree, agree after the
inclusion. -/
theorem comp_eq_of_restrict_eq {A₀ A₁ A B₁ B : C} (pi : A₀ ⟶ A₁) (ri : A₁ ⟶ A) (o : A₀ ⟶ A)
    (s s' : A ⟶ B) (r r' : A₁ ⟶ B₁) (rj : B₁ ⟶ B) (hpi : pi ≫ ri = o)
    (h1 : r ≫ rj = ri ≫ s) (h1' : r' ≫ rj = ri ≫ s') (hrr : r = r') : o ≫ s = o ≫ s' := by
  rw [← hpi, Category.assoc, Category.assoc, ← h1, ← h1', hrr]

/-- A morphism over the base, conjugated by two identifications over the base, is over the
base. -/
theorem over_of_conj {A' A B B' Y Y' Z : C} (εi_inv : A' ⟶ A) (εj_hom : B ⟶ B') (s : A ⟶ B)
    (ofRA : A ⟶ Y) (ofRA' : A' ⟶ Y) (ofRB : B ⟶ Y') (ofRB' : B' ⟶ Y') (πA : Y ⟶ Z) (πB : Y' ⟶ Z)
    (hεi : εi_inv ≫ ofRA = ofRA') (hεj : εj_hom ≫ ofRB' = ofRB)
    (hs : ofRA ≫ πA = (s ≫ ofRB) ≫ πB) :
    ofRA' ≫ πA = ((εi_inv ≫ s ≫ εj_hom) ≫ ofRB') ≫ πB := by
  simp only [Category.assoc]
  rw [← Category.assoc εj_hom, hεj, ← Category.assoc s, ← hs, ← Category.assoc, hεi]

end CategoryTheory

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K] {A Z : KLocallyRingedSpace.{u} K} (πA : A ⟶ Z) (O : Opens Z)
  {ι : Type*} (N : ι → Opens Z) (hN : ∀ i, N i ≤ O)

/-- For the cover of `A|πA⁻¹O` by the parts over the `N i`: the inclusion of a member of the cover
into the part over `N i`, followed by the inclusion of that part into `A|πA⁻¹O`, is the open
immersion of the member (both agree after the open immersion into `A`). -/
theorem pieceIncl_comp_restrictIncl (i : ι) :
    pieceIncl πA O N i ≫ KLocallyRingedSpace.restrictIncl A (Opens.comap_mono _ (hN i)) =
      ofRestrict _ (glueCoverOpens πA O N i) :=
  Hom.ext_of_comp_ofRestrict ((Category.assoc _ _ _).trans
    ((congrArg (fun k => pieceIncl πA O N i ≫ k)
        (KLocallyRingedSpace.restrictIncl_comp_ofRestrict _ _)).trans
      (pieceIncl_comp_ofRestrict πA O N i)))

end AnalyticSpace.KLocallyRingedSpace

namespace Hironaka.Manifold.PieceEmbedding

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {n m : ℕ}
  {V V' : Set X}
  (E : PieceEmbedding 𝕜 n X V) (E' : PieceEmbedding 𝕜 m X V')

/-- **The local transition at a point** for two embeddings `E`, `E'` of two pieces, in the PAIR
form (`LocalEmbeddingData.exists_localTransition` is its instance) — for `z` in an open `O'` of
the common base open, a cover member `P ∋ z`, `P ≤ O'`, carrying the UNIQUE isomorphism over `X`
between the parts of the two local resolutions over `P` (`exists_transitionData_pair` +
`exists_transition_over_pair`). -/
theorem exists_localTransition_pair (hV : IsOpen V) (hV' : IsOpen V') (bed : BEDanFamStar.{u} 𝕜)
    (hbed : bed.IsEmbeddedDesing) (hind : LocalResolutionIndependentOn X bed)
    (W : Opens (pieceAmbient.{u} 𝕜 E.G)) (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G))))
    (W' : Opens (pieceAmbient.{u} 𝕜 E'.G))
    (hW' : IsCompact (closure (W' : Set (pieceAmbient 𝕜 E'.G))))
    (O' : Opens X) (hO' : O' ≤ E.domOpens W ⊓ E'.domOpens W') {z : X} (hz : z ∈ O') :
    ∃ (P : Opens X) (_ : z ∈ P) (_ : P ≤ O'),
      ∃ θ : (E.localResolution bed W hW).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨Hom.toFun (E.toSpaceMap bed W hW),
              Hom.continuous_toFun (E.toSpaceMap bed W hW)⟩ P) ⟶
          (E'.localResolution bed W' hW').toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨Hom.toFun (E'.toSpaceMap bed W' hW'),
              Hom.continuous_toFun (E'.toSpaceMap bed W' hW')⟩ P),
        IsIso θ ∧
          ofRestrict _ _ ≫ E.toSpaceMap bed W hW =
            (θ ≫ ofRestrict _ _) ≫ E'.toSpaceMap bed W' hW' ∧
          ∀ s : (E.localResolution bed W hW).toKLocallyRingedSpace.restrictOpen
              (Opens.comap ⟨Hom.toFun (E.toSpaceMap bed W hW),
                Hom.continuous_toFun (E.toSpaceMap bed W hW)⟩ P) ⟶
            (E'.localResolution bed W' hW').toKLocallyRingedSpace.restrictOpen
              (Opens.comap ⟨Hom.toFun (E'.toSpaceMap bed W' hW'),
                Hom.continuous_toFun (E'.toSpaceMap bed W' hW')⟩ P),
            IsIso s →
              ofRestrict _ _ ≫ E.toSpaceMap bed W hW =
                (s ≫ ofRestrict _ _) ≫ E'.toSpaceMap bed W' hW' → s = θ := by
  obtain ⟨N', hN', hN'i, hN'j, W₁, W₂, hN'O', hc₁, hc₂, hle₁, hle₂, hz₁, hz₂⟩ :=
    E.exists_transitionData_pair E' hV hV' W W' O'.isOpen (fun x hx => (hO' hx).1)
      (fun x hx => (hO' hx).2) hz
  refine ⟨E.domOpens (pieceAmbientImageOpens (E.restrictAmbient_le hN') W₁) ⊓
      E'.domOpens (pieceAmbientImageOpens (E'.restrictAmbient_le hN') W₂),
    (Opens.mem_inf).mpr ⟨hz₁, hz₂⟩, fun x hx => hN'O' (subset_closure
      (E.domOpens_pieceAmbientImageOpens_subset hN' W₁ ((Opens.mem_inf).mp hx).1)), ?_⟩
  exact E.exists_transition_over_pair E' bed hbed W W' hW hW' hN' hN'i hN'j W₁ W₂ hind hc₁ hc₂
    hle₁ hle₂

end Hironaka.Manifold.PieceEmbedding

namespace Hironaka.Manifold.LocalEmbeddingData

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {U : Set X}
  (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
  (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
  (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient 𝕜 (D.embedding i).G))))

/-- **The local transition at a point** — for `z` in an open `O'` of the common base open of the
pieces `i`, `j`, a cover member `P ∋ z`, `P ≤ O'`, carrying the UNIQUE isomorphism over `X` between
the parts of the two local resolutions over `P` (`exists_transitionData` +
`exists_transition_over`). -/
theorem exists_localTransition (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) (i j : D.ι)
    (O' : Opens X) (hO' : O' ≤ D.pieceDom i (W i) ⊓ D.pieceDom j (W j)) {z : X} (hz : z ∈ O') :
    ∃ (P : Opens X) (_ : z ∈ P) (_ : P ≤ O'),
      ∃ θ : (pieceR D bed W hW i).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨Hom.toFun (D.pieceToSpace bed i (W i) (hW i)),
              Hom.continuous_toFun (D.pieceToSpace bed i (W i) (hW i))⟩ P) ⟶
          (pieceR D bed W hW j).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨Hom.toFun (D.pieceToSpace bed j (W j) (hW j)),
              Hom.continuous_toFun (D.pieceToSpace bed j (W j) (hW j))⟩ P),
        IsIso θ ∧
          ofRestrict _ _ ≫ D.pieceToSpace bed i (W i) (hW i) =
            (θ ≫ ofRestrict _ _) ≫ D.pieceToSpace bed j (W j) (hW j) ∧
          ∀ s : (pieceR D bed W hW i).toKLocallyRingedSpace.restrictOpen
              (Opens.comap ⟨Hom.toFun (D.pieceToSpace bed i (W i) (hW i)),
                Hom.continuous_toFun (D.pieceToSpace bed i (W i) (hW i))⟩ P) ⟶
            (pieceR D bed W hW j).toKLocallyRingedSpace.restrictOpen
              (Opens.comap ⟨Hom.toFun (D.pieceToSpace bed j (W j) (hW j)),
                Hom.continuous_toFun (D.pieceToSpace bed j (W j) (hW j))⟩ P),
            IsIso s →
              ofRestrict _ _ ≫ D.pieceToSpace bed i (W i) (hW i) =
                (s ≫ ofRestrict _ _) ≫ D.pieceToSpace bed j (W j) (hW j) → s = θ :=
  (D.embedding i).exists_localTransition_pair (D.embedding j) (D.isOpen_piece i) (D.isOpen_piece j)
    bed hbed hind (W i) (hW i) (W j) (hW j) O' hO' hz

/-- **The transition is unique** (Kollár's "the required uniqueness", [Kol07, Theorem 36, proof];
with the independence as the hypothesis `hind`): two isomorphisms over `X` between the parts of two
pieces over a common base open `O` agree — on every cover member `P_z` both restrict
(`restrictOver`) to isomorphisms over `X`, hence to the unique local transition, and morphisms
agreeing on a cover agree (`hom_ext_of_cover`). -/
theorem transition_unique (hbed : bed.IsEmbeddedDesing) (hind : LocalResolutionIndependentOn X bed)
    (i j : D.ι) (O : Opens X)
    (hO : O ≤ D.pieceDom i (W i) ⊓ D.pieceDom j (W j))
    (s s' : (pieceR D bed W hW i).toKLocallyRingedSpace.restrictOpen
        (Opens.comap ⟨Hom.toFun (D.pieceToSpace bed i (W i) (hW i)),
          Hom.continuous_toFun (D.pieceToSpace bed i (W i) (hW i))⟩ O) ⟶
      (pieceR D bed W hW j).toKLocallyRingedSpace.restrictOpen
        (Opens.comap ⟨Hom.toFun (D.pieceToSpace bed j (W j) (hW j)),
          Hom.continuous_toFun (D.pieceToSpace bed j (W j) (hW j))⟩ O))
    (hs : IsIso s) (hs' : IsIso s')
    (hc : ofRestrict _ _ ≫ D.pieceToSpace bed i (W i) (hW i) =
      (s ≫ ofRestrict _ _) ≫ D.pieceToSpace bed j (W j) (hW j))
    (hc' : ofRestrict _ _ ≫ D.pieceToSpace bed i (W i) (hW i) =
      (s' ≫ ofRestrict _ _) ≫ D.pieceToSpace bed j (W j) (hW j)) :
    s = s' := by
  -- on every cover member the two restrictions are the unique local transition
  have hloc : ∀ z ∈ O, ∃ (P : Opens X) (_ : z ∈ P) (hPO : P ≤ O),
      restrictOver (D.pieceToSpace bed i (W i) (hW i)) (D.pieceToSpace bed j (W j) (hW j)) hPO
          s hc =
        restrictOver (D.pieceToSpace bed i (W i) (hW i)) (D.pieceToSpace bed j (W j) (hW j)) hPO
          s' hc' := by
    intro z hz
    obtain ⟨P, hzP, hPO, θ, -, -, huniq⟩ := D.exists_localTransition bed W hW hbed hind i j O hO hz
    refine ⟨P, hzP, hPO, ?_⟩
    exact (huniq _ (@isIso_restrictOver _ _ _ _ _ _ _ _ _ hPO s hc hs)
        (restrictOver_over _ _ hPO s hc)).trans
      (huniq _ (@isIso_restrictOver _ _ _ _ _ _ _ _ _ hPO s' hc' hs')
        (restrictOver_over _ _ hPO s' hc')).symm
  choose P hzP hPO hEq using hloc
  -- the cover of the part over `O` by the parts over the `P z`, and the agreement on each member
  refine hom_ext_of_cover s s'
    (fun z : O => glueCoverOpens (D.pieceToSpace bed i (W i) (hW i)) O (fun w : O => P w.1 w.2) z)
    (fun x => glueCoverOpens_cover _ O _ (fun w hw => ⟨⟨w, hw⟩, hzP w hw⟩) x) fun z => ?_
  exact CategoryTheory.comp_eq_of_restrict_eq _ _ _ s s' _ _ _
    (pieceIncl_comp_restrictIncl _ O (fun w : O => P w.1 w.2) (fun w => hPO w.1 w.2) z)
    (restrictOver_comp_restrictIncl _ _ (hPO z.1 z.2) s hc)
    (restrictOver_comp_restrictIncl _ _ (hPO z.1 z.2) s' hc') (hEq z.1 z.2)

/-- **The transition of two pieces** (Włodarczyk's isomorphisms over the overlaps `Ṽ_i ∩ Ṽ_j`,
[Wlo09, §4, (3)⇒(4)]; with the independence as the hypothesis `hind`) — an isomorphism over `X`
between the parts of their local resolutions over the common base open:
`exists_isIso_over_of_cover` glues the local transitions of the cover members `P_z`
(`exists_localTransition`), with `transition_unique` as the uniqueness hypothesis, and the result
is read onto the gluing opens `pieceGlueOpens` (the same opens, spelled through `overOpens`;
`restrictOpenIsoOfSetEq`). -/
theorem exists_transition (hbed : bed.IsEmbeddedDesing) (hind : LocalResolutionIndependentOn X bed)
    (i j : D.ι) :
    ∃ t : (pieceR D bed W hW i).toKLocallyRingedSpace.restrictOpen
          (pieceGlueOpens D bed W hW i j) ⟶
        (pieceR D bed W hW j).toKLocallyRingedSpace.restrictOpen (pieceGlueOpens D bed W hW j i),
      IsIso t ∧
        ofRestrict _ (pieceGlueOpens D bed W hW i j) ≫ D.pieceToSpace bed i (W i) (hW i) =
          (t ≫ ofRestrict _ (pieceGlueOpens D bed W hW j i)) ≫
            D.pieceToSpace bed j (W j) (hW j) := by
  -- the local transitions on the cover members, chosen
  have hloc := fun z (hz : z ∈ D.pieceDom i (W i) ⊓ D.pieceDom j (W j)) =>
    D.exists_localTransition bed W hW hbed hind i j _ le_rfl hz
  choose P hzP hPO θ hθ using hloc
  -- the gluing of local isomorphisms over `X` on the cover
  obtain ⟨t₀, ht₀, ht₀c⟩ := exists_isIso_over_of_cover (D.pieceToSpace bed i (W i) (hW i))
    (D.pieceToSpace bed j (W j) (hW j)) (D.pieceDom i (W i) ⊓ D.pieceDom j (W j))
    (fun w : (D.pieceDom i (W i) ⊓ D.pieceDom j (W j) : Opens X) => P w.1 w.2)
    (fun w => hPO w.1 w.2) (fun z hz => ⟨⟨z, hz⟩, hzP z hz⟩)
    (fun w => ⟨θ w.1 w.2, (hθ w.1 w.2).1, (hθ w.1 w.2).2.1⟩)
    (fun O' hO' s s' hs hs' hc hc' =>
      D.transition_unique bed W hW hbed hind i j O' hO' s s' hs hs' hc hc')
  -- read onto the gluing opens (the same opens up to `inf_comm`)
  have hseti : ((pieceGlueOpens D bed W hW i j :
        Opens (pieceR D bed W hW i).toKLocallyRingedSpace) :
        Set (pieceR D bed W hW i).toKLocallyRingedSpace) =
      ((Opens.comap ⟨Hom.toFun (D.pieceToSpace bed i (W i) (hW i)),
        Hom.continuous_toFun (D.pieceToSpace bed i (W i) (hW i))⟩
          (D.pieceDom i (W i) ⊓ D.pieceDom j (W j)) :
        Opens (pieceR D bed W hW i).toKLocallyRingedSpace) :
        Set (pieceR D bed W hW i).toKLocallyRingedSpace) := rfl
  have hsetj : ((Opens.comap ⟨Hom.toFun (D.pieceToSpace bed j (W j) (hW j)),
        Hom.continuous_toFun (D.pieceToSpace bed j (W j) (hW j))⟩
          (D.pieceDom i (W i) ⊓ D.pieceDom j (W j)) :
        Opens (pieceR D bed W hW j).toKLocallyRingedSpace) :
        Set (pieceR D bed W hW j).toKLocallyRingedSpace) =
      ((pieceGlueOpens D bed W hW j i : Opens (pieceR D bed W hW j).toKLocallyRingedSpace) :
        Set (pieceR D bed W hW j).toKLocallyRingedSpace) :=
    Set.ext fun q => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  refine ⟨(restrictOpenIsoOfSetEq hseti).inv ≫ t₀ ≫ (restrictOpenIsoOfSetEq hsetj).hom,
    @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv _)
      (@IsIso.comp_isIso _ _ _ _ _ _ _ ht₀ (Iso.isIso_hom _)), ?_⟩
  exact CategoryTheory.over_of_conj _ _ t₀ _ _ _ _ _ _ (restrictOpenIsoOfSetEq_inv_comp hseti)
    (restrictOpenIsoOfSetEq_hom_comp hsetj) ht₀c

end Hironaka.Manifold.LocalEmbeddingData

end
