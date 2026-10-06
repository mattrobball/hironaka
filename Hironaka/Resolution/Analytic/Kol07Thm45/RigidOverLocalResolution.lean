/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.Glue.OverRigidity
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueProof
public import Hironaka.Resolution.Analytic.Kol07Thm45.Resolution
import Hironaka.AnalyticSpace.HomLocal
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalModel
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueIndep
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceTransitionGlue
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic
/-!
# Rigidity of the local resolutions over `X`

Kollár's descent of the centres from the disjoint union of an affine cover — the pieces of the
centre agree on the overlaps, (37.2) in [Kol07, Proposition 37, proof] — and the uniqueness of the
canonical isomorphisms of the local resolutions [Kol07, Theorem 36, proof]; Włodarczyk's
transitions over the overlaps [Wlo09, §4, (3)⇒(4)]. The independence of the local resolution from
the embedding, taken as the hypothesis `hind : LocalResolutionIndependentOn X bed`, says the
isomorphism over the base between two local resolutions is UNIQUE. Read at one local resolution
against itself, this is RIGIDITY: every automorphism over `X` of a part of a local resolution over
a base open is the identity — the `haut` hypothesis of `isoOver_unique_of_aut` (`LocalModel.lean`),
named `RigidOver`. This module supplies it for the FOUR maps to `X` that the resolutions carry,
each by `hind`'s uniqueness applied to the given automorphism AND to `𝟙`:

* `PieceEmbedding.rigidOver_toSpaceMap`: the parts of a piece's local resolution over ANY open
  under its base open (`toSpaceMap`), by the cover argument of `transition_unique` at one
  embedding — `exists_localTransition_pair E E` at each point, then `hom_ext_of_cover`; with the
  corollary `rigidOver_toSpaceMap_domOpens` at `O := E.domOpens Q`, `Q ≤ W` (`domOpens_mono`);
* `LocalEmbeddingData.rigidOver_pieceToSpace`: the pieces of a gluing datum (`pieceToSpace`) —
  `transition_unique` at `i = j`;
* `LocalEmbeddingData.rigidOver_resolutionOnToSpace`: the glued `resolutionOn`
  (`resolutionOnToSpace`) — the uniqueness clause of `exists_isoOver_resolutionOn D D`;
* `BEDanFamStar.ExhaustionGluing.rigidOver_descMap`: the exhaustion glue (`descMap`) —
  `ExhaustionGluing.isoOver_eq_id` (`LocalModel.lean`), repackaged.

The datum-level and `resolutionOn`-level forms are the rigidity hypotheses of the gluing of the
exceptional families (`compatClosedSubspaces_pair_of_forall_exists_isoOver`,
`eq_tOver_of_isoOver`; `CoproductGluedFamilyCompat.lean`, `ExhaustionChainFamilies.lean`); the
piece-level and exhaustion-glue forms are stated for completeness and have no user in the
library. Not in the sources beyond the remarks cited; bookkeeping.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set
open AnalyticSpace.KLocallyRingedSpace

universe u

namespace Hironaka.Manifold.PieceEmbedding

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {n : ℕ} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V)

/-- **The parts of a piece's local resolution are rigid over `X`** ([Kol07, Theorem 36, proof];
[Wlo09, §4, (3)⇒(4)]; with the independence as `hind`) — every automorphism over `X` of the part
over an open `O` under the base open is the identity. The argument of `transition_unique` at ONE
embedding: at every point of `O` the unique local transition
of `E` with itself (`exists_localTransition_pair`) is what BOTH `t` and `𝟙` restrict to
(`restrictOver`, `isIso_restrictOver`, `restrictOver_over`), and morphisms agreeing on a cover agree
(`hom_ext_of_cover`, `comp_eq_of_restrict_eq`, `restrictOver_comp_restrictIncl`). -/
theorem rigidOver_toSpaceMap (hV : IsOpen V) (bed : BEDanFamStar.{u} 𝕜)
    (hbed : bed.IsEmbeddedDesing) (hind : LocalResolutionIndependentOn X bed)
    (W : Opens (pieceAmbient.{u} 𝕜 E.G)) (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G))))
    (O : Opens X) (hO : O ≤ E.domOpens W) : RigidOver (E.toSpaceMap bed W hW) O := by
  intro t ht hc
  have hid : ofRestrict _ _ ≫ E.toSpaceMap bed W hW =
      ((𝟙 _ : (E.localResolution bed W hW).toKLocallyRingedSpace.restrictOpen
        (Opens.comap ⟨Hom.toFun (E.toSpaceMap bed W hW),
          Hom.continuous_toFun (E.toSpaceMap bed W hW)⟩ O) ⟶ _) ≫ ofRestrict _ _) ≫
        E.toSpaceMap bed W hW :=
    congrArg (fun k => k ≫ E.toSpaceMap bed W hW) (Category.id_comp _).symm
  -- on every cover member `t` and `𝟙` restrict to the unique local transition of `E` with itself
  have hloc : ∀ z ∈ O, ∃ (P : Opens X) (_ : z ∈ P) (hPO : P ≤ O),
      restrictOver (E.toSpaceMap bed W hW) (E.toSpaceMap bed W hW) hPO t hc =
        restrictOver (E.toSpaceMap bed W hW) (E.toSpaceMap bed W hW) hPO (𝟙 _) hid := by
    intro z hz
    obtain ⟨P, hzP, hPO, θ, -, -, huniq⟩ :=
      E.exists_localTransition_pair E hV hV bed hbed hind W hW W hW O (le_inf hO hO) hz
    refine ⟨P, hzP, hPO, ?_⟩
    exact (huniq _ (@isIso_restrictOver _ _ _ _ _ _ _ _ _ hPO t hc ht)
        (restrictOver_over _ _ hPO t hc)).trans
      (huniq _ (@isIso_restrictOver _ _ _ _ _ _ _ _ _ hPO (𝟙 _) hid inferInstance)
        (restrictOver_over _ _ hPO (𝟙 _) hid)).symm
  choose P hzP hPO hEq using hloc
  -- the cover of the part over `O` by the parts over the `P z`, and the agreement on each member
  refine hom_ext_of_cover t (𝟙 _)
    (fun z : O => glueCoverOpens (E.toSpaceMap bed W hW) O (fun w : O => P w.1 w.2) z)
    (fun x => glueCoverOpens_cover _ O _ (fun w hw => ⟨⟨w, hw⟩, hzP w hw⟩) x) fun z => ?_
  exact CategoryTheory.comp_eq_of_restrict_eq _ _ _ t (𝟙 _) _ _ _
    (pieceIncl_comp_restrictIncl _ O (fun w : O => P w.1 w.2) (fun w => hPO w.1 w.2) z)
    (restrictOver_comp_restrictIncl _ _ (hPO z.1 z.2) t hc)
    (restrictOver_comp_restrictIncl _ _ (hPO z.1 z.2) (𝟙 _) hid) (hEq z.1 z.2)

/-- The named form — rigidity over the base open `domOpens Q` of an ambient open `Q ≤ W`. -/
theorem rigidOver_toSpaceMap_domOpens (hV : IsOpen V) (bed : BEDanFamStar.{u} 𝕜)
    (hbed : bed.IsEmbeddedDesing) (hind : LocalResolutionIndependentOn X bed)
    (W : Opens (pieceAmbient.{u} 𝕜 E.G)) (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G))))
    (Q : Opens (pieceAmbient.{u} 𝕜 E.G)) (hQ : Q ≤ W) :
    RigidOver (E.toSpaceMap bed W hW) (E.domOpens Q) :=
  E.rigidOver_toSpaceMap hV bed hbed hind W hW (E.domOpens Q) (E.domOpens_mono hQ)

end Hironaka.Manifold.PieceEmbedding

namespace Hironaka.Manifold.LocalEmbeddingData

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {U : Set X}
  (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)

/-- **The parts of a datum's pieces are rigid over `X`** (with the independence as `hind`) —
`transition_unique` at `i = j`, for the automorphism and for `𝟙`. -/
theorem rigidOver_pieceToSpace (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient 𝕜 (D.embedding i).G))))
    (hbed : bed.IsEmbeddedDesing) (hind : LocalResolutionIndependentOn X bed) (i : D.ι)
    (O : Opens X) (hO : O ≤ D.pieceDom i (W i)) :
    RigidOver (D.pieceToSpace bed i (W i) (hW i)) O := fun t ht hc =>
  D.transition_unique bed W hW hbed hind i i O (le_inf hO hO) t (𝟙 _) ht inferInstance hc
    (congrArg (fun k => k ≫ D.pieceToSpace bed i (W i) (hW i)) (Category.id_comp _).symm)

/-- **The parts of the glued `resolutionOn` are rigid over `X`** (with the independence as `hind`)
— the uniqueness clause of `exists_isoOver_resolutionOn D D`, for the automorphism and for `𝟙`. -/
theorem rigidOver_resolutionOnToSpace (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) (O : Opens X) (hO : (O : Set X) ⊆ U) :
    RigidOver (D.resolutionOnToSpace bed) O := fun t ht hc => by
  obtain ⟨s, -, -, huniq⟩ :=
    D.exists_isoOver_resolutionOn D bed hbed hind O fun x hx => ⟨hO hx, hO hx⟩
  have hid : ofRestrict _ _ ≫ D.resolutionOnToSpace bed =
      ((𝟙 _ : (D.resolutionOn bed).toKLocallyRingedSpace.restrictOpen
        (Opens.comap ⟨Hom.toFun (D.resolutionOnToSpace bed),
          Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ O) ⟶ _) ≫ ofRestrict _ _) ≫
        D.resolutionOnToSpace bed := by
    rw [Category.id_comp]
  exact (huniq t ht hc).trans (huniq (𝟙 _) inferInstance hid).symm

end Hironaka.Manifold.LocalEmbeddingData

namespace Hironaka.Manifold.BEDanFamStar

variable {𝕜 : Type} [RCLike 𝕜] (bed : BEDanFamStar.{u} 𝕜)
  (X : AnalyticSpace.{u} 𝕜)

/-- **The parts of the exhaustion glue are rigid over `X`** — `ExhaustionGluing.isoOver_eq_id`
(`LocalModel.lean`), in the `RigidOver` spelling. -/
theorem ExhaustionGluing.rigidOver_descMap (Ξ : bed.ExhaustionGluing X)
    (hbed : bed.IsEmbeddedDesing) (hind : LocalResolutionIndependentOn X bed) (O : Opens X) :
    RigidOver Ξ.glue.descMap O := fun t ht hc =>
  ExhaustionGluing.isoOver_eq_id bed X Ξ hbed hind O t ht hc

end Hironaka.Manifold.BEDanFamStar

end
