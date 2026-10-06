/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceEmbedding
public import Hironaka.Resolution.Analytic.Functor.EmbeddedDesingFam
public import Hironaka.Manifold.FiniteSuccession.Restrict.StrictSubspaceSeqCompat
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The local resolution of a piece

The local resolution of a piece is the embedded desingularization sequence of the piece's triple,
its final strict transform and the map to the piece. Włodarczyk defines the canonical
desingularization of a germ `Y_Z` through the canonical embedded desingularization
`(Ũ_Z, Ỹ_Z) → (U_Z, Y_Z)` of a local embedding: it is `Ỹ_Z → Y_Z` [Wlo09, §4, (3)⇒(4)], obtained by
resolving the marked ideal `(I_Y, 1)` with empty divisor [Wlo09, §6, Remark (3) after Step 2b].
Kollár's resolution of an affine variety is likewise read off the principalization of its ideal in
an ambient smooth variety ([Kol07, Corollary 22, proof] and [Kol07, Theorem 36, proof]; the
algebraic counterpart in this library is `Hironaka.Resolution.BR_affine`). For a piece
`E : PieceEmbedding 𝕜 n X V` and an embedded desingularization functor `bed : BEDanFamStar 𝕜` (the
type of such functors; a particular one is constructed in
`Hironaka/Resolution/Analytic/Wlo09/Concrete.lean`), read per relatively compact open `W` of the
piece's ambient:

* `BEDanFamStar.seqOn`, `lastIdealOn`, `localResolutionOn`, `localResolutionMapOn`: the value of
  the functor on any triple `T` of its domain over `W`, the final strict transform of `T.I|W`
  along it, the closed subspace it cuts out and the latter's map to `Sp(W)/T.I|W`; the three piece
  notions below are their instances at the piece's triple;
* `PieceEmbedding.localResolutionSeq E bed W hW`: the value of the functor on the piece's triple
  `(G, 𝓘_Y, ∅)` over `W` — the finite blow-up sequence `σ : P_r → ⋯ → P_0 = W` of Włodarczyk's
  modified sequence [Wlo09, §7.4], with the properties of [Wlo09, Theorem 2.0.2] as the clauses of
  `IsEmbeddedDesing`;
* `PieceEmbedding.localResolution E bed W hW`: `Ỹ` — the final ideal-theoretic strict transform of
  `𝓘_Y|_W` along the sequence (`FiniteSuccession.strictTransformSubspaceSeq`, the chain
  `transform` of `AmbientBlowUpFactorization`), as an analytic `𝕜`-space
  (`IdealSheaf.toAnalyticSpace`);
* `PieceEmbedding.localResolutionMap E bed W hW`: `Π = σ|_{Ỹ} : Ỹ → Y|_W`, the morphism of closed
  subspaces over the composite `σ^r` (`KLocallyRingedSpace.quotientMap`), whose compatibility
  hypothesis is `compat_composite_strictTransformSubspaceSeq` (`StrictSubspaceSeqCompat.lean`);
  `localResolutionMap_comp_ι` is the field `map_comp` of `AmbientBlowUpFactorization`:
  `ι_Y ∘ Π = σ^r ∘ ι_Ỹ`.

`emb` (the model isomorphism `X|V ≅ Sp(G)/𝓘_Y` of the piece) and `localResolutionMap` are kept
separate, as `AmbientBlowUpFactorization` keeps `emb` and `map`; they are composed where the
resolution of the space is assembled. The functor `bed` is an explicit binder: this module uses
only the types `DomBEDan`, `BEDanFam`, `BEDanFamStar`, never a particular functor.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff CategoryTheory

universe u

namespace Hironaka.Manifold

namespace BEDanFamStar

variable {𝕜 : Type} [RCLike 𝕜] (bed : BEDanFamStar.{u} 𝕜) {n : ℕ}
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : Manifold.AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
  (W : Opens M) (hW : IsCompact (closure (W : Set M)))

/-- **The value of the functor on the triple `T` over the relatively compact open `W`**: a finite
blow-up sequence on `M|W`. -/
def seqOn : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    (M.restrict W) :=
  ((bed.fam n).fam T hT).seqOn W hW

/-- The ideal of the restricted triple `T|W` (the pull-back along the inclusion). -/
abbrev restrictedIdealOn : AnalyticManifold.IdealSheaf (M.restrict W) := T.I.restrict W

/-- The final strict transform of `T.I|W` along the sequence (`strictTransformSubspaceSeq`). -/
def lastIdealOn : AnalyticManifold.IdealSheaf ((bed.seqOn T hT W hW).stage (Fin.last _)) :=
  (bed.seqOn T hT W hW).toSuccession.strictTransformSubspaceSeq (restrictedIdealOn T W)
    (Fin.last _)

/-- **The local resolution of the triple `T` over `W`** — the closed subspace of the last stage
cut out by the final strict transform (the piece case is `PieceEmbedding.localResolution`). -/
def localResolutionOn : AnalyticSpace.{u} 𝕜 :=
  (bed.lastIdealOn T hT W hW).toAnalyticSpace

/-- **Its map to the restricted closed subspace `Sp(W)/T.I|W`**, the morphism of closed subspaces
induced by the composite of the sequence (`compat_composite_strictTransformSubspaceSeq`). -/
def localResolutionMapOn :
    bed.localResolutionOn T hT W hW ⟶ (restrictedIdealOn T W).toAnalyticSpace :=
  AnalyticSpace.KLocallyRingedSpace.quotientMap
    (AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (bed.seqOn T hT W hW).toSuccession.composite) _ _
    ((bed.seqOn T hT W hW).toSuccession.compat_composite_strictTransformSubspaceSeq
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (restrictedIdealOn T W))

end BEDanFamStar

namespace PieceEmbedding

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V)

/-- The piece's triple `(G, 𝓘_Y, ∅)` lies in the domain class `DomBEDan` of the embedded
desingularization functor: its divisor is empty and `𝓘_Y` is reduced (the marked ideal `(I_Y, 1)`
with empty divisor of [Wlo09, §6, Remark (3) after Step 2b]). -/
theorem domBEDan_ambientTriple : DomBEDan 𝕜 E.ambientTriple :=
  ⟨by rw [ambientTriple_F]; exact ⟨fun x => PEmpty.elim x⟩, E.isReduced⟩

/-- **The embedded desingularization sequence of the piece over the relatively compact open
`W`**: the value of the functor `bed : BEDanFamStar 𝕜`, in the piece's dimension `n`, on the
triple `(G, 𝓘_Y, ∅)` over `W` — a finite blow-up sequence `σ : P_r → ⋯ → P_0 = W` with smooth
centres, the canonical embedded desingularization of the germ [Wlo09, §4, (3)⇒(4)] (its
properties, the clauses of [Wlo09, Theorem 2.0.2], are the theorems about `IsEmbeddedDesing`; the
principalization of the ideal of the variety in [Kol07, Corollary 22, proof]). -/
def localResolutionSeq (bed : BEDanFamStar.{u} 𝕜) (W : Opens (pieceAmbient 𝕜 E.G))
    (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G)))) :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        ((pieceAmbient 𝕜 E.G).restrict W) :=
  bed.seqOn E.ambientTriple E.domBEDan_ambientTriple W hW

/-- The ideal sheaf `𝓘_Y|_W` of the piece restricted to `W` — the ideal of the restricted triple
`(G, 𝓘_Y, ∅)|_W` (the pullback along the inclusion). -/
abbrev restrictedIdeal (W : Opens (pieceAmbient 𝕜 E.G)) :
    AnalyticManifold.IdealSheaf ((pieceAmbient 𝕜 E.G).restrict W) :=
  E.ideal.restrict W

/-- **The local resolution of the piece over `W`**: the final ideal-theoretic strict transform
`Ỹ = Y_r` of `𝓘_Y|_W` along the sequence (`FiniteSuccession.strictTransformSubspaceSeq`), as an
analytic `𝕜`-space (`IdealSheaf.toAnalyticSpace`, the closed subspace of `Sp(P_r)`) — Włodarczyk's
`Ỹ_Z` [Wlo09, §4, (3)⇒(4)], the smooth centre `Z_j` at the stage where it contains the generic
point in [Kol07, Corollary 22, proof]; the chain `Y_0, …, Y_r` of `AmbientBlowUpFactorization`. The
analytic counterpart of `Hironaka.Resolution.BR_affine`. -/
def localResolution (bed : BEDanFamStar.{u} 𝕜) (W : Opens (pieceAmbient 𝕜 E.G))
    (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G)))) : AnalyticSpace.{u} 𝕜 :=
  bed.localResolutionOn E.ambientTriple E.domBEDan_ambientTriple W hW

/-- **The local resolution map `Π = σ|_{Ỹ} : Ỹ → Y|_W`**, Włodarczyk's `Ỹ_Z → Y_Z`
[Wlo09, §4, (3)⇒(4)]: the morphism of closed subspaces induced by the composite `σ^r : P_r → W`
(`KLocallyRingedSpace.quotientMap`), under the compatibility
`compat_composite_strictTransformSubspaceSeq` (the inverse image of `𝓘_Y|_W` lies in `𝓘_Ỹ`,
[BM97, §3, Proposition 3.13] iterated). The field `map` of `AmbientBlowUpFactorization`; as Kollár
warns, it need not itself be a composite of smooth blow-ups [Kol07, Warning 23]. -/
def localResolutionMap (bed : BEDanFamStar.{u} 𝕜) (W : Opens (pieceAmbient 𝕜 E.G))
    (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G)))) :
    E.localResolution bed W hW ⟶ (E.restrictedIdeal W).toAnalyticSpace :=
  bed.localResolutionMapOn E.ambientTriple E.domBEDan_ambientTriple W hW

/-- The local resolution map lies over the composite `σ^r` (the field `map_comp` of
`AmbientBlowUpFactorization`): `ι_Y ∘ Π = Sp(σ^r) ∘ ι_Ỹ` as morphisms `Ỹ → Sp(W)`. -/
theorem localResolutionMap_comp_ι (bed : BEDanFamStar.{u} 𝕜) (W : Opens (pieceAmbient 𝕜 E.G))
    (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G)))) :
    E.localResolutionMap bed W hW ≫ (E.restrictedIdeal W).toAnalyticSpaceι =
      ((E.localResolutionSeq bed W hW).toSuccession.strictTransformSubspaceSeq (E.restrictedIdeal W)
          (Fin.last _)).toAnalyticSpaceι ≫
        AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          (E.localResolutionSeq bed W hW).toSuccession.composite :=
  Subtype.ext (AnalyticSpace.QuotientSpace.map_comp_ι
    (AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (E.localResolutionSeq bed W hW).toSuccession.composite).1 _ _
    ((E.localResolutionSeq bed W hW).toSuccession.compat_composite_strictTransformSubspaceSeq
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (E.restrictedIdeal W)))

end PieceEmbedding

end Hironaka.Manifold

end
