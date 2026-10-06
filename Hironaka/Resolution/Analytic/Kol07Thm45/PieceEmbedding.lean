/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Triple
public import Hironaka.Manifold.Snc.Basic
public import Hironaka.AnalyticSpace.Manifold.Defs
public import Hironaka.AnalyticSpace.Restrict.Defs
public import Hironaka.Manifold.IdealSheaf.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial
/-!
# Local embedding data of a relatively compact piece of an analytic space

The resolution of an analytic space is assembled from local embeddings into affine space. Kollár
chooses an embedding of the variety into a smooth variety ([Kol07, Corollary 22, proof] and
[Kol07, Theorem 36, proof]) and glues the resolutions of the members of an affine cover
[Kol07, Proposition 37, proof]; Włodarczyk covers the analytic space by neighbourhoods `V`
locally isomorphic to closed analytic subsets of open balls `U ⊂ ℂⁿ`, shrunk to
`V_i ⊆ W_i ⊆ U_i` with compact closures [Wlo09, §4, (3)⇒(4)], and makes the ambient dimensions
agree by adding coordinates [Wlo09, §7.1]. An analytic space is by definition locally isomorphic
to a local analytic space in `Kⁿ` [Hir64, Ch. 0, §1, pp. 119–120]. This module defines the data
of such local embeddings, in the vocabulary of the structure `AmbientBlowUpFactorization` with
which the resolution theorem for analytic spaces (`exists_functorial_resolution`) is stated.

* `pieceAmbient G`: the open `G ⊆ 𝕜ⁿ` as the disjoint-union manifold `sigmaOpens` with ONE
  summand — the universe lift used throughout (a manifold with carrier `↥G` lives in `Type`, the
  analytic spaces in `Type u`; `AnalyticSpace.Hom` takes both spaces at one universe). Its points
  are `⟨(), x⟩`.
* `PieceEmbedding 𝕜 n X V`: a closed embedding of the open subspace `X|V` into an open `G ⊆ 𝕜ⁿ` —
  the ideal sheaf `𝓘_Y` on `pieceAmbient G`, nonzero at every stalk and reduced, with an isomorphism
  of analytic `𝕜`-spaces `X|V ≅ Sp(G)/𝓘_Y` (the fields `emb`, `emb_isIso` of
  `AmbientBlowUpFactorization`); `n` is a parameter, so that two embeddings of one piece into `𝕜ⁿ`
  and `𝕜ᵐ` can be compared.
* `PieceEmbedding.ambientTriple E`: the analytic triple `(G, 𝓘_Y, ∅)`, the input of the embedded
  desingularization functor for the piece (to desingularize `Y` one resolves the marked ideal
  `(I_Y, 1)` with empty divisor, [Wlo09, §6, Remark (3) after Step 2b]).
* `LocalEmbeddingData 𝕜 X U`: finitely many open pieces `Uᵢ ⊆ X` with relatively compact inner opens
  `Vᵢ`, `closure Vᵢ ⊆ Uᵢ`, covering `U`, one ambient dimension `n`, and a `PieceEmbedding 𝕜 n X Uᵢ`
  per piece; `LocalEmbeddingData.subset_iUnion_piece` (the corresponding field of
  `AmbientBlowUpFactorization`) is derived.

That every relatively compact open of a reduced analytic `𝕜`-space carries such data is
`exists_localEmbeddingData_of_padTools` (`PieceModel.lean`) at the padding tools `padTools` of
`PieceModelPad.lean`.
-/

@[expose] public section

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

noncomputable section

namespace Hironaka.Manifold

variable (𝕜 : Type) [RCLike 𝕜]

/-- **The one-piece ambient**: the open `G ⊆ 𝕜ⁿ` as the disjoint-union manifold `sigmaOpens`
with a single summand, so that it lives in the universe of the analytic spaces it embeds
(`AnalyticSpace.Hom` takes both spaces at one universe; the carrier `↥G` alone is in `Type`). Its
points are `⟨(), x⟩`. The ambient manifold of an `AmbientBlowUpFactorization` is the disjoint
union of the ambients of the members of a finite open cover, as in the gluing argument of
[Kol07, Proposition 37, proof]. -/
abbrev pieceAmbient {n : ℕ} (G : Opens (Fin n → 𝕜)) : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜) :=
  AnalyticManifold.sigmaOpens fun _ : PUnit.{u + 1} => G

/-- **A closed embedding of the open subspace `X|V` into an open `G ⊆ 𝕜ⁿ`**, the local model of
an analytic space ([Hir64, Ch. 0, §1, pp. 119–120]; the embedding into a smooth variety of
[Kol07, Corollary 22, proof] and [Kol07, Theorem 36, proof]; the neighbourhood isomorphic to a
closed analytic subset of a ball of [Wlo09, §4, (3)⇒(4)]): the ideal sheaf `𝓘_Y` of the closed
subspace `Y ⊆ G` on the one-piece ambient, nonzero at every stalk (as after adding a coordinate,
[Wlo09, §7.1]) and reduced (the defining ideal of a reduced subspace), with an isomorphism of
analytic `𝕜`-spaces `X|V ≅ Sp(G)/𝓘_Y` (the fields `emb`, `emb_isIso` of
`AmbientBlowUpFactorization`). The ambient dimension `n` is a parameter, so that two embeddings of
one piece into `𝕜ⁿ` and `𝕜ᵐ` can be compared. -/
structure PieceEmbedding (n : ℕ) (X : AnalyticSpace.{u} 𝕜) (V : Set X) where
  /-- The open subset `G ⊆ 𝕜ⁿ`. -/
  G : Opens (Fin n → 𝕜)
  /-- The ideal sheaf `𝓘_Y` of the closed subspace `Y ⊆ G` (locally finitely generated). -/
  ideal : AnalyticManifold.IdealSheaf (pieceAmbient 𝕜 G)
  /-- `𝓘_Y` is nonzero at every stalk. -/
  isNonzeroEverywhere : ideal.IsNonzeroEverywhere
  /-- `𝓘_Y` is reduced: the defining ideal sheaf of a reduced closed subspace has radical stalks. -/
  isReduced : ideal.IsReduced
  /-- The closed embedding: `X|V` is isomorphic to `Sp(G)/𝓘_Y` … -/
  emb : X.restrictSet V ⟶ ideal.toAnalyticSpace
  /-- … as analytic `𝕜`-spaces. -/
  emb_isIso : CategoryTheory.IsIso emb

namespace PieceEmbedding

open _root_.Manifold

variable {𝕜} {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X} (E : PieceEmbedding 𝕜 n X V)

/-- **The analytic triple `(G, 𝓘_Y, ∅)` of the piece**: the input of the embedded
desingularization functor for the piece (to desingularize `Y` one resolves the marked ideal
`(I_Y, 1)` with empty divisor, [Wlo09, §6, Remark (3) after Step 2b]); its divisor is empty
(`HypersurfaceFamily.empty`, index `PEmpty`, simple normal crossings by `isSnc_empty`). -/
def ambientTriple :
    AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (pieceAmbient 𝕜 E.G) where
  I := E.ideal
  isNonzeroEverywhere := E.isNonzeroEverywhere
  F := HypersurfaceFamily.empty _
  isSnc := HypersurfaceFamily.isSnc_empty

/-- The divisor of the piece's triple is empty. -/
theorem ambientTriple_F : E.ambientTriple.F = HypersurfaceFamily.empty _ := rfl

/-- The ideal sheaf of the piece's triple is `𝓘_Y`. -/
theorem ambientTriple_I : E.ambientTriple.I = E.ideal := rfl

end PieceEmbedding

/-- **The local embedding data of an open `U ⊆ X`**: finitely many open pieces `Uᵢ` with
relatively compact inner opens `Vᵢ`, `closure Vᵢ ⊆ Uᵢ`, covering `U`; one ambient dimension `n`;
and a closed embedding of each `X|Uᵢ` into an open of `𝕜ⁿ` (`PieceEmbedding`). The fields `n`,
`ι`, `finite`, `piece`, `isOpen_piece` are the first block of `AmbientBlowUpFactorization`; the
shrinking is Włodarczyk's cover `V_i ⊆ W_i ⊆ U_i` with compact closures [Wlo09, §4, (3)⇒(4)],
the common `n` his addition of coordinates [Wlo09, §7.1], and the finite affine cover the one
glued in [Kol07, Proposition 37, proof]. -/
structure LocalEmbeddingData (X : AnalyticSpace.{u} 𝕜) (U : Set X) where
  /-- The common dimension `n` of the ambient pieces `Gᵢ ⊆ 𝕜ⁿ`. -/
  n : ℕ
  /-- The finite index set of the pieces. -/
  ι : Type u
  [finite : Finite ι]
  /-- The open subspaces `Uᵢ ⊆ X` carrying the local models … -/
  piece : ι → Set X
  isOpen_piece : ∀ i, IsOpen (piece i)
  /-- … and the inner opens `Vᵢ`, relatively compact in `X` with `closure Vᵢ ⊆ Uᵢ`
  (Włodarczyk's `V_i ⊆ W_i ⊆ U_i` with compact closures [Wlo09, §4, (3)⇒(4)]), … -/
  inner : ι → Set X
  isOpen_inner : ∀ i, IsOpen (inner i)
  isCompact_closure_inner : ∀ i, IsCompact (closure (inner i))
  closure_inner_subset : ∀ i, closure (inner i) ⊆ piece i
  /-- … covering `U`. -/
  subset_iUnion_inner : U ⊆ ⋃ i, inner i
  /-- The closed embedding of each piece into an open of `𝕜ⁿ`. -/
  embedding : ∀ i, PieceEmbedding 𝕜 n X (piece i)

attribute [instance] LocalEmbeddingData.finite

namespace LocalEmbeddingData

variable {𝕜} {X : AnalyticSpace.{u} 𝕜} {U : Set X} (D : LocalEmbeddingData 𝕜 X U)

/-- The pieces cover `U` (the field `subset_iUnion_piece` of `AmbientBlowUpFactorization`), from
the inner opens. -/
theorem subset_iUnion_piece : U ⊆ ⋃ i, D.piece i :=
  D.subset_iUnion_inner.trans
    (iUnion_mono fun i => subset_closure.trans (D.closure_inner_subset i))

end LocalEmbeddingData

end Hironaka.Manifold

end
