/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlue
import Hironaka.AnalyticSpace.Exhaustion
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceRestrict
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The gluing datum of the local resolutions: the pieces and their ambient opens

Włodarczyk glues the canonical desingularizations of the local embeddings of an analytic space
into a desingularization of the space [Wlo09, §4, (3)⇒(4)]. For local embedding data
`D : LocalEmbeddingData 𝕜 X U` (inner opens `V_i ⋐ U_i` with compact closures, covering `U`), this
module holds the piece-level notions of the proof that the local resolutions glue
(`ResolutionGluesOn`, `PieceGlue.lean`; proved in `PieceGlueDatum.lean` as
`LocalEmbeddingData.resolutionGluesOn_of_isEmbeddedDesing_of_independent`) that need no gluing
yet:

* `LocalEmbeddingData.pieceR D bed W hW i` and `pieceGlueOpens D bed W hW i j`: the pieces
  `Ỹ_i := localResolution (D.embedding i) bed (W i) _` of the gluing datum and their gluing opens
  (`GlueOver.glueOpens`, the points over the overlaps `pieceDom i ⊓ pieceDom j`);
* `LocalResolutionIndependentOn X bed`: the independence of the local resolution from the
  embedding, as a hypothesis — the conclusion of `localResolution_independent_of_local`
  (`LocalResolutionIndependent.lean`) for a fixed `X`, the input of the transitions between the
  pieces; discharged from `IsEmbeddedDesing` in `GluingProperties.lean`;
* `LocalEmbeddingData.exists_W D i`: the relatively compact ambient open `W_i` of the piece whose
  base open contains `closure (inner i)` (Włodarczyk's `V̄_i ⊂ W_i`) — the ambient image of the
  compact `closure (inner i)` (pulled into the piece along the closed embedding `ambientPoint`) is
  compact in the ambient `G_i`, and `exists_opens_isCompact_closure_superset` (the ambient being
  locally compact Hausdorff) gives `W_i ⋐ G_i` around it.

Not in the sources beyond Włodarczyk's construction; bookkeeping.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace KLocallyRingedSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜]

/-- **The independence of the local resolution from the embedding, as a hypothesis**: for two
piece embeddings `E₁`, `E₂` of the same open `V ⊆ X` and relatively compact ambient opens `W₁`,
`W₂`, the local resolutions restricted over `embPreimage W₁ ∩ embPreimage W₂` are isomorphic over
the piece by a UNIQUE isomorphism — the conclusion of `localResolution_independent_of_local`
(`LocalResolutionIndependent.lean`) for a fixed `X`, with the functor `bed` outside the
quantifier. The theorems of the gluing take this proposition as a hypothesis `hind`;
`localResolutionIndependentOn_of_isEmbeddedDesing` (`GluingProperties.lean`) discharges it from
`IsEmbeddedDesing`. -/
def LocalResolutionIndependentOn (X : AnalyticSpace.{u} 𝕜)
    (bed : BEDanFamStar.{u} 𝕜) :
    Prop :=
  ∀ {V : Set X} {n m : ℕ} (E₁ : PieceEmbedding 𝕜 n X V) (E₂ : PieceEmbedding 𝕜 m X V)
    (W₁ : Opens (pieceAmbient.{u} 𝕜 E₁.G))
    (hW₁ : IsCompact (closure (W₁ : Set (pieceAmbient 𝕜 E₁.G))))
    (W₂ : Opens (pieceAmbient.{u} 𝕜 E₂.G))
    (hW₂ : IsCompact (closure (W₂ : Set (pieceAmbient 𝕜 E₂.G)))),
    ∃! ψ : (E₁.localResolution bed W₁ hW₁).restrictSet (E₁.localResolutionToPiece bed W₁ hW₁ ⁻¹'
        (E₁.embPreimage W₁ ∩ E₂.embPreimage
        W₂)) ⟶ (E₂.localResolution bed W₂ hW₂).restrictSet
        (E₂.localResolutionToPiece bed W₂ hW₂ ⁻¹' (E₁.embPreimage W₁ ∩ E₂.embPreimage W₂)),
      IsIso ψ ∧
      ψ ≫ (E₂.localResolutionToPiece bed W₂ hW₂).restrictSet (E₁.embPreimage W₁ ∩ E₂.embPreimage
          W₂) =
        (E₁.localResolutionToPiece bed W₁ hW₁).restrictSet (E₁.embPreimage W₁ ∩ E₂.embPreimage W₂)

end Hironaka.Manifold

namespace Hironaka.Manifold.LocalEmbeddingData

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {U : Set X}
  (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
  (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
  (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient 𝕜 (D.embedding i).G))))

/-- The pieces of the gluing datum — the local resolutions of the pieces of `D` over the chosen
ambient opens (Włodarczyk's `Ṽ_i`, [Wlo09, §4, (3)⇒(4)]). -/
abbrev pieceR (i : D.ι) : AnalyticSpace.{u} 𝕜 :=
  (D.embedding i).localResolution bed (W i) (hW i)

/-- The gluing opens of the pieces — the points of `Ỹ_i` over the overlap `pieceDom i ⊓ pieceDom j`
of the base opens (`GlueOver.glueOpens`; [Wlo09, §4, (3)⇒(4)]). -/
abbrev pieceGlueOpens (i j : D.ι) : Opens (pieceR D bed W hW i) :=
  GlueOver.glueOpens X (pieceR D bed W hW) (fun i => D.pieceToSpace bed i (W i) (hW i))
    (fun i => D.pieceDom i (W i)) i j

/-- **The ambient opens of the gluing datum** (Włodarczyk's `V̄_i ⊂ W_i`, [Wlo09, §4, (3)⇒(4)]) —
each inner closure lies over a relatively compact open of the piece's ambient: the ambient image
of the compact `closure (inner i)` is compact (`isClosedEmbedding_ambientPoint`), and
`exists_opens_isCompact_closure_superset` puts a relatively compact open around it in the locally
compact Hausdorff ambient `G_i`. -/
theorem exists_W (i : D.ι) :
    ∃ W' : Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G),
      IsCompact (closure (W' : Set (pieceAmbient 𝕜 (D.embedding i).G))) ∧
        closure (D.inner i) ⊆ D.pieceDom i W' := by
  have hsub : ∀ x ∈ closure (D.inner i), x ∈ openOf X (D.piece i) :=
    fun _ hx => mem_openOf_of_subset Set.Subset.rfl
      (D.closure_inner_subset i hx)
  -- the compact `closure (inner i)`, pulled into the piece
  have hK₀ : IsCompact ((Subtype.val :
      {x // x ∈ openOf X (D.piece i)} → X) ''
        (Subtype.val ⁻¹' closure (D.inner i))) :=
    (congrArg IsCompact (Set.image_preimage_eq_of_subset fun x hx =>
      ⟨⟨x, hsub x hx⟩, rfl⟩)).mpr (D.isCompact_closure_inner i)
  have hK : IsCompact ((D.embedding i).ambientPoint ''
      (Subtype.val ⁻¹' closure (D.inner i) : Set (X.restrictSet (D.piece i)))) :=
    IsCompact.image ((Subtype.isCompact_iff
        (p := fun x => x ∈ openOf X (D.piece i))
        (s := Subtype.val ⁻¹' closure (D.inner i))).mpr hK₀)
      (D.embedding i).isClosedEmbedding_ambientPoint.continuous
  -- a relatively compact open around it in the locally compact Hausdorff ambient
  have : LocallyCompactSpace (pieceAmbient.{u} 𝕜 (D.embedding i).G) :=
    ChartedSpace.locallyCompactSpace (H := Fin D.n → 𝕜) (M := pieceAmbient.{u} 𝕜 (D.embedding i).G)
  obtain ⟨W', hKW', hW'⟩ := exists_opens_isCompact_closure_superset hK
  refine ⟨W', hW', fun x hx => ?_⟩
  exact (D.embedding i).mem_domOpens.mpr ⟨⟨x, hsub x hx⟩, hKW' ⟨⟨x, hsub x hx⟩, hx, rfl⟩, rfl⟩

end Hironaka.Manifold.LocalEmbeddingData

end
