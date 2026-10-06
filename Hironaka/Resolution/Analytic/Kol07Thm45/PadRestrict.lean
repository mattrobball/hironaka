/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceRestrict
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.OrderReduction.Step22Pullback
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic
/-!
# The padded restricted piece

Włodarczyk's extension of an open embedding of germs `Y_Z ⊂ Y_{Z'}` to an open embedding
`U_Z ⊂ U_{Z'}` of the ambient manifolds [Wlo09, §4, (3)⇒(4)], read together with the padding
`X ⊂ ℂⁿ ⊂ ℂᴺ` of Kollár's proof of Theorem 36 [Kol07, Theorem 36, proof] (compare
[Wlo09, §7.1]): shrinking the piece to an open `V' ⊆ V` of the space and then padding its ambient
along `σ : Fin n ↪ Fin n'` gives the same piece as padding first and then restricting to the padded
shrunk ambient `padOpens σ G'` — the **padded restricted piece is the pull-back of the padded
piece** along the inclusion `Sp(padOpens σ G') → Sp(padOpens σ G)` of one-piece ambients, an
analytic open embedding.

The four items:
* (i) `padOpens_mono`: padding is monotone in the open; `isAnalyticOpenEmbedding_pieceAmbientIncl`:
  the inclusion of one-piece ambients is `IsAnalyticOpenEmbedding` (a local analytic isomorphism,
  injective — the two halves proved in `PieceAmbientIncl.lean`).
* (ii) `padCoordProj_comp_pieceAmbientIncl`: the coordinate projection `z ↦ z ∘ σ` commutes with
  the inclusions of ambients; `preimage_padSlice_pieceAmbientIncl`: the coordinate slice
  `{z_j = 0, j ∉ range σ}` pulls back to the coordinate slice; (ii′) `pieceAmbientIncl_padExt`: the
  inclusions carry the zero extension `padExt` to the zero extension — all identities of
  coordinates.
* (iii) `padIdeal_comap`: `padIdeal σ (J|_{G'}) = (padIdeal σ J)|_{padOpens σ G'}` — the pull-back
  summand by `pullback_pullback` along the square (ii), the slice summand by
  `comap_idealSheaf_of_isLocalDiffeomorph` + `idealSheaf_congr` along the preimage identity (ii),
  the sum stalkwise (`Ideal.map_sup`).
* (iv) `isPullbackOf_ambientTriple_padAlong_restrictPiece`: the triple of
  `(E.restrictPiece hV' hsub).padAlong σ` is the pull-back of the triple of `E.padAlong σ` along
  the inclusion of the padded shrunk ambient — (iii) at `E.ideal` through the definitional
  identities `padAlong_ideal`/`restrictPiece_ideal`, the empty family by
  `HypersurfaceFamily.empty_comap` (the two-line proof of
  `ambientTriple_restrictPiece_isPullbackOf`, with (iii) for `rfl`).

Not in the sources beyond the remarks cited; bookkeeping. The pull-back of a blow-up sequence
along an open immersion, with the empty blow-ups deleted, is the compatibility of
[Kol07, 34.1].
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n n' : ℕ} (σ : Fin n ↪ Fin n')

/-! ### (i) Monotonicity of the padding; the inclusion of ambients is an open embedding -/

/-- **Padding is monotone** in the open — `G' ≤ G` gives `padOpens σ G' ≤ padOpens σ G` (the
coordinate `z ∘ σ` of a point of the padded `G'` lies in `G' ⊆ G`). -/
theorem padOpens_mono {G' G : Opens (Fin n → 𝕜)} (h : G' ≤ G) : padOpens σ G' ≤ padOpens σ G :=
  fun _ hz => h hz

/-- **The inclusion `Sp(G') → Sp(G)` of one-piece ambients is an analytic open embedding** — a
local analytic isomorphism (`isLocalDiffeomorph_pieceAmbientIncl`) that is injective
(`pieceAmbientIncl_injective`). -/
theorem isAnalyticOpenEmbedding_pieceAmbientIncl {G' G : Opens (Fin n → 𝕜)} (h : G' ≤ G) :
    IsAnalyticOpenEmbedding (pieceAmbientIncl.{u} h) :=
  ⟨isLocalDiffeomorph_pieceAmbientIncl h, pieceAmbientIncl_injective h⟩

/-! ### (ii) The coordinate square and the slice -/

/-- **The coordinate projection commutes with the inclusions of ambients**, pointwise — both sides
are the point of `Sp(G)` with coordinate `z ∘ σ`. -/
theorem padCoordProj_pieceAmbientIncl {G' G : Opens (Fin n → 𝕜)} (h : G' ≤ G)
    (x : pieceAmbient.{u} 𝕜 (padOpens σ G')) :
    padCoordProj σ G (pieceAmbientIncl (padOpens_mono σ h) x) =
      pieceAmbientIncl h (padCoordProj σ G' x) :=
  Sigma.ext rfl (heq_of_eq (Subtype.ext rfl))

/-- **The coordinate square** `p_G ∘ ι = ι ∘ p_{G'}` — the coordinate projection `padCoordProj`
commutes with the inclusions `pieceAmbientIncl` of the padded and of the unpadded ambients. -/
theorem padCoordProj_comp_pieceAmbientIncl {G' G : Opens (Fin n → 𝕜)} (h : G' ≤ G) :
    padCoordProj.{u} σ G ∘ pieceAmbientIncl (padOpens_mono σ h) =
      pieceAmbientIncl h ∘ padCoordProj.{u} σ G' :=
  funext (padCoordProj_pieceAmbientIncl σ h)

/-- **The coordinate slice pulls back to the coordinate slice** along the inclusion of the padded
ambients — the inclusion keeps the coordinates, so the condition `z_j = 0` for `j ∉ range σ` is
unchanged. -/
theorem preimage_padSlice_pieceAmbientIncl {G' G : Opens (Fin n → 𝕜)} (h : G' ≤ G) :
    pieceAmbientIncl (padOpens_mono σ h) ⁻¹' padSlice.{u} σ G = padSlice.{u} σ G' :=
  Set.ext fun _ => Iff.rfl

/-- **The inclusion of the padded ambients carries zero extensions to zero extensions** —
`ι (s w) = s (ι w)` for the zero extension `s = padExt` and the inclusions `ι`; both sides are the
point of `Sp(padOpens σ G)` with coordinate `extend σ (coord w) 0`. Hence the padded restricted
piece's ambient point of `x` is the padded piece's ambient point of `x` (`ambientPoint_padAlong`
twice, `pieceAmbientIncl_ambientPoint_restrictPiece`, and this identity). -/
theorem pieceAmbientIncl_padExt {G' G : Opens (Fin n → 𝕜)} (h : G' ≤ G)
    (w : pieceAmbient.{u} 𝕜 G') :
    pieceAmbientIncl (padOpens_mono σ h) (padExt σ G' w) = padExt σ G (pieceAmbientIncl h w) :=
  Sigma.ext rfl (heq_of_eq (Subtype.ext rfl))

/-! ### (iii) The padded ideal of a restricted ideal -/

/-- **The padded ideal of a pulled-back ideal is the pull-back of the padded ideal**,
`padIdeal σ (ι^* J) = ι^* (padIdeal σ J)` for the inclusions `ι` of `G' ≤ G` and of the padded
opens — the pull-back summand `p^* J` by `pullback_pullback` twice along the coordinate square
(ii), the slice summand `𝓘_S` by `comap_idealSheaf_of_isLocalDiffeomorph` (the inclusion is a
local analytic isomorphism) and `idealSheaf_congr` along the preimage identity (ii), and the sum
stalkwise (`Ideal.map_sup`). -/
theorem padIdeal_comap {G' G : Opens (Fin n → 𝕜)} (h : G' ≤ G)
    (J : AnalyticManifold.IdealSheaf (pieceAmbient.{u} 𝕜 G)) :
    padIdeal σ (J.pullback _ (pieceAmbientIncl h).contMDiff) =
      (padIdeal σ J).pullback _ (pieceAmbientIncl (padOpens_mono σ h)).contMDiff := by
  -- the pull-back summand: two pull-backs compose, and the composites agree by the square (ii)
  have hpull :
      (J.pullback _ (pieceAmbientIncl h).contMDiff).pullback (padCoordProj σ G')
        (contMDiff_padCoordProj σ G') =
      (J.pullback (padCoordProj σ G) (contMDiff_padCoordProj σ G)).pullback _ (pieceAmbientIncl
          (padOpens_mono σ h)).contMDiff :=
    (IdealSheaf.pullback_pullback J _ _ _ _).trans
      ((IdealSheaf.pullback_congr J _ _ (padCoordProj_comp_pieceAmbientIncl σ h).symm).trans
        (IdealSheaf.pullback_pullback J _ _ _ _).symm)
  -- the slice summand: the ideal sheaf of the slice pulls back to the ideal sheaf of the preimage
  have hslice : (isClosedSubmanifold_padSlice σ G).idealSheaf.pullback _ (pieceAmbientIncl
      (padOpens_mono σ
      h)).contMDiff =
      (isClosedSubmanifold_padSlice σ G').idealSheaf :=
    (comap_idealSheaf_of_isLocalDiffeomorph _ _ (isLocalDiffeomorph_pieceAmbientIncl _)
      (isClosedSubmanifold_padSlice σ G)).trans
      (IsClosedSubmanifold.idealSheaf_congr _ _ (preimage_padSlice_pieceAmbientIncl σ h))
  -- the pull-back of the sum is the sum of the pull-backs, stalk by stalk
  have hadd :
      (padIdeal σ J).pullback _ (pieceAmbientIncl (padOpens_mono σ h)).contMDiff =
      (J.pullback (padCoordProj σ G) (contMDiff_padCoordProj σ G)).pullback _ (pieceAmbientIncl
          (padOpens_mono σ h)).contMDiff +
        (isClosedSubmanifold_padSlice σ G).idealSheaf.pullback _ (pieceAmbientIncl (padOpens_mono σ
            h)).contMDiff :=
    IdealSheaf.ext fun b => by
      simp only [padIdeal, IdealSheaf.stalkIdeal_pullback,
        IdealSheaf.stalkIdeal_add, Ideal.map_sup]
  rw [hadd, padIdeal, hpull, hslice]

/-! ### (iv) The padded restricted piece is a pull-back of the padded piece -/

variable {X : AnalyticSpace.{u} 𝕜} {V V' : Set X}

/-- **The padded restricted piece is a pull-back of the padded piece** ([Wlo09, §4, (3)⇒(4)]
with the padding of [Kol07, Theorem 36, proof]) — the triple
`(padOpens σ G', padIdeal σ 𝓘|_{G'}, ∅)` of `(E|V').padAlong σ` is the pull-back of the triple
`(padOpens σ G, padIdeal σ 𝓘, ∅)` of `E.padAlong σ` along the inclusion of the padded shrunk
ambient (an analytic open embedding, (i)): the ideal by (iii) at `𝓘 = E.ideal` through the
definitional identities `padAlong_ideal` and `restrictPiece_ideal`, the empty family by
`empty_comap`. -/
theorem isPullbackOf_ambientTriple_padAlong_restrictPiece (E : PieceEmbedding 𝕜 n X V)
    (hV' : IsOpen V') (hsub : V' ⊆ V) :
    ((E.restrictPiece hV' hsub).padAlong σ).ambientTriple.IsPullbackOf
      (E.padAlong σ).ambientTriple
      (pieceAmbientIncl (padOpens_mono σ (E.restrictAmbient_le hV'))) :=
  ⟨padIdeal_comap σ (E.restrictAmbient_le hV') E.ideal, (HypersurfaceFamily.empty_comap _).symm⟩

end Hironaka.Manifold

end
