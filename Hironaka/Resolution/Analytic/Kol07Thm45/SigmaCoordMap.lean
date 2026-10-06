/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceAmbientIncl
public import Hironaka.Manifold.SigmaManifold
public import Hironaka.Manifold.FiniteSuccession.Functor.SigmaDesc
import Hironaka.Manifold.FiniteSuccession.Functor.SigmaLocalDiffeo
import Hironaka.Manifold.FiniteSuccession.Functor.SigmaTriple
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceRestrict
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The summand-wise coordinate map `Θ₀ : ⊔ᵢ Gᵢ' → ⊔ᵢ Sp(Gᵢ)`

Kollár presents the local model as the disjoint union `X' = ⊔ᵢ Uᵢ` of the charts
[Kol07, Proposition 37, proof]. The library spells that disjoint union twice: the ambient
manifold of the local model of `exists_functorial_resolution` is a `sigmaOpens G'` (`Σ i, ↥(G' i)`,
the `Σ`-type of opens `G' i ⊆ 𝕜ⁿ`), while the order-reduction functor is applied on
`sigmaManifold (fun i => pieceAmbient 𝕜 (G i))` (`Σ i, Σ _ : PUnit, ↥(G i)`, the disjoint union of
the one-piece ambients `Sp(Gᵢ)`). Given relatively compact opens `Wᵢ ⊆ Sp(Gᵢ)` on which the functor
was applied, this module identifies the `sigmaOpens` of the coordinate images
`Gᵢ' := pieceCoord '' Wᵢ` with the open `U_Σ = ⋃ᵢ sigmaMk i '' Wᵢ` of the functor's ambient:

* `coordImageOpens G W`: the coordinate image `pieceCoord G '' W ⊆ 𝕜ⁿ` of an open `W ⊆ Sp(G)`, an
  open of `𝕜ⁿ` (`pieceCoord` is an open map — `isOpenMap_pieceCoord`, `PieceRestrict.lean`), with
  `mem_coordImageOpens` and `coordImageOpens_le`;
* `sigmaCoordMap G W`: **`Θ₀`**, the analytic map `⊔ᵢ Gᵢ' → ⊔ᵢ Sp(Gᵢ)`, `⟨i, z⟩ ↦ ⟨i, ⟨(), z⟩⟩`
  (`sigmaCoordMap_apply`); the summand square `sigmaCoordMap_mk_of_mem` (the point of `Gᵢ'` with
  the coordinates of `w ∈ Wᵢ` goes to `w`);
* `isAnalyticOpenEmbedding_sigmaCoordMap`: `Θ₀` is an analytic open embedding (a local analytic
  isomorphism, injective), by `IsLocalDiffeomorph.sigmaDesc` of the summand maps;
* `sigmaCoordImage G W`: its image `U_Σ` (Mathlib's `IsLocalDiffeomorph.image`), with
  `coe_sigmaCoordImage` (`= ⋃ᵢ sigmaMk i '' Wᵢ`) and `isCompact_closure_sigmaCoordImage` (a finite
  union of relatively compact opens).

Internal helpers: `pieceAmbientMkDiffeo G`, the diffeomorphism `↥G ≃ Sp(G)`, `z ↦ ⟨(), z⟩` (with
`pieceAmbientMkDiffeo_apply`); the summand map `sigmaCoordSummand G W i` with
`sigmaCoordSummand_apply`, `contMDiff_sigmaCoordSummand` and
`isLocalDiffeomorph_sigmaCoordSummand`; `sigmaCoordMap_injective`.

Not in the sources; bookkeeping: `Θ₀` is Kollár's identification `X' = ⊔ Uᵢ` read against the two
spellings of the disjoint union (compare [Kol07, Warning 38]). `Θ₀` is used in `AmbientEmb.lean`;
its image `U_Σ` (`sigmaCoordImage`) also in `CoproductSumData.lean`, `CoproductPadIdentity.lean`,
`CoproductPadIdentityPiece.lean`, `DoubledDatumLabels.lean` and
`Hironaka/Resolution/Analytic/Kol07Thm45/SigmaSubmanifold.lean`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

section CoordImage

/-- The one-piece ambient `Sp(G) = ⊔_{PUnit} G` is the open `G ⊆ 𝕜ⁿ` itself — the diffeomorphism
`↥G ≃ Sp(G)`, `z ↦ ⟨(), z⟩`, with inverse the second projection. Internal helper. -/
def pieceAmbientMkDiffeo (G : Opens (Fin n → 𝕜)) :
    Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) G (pieceAmbient.{u} 𝕜 G) ω where
  toFun z := ⟨PUnit.unit, z⟩
  invFun w := w.2
  left_inv _ := rfl
  right_inv _ := Sigma.ext (Subsingleton.elim _ _) (heq_of_eq rfl)
  contMDiff_toFun := ContMDiff.sigmaMk (I := 𝓘(𝕜, Fin n → 𝕜)) (n := ω)
    (M := fun _ : PUnit.{u + 1} => (G : Type)) PUnit.unit
  contMDiff_invFun := ContMDiff.sigmaDesc (I := 𝓘(𝕜, Fin n → 𝕜)) (J := 𝓘(𝕜, Fin n → 𝕜)) (n := ω)
    (M := fun _ : PUnit.{u + 1} => (G : Type)) (P := (G : Type)) (f := fun _ => id)
    fun _ => contMDiff_id

/-- The diffeomorphism `↥G ≃ Sp(G)` on points. -/
theorem pieceAmbientMkDiffeo_apply (G : Opens (Fin n → 𝕜)) (z : G) :
    pieceAmbientMkDiffeo.{u} G z = ⟨PUnit.unit, z⟩ := rfl

/-- The coordinate image `pieceCoord G '' W ⊆ 𝕜ⁿ` of an open `W` of the one-piece ambient
`Sp(G) = ⊔_{PUnit} G`, as an open of `𝕜ⁿ` (one of the opens `Uᵢ ⊆ 𝕜ⁿ` of the disjoint-union
presentation, [Kol07, Proposition 37, proof]): the summand `Gᵢ' := pieceCoord '' Wᵢ` over which the
functor's value on `Wᵢ` is read. -/
def coordImageOpens (G : Opens (Fin n → 𝕜)) (W : Opens (pieceAmbient.{u} 𝕜 G)) :
    Opens (Fin n → 𝕜) :=
  ⟨pieceCoord G '' (W : Set (pieceAmbient.{u} 𝕜 G)), isOpenMap_pieceCoord G _ W.isOpen⟩

/-- Membership in the coordinate image — a point of `W` with these coordinates. -/
theorem mem_coordImageOpens (G : Opens (Fin n → 𝕜)) (W : Opens (pieceAmbient.{u} 𝕜 G))
    (z : Fin n → 𝕜) : z ∈ coordImageOpens G W ↔ ∃ w ∈ W, pieceCoord G w = z := Iff.rfl

/-- The coordinate image lies in `G` — the coordinates of a point of `Sp(G)` lie in `G`
(`pieceCoord_mem`). -/
theorem coordImageOpens_le (G : Opens (Fin n → 𝕜)) (W : Opens (pieceAmbient.{u} 𝕜 G)) :
    coordImageOpens G W ≤ G := by
  rintro _ ⟨w, -, rfl⟩
  exact pieceCoord_mem G w

end CoordImage

section Theta

variable {ι : Type u} [Finite ι] (G : ι → Opens (Fin n → 𝕜))
  (W : ∀ i, Opens (pieceAmbient.{u} 𝕜 (G i)))

/-- The `i`-th summand map of `Θ₀`, `Gᵢ' → ⊔ⱼ Sp(Gⱼ)`, `z ↦ ⟨i, ⟨(), z⟩⟩` — the diffeomorphism
`↥Gᵢ' ≃ Sp(Gᵢ')`, the inclusion `Sp(Gᵢ') → Sp(Gᵢ)` of one-piece ambients (`pieceAmbientIncl`,
`Gᵢ' ≤ Gᵢ`), then the summand inclusion `sigmaMk i`. Internal helper. -/
def sigmaCoordSummand (i : ι) (z : coordImageOpens (G i) (W i)) :
    sigmaManifold fun i => pieceAmbient.{u} 𝕜 (G i) :=
  sigmaMk (fun i => pieceAmbient.{u} 𝕜 (G i)) i
    (pieceAmbientIncl (coordImageOpens_le (G i) (W i))
      (pieceAmbientMkDiffeo.{u} (coordImageOpens (G i) (W i)) z))

/-- The summand map on points. -/
theorem sigmaCoordSummand_apply (i : ι) (z : coordImageOpens (G i) (W i)) :
    sigmaCoordSummand G W i z =
      sigmaMk (fun i => pieceAmbient.{u} 𝕜 (G i)) i
        ⟨PUnit.unit, ⟨z.1, coordImageOpens_le (G i) (W i) z.2⟩⟩ := rfl

/-- The summand map is analytic — a composite of analytic maps. -/
theorem contMDiff_sigmaCoordSummand (i : ι) :
    ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (sigmaCoordSummand G W i) :=
  (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (G i)) i).contMDiff.comp
    ((pieceAmbientIncl (coordImageOpens_le (G i) (W i))).contMDiff.comp
      (pieceAmbientMkDiffeo.{u} (coordImageOpens (G i) (W i))).contMDiff)

/-- The summand map is a local analytic isomorphism — a diffeomorphism, then the inclusion of
one-piece ambients (`isLocalDiffeomorph_pieceAmbientIncl`), then the summand inclusion
(`isLocalDiffeomorph_sigmaMk`), composed pointwise (`IsLocalDiffeomorphAt.comp`). -/
theorem isLocalDiffeomorph_sigmaCoordSummand (i : ι) :
    IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (sigmaCoordSummand G W i) := fun z =>
  IsLocalDiffeomorphAt.comp
    (hf := IsLocalDiffeomorphAt.comp
      (hf := (pieceAmbientMkDiffeo.{u} (coordImageOpens (G i) (W i))).isLocalDiffeomorph z)
      (hg := isLocalDiffeomorph_pieceAmbientIncl (coordImageOpens_le (G i) (W i)) _))
    (hg := isLocalDiffeomorph_sigmaMk (fun i => pieceAmbient.{u} 𝕜 (G i)) i _)

/-- **`Θ₀`, the summand-wise coordinate map** `⊔ᵢ Gᵢ' → ⊔ᵢ Sp(Gᵢ)`, `⟨i, z⟩ ↦ ⟨i, ⟨(), z⟩⟩` —
from the `sigmaOpens` of the coordinate images `Gᵢ' = pieceCoord '' Wᵢ` into the disjoint union of
the one-piece ambients: Kollár's identification `X' = ⊔ Uᵢ` [Kol07, Proposition 37, proof] read
against the two spellings of the disjoint union. Analytic by `ContMDiff.sigmaDesc` of the summand
maps. -/
def sigmaCoordMap : AnalyticMap
    (AnalyticManifold.sigmaOpens fun i => coordImageOpens (G i) (W i))
    (sigmaManifold fun i => pieceAmbient.{u} 𝕜 (G i)) :=
  ⟨fun p => sigmaCoordSummand G W p.1 p.2,
    ContMDiff.sigmaDesc (I := 𝓘(𝕜, Fin n → 𝕜)) (J := 𝓘(𝕜, Fin n → 𝕜)) (n := ω)
      (M := fun i => (coordImageOpens (G i) (W i) : Type)) (f := sigmaCoordSummand G W)
      (contMDiff_sigmaCoordSummand G W)⟩

/-- `Θ₀` on points, `⟨i, z⟩ ↦ ⟨i, ⟨(), z⟩⟩` (the coordinates of `z` read in `Gᵢ`,
`coordImageOpens_le`). -/
theorem sigmaCoordMap_apply (i : ι) (z : coordImageOpens (G i) (W i)) :
    sigmaCoordMap G W ⟨i, z⟩ =
      sigmaMk (fun i => pieceAmbient.{u} 𝕜 (G i)) i
        ⟨PUnit.unit, ⟨z.1, coordImageOpens_le (G i) (W i) z.2⟩⟩ := rfl

/-- The summand square: the point of `Gᵢ'` with the coordinates of `w ∈ Wᵢ` goes to `w` — a point
of `Sp(Gᵢ)` is determined by its coordinates (`Sigma.ext`, `Subtype.ext`). -/
theorem sigmaCoordMap_mk_of_mem (i : ι) (w : pieceAmbient.{u} 𝕜 (G i)) (hw : w ∈ W i) :
    sigmaCoordMap G W
        ⟨i, ⟨pieceCoord (G i) w, (mem_coordImageOpens (G i) (W i) _).mpr ⟨w, hw, rfl⟩⟩⟩ =
      sigmaMk (fun i => pieceAmbient.{u} 𝕜 (G i)) i w := by
  rw [sigmaCoordMap_apply]
  exact congrArg _ (Sigma.ext (Subsingleton.elim _ _) (heq_of_eq (Subtype.ext rfl)))

/-- `Θ₀` is injective — equal images have the same summand (`congrArg Sigma.fst`) and, in that
summand (`sigma_mk_injective`), the same coordinates (`pieceCoord`). Internal helper. -/
theorem sigmaCoordMap_injective : Function.Injective (sigmaCoordMap G W) := by
  rintro ⟨i, z⟩ ⟨j, z'⟩ h
  have hij : i = j := congrArg Sigma.fst h
  subst hij
  have h2 : (⟨PUnit.unit, ⟨z.1, coordImageOpens_le (G i) (W i) z.2⟩⟩ : pieceAmbient.{u} 𝕜 (G i)) =
      ⟨PUnit.unit, ⟨z'.1, coordImageOpens_le (G i) (W i) z'.2⟩⟩ :=
    sigma_mk_injective (β := fun j => (pieceAmbient.{u} 𝕜 (G j) : Type u)) (i := i) h
  exact congrArg (Sigma.mk i) (Subtype.ext (congrArg (pieceCoord (G i)) h2))

/-- `Θ₀` is an analytic open embedding (a local analytic isomorphism, injective): the coproduct of
the local analytic isomorphisms of the summands (`IsLocalDiffeomorph.sigmaDesc`) and
`sigmaCoordMap_injective`. -/
theorem isAnalyticOpenEmbedding_sigmaCoordMap : IsAnalyticOpenEmbedding (sigmaCoordMap G W) :=
  ⟨IsLocalDiffeomorph.sigmaDesc (I := 𝓘(𝕜, Fin n → 𝕜)) (J := 𝓘(𝕜, Fin n → 𝕜)) (n := ω)
    (M := fun i => (coordImageOpens (G i) (W i) : Type)) (f := sigmaCoordSummand G W)
    (isLocalDiffeomorph_sigmaCoordSummand G W), sigmaCoordMap_injective G W⟩

/-- `U_Σ`, the image of `Θ₀` (Mathlib's `IsLocalDiffeomorph.image`, `⟨range Θ₀, _⟩`) — the open
of `⊔ᵢ Sp(Gᵢ)` on which the data of the local model live. -/
def sigmaCoordImage : Opens (sigmaManifold fun i => pieceAmbient.{u} 𝕜 (G i)) :=
  (isAnalyticOpenEmbedding_sigmaCoordMap G W).1.image

/-- `U_Σ = ⋃ᵢ sigmaMk i '' Wᵢ` — a point of the range of `Θ₀` is `sigmaMk i w` for the `w ∈ Wᵢ`
with its coordinates (`mem_coordImageOpens`), and conversely by the summand square
`sigmaCoordMap_mk_of_mem`. -/
theorem coe_sigmaCoordImage :
    (sigmaCoordImage G W : Set (sigmaManifold fun i => pieceAmbient.{u} 𝕜 (G i))) =
      ⋃ i, ⇑(sigmaMk (fun i => pieceAmbient.{u} 𝕜 (G i)) i) ''
        (W i : Set (pieceAmbient.{u} 𝕜 (G i))) := by
  ext p
  change p ∈ Set.range (sigmaCoordMap G W) ↔ _
  simp only [Set.mem_range, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨⟨i, z⟩, rfl⟩
    obtain ⟨w, hw, hwz⟩ := (mem_coordImageOpens (G i) (W i) z).mp z.2
    exact ⟨i, w, hw, (sigmaCoordMap_mk_of_mem G W i w hw).symm.trans
      (congrArg (sigmaCoordMap G W) (congrArg (Sigma.mk i) (Subtype.ext hwz)))⟩
  · rintro ⟨i, w, hw, rfl⟩
    exact ⟨⟨i, ⟨pieceCoord (G i) w, (mem_coordImageOpens (G i) (W i) _).mpr ⟨w, hw, rfl⟩⟩⟩,
      sigmaCoordMap_mk_of_mem G W i w hw⟩

/-- `U_Σ` is relatively compact when the `Wᵢ` are — a FINITE union (`closure_iUnion_of_finite`,
`isCompact_iUnion`) of the images of relatively compact opens under the analytic maps `sigmaMk i`
(`AnalyticMap.isCompact_closure_image`). -/
theorem isCompact_closure_sigmaCoordImage
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (G i))))) :
    IsCompact
      (closure (sigmaCoordImage G W : Set (sigmaManifold fun i => pieceAmbient.{u} 𝕜 (G i)))) := by
  rw [coe_sigmaCoordImage, closure_iUnion_of_finite]
  exact isCompact_iUnion fun i =>
    AnalyticMap.isCompact_closure_image (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (G i)) i) (hW i)

end Theta

end Hironaka.Manifold

end
