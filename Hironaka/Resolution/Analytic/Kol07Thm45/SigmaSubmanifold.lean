/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.CoverData
public import Hironaka.Resolution.Analytic.Functor.SigmaIdealSheaf
public import Hironaka.Resolution.Analytic.Kol07Thm45.SigmaCoordMap
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.FiniteSuccession.Functor.LocalTriples
import Hironaka.Manifold.FiniteSuccession.Functor.PushforwardPullback
import Hironaka.Manifold.FiniteSuccession.Functor.SigmaLocalDiffeo
import Hironaka.Manifold.Submanifold.DisjointUnion
import Hironaka.Resolution.Analytic.Kol07Thm45.ExceptionalFamilyGlue
import Hironaka.Resolution.Analytic.Submanifold.FlagIdeal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Closed submanifolds of a coproduct manifold

Given closed submanifolds `S i ⊆ N i` of codimension `s` of countably many analytic manifolds
modelled on `E`, the union of their images under the summand inclusions `sigmaMk N i` is a closed
submanifold `S* ⊆ sigmaManifold N` of codimension `s`, and the coproduct of the bundled
submanifolds is the bundled submanifold `S*`. Not in the sources: bookkeeping for the comparison
of resolutions along a closed embedding of a coproduct (cf. [Kol07, 34.4]).

* `preimage_sigmaMk_iUnion_image`: `sigmaMk N i ⁻¹' (⋃ j, sigmaMk N j '' Y j) = Y i` — the summand
  images are disjoint and `sigmaMk N i` is injective (the identity behind every clause below);
* `isClosedSubmanifold_sigmaUnion`: `S*` is a closed submanifold, the instance of
  `IsClosedSubmanifold.iUnion_image` at the summand inclusions;
* `sigmaSubmanifoldIncl` (the summand inclusion of the bundled `S i` into the bundled `S*`,
  `IsClosedSubmanifold.restrictMap` along `sigmaMk N i`), a local diffeomorphism;
  `sigmaSubmanifoldDesc` (their descent, `sigmaDescMap`), bijective; `sigmaSubmanifoldDiffeomorph`
  (`IsLocalDiffeomorph.toDiffeomorphOfBijective`), with the two compatibilities
  `inclusionMap_sigmaSubmanifoldDiffeomorph_mk` (with the inclusion maps) and
  `sigmaSubmanifoldDiffeomorph_comp_sigmaMk` (with the summand inclusions);
* `idealSheaf_sigmaUnion`: the ideal sheaf of `S*` is the coproduct ideal sheaf
  `IdealSheaf.sigmaOf N (fun i => (hS i).idealSheaf)`;
* `preimage_sigmaSubmanifoldDiffeomorph_preimageOpens`: the preimage under the diffeomorphism of
  `preimageOpens U` on `S*` is the union of the summand images of the pieces' `preimageOpens` of
  the preimages of `U` along `sigmaMk N i`; and `preimageOpens_sigmaMk_sigmaCoordImage`:
  `sigmaMk i ⁻¹' sigmaCoordImage G W = W i` as `Opens`;
* `sigmaMapDiffeomorph`: the coproduct of a family of diffeomorphisms `e i : M i ≅ N i` (one pair
  of models `E`, `E'`) is a diffeomorphism `sigmaManifold M ≅ sigmaManifold N` with
  `sigmaMapDiffeomorph e (sigmaMk M i x) = sigmaMk N i (e i x)`.

Everything here is at the level of manifolds; no blow-up sequence enters. It is used to compare
the resolution of a disjoint union of pieces with the disjoint union of their resolutions
(`Hironaka/Resolution/Analytic/Kol07Thm45/CoproductPadIdentity.lean`).
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set Topology

open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### Preimages along the summand inclusions -/

section Preimage

variable {σ : Type u} [Countable σ] (N : σ → AnalyticManifold.{u} 𝕜 E)

/-- The preimage under the summand inclusion `sigmaMk N i` of a union of summand images is the
`i`-th set: the summand images are pairwise disjoint (`pairwise_disjoint_range_sigmaMk`) and
`sigmaMk N i` is injective. -/
theorem preimage_sigmaMk_iUnion_image (Y : ∀ i, Set (N i)) (i : σ) :
    ⇑(sigmaMk N i) ⁻¹' (⋃ j, ⇑(sigmaMk N j) '' Y j) = Y i := by
  ext x
  refine ⟨fun hx => ?_, fun hx => mem_iUnion.2 ⟨i, mem_image_of_mem _ hx⟩⟩
  have hx' : sigmaMk N i x ∈ (⋃ j, ⇑(sigmaMk N j) '' Y j) ∩ range ⇑(sigmaMk N i) :=
    ⟨hx, mem_range_self x⟩
  rw [iUnion_image_inter_range (sigmaMk N) (isAnalyticOpenEmbedding_sigmaMk N)
    (pairwise_disjoint_range_sigmaMk N) Y i] at hx'
  obtain ⟨y, hy, hyx⟩ := hx'
  exact (isAnalyticOpenEmbedding_sigmaMk N i).2 hyx ▸ hy

/-- The summand inclusion maps `Y i` into the union of the summand images. -/
theorem sigmaMk_mem_iUnion_image (Y : ∀ i, Set (N i)) (i : σ) :
    ∀ x ∈ Y i, sigmaMk N i x ∈ ⋃ j, ⇑(sigmaMk N j) '' Y j :=
  fun _ hx => mem_iUnion.2 ⟨i, mem_image_of_mem _ hx⟩

end Preimage

/-! ### The restricted map along a local diffeomorphism, for an equal preimage -/

section RestrictMapOfEq

variable {A B : AnalyticManifold.{u} 𝕜 E}

/-- `IsClosedSubmanifold.isLocalDiffeomorph_restrictMap` for a closed submanifold `S'` equal to
the preimage `h ⁻¹' S` (not syntactically the preimage): the restriction of the local analytic
isomorphism `h` to `S' → S` is a local analytic isomorphism of the bundled submanifolds. -/
theorem _root_.Manifold.IsClosedSubmanifold.isLocalDiffeomorph_restrictMap_of_eq
    (h : AnalyticMap B A)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {S : Set A} {S' : Set B} {s : ℕ}
    (hS : IsClosedSubmanifold ψ S s) (hS' : IsClosedSubmanifold ψ S' s) (heq : S' = ⇑h ⁻¹' S)
    (hmaps : ∀ x ∈ S', h x ∈ S) :
    IsLocalDiffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) ω
      (hS'.restrictMap hS h h.contMDiff hmaps) := by
  subst heq
  exact IsClosedSubmanifold.isLocalDiffeomorph_restrictMap h hh hS

end RestrictMapOfEq

/-! ### The coproduct slice -/

section Slice

variable {σ : Type u} [Countable σ] {N : σ → AnalyticManifold.{u} 𝕜 E} {S : ∀ i, Set (N i)}
  {s : ℕ} (hS : ∀ i, IsClosedSubmanifold ψ (S i) s)

include hS in
/-- The union of the summand images of closed submanifolds of codimension `s` is a closed
submanifold of the coproduct of codimension `s`: `IsClosedSubmanifold.iUnion_image` at the
summand inclusions. -/
theorem isClosedSubmanifold_sigmaUnion :
    IsClosedSubmanifold ψ (⋃ i, ⇑(sigmaMk N i) '' S i) s :=
  IsClosedSubmanifold.iUnion_image (sigmaMk N) (isAnalyticOpenEmbedding_sigmaMk N)
    (pairwise_disjoint_range_sigmaMk N) (iUnion_range_sigmaMk N) S hS

/-- The summand inclusion of the coproduct slice: the restriction of `sigmaMk N i` to the bundled
submanifolds (`IsClosedSubmanifold.restrictMap`). -/
def sigmaSubmanifoldIncl (i : σ) :
    AnalyticMap (hS i).toAnalyticManifold (isClosedSubmanifold_sigmaUnion hS).toAnalyticManifold :=
  (hS i).restrictMap (isClosedSubmanifold_sigmaUnion hS) (sigmaMk N i) (sigmaMk N i).contMDiff
    (sigmaMk_mem_iUnion_image N S i)

/-- The summand inclusion of the slice commutes with the inclusion maps. -/
theorem inclusionMap_sigmaSubmanifoldIncl (i : σ) (p : (hS i).toAnalyticManifold) :
    (isClosedSubmanifold_sigmaUnion hS).inclusionMap (sigmaSubmanifoldIncl hS i p) =
      sigmaMk N i ((hS i).inclusionMap p) := by
  rw [IsClosedSubmanifold.inclusionMap_apply, IsClosedSubmanifold.inclusionMap_apply]
  exact (hS i).restrictMap_apply (isClosedSubmanifold_sigmaUnion hS) (sigmaMk N i)
    (sigmaMk N i).contMDiff (sigmaMk_mem_iUnion_image N S i) p

/-- The summand inclusion of the slice is a local analytic isomorphism
(`isLocalDiffeomorph_restrictMap_of_eq` at `sigmaMk N i`, whose preimage of the slice is `S i`). -/
theorem isLocalDiffeomorph_sigmaSubmanifoldIncl (i : σ) :
    IsLocalDiffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) ω
      (sigmaSubmanifoldIncl hS i) :=
  IsClosedSubmanifold.isLocalDiffeomorph_restrictMap_of_eq (sigmaMk N i)
    (isLocalDiffeomorph_sigmaMk N i) (isClosedSubmanifold_sigmaUnion hS) (hS i)
    (preimage_sigmaMk_iUnion_image N S i).symm _

/-- The descent of the summand inclusions, `∐ᵢ Sᵢ → S*`. -/
def sigmaSubmanifoldDesc :
    AnalyticMap (sigmaManifold fun i => (hS i).toAnalyticManifold)
      (isClosedSubmanifold_sigmaUnion hS).toAnalyticManifold :=
  sigmaDescMap fun i => sigmaSubmanifoldIncl hS i

/-- The descent on the `i`-th summand is the `i`-th inclusion. -/
theorem sigmaSubmanifoldDesc_mk (i : σ) (p : (hS i).toAnalyticManifold) :
    sigmaSubmanifoldDesc hS (sigmaMk (fun i => (hS i).toAnalyticManifold) i p) =
      sigmaSubmanifoldIncl hS i p :=
  rfl

/-- The descent of the summand inclusions is a local diffeomorphism (each inclusion is one). -/
theorem isLocalDiffeomorph_sigmaSubmanifoldDesc :
    IsLocalDiffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) ω
      (sigmaSubmanifoldDesc hS) :=
  isLocalDiffeomorph_sigmaDescMap _ (isLocalDiffeomorph_sigmaSubmanifoldIncl hS)

/-- The descent is bijective: injective since the summand images are disjoint and each summand
inclusion is injective, surjective since every point of the slice lies in some summand image. -/
theorem bijective_sigmaSubmanifoldDesc : Function.Bijective (sigmaSubmanifoldDesc hS) := by
  constructor
  · rintro ⟨i, p⟩ ⟨j, q⟩ h
    have h1 : (isClosedSubmanifold_sigmaUnion hS).inclusionMap (sigmaSubmanifoldIncl hS i p) =
        (isClosedSubmanifold_sigmaUnion hS).inclusionMap (sigmaSubmanifoldIncl hS j q) :=
      congrArg (isClosedSubmanifold_sigmaUnion hS).inclusionMap h
    rw [inclusionMap_sigmaSubmanifoldIncl, inclusionMap_sigmaSubmanifoldIncl, sigmaMk_apply,
      sigmaMk_apply] at h1
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h1
    have h3 := eq_of_heq h2
    rw [IsClosedSubmanifold.inclusionMap_apply, IsClosedSubmanifold.inclusionMap_apply] at h3
    exact congrArg (Sigma.mk i) (Subtype.ext h3)
  · rintro ⟨⟨i, x⟩, hx⟩
    have hxi : x ∈ S i := by
      rw [← preimage_sigmaMk_iUnion_image N S i]; exact hx
    exact ⟨⟨i, ⟨x, hxi⟩⟩, Subtype.ext ((hS i).restrictMap_apply (isClosedSubmanifold_sigmaUnion hS)
      (sigmaMk N i) (sigmaMk N i).contMDiff (sigmaMk_mem_iUnion_image N S i) ⟨x, hxi⟩)⟩

/-- The coproduct of the bundled submanifolds is analytically isomorphic to the bundled slice
(`IsLocalDiffeomorph.toDiffeomorphOfBijective`). -/
def sigmaSubmanifoldDiffeomorph :
    Diffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜)
      (sigmaManifold fun i => (hS i).toAnalyticManifold)
      (isClosedSubmanifold_sigmaUnion hS).toAnalyticManifold ω :=
  (isLocalDiffeomorph_sigmaSubmanifoldDesc hS).toDiffeomorphOfBijective
    (bijective_sigmaSubmanifoldDesc hS)

/-- The diffeomorphism's underlying map is the descent `sigmaSubmanifoldDesc`. -/
theorem coe_sigmaSubmanifoldDiffeomorph :
    ⇑(sigmaSubmanifoldDiffeomorph hS) = ⇑(sigmaSubmanifoldDesc hS) :=
  rfl

theorem sigmaSubmanifoldDiffeomorph_mk (i : σ) (p : (hS i).toAnalyticManifold) :
    sigmaSubmanifoldDiffeomorph hS (sigmaMk (fun i => (hS i).toAnalyticManifold) i p) =
      sigmaSubmanifoldIncl hS i p :=
  rfl

/-- The isomorphism commutes with the inclusion maps:
`hS*.inclusionMap (Φ ⟨i, p⟩) = sigmaMk N i ((hS i).inclusionMap p)`. -/
theorem inclusionMap_sigmaSubmanifoldDiffeomorph_mk (i : σ) (p : (hS i).toAnalyticManifold) :
    (isClosedSubmanifold_sigmaUnion hS).inclusionMap
        (sigmaSubmanifoldDiffeomorph hS (sigmaMk (fun i => (hS i).toAnalyticManifold) i p)) =
      sigmaMk N i ((hS i).inclusionMap p) :=
  inclusionMap_sigmaSubmanifoldIncl hS i p

/-- The isomorphism composed with the `i`-th summand inclusion of the coproduct is the `i`-th
summand inclusion of the slice. -/
theorem sigmaSubmanifoldDiffeomorph_comp_sigmaMk (i : σ) :
    ⇑(sigmaSubmanifoldDiffeomorph hS) ∘ ⇑(sigmaMk (fun i => (hS i).toAnalyticManifold) i) =
      ⇑(sigmaSubmanifoldIncl hS i) :=
  rfl

/-- The ideal sheaf of the slice is the coproduct ideal sheaf of the pieces'
(`IdealSheaf.ext_of_comap_sigmaMk`; per summand `comap_sigmaMk_sigmaOf`,
`idealSheaf_preimage_of_isLocalDiffeomorph` at `sigmaMk N i` and `idealSheaf_congr` on
`preimage_sigmaMk_iUnion_image`). -/
theorem idealSheaf_sigmaUnion :
    (isClosedSubmanifold_sigmaUnion hS).idealSheaf =
      IdealSheaf.sigmaOf N fun i => (hS i).idealSheaf := by
  refine IdealSheaf.ext_of_comap_sigmaMk N _ _ fun i => ?_
  rw [IdealSheaf.comap_sigmaMk_sigmaOf]
  exact ((isClosedSubmanifold_sigmaUnion hS).idealSheaf_preimage_of_isLocalDiffeomorph
    (sigmaMk N i) (isLocalDiffeomorph_sigmaMk N i)).symm.trans
    (IsClosedSubmanifold.idealSheaf_congr _ (hS i) (preimage_sigmaMk_iUnion_image N S i))

/-- The preimage under the isomorphism of the slice's reading of an open `U` of the coproduct is
the union of the summand images of the pieces' readings of the preimages of `U` along the summand
inclusions. -/
theorem preimage_sigmaSubmanifoldDiffeomorph_preimageOpens (U : Opens (sigmaManifold N)) :
    ⇑(sigmaSubmanifoldDiffeomorph hS) ⁻¹'
        ((isClosedSubmanifold_sigmaUnion hS).preimageOpens U :
          Set (isClosedSubmanifold_sigmaUnion hS).toAnalyticManifold) =
      ⋃ i, ⇑(sigmaMk (fun i => (hS i).toAnalyticManifold) i) ''
        ((hS i).preimageOpens (preimageOpens (sigmaMk N i) (sigmaMk N i).contMDiff U) :
          Set (hS i).toAnalyticManifold) := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, q⟩ := x
    refine mem_iUnion.2 ⟨j, mem_image_of_mem _ ?_⟩
    have hx' : (isClosedSubmanifold_sigmaUnion hS).inclusionMap
        (sigmaSubmanifoldDiffeomorph hS (sigmaMk (fun i => (hS i).toAnalyticManifold) j q)) ∈ U :=
      hx
    rw [inclusionMap_sigmaSubmanifoldDiffeomorph_mk] at hx'
    exact hx'
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    obtain ⟨q, hq, rfl⟩ := hj
    change (isClosedSubmanifold_sigmaUnion hS).inclusionMap
      (sigmaSubmanifoldDiffeomorph hS (sigmaMk (fun i => (hS i).toAnalyticManifold) j q)) ∈ U
    rw [inclusionMap_sigmaSubmanifoldDiffeomorph_mk]
    exact hq

end Slice

/-! ### The coordinate image read on a summand -/

section CoordImage

/-- The preimage along the `i`-th summand inclusion of `sigmaCoordImage G W = ⋃ⱼ sigmaMk j '' W j`
is `W i`, as `Opens` (`coe_sigmaCoordImage`, `preimage_sigmaMk_iUnion_image`). -/
theorem preimageOpens_sigmaMk_sigmaCoordImage {ι : Type u} [Finite ι] (G : ι → Opens (Fin n → 𝕜))
    (W : ∀ i, Opens (pieceAmbient.{u} 𝕜 (G i))) (i : ι) :
    preimageOpens (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (G i)) i)
        (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (G i)) i).contMDiff (sigmaCoordImage G W) = W i := by
  apply Opens.ext
  change ⇑(sigmaMk (fun i => pieceAmbient.{u} 𝕜 (G i)) i) ⁻¹'
    (sigmaCoordImage G W : Set (sigmaManifold fun i => pieceAmbient.{u} 𝕜 (G i))) = (W i : Set _)
  rw [coe_sigmaCoordImage]
  exact preimage_sigmaMk_iUnion_image (fun i => pieceAmbient.{u} 𝕜 (G i))
    (fun i => (W i : Set (pieceAmbient.{u} 𝕜 (G i)))) i

end CoordImage

/-! ### The coproduct of a family of diffeomorphisms -/

section Map

variable {σ : Type u} [Countable σ] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {M : σ → AnalyticManifold.{u} 𝕜 E} {N : σ → AnalyticManifold.{u} 𝕜 E'}
  (e : ∀ i, Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') (M i) (N i) ω)

/-- The summand-wise map of a family of diffeomorphisms is a local analytic isomorphism of the
coproducts (`IsLocalDiffeomorph.sigmaDesc` of the compositions `sigmaMk N i ∘ e i`). -/
theorem isLocalDiffeomorph_sigmaMapFun :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') ω
      (fun p : sigmaManifold M => sigmaMk N p.1 (e p.1 p.2)) :=
  IsLocalDiffeomorph.sigmaDesc (M := fun i => (M i : Type u)) (f := fun i x => sigmaMk N i (e i x))
    fun i x => ((e i).isLocalDiffeomorph x).comp (K := 𝓘(𝕜, E')) (P := (sigmaManifold N : Type u))
      (isLocalDiffeomorph_sigmaMk N i (e i x))

/-- The summand-wise map of a family of diffeomorphisms is bijective. -/
theorem bijective_sigmaMapFun :
    Function.Bijective (fun p : sigmaManifold M => sigmaMk N p.1 (e p.1 p.2)) := by
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ h
    have h1 : (Sigma.mk i (e i x) : Σ k, (N k : Type u)) = Sigma.mk j (e j y) := h
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h1
    have h3 := congrArg (e i).symm (eq_of_heq h2)
    rw [(e i).symm_apply_apply, (e i).symm_apply_apply] at h3
    exact congrArg (Sigma.mk i) h3
  · rintro ⟨i, y⟩
    exact ⟨⟨i, (e i).symm y⟩, congrArg (Sigma.mk i) ((e i).apply_symm_apply y)⟩

/-- The coproduct of a family of diffeomorphisms `e i : M i ≅ N i` (one pair of models `E`, `E'`)
as a diffeomorphism of the coproducts, with `sigmaMapDiffeomorph e (sigmaMk M i x) = sigmaMk N i
(e i x)` by `rfl`. -/
def sigmaMapDiffeomorph :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') (sigmaManifold M) (sigmaManifold N) ω :=
  (isLocalDiffeomorph_sigmaMapFun e).toDiffeomorphOfBijective (bijective_sigmaMapFun e)

theorem sigmaMapDiffeomorph_mk (i : σ) (x : M i) :
    sigmaMapDiffeomorph e (sigmaMk M i x) = sigmaMk N i (e i x) :=
  rfl

end Map

end Hironaka.Manifold

end
