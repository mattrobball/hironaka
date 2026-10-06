/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Manifold.Defs
public import Hironaka.Manifold.SigmaManifold
public import Hironaka.AnalyticSpace.Sigma
import Hironaka.AnalyticSpace.SigmaLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The space of a disjoint union of manifolds is the coproduct

The functor `Sp` sends the disjoint union `Σ i, M i` of a countable family of analytic manifolds
(the bundled manifold `sigmaManifold M`, `Hironaka.Manifold.SigmaManifold`) to the coproduct
`AnalyticSpace.sigma (fun i => Sp(M i))` of analytic spaces, compatibly with the inclusions of the
summands.

* `contMDiffAt_sigmaMk_comp_iff`: a map into a summand is `C^n` iff its composite with the inclusion
  `Sigma.mk i` into the disjoint union is: in the lifted charts of the disjoint union
  (`ChartedSpace.sigma_chartAt`) the inclusion reads as the identity, so both sides unfold to the
  same `ContDiffWithinAt` (the family version of Mathlib's `ContMDiff.inl`, in both directions).
* `isOpenImmersion_ofManifoldHom_sigmaMk`: `Sp(Sigma.mk i)` is an open immersion: the base map is
  the open embedding `Sigma.mk i`, and an analytic function on an open subset of the image of `M i`
  is the same as an analytic function on the corresponding open subset of `M i` (the argument of
  `isOpenImmersion_ofManifoldHom_val` for open submanifolds, with the lemma above in place of
  Mathlib's `liftPropWithinAt_subtypeVal_comp_iff`).
* `toSpaceSigmaIso ψ M : Sp(Σ i, M i) ≅ ∐ i, Sp(M i)`: the inverse of the descent
  `sigmaDesc (fun i => Sp(Sigma.mk i))`, an isomorphism by `isIso_sigmaDesc_of_isOpenImmersion`
  because the `Sp(Sigma.mk i)` are open immersions with pairwise disjoint images covering
  `Sp(Σ i, M i)`; it is compatible with the injections
  (`toSpaceHom_sigmaMk_comp_toSpaceSigmaIso_hom`, and on points `toFun_toSpaceSigmaIso_hom_mk`).

A non-singular analytic space is the disjoint union of its pure-dimensional strata, each the space
of a manifold [Hir64, Ch. 0, §1, p. 121]; this module and
`Hironaka.AnalyticSpace.Manifold.SigmaStratum` make the two descriptions of such a space, as one
manifold whose components may have different dimensions and as a coproduct of spaces,
interchangeable. The isomorphism `toSpaceSigmaIso` is used in
`Hironaka.AnalyticSpace.SigmaCoproductLemmas`; the analyticity criterion
`contMDiff_sigmaMk_comp_iff` and the chart formula `extChartAt_sigma_mk` are used for the resolution
functor on a disjoint union (`Hironaka.Manifold.FiniteSuccession.Functor.SigmaDesc`,
`Hironaka.Manifold.FiniteSuccession.Functor.SigmaTriple`) and in the gluing of local resolutions
(`Hironaka.Resolution.Analytic.Kol07Thm45.PadIdeal`,
`Hironaka.Resolution.Analytic.Kol07Thm45.PieceAmbientIncl`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Set
open Manifold
open scoped Manifold ContDiff Topology

universe u

/-! ### Analyticity through the inclusion of a summand -/

section ContMDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} {n : WithTop ℕ∞}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]

/-- The extended chart of the disjoint union at a point of the `i`-th summand, evaluated on that
summand, is the extended chart of the summand. -/
theorem extChartAt_sigma_mk [Nonempty H] {i : ι} (x y : M i) :
    extChartAt I (⟨i, x⟩ : Σ j, M j) ⟨i, y⟩ = extChartAt I x y := by
  change I (chartAt H (⟨i, x⟩ : Σ j, M j) ⟨i, y⟩) = I (chartAt H x y)
  rw [ChartedSpace.sigma_chartAt]
  exact congrArg I (OpenPartialHomeomorph.lift_openEmbedding_apply _ _)

/-- A map into a summand is `C^n` at a point iff its composite with the inclusion into the disjoint
union is: in the lifted charts the inclusion is the identity (the family version of Mathlib's
`ContMDiff.inl`, in both directions). -/
theorem contMDiffAt_sigmaMk_comp_iff {i : ι} {h : P → M i} {p : P} :
    ContMDiffAt J I n (Sigma.mk i ∘ h) p ↔ ContMDiffAt J I n h p := by
  obtain (hH | hH) := isEmpty_or_nonempty H
  · exact ((isEmpty_of_chartedSpace H (M := M i)).false (h p)).elim
  rw [contMDiffAt_iff, contMDiffAt_iff,
    Topology.IsOpenEmbedding.sigmaMk.toIsEmbedding.toIsInducing.continuousAt_iff]
  refine and_congr Iff.rfl ?_
  have : extChartAt I ((Sigma.mk i ∘ h) p) ∘ (Sigma.mk i ∘ h) ∘ (extChartAt J p).symm =
      extChartAt I (h p) ∘ h ∘ (extChartAt J p).symm := by
    funext z
    exact extChartAt_sigma_mk _ _
  rw [this]

/-- A map into a summand is `C^n` iff its composite with the inclusion is. -/
theorem contMDiff_sigmaMk_comp_iff {i : ι} {h : P → M i} :
    ContMDiff J I n (Sigma.mk i ∘ h) ↔ ContMDiff J I n h :=
  forall_congr' fun _ => contMDiffAt_sigmaMk_comp_iff

end ContMDiff

noncomputable section

namespace AnalyticSpace

open KLocallyRingedSpace

variable {K : Type} [RCLike K] {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
  {ι : Type u} {M : ι → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace E (M i)]

/-! ### `Sp(Sigma.mk i)` is an open immersion -/

/-- **`Sp` of the inclusion of a summand into the disjoint union is an open immersion**: the base
map is the open embedding `Sigma.mk i`, and analytic functions on an open subset of the image
correspond to analytic functions on the corresponding open subset of the summand (the argument of
`isOpenImmersion_ofManifoldHom_val`). -/
instance isOpenImmersion_ofManifoldHom_sigmaMk (i : ι) :
    LocallyRingedSpace.IsOpenImmersion
      (ofManifoldHom (K := K) (E := E) (E' := E) (Sigma.mk i : M i → Σ j, M j)
        (ContMDiff.sigmaMk i)).1 where
  base_open := Topology.IsOpenEmbedding.sigmaMk
  c_iso V := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a b hab => Subtype.ext ?_, fun ⟨g, hg⟩ => ?_⟩
    · ext ⟨x, y, hy, rfl⟩
      exact congr($(hab).1 ⟨y, ⟨y, hy, rfl⟩⟩)
    · let a : TopCat.of (M i) ⟶ TopCat.of (Σ j, M j) :=
        ofManifoldBase (K := K) (E := E) (E' := E) (Sigma.mk i)
          (ContMDiff.sigmaMk (I := 𝓘(K, E)) (n := ω) (M := M) i)
      have ha : Topology.IsOpenEmbedding a.hom := Topology.IsOpenEmbedding.sigmaMk
      let V' : Opens (M i) := (Opens.map a).obj (ha.isOpenMap.functor.obj V)
      let b : V' ≃ₜ ha.isOpenMap.functor.obj V :=
        ha.homeomorphOfSubsetRange <| Set.image_subset_range _ V.1
      refine ⟨⟨g ∘ b.symm, ContMDiff.comp hg ?_⟩, Subtype.ext <| funext fun _ => ?_⟩
      · refine (contMDiff_subtypeVal_comp_iff' _).mp ?_
        rw [← contMDiff_sigmaMk_comp_iff (I := 𝓘(K, E))]
        convert! contMDiff_subtype_val
        funext x
        exact congr($(b.apply_symm_apply x).1)
      · change g _ = _
        congr
        apply b.symm_apply_apply

/-! ### `Sp(Σ i, M i) ≅ ∐ Sp(M i)` -/

section Iso

variable {n : ℕ} (ψ : E ≃L[K] (Fin n → K)) {ι : Type u} [Countable ι]
  (M : ι → AnalyticManifold.{u} K E)

/-- `Sp` of the inclusion of a summand, as a morphism of analytic spaces, is an open immersion. -/
instance isOpenImmersion_toSpaceHom_sigmaMk (i : ι) :
    LocallyRingedSpace.IsOpenImmersion (toSpaceHom ψ (Manifold.sigmaMk M i)).1 :=
  isOpenImmersion_ofManifoldHom_sigmaMk (K := K) (E := E) (M := fun j => (M j : Type u)) i

/-- The descent `∐ Sp(M i) ⟶ Sp(Σ i, M i)` of the `Sp(Sigma.mk i)`. -/
def sigmaToSpaceDesc :
    AnalyticSpace.sigma (fun i => toSpace ψ (M i)) ⟶ toSpace ψ (sigmaManifold M) :=
  AnalyticSpace.sigmaDesc fun i => toSpaceHom ψ (Manifold.sigmaMk M i)

/-- The descent is an isomorphism: the `Sp(Sigma.mk i)` are open immersions with pairwise disjoint
images covering the disjoint union (`isIso_sigmaDesc_of_isOpenImmersion`). -/
theorem isIso_sigmaToSpaceDesc : IsIso (sigmaToSpaceDesc ψ M) := by
  refine AnalyticSpace.isIso_sigmaDesc_of_isOpenImmersion _ ?_ ?_
  · intro i j hij a b h
    exact hij (Sigma.mk.inj_iff.mp h).1
  · intro y
    exact ⟨y.1, y.2, rfl⟩

/-- **`Sp` of a countable disjoint union of analytic manifolds is the coproduct of the spaces of the
summands**: the inverse of the descent of the `Sp(Sigma.mk i)`. -/
def toSpaceSigmaIso :
    toSpace ψ (sigmaManifold M) ≅ AnalyticSpace.sigma (fun i => toSpace ψ (M i)) :=
  have := isIso_sigmaToSpaceDesc ψ M
  (asIso (sigmaToSpaceDesc ψ M)).symm

/-- The isomorphism is compatible with the injections: `Sp(Sigma.mk i)` composed with it is the
`i`-th injection of the coproduct. -/
theorem toSpaceHom_sigmaMk_comp_toSpaceSigmaIso_hom (i : ι) :
    toSpaceHom ψ (Manifold.sigmaMk M i) ≫ (toSpaceSigmaIso ψ M).hom =
      AnalyticSpace.sigmaι (fun i => toSpace ψ (M i)) i := by
  have := isIso_sigmaToSpaceDesc ψ M
  change toSpaceHom ψ (Manifold.sigmaMk M i) ≫ (asIso (sigmaToSpaceDesc ψ M)).inv = _
  rw [Iso.comp_inv_eq, asIso_hom]
  exact (AnalyticSpace.sigmaι_sigmaDesc (fun i => toSpaceHom ψ (Manifold.sigmaMk M i)) i).symm

/-- On points, the isomorphism carries `⟨i, x⟩` to the image of `x` under the `i`-th injection. -/
theorem toFun_toSpaceSigmaIso_hom_mk (i : ι) (x : M i) :
    KLocallyRingedSpace.Hom.toFun (toSpaceSigmaIso ψ M).hom (Sigma.mk i x) =
      KLocallyRingedSpace.Hom.toFun (AnalyticSpace.sigmaι (fun i => toSpace ψ (M i)) i) x :=
  congrArg (fun g : toSpace ψ (M i) ⟶ AnalyticSpace.sigma (fun i => toSpace ψ (M i)) =>
    KLocallyRingedSpace.Hom.toFun g x) (toSpaceHom_sigmaMk_comp_toSpaceSigmaIso_hom ψ M i)

end Iso

end AnalyticSpace
