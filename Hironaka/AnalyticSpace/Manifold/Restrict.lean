/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.KSpace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The space of a manifold restricted to an open subset

The open subspace `Sp(M) | U` of the `K`-local-ringed space of a manifold `M` is the space of the
open submanifold `U`. The inclusion `U → M` is an analytic map whose `K`-morphism
`ofManifoldHom Subtype.val` is an open immersion (`isOpenImmersion_ofManifoldHom_val`): the base map
is the open embedding of `U`, and on sections the restriction `𝒪_M(V) → 𝒪_U(V ∩ U)` is a bijection,
an analytic function on an open `V ⊆ U` being an analytic function on the open `V` of `M`. Two open
immersions with the same range are `K`-isomorphic over their common target (`isoOfRangeEq`), which
gives `ofManifold_restrictOpen_iso : Sp(M) | U ≅ Sp(U)`, an isomorphism over `Sp(M)`
(`ofManifold_restrictOpen_iso_hom_comp`). This is the analytic analogue of Mathlib's
`ChartedSpace.restrictLocallyRingedSpaceIso` for smooth manifolds, stated for `K`-local-ringed
spaces.

The isomorphism is used throughout the comparison of manifolds with their spaces: the chart
isomorphisms (`Hironaka.AnalyticSpace.Manifold.Chart`, `Hironaka.AnalyticSpace.ChartLift`), the
stratum isomorphisms (`Hironaka.AnalyticSpace.Manifold.Stratum`,
`Hironaka.AnalyticSpace.Manifold.StratumIso`, `Hironaka.AnalyticSpace.HomExtNonSingular`), morphisms
into an open subset of `Kⁿ` (`Hironaka.AnalyticSpace.HomOfSectionsAffine`), and the restriction of
local resolutions to the pieces of a cover
(`Hironaka.Resolution.Analytic.Kol07Thm45.PieceRestrict`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open scoped Manifold ContDiff

universe u

noncomputable section

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- The isomorphism of two open immersions with the same range is over the target. -/
theorem isoOfRangeEq_hom_comp {A B X : KLocallyRingedSpace.{u} K} (a : A ⟶ X) (b : B ⟶ X)
    [LocallyRingedSpace.IsOpenImmersion a.1] [LocallyRingedSpace.IsOpenImmersion b.1]
    (h : Set.range (Hom.toFun a) = Set.range (Hom.toFun b)) :
    (isoOfRangeEq a b h).hom ≫ b = a := by
  apply Hom.ext
  rw [Hom.comp_val]
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac b.1 a.1 (le_of_eq h)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] {M : Type u} [TopologicalSpace M]
  [ChartedSpace E M]

/-- **The `K`-morphism of the inclusion of an open submanifold is an open immersion**: an analytic
function on an open `V ⊆ U` is an analytic function on the open `V` of `M`, so the restriction of
sections is bijective (the analytic analogue of Mathlib's instance for
`ChartedSpace.locallyRingedSpaceMap Subtype.val`). -/
instance isOpenImmersion_ofManifoldHom_val (U : Opens M) :
    LocallyRingedSpace.IsOpenImmersion
      (ofManifoldHom (K := K) (E := E) (E' := E) (Subtype.val : U → M)
        contMDiff_subtype_val).1 where
  base_open := U.isOpenEmbedding'
  c_iso V := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a b hab => Subtype.ext ?_, fun ⟨g, hg⟩ => ?_⟩
    · ext ⟨x, y, hy, rfl⟩
      exact congr($(hab).1 ⟨y, ⟨y, hy, rfl⟩⟩)
    · let a : TopCat.of U ⟶ TopCat.of M := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
      have ha : Topology.IsOpenEmbedding a.hom := U.isOpenEmbedding'
      let V' : Opens U := (Opens.map a).obj (ha.isOpenMap.functor.obj V)
      let b : V' ≃ₜ ha.isOpenMap.functor.obj V :=
        U.isOpenEmbedding'.homeomorphOfSubsetRange <| Set.image_subset_range _ V.1
      refine ⟨⟨g ∘ b.symm, ContMDiff.comp hg ?_⟩, Subtype.ext <| funext fun _ => ?_⟩
      · refine (contMDiff_subtypeVal_comp_iff' _).mp ?_
        rw [← contMDiff_subtypeVal_comp_iff']
        convert! contMDiff_subtype_val
        ext x
        exact congr($(b.apply_symm_apply x).1)
      · change g _ = _
        congr
        apply b.symm_apply_apply

/-- **`Sp(M) | U ≅ Sp(U)`** for an open `U ⊆ M` (the analytic analogue of Mathlib's
`ChartedSpace.restrictLocallyRingedSpaceIso`, as `K`-local-ringed spaces). -/
def ofManifold_restrictOpen_iso (U : Opens M) :
    KIso ((ofManifold K E M).restrictOpen U) (ofManifold K E U) :=
  isoOfRangeEq (ofRestrict (ofManifold K E M) U)
    (ofManifoldHom (K := K) (E := E) (E' := E) (Subtype.val : U → M) contMDiff_subtype_val)
    (by rw [range_toFun_ofRestrict, toFun_ofManifoldHom, Subtype.range_val])

/-- The isomorphism `Sp(M) | U ≅ Sp(U)` is over `Sp(M)`: composed with `Sp(U → M)` it is the open
immersion `Sp(M) | U ⟶ Sp(M)`. -/
theorem ofManifold_restrictOpen_iso_hom_comp (U : Opens M) :
    (ofManifold_restrictOpen_iso (K := K) (E := E) U).hom ≫
        ofManifoldHom (K := K) (E := E) (E' := E) (Subtype.val : U → M) contMDiff_subtype_val =
      ofRestrict (ofManifold K E M) U :=
  isoOfRangeEq_hom_comp (ofRestrict (ofManifold K E M) U)
    (ofManifoldHom (K := K) (E := E) (E' := E) (Subtype.val : U → M) contMDiff_subtype_val) _

end AnalyticSpace.KLocallyRingedSpace
