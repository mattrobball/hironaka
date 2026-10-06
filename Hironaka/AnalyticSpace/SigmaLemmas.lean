/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Sigma
import Hironaka.AnalyticSpace.IsoCriterion
import Hironaka.AnalyticSpace.KSpace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The coproduct in `An/K`: universal property and the isomorphism criterion

The facts about `AnalyticSpace.sigma` read off the construction of
`Hironaka/AnalyticSpace/Sigma.lean` (the morphisms of `An/K` being those of `ℜ/K`), and the colimit
structure of the cofan `(sigma X, sigmaι X)` (`isColimitSigmaCofan`, `hasCoproduct`): `An/K` has
the coproduct of every countable family.

`isIso_sigmaDesc_of_isOpenImmersion` is the tool for identifying a space with a coproduct: the
descent `sigmaDesc f` of a family of open immersions `f i : X i ⟶ Y` with pairwise disjoint images
covering `Y` is an isomorphism — its base map is a bijective open map, hence a homeomorphism, and
its stalk maps are isomorphisms because `sigmaι X i ≫ sigmaDesc f = f i` with both `sigmaι X i`
and `f i` open immersions (the criterion `isIso_of_isIso_base_of_stalkMap_bijective` of
`Hironaka/AnalyticSpace/IsoCriterion.lean`). This is how `Sp(Σ i, M i) ≅ ∐ Sp(M i)`
(`toSpaceSigmaIso`, `Hironaka/AnalyticSpace/Manifold/Sigma.lean`) and the decomposition of a
non-singular space into its pure-dimensional strata (`stratumSigmaIso`,
`Hironaka/AnalyticSpace/Manifold/SigmaStratum.lean`) are proved; both are restated in
`Hironaka/AnalyticSpace/SigmaCoproductLemmas.lean`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

noncomputable section

namespace AnalyticSpace

variable {K : Type} [RCLike K] {ι : Type v} [Countable ι] (X : ι → AnalyticSpace.{u} K)

/-- The injections of the coproduct in `An/K` are open immersions. -/
instance isOpenImmersion_sigmaι (i : ι) : LocallyRingedSpace.IsOpenImmersion (sigmaι X i).1 :=
  KLocallyRingedSpace.isOpenImmersion_coprodι _ i

/-- The injections are injective on points. -/
theorem sigmaι_toFun_injective (i : ι) : Function.Injective (Hom.toFun (sigmaι X i)) :=
  KLocallyRingedSpace.coprodι_toFun_injective (fun i => (X i).toKLocallyRingedSpace) i

/-- The images of distinct summands are disjoint. -/
theorem sigmaι_toFun_ne {i j : ι} (hij : i ≠ j) (a : X i) (b : X j) :
    Hom.toFun (sigmaι X i) a ≠ Hom.toFun (sigmaι X j) b :=
  KLocallyRingedSpace.coprodι_toFun_ne (fun i => (X i).toKLocallyRingedSpace) hij a b

/-- Every point of the coproduct lies in the image of a summand. -/
theorem exists_sigmaι_toFun_eq (x : sigma X) :
    ∃ (i : ι) (a : X i), Hom.toFun (sigmaι X i) a = x :=
  KLocallyRingedSpace.exists_coprodι_toFun_eq (fun i => (X i).toKLocallyRingedSpace) x

variable {X} in
/-- The descent factors the injections. -/
theorem sigmaι_sigmaDesc {Y : AnalyticSpace.{u} K} (f : ∀ i, X i ⟶ Y) (i : ι) :
    sigmaι X i ≫ sigmaDesc f = f i :=
  KLocallyRingedSpace.coprodι_coprodDesc (X := fun i => (X i).toKLocallyRingedSpace) f i

variable {X} in
/-- A morphism out of the coproduct is determined by its restrictions to the summands. -/
theorem sigma_hom_ext {Y : AnalyticSpace.{u} K} {g h : sigma X ⟶ Y}
    (H : ∀ i, sigmaι X i ≫ g = sigmaι X i ≫ h) : g = h :=
  KLocallyRingedSpace.coprod_hom_ext (X := fun i => (X i).toKLocallyRingedSpace) H

variable {X} in
/-- The underlying map of the descent on the image of the `i`-th summand is the underlying map of
`f i`. -/
theorem toFun_sigmaDesc_toFun_sigmaι {Y : AnalyticSpace.{u} K} (f : ∀ i, X i ⟶ Y) (i : ι)
    (a : X i) : Hom.toFun (sigmaDesc f) (Hom.toFun (sigmaι X i) a) = Hom.toFun (f i) a :=
  congrArg (fun g : X i ⟶ Y => Hom.toFun g a) (sigmaι_sigmaDesc f i)

/-- **The cofan `(sigma X, sigmaι X)` is a colimit cocone**: the coproduct of `X` in the category
`An/K`. -/
def isColimitSigmaCofan : IsColimit (Cofan.mk (sigma X) (sigmaι X)) where
  desc s := sigmaDesc fun i => s.ι.app ⟨i⟩
  fac _ := fun ⟨i⟩ => sigmaι_sigmaDesc _ i
  uniq s _ hm := sigma_hom_ext fun i =>
    (hm ⟨i⟩).trans (sigmaι_sigmaDesc (fun i => s.ι.app ⟨i⟩) i).symm

/-- `An/K` has the coproduct of every countable family. -/
theorem hasCoproduct : HasCoproduct X :=
  ⟨⟨⟨_, isColimitSigmaCofan X⟩⟩⟩

/-! ### The isomorphism criterion for descents -/

/-- A morphism of `An/K` which is an isomorphism in `ℜ/K` is an isomorphism (the morphisms and
compositions are the same). -/
theorem isIso_of_isIso_toKLocallyRingedSpace {Y Z : AnalyticSpace.{u} K} (f : Y ⟶ Z)
    (h : @IsIso (KLocallyRingedSpace.{u} K) _ Y.toKLocallyRingedSpace Z.toKLocallyRingedSpace f) :
    IsIso f :=
  ⟨⟨@inv (KLocallyRingedSpace.{u} K) _ Y.toKLocallyRingedSpace Z.toKLocallyRingedSpace f h,
    @IsIso.hom_inv_id (KLocallyRingedSpace.{u} K) _ _ _ f h,
    @IsIso.inv_hom_id (KLocallyRingedSpace.{u} K) _ _ _ f h⟩⟩

variable {X} in
/-- **The descent of a family of open immersions with pairwise disjoint images covering the target
is an isomorphism.** The base map is a bijective open map, hence a homeomorphism; the stalk maps
are isomorphisms since `sigmaι X i ≫ sigmaDesc f = f i` with `sigmaι X i` and `f i` open
immersions. -/
theorem isIso_sigmaDesc_of_isOpenImmersion {Y : AnalyticSpace.{u} K} (f : ∀ i, X i ⟶ Y)
    [∀ i, LocallyRingedSpace.IsOpenImmersion (f i).1]
    (hdisj : ∀ i j, i ≠ j → ∀ (a : X i) (b : X j), Hom.toFun (f i) a ≠ Hom.toFun (f j) b)
    (hcover : ∀ y : Y, ∃ (i : ι) (a : X i), Hom.toFun (f i) a = y) :
    IsIso (sigmaDesc f) := by
  apply isIso_of_isIso_toKLocallyRingedSpace
  have hbij : Function.Bijective (sigmaDesc f).1.1.base := by
    constructor
    · intro x x' hxx'
      obtain ⟨i, a, rfl⟩ := exists_sigmaι_toFun_eq X x
      obtain ⟨j, b, rfl⟩ := exists_sigmaι_toFun_eq X x'
      change Hom.toFun (sigmaDesc f) (Hom.toFun (sigmaι X i) a) =
        Hom.toFun (sigmaDesc f) (Hom.toFun (sigmaι X j) b) at hxx'
      rw [toFun_sigmaDesc_toFun_sigmaι, toFun_sigmaDesc_toFun_sigmaι] at hxx'
      by_cases hij : i = j
      · subst hij
        rw [(KLocallyRingedSpace.Hom.isOpenEmbedding_toFun (f i)).injective hxx']
      · exact (hdisj i j hij a b hxx').elim
    · intro y
      obtain ⟨i, a, rfl⟩ := hcover y
      exact ⟨Hom.toFun (sigmaι X i) a, toFun_sigmaDesc_toFun_sigmaι f i a⟩
  have hopen : IsOpenMap (sigmaDesc f).1.1.base := by
    intro U hU
    have : (sigmaDesc f).1.1.base '' U =
        ⋃ i, Hom.toFun (f i) '' (Hom.toFun (sigmaι X i) ⁻¹' U) := by
      ext y
      simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨x, hxU, rfl⟩
        obtain ⟨i, a, rfl⟩ := exists_sigmaι_toFun_eq X x
        exact ⟨i, a, hxU, (toFun_sigmaDesc_toFun_sigmaι f i a).symm⟩
      · rintro ⟨i, a, ha, rfl⟩
        exact ⟨Hom.toFun (sigmaι X i) a, ha, toFun_sigmaDesc_toFun_sigmaι f i a⟩
    rw [this]
    exact isOpen_iUnion fun i => (KLocallyRingedSpace.Hom.isOpenEmbedding_toFun (f i)).isOpenMap _
      ((KLocallyRingedSpace.Hom.continuous_toFun (sigmaι X i)).isOpen_preimage U hU)
  have : IsIso (sigmaDesc f).1.1.base := TopCat.isIso_of_bijective_of_isOpenMap _ hbij hopen
  refine KLocallyRingedSpace.isIso_of_isIso_base_of_stalkMap_bijective
    (sigmaDesc f : (sigma X).toKLocallyRingedSpace ⟶ Y.toKLocallyRingedSpace) fun x => ?_
  obtain ⟨i, a, rfl⟩ := exists_sigmaι_toFun_eq X x
  have h1 : (sigmaι X i).1 ≫ (sigmaDesc f).1 = (f i).1 :=
    congrArg Subtype.val (sigmaι_sigmaDesc f i)
  have h2 : IsIso (((sigmaι X i).1 ≫ (sigmaDesc f).1).stalkMap a) := by
    rw [h1]
    infer_instance
  have h2' : IsIso ((sigmaDesc f).1.stalkMap ((sigmaι X i).1.base a) ≫
      (sigmaι X i).1.stalkMap a) := by
    rw [← LocallyRingedSpace.stalkMap_comp]
    exact h2
  have h3 : IsIso ((sigmaDesc f).1.stalkMap ((sigmaι X i).1.base a)) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _ ((sigmaι X i).1.stalkMap a) inferInstance h2'
  exact (ConcreteCategory.isIso_iff_bijective _).mp h3

end AnalyticSpace
