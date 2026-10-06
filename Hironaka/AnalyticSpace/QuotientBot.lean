/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Quotient.Defs
import Hironaka.AnalyticSpace.Lemmas
import Hironaka.AnalyticSpace.Quotient
import Hironaka.Manifold.IdealSheaf.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The quotient by the zero ideal sheaf

The canonical morphism `QuotientSpace.ι : (S(𝒥), 𝒪_X/𝒥) ⟶ X` of the quotient is an
isomorphism when every stalk ideal of `𝒥` is zero: the support is the whole space, so the base map
is a homeomorphism (the inclusion of `univ`), and the stalk maps are the quotient maps
`𝒪_{X,z} → 𝒪_{X,z}/0`, bijective; a morphism of sheaves whose stalk maps are isomorphisms is an
isomorphism (Mathlib's `TopCat.Presheaf.isIso_of_stalkFunctor_map_iso`, through the pushforward
along the homeomorphism, whose stalks are those of the quotient sheaf:
`stalkPushforward_iso_of_isInducing`). Hence `X.quotient 𝒥 ≅ X` as `K`-local-ringed spaces
(`quotientBotIso`), and in particular the local analytic `K`-space with no equations,
`localModel K n G ![]`, is `K`-isomorphic to `(G, 𝒜_G)` — a theorem, not a definitional identity.
This is how the chart domain of an analytic manifold is exhibited as a local model when the space
of a manifold is shown to be an analytic `K`-space. Not in the sources; routine.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold

universe u

namespace AnalyticSpace.QuotientSpace

variable (X : LocallyRingedSpace.{u}) (J : IdealSheaf X.𝒪)

/-- If every stalk ideal of `𝒥` is zero, its cosupport is the whole space. -/
theorem cosupport_eq_univ_of_stalkIdeal_eq_bot (hJ : ∀ x : X, J.stalkIdeal x = ⊥) :
    J.support = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  rw [IdealSheaf.mem_support, hJ x]
  have : Nontrivial (X.𝒪.presheaf.stalk x) := (X.isLocalRing x).toNontrivial
  exact fun h => one_ne_zero (Ideal.mem_bot.mp ((Ideal.eq_top_iff_one _).mp h))

/-- The homeomorphism `S(𝒥) ≃ₜ X` when every stalk ideal of `𝒥` is zero. -/
noncomputable def supportHomeomorph (hJ : ∀ x : X, J.stalkIdeal x = ⊥) : support X J ≃ₜ X :=
  (Homeomorph.setCongr (cosupport_eq_univ_of_stalkIdeal_eq_bot X J hJ)).trans
    (Homeomorph.Set.univ X)

theorem isIso_ιTop_of_stalkIdeal_eq_bot (hJ : ∀ x : X, J.stalkIdeal x = ⊥) : IsIso (ιTop X J) := by
  have h : ιTop X J = (TopCat.isoOfHomeo (supportHomeomorph X J hJ)).hom := by
    ext x
    rfl
  rw [h]
  infer_instance

/-- The stalk map of the canonical morphism is injective when the stalk ideal is zero. -/
theorem stalkMap_injective_of_stalkIdeal_eq_bot (z : support X J) (hz : J.stalkIdeal z.1 = ⊥) :
    Function.Injective ((ιHom X J).stalkMap z).hom := by
  intro σ τ h
  have h1 := congrArg (evalHom X J z).hom h
  rw [evalHom_stalkMap, evalHom_stalkMap] at h1
  have hinj : Function.Injective (Ideal.Quotient.mk (stalkIdeal X J z.1)) := by
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker]
    exact hz
  exact hinj h1

theorem isIso_stalkMap_of_stalkIdeal_eq_bot (z : support X J) (hz : J.stalkIdeal z.1 = ⊥) :
    IsIso ((ιHom X J).stalkMap z) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨stalkMap_injective_of_stalkIdeal_eq_bot X J z hz, stalkMap_surjective X J z⟩

/-- The sheaf map of the canonical morphism is an isomorphism when every stalk ideal is zero. -/
theorem isIso_ιHom_c_of_stalkIdeal_eq_bot (hJ : ∀ x : X, J.stalkIdeal x = ⊥) :
    IsIso (ιHom X J).c := by
  -- read `c` as a morphism of sheaves `𝒪_X ⟶ ιTop_* (𝒪_X/𝒥)` and use the stalk criterion
  let F : TopCat.Sheaf CommRingCat.{u} X.toTopCat := X.sheaf
  let G : TopCat.Sheaf CommRingCat.{u} X.toTopCat :=
    (TopCat.Sheaf.pushforward CommRingCat.{u} (ιTop X J)).obj (sheafCommRing X J)
  let φ : F ⟶ G := ⟨(ιHom X J).c⟩
  have hcos := cosupport_eq_univ_of_stalkIdeal_eq_bot X J hJ
  have hstalk : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ.hom) := by
    intro x
    have hx : x ∈ J.support := hcos ▸ Set.mem_univ x
    let z : support X J := ⟨x, hx⟩
    have hind : Topology.IsInducing (ιTop X J) := Topology.IsInducing.subtypeVal
    have hpush : IsIso ((quotientSpace X J).presheaf.stalkPushforward CommRingCat.{u}
        (ιHom X J).base z) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing _ hind _ z
    have hmap : IsIso ((ιHom X J).stalkMap z) := isIso_stalkMap_of_stalkIdeal_eq_bot X J z (hJ x)
    change IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} ((ιTop X J) z)).map φ.hom)
    exact @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ hpush hmap rfl
  have : IsIso φ := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso φ
  exact Functor.map_isIso (TopCat.Sheaf.forget CommRingCat.{u} X.toTopCat) φ

/-- The canonical morphism of presheafed spaces `(S(𝒥), 𝒪_X/𝒥) ⟶ X` is an isomorphism when every
stalk ideal of `𝒥` is zero. -/
theorem isIso_ιHom_of_stalkIdeal_eq_bot (hJ : ∀ x : X, J.stalkIdeal x = ⊥) : IsIso (ιHom X J) := by
  have : IsIso (ιHom X J).base := isIso_ιTop_of_stalkIdeal_eq_bot X J hJ
  have : IsIso (ιHom X J).c := isIso_ιHom_c_of_stalkIdeal_eq_bot X J hJ
  exact PresheafedSpace.isIso_of_components _

/-- The canonical morphism of locally ringed spaces `(S(𝒥), 𝒪_X/𝒥) ⟶ X` is an isomorphism when
every stalk ideal of `𝒥` is zero. -/
theorem isIso_ι_of_stalkIdeal_eq_bot (hJ : ∀ x : X, J.stalkIdeal x = ⊥) : IsIso (ι X J) := by
  have h1 : IsIso (SheafedSpace.forgetToPresheafedSpace.map
      (LocallyRingedSpace.forgetToSheafedSpace.map (ι X J))) :=
    isIso_ιHom_of_stalkIdeal_eq_bot X J hJ
  have h2 : IsIso (LocallyRingedSpace.forgetToSheafedSpace.map (ι X J)) :=
    isIso_of_reflects_iso _ SheafedSpace.forgetToPresheafedSpace
  exact isIso_of_reflects_iso _ LocallyRingedSpace.forgetToSheafedSpace

end QuotientSpace

namespace KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- The canonical `K`-morphism of the quotient by an ideal sheaf with zero stalks is an
isomorphism. -/
theorem isIso_quotientι_of_stalkIdeal_eq_bot (X : KLocallyRingedSpace.{u} K)
    (J : IdealSheaf X.toLocallyRingedSpace.𝒪) (hJ : ∀ x : X, J.stalkIdeal x = ⊥) :
    IsIso (quotientι X J) :=
  haveI : IsIso (quotientι X J).1 := QuotientSpace.isIso_ι_of_stalkIdeal_eq_bot _ J hJ
  isIso_of_isIso_val _

/-- **The quotient of a `K`-local-ringed space by an ideal sheaf with zero stalks is
`K`-isomorphic to the space.** -/
noncomputable def quotientBotIso (X : KLocallyRingedSpace.{u} K)
    (J : IdealSheaf X.toLocallyRingedSpace.𝒪) (hJ : ∀ x : X, J.stalkIdeal x = ⊥) :
    KIso (X.quotient J) X :=
  haveI := isIso_quotientι_of_stalkIdeal_eq_bot X J hJ
  asIso (quotientι X J)

end KLocallyRingedSpace

end AnalyticSpace
