/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.GlueHomAffine
public import Hironaka.AnalyticSpace.HomExt
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# `K`-morphisms into `(Kⁿ, 𝒜_{Kⁿ})` from `n` global sections: compatibility

A `K`-morphism from an analytic `K`-space `X` into `(Kⁿ, 𝒜_{Kⁿ})` is the same as `n` global
sections of `𝒪_X` (a local `Kⁿ`-coordination is such a morphism, [Hir64, Ch. 0, §1, p. 120]).
The uniqueness is `hom_ext_of_coord` (`Hironaka/AnalyticSpace/HomExt.lean`: the pullbacks of the
coordinate functions determine the morphism); the existence, `AnalyticSpace.homOfSections`, is
assembled in `Hironaka/AnalyticSpace/HomOfSections.lean` from this file (compatibility),
`Hironaka/AnalyticSpace/HomOfSectionsAffine.lean` (the affine case),
`Hironaka/AnalyticSpace/HomOfSectionsModel.lean` (local models) and
`Hironaka/AnalyticSpace/GlueHomAffine.lean` (gluing).

**Compatibility from coordinates.** For a `K`-morphism `φ : X|W ⟶ Kⁿ` and `z ∈ W`, the stalk
map of `φ` at `z` followed by the isomorphism of the stalk of `X|W` with that of `X` is a local
homomorphism `σ_φ : 𝒜_{Kⁿ, φ(z)} → 𝒪_{X,z}` sending constants to constants and the coordinate
germs to the germs of the pullbacks `φ^*(z_i)`. Two morphisms `φ : X|W ⟶ Kⁿ`, `φ' : X|W' ⟶ Kⁿ`
whose coordinate pullbacks have the same germs at `z ∈ W ∩ W'` therefore have the same base point
at `z` (the coordinates of `φ(z)` are the residues of `φ^*(z_i)` at `z`) and, when the stalk
`𝒪_{X,z}` is Noetherian (hypothesis `hN`; `ringHom_ext_of_coord`, Krull's intersection
theorem), the same `σ`, hence the same germs of the
pullbacks of every function of `𝒜_{Kⁿ}`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold

universe u

namespace AnalyticSpace

open KLocallyRingedSpace

variable {K : Type} [RCLike K] {n : ℕ}

/-! ### The stalk of an open subspace as the stalk of the space -/

section ResIso

variable (Z : KLocallyRingedSpace.{u} K)

/-- The stalk of `Z|W` at `z ∈ W`, identified with the stalk of `Z` at `z` (Mathlib's
`restrictStalkIso`). -/
abbrev resIso (W : Opens Z) {z : Z} (hz : z ∈ W) :
    (Z.restrictOpen W).toLocallyRingedSpace.presheaf.stalk ⟨z, hz⟩ ≅
      Z.toLocallyRingedSpace.presheaf.stalk z :=
  PresheafedSpace.restrictStalkIso Z.toLocallyRingedSpace.toPresheafedSpace
    (Opens.isOpenEmbedding W) ⟨z, hz⟩

/-- The identification on germs: a section of `𝒪_{Z|W}` over `T` is a section of `𝒪_Z` over the
image of `T`. -/
theorem resIso_hom_germ (W : Opens Z) {z : Z} (hz : z ∈ W) (T : Opens (Z.restrictOpen W))
    (hT : (⟨z, hz⟩ : W) ∈ T) (s : Z.toLocallyRingedSpace.presheaf.obj (op (imgOpens Z W T))) :
    (resIso Z W hz).hom ((Z.restrictOpen W).toLocallyRingedSpace.presheaf.germ T ⟨z, hz⟩ hT s) =
      Z.toLocallyRingedSpace.presheaf.germ (imgOpens Z W T) z (mem_imgOpens_of_mem Z hz hT) s :=
  congrArg (fun φ => φ.hom s) (PresheafedSpace.restrictStalkIso_hom_eq_germ
    Z.toLocallyRingedSpace.toPresheafedSpace (Opens.isOpenEmbedding W) T ⟨z, hz⟩ hT)

/-- The identification sends the constant germs of `Z|W` to those of `Z`. -/
theorem resIso_hom_constAt (W : Opens Z) {z : Z} (hz : z ∈ W) (c : K) :
    (resIso Z W hz).hom (constAt (Z.restrictOpen W) ⟨z, hz⟩ c) = constAt Z z c := by
  change (resIso Z W hz).hom ((Z.restrictOpen W).toLocallyRingedSpace.presheaf.germ ⊤ ⟨z, hz⟩
    trivial ((Z.restrictOpen W).algebraMap c)) = _
  refine (resIso_hom_germ Z W hz ⊤ trivial _).trans ?_
  change Z.toLocallyRingedSpace.presheaf.germ _ z _
    ((LocallyRingedSpace.Γ.map (ofRestrict Z W).1.op).hom (Z.algebraMap c)) = _
  rw [LocallyRingedSpace.Γ_map_op]
  exact TopCat.Presheaf.germ_res_apply Z.toLocallyRingedSpace.presheaf
    ((Opens.isOpenEmbedding W).isOpenMap.adjunction.counit.app ⊤) z _ _

/-- The inverse of the identification is the stalk map of the open immersion `Z|W ⟶ Z`
(Mathlib's `restrictStalkIso_inv_eq_ofRestrict`). -/
theorem resIso_inv_eq_stalkMap_ofRestrict (W : Opens Z) (w : Z.restrictOpen W) :
    (resIso Z W w.2).inv = (ofRestrict Z W).1.stalkMap w :=
  PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict Z.toLocallyRingedSpace.toPresheafedSpace
    (Opens.isOpenEmbedding W) w

/-- A local homomorphism sends the maximal ideal into the maximal ideal. -/
theorem map_mem_maximalIdeal_of_isLocalHom {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) :
    φ x ∈ IsLocalRing.maximalIdeal S := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  exact fun hu => hx (IsLocalHom.map_nonunit x hu)

end ResIso

/-! ### The stalk map of a morphism into affine space, as a map into the stalk of `X` -/

section Sigma

variable (Z : KLocallyRingedSpace.{u} K) {W : Opens Z} (φ : Z.restrictOpen W ⟶ affine.{u} K n)
  {z : Z} (hz : z ∈ W)

/-- The stalk map of `φ : Z|W ⟶ Kⁿ` at `z`, followed by the identification of the stalk of `Z|W`
with that of `Z`: `𝒜_{Kⁿ, φ(z)} → 𝒪_{Z,z}`. -/
def sigmaStalk : (affine.{u} K n).toLocallyRingedSpace.presheaf.stalk (φ.1.base ⟨z, hz⟩) →+*
    Z.toLocallyRingedSpace.presheaf.stalk z :=
  ((resIso Z W hz).hom.hom).comp (φ.1.stalkMap ⟨z, hz⟩).hom

theorem sigmaStalk_apply (a : (affine.{u} K n).toLocallyRingedSpace.presheaf.stalk
    (φ.1.base ⟨z, hz⟩)) :
    sigmaStalk Z φ hz a = (resIso Z W hz).hom ((φ.1.stalkMap ⟨z, hz⟩) a) := rfl

instance isLocalHom_sigmaStalk : IsLocalHom (sigmaStalk Z φ hz) := by
  have h1 : IsLocalHom (φ.1.stalkMap ⟨z, hz⟩).hom := φ.1.prop ⟨z, hz⟩
  have h2 : IsLocalHom (resIso Z W hz).hom.hom := isLocalHom_of_isIso _
  exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ h2 h1

theorem sigmaStalk_const (c : K) :
    sigmaStalk Z φ hz (const K (Kn.{u} K n) (Kn.{u} K n) (φ.1.base ⟨z, hz⟩) c) = constAt Z z c := by
  rw [sigmaStalk_apply]
  erw [AnalyticSpace.stalkMap_const (Z.restrictOpen W) φ ⟨z, hz⟩ c]
  exact resIso_hom_constAt Z W hz c

theorem sigmaStalk_coordAt (i : Fin n) :
    sigmaStalk Z φ hz (coordAt K n (φ.1.base ⟨z, hz⟩) i) =
      Z.toLocallyRingedSpace.presheaf.germ (imgOpens Z W ⊤) z (mem_imgOpens_of_mem Z hz trivial)
        (φ.pullbackΓ (coordSection K n i)) := by
  rw [sigmaStalk_apply]
  erw [AnalyticSpace.stalkMap_coordAt (Z.restrictOpen W) φ ⟨z, hz⟩ i]
  exact resIso_hom_germ Z W hz ⊤ trivial _

/-- The stalk map on a germ of `F ∈ 𝒜(V)`: the germ at `z` of the pullback `φ^*F`. -/
theorem sigmaStalk_germ (V : Opens (Kn.{u} K n)) (hV : φ.1.base ⟨z, hz⟩ ∈ V)
    (F : (affine.{u} K n).toLocallyRingedSpace.presheaf.obj (op V)) :
    sigmaStalk Z φ hz
        ((affine.{u} K n).toLocallyRingedSpace.presheaf.germ V (φ.1.base ⟨z, hz⟩) hV F) =
      Z.toLocallyRingedSpace.presheaf.germ (imgOpens Z W ((Opens.map φ.1.base).obj V)) z
        (mem_imgOpens_of_mem Z hz hV) (φ.1.c.app (op V) F) := by
  rw [sigmaStalk_apply]
  have e := PresheafedSpace.stalkMap_germ_apply φ.1.1 V ⟨z, hz⟩ hV F
  erw [e]
  exact resIso_hom_germ Z W hz _ hV _

/-- The coordinates of `φ(z)` are the residues of the pullbacks of the coordinates at `z`. -/
theorem germ_pullbackΓ_coord_sub_constAt_mem (i : Fin n) :
    Z.toLocallyRingedSpace.presheaf.germ (imgOpens Z W ⊤) z (mem_imgOpens_of_mem Z hz trivial)
        (φ.pullbackΓ (coordSection K n i)) - constAt Z z ((φ.1.base ⟨z, hz⟩).down i) ∈
      IsLocalRing.maximalIdeal (Z.toLocallyRingedSpace.presheaf.stalk z) := by
  rw [← sigmaStalk_coordAt Z φ hz i, ← sigmaStalk_const Z φ hz, ← map_sub]
  have hm := mem_maximalIdeal_coordAt_sub K n (φ.1.base ⟨z, hz⟩) i
  rw [eval_coordAt] at hm
  exact map_mem_maximalIdeal_of_isLocalHom (sigmaStalk Z φ hz) hm

end Sigma

/-! ### Transport of germs along an equality of points -/

section EqToHom

variable (n)

theorem germ_eqToHom {p q : Kn.{u} K n} (hpq : p = q) (V : Opens (Kn.{u} K n)) (hp : p ∈ V)
    (F : (affine.{u} K n).toLocallyRingedSpace.presheaf.obj (op V)) :
    (eqToHom (congrArg (affine.{u} K n).toLocallyRingedSpace.presheaf.stalk hpq)).hom
        ((affine.{u} K n).toLocallyRingedSpace.presheaf.germ V p hp F) =
      (affine.{u} K n).toLocallyRingedSpace.presheaf.germ V q (hpq ▸ hp) F := by
  subst hpq
  rfl

theorem const_eqToHom {p q : Kn.{u} K n} (hpq : p = q) (c : K) :
    (eqToHom (congrArg (affine.{u} K n).toLocallyRingedSpace.presheaf.stalk hpq)).hom
        (const K (Kn.{u} K n) (Kn.{u} K n) p c) = const K (Kn.{u} K n) (Kn.{u} K n) q c := by
  subst hpq
  rfl

theorem coordAt_eqToHom {p q : Kn.{u} K n} (hpq : p = q) (i : Fin n) :
    (eqToHom (congrArg (affine.{u} K n).toLocallyRingedSpace.presheaf.stalk hpq)).hom
        (coordAt K n p i) = coordAt K n q i := by
  subst hpq
  rfl

end EqToHom

/-! ### Two morphisms with the same coordinate pullbacks agree on base points and germs -/

section Compat

variable (Z : KLocallyRingedSpace.{u} K) {W W' : Opens Z} (φ : Z.restrictOpen W ⟶ affine.{u} K n)
  (φ' : Z.restrictOpen W' ⟶ affine.{u} K n) {z : Z} (hz : z ∈ W) (hz' : z ∈ W')
  (hcoord : ∀ i : Fin n,
    Z.toLocallyRingedSpace.presheaf.germ (imgOpens Z W ⊤) z (mem_imgOpens_of_mem Z hz trivial)
        (φ.pullbackΓ (coordSection K n i)) =
      Z.toLocallyRingedSpace.presheaf.germ (imgOpens Z W' ⊤) z (mem_imgOpens_of_mem Z hz' trivial)
        (φ'.pullbackΓ (coordSection K n i)))

include hcoord in
/-- Same coordinate pullbacks at `z` ⇒ same base point at `z`. -/
theorem base_eq_of_germ_pullbackΓ_coord : φ.1.base ⟨z, hz⟩ = φ'.1.base ⟨z, hz'⟩ := by
  apply ULift.ext
  funext i
  have h1 := germ_pullbackΓ_coord_sub_constAt_mem Z φ hz i
  have h2 := germ_pullbackΓ_coord_sub_constAt_mem Z φ' hz' i
  have hmem := Ideal.sub_mem _ h1 h2
  rw [hcoord i, sub_sub_sub_cancel_left, ← map_sub] at hmem
  by_contra hne
  exact ((IsLocalRing.mem_maximalIdeal _).mp hmem)
    (isUnit_constAt Z z (sub_ne_zero.mpr (Ne.symm hne)))

include hcoord in
/-- Same coordinate pullbacks at `z` ⇒ same germs at `z` of the pullbacks of every `F ∈ 𝒜(V)`
(`ringHom_ext_of_coord` on the stalk maps). -/
theorem germ_c_app_eq_of_germ_pullbackΓ_coord
    (hN : IsNoetherianRing (Z.toLocallyRingedSpace.presheaf.stalk z)) (V : Opens (Kn.{u} K n))
    (hV : φ.1.base ⟨z, hz⟩ ∈ V) (hV' : φ'.1.base ⟨z, hz'⟩ ∈ V)
    (F : (affine.{u} K n).toLocallyRingedSpace.presheaf.obj (op V)) :
    Z.toLocallyRingedSpace.presheaf.germ (imgOpens Z W ((Opens.map φ.1.base).obj V)) z
        (mem_imgOpens_of_mem Z hz hV) (φ.1.c.app (op V) F) =
      Z.toLocallyRingedSpace.presheaf.germ (imgOpens Z W' ((Opens.map φ'.1.base).obj V)) z
        (mem_imgOpens_of_mem Z hz' hV') (φ'.1.c.app (op V) F) := by
  have hq := base_eq_of_germ_pullbackΓ_coord Z φ φ' hz hz' hcoord
  -- transport `σ_{φ'}` to the stalk at `φ(z)`
  let e := eqToHom (congrArg (affine.{u} K n).toLocallyRingedSpace.presheaf.stalk hq)
  let σ' : (affine.{u} K n).toLocallyRingedSpace.presheaf.stalk (φ.1.base ⟨z, hz⟩) →+*
      Z.toLocallyRingedSpace.presheaf.stalk z := (sigmaStalk Z φ' hz').comp e.hom
  have hσ' : IsLocalHom σ' := by
    have h1 : IsLocalHom e.hom := isLocalHom_of_isIso _
    have h2 : IsLocalHom (sigmaStalk Z φ' hz') := isLocalHom_sigmaStalk Z φ' hz'
    exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ h2 h1
  have key : sigmaStalk Z φ hz = σ' := by
    refine @ringHom_ext_of_coord K _ n _ _ _ hN (φ.1.base ⟨z, hz⟩) (sigmaStalk Z φ hz) σ'
      (isLocalHom_sigmaStalk Z φ hz) hσ' (fun c => ?_) (fun i => ?_)
    · rw [sigmaStalk_const]
      change _ = sigmaStalk Z φ' hz' (e.hom (const K (Kn.{u} K n) (Kn.{u} K n) _ c))
      rw [const_eqToHom n hq c, sigmaStalk_const]
    · rw [sigmaStalk_coordAt]
      change _ = sigmaStalk Z φ' hz' (e.hom (coordAt K n _ i))
      rw [coordAt_eqToHom n hq i, sigmaStalk_coordAt]
      exact hcoord i
  rw [← sigmaStalk_germ Z φ hz V hV F, ← sigmaStalk_germ Z φ' hz' V hV' F, key]
  change sigmaStalk Z φ' hz' (e.hom _) = _
  rw [germ_eqToHom n hq V hV F]

end Compat

end AnalyticSpace
