/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.KSpace.Defs
public import Hironaka.Manifold.IdealSheaf.Defs
import Hironaka.Manifold.IdealSheaf.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The quotient of a locally ringed space by an ideal sheaf

Hironaka's local analytic `K`-space is `(S(𝓘), (𝒜_G/𝓘)|_{S(𝓘)})` [Hir64, Ch. 0, §1]: the support
`S(𝓘) = supp (𝒜_G/𝓘)` of the quotient sheaf, with the restriction of the quotient sheaf to it
("restriction to a closed subset" meaning the inverse-image sheaf). Bierstone and Milman use the
same construction for every closed subspace [BM97, §3]: a closed subspace `Y` of `X` is given by
a sheaf of ideals `𝓘_Y` of finite type in `𝒪_X`, with `|Y| = supp 𝒪_X/𝓘_Y` and `𝒪_Y` the
restriction of `𝒪_X/𝓘_Y` to `|Y|`. This file carries out the construction for an
arbitrary locally ringed space `X` and an ideal sheaf `𝒥` on it.

## The construction

The structure sheaf of the quotient is built directly as the sheaf of **compatible germ families**
over `Z := supp (𝒪_X/𝒥) = {z | 𝒥_z ≠ 𝒪_{X,z}}`: a section over an open `V ⊆ Z` is a family
`(s_z)_{z ∈ V}` with `s_z ∈ 𝒪_{X,z}/𝒥_z` which is locally the family of classes of one ambient
section. This is Mathlib's `TopCat.LocalPredicate` (the sheafification of the prelocal predicate
"the family of classes of one section over an open `W` of `X`") and `TopCat.subsheafToTypes`,
lifted to `CommRingCat` pointwise as `smoothSheafCommRing` lifts `smoothSheaf`. Its stalk at `z`
is `𝒪_{X,z}/𝒥_z`: the evaluation `evalHom` of a germ at `z` is a ring homomorphism, surjective
(every class is realized by a family near `z`) and injective (two families agreeing at `z` agree
near `z`: the difference of the ambient representatives has germ in `𝒥_z`, hence is the germ of
a section of `𝒥`, hence lies in `𝒥_y` for `y` near `z`). So the stalks are local rings
(quotients of the local rings `𝒪_{X,z}` by proper ideals), `quotientSpace X 𝒥` is a locally
ringed space, and the canonical morphism `ι : quotientSpace X 𝒥 ⟶ X` has the quotient maps as
stalk maps (`stalkMap_comp_evalHom`, `stalkMap_surjective`), which are local.

## Main definitions

In the namespace `QuotientSpace`: `support`, `fiber`, `localPred`, `presheafCommRing`,
`sheafCommRing`, `quotientSpace`, `evalHom` with `stalkEquiv` (the identification
`𝒪_{Z,z} ≅ 𝒪_{X,z}/𝒥_z`) and `ι`; then `KLocallyRingedSpace.quotient` with `quotientι`, the
same with the induced `K`-structure. The local models (`localModel`) are the quotients of
`(G, 𝒜_G)` by `(f₁, …, f_k)`, and the closed subspaces of an analytic space (`closedSubspace`) are
the quotients by its finite-type ideal sheaves.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold

universe u

namespace AnalyticSpace

namespace QuotientSpace

variable (X : LocallyRingedSpace.{u}) (J : IdealSheaf X.𝒪)

/-- The stalk ideal `𝒥_z`, as an ideal of the local ring `𝒪_{X,z}` (the same ideal as
`J.stalkIdeal z`, typed over `X.presheaf.stalk z`). -/
abbrev stalkIdeal (z : X) : Ideal (X.presheaf.stalk z) := J.stalkIdeal z

/-- The stalk ideal `𝒥_z` consists of the germs at `z` of sections of `𝒥`. Restates
`IdealSheaf.mem_stalkIdeal_iff` (`Hironaka/Manifold/IdealSheaf/Basic.lean`) for the
abbreviation `stalkIdeal X J z`. -/
theorem mem_stalkIdeal_iff {z : X} {s : X.presheaf.stalk z} :
    s ∈ stalkIdeal X J z ↔ ∃ (V : Opens X) (hz : z ∈ V) (g : X.presheaf.obj (op V)),
      g ∈ J.carrier V ∧ X.presheaf.germ V z hz g = s :=
  J.mem_stalkIdeal_iff

/-- The support `S(𝒥) = supp (𝒪_X/𝒥) = {z | 𝒥_z ≠ 𝒪_{X,z}}` of the quotient sheaf [Hir64, Ch. 0,
§1] (the `cosupport` of the ideal sheaf), as a topological space. -/
@[implicit_reducible]
def support : TopCat.{u} := TopCat.of J.support

/-- The inclusion of the support into `X`. -/
@[implicit_reducible]
def ιTop : support X J ⟶ X.toTopCat := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The preimage in the support of an open subset of `X`. -/
abbrev preimage (W : Opens X) : Opens (support X J) := (Opens.map (ιTop X J)).obj W

/-- Membership in the trace `W ∩ S(𝒥)` of an open `W ⊆ X` on the support. -/
@[simp]
theorem mem_preimage {W : Opens X} {z : support X J} : z ∈ preimage X J W ↔ z.1 ∈ W := Iff.rfl

/-- The fibre `𝒪_{X,z}/𝒥_z` of the quotient at a point `z` of the support. -/
abbrev fiber (z : support X J) : Type u := X.presheaf.stalk z.1 ⧸ stalkIdeal X J z.1

instance (z : support X J) : Nontrivial (fiber X J z) :=
  Ideal.Quotient.nontrivial_iff.mpr (J.mem_support.mp z.2)

instance (z : support X J) : IsLocalRing (fiber X J z) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (stalkIdeal X J z.1)) Ideal.Quotient.mk_surjective

/-- The prelocal predicate on families `(s_z)_{z ∈ V}` of classes: "`s` is the family of the
classes `[a_z]` of one ambient section `a ∈ 𝒪_X(W)`". -/
abbrev prelocalPred : TopCat.PrelocalPredicate (fiber X J) where
  pred {V} s := ∃ (W : Opens X) (a : X.presheaf.obj (op W)),
    ∀ z : V, ∃ hz : z.1.1 ∈ W, s z = Ideal.Quotient.mk _ (X.presheaf.germ W z.1.1 hz a)
  res {_ _} i s hs := by
    obtain ⟨W, a, h⟩ := hs
    exact ⟨W, a, fun z => h (i z)⟩

/-- The local predicate "compatible germ family": locally the family of classes of one ambient
section — the sheafification of `prelocalPred`. -/
def localPred : TopCat.LocalPredicate (fiber X J) := (prelocalPred X J).sheafify

/-- The sheaf of sets of compatible germ families (`TopCat.subsheafToTypes`). -/
def sheafTypes : TopCat.Sheaf (Type u) (support X J) := TopCat.subsheafToTypes (localPred X J)

/-- The compatible germ families over `V` form a subring of the product of the fibres. -/
def sectionsSubring (V : Opens (support X J)) : Subring (∀ z : V, fiber X J z) where
  carrier := {s | (localPred X J).pred s}
  zero_mem' z := ⟨V, z.2, 𝟙 V, ⊤, 0, fun _ => ⟨trivial, by simp⟩⟩
  one_mem' z := ⟨V, z.2, 𝟙 V, ⊤, 1, fun _ => ⟨trivial, by simp⟩⟩
  add_mem' {s t} hs ht z := by
    obtain ⟨U₁, hz₁, i₁, W₁, a₁, h₁⟩ := hs z
    obtain ⟨U₂, hz₂, i₂, W₂, a₂, h₂⟩ := ht z
    refine ⟨U₁ ⊓ U₂, Opens.mem_inf.mpr ⟨hz₁, hz₂⟩, U₁.infLELeft U₂ ≫ i₁, W₁ ⊓ W₂,
      X.presheaf.map (W₁.infLELeft W₂).op a₁ + X.presheaf.map (W₁.infLERight W₂).op a₂,
      fun w => ?_⟩
    obtain ⟨hw₁, e₁⟩ := h₁ (U₁.infLELeft U₂ w)
    obtain ⟨hw₂, e₂⟩ := h₂ (U₁.infLERight U₂ w)
    refine ⟨Opens.mem_inf.mpr ⟨hw₁, hw₂⟩, ?_⟩
    beta_reduce at e₁ e₂
    change s (i₁ (U₁.infLELeft U₂ w)) + t (i₂ (U₁.infLERight U₂ w)) = _
    simp only [map_add, TopCat.Presheaf.germ_res_apply]
    exact congr_arg₂ (· + ·) e₁ e₂
  mul_mem' {s t} hs ht z := by
    obtain ⟨U₁, hz₁, i₁, W₁, a₁, h₁⟩ := hs z
    obtain ⟨U₂, hz₂, i₂, W₂, a₂, h₂⟩ := ht z
    refine ⟨U₁ ⊓ U₂, Opens.mem_inf.mpr ⟨hz₁, hz₂⟩, U₁.infLELeft U₂ ≫ i₁, W₁ ⊓ W₂,
      X.presheaf.map (W₁.infLELeft W₂).op a₁ * X.presheaf.map (W₁.infLERight W₂).op a₂,
      fun w => ?_⟩
    obtain ⟨hw₁, e₁⟩ := h₁ (U₁.infLELeft U₂ w)
    obtain ⟨hw₂, e₂⟩ := h₂ (U₁.infLERight U₂ w)
    refine ⟨Opens.mem_inf.mpr ⟨hw₁, hw₂⟩, ?_⟩
    beta_reduce at e₁ e₂
    change s (i₁ (U₁.infLELeft U₂ w)) * t (i₂ (U₁.infLERight U₂ w)) = _
    simp only [map_mul, TopCat.Presheaf.germ_res_apply]
    exact congr_arg₂ (· * ·) e₁ e₂
  neg_mem' {s} hs z := by
    obtain ⟨U₁, hz₁, i₁, W₁, a₁, h₁⟩ := hs z
    refine ⟨U₁, hz₁, i₁, W₁, -a₁, fun w => ?_⟩
    obtain ⟨hw₁, e₁⟩ := h₁ w
    refine ⟨hw₁, ?_⟩
    beta_reduce at e₁
    change -s (i₁ w) = _
    simp only [map_neg]
    exact congr_arg Neg.neg e₁

instance (V : (Opens (support X J))ᵒᵖ) : CommRing ((sheafTypes X J).presheaf.obj V) :=
  inferInstanceAs (CommRing (sectionsSubring X J (unop V)))

/-- The presheaf of commutative rings of compatible germ families (pointwise operations). -/
def presheafCommRing : TopCat.Presheaf CommRingCat.{u} (support X J) where
  obj V := CommRingCat.of ((sheafTypes X J).presheaf.obj V)
  map {_ _} i := CommRingCat.ofHom
    { toFun := (sheafTypes X J).presheaf.map i
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The sheaf of commutative rings `(𝒪_X/𝒥)|_{S(𝒥)}` of compatible germ families, a sheaf
because its sheaf of sets is one. -/
def sheafCommRing : TopCat.Sheaf CommRingCat.{u} (support X J) where
  obj := presheafCommRing X J
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget CommRingCat)]
    exact (sheafTypes X J).property

/-- Evaluation at `z` of a section over an open neighbourhood of `z`. -/
def evalAt (z : support X J) (U : OpenNhds z) :
    (presheafCommRing X J).obj (op U.1) ⟶ CommRingCat.of (fiber X J z) :=
  CommRingCat.ofHom
    { toFun := fun s => s.1 ⟨z, U.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- The evaluation of germs at `z`, `𝒪_{Z,z} → 𝒪_{X,z}/𝒥_z` (Mathlib's `stalkToFiber` lifted to
rings, as `smoothSheafCommRing.evalHom`). -/
def evalHom (z : support X J) :
    (presheafCommRing X J).stalk z ⟶ CommRingCat.of (fiber X J z) := by
  refine Limits.colimit.desc _ ⟨_, ⟨fun U => evalAt X J z (unop U), ?_⟩⟩
  cat_disch

/-- The stalk evaluation `evalHom` after the colimit leg at `U ∋ z` is the evaluation `evalAt` of
germ families at `z`. -/
theorem ι_evalHom (z : support X J) (U : (OpenNhds z)ᵒᵖ) :
    Limits.colimit.ι ((OpenNhds.inclusion z).op ⋙ presheafCommRing X J) U ≫ evalHom X J z =
      evalAt X J z (unop U) :=
  Limits.colimit.ι_desc _ _

/-- `evalHom` after the germ map at `z` is the evaluation of germ families at `z`. -/
theorem germ_comp_evalHom (U : Opens (support X J)) (z : support X J) (hz : z ∈ U) :
    (presheafCommRing X J).germ U z hz ≫ evalHom X J z = evalAt X J z ⟨U, hz⟩ :=
  ι_evalHom X J z (op ⟨U, hz⟩)

/-- `evalHom` of the germ at `z` of a germ family `s` is its value `s z ∈ 𝒪_{X,z}/𝒥_z`. -/
theorem evalHom_germ (U : Opens (support X J)) (z : support X J) (hz : z ∈ U)
    (s : (presheafCommRing X J).obj (op U)) :
    evalHom X J z ((presheafCommRing X J).germ U z hz s) = s.1 ⟨z, hz⟩ :=
  congr_arg (fun a => a s) (germ_comp_evalHom X J U z hz)

/-- The family of the classes `[a_z]` of an ambient section `a ∈ 𝒪_X(W)`, a section of the
quotient sheaf over the preimage of `W`. -/
def classFamily (W : Opens X) (a : X.presheaf.obj (op W)) :
    (presheafCommRing X J).obj (op (preimage X J W)) :=
  ⟨fun z => Ideal.Quotient.mk _ (X.presheaf.germ W z.1.1 ((mem_preimage X J).mp z.2) a),
    fun z => ⟨preimage X J W, z.2, 𝟙 _, W, a, fun w => ⟨(mem_preimage X J).mp w.2, rfl⟩⟩⟩

/-- `a ↦ ([a_z])_z` as a morphism of rings `𝒪_X(W) ⟶ 𝒪_Z(ι⁻¹ W)`. -/
def classHom (W : Opens X) :
    X.presheaf.obj (op W) ⟶ (presheafCommRing X J).obj (op (preimage X J W)) :=
  CommRingCat.ofHom
    { toFun := classFamily X J W
      map_one' := Subtype.ext (funext fun z => by
        change Ideal.Quotient.mk _ (X.presheaf.germ _ z.1.1 _ 1) = 1
        simp)
      map_mul' := fun a b => Subtype.ext (funext fun z => by
        change Ideal.Quotient.mk _ (X.presheaf.germ _ z.1.1 _ (a * b)) =
          Ideal.Quotient.mk _ (X.presheaf.germ _ z.1.1 _ a) *
            Ideal.Quotient.mk _ (X.presheaf.germ _ z.1.1 _ b)
        rw [map_mul, map_mul])
      map_zero' := Subtype.ext (funext fun z => by
        change Ideal.Quotient.mk _ (X.presheaf.germ _ z.1.1 _ 0) = 0
        simp)
      map_add' := fun a b => Subtype.ext (funext fun z => by
        change Ideal.Quotient.mk _ (X.presheaf.germ _ z.1.1 _ (a + b)) =
          Ideal.Quotient.mk _ (X.presheaf.germ _ z.1.1 _ a) +
            Ideal.Quotient.mk _ (X.presheaf.germ _ z.1.1 _ b)
        rw [map_add, map_add]) }

/-- Every class is the germ of a family: `evalHom` is surjective (as Mathlib's
`stalkToFiber_surjective`). -/
theorem evalHom_surjective (z : support X J) : Function.Surjective (evalHom X J z).hom := by
  intro q
  obtain ⟨σ, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨W, hzW, a, rfl⟩ := X.presheaf.exists_germ_eq σ
  refine ⟨(presheafCommRing X J).germ (preimage X J W) z ((mem_preimage X J).mpr hzW)
    (classFamily X J W a), ?_⟩
  change evalHom X J z _ = _
  rw [evalHom_germ]
  rfl

/-- Two families with the same class at `z` agree near `z`, because the difference of their
ambient representatives has germ in `𝒥_z`, hence is the germ of a section of `𝒥`, which lies in
`𝒥_y` for every `y` near `z`: `evalHom` is injective (as Mathlib's `stalkToFiber_injective`). -/
theorem evalHom_injective (z : support X J) : Function.Injective (evalHom X J z).hom := by
  refine (injective_iff_map_eq_zero (evalHom X J z).hom).mpr fun ξ hξ => ?_
  obtain ⟨V, hzV, s, rfl⟩ := (presheafCommRing X J).exists_germ_eq ξ
  change evalHom X J z _ = 0 at hξ
  rw [evalHom_germ] at hξ
  obtain ⟨U₁, hz₁, i₁, W, a, hWa⟩ := s.2 ⟨z, hzV⟩
  obtain ⟨hzW, e⟩ := hWa ⟨z, hz₁⟩
  have hmem : X.presheaf.germ W z.1 hzW a ∈ stalkIdeal X J z.1 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← e]
    exact hξ
  obtain ⟨V', hzV', g, hg, hge⟩ := (mem_stalkIdeal_iff X J).mp hmem
  obtain ⟨W', hzW', iV', iW, hres⟩ := X.presheaf.germ_eq z.1 hzV' hzW g a hge
  have hzW'' : z ∈ preimage X J W' := (mem_preimage X J).mpr hzW'
  have hzero : (presheafCommRing X J).map (U₁.infLELeft (preimage X J W') ≫ i₁).op s = 0 := by
    apply Subtype.ext
    funext w
    obtain ⟨hwW, ew⟩ := hWa (U₁.infLELeft (preimage X J W') w)
    beta_reduce at ew
    change s.1 (i₁ (U₁.infLELeft (preimage X J W') w)) = 0
    rw [ew, Ideal.Quotient.eq_zero_iff_mem]
    have hw' : (U₁.infLELeft (preimage X J W') w).1.1 ∈ W' :=
      (mem_preimage X J).mp (U₁.infLERight (preimage X J W') w).2
    have hgerm : X.presheaf.germ W (U₁.infLELeft (preimage X J W') w).1.1 hwW a =
        X.presheaf.germ V' (U₁.infLELeft (preimage X J W') w).1.1 (iV'.le hw') g := by
      rw [← TopCat.Presheaf.germ_res_apply X.presheaf iW _ hw', ← hres,
        TopCat.Presheaf.germ_res_apply]
    rw [hgerm]
    exact J.germ_mem_stalkIdeal _ hg
  have := TopCat.Presheaf.germ_res_apply (presheafCommRing X J)
    (U₁.infLELeft (preimage X J W') ≫ i₁) z (Opens.mem_inf.mpr ⟨hz₁, hzW''⟩) s
  rw [hzero, map_zero] at this
  exact this.symm

/-- The stalk of the quotient sheaf at `z` is `𝒪_{X,z}/𝒥_z`. -/
def stalkEquiv (z : support X J) : (presheafCommRing X J).stalk z ≃+* fiber X J z :=
  RingEquiv.ofBijective (evalHom X J z).hom ⟨evalHom_injective X J z, evalHom_surjective X J z⟩

instance (z : support X J) : IsLocalRing ((presheafCommRing X J).stalk z) :=
  (stalkEquiv X J z).symm.isLocalRing

/-- The locally ringed space `(S(𝒥), (𝒪_X/𝒥)|_{S(𝒥)})` [Hir64, Ch. 0, §1], [BM97, §3]. -/
@[implicit_reducible]
def quotientSpace : LocallyRingedSpace.{u} where
  carrier := support X J
  presheaf := presheafCommRing X J
  IsSheaf := (sheafCommRing X J).property
  isLocalRing := fun _ => inferInstance

/-- The canonical morphism of presheafed spaces `(S(𝒥), 𝒪_X/𝒥) ⟶ X`: the inclusion of the
support with `a ↦ ([a_z])_z` on sections. -/
@[implicit_reducible]
def ιHom : (quotientSpace X J).toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := ιTop X J
  c :=
    { app := fun W => classHom X J (unop W)
      naturality := fun W W' i => by
        ext a
        apply Subtype.ext
        funext z
        change Ideal.Quotient.mk _ (X.presheaf.germ _ z.1.1 _ (X.presheaf.map i a)) =
          Ideal.Quotient.mk _ (X.presheaf.germ _ z.1.1 _ a)
        rw [TopCat.Presheaf.germ_res_apply'] }

/-- The stalk map of the canonical morphism, followed by the identification of the stalk with
`𝒪_{X,z}/𝒥_z`, is the quotient map. -/
theorem stalkMap_comp_evalHom (z : support X J) :
    (ιHom X J).stalkMap z ≫ evalHom X J z =
      CommRingCat.ofHom (Ideal.Quotient.mk (stalkIdeal X J z.1)) := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hzU => ?_
  rw [PresheafedSpace.stalkMap_germ_assoc]
  erw [germ_comp_evalHom]
  ext a
  rfl

/-- The stalk map at `z` of `ι : (𝒪_X/𝒥)|_{S(𝒥)} → X`, read through `evalHom`, is the quotient
map `𝒪_{X,z} → 𝒪_{X,z}/𝒥_z`. -/
theorem evalHom_stalkMap (z : support X J) (σ : X.presheaf.stalk z.1) :
    evalHom X J z ((ιHom X J).stalkMap z σ) = Ideal.Quotient.mk (stalkIdeal X J z.1) σ :=
  congr_arg (fun f => f σ) (stalkMap_comp_evalHom X J z)

instance isLocalHom_stalkMap (z : support X J) : IsLocalHom ((ιHom X J).stalkMap z).hom where
  map_nonunit r hr := by
    have hmk : IsLocalHom (Ideal.Quotient.mk (stalkIdeal X J z.1)) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    apply hmk.map_nonunit
    rw [← evalHom_stalkMap X J z r]
    exact hr.map (evalHom X J z).hom

/-- The canonical morphism of locally ringed spaces `(S(𝒥), 𝒪_X/𝒥) ⟶ X`, the closed embedding of
the subspace; its stalk maps are the quotient maps. -/
@[implicit_reducible]
def ι : quotientSpace X J ⟶ X := ⟨ιHom X J, fun z => isLocalHom_stalkMap X J z⟩

end QuotientSpace

namespace KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- The quotient of a `K`-local-ringed space by an ideal sheaf, with the `K`-structure induced
along the canonical morphism. The closed subspaces of an analytic `K`-space are these
(`closedSubspace`). -/
def quotient (X : KLocallyRingedSpace.{u} K) (J : IdealSheaf X.toLocallyRingedSpace.𝒪) :
    KLocallyRingedSpace.{u} K where
  toLocallyRingedSpace := QuotientSpace.quotientSpace X.toLocallyRingedSpace J
  algebraMap := (LocallyRingedSpace.Γ.map
    (QuotientSpace.ι X.toLocallyRingedSpace J).op).hom.comp X.algebraMap

/-- The canonical morphism of the quotient as a `K`-morphism. -/
def quotientι (X : KLocallyRingedSpace.{u} K) (J : IdealSheaf X.toLocallyRingedSpace.𝒪) :
    X.quotient J ⟶ X :=
  ⟨QuotientSpace.ι X.toLocallyRingedSpace J, rfl⟩

end KLocallyRingedSpace

end AnalyticSpace
