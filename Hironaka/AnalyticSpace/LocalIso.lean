/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.HomOfSectionsCompat
public import Hironaka.AnalyticSpace.Complexification
import Hironaka.AnalyticSpace.Glue
import Hironaka.AnalyticSpace.HomOfSections
import Hironaka.AnalyticSpace.HomOfSectionsModel
import Hironaka.AnalyticSpace.IsoCriterion
import Hironaka.AnalyticSpace.Lemmas
import Hironaka.AnalyticSpace.Propagation
import Hironaka.AnalyticSpace.Quotient
import Hironaka.AnalyticSpace.QuotientBot
import Hironaka.AnalyticSpace.Restrict.Defs
import Hironaka.AnalyticSpace.StalkMapLemmas
import Hironaka.Manifold.IdealSheaf.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The local isomorphism criterion for analytic `K`-spaces

A `K`-morphism `φ : X ⟶ Y` of analytic `K`-spaces whose stalk map `φ^*_x : 𝒪_{Y,φ x} → 𝒪_{X,x}` is
bijective restricts to a `K`-isomorphism `X|U ≅ Y|V` of open neighbourhoods of `x` and `φ x`
(`AnalyticSpace.exists_isIso_restrictTo_of_bijective_stalkMap`). Hironaka's analytic `K`-spaces are
locally the closed subspaces `V(f) ⊆ G ⊆ Kⁿ` of opens of `Kⁿ` cut out by finitely many analytic
functions, with the structure sheaf `𝒜_G/(f)` [Hir64, Ch. 0, §1, pp. 119–120]; the local rings
determine the spaces near a point — the content of the equivalence between germs of analytic
spaces and analytic algebras [GR84, Ch. 1], of which this is the weakest form, the one Hironaka
uses tacitly when a local `Kⁿ`-coordination is recognised on the local rings
[Hir64, Ch. 0, §1, p. 120]. Not proved in the sources; the argument:

*Construction of the local inverse.* Take a chart `eX : X|U₁ ≅ V(f') ⊆ G' ⊆ Kⁿ` at `x`, with chart
map `κ = eX.hom ≫ ι : X|U₁ ⟶ (Kⁿ, 𝒜)`. The `n` coordinate germs of `κ` at `x` have preimages under
the bijection `φ^*_x`, realised as sections `t_j` of `Y` near `φ x`; the `t_j` are the
coordinates of a unique `K`-morphism `χ₀ : Y|W → (Kⁿ, 𝒜)` (`AnalyticSpace.homOfSections`,
`Hironaka/AnalyticSpace/HomOfSections.lean`). Its base point at `φ x` is `κ(x) ∈ G'` (the coordinate
germs of `κ` at `x` and of `χ₀` at `φ x` correspond under the local homomorphism `φ^*_x`, so the
values agree, `stalkMap_sigmaStalk_eq_of_coord`), and the pullbacks of the equations `f'_i` along
`χ₀` have zero germs at `φ x` (they are the `(φ^*_x)⁻¹`-images of the pullbacks along `κ`, which
vanish on the model, `stalkMap_localModel_ι_germ_eq_zero`); shrinking `W` to `W₂`, `χ₀` lands in
`G'` and kills the `f'_i`, so it factors through the model by the functoriality of quotients along
the zero ideal sheaf (`quotientMap`, `quotientBotIso`), and `χ = (…) ≫ eX.inv : Y|W₂ ⟶ X|U₁` has
the coordinate identity `φ^*_x(germ (χ ≫ κ)^* z_j) = germ κ^* z_j`
(`exists_hom_coord_of_bijective_stalkMap`).

*The two inverse identities.* Germ identities between finitely many sections spread to a
neighbourhood (`exists_opens_forall_germ_eq`, `exists_opens_forall_stalkMap_germ_eq`). A
`K`-morphism into `(Kⁿ, 𝒜)` is determined by its coordinate pullbacks (`hom_ext_of_coord`) and the
chart map is a monomorphism (`Hom.ext_of_comp_localModel_ι`), so equality of morphisms into a
chart of `A` reduces to germ identities of coordinates
(`restrictTo_comp_eq_of_stalkMap_germ_pullbackΓ_coord`, with the bookkeeping lemma
`germ_pullbackΓ_restrictTo`: the germ of a pullback along a restriction `g|U` is the stalk map of
`g` on the germ). This gives `φ|S ≫ χ = incl` on an open `S ∋ x`; then the coordinates of
`χ ≫ φ|U₁ ≫ κY` and of `κY` (`κY` the chart map of `Y` at `φ x`) have the same germs at `φ x`
(apply the injective `φ^*_x` and use the first identity), spread to an open `T ∋ φ x`, and give
`incl ≫ χ ≫ φ|U₁ = incl` on `Y|T`.

*Assembly* (`exists_isIso_restrictTo_of_inverse`). With `U = S ∩ φ⁻¹T` and
`V = {b ∈ T | χ b ∈ U}`, the base map of `φ|U : X|U ⟶ Y|V` is a homeomorphism with inverse `χ`,
and the stalk maps are bijective: surjective by the first identity (`φ|S^* ∘ χ^* = id`), injective
by the second (`χ^* ∘ φ|U₁^* = id`); the criterion `isIso_of_isIso_base_of_stalkMap_bijective`
(`Hironaka/AnalyticSpace/IsoCriterion.lean`) concludes. Mathlib's `stalkMap_comp`,
`stalkMap_germ_apply`, `germ_eq` and `section_ext` carry the stalk computations. Used by
`Hironaka/AnalyticSpace/IsoOverOpen.lean` and `Hironaka/Manifold/Sequence/Restrict/`.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold

universe u

namespace AnalyticSpace

open KLocallyRingedSpace

variable {K : Type} [RCLike K]

namespace KLocallyRingedSpace

/-- The closed immersion `(S(𝒥), 𝒪_X/𝒥) ⟶ X` of a quotient is a monomorphism of `K`-spaces: two
`K`-morphisms into the quotient with the same composite into `X` are equal (the base map of the
immersion is injective, its stalk maps are surjective, and a morphism of locally ringed spaces
into a sheaf-valued target is determined by its base map and its stalk maps). -/
theorem Hom.ext_of_comp_quotientι {Z X : KLocallyRingedSpace.{u} K}
    (J : IdealSheaf X.toLocallyRingedSpace.𝒪) {f g : Z ⟶ X.quotient J}
    (h : f ≫ quotientι X J = g ≫ quotientι X J) : f = g := by
  have hb : f.1.base = g.1.base := by
    ext z
    have h1 := congrArg (fun φ : Z ⟶ X => Hom.toFun φ z) h
    exact Subtype.ext h1
  obtain ⟨⟨⟨b₁, c₁⟩, p₁⟩, hf⟩ := f
  obtain ⟨⟨⟨b₂, c₂⟩, p₂⟩, hg⟩ := g
  change b₁ = b₂ at hb
  subst hb
  let f₁ : Z.toLocallyRingedSpace ⟶ (X.quotient J).toLocallyRingedSpace := ⟨⟨b₁, c₁⟩, p₁⟩
  let f₂ : Z.toLocallyRingedSpace ⟶ (X.quotient J).toLocallyRingedSpace := ⟨⟨b₁, c₂⟩, p₂⟩
  have h1 : f₁ ≫ (quotientι X J).1 = f₂ ≫ (quotientι X J).1 := congrArg Subtype.val h
  have hc : c₁ = c₂ := by
    ext U s
    apply TopCat.Presheaf.section_ext Z.toLocallyRingedSpace.𝒪
    intro z hz
    have hh : HEq ((f₁ ≫ (quotientι X J).1).stalkMap z) ((f₂ ≫ (quotientι X J).1).stalkMap z) := by
      rw [h1]
    have hsz : (f₁ ≫ (quotientι X J).1).stalkMap z = (f₂ ≫ (quotientι X J).1).stalkMap z :=
      eq_of_heq hh
    rw [LocallyRingedSpace.stalkMap_comp, LocallyRingedSpace.stalkMap_comp] at hsz
    have hepi : Epi ((quotientι X J).1.stalkMap (b₁ z)) :=
      ConcreteCategory.epi_of_surjective _
        (QuotientSpace.stalkMap_surjective X.toLocallyRingedSpace J (b₁ z))
    have hst : f₁.stalkMap z = f₂.stalkMap z := (cancel_epi _).mp hsz
    refine (PresheafedSpace.stalkMap_germ_apply f₁.toHom U z hz s).symm.trans ?_
    refine Eq.trans ?_ (PresheafedSpace.stalkMap_germ_apply f₂.toHom U z hz s)
    exact congrArg (fun ψ : (X.quotient J).toLocallyRingedSpace.presheaf.stalk (b₁ z) ⟶
      Z.toLocallyRingedSpace.presheaf.stalk z => ψ _) hst
  subst hc
  rfl

/-- Two `K`-morphisms into `Y|U` with the same composite into `Y` are equal; the composite of two
open immersions with a closed immersion of a quotient is a monomorphism: the chart map
`X|U ≅ V(f) ⟶ (G, 𝒜_G) ⟶ (Kⁿ, 𝒜)` of a local coordination is a monomorphism of `K`-spaces. -/
theorem Hom.ext_of_comp_localModel_ι {Z A : KLocallyRingedSpace.{u} K} {n : ℕ}
    {G : Opens (Kn.{u} K n)} {k : ℕ} {f : Fin k → AnalyticFun K n G}
    (e : KIso A (localModel K n G f))
    {φ ψ : Z ⟶ A} (h : φ ≫ e.hom ≫ localModel.ι K n G f = ψ ≫ e.hom ≫ localModel.ι K n G f) :
    φ = ψ := by
  have h1 : (φ ≫ e.hom) ≫ quotientι _ _ = (ψ ≫ e.hom) ≫ quotientι _ _ := by
    apply Hom.ext_of_comp_ofRestrict
    simpa only [Category.assoc, localModel.ι] using h
  have h2 : φ ≫ e.hom = ψ ≫ e.hom := Hom.ext_of_comp_quotientι _ h1
  exact (cancel_mono e.hom).mp h2

/-- The functoriality of quotients commutes with the canonical morphisms. -/
theorem quotientMap_comp_quotientι {X' X : KLocallyRingedSpace.{u} K} (ψ : X' ⟶ X)
    (J' : IdealSheaf X'.toLocallyRingedSpace.𝒪) (J : IdealSheaf X.toLocallyRingedSpace.𝒪)
    (h : QuotientSpace.Compat ψ.1 J' J) :
    quotientMap ψ J' J h ≫ quotientι X J = quotientι X' J' ≫ ψ :=
  Hom.ext (by
    rw [Hom.comp_val, Hom.comp_val, quotientMap_val]
    exact QuotientSpace.map_comp_ι ψ.1 J' J h)

end KLocallyRingedSpace

/-- The equations of a local model pull back to zero along its closed embedding into `(Kⁿ, 𝒜)`: the
germ of `f i` at the image of a point of the model is killed by the stalk map. -/
theorem stalkMap_localModel_ι_germ_eq_zero {n : ℕ} (G : Opens (Kn.{u} K n)) {k : ℕ}
    (f : Fin k → AnalyticFun K n G) (z : localModel K n G f) (i : Fin k) :
    ((localModel.ι K n G f).1.stalkMap z).hom
      ((affine K n).toLocallyRingedSpace.presheaf.germ G z.1.1 z.1.2 (f i)) = 0 := by
  change (((quotientι _ _).1 ≫ (ofRestrict (affine K n) G).1).stalkMap z).hom _ = 0
  rw [LocallyRingedSpace.stalkMap_comp]
  change ((quotientι _ _).1.stalkMap z).hom (((ofRestrict (affine K n) G).1.stalkMap z.1).hom
    ((affine K n).toLocallyRingedSpace.presheaf.germ G z.1.1 z.1.2 (f i))) = 0
  have h1 := stalkMap_ofRestrict_germ _ _ G z.1 (f i)
  rw [h1]
  apply QuotientSpace.evalHom_injective (analyticSpaceOfOpen K n G).toLocallyRingedSpace
    (modelIdeal K n G f) z
  refine (QuotientSpace.evalHom_stalkMap _ _ z _).trans ?_
  refine Eq.trans ?_ (map_zero (QuotientSpace.evalHom
    (analyticSpaceOfOpen K n G).toLocallyRingedSpace (modelIdeal K n G f) z).hom).symm
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact (IdealSheaf.stalkIdeal_ofGlobal (analyticSpaceOfOpen K n G).toLocallyRingedSpace.𝒪
    (fun j => toGlobal K n G (f j)) z.1).symm.le (Ideal.subset_span ⟨i, rfl⟩)

/-- The equations of a local model pull back to zero along `e ≫ ι` for a `K`-isomorphism `e` onto
the model. -/
theorem stalkMap_comp_localModel_ι_germ_eq_zero {A : KLocallyRingedSpace.{u} K} {n : ℕ}
    (G : Opens (Kn.{u} K n)) {k : ℕ} (f : Fin k → AnalyticFun K n G)
    (e : KIso A (localModel K n G f)) (a : A) (hpG : (e.hom ≫ localModel.ι K n G f).1.base a ∈ G)
    (i : Fin k) :
    ((e.hom ≫ localModel.ι K n G f).1.stalkMap a).hom
      ((affine K n).toLocallyRingedSpace.presheaf.germ G _ hpG (f i)) = 0 := by
  have h4 := LocallyRingedSpace.stalkMap_comp e.hom.1 (localModel.ι K n G f).1 a
  change ((e.hom.1 ≫ (localModel.ι K n G f).1).stalkMap a).hom _ = 0
  rw [h4]
  change (e.hom.1.stalkMap a).hom (((localModel.ι K n G f).1.stalkMap (e.hom.1.base a)).hom
    ((affine K n).toLocallyRingedSpace.presheaf.germ G (e.hom.1.base a).1.1 (e.hom.1.base a).1.2
      (f i))) = 0
  rw [stalkMap_localModel_ι_germ_eq_zero, map_zero]

/-- Equal morphisms have equal stalk maps on germs (the point of the germ transported along the
equality; a `Prop`-level congruence avoiding the dependent rewrite). -/
theorem stalkMap_germ_congr {Z B : KLocallyRingedSpace.{u} K} {ψ ψ' : Z ⟶ B} (h : ψ = ψ') (z : Z)
    {V : Opens B} (hψ : ψ.1.base z ∈ V) (hψ' : ψ'.1.base z ∈ V)
    (u : B.toLocallyRingedSpace.presheaf.obj (op V)) :
    (ψ.1.stalkMap z).hom (B.toLocallyRingedSpace.presheaf.germ V (ψ.1.base z) hψ u) =
      (ψ'.1.stalkMap z).hom (B.toLocallyRingedSpace.presheaf.germ V (ψ'.1.base z) hψ' u) := by
  subst h
  rfl

/-- The germ at `a ∈ U` of the pullback of a global section `u` of `B|U'` along the restriction
`g|U : A|U ⟶ B|U'` of `g : A ⟶ B` is the image under the stalk map `g^*_a` of the germ of `u` at
`g a` (both read in the stalks of `A` and `B`). -/
theorem germ_pullbackΓ_restrictTo {A B : KLocallyRingedSpace.{u} K} (g : A ⟶ B) (U : Opens A)
    (U' : Opens B) (h : ∀ a ∈ U, KLocallyRingedSpace.Hom.toFun g a ∈ U') {a : A} (ha : a ∈ U)
    (u : LocallyRingedSpace.Γ.obj (op (B.restrictOpen U').toLocallyRingedSpace)) :
    A.toLocallyRingedSpace.presheaf.germ (imgOpens A U ⊤) a (mem_imgOpens_of_mem A ha trivial)
        ((Hom.restrictTo g U U' h).pullbackΓ u) =
      (g.1.stalkMap a).hom (B.toLocallyRingedSpace.presheaf.germ (imgOpens B U' ⊤) (g.1.base a)
        (mem_imgOpens_of_mem B (h a ha) trivial) u) := by
  refine (resIso_hom_germ A U ha ⊤ trivial ((Hom.restrictTo g U U' h).pullbackΓ u)).symm.trans ?_
  have h2 := LocallyRingedSpace.stalkMap_germ_apply (Hom.restrictTo g U U' h).1 ⊤ ⟨a, ha⟩ trivial u
  have h3 : ∀ w : B.restrictOpen U',
      (B.restrictOpen U').toLocallyRingedSpace.presheaf.germ ⊤ w trivial u =
        ((ofRestrict B U').1.stalkMap w).hom (B.toLocallyRingedSpace.presheaf.germ
          (imgOpens B U' ⊤) w.1 (mem_imgOpens_of_mem B w.2 trivial) u) := by
    intro w
    rw [← resIso_inv_eq_stalkMap_ofRestrict B U' w]
    exact ((congrArg (fun y => (resIso B U' w.2).inv y)
      (resIso_hom_germ B U' w.2 ⊤ trivial u)).symm.trans (Iso.hom_inv_id_apply _ _)).symm
  have h5 : ∀ hm : (ofRestrict A U ≫ g).1.base ⟨a, ha⟩ ∈ imgOpens B U' ⊤,
      ((ofRestrict A U ≫ g).1.stalkMap ⟨a, ha⟩).hom (B.toLocallyRingedSpace.presheaf.germ
          (imgOpens B U' ⊤) ((ofRestrict A U ≫ g).1.base ⟨a, ha⟩) hm u) =
        ((ofRestrict A U).1.stalkMap ⟨a, ha⟩).hom ((g.1.stalkMap a).hom
          (B.toLocallyRingedSpace.presheaf.germ (imgOpens B U' ⊤) (g.1.base a)
            (mem_imgOpens_of_mem B (h a ha) trivial) u)) := by
    intro hm
    have h4 := LocallyRingedSpace.stalkMap_comp (ofRestrict A U).1 g.1 (⟨a, ha⟩ : A.restrictOpen U)
    change (((ofRestrict A U).1 ≫ g.1).stalkMap ⟨a, ha⟩).hom (B.toLocallyRingedSpace.presheaf.germ
      (imgOpens B U' ⊤) (((ofRestrict A U).1 ≫ g.1).base ⟨a, ha⟩) hm u) = _
    rw [h4]
    rfl
  have h6 := (stalkMap_germ_congr (V := imgOpens B U' ⊤)
    (Hom.restrictTo_comp_ofRestrict g U U' h) ⟨a, ha⟩
    (mem_imgOpens_of_mem B ((Hom.restrictTo g U U' h).1.base ⟨a, ha⟩).2 trivial)
    (mem_imgOpens_of_mem B (h a ha) trivial) u).trans (h5 _)
  have h4' := LocallyRingedSpace.stalkMap_comp (Hom.restrictTo g U U' h).1 (ofRestrict B U').1
    (⟨a, ha⟩ : A.restrictOpen U)
  change ((((Hom.restrictTo g U U' h).1 ≫ (ofRestrict B U').1)).stalkMap ⟨a, ha⟩).hom
    (B.toLocallyRingedSpace.presheaf.germ (imgOpens B U' ⊤)
      (((Hom.restrictTo g U U' h).1 ≫ (ofRestrict B U').1).base ⟨a, ha⟩) _ u) = _ at h6
  rw [h4'] at h6
  change ((Hom.restrictTo g U U' h).1.stalkMap ⟨a, ha⟩).hom (((ofRestrict B U').1.stalkMap
    ((Hom.restrictTo g U U' h).1.base ⟨a, ha⟩)).hom (B.toLocallyRingedSpace.presheaf.germ
      (imgOpens B U' ⊤) ((Hom.restrictTo g U U' h).1.base ⟨a, ha⟩).1 _ u)) = _ at h6
  rw [← h3 ((Hom.restrictTo g U U' h).1.base ⟨a, ha⟩), h2] at h6
  change (resIso A U ha).hom ((A.restrictOpen U).toLocallyRingedSpace.presheaf.germ
    ((Opens.map (Hom.restrictTo g U U' h).1.base).obj ⊤) ⟨a, ha⟩ trivial
      ((Hom.restrictTo g U U' h).1.c.app (op ⊤) u)) = _
  rw [h6, ← resIso_inv_eq_stalkMap_ofRestrict A U ⟨a, ha⟩]
  exact Iso.inv_hom_id_apply _ _

/-- Two finite families of sections with the same germs at `x` have the same germs on a
neighbourhood of `x`. -/
theorem exists_opens_forall_germ_eq {T : TopCat.{u}} (F : T.Presheaf CommRingCat.{u})
    {U V : Opens T} (x : T) (hxU : x ∈ U) (hxV : x ∈ V) {n : ℕ} (u : Fin n → F.obj (op U))
    (v : Fin n → F.obj (op V)) (h : ∀ i, F.germ U x hxU (u i) = F.germ V x hxV (v i)) :
    ∃ (W : Opens T) (_ : x ∈ W) (hWU : W ≤ U) (hWV : W ≤ V),
      ∀ (y : T) (hy : y ∈ W) (i : Fin n),
        F.germ U y (hWU hy) (u i) = F.germ V y (hWV hy) (v i) := by
  choose W hxW iU iV e using fun i => F.germ_eq x hxU hxV (u i) (v i) (h i)
  refine ⟨U ⊓ V ⊓ ⨅ i, W i, ⟨⟨hxU, hxV⟩, mem_iInf_opens.mpr hxW⟩, fun _ hy => hy.1.1,
    fun _ hy => hy.1.2, fun y hy i => ?_⟩
  have hyW : y ∈ W i := mem_iInf_opens.mp hy.2 i
  rw [← F.germ_res_apply (iU i) y hyW, e i, F.germ_res_apply (iV i) y hyW]

/-- A finite family of identities `f^*_x (germ u_i) = germ v_i` between germs at `x` holds at every
point of a neighbourhood of `x`. -/
theorem exists_opens_forall_stalkMap_germ_eq {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X)
    {U : Opens Y} {V : Opens X} (hxU : f.base x ∈ U) (hxV : x ∈ V) {n : ℕ}
    (u : Fin n → Y.presheaf.obj (op U)) (v : Fin n → X.presheaf.obj (op V))
    (h : ∀ i, (f.stalkMap x).hom (Y.presheaf.germ U (f.base x) hxU (u i)) =
      X.presheaf.germ V x hxV (v i)) :
    ∃ (W : Opens X) (_ : x ∈ W) (hWU : ∀ a ∈ W, f.base a ∈ U) (hWV : W ≤ V),
      ∀ (a : X) (ha : a ∈ W) (i : Fin n),
        (f.stalkMap a).hom (Y.presheaf.germ U (f.base a) (hWU a ha) (u i)) =
          X.presheaf.germ V a (hWV ha) (v i) := by
  have h' : ∀ i, X.presheaf.germ ((Opens.map f.base).obj U) x hxU (f.c.app (op U) (u i)) =
      X.presheaf.germ V x hxV (v i) := fun i =>
    (LocallyRingedSpace.stalkMap_germ_apply f U x hxU (u i)).symm.trans (h i)
  obtain ⟨W, hxW, hWU, hWV, hW⟩ := exists_opens_forall_germ_eq X.presheaf x hxU hxV _ _ h'
  refine ⟨W, hxW, fun a ha => hWU ha, hWV, fun a ha i => ?_⟩
  exact (LocallyRingedSpace.stalkMap_germ_apply f U a (hWU ha) (u i)).trans (hW a ha i)

/-- A one-sided inverse identity from coordinates: if the stalk maps of `g : Z ⟶ Z'` carry the
coordinate germs of `α ≫ κ` (`κ = e.hom ≫ ι` the chart map of `A`) at `g z` to those of `β ≫ κ` at
`z` for every `z ∈ S`, then `g|S ≫ α = (S ⊆ U') ≫ β` as morphisms `Z|S ⟶ A` — the chart map is a
monomorphism (`Hom.ext_of_comp_localModel_ι`) and a morphism into `Kⁿ` is determined by its
coordinate pullbacks (`hom_ext_of_coord`), which are determined by their germs. -/
theorem restrictTo_comp_eq_of_stalkMap_germ_pullbackΓ_coord {Z : AnalyticSpace.{u} K}
    {Z' A : KLocallyRingedSpace.{u} K} (g : Z.toKLocallyRingedSpace ⟶ Z') {S : Opens Z}
    {W : Opens Z'} (hSW : ∀ z ∈ S, KLocallyRingedSpace.Hom.toFun g z ∈ W) {U' : Opens Z}
        (hSU' : S ≤ U')
    (α : Z'.restrictOpen W ⟶ A) (β : Z.toKLocallyRingedSpace.restrictOpen U' ⟶ A) {n : ℕ}
    {G : Opens (Kn.{u} K n)} {k : ℕ} {f : Fin k → AnalyticFun K n G}
    (e : KIso A (localModel K n G f))
    (h : ∀ (z : Z) (hz : z ∈ S) (j : Fin n),
      (g.1.stalkMap z).hom (Z'.toLocallyRingedSpace.presheaf.germ (imgOpens Z' W ⊤) (g.1.base z)
          (mem_imgOpens_of_mem Z' (hSW z hz) trivial)
          ((α ≫ e.hom ≫ localModel.ι K n G f).pullbackΓ (coordSection K n j))) =
        Z.toLocallyRingedSpace.presheaf.germ (imgOpens Z.toKLocallyRingedSpace U' ⊤) z
          (mem_imgOpens_of_mem _ (hSU' hz) trivial)
          ((β ≫ e.hom ≫ localModel.ι K n G f).pullbackΓ (coordSection K n j))) :
    Hom.restrictTo g S W hSW ≫ α = restrictOpenIncl Z.toKLocallyRingedSpace hSU' ≫ β := by
  apply Hom.ext_of_comp_localModel_ι e
  refine AnalyticSpace.hom_ext_of_coord (Z.restrictOpen S) _ _ fun j => ?_
  rw [Category.assoc, Category.assoc]
  refine (Hom.pullbackΓ_comp (Hom.restrictTo g S W hSW) (α ≫ e.hom ≫ localModel.ι K n G f)
    (coordSection K n j)).trans (Eq.trans ?_ (Hom.pullbackΓ_comp
      (restrictOpenIncl Z.toKLocallyRingedSpace hSU') (β ≫ e.hom ≫ localModel.ι K n G f)
      (coordSection K n j)).symm)
  refine TopCat.Presheaf.section_ext Z.toLocallyRingedSpace.𝒪
    (imgOpens Z.toKLocallyRingedSpace S ⊤) _ _ fun z hz => ?_
  have hzS : z ∈ S := imgOpens_top_le Z.toKLocallyRingedSpace S hz
  have hL := germ_pullbackΓ_restrictTo g S W hSW hzS
    ((α ≫ e.hom ≫ localModel.ι K n G f).pullbackΓ (coordSection K n j))
  have hR := germ_pullbackΓ_restrictTo (𝟙 Z.toKLocallyRingedSpace) S U' (fun _ hz => hSU' hz) hzS
    ((β ≫ e.hom ≫ localModel.ι K n G f).pullbackΓ (coordSection K n j))
  refine hL.trans ((h z hzS j).trans (Eq.trans ?_ hR.symm))
  change _ = ((𝟙 Z.toLocallyRingedSpace : Z.toLocallyRingedSpace ⟶ _).stalkMap z).hom
    (Z.toLocallyRingedSpace.presheaf.germ (imgOpens Z.toKLocallyRingedSpace U' ⊤) z
      (mem_imgOpens_of_mem _ (hSU' hzS) trivial) _)
  rw [LocallyRingedSpace.stalkMap_id]
  rfl

/-- The germ of the pullback of a section of `A|U'` along the inclusion `A|U ⟶ A|U'`, `U ≤ U'`. -/
theorem germ_pullbackΓ_restrictOpenIncl (A : KLocallyRingedSpace.{u} K) {U U' : Opens A}
    (h : U ≤ U') {a : A} (ha : a ∈ U)
    (u : LocallyRingedSpace.Γ.obj (op (A.restrictOpen U').toLocallyRingedSpace)) :
    A.toLocallyRingedSpace.presheaf.germ (imgOpens A U ⊤) a (mem_imgOpens_of_mem A ha trivial)
        ((restrictOpenIncl A h).pullbackΓ u) =
      A.toLocallyRingedSpace.presheaf.germ (imgOpens A U' ⊤) a
        (mem_imgOpens_of_mem A (h ha) trivial) u := by
  refine (germ_pullbackΓ_restrictTo (𝟙 A) U U' (fun _ ha => h ha) ha u).trans ?_
  change ((𝟙 A.toLocallyRingedSpace : A.toLocallyRingedSpace ⟶ _).stalkMap a).hom _ = _
  rw [LocallyRingedSpace.stalkMap_id]
  rfl

/-- Equal morphisms have stalk maps that are injective together. -/
theorem injective_stalkMap_congr {A B : KLocallyRingedSpace.{u} K} {φ ψ : A ⟶ B} (h : φ = ψ)
    (a : A) :
    Function.Injective (φ.1.stalkMap a).hom ↔ Function.Injective (ψ.1.stalkMap a).hom := by
  subst h
  exact Iff.rfl

/-- Equal morphisms have stalk maps that are surjective together. -/
theorem surjective_stalkMap_congr {A B : KLocallyRingedSpace.{u} K} {φ ψ : A ⟶ B} (h : φ = ψ)
    (a : A) :
    Function.Surjective (φ.1.stalkMap a).hom ↔ Function.Surjective (ψ.1.stalkMap a).hom := by
  subst h
  exact Iff.rfl

/-- Injectivity of the stalk map of a composite passes to the second factor. -/
theorem injective_stalkMap_of_comp {A B C : KLocallyRingedSpace.{u} K} (f : A ⟶ B) (g : B ⟶ C)
    (a : A) (h : Function.Injective ((f ≫ g).1.stalkMap a).hom) :
    Function.Injective (g.1.stalkMap (f.1.base a)).hom := by
  rw [Hom.comp_val, LocallyRingedSpace.stalkMap_comp] at h
  change Function.Injective (⇑(f.1.stalkMap a).hom ∘ ⇑(g.1.stalkMap (f.1.base a)).hom) at h
  exact h.of_comp

/-- Surjectivity of the stalk map of a composite passes to the first factor. -/
theorem surjective_stalkMap_of_comp {A B C : KLocallyRingedSpace.{u} K} (f : A ⟶ B) (g : B ⟶ C)
    (a : A) (h : Function.Surjective ((f ≫ g).1.stalkMap a).hom) :
    Function.Surjective (f.1.stalkMap a).hom := by
  rw [Hom.comp_val, LocallyRingedSpace.stalkMap_comp] at h
  change Function.Surjective (⇑(f.1.stalkMap a).hom ∘ ⇑(g.1.stalkMap (f.1.base a)).hom) at h
  exact h.of_comp

/-- The stalk maps of the inclusion `A|U ⟶ A|U'` of open subspaces are bijective. -/
theorem bijective_stalkMap_restrictOpenIncl (A : KLocallyRingedSpace.{u} K) {U U' : Opens A}
    (h : U ≤ U') (a : A.restrictOpen U) :
    Function.Bijective ((restrictOpenIncl A h).1.stalkMap a).hom := by
  refine bijective_stalkMap_restrictTo (𝟙 A) U U' _ a ?_
  change Function.Bijective ((𝟙 A.toLocallyRingedSpace : A.toLocallyRingedSpace ⟶ _).stalkMap _).hom
  rw [LocallyRingedSpace.stalkMap_id]
  exact Function.bijective_id

/-- Surjectivity of a stalk map of `g|U : A|U ⟶ B|U'` gives that of the stalk map of `g`. -/
theorem surjective_stalkMap_of_restrictTo {A B : KLocallyRingedSpace.{u} K} (g : A ⟶ B)
    (U : Opens A) (U' : Opens B) (h : ∀ a ∈ U, KLocallyRingedSpace.Hom.toFun g a ∈ U')
        (a : A.restrictOpen U)
    (hs : Function.Surjective ((Hom.restrictTo g U U' h).1.stalkMap a).hom) :
    Function.Surjective (g.1.stalkMap ((ofRestrict A U).1.base a)).hom := by
  have h₁ : Function.Surjective ((Hom.restrictTo g U U' h ≫ ofRestrict B U').1.stalkMap a).hom := by
    rw [Hom.comp_val, LocallyRingedSpace.stalkMap_comp]
    change Function.Surjective (⇑((Hom.restrictTo g U U' h).1.stalkMap a).hom ∘
      ⇑((ofRestrict B U').1.stalkMap ((Hom.restrictTo g U U' h).1.base a)).hom)
    exact hs.comp (bijective_stalkMap_ofRestrict B U' _).2
  rw [surjective_stalkMap_congr (Hom.restrictTo_comp_ofRestrict g U U' h), Hom.comp_val,
    LocallyRingedSpace.stalkMap_comp] at h₁
  change Function.Surjective (⇑((ofRestrict A U).1.stalkMap a).hom ∘
    ⇑(g.1.stalkMap ((ofRestrict A U).1.base a)).hom) at h₁
  exact h₁.of_comp_left (bijective_stalkMap_ofRestrict A U a).1

/-- Injectivity of a stalk map of `g|U : A|U ⟶ B|U'` gives that of the stalk map of `g`. -/
theorem injective_stalkMap_of_restrictTo {A B : KLocallyRingedSpace.{u} K} (g : A ⟶ B)
    (U : Opens A) (U' : Opens B) (h : ∀ a ∈ U, KLocallyRingedSpace.Hom.toFun g a ∈ U')
        (a : A.restrictOpen U)
    (hi : Function.Injective ((Hom.restrictTo g U U' h).1.stalkMap a).hom) :
    Function.Injective (g.1.stalkMap ((ofRestrict A U).1.base a)).hom := by
  have h₁ : Function.Injective ((Hom.restrictTo g U U' h ≫ ofRestrict B U').1.stalkMap a).hom := by
    rw [Hom.comp_val, LocallyRingedSpace.stalkMap_comp]
    change Function.Injective (⇑((Hom.restrictTo g U U' h).1.stalkMap a).hom ∘
      ⇑((ofRestrict B U').1.stalkMap ((Hom.restrictTo g U U' h).1.base a)).hom)
    exact hi.comp (bijective_stalkMap_ofRestrict B U' _).1
  rw [injective_stalkMap_congr (Hom.restrictTo_comp_ofRestrict g U U' h), Hom.comp_val,
    LocallyRingedSpace.stalkMap_comp] at h₁
  change Function.Injective (⇑((ofRestrict A U).1.stalkMap a).hom ∘
    ⇑(g.1.stalkMap ((ofRestrict A U).1.base a)).hom) at h₁
  exact h₁.of_comp

/-- The assembly of the local isomorphism criterion: a `K`-morphism `φ : X ⟶ Y` with a two-sided
local inverse `χ : Y|W₂ ⟶ X|U₁` — `φ|S ≫ χ` is the inclusion `X|S ⟶ X|U₁` and `χ ≫ φ|U₁`
restricted to `Y|T` is the inclusion `Y|T ⟶ Y|V₁` — restricts to a `K`-isomorphism `X|U ≅ Y|V` at
any `x ∈ S` with `φ x ∈ T`: `U = S ∩ φ⁻¹T`, `V = {b ∈ T | χ b ∈ U}`; the base map is a
homeomorphism with inverse `χ`, and the stalk maps are bijective (surjective from the first
identity, injective from the second), so `isIso_of_isIso_base_of_stalkMap_bijective` applies. -/
theorem exists_isIso_restrictTo_of_inverse {X Y : KLocallyRingedSpace.{u} K} (φ : X ⟶ Y)
    {S U₁ : Opens X} {T W₂ V₁ : Opens Y} (hSU₁ : S ≤ U₁) (hSW₂ : ∀ a ∈ S,
        KLocallyRingedSpace.Hom.toFun φ a ∈ W₂)
    (hU₁V₁ : ∀ a ∈ U₁, KLocallyRingedSpace.Hom.toFun φ a ∈ V₁) (hTW₂ : T ≤ W₂) (hTV₁ : T ≤ V₁)
    (χ : Y.restrictOpen W₂ ⟶ X.restrictOpen U₁)
    (hX : Hom.restrictTo φ S W₂ hSW₂ ≫ χ = restrictOpenIncl X hSU₁)
    (hY : restrictOpenIncl Y hTW₂ ≫ χ ≫ Hom.restrictTo φ U₁ V₁ hU₁V₁ = restrictOpenIncl Y hTV₁)
    (x : X) (hxS : x ∈ S) (hxT : KLocallyRingedSpace.Hom.toFun φ x ∈ T) :
    ∃ (U : Opens X) (_ : x ∈ U) (V : Opens Y) (hUV : ∀ u ∈ U,
        KLocallyRingedSpace.Hom.toFun φ u ∈ V),
      IsIso (Hom.restrictTo φ U V hUV) := by
  -- the base identities
  have hΦS : ∀ (a : X) (ha : a ∈ S),
      KLocallyRingedSpace.Hom.toFun (Hom.restrictTo φ S W₂ hSW₂) ⟨a, ha⟩ =
          ⟨KLocallyRingedSpace.Hom.toFun φ a, hSW₂ a ha⟩ :=
    fun a ha => Subtype.ext (Hom.toFun_restrictTo φ S W₂ hSW₂ ⟨a, ha⟩)
  have hincl : ∀ (b : Y) (hb : b ∈ T), KLocallyRingedSpace.Hom.toFun (restrictOpenIncl Y hTW₂) ⟨b,
      hb⟩ = ⟨b, hTW₂ hb⟩ :=
    fun b hb => Subtype.ext (Hom.toFun_restrictTo (𝟙 Y) T W₂ _ ⟨b, hb⟩)
  have hbaseX : ∀ (a : X) (ha : a ∈ S), (KLocallyRingedSpace.Hom.toFun χ
      ⟨KLocallyRingedSpace.Hom.toFun φ a, hSW₂ a ha⟩).1 = a := by
    intro a ha
    have h1 := congrArg (fun ψ : X.restrictOpen S ⟶ X.restrictOpen U₁ =>
        (KLocallyRingedSpace.Hom.toFun ψ ⟨a, ha⟩).1) hX
    change (KLocallyRingedSpace.Hom.toFun χ (KLocallyRingedSpace.Hom.toFun
        (Hom.restrictTo φ S W₂ hSW₂) ⟨a, ha⟩)).1 =
      (KLocallyRingedSpace.Hom.toFun (restrictOpenIncl X hSU₁) ⟨a, ha⟩).1 at h1
    rw [hΦS a ha] at h1
    exact h1.trans (Hom.toFun_restrictTo (𝟙 X) S U₁ _ ⟨a, ha⟩)
  have hbaseXT : ∀ (a : X) (ha : a ∈ S) (hb : KLocallyRingedSpace.Hom.toFun φ a ∈ T),
      (KLocallyRingedSpace.Hom.toFun (restrictOpenIncl Y hTW₂ ≫ χ)
          ⟨KLocallyRingedSpace.Hom.toFun φ a, hb⟩).1 = a := by
    intro a ha hb
    change (KLocallyRingedSpace.Hom.toFun χ (KLocallyRingedSpace.Hom.toFun
        (restrictOpenIncl Y hTW₂) ⟨KLocallyRingedSpace.Hom.toFun φ a, hb⟩)).1 = a
    rw [hincl]
    exact hbaseX a ha
  have hbaseY : ∀ (b : Y) (hb : b ∈ T),
      KLocallyRingedSpace.Hom.toFun φ (KLocallyRingedSpace.Hom.toFun (restrictOpenIncl Y hTW₂ ≫ χ)
          ⟨b, hb⟩).1 = b := by
    intro b hb
    have h1 := congrArg (fun ψ : Y.restrictOpen T ⟶ Y.restrictOpen V₁ =>
        (KLocallyRingedSpace.Hom.toFun ψ ⟨b, hb⟩).1) hY
    change (KLocallyRingedSpace.Hom.toFun (Hom.restrictTo φ U₁ V₁ hU₁V₁)
      (KLocallyRingedSpace.Hom.toFun (restrictOpenIncl Y hTW₂ ≫ χ) ⟨b, hb⟩)).1 =
      (KLocallyRingedSpace.Hom.toFun (restrictOpenIncl Y hTV₁) ⟨b, hb⟩).1 at h1
    rw [Hom.toFun_restrictTo φ U₁ V₁ hU₁V₁] at h1
    exact h1.trans (Hom.toFun_restrictTo (𝟙 Y) T V₁ _ ⟨b, hb⟩)
  -- the opens `U = S ∩ φ⁻¹T` and `V = {b ∈ T | χ b ∈ U}`
  let U : Opens X := S ⊓ (Opens.map φ.1.base).obj T
  have hxU : x ∈ U := Opens.mem_inf.mpr ⟨hxS, hxT⟩
  let V : Opens Y := imgOpens Y T ((Opens.map (restrictOpenIncl Y hTW₂ ≫ χ).1.base).obj
    ((Opens.map (ofRestrict X U₁).1.base).obj U))
  have hVT : ∀ b ∈ V, b ∈ T := by
    intro b hb
    obtain ⟨hb', -⟩ := (mem_imgOpens Y).mp hb
    exact hb'
  have hVU : ∀ (b : Y) (hb : b ∈ V),
      (KLocallyRingedSpace.Hom.toFun (restrictOpenIncl Y hTW₂ ≫ χ) ⟨b, hVT b hb⟩).1 ∈ U := by
    intro b hb
    obtain ⟨hb', h2⟩ := (mem_imgOpens Y).mp hb
    exact h2
  have hmemV : ∀ (b : Y) (hb : b ∈ T),
      (KLocallyRingedSpace.Hom.toFun (restrictOpenIncl Y hTW₂ ≫ χ) ⟨b, hb⟩).1 ∈ U → b ∈ V :=
    fun b hb h2 => (mem_imgOpens Y).mpr ⟨hb, h2⟩
  have hUV : ∀ a ∈ U, KLocallyRingedSpace.Hom.toFun φ a ∈ V := by
    intro a ha
    obtain ⟨haS, haT⟩ := Opens.mem_inf.mp ha
    refine hmemV _ haT ?_
    rw [hbaseXT a haS haT]
    exact ha
  -- the base map is a homeomorphism, with inverse `χ`
  have hΦ : ∀ a : X.restrictOpen U,
      KLocallyRingedSpace.Hom.toFun (Hom.restrictTo φ U V hUV) a =
          ⟨KLocallyRingedSpace.Hom.toFun φ a.1, hUV a.1 a.2⟩ :=
    fun a => Subtype.ext (Hom.toFun_restrictTo φ U V hUV a)
  let invFun : Y.restrictOpen V → X.restrictOpen U := fun b =>
    ⟨(KLocallyRingedSpace.Hom.toFun (restrictOpenIncl Y hTW₂ ≫ χ) ⟨b.1, hVT b.1 b.2⟩).1,
        hVU b.1 b.2⟩
  have hinvcont : Continuous invFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp
      ((restrictOpenIncl Y hTW₂ ≫ χ).1.base.hom.continuous.comp
        (continuous_subtype_val.subtype_mk _))
  have hleft : ∀ a : X.restrictOpen U, invFun (KLocallyRingedSpace.Hom.toFun
      (Hom.restrictTo φ U V hUV) a) = a := by
    intro a
    rw [hΦ a]
    exact Subtype.ext (hbaseXT a.1 (Opens.mem_inf.mp a.2).1 (Opens.mem_inf.mp a.2).2)
  have hright : ∀ b : Y.restrictOpen V, KLocallyRingedSpace.Hom.toFun (Hom.restrictTo φ U V hUV)
      (invFun b) = b := by
    intro b
    rw [hΦ]
    exact Subtype.ext (hbaseY b.1 (hVT b.1 b.2))
  have hbase : IsIso (Hom.restrictTo φ U V hUV).1.1.base := by
    refine ⟨TopCat.ofHom ⟨invFun, hinvcont⟩, ?_, ?_⟩
    · exact TopCat.ext fun a => hleft a
    · exact TopCat.ext fun b => hright b
  -- the stalk maps are bijective
  have hstalk : ∀ a : X.restrictOpen U,
      Function.Bijective (φ.1.stalkMap ((ofRestrict X U).1.base a)).hom := by
    intro a
    obtain ⟨haS, haT⟩ := Opens.mem_inf.mp a.2
    constructor
    · have h1 : Function.Injective
          ((restrictOpenIncl Y hTV₁).1.stalkMap ⟨KLocallyRingedSpace.Hom.toFun φ a.1, haT⟩).hom :=
        (bijective_stalkMap_restrictOpenIncl Y hTV₁ _).1
      have hY' : (restrictOpenIncl Y hTW₂ ≫ χ) ≫ Hom.restrictTo φ U₁ V₁ hU₁V₁ =
          restrictOpenIncl Y hTV₁ := (Category.assoc _ _ _).trans hY
      have h2 := injective_stalkMap_of_comp (restrictOpenIncl Y hTW₂ ≫ χ)
        (Hom.restrictTo φ U₁ V₁ hU₁V₁) ⟨KLocallyRingedSpace.Hom.toFun φ a.1, haT⟩
        ((injective_stalkMap_congr hY' _).mpr h1)
      have hpt : (restrictOpenIncl Y hTW₂ ≫ χ).1.base ⟨KLocallyRingedSpace.Hom.toFun φ a.1, haT⟩ =
          ⟨a.1, hSU₁ haS⟩ :=
        Subtype.ext (hbaseXT a.1 haS haT)
      rw [hpt] at h2
      exact injective_stalkMap_of_restrictTo φ U₁ V₁ hU₁V₁ ⟨a.1, hSU₁ haS⟩ h2
    · have h1 : Function.Surjective ((restrictOpenIncl X hSU₁).1.stalkMap ⟨a.1, haS⟩).hom :=
        (bijective_stalkMap_restrictOpenIncl X hSU₁ _).2
      have h2 := surjective_stalkMap_of_comp (Hom.restrictTo φ S W₂ hSW₂) χ ⟨a.1, haS⟩
        ((surjective_stalkMap_congr hX _).mpr h1)
      exact surjective_stalkMap_of_restrictTo φ S W₂ hSW₂ ⟨a.1, haS⟩ h2
  exact ⟨U, hxU, V, hUV, KLocallyRingedSpace.isIso_of_isIso_base_of_stalkMap_bijective
    (Hom.restrictTo φ U V hUV) fun a => bijective_stalkMap_restrictTo φ U V hUV a (hstalk a)⟩


variable {X Y : AnalyticSpace.{u} K}

/-- The chart at `x` may be taken inside any open neighbourhood `O` of `x` (a chart of the open
subspace `X|O` at `x`, carried back by `restrictOpen_restrictOpen_iso`; `exists_kIso_localModel`
refined). -/
theorem exists_kIso_localModel_le (X : AnalyticSpace.{u} K) (x : X) (O : Opens X) (hxO : x ∈ O) :
    ∃ (U : Opens X) (_ : x ∈ U) (_ : U ≤ O) (n k : ℕ) (G : Opens (Kn.{u} K n))
      (f : Fin k → AnalyticFun K n G),
      Nonempty (KIso (X.toKLocallyRingedSpace.restrictOpen U) (localModel K n G f)) := by
  obtain ⟨U', hxU', n, k, G, f, ⟨e⟩⟩ := (X.restrictOpen O).exists_kIso_localModel ⟨x, hxO⟩
  exact ⟨imageOpens O U', mem_imageOpens.mpr ⟨hxO, hxU'⟩, fun _ hz => (mem_imageOpens.mp hz).1,
    n, k, G, f, ⟨(restrictOpen_restrictOpen_iso O U').symm ≪≫ e⟩⟩

/-- The germ-level content of the local isomorphism criterion. For a `K`-morphism `φ : X → Y`, a
point `x`, a `K`-morphism `κ : X|U₁ → Kⁿ` and a `K`-morphism `ψ : Y|W → Kⁿ` whose coordinate
pullbacks at `φ x` are carried by the stalk map `φ^*_x` to the coordinate pullbacks of `κ` at `x`:
then `ψ(φ x) = κ(x)`, and `φ^*_x ∘ σ_ψ = σ_κ` on the stalk `𝒜_{Kⁿ,ψ(φ x)}` (`sigmaStalk`: the stalk
maps followed by the identification of the stalks of the open subspaces with those of the spaces)
— two local `K`-algebra maps out of `𝒜_{Kⁿ,q}` agreeing on the constants and the coordinates agree
(`ringHom_ext_of_coord`). -/
theorem stalkMap_sigmaStalk_eq_of_coord (φ : X.toKLocallyRingedSpace ⟶ Y.toKLocallyRingedSpace)
    (x : X) {n : ℕ} {U₁ : Opens X} (hx : x ∈ U₁)
    (κ : X.toKLocallyRingedSpace.restrictOpen U₁ ⟶ affine K n) {W : Opens Y}
    (hy : φ.1.base x ∈ W) (ψ : Y.toKLocallyRingedSpace.restrictOpen W ⟶ affine K n)
    (hcoord : ∀ j, (φ.1.stalkMap x).hom (Y.toLocallyRingedSpace.presheaf.germ
        (imgOpens Y.toKLocallyRingedSpace W ⊤) (φ.1.base x) (mem_imgOpens_of_mem _ hy trivial)
        (ψ.pullbackΓ (coordSection K n j))) =
      X.toLocallyRingedSpace.presheaf.germ (imgOpens X.toKLocallyRingedSpace U₁ ⊤) x
        (mem_imgOpens_of_mem _ hx trivial) (κ.pullbackΓ (coordSection K n j))) :
    ∃ hb : ψ.1.base ⟨φ.1.base x, hy⟩ = κ.1.base ⟨x, hx⟩,
      ∀ a, (φ.1.stalkMap x).hom (sigmaStalk Y.toKLocallyRingedSpace ψ hy a) =
        sigmaStalk X.toKLocallyRingedSpace κ hx
          ((eqToHom (congrArg (affine K n).toLocallyRingedSpace.presheaf.stalk hb)).hom a) := by
  have hconst : ∀ c : K, (φ.1.stalkMap x).hom (constAt Y.toKLocallyRingedSpace (φ.1.base x) c) =
      constAt X.toKLocallyRingedSpace x c := fun c => φ.algebraMap_stalk x c
  -- the base points agree
  have hb : ψ.1.base ⟨φ.1.base x, hy⟩ = κ.1.base ⟨x, hx⟩ := by
    apply ULift.ext
    funext i
    have h1 := map_mem_maximalIdeal_of_isLocalHom (φ.1.stalkMap x).hom
      (germ_pullbackΓ_coord_sub_constAt_mem Y.toKLocallyRingedSpace ψ hy i)
    rw [map_sub, hcoord i, hconst] at h1
    have h2 := germ_pullbackΓ_coord_sub_constAt_mem X.toKLocallyRingedSpace κ hx i
    have hmem := Ideal.sub_mem _ h1 h2
    rw [sub_sub_sub_cancel_left, ← map_sub] at hmem
    by_contra hne
    exact ((IsLocalRing.mem_maximalIdeal _).mp hmem)
      (isUnit_constAt X.toKLocallyRingedSpace x (sub_ne_zero.mpr (Ne.symm hne)))
  refine ⟨hb, ?_⟩
  let e := eqToHom (congrArg (affine K n).toLocallyRingedSpace.presheaf.stalk hb)
  let α : (affine K n).toLocallyRingedSpace.presheaf.stalk (ψ.1.base ⟨φ.1.base x, hy⟩) →+*
      X.toLocallyRingedSpace.presheaf.stalk x :=
    (φ.1.stalkMap x).hom.comp (sigmaStalk Y.toKLocallyRingedSpace ψ hy)
  let β : (affine K n).toLocallyRingedSpace.presheaf.stalk (ψ.1.base ⟨φ.1.base x, hy⟩) →+*
      X.toLocallyRingedSpace.presheaf.stalk x :=
    (sigmaStalk X.toKLocallyRingedSpace κ hx).comp e.hom
  have hα : IsLocalHom α := by
    have h1 : IsLocalHom (φ.1.stalkMap x).hom := inferInstance
    have h2 : IsLocalHom (sigmaStalk Y.toKLocallyRingedSpace ψ hy) := isLocalHom_sigmaStalk _ ψ hy
    exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ h1 h2
  have hβ : IsLocalHom β := by
    have h1 : IsLocalHom e.hom := isLocalHom_of_isIso _
    have h2 : IsLocalHom (sigmaStalk X.toKLocallyRingedSpace κ hx) := isLocalHom_sigmaStalk _ κ hx
    exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ h2 h1
  have key : α = β := by
    refine @ringHom_ext_of_coord K _ n _ _ _ (X.isNoetherianRing_stalk x) _ α β hα hβ
      (fun c => ?_) (fun i => ?_)
    · change (φ.1.stalkMap x).hom (sigmaStalk Y.toKLocallyRingedSpace ψ hy _) =
        sigmaStalk X.toKLocallyRingedSpace κ hx (e.hom _)
      rw [sigmaStalk_const, hconst, const_eqToHom n hb c, sigmaStalk_const]
    · change (φ.1.stalkMap x).hom (sigmaStalk Y.toKLocallyRingedSpace ψ hy _) =
        sigmaStalk X.toKLocallyRingedSpace κ hx (e.hom _)
      rw [sigmaStalk_coordAt, hcoord i, coordAt_eqToHom n hb i, sigmaStalk_coordAt]
  intro a
  exact DFunLike.congr_fun key a

/-- The construction of the local inverse: for `φ : X → Y` with a bijective stalk map at `x`, a
chart `e : X|U₁ ≅ V(f') ⊆ G' ⊆ Kⁿ` of `X` at `x` and an open `V₁ ∋ φ x`, there is an open
`W₂ ∋ φ x` inside `V₁` and a `K`-morphism `χ : Y|W₂ ⟶ X|U₁` such that `φ^*_x` carries the
coordinate germs of `χ ≫ κ` (`κ = e.hom ≫ ι` the chart map) at `φ x` to those of `κ` at `x`. The
coordinates of `χ ≫ κ` are sections `t j` of `Y` near `φ x` whose germs are the preimages under
`φ^*_x` of the coordinate germs of `κ`; the morphism `Y|W₂ → Kⁿ` with those coordinates is
`homOfSections`; it lands in `G'` near `φ x`; its pullbacks of the equations `f'` of the model
vanish near `φ x` (their germs at `φ x` are `(φ^*_x)⁻¹` of the germs of the pullbacks along `κ`,
which are zero, `stalkMap_localModel_ι_germ_eq_zero`), so it factors through the model by the
functoriality of quotients along the zero ideal sheaf (`quotientMap`, `quotientBotIso`), and `χ`
is the composite with `e.inv`. -/
theorem exists_hom_coord_of_bijective_stalkMap
    (φ : X.toKLocallyRingedSpace ⟶ Y.toKLocallyRingedSpace) (x : X)
    (hφ : Function.Bijective (φ.1.stalkMap x).hom) {n : ℕ} {U₁ : Opens X} (hxU₁ : x ∈ U₁)
    {k' : ℕ} {G' : Opens (Kn.{u} K n)} {f' : Fin k' → AnalyticFun K n G'}
    (eX : KIso (X.toKLocallyRingedSpace.restrictOpen U₁) (localModel K n G' f')) (V₁ : Opens Y)
    (hyV₁ : φ.1.base x ∈ V₁) :
    ∃ (W₂ : Opens Y) (hy : φ.1.base x ∈ W₂) (_ : W₂ ≤ V₁)
      (χ : Y.toKLocallyRingedSpace.restrictOpen W₂ ⟶ X.toKLocallyRingedSpace.restrictOpen U₁),
      ∀ j, (φ.1.stalkMap x).hom
          (Y.toLocallyRingedSpace.presheaf.germ (imgOpens Y.toKLocallyRingedSpace W₂ ⊤)
            (φ.1.base x) (mem_imgOpens_of_mem _ hy trivial)
            ((χ ≫ eX.hom ≫ localModel.ι K n G' f').pullbackΓ (coordSection K n j))) =
        X.toLocallyRingedSpace.presheaf.germ (imgOpens X.toKLocallyRingedSpace U₁ ⊤) x
          (mem_imgOpens_of_mem _ hxU₁ trivial)
          ((eX.hom ≫ localModel.ι K n G' f').pullbackΓ (coordSection K n j)) := by
  classical
  -- the stalk map as a ring equivalence
  let α : Y.toLocallyRingedSpace.presheaf.stalk (φ.1.base x) ≃+*
      X.toLocallyRingedSpace.presheaf.stalk x := RingEquiv.ofBijective (φ.1.stalkMap x).hom hφ
  -- the coordinate germs of the chart of `X` at `x`
  let σ : Fin n → X.toLocallyRingedSpace.presheaf.stalk x := fun j =>
    X.toLocallyRingedSpace.presheaf.germ (imgOpens X.toKLocallyRingedSpace U₁ ⊤) x
      (mem_imgOpens_of_mem _ hxU₁ trivial)
      ((eX.hom ≫ localModel.ι K n G' f').pullbackΓ (coordSection K n j))
  -- their preimages under the stalk map, realized as sections of `Y` near `φ x`
  choose W₀ hyW₀ t ht using fun j =>
    Y.toLocallyRingedSpace.presheaf.exists_germ_eq (α.symm (σ j))
  let W : Opens Y := V₁ ⊓ ⨅ j, W₀ j
  have hyW : φ.1.base x ∈ W := Opens.mem_inf.mpr ⟨hyV₁, mem_iInf_opens.mpr hyW₀⟩
  have hWW₀ : ∀ j, W ≤ W₀ j := fun j => inf_le_right.trans (iInf_le _ j)
  have hWV₁ : W ≤ V₁ := inf_le_left
  -- the sections `t j` as global sections of `Y | W'`, `W' ≤ W`
  let tt : ∀ W' : Opens Y, W' ≤ W → Fin n → LocallyRingedSpace.Γ.obj
      (op (Y.toKLocallyRingedSpace.restrictOpen W').toLocallyRingedSpace) :=
    fun W' hW' j => Y.toLocallyRingedSpace.presheaf.map
      (homOfLE ((imgOpens_top_le Y.toKLocallyRingedSpace W').trans (hW'.trans (hWW₀ j)))).op (t j)
  have hgermt : ∀ (W' : Opens Y) (hW' : W' ≤ W) (j : Fin n) (w : Y) (hw : w ∈ W'),
      Y.toLocallyRingedSpace.presheaf.germ (imgOpens Y.toKLocallyRingedSpace W' ⊤) w
          (mem_imgOpens_of_mem _ hw trivial) (tt W' hW' j) =
        Y.toLocallyRingedSpace.presheaf.germ (W₀ j) w (hWW₀ j (hW' hw)) (t j) :=
    fun W' hW' j w hw => Y.toLocallyRingedSpace.presheaf.germ_res_apply _ w _ (t j)
  -- the `K`-morphisms `Y | W' → Kⁿ` with these coordinates (`homOfSections`)
  let χ₀ : ∀ W' : Opens Y, W' ≤ W → (Y.toKLocallyRingedSpace.restrictOpen W' ⟶ affine K n) :=
    fun W' hW' => homOfSections (Y.restrictOpen W') (tt W' hW')
  have hχ₀ : ∀ W' hW' j, (χ₀ W' hW').pullbackΓ (coordSection K n j) = tt W' hW' j :=
    fun W' hW' j => pullbackΓ_homOfSections_coordSection (Y.restrictOpen W') (tt W' hW') j
  -- the coordinate compatibility at `φ x`
  have hcoord : ∀ (W' : Opens Y) (hW' : W' ≤ W) (hy' : φ.1.base x ∈ W') (j : Fin n),
      (φ.1.stalkMap x).hom (Y.toLocallyRingedSpace.presheaf.germ
        (imgOpens Y.toKLocallyRingedSpace W' ⊤) (φ.1.base x) (mem_imgOpens_of_mem _ hy' trivial)
        ((χ₀ W' hW').pullbackΓ (coordSection K n j))) = σ j := by
    intro W' hW' hy' j
    rw [hχ₀ W' hW' j, hgermt W' hW' j _ hy', ht j]
    exact α.apply_symm_apply (σ j)
  -- the base points and the stalk maps of the `χ₀ W'` at `φ x`
  have hS := fun (W' : Opens Y) (hW' : W' ≤ W) (hy' : φ.1.base x ∈ W') =>
    stalkMap_sigmaStalk_eq_of_coord φ x hxU₁ (eX.hom ≫ localModel.ι K n G' f') hy' (χ₀ W' hW')
      (hcoord W' hW' hy')
  have hWle : W ≤ W := le_rfl
  -- notation for the chart map of `X` and the point `p = κ(x) ∈ G'`
  have hpG' : (eX.hom ≫ localModel.ι K n G' f').1.base ⟨x, hxU₁⟩ ∈ G' :=
    (eX.hom.1.base ⟨x, hxU₁⟩).1.2
  obtain ⟨hb, hstalk⟩ := hS W hWle hyW
  -- the coordinate germs of `χ₀ W'` and `χ₀ W''` agree at every common point
  have hcoord2 : ∀ (W' : Opens Y) (hW' : W' ≤ W) (W'' : Opens Y) (hW'' : W'' ≤ W) (w : Y)
      (hw : w ∈ W') (hw' : w ∈ W'') (j : Fin n),
      Y.toLocallyRingedSpace.presheaf.germ (imgOpens Y.toKLocallyRingedSpace W' ⊤) w
          (mem_imgOpens_of_mem _ hw trivial) ((χ₀ W' hW').pullbackΓ (coordSection K n j)) =
        Y.toLocallyRingedSpace.presheaf.germ (imgOpens Y.toKLocallyRingedSpace W'' ⊤) w
          (mem_imgOpens_of_mem _ hw' trivial) ((χ₀ W'' hW'').pullbackΓ (coordSection K n j)) := by
    intro W' hW' W'' hW'' w hw hw' j
    rw [hχ₀ W' hW' j, hgermt W' hW' j w hw, hχ₀ W'' hW'' j, hgermt W'' hW'' j w hw']
  have hbase2 : ∀ (W' : Opens Y) (hW' : W' ≤ W) (W'' : Opens Y) (hW'' : W'' ≤ W) (w : Y)
      (hw : w ∈ W') (hw' : w ∈ W''),
      (χ₀ W' hW').1.base ⟨w, hw⟩ = (χ₀ W'' hW'').1.base ⟨w, hw'⟩ := fun W' hW' W'' hW'' w hw hw' =>
    base_eq_of_germ_pullbackΓ_coord Y.toKLocallyRingedSpace (χ₀ W' hW') (χ₀ W'' hW'') hw hw'
      (hcoord2 W' hW' W'' hW'' w hw hw')
  -- the open `W₁ ≤ W` where `χ₀ W` lands in `G'`
  let W₁ : Opens Y := imgOpens Y.toKLocallyRingedSpace W ((Opens.map (χ₀ W hWle).1.base).obj G')
  have hW₁W : W₁ ≤ W := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hyW₁ : φ.1.base x ∈ W₁ := by
    refine mem_imgOpens_of_mem _ hyW ?_
    change (χ₀ W hWle).1.base ⟨φ.1.base x, hyW⟩ ∈ G'
    rw [hb]
    exact hpG'
  have hG' : ∀ (W' : Opens Y) (hW' : W' ≤ W₁) (w : Y.toKLocallyRingedSpace.restrictOpen W'),
      (χ₀ W' (hW'.trans hW₁W)).1.base w ∈ G' := by
    intro W' hW' ⟨w, hw₀⟩
    obtain ⟨hw, hwG⟩ := (mem_imgOpens _).mp (hW' hw₀)
    rw [hbase2 W' (hW'.trans hW₁W) W hWle w hw₀ hw]
    exact hwG
  -- the lifts into `(G', 𝒜_{G'})` (opaque: the lift through an open immersion is a pullback)
  obtain ⟨χ₁, hχ₁⟩ : ∃ χ₁ : ∀ (W' : Opens Y), W' ≤ W₁ →
      (Y.toKLocallyRingedSpace.restrictOpen W' ⟶ (affine K n).restrictOpen G'),
      ∀ W' hW', χ₁ W' hW' ≫ ofRestrict (affine K n) G' = χ₀ W' (hW'.trans hW₁W) :=
    ⟨fun W' hW' => Hom.liftRestrict (χ₀ W' (hW'.trans hW₁W)) G' (hG' W' hW'),
      fun W' hW' => Hom.liftRestrict_comp_ofRestrict (χ₀ W' (hW'.trans hW₁W)) G' (hG' W' hW')⟩
  -- the equations of the model of `X` pull back to sections vanishing at `φ x`
  have hpG'' : (χ₀ W hWle).1.base ⟨φ.1.base x, hyW⟩ ∈ G' := by rw [hb]; exact hpG'
  have hzero : ∀ i : Fin k', Y.toLocallyRingedSpace.presheaf.germ
      (imgOpens Y.toKLocallyRingedSpace W ((Opens.map (χ₀ W hWle).1.base).obj G')) (φ.1.base x)
      (mem_imgOpens_of_mem _ hyW hpG'') ((χ₀ W hWle).1.c.app (op G') (f' i)) = 0 := by
    intro i
    apply hφ.1
    rw [map_zero, ← sigmaStalk_germ Y.toKLocallyRingedSpace (χ₀ W hWle) hyW G' hpG'' (f' i),
      hstalk, germ_eqToHom n hb G' hpG'' (f' i), sigmaStalk_apply]
    rw [stalkMap_comp_localModel_ι_germ_eq_zero G' f' eX ⟨x, hxU₁⟩ hpG' i, map_zero]
  -- hence they vanish on an open `W₂ ≤ W₁` containing `φ x`
  choose W₂' hyW₂' iW₂' iT hW₂' using fun i : Fin k' =>
    Y.toLocallyRingedSpace.presheaf.germ_eq
      (U := imgOpens Y.toKLocallyRingedSpace W ((Opens.map (χ₀ W hWle).1.base).obj G')) (V := ⊤)
      (φ.1.base x) (mem_imgOpens_of_mem _ hyW hpG'') (Opens.mem_top _)
      ((χ₀ W hWle).1.c.app (op G') (f' i)) (0 : Y.toLocallyRingedSpace.presheaf.obj (op ⊤))
      (by rw [hzero i, map_zero])
  let W₂ : Opens Y := W₁ ⊓ ⨅ i, W₂' i
  have hyW₂ : φ.1.base x ∈ W₂ := Opens.mem_inf.mpr ⟨hyW₁, mem_iInf_opens.mpr hyW₂'⟩
  have hW₂W₁ : W₂ ≤ W₁ := inf_le_left
  have hW₂W : W₂ ≤ W := hW₂W₁.trans hW₁W
  have hW₂W₂' : ∀ i, W₂ ≤ W₂' i := fun i => inf_le_right.trans (iInf_le _ i)
  -- the `Compat` condition of the lift on `W₂`: the equations pull back to zero at every point
  have hcompat : QuotientSpace.Compat (χ₁ W₂ hW₂W₁).1 ⊥ (modelIdeal K n G' f') := by
    intro w
    refine le_of_le_of_eq ?_ (show (⊥ : Ideal _) = QuotientSpace.stalkIdeal
      (Y.toKLocallyRingedSpace.restrictOpen W₂).toLocallyRingedSpace ⊥ w from
      (IdealSheaf.stalkIdeal_bot
        (𝒪 := (Y.toKLocallyRingedSpace.restrictOpen W₂).toLocallyRingedSpace.𝒪) w).symm)
    refine le_trans (Ideal.map_mono (IdealSheaf.stalkIdeal_ofGlobal
      (analyticSpaceOfOpen K n G').toLocallyRingedSpace.𝒪 (fun j => toGlobal K n G' (f' j)) _).le)
      ?_
    refine le_trans (le_of_eq (Ideal.map_span _ _)) (Ideal.span_le.mpr ?_)
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    refine Ideal.mem_bot.mpr ?_
    -- the statement for `χ₀ W₂`, then transported to `χ₁ W₂ ≫ ofRestrict`
    have key : ∀ ψ : Y.toKLocallyRingedSpace.restrictOpen W₂ ⟶ affine K n, ψ = χ₀ W₂ hW₂W →
        ∀ hG : ψ.1.base w ∈ G', (ψ.1.stalkMap w).hom
          ((affine K n).toLocallyRingedSpace.presheaf.germ G' (ψ.1.base w) hG (f' i)) = 0 := by
      rintro ψ rfl hG
      have hwW : w.1 ∈ W := hW₂W w.2
      have hwG : (χ₀ W hWle).1.base ⟨w.1, hwW⟩ ∈ G' := by
        rw [← hbase2 W₂ hW₂W W hWle w.1 w.2 hwW]
        exact hG
      apply (ConcreteCategory.bijective_of_isIso (resIso Y.toKLocallyRingedSpace W₂ w.2).hom).1
      refine Eq.trans ?_ (map_zero (resIso Y.toKLocallyRingedSpace W₂ w.2).hom.hom).symm
      have h1 := sigmaStalk_germ Y.toKLocallyRingedSpace (χ₀ W₂ hW₂W) w.2 G' hG (f' i)
      rw [sigmaStalk_apply] at h1
      refine h1.trans ?_
      rw [germ_c_app_eq_of_germ_pullbackΓ_coord Y.toKLocallyRingedSpace (χ₀ W₂ hW₂W) (χ₀ W hWle)
        w.2 hwW (hcoord2 W₂ hW₂W W hWle w.1 w.2 hwW) (Y.isNoetherianRing_stalk w.1) G' hG hwG
        (f' i)]
      have h2 : w.1 ∈ W₂' i := hW₂W₂' i w.2
      have h6 := Y.toLocallyRingedSpace.presheaf.germ_res_apply (iW₂' i) w.1 h2
        ((χ₀ W hWle).1.c.app (op G') (f' i))
      have h7 := Y.toLocallyRingedSpace.presheaf.germ_res_apply (iT i) w.1 h2
        (0 : Y.toLocallyRingedSpace.presheaf.obj (op ⊤))
      refine h6.symm.trans ?_
      refine (DFunLike.congr_arg (Y.toLocallyRingedSpace.presheaf.germ (W₂' i) w.1 h2).hom
        (hW₂' i)).trans ?_
      exact h7.trans (map_zero (Y.toLocallyRingedSpace.presheaf.germ ⊤ w.1 trivial).hom)
    have h3 := key _ (hχ₁ W₂ hW₂W₁) ((χ₁ W₂ hW₂W₁).1.base w).2
    have h4 := LocallyRingedSpace.stalkMap_comp (χ₁ W₂ hW₂W₁).1 (ofRestrict (affine K n) G').1 w
    have h5 := stalkMap_ofRestrict_germ _ _ G' ((χ₁ W₂ hW₂W₁).1.base w) (f' i)
    change (((χ₁ W₂ hW₂W₁).1 ≫ (ofRestrict (affine K n) G').1).stalkMap w).hom _ = 0 at h3
    rw [h4] at h3
    change ((χ₁ W₂ hW₂W₁).1.stalkMap w).hom (((ofRestrict (affine K n) G').1.stalkMap
      ((χ₁ W₂ hW₂W₁).1.base w)).hom ((affine K n).toLocallyRingedSpace.presheaf.germ G'
        ((χ₁ W₂ hW₂W₁).1.base w).1 ((χ₁ W₂ hW₂W₁).1.base w).2 (f' i))) = 0 at h3
    rw [h5] at h3
    exact h3
  -- the morphism into the model of `X`, and into `X|U₁`
  let ε := quotientBotIso (Y.toKLocallyRingedSpace.restrictOpen W₂) ⊥
    (fun _ => IdealSheaf.stalkIdeal_bot _)
  let χ : Y.toKLocallyRingedSpace.restrictOpen W₂ ⟶ X.toKLocallyRingedSpace.restrictOpen U₁ :=
    ε.inv ≫ quotientMap (χ₁ W₂ hW₂W₁) ⊥ (modelIdeal K n G' f') hcompat ≫ eX.inv
  have hε : ε.inv ≫ quotientι (Y.toKLocallyRingedSpace.restrictOpen W₂) ⊥ = 𝟙 _ := ε.inv_hom_id
  have hχκ : χ ≫ eX.hom ≫ localModel.ι K n G' f' = χ₀ W₂ hW₂W := by
    dsimp only [χ]
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, localModel.ι,
      ← Category.assoc (quotientMap _ _ _ _), quotientMap_comp_quotientι, Category.assoc, hχ₁,
      ← Category.assoc, hε, Category.id_comp]
  refine ⟨W₂, hyW₂, hW₂W.trans hWV₁, χ, fun j => ?_⟩
  rw [hχκ]
  exact hcoord W₂ hW₂W hyW₂ j

/-- **The local isomorphism criterion** ([Hir64, Ch. 0, §1, pp. 119–120], tacit; [GR84, Ch. 1]): a
`K`-morphism `φ : X ⟶ Y` of analytic `K`-spaces whose stalk map at `x` is bijective restricts to a
`K`-isomorphism of open neighbourhoods `X|U ≅ Y|V`. Charts `eY` of `Y` at `φ x` and `eX` of `X` at
`x` inside `φ⁻¹V₁`; the construction `exists_hom_coord_of_bijective_stalkMap` gives
`χ : Y|W₂ ⟶ X|U₁` with the coordinate identity at `φ x`, which spreads to an open `S ∋ x`
(`exists_opens_forall_stalkMap_germ_eq`) and yields `φ|S ≫ χ = incl` by the uniqueness of
morphisms into `Kⁿ` with given coordinates (`restrictTo_comp_eq_of_stalkMap_germ_pullbackΓ_coord`);
the coordinates of `χ ≫ φ|U₁ ≫ κY` and of `κY` have the same germs at `φ x` (by the first identity
and injectivity of `φ^*_x`), spread to an open `T ∋ φ x`, and give `incl ≫ χ ≫ φ|U₁ = incl` on
`Y|T`; `exists_isIso_restrictTo_of_inverse` concludes through
`isIso_of_isIso_base_of_stalkMap_bijective`. -/
theorem exists_isIso_restrictTo_of_bijective_stalkMap
    (φ : X.toKLocallyRingedSpace ⟶ Y.toKLocallyRingedSpace) (x : X)
    (hφ : Function.Bijective (φ.1.stalkMap x).hom) :
    ∃ (U : Opens X) (_ : x ∈ U) (V : Opens Y) (hUV : ∀ u ∈ U, Hom.toFun φ u ∈ V),
      IsIso (Hom.restrictTo φ U V hUV) := by
  obtain ⟨V₁, hyV₁, m, l, H, g, ⟨eY⟩⟩ := Y.exists_kIso_localModel (φ.1.base x)
  obtain ⟨U₁, hxU₁, hU₁V₁, n, k', G', f', ⟨eX⟩⟩ :=
    X.exists_kIso_localModel_le x ((Opens.map φ.1.base).obj V₁) hyV₁
  obtain ⟨W₂, hyW₂, hW₂V₁, χ, hχ⟩ :=
    exists_hom_coord_of_bijective_stalkMap φ x hφ hxU₁ eX V₁ hyV₁
  -- the coordinate identity spreads to an open `S ∋ x`: `φ|S ≫ χ` is the inclusion
  obtain ⟨S, hxS, hSW₂', hSU₁', hS⟩ := exists_opens_forall_stalkMap_germ_eq φ.1 x
    (U := imgOpens Y.toKLocallyRingedSpace W₂ ⊤) (V := imgOpens X.toKLocallyRingedSpace U₁ ⊤)
    (mem_imgOpens_of_mem _ hyW₂ trivial) (mem_imgOpens_of_mem _ hxU₁ trivial)
    (fun j => (χ ≫ eX.hom ≫ localModel.ι K n G' f').pullbackΓ (coordSection K n j))
    (fun j => (eX.hom ≫ localModel.ι K n G' f').pullbackΓ (coordSection K n j)) hχ
  have hSU₁ : S ≤ U₁ := hSU₁'.trans (imgOpens_top_le _ U₁)
  have hSW₂ : ∀ a ∈ S, Hom.toFun φ a ∈ W₂ := fun a ha => imgOpens_top_le _ W₂ (hSW₂' a ha)
  have hU₁V₁' : ∀ a ∈ U₁, Hom.toFun φ a ∈ V₁ := fun a ha => hU₁V₁ ha
  have hXid : Hom.restrictTo φ S W₂ hSW₂ ≫ χ = restrictOpenIncl X.toKLocallyRingedSpace hSU₁ :=
    (restrictTo_comp_eq_of_stalkMap_germ_pullbackΓ_coord φ hSW₂ hSU₁ χ (𝟙 _) eX
      fun a ha j => by rw [Category.id_comp]; exact hS a ha j).trans (Category.comp_id _)
  -- the coordinates of `χ ≫ φ|U₁ ≫ κY` and of `κY` have the same germs at `φ x`
  have hY0 : ∀ i, Y.toLocallyRingedSpace.presheaf.germ (imgOpens Y.toKLocallyRingedSpace W₂ ⊤)
        (φ.1.base x) (mem_imgOpens_of_mem _ hyW₂ trivial)
        ((χ ≫ Hom.restrictTo φ U₁ V₁ hU₁V₁' ≫ eY.hom ≫ localModel.ι K m H g).pullbackΓ
          (coordSection K m i)) =
      Y.toLocallyRingedSpace.presheaf.germ (imgOpens Y.toKLocallyRingedSpace V₁ ⊤) (φ.1.base x)
        (mem_imgOpens_of_mem _ hyV₁ trivial)
        ((eY.hom ≫ localModel.ι K m H g).pullbackΓ (coordSection K m i)) := by
    intro i
    apply hφ.1
    have hA := germ_pullbackΓ_restrictTo φ S W₂ hSW₂ hxS
      ((χ ≫ Hom.restrictTo φ U₁ V₁ hU₁V₁' ≫ eY.hom ≫ localModel.ι K m H g).pullbackΓ
        (coordSection K m i))
    have hB := Hom.pullbackΓ_comp (Hom.restrictTo φ S W₂ hSW₂)
      (χ ≫ Hom.restrictTo φ U₁ V₁ hU₁V₁' ≫ eY.hom ≫ localModel.ι K m H g) (coordSection K m i)
    have hC : Hom.restrictTo φ S W₂ hSW₂ ≫
        (χ ≫ Hom.restrictTo φ U₁ V₁ hU₁V₁' ≫ eY.hom ≫ localModel.ι K m H g) =
        restrictOpenIncl X.toKLocallyRingedSpace hSU₁ ≫
          (Hom.restrictTo φ U₁ V₁ hU₁V₁' ≫ eY.hom ≫ localModel.ι K m H g) := by
      rw [← Category.assoc, hXid]
    have hD := Hom.pullbackΓ_comp (restrictOpenIncl X.toKLocallyRingedSpace hSU₁)
      (Hom.restrictTo φ U₁ V₁ hU₁V₁' ≫ eY.hom ≫ localModel.ι K m H g) (coordSection K m i)
    have hE := germ_pullbackΓ_restrictOpenIncl X.toKLocallyRingedSpace hSU₁ hxS
      ((Hom.restrictTo φ U₁ V₁ hU₁V₁' ≫ eY.hom ≫ localModel.ι K m H g).pullbackΓ
        (coordSection K m i))
    have hF := Hom.pullbackΓ_comp (Hom.restrictTo φ U₁ V₁ hU₁V₁')
      (eY.hom ≫ localModel.ι K m H g) (coordSection K m i)
    have hG := germ_pullbackΓ_restrictTo φ U₁ V₁ hU₁V₁' hxU₁
      ((eY.hom ≫ localModel.ι K m H g).pullbackΓ (coordSection K m i))
    refine hA.symm.trans ?_
    refine (congrArg (fun s => X.toLocallyRingedSpace.presheaf.germ
      (imgOpens X.toKLocallyRingedSpace S ⊤) x (mem_imgOpens_of_mem _ hxS trivial) s)
      hB.symm).trans ?_
    refine (congrArg (fun ψ : X.toKLocallyRingedSpace.restrictOpen S ⟶ affine K m =>
      X.toLocallyRingedSpace.presheaf.germ (imgOpens X.toKLocallyRingedSpace S ⊤) x
        (mem_imgOpens_of_mem _ hxS trivial) (ψ.pullbackΓ (coordSection K m i))) hC).trans ?_
    refine (congrArg (fun s => X.toLocallyRingedSpace.presheaf.germ
      (imgOpens X.toKLocallyRingedSpace S ⊤) x (mem_imgOpens_of_mem _ hxS trivial) s) hD).trans ?_
    refine hE.trans ?_
    refine (congrArg (fun s => X.toLocallyRingedSpace.presheaf.germ
      (imgOpens X.toKLocallyRingedSpace U₁ ⊤) x (mem_imgOpens_of_mem _ hxU₁ trivial) s)
      hF).trans ?_
    exact hG
  -- they spread to an open `T ∋ φ x`: `χ ≫ φ|U₁` restricted to `Y|T` is the inclusion
  obtain ⟨T, hyT, hTW₂', hTV₁', hT⟩ := exists_opens_forall_germ_eq
    Y.toLocallyRingedSpace.presheaf (U := imgOpens Y.toKLocallyRingedSpace W₂ ⊤)
    (V := imgOpens Y.toKLocallyRingedSpace V₁ ⊤) (φ.1.base x)
    (mem_imgOpens_of_mem _ hyW₂ trivial) (mem_imgOpens_of_mem _ hyV₁ trivial)
    (fun i => (χ ≫ Hom.restrictTo φ U₁ V₁ hU₁V₁' ≫ eY.hom ≫ localModel.ι K m H g).pullbackΓ
      (coordSection K m i))
    (fun i => (eY.hom ≫ localModel.ι K m H g).pullbackΓ (coordSection K m i)) hY0
  have hTW₂ : T ≤ W₂ := hTW₂'.trans (imgOpens_top_le _ W₂)
  have hTV₁ : T ≤ V₁ := hTV₁'.trans (imgOpens_top_le _ V₁)
  have hYid : restrictOpenIncl Y.toKLocallyRingedSpace hTW₂ ≫ χ ≫ Hom.restrictTo φ U₁ V₁ hU₁V₁' =
      restrictOpenIncl Y.toKLocallyRingedSpace hTV₁ :=
    (restrictTo_comp_eq_of_stalkMap_germ_pullbackΓ_coord (𝟙 Y.toKLocallyRingedSpace)
      (fun _ hb => hTW₂ hb) hTV₁ (χ ≫ Hom.restrictTo φ U₁ V₁ hU₁V₁') (𝟙 _) eY fun b hb i => by
        change ((𝟙 Y.toLocallyRingedSpace : Y.toLocallyRingedSpace ⟶ _).stalkMap b).hom _ = _
        rw [LocallyRingedSpace.stalkMap_id, Category.id_comp, Category.assoc]
        exact hT b hb i).trans (Category.comp_id _)
  exact exists_isIso_restrictTo_of_inverse φ hSU₁ hSW₂ hU₁V₁' hTW₂ hTV₁ χ hXid hYid x hxS hyT


end AnalyticSpace

end
