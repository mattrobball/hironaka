/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Complexified
public import Hironaka.AnalyticSpace.HomExt
public import Mathlib.Analysis.Complex.Basic
import Hironaka.AnalyticSpace.Lemmas
import Hironaka.AnalyticSpace.OpenSubspaceLemmas
import Hironaka.AnalyticSpace.Quotient
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The complexification `X(ℂ) = (|X|, 𝒪_X ⊗_ℝ ℂ)` of a real-analytic space

For a preanalytic `ℝ`-space `X = (X, 𝒪_X)`, Hironaka defines `X(ℂ)` as the `ℂ`-local-ringed space
`(X, 𝒪_X ⊗_ℝ ℂ)` [Hir64, Ch. 0, §1, p. 120]. This file builds `X(ℂ)` for
every `ℝ`-local-ringed space `X` whose residue fields are `ℝ` — the property of the stalks of a
(pre)analytic `ℝ`-space that makes `𝒪_{X,x} ⊗_ℝ ℂ` a local ring — and complexifies
`ℝ`-morphisms (Hironaka's `h_ℂ`).

* `complexifyFunctor : CommRingCat ⥤ CommRingCat`, `A ↦ A[i]`
  (`Hironaka/AnalyticSpace/Complexified.lean`), and the presheaf
  `complexifyPresheaf 𝒪_X = 𝒪_X ⊗_ℝ ℂ := 𝒪_X ⋙ complexifyFunctor`, `U ↦ Γ(U, 𝒪_X)[i]`. It is a
  sheaf: a compatible family of pairs glues uniquely because its two components do
  (`isSheaf_complexifyPresheaf`).
* Its stalk at `x` is `𝒪_{X,x}[i]` (`stalkComplexifyEquiv`): the canonical map `colimit.post`
  sends the germ of `a + b i` to `(germ a) + (germ b) i`; surjective since every element of
  `𝒪_{X,x}` is a germ, injective since a germ vanishing at `x` vanishes near `x`.
* `HasRealResidueFields X` (a class on `ℝ`-local-ringed spaces): every element of every stalk is
  congruent modulo the maximal ideal to a constant `constAt X x c`. It holds for `(ℝⁿ, 𝒜_{ℝⁿ})`
  (a germ is congruent to its value), passes from the target to the source of an `ℝ`-morphism
  with surjective stalk maps (open immersions, the quotient by an ideal sheaf) and from the
  source to the target of an `ℝ`-morphism with surjective base map (the residue field of the
  target embeds in that of the source), hence holds for every local model and for every analytic
  `ℝ`-space (`exists_kIso_localModel`).
* `complexify X : KLocallyRingedSpace ℂ`, the space `X(ℂ)`: the carrier `|X|`, the sheaf
  `𝒪_X ⊗_ℝ ℂ`, local stalks by `Complexified.isLocalRing_of_exists_sub_mem`, the `ℂ`-structure
  `c ↦ Re c + Im c · i` on the constants of `X`.
* `complexifyHom (f : X ⟶ Y) : complexify X ⟶ complexify Y`, Hironaka's `h_ℂ`: the same base map
  and the complexified sheaf map; its stalk maps are the complexified stalk maps of `f`
  (`stalkMap_complexifyHomAux`, `complexifyStalkEquiv_stalkMap_complexifyHom`), so they are
  local; `complexifyHom_id`, `complexifyHom_comp`.
* `complexifyRestrictIso : complexify (X | U) ≅ (complexify X) | U`: complexification commutes
  with open subspaces.

Hironaka's complexifications `(Y, f)` of `X`, the analytic `ℂ`-spaces receiving `X(ℂ)` as a
closed subspace, are defined in `Hironaka/AnalyticSpace/Complexification.lean`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AnalyticSpace

/-! ### The functor `A ↦ A[i]` and the presheaf `𝒪_X ⊗_ℝ ℂ` -/

/-- The functor `A ↦ A ⊗_ℝ ℂ = A[i]` on commutative rings. -/
def complexifyFunctor : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj A := CommRingCat.of (Complexified A)
  map f := CommRingCat.ofHom (Complexified.map f.hom)
  map_id A := by
    ext z
    · rfl
    · rfl
  map_comp f g := by
    ext z
    · rfl
    · rfl

@[simp] theorem complexifyFunctor_obj (A : CommRingCat.{u}) :
    complexifyFunctor.obj A = CommRingCat.of (Complexified A) := rfl

@[simp] theorem complexifyFunctor_map_apply {A B : CommRingCat.{u}} (f : A ⟶ B)
    (z : Complexified A) : complexifyFunctor.map f z = Complexified.map f.hom z := rfl

/-- The presheaf `𝒪_X ⊗_ℝ ℂ`, `U ↦ Γ(U, 𝒪_X)[i]`, of a presheaf of rings `𝒪_X`. -/
abbrev complexifyPresheaf {X : TopCat.{u}} (F : X.Presheaf CommRingCat.{u}) :
    X.Presheaf CommRingCat.{u} :=
  F ⋙ complexifyFunctor

section Sheaf

variable {X : TopCat.{u}} (F : X.Presheaf CommRingCat.{u})

theorem complexifyPresheaf_obj (U : (Opens X)ᵒᵖ) :
    (complexifyPresheaf F).obj U = CommRingCat.of (Complexified (F.obj U)) := rfl

theorem complexifyPresheaf_map_apply {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (z : Complexified (F.obj U)) :
    (complexifyPresheaf F).map i z = Complexified.map (F.map i).hom z := rfl

/-- The presheaf `U ↦ Γ(U, 𝒪_X)[i]` of a sheaf of rings is a sheaf: a compatible family of pairs
`(a_j + b_j i)` glues uniquely because the families `(a_j)` and `(b_j)` do. -/
theorem isSheaf_complexifyPresheaf (hF : F.IsSheaf) : (complexifyPresheaf F).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget CommRingCat.{u}),
    TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types]
  intro ι U sf hsf
  let G : X.Sheaf CommRingCat.{u} := ⟨F, hF⟩
  have hre : TopCat.Presheaf.IsCompatible F U fun i => (sf i).re := fun i j =>
    congrArg Complexified.re (hsf i j)
  have him : TopCat.Presheaf.IsCompatible F U fun i => (sf i).im := fun i j =>
    congrArg Complexified.im (hsf i j)
  obtain ⟨a, ha, ha'⟩ := G.existsUnique_gluing U _ hre
  obtain ⟨b, hb, hb'⟩ := G.existsUnique_gluing U _ him
  refine ⟨⟨a, b⟩, fun i => ?_, fun s hs => ?_⟩
  · exact Complexified.ext (ha i) (hb i)
  · exact Complexified.ext (ha' s.re fun i => congrArg Complexified.re (hs i))
      (hb' s.im fun i => congrArg Complexified.im (hs i))

/-! ### Stalks: `(𝒪_X ⊗_ℝ ℂ)_x = 𝒪_{X,x}[i]` -/

variable (x : X)

/-- The canonical map from the stalk of `𝒪_X[i]` to `𝒪_{X,x}[i]`: the germ of `a + b i` goes to
`(germ a) + (germ b) i`. -/
def stalkToComplexified :
    (complexifyPresheaf F).stalk x ⟶ complexifyFunctor.obj (F.stalk x) :=
  colimit.post ((OpenNhds.inclusion x).op ⋙ F) complexifyFunctor

theorem stalkToComplexified_germ (U : Opens X) (hx : x ∈ U)
    (z : (complexifyPresheaf F).obj (op U)) :
    stalkToComplexified F x ((complexifyPresheaf F).germ U x hx z) =
      Complexified.map (F.germ U x hx).hom z := by
  have h := colimit.ι_post ((OpenNhds.inclusion x).op ⋙ F) complexifyFunctor (op ⟨U, hx⟩)
  exact congrArg (fun g : _ ⟶ complexifyFunctor.obj (F.stalk x) => g.hom z) h

theorem stalkToComplexified_surjective : Function.Surjective (stalkToComplexified F x).hom := by
  rintro ⟨α, β⟩
  obtain ⟨U, hU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq F α
  obtain ⟨V, hV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq F β
  let w : (complexifyPresheaf F).obj (op (U ⊓ V)) :=
    ⟨F.map (homOfLE inf_le_left).op a, F.map (homOfLE inf_le_right).op b⟩
  refine ⟨(complexifyPresheaf F).germ (U ⊓ V) x ⟨hU, hV⟩ w, ?_⟩
  refine (stalkToComplexified_germ F x (U ⊓ V) ⟨hU, hV⟩ w).trans ?_
  refine Complexified.ext ?_ ?_
  · exact TopCat.Presheaf.germ_res_apply F (homOfLE inf_le_left) x ⟨hU, hV⟩ a
  · exact TopCat.Presheaf.germ_res_apply F (homOfLE inf_le_right) x ⟨hU, hV⟩ b

theorem stalkToComplexified_injective : Function.Injective (stalkToComplexified F x).hom := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨U, hU, z, rfl⟩ := TopCat.Presheaf.exists_germ_eq (complexifyPresheaf F) t
  change stalkToComplexified F x ((complexifyPresheaf F).germ U x hU z) = 0 at ht
  rw [stalkToComplexified_germ] at ht
  have ha : F.germ U x hU z.re = F.germ U x hU 0 := by
    rw [map_zero]; exact congrArg Complexified.re ht
  have hb : F.germ U x hU z.im = F.germ U x hU 0 := by
    rw [map_zero]; exact congrArg Complexified.im ht
  obtain ⟨W₁, hW₁, i₁, _, e₁⟩ := TopCat.Presheaf.germ_eq F x hU hU _ _ ha
  obtain ⟨W₂, hW₂, i₂, _, e₂⟩ := TopCat.Presheaf.germ_eq F x hU hU _ _ hb
  rw [map_zero] at e₁ e₂
  have hW : x ∈ W₁ ⊓ W₂ := ⟨hW₁, hW₂⟩
  have iW : W₁ ⊓ W₂ ⟶ U := homOfLE (inf_le_left.trans i₁.le)
  have hz : (complexifyPresheaf F).map iW.op z = 0 := by
    refine Complexified.ext ?_ ?_
    · change F.map iW.op z.re = 0
      have := congrArg (F.map (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)).op) e₁
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, map_zero] at this
      exact this
    · change F.map iW.op z.im = 0
      have := congrArg (F.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op) e₂
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, map_zero] at this
      exact this
  rw [← TopCat.Presheaf.germ_res_apply (complexifyPresheaf F) iW x hW z, hz, map_zero]

theorem stalkToComplexified_bijective : Function.Bijective (stalkToComplexified F x).hom :=
  ⟨stalkToComplexified_injective F x, stalkToComplexified_surjective F x⟩

/-- The stalk of `𝒪_X ⊗_ℝ ℂ` at `x` is `𝒪_{X,x} ⊗_ℝ ℂ = 𝒪_{X,x}[i]`. -/
def stalkComplexifyEquiv : (complexifyPresheaf F).stalk x ≃+* Complexified (F.stalk x) :=
  RingEquiv.ofBijective (stalkToComplexified F x).hom (stalkToComplexified_bijective F x)

theorem stalkComplexifyEquiv_germ (U : Opens X) (hx : x ∈ U)
    (z : (complexifyPresheaf F).obj (op U)) :
    stalkComplexifyEquiv F x ((complexifyPresheaf F).germ U x hx z) =
      Complexified.map (F.germ U x hx).hom z :=
  stalkToComplexified_germ F x U hx z

theorem stalkToComplexified_germ' (U : Opens X) (hx : x ∈ U)
    (z : (complexifyPresheaf F).obj (op U)) :
    (stalkToComplexified F x).hom (((complexifyPresheaf F).germ U x hx).hom z) =
      Complexified.map (F.germ U x hx).hom z :=
  stalkToComplexified_germ F x U hx z

instance isIso_stalkToComplexified : IsIso (stalkToComplexified F x) :=
  ⟨⟨CommRingCat.ofHom (stalkComplexifyEquiv F x).symm.toRingHom,
    CommRingCat.hom_ext (RingHom.ext fun t => (stalkComplexifyEquiv F x).symm_apply_apply t),
    CommRingCat.hom_ext (RingHom.ext fun t => (stalkComplexifyEquiv F x).apply_symm_apply t)⟩⟩

end Sheaf

/-! ### Real residue fields -/

namespace KLocallyRingedSpace

/-- An `ℝ`-local-ringed space has real residue fields when every element of every stalk is
congruent modulo the maximal ideal to a constant — the property of the stalks of a preanalytic
`ℝ`-space (quotients of `ℝ{z}`) that makes `𝒪_{X,x} ⊗_ℝ ℂ` a local ring
[Hir64, Ch. 0, §1, p. 120]. -/
class HasRealResidueFields (X : KLocallyRingedSpace.{u} ℝ) : Prop where
  exists_sub_constAt_mem : ∀ (x : X) (s : X.toLocallyRingedSpace.presheaf.stalk x),
    ∃ c : ℝ, s - constAt X x c ∈
      IsLocalRing.maximalIdeal (X.toLocallyRingedSpace.presheaf.stalk x)

theorem constAt_eq_germ (X : KLocallyRingedSpace.{u} ℝ) (x : X) (c : ℝ) :
    constAt X x c =
      X.toLocallyRingedSpace.presheaf.germ ⊤ x trivial (X.algebraMap c) := rfl

/-- The residue-field property passes from the source of an `ℝ`-morphism with surjective base map
to its target: the residue field of `𝒪_{Y,f x}` embeds into that of `𝒪_{X,x}` through the local
homomorphism `f_x^♯`, which carries constants to constants. -/
theorem exists_sub_constAt_mem_of_hom {X Y : KLocallyRingedSpace.{u} ℝ} (f : X ⟶ Y) (x : X)
    (hX : ∀ s : X.toLocallyRingedSpace.presheaf.stalk x,
      ∃ c : ℝ, s - constAt X x c ∈ IsLocalRing.maximalIdeal _)
    (t : Y.toLocallyRingedSpace.presheaf.stalk (f.1.base x)) :
    ∃ c : ℝ, t - constAt Y (f.1.base x) c ∈ IsLocalRing.maximalIdeal _ := by
  obtain ⟨c, hc⟩ := hX ((f.1.stalkMap x).hom t)
  refine ⟨c, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hc ⊢
  intro hu
  apply hc
  have := hu.map (f.1.stalkMap x).hom
  rwa [map_sub, constAt_eq_germ, f.algebraMap_stalk] at this

/-- The residue-field property passes from the target of an `ℝ`-morphism with surjective stalk
map to its source. -/
theorem exists_sub_constAt_mem_of_surjective {X Y : KLocallyRingedSpace.{u} ℝ} (f : X ⟶ Y) (x : X)
    (hf : Function.Surjective (f.1.stalkMap x).hom)
    (hY : ∀ t : Y.toLocallyRingedSpace.presheaf.stalk (f.1.base x),
      ∃ c : ℝ, t - constAt Y (f.1.base x) c ∈ IsLocalRing.maximalIdeal _)
    (s : X.toLocallyRingedSpace.presheaf.stalk x) :
    ∃ c : ℝ, s - constAt X x c ∈ IsLocalRing.maximalIdeal _ := by
  obtain ⟨t, rfl⟩ := hf s
  obtain ⟨c, hc⟩ := hY t
  refine ⟨c, ?_⟩
  rw [constAt_eq_germ, ← f.algebraMap_stalk, ← map_sub]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hc ⊢
  intro hu
  exact hc (IsLocalHom.map_nonunit _ hu)

theorem hasRealResidueFields_of_hom_surjective {X Y : KLocallyRingedSpace.{u} ℝ} (f : X ⟶ Y)
    (hf : ∀ x, Function.Surjective (f.1.stalkMap x).hom) [HasRealResidueFields Y] :
    HasRealResidueFields X :=
  ⟨fun x => exists_sub_constAt_mem_of_surjective f x (hf x)
    (HasRealResidueFields.exists_sub_constAt_mem (f.1.base x))⟩

theorem hasRealResidueFields_of_hom_surjective_base {X Y : KLocallyRingedSpace.{u} ℝ} (f : X ⟶ Y)
    (hf : Function.Surjective f.1.base) [HasRealResidueFields X] : HasRealResidueFields Y :=
  ⟨fun y t => by
    obtain ⟨x, rfl⟩ := hf y
    exact exists_sub_constAt_mem_of_hom f x (HasRealResidueFields.exists_sub_constAt_mem x) t⟩

/-- Transport along a `K`-isomorphism. -/
theorem hasRealResidueFields_of_kIso {A B : KLocallyRingedSpace.{u} ℝ} (e : KIso A B)
    [HasRealResidueFields B] : HasRealResidueFields A :=
  hasRealResidueFields_of_hom_surjective_base e.inv fun a =>
    ⟨e.hom.1.base a, by
      change (e.hom ≫ e.inv).1.base a = a
      rw [e.hom_inv_id]; rfl⟩

/-- The open subspace `X | U` of a space with real residue fields has real residue fields (the
stalk maps of the open immersion are isomorphisms). -/
instance hasRealResidueFields_restrictOpen (X : KLocallyRingedSpace.{u} ℝ) [HasRealResidueFields X]
    (U : Opens X) : HasRealResidueFields (X.restrictOpen U) :=
  hasRealResidueFields_of_hom_surjective (ofRestrict X U) fun x => by
    have : IsIso ((ofRestrict X U).1.stalkMap x) := inferInstanceAs
      (IsIso ((X.toLocallyRingedSpace.ofRestrict (Opens.isOpenEmbedding U)).stalkMap x))
    exact (ConcreteCategory.bijective_of_isIso ((ofRestrict X U).1.stalkMap x)).2

/-- The quotient by an ideal sheaf of a space with real residue fields has real residue fields
(the stalk maps of the canonical morphism are the quotient maps, surjective). -/
instance hasRealResidueFields_quotient (X : KLocallyRingedSpace.{u} ℝ) [HasRealResidueFields X]
    (J : Manifold.IdealSheaf X.toLocallyRingedSpace.𝒪) :
    HasRealResidueFields (X.quotient J) :=
  hasRealResidueFields_of_hom_surjective (quotientι X J) fun z =>
    QuotientSpace.stalkMap_surjective X.toLocallyRingedSpace J z

/-- A germ of `𝒜_{ℝⁿ}` is congruent modulo the maximal ideal to its value. -/
theorem exists_sub_constAt_mem_affine (n : ℕ) (q : Kn.{u} ℝ n)
    (s : (affine.{u} ℝ n).toLocallyRingedSpace.presheaf.stalk q) :
    ∃ c : ℝ, s - constAt (affine.{u} ℝ n) q c ∈ IsLocalRing.maximalIdeal _ := by
  refine ⟨Manifold.eval ℝ (Kn.{u} ℝ n) (Kn.{u} ℝ n) q s, ?_⟩
  have h : ∀ t : (Manifold.structureSheaf ℝ (Kn.{u} ℝ n) (Kn.{u} ℝ n)).presheaf.stalk q,
      t - Manifold.const ℝ (Kn.{u} ℝ n) (Kn.{u} ℝ n) q
        (Manifold.eval ℝ (Kn.{u} ℝ n) (Kn.{u} ℝ n) q t) ∈
        IsLocalRing.maximalIdeal _ := fun t => by
    rw [Manifold.mem_maximalIdeal_iff_eval, map_sub, Manifold.eval_const,
      sub_self]
  exact h s

/-- `(ℝⁿ, 𝒜_{ℝⁿ})` has real residue fields: a germ is congruent to its value. -/
instance hasRealResidueFields_affine (n : ℕ) : HasRealResidueFields (affine.{u} ℝ n) :=
  ⟨fun q s => exists_sub_constAt_mem_affine n q s⟩

instance hasRealResidueFields_analyticSpaceOfOpen (n : ℕ) (G : Opens (Kn.{u} ℝ n)) :
    HasRealResidueFields (analyticSpaceOfOpen.{u} ℝ n G) :=
  hasRealResidueFields_restrictOpen (affine.{u} ℝ n) G

instance hasRealResidueFields_localModel (n : ℕ) (G : Opens (Kn.{u} ℝ n)) {k : ℕ}
    (f : Fin k → AnalyticFun ℝ n G) : HasRealResidueFields (localModel.{u} ℝ n G f) :=
  hasRealResidueFields_quotient (analyticSpaceOfOpen.{u} ℝ n G) (modelIdeal ℝ n G f)

end KLocallyRingedSpace

/-- Every analytic `ℝ`-space has real residue fields: near every point it is `ℝ`-isomorphic to a
local model, whose stalks are quotients of `𝒜_{ℝⁿ,q}`. -/
instance hasRealResidueFields (X : AnalyticSpace.{u} ℝ) :
    KLocallyRingedSpace.HasRealResidueFields X.toKLocallyRingedSpace :=
  ⟨fun x s => by
    obtain ⟨U, hxU, n, k, G, f, ⟨e⟩⟩ := AnalyticSpace.exists_kIso_localModel X x
    have hU : KLocallyRingedSpace.HasRealResidueFields (X.toKLocallyRingedSpace.restrictOpen U) :=
      KLocallyRingedSpace.hasRealResidueFields_of_kIso e
    exact KLocallyRingedSpace.exists_sub_constAt_mem_of_hom
      (KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace U) ⟨x, hxU⟩
      (hU.exists_sub_constAt_mem ⟨x, hxU⟩) s⟩

/-! ### The complexification `X(ℂ)` -/

namespace KLocallyRingedSpace

variable (X : KLocallyRingedSpace.{u} ℝ) [HasRealResidueFields X]

theorem isLocalRing_stalk_complexified (x : X) :
    IsLocalRing (Complexified (X.toLocallyRingedSpace.presheaf.stalk x)) :=
  Complexified.isLocalRing_of_exists_sub_mem (constAt X x)
    (HasRealResidueFields.exists_sub_constAt_mem x)

theorem isLocalRing_stalk_complexifyPresheaf (x : X) :
    IsLocalRing ((complexifyPresheaf X.toLocallyRingedSpace.presheaf).stalk x) := by
  have := isLocalRing_stalk_complexified X x
  have e := stalkComplexifyEquiv X.toLocallyRingedSpace.presheaf x
  have : Nontrivial ((complexifyPresheaf X.toLocallyRingedSpace.presheaf).stalk x) :=
    e.surjective.nontrivial
  exact IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective

/-- The complexification `X(ℂ) = (|X|, 𝒪_X ⊗_ℝ ℂ)` of an `ℝ`-local-ringed space with real residue
fields [Hir64, Ch. 0, §1, p. 120], a `ℂ`-local-ringed space; the `ℂ`-structure sends `c` to
`Re c + Im c · i` on the constants of `X`. -/
@[implicit_reducible]
def complexify : KLocallyRingedSpace.{u} ℂ where
  carrier := X.toLocallyRingedSpace.carrier
  presheaf := complexifyPresheaf X.toLocallyRingedSpace.presheaf
  IsSheaf := isSheaf_complexifyPresheaf _ X.toLocallyRingedSpace.IsSheaf
  isLocalRing := isLocalRing_stalk_complexifyPresheaf X
  algebraMap := Complexified.algebraMapComplex X.algebraMap

theorem complexify_presheaf_obj (U : (Opens X)ᵒᵖ) :
    (complexify X).toLocallyRingedSpace.presheaf.obj U =
      CommRingCat.of (Complexified (X.toLocallyRingedSpace.presheaf.obj U)) := rfl

theorem complexify_algebraMap (c : ℂ) :
    (complexify X).algebraMap c = Complexified.algebraMapComplex X.algebraMap c := rfl

/-- The stalk of `X(ℂ)` at `x` is `𝒪_{X,x} ⊗_ℝ ℂ`. -/
def complexifyStalkEquiv (x : X) :
    (complexify X).toLocallyRingedSpace.presheaf.stalk x ≃+*
      Complexified (X.toLocallyRingedSpace.presheaf.stalk x) :=
  stalkComplexifyEquiv X.toLocallyRingedSpace.presheaf x

/-! ### Functoriality: Hironaka's `h_ℂ` -/

variable {X}
variable {Y : KLocallyRingedSpace.{u} ℝ} [HasRealResidueFields Y]

/-- The complexified sheaf map of a morphism, as a morphism of presheafed spaces. -/
def complexifyHomAux (f : X ⟶ Y) :
    (complexify X).toPresheafedSpace ⟶ (complexify Y).toPresheafedSpace where
  base := f.1.base
  c := Functor.whiskerRight f.1.c complexifyFunctor

theorem complexifyHomAux_c_app (f : X ⟶ Y) (U : (Opens Y)ᵒᵖ)
    (z : Complexified (Y.toLocallyRingedSpace.presheaf.obj U)) :
    (complexifyHomAux f).c.app U z = Complexified.map (f.1.c.app U).hom z := rfl

/-- The stalk map of the complexified morphism is the complexified stalk map, through the
identifications of the stalks. -/
theorem stalkMap_complexifyHomAux (f : X ⟶ Y) (x : X) :
    (complexifyHomAux f).stalkMap x ≫ stalkToComplexified X.toLocallyRingedSpace.presheaf x =
      stalkToComplexified Y.toLocallyRingedSpace.presheaf (f.1.base x) ≫
        complexifyFunctor.map (f.1.stalkMap x) := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hxU
  have e1 := PresheafedSpace.stalkMap_germ_assoc (complexifyHomAux f) U x hxU
    (stalkToComplexified X.toLocallyRingedSpace.presheaf x)
  refine e1.trans ?_
  have e2 : (complexifyPresheaf X.toLocallyRingedSpace.presheaf).germ
      ((Opens.map f.1.base).obj U) x hxU ≫ stalkToComplexified X.toLocallyRingedSpace.presheaf x =
      complexifyFunctor.map
        (X.toLocallyRingedSpace.presheaf.germ ((Opens.map f.1.base).obj U) x hxU) :=
    colimit.ι_post ((OpenNhds.inclusion x).op ⋙ X.toLocallyRingedSpace.presheaf)
      complexifyFunctor (op ⟨(Opens.map f.1.base).obj U, hxU⟩)
  have e3 : (complexifyPresheaf Y.toLocallyRingedSpace.presheaf).germ U (f.1.base x) hxU ≫
      stalkToComplexified Y.toLocallyRingedSpace.presheaf (f.1.base x) =
      complexifyFunctor.map (Y.toLocallyRingedSpace.presheaf.germ U (f.1.base x) hxU) :=
    colimit.ι_post ((OpenNhds.inclusion (f.1.base x)).op ⋙ Y.toLocallyRingedSpace.presheaf)
      complexifyFunctor (op ⟨U, hxU⟩)
  have e4 := PresheafedSpace.stalkMap_germ f.1.toShHom.hom U x hxU
  calc complexifyFunctor.map (f.1.toShHom.hom.c.app (op U)) ≫
        (complexifyPresheaf X.toLocallyRingedSpace.presheaf).germ
          ((Opens.map f.1.base).obj U) x hxU ≫
          stalkToComplexified X.toLocallyRingedSpace.presheaf x
      = complexifyFunctor.map (f.1.toShHom.hom.c.app (op U)) ≫
          complexifyFunctor.map
            (X.toLocallyRingedSpace.presheaf.germ ((Opens.map f.1.base).obj U) x hxU) :=
        congrArg (fun h => complexifyFunctor.map (f.1.toShHom.hom.c.app (op U)) ≫ h) e2
    _ = complexifyFunctor.map (f.1.toShHom.hom.c.app (op U) ≫
          X.toLocallyRingedSpace.presheaf.germ ((Opens.map f.1.base).obj U) x hxU) :=
        (Functor.map_comp _ _ _).symm
    _ = complexifyFunctor.map (Y.toLocallyRingedSpace.presheaf.germ U (f.1.base x) hxU ≫
          f.1.toShHom.hom.stalkMap x) :=
        congrArg complexifyFunctor.map e4.symm
    _ = complexifyFunctor.map (Y.toLocallyRingedSpace.presheaf.germ U (f.1.base x) hxU) ≫
          complexifyFunctor.map (f.1.toShHom.hom.stalkMap x) := Functor.map_comp _ _ _
    _ = (complexifyPresheaf Y.toLocallyRingedSpace.presheaf).germ U (f.1.base x) hxU ≫
          stalkToComplexified Y.toLocallyRingedSpace.presheaf (f.1.base x) ≫
            complexifyFunctor.map (f.1.stalkMap x) := by
        rw [← Category.assoc]
        exact congrArg (fun h => h ≫ complexifyFunctor.map (f.1.stalkMap x)) e3.symm

theorem isLocalHom_stalkMap_complexifyHomAux (f : X ⟶ Y) (x : X) :
    IsLocalHom ((complexifyHomAux f).stalkMap x).hom := by
  have e : (complexifyHomAux f).stalkMap x =
      (stalkToComplexified Y.toLocallyRingedSpace.presheaf (f.1.base x) ≫
        complexifyFunctor.map (f.1.stalkMap x)) ≫
          inv (stalkToComplexified X.toLocallyRingedSpace.presheaf x) :=
    (IsIso.eq_comp_inv _).mpr (stalkMap_complexifyHomAux f x)
  have h1 : IsLocalHom (complexifyFunctor.map (f.1.stalkMap x)).hom := by
    have := isLocalRing_stalk_complexified X x
    have := isLocalRing_stalk_complexified Y (f.1.base x)
    exact Complexified.isLocalHom_map (f.1.stalkMap x).hom
  have h2 : IsLocalHom (inv (stalkToComplexified X.toLocallyRingedSpace.presheaf x)).hom :=
    isLocalHom_of_iso (asIso (stalkToComplexified X.toLocallyRingedSpace.presheaf x)).symm
  have h3 : IsLocalHom (stalkToComplexified Y.toLocallyRingedSpace.presheaf (f.1.base x)).hom :=
    isLocalHom_of_iso (asIso (stalkToComplexified Y.toLocallyRingedSpace.presheaf (f.1.base x)))
  have h5 : IsLocalHom (stalkToComplexified Y.toLocallyRingedSpace.presheaf (f.1.base x) ≫
      complexifyFunctor.map (f.1.stalkMap x)).hom :=
    @CommRingCat.isLocalHom_comp _ _ _ _ _ h1 h3
  rw [e]
  exact @CommRingCat.isLocalHom_comp _ _ _ _ _ h2 h5

/-- The `ℂ`-morphism `h_ℂ : X(ℂ) ⟶ Y(ℂ)` induced by an `ℝ`-morphism `h : X ⟶ Y`
[Hir64, Ch. 0, §1, p. 120]: the same base map, the complexified sheaf map. -/
def complexifyHom (f : X ⟶ Y) : complexify X ⟶ complexify Y :=
  ⟨⟨complexifyHomAux f, isLocalHom_stalkMap_complexifyHomAux f⟩, by
    have h := f.2
    rw [LocallyRingedSpace.Γ_map_op] at h
    rw [LocallyRingedSpace.Γ_map_op]
    exact RingHom.ext fun c =>
      Complexified.ext (RingHom.congr_fun h c.re) (RingHom.congr_fun h c.im)⟩

theorem complexifyHom_val (f : X ⟶ Y) : (complexifyHom f).1.1 = complexifyHomAux f := rfl

theorem complexifyHom_base (f : X ⟶ Y) : (complexifyHom f).1.base = f.1.base := rfl

theorem toFun_complexifyHom (f : X ⟶ Y) : Hom.toFun (complexifyHom f) = Hom.toFun f := rfl

theorem complexifyHom_id : complexifyHom (𝟙 X) = 𝟙 (complexify X) := by
  apply Hom.ext
  apply LocallyRingedSpace.Hom.ext'
  apply PresheafedSpace.Hom.ext _ _ rfl
  ext U : 2
  simp

theorem complexifyHom_comp {Z : KLocallyRingedSpace.{u} ℝ} [HasRealResidueFields Z] (f : X ⟶ Y)
    (g : Y ⟶ Z) : complexifyHom (f ≫ g) = complexifyHom f ≫ complexifyHom g := by
  apply Hom.ext
  apply LocallyRingedSpace.Hom.ext'
  apply PresheafedSpace.Hom.ext _ _ rfl
  ext U : 2
  simp

/-- The stalk map of `h_ℂ` at `x` is the complexified stalk map of `h`, through the stalk
identifications. -/
theorem complexifyStalkEquiv_stalkMap_complexifyHom (f : X ⟶ Y) (x : X)
    (t : (complexify Y).toLocallyRingedSpace.presheaf.stalk (f.1.base x)) :
    complexifyStalkEquiv X x (((complexifyHom f).1.stalkMap x).hom t) =
      Complexified.map (f.1.stalkMap x).hom (complexifyStalkEquiv Y (f.1.base x) t) := by
  have h := congrArg CommRingCat.Hom.hom (stalkMap_complexifyHomAux f x)
  simp only [CommRingCat.hom_comp] at h
  exact RingHom.congr_fun h t

/-! ### Complexification commutes with open subspaces -/

variable (X)

/-- `X(ℂ) | U = (X | U)(ℂ)`: the two `ℂ`-local-ringed spaces have the same carrier and structure
sheaf; only the `ℂ`-structures differ syntactically, and they agree. -/
def complexifyRestrictIso (U : Opens X) :
    complexify (X.restrictOpen U) ≅ (complexify X).restrictOpen U where
  hom := ⟨𝟙 _, RingHom.ext fun _ => Complexified.ext rfl rfl⟩
  inv := ⟨𝟙 _, RingHom.ext fun _ => Complexified.ext rfl rfl⟩
  hom_inv_id := Hom.ext (Category.id_comp _)
  inv_hom_id := Hom.ext (Category.id_comp _)

end KLocallyRingedSpace

end AnalyticSpace
