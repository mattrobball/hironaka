/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Complexification
public import Hironaka.AnalyticSpace.OpenSubspaceLemmas
public import Hironaka.AnalyticSpace.Restrict.Defs
public import Hironaka.AnalyticSpace.Glue
import Hironaka.AnalyticSpace.StalkMapLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Restriction of a complexification to an open subspace

If `(Y, f)` is a complexification of the open subspace `X | U` of an analytic `ℝ`-space `X`
(`Complexification`, `Hironaka.AnalyticSpace.Complexification`; the analytic complexifications of
[Hir64, Ch. 0, §1, p. 120]: `f(X)` closed in `Y`, `f` a `ℂ`-isomorphism of `X(ℂ)` onto `Y | f(X)`)
and `V ≤ U` is a smaller open subset, then `(Y | W, f | V)` with `W = Y ∖ f(U ∖ V)` is a
complexification of `X | V` (`Complexification.restrictLe`). This is the elementary step of the
gluing of local complexifications [BW59, Proposition 1]: the local complexifications of a cover are
restricted to the overlaps before their germs are compared. Also here: `complexifyIso`, the
complexification of a `K`-isomorphism of `ℝ`-spaces as a `ℂ`-isomorphism (`complexifyHom` in both
directions), which transports a complexification along an isomorphism of the real space.

Conventions. `f(U ∖ V)` is closed in `Y` (`isClosed_imageDiff`): `f(U)` is closed and `f(U ∩ V)` is
open in `f(U)` because `f` is an embedding, so `f(U ∖ V) = f(U) ∖ f(U ∩ V)` is closed. The
restricted morphism `restrictLeHom` is `f | V` composed with the identification
`(X | U) | V ≅ X | V` (`restrictOpen_restrictOpen_iso`, `imageOpens_map_eq`) and with
`complexifyRestrictIso` (`Hironaka.AnalyticSpace.Complexify`); its stalk maps are conjugate to those
of `f` by the stalk isomorphisms of the open immersions
(`KLocallyRingedSpace.isIso_ofRestrict_stalkMap`) and of the `K`-isomorphisms. For `V = U`, `W = Y`
and the restriction is `f` up to the identifications; for `V = ⊥`, `X | ⊥` is empty, `W = Y ∖ f(U)`,
and the empty morphism is a complexification.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Topology
open AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace

noncomputable section

universe u

namespace KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- The complexification of a `K`-isomorphism of `ℝ`-spaces is a `ℂ`-isomorphism. -/
def complexifyIso {A B : KLocallyRingedSpace.{u} ℝ} [HasRealResidueFields A]
    [HasRealResidueFields B] (e : KIso A B) : KIso (complexify A) (complexify B) where
  hom := complexifyHom e.hom
  inv := complexifyHom e.inv
  hom_inv_id := by rw [← complexifyHom_comp, e.hom_inv_id, complexifyHom_id]
  inv_hom_id := by rw [← complexifyHom_comp, e.inv_hom_id, complexifyHom_id]

end KLocallyRingedSpace

namespace Complexification

variable {X : AnalyticSpace.{u} ℝ} {U : Opens X} (C : Complexification (X.restrictOpen U))

/-- The morphism `f` of the complexification, typed on `X.toK | U` (the same term; the uniform
typing lets the restriction lemmas of `Hironaka.AnalyticSpace.OpenSubspaceLemmas` apply
syntactically).
-/
def fK : complexify (X.toKLocallyRingedSpace.restrictOpen U) ⟶ C.Y.toKLocallyRingedSpace := C.f

theorem toFun_fK : KLocallyRingedSpace.Hom.toFun C.fK = KLocallyRingedSpace.Hom.toFun C.f := rfl

/-- The image `f(U ∖ V)` of the real points of `U` outside `V`. -/
def imageDiff (V : Opens X) : Set C.Y :=
  KLocallyRingedSpace.Hom.toFun C.f '' {u : X.restrictOpen U | u.1 ∉ V}

theorem mem_imageDiff {V : Opens X} {y : C.Y} :
    y ∈ C.imageDiff V ↔ ∃ u : X.restrictOpen U, u.1 ∉ V ∧ KLocallyRingedSpace.Hom.toFun C.f u = y :=
  Iff.rfl

/-- `f(U ∖ V)` is closed in `Y`: `f(U)` is closed and `f(U ∩ V)` is open in it. -/
theorem isClosed_imageDiff (V : Opens X) : IsClosed (C.imageDiff V) := by
  have hV : IsOpen {u : X.restrictOpen U | u.1 ∈ V} :=
    V.isOpen.preimage continuous_subtype_val
  obtain ⟨O, hO, hOeq⟩ := (C.isEmbedding.isInducing.isOpen_iff).mp hV
  have heq : C.imageDiff V = Set.range (KLocallyRingedSpace.Hom.toFun C.f) ∩ Oᶜ := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨⟨u, rfl⟩, fun hy => hu ?_⟩
      have : u ∈ KLocallyRingedSpace.Hom.toFun C.f ⁻¹' O := hy
      rw [hOeq] at this
      exact this
    · rintro ⟨⟨u, rfl⟩, hy⟩
      refine ⟨u, fun hu => hy ?_, rfl⟩
      have : u ∈ KLocallyRingedSpace.Hom.toFun C.f ⁻¹' O := by rw [hOeq]; exact hu
      exact this
  rw [heq]
  exact C.isClosed_range.inter hO.isClosed_compl

/-- The open `W = Y ∖ f(U ∖ V)` on which the restricted complexification lives. -/
def restrictLeOpens (V : Opens X) : Opens C.Y :=
  ⟨(C.imageDiff V)ᶜ, (C.isClosed_imageDiff V).isOpen_compl⟩

theorem mem_restrictLeOpens {V : Opens X} {y : C.Y} :
    y ∈ C.restrictLeOpens V ↔ ∀ u : X.restrictOpen U, KLocallyRingedSpace.Hom.toFun C.f u = y → u.1
        ∈ V := by
  change y ∉ C.imageDiff V ↔ _
  rw [mem_imageDiff]
  constructor
  · intro h u hu
    by_contra hv
    exact h ⟨u, hv, hu⟩
  · rintro h ⟨u, hv, hu⟩
    exact hv (h u hu)

/-- The real points of `V` land in `W`. -/
theorem toFun_mem_restrictLeOpens {V : Opens X} (u : X.restrictOpen U) (hu : u.1 ∈ V) :
    KLocallyRingedSpace.Hom.toFun C.f u ∈ C.restrictLeOpens V := by
  rw [mem_restrictLeOpens]
  intro u' hu'
  have : u' = u := C.injective_toFun hu'
  rw [this]
  exact hu

/-- `V` as an open of `X | U`. -/
def pullbackOpens (V : Opens X) : Opens (X.toKLocallyRingedSpace.restrictOpen U) :=
  (Opens.map (ofRestrict X.toKLocallyRingedSpace U).1.base).obj V

theorem mem_pullbackOpens {V : Opens X} {u : X.restrictOpen U} :
    u ∈ pullbackOpens (X := X) (U := U) V ↔ u.1 ∈ V :=
  Iff.rfl

/-- The identification `(X | U) | V ≅ X | V` for `V ≤ U` (`restrictOpen_restrictOpen_iso`). -/
def restrictRestrictIso (V : Opens X) (hV : V ≤ U) :
    (X.toKLocallyRingedSpace.restrictOpen U).restrictOpen (pullbackOpens (X := X) (U := U) V) ≅
      X.toKLocallyRingedSpace.restrictOpen V :=
  restrictOpen_restrictOpen_iso U (pullbackOpens (X := X) (U := U) V) ≪≫
    eqToIso (congrArg X.toKLocallyRingedSpace.restrictOpen
      (imageOpens_map_eq X.toKLocallyRingedSpace hV))

/-- The pointwise form of `f | V`: `u ↦ f(u)` into `W`. -/
def restrictFun (V : Opens X) :
    (X.toKLocallyRingedSpace.restrictOpen U).restrictOpen (pullbackOpens (X := X) (U := U) V) →
      C.restrictLeOpens V :=
  fun u => ⟨KLocallyRingedSpace.Hom.toFun C.fK u.1, C.toFun_mem_restrictLeOpens u.1 u.2⟩

theorem isEmbedding_restrictFun (V : Opens X) : IsEmbedding (C.restrictFun V) :=
  (C.isEmbedding.comp IsEmbedding.subtypeVal).codRestrict _ _

/-- The restricted morphism `f | V : (X | V)(ℂ) ⟶ Y | W`. -/
def restrictLeHom (V : Opens X) (hV : V ≤ U) :
    complexify (X.restrictOpen V).toKLocallyRingedSpace ⟶
      (C.Y.restrictOpen (C.restrictLeOpens V)).toKLocallyRingedSpace :=
  (complexifyIso (restrictRestrictIso (X := X) (U := U) V hV)).inv ≫
    (complexifyRestrictIso (X.toKLocallyRingedSpace.restrictOpen U)
      (pullbackOpens (X := X) (U := U) V)).hom ≫
    Hom.restrictTo C.fK (pullbackOpens (X := X) (U := U) V) (C.restrictLeOpens V)
      (fun u hu => C.toFun_mem_restrictLeOpens u hu)

theorem toFun_restrictLeHom (V : Opens X) (hV : V ≤ U) :
    KLocallyRingedSpace.Hom.toFun (C.restrictLeHom V hV) =
      C.restrictFun V ∘ KLocallyRingedSpace.Hom.toFun (restrictRestrictIso (X := X) (U :=
          U) V hV).inv := by
  funext v
  apply Subtype.ext
  exact Hom.toFun_restrictTo C.fK (pullbackOpens (X := X) (U := U) V) (C.restrictLeOpens V)
    (fun u hu => C.toFun_mem_restrictLeOpens u hu) _

/-- The range of the restricted morphism is the trace of `f(U)` on `W`. -/
theorem range_toFun_restrictLeHom (V : Opens X) (hV : V ≤ U) :
    Set.range (KLocallyRingedSpace.Hom.toFun (C.restrictLeHom V hV)) =
      Subtype.val ⁻¹' Set.range (KLocallyRingedSpace.Hom.toFun C.f) := by
  ext ⟨y, hy⟩
  rw [C.toFun_restrictLeHom V hV]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨_, congrArg Subtype.val hv⟩
  · rintro ⟨u, hu⟩
    have huV : u.1 ∈ V := (mem_restrictLeOpens C).mp hy u hu
    let e := restrictRestrictIso (X := X) (U := U) V hV
    let u' : (X.toKLocallyRingedSpace.restrictOpen U).restrictOpen
        (pullbackOpens (X := X) (U := U) V) :=
      (⟨u, huV⟩ : pullbackOpens (X := X) (U := U) V)
    refine ⟨(KLocallyRingedSpace.Hom.toFun e.hom u' : X.toKLocallyRingedSpace.restrictOpen V), ?_⟩
    have hinv : KLocallyRingedSpace.Hom.toFun e.inv (KLocallyRingedSpace.Hom.toFun e.hom u') = u' :=
      congrArg (fun φ => KLocallyRingedSpace.Hom.toFun φ u') e.hom_inv_id
    rw [Function.comp_apply, hinv]
    exact Subtype.ext hu

/-- The stalk maps of the restricted morphism are bijective. -/
theorem bijective_stalkMap_restrictLeHom (V : Opens X) (hV : V ≤ U)
    (v : complexify (X.restrictOpen V).toKLocallyRingedSpace) :
    Function.Bijective ((C.restrictLeHom V hV).1.stalkMap v).hom := by
  let a := (complexifyIso (restrictRestrictIso (X := X) (U := U) V hV)).inv
  let b := (complexifyRestrictIso (X.toKLocallyRingedSpace.restrictOpen U)
    (pullbackOpens (X := X) (U := U) V)).hom
  let c := Hom.restrictTo C.fK (pullbackOpens (X := X) (U := U) V) (C.restrictLeOpens V)
    (fun u hu => C.toFun_mem_restrictLeOpens u hu)
  have ha : IsIso (a.1.stalkMap v) := (ConcreteCategory.isIso_iff_bijective _).mpr
    (KIso.bijective_stalkMap (complexifyIso (restrictRestrictIso (X := X) (U := U) V hV)).symm v)
  have hb : IsIso (b.1.stalkMap (a.1.base v)) := (ConcreteCategory.isIso_iff_bijective _).mpr
    (KIso.bijective_stalkMap (complexifyRestrictIso _ _) _)
  have hc : IsIso (c.1.stalkMap (b.1.base (a.1.base v))) :=
    isIso_stalkMap_restrictTo C.fK _ _ _ _
      ((ConcreteCategory.isIso_iff_bijective _).mpr (C.bijective_stalkMap _))
  have hbc : IsIso ((b.1 ≫ c.1).stalkMap (a.1.base v)) :=
    (congrArg (fun φ => IsIso φ) (LocallyRingedSpace.stalkMap_comp b.1 c.1 (a.1.base v))).mpr
      (IsIso.comp_isIso' hc hb)
  have habc : IsIso ((a.1 ≫ b.1 ≫ c.1).stalkMap v) :=
    (congrArg (fun φ => IsIso φ) (LocallyRingedSpace.stalkMap_comp a.1 (b.1 ≫ c.1) v)).mpr
      (IsIso.comp_isIso' hbc ha)
  exact (ConcreteCategory.isIso_iff_bijective _).mp habc

/-- The restriction of a complexification of `X | U` to `X | V` along `V ≤ U`: `(Y | W, f | V)` with
`W = Y ∖ f(U ∖ V)`. -/
def restrictLe (V : Opens X) (hV : V ≤ U) : Complexification (X.restrictOpen V) where
  Y := C.Y.restrictOpen (C.restrictLeOpens V)
  f := C.restrictLeHom V hV
  isClosed_range := by
    rw [C.range_toFun_restrictLeHom V hV]
    exact C.isClosed_range.preimage continuous_subtype_val
  isEmbedding := by
    rw [C.toFun_restrictLeHom V hV]
    exact (C.isEmbedding_restrictFun V).comp
      (KIso.homeomorph (restrictRestrictIso (X := X) (U := U) V hV).symm).isEmbedding
  bijective_stalkMap := C.bijective_stalkMap_restrictLeHom V hV

end Complexification

end

end AnalyticSpace
