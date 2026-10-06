/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Hironaka.AnalyticSpace.Defs
import Hironaka.AnalyticSpace.KSpace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Countable disjoint unions of analytic `K`-spaces

The coproduct of a countable family of analytic `K`-spaces, in the category `ℜ/K` of
`K`-local-ringed spaces and in `An/K` [Hir64, Ch. 0, §1]. Not in the sources as a stated result;
the construction is Mathlib's coproduct of locally ringed spaces with the `K`-structure supplied
through the adjunction between global sections and `Spec`.

* **`K`-structures as morphisms to `Spec K`.** Hironaka's `K`-structure `K →+* Γ(X, 𝒪_X)` of a
  `K`-local-ringed space is, under the adjunction `Γ ⊣ Spec`
  (`ΓSpec.locallyRingedSpaceAdjunction`), a morphism of locally ringed spaces `X ⟶ Spec K`
  (`toSpecK`; the field lifted to `Type u`, `specK`); a morphism of locally ringed spaces is a
  `K`-morphism exactly when it is a morphism over `Spec K` (`Hom.comp_toSpecK`, `Hom.ofSpecK`),
  and a morphism `X ⟶ Spec K` makes `X` a `K`-local-ringed space (`ofSpecKHom`,
  `toSpecK_ofSpecKHom`). This is the device by which the coproduct's constants are obtained: no
  global section of the colimit presheaf is built by hand.
* **Coproducts in `ℜ/K`** (`KLocallyRingedSpace.coprod X` for `X : ι → KLocallyRingedSpace K`,
  `ι` countable): the underlying locally ringed space is Mathlib's coproduct
  `LocallyRingedSpace.coproduct` of the underlying spaces (smallness of `ι` from countability),
  the `K`-structure the adjunct of the descent of the components' morphisms to `Spec K`; the
  injections `coprodι` and the descent `coprodDesc` are `K`-morphisms (`coprodι_coprodDesc`,
  `coprod_hom_ext`: the universal property). The injections are open immersions (Mathlib's
  `sigma_ι_isOpenImmersion`), jointly surjective (`exists_coprodι_toFun_eq`) with pairwise
  disjoint images (`coprodι_toFun_ne`, by descending to a two-point space); hence the coproduct
  of Hausdorff spaces is Hausdorff (`t2Space_coprod`) and the countable coproduct of σ-compact
  spaces is σ-compact (`sigmaCompactSpace_coprod`).
* **Coproducts in `An/K`** (`AnalyticSpace.sigma X` for `X : ι → AnalyticSpace K`, `ι`
  countable): the coproduct in `ℜ/K` with Hironaka's clauses — (i) the local-model clause
  componentwise (a point of the coproduct lies in the image of one summand, whose local model is
  transported along the open immersion by `isoOfRangeEq`), (ii) σ-compactness for countable `ι`
  (Hironaka's countability at infinity: the coproduct of an uncountable family is not σ-compact,
  which is why the index type is countable), (iii) Hausdorff. `sigmaι`, `sigmaDesc` are the
  coproduct's injections and descent in `An/K` (whose morphisms are those of `ℜ/K`).

The carrier of the coproduct is Mathlib's colimit, homeomorphic to — not equal to — the `Σ`-type
`Σ i, X i`; statements about the coproduct are therefore made at the level of points through the
injections. The index type lives in an arbitrary universe `v` (the strata of a non-singular
space are indexed by `ℕ`); `Countable ι` supplies `Small.{u} ι`. The universal property and the
isomorphism criterion for descents are in `Hironaka/AnalyticSpace/SigmaLemmas.lean`; the disjoint
union of manifolds and the decomposition of a non-singular space into pure-dimensional strata are
in `Hironaka/AnalyticSpace/SigmaCoproductLemmas.lean`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v

noncomputable section

namespace AnalyticSpace

namespace KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-! ### `K`-structures as morphisms to `Spec K` -/

variable (K) in
/-- `Spec K` as a locally ringed space in universe `u` (the field lifted to `Type u`; an
abbreviation so that the adjunction's lemmas apply to it verbatim). -/
abbrev specK : LocallyRingedSpace.{u} :=
  Spec.toLocallyRingedSpace.obj (op (CommRingCat.of (ULift.{u} K)))

/-- The `K`-structure of `X` as a morphism of rings `ULift K ⟶ Γ(X, 𝒪_X)` in `CommRingCat`. -/
def algebraMapULift (X : KLocallyRingedSpace.{u} K) :
    CommRingCat.of (ULift.{u} K) ⟶ LocallyRingedSpace.Γ.obj (op X.toLocallyRingedSpace) :=
  CommRingCat.ofHom (X.algebraMap.comp ULift.ringEquiv.toRingHom)

/-- The structural morphism `X ⟶ Spec K` of a `K`-local-ringed space [Hir64, Ch. 0, §1, p. 121],
the adjunct of its `K`-structure under `Γ ⊣ Spec`. -/
def toSpecK (X : KLocallyRingedSpace.{u} K) : X.toLocallyRingedSpace ⟶ specK.{u} K :=
  ΓSpec.locallyRingedSpaceAdjunction.homEquiv X.toLocallyRingedSpace
    (op (CommRingCat.of (ULift.{u} K))) X.algebraMapULift.op

theorem homEquiv_symm_toSpecK (X : KLocallyRingedSpace.{u} K) :
    (ΓSpec.locallyRingedSpaceAdjunction.homEquiv X.toLocallyRingedSpace
      (op (CommRingCat.of (ULift.{u} K)))).symm X.toSpecK = X.algebraMapULift.op :=
  Equiv.symm_apply_apply _ _

/-- A `K`-morphism is a morphism over `Spec K`. -/
theorem Hom.comp_toSpecK {X Y : KLocallyRingedSpace.{u} K} (f : X ⟶ Y) :
    f.1 ≫ Y.toSpecK = X.toSpecK := by
  unfold toSpecK
  rw [← Adjunction.homEquiv_naturality_left]
  congr 1
  change (LocallyRingedSpace.Γ.map f.1.op).op ≫ Y.algebraMapULift.op = X.algebraMapULift.op
  rw [← op_comp]
  congr 1
  ext c
  exact RingHom.congr_fun f.2 (ULift.ringEquiv c)

/-- A morphism of locally ringed spaces over `Spec K` is a `K`-morphism. -/
def Hom.ofSpecK {X Y : KLocallyRingedSpace.{u} K}
    (f : X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace) (hf : f ≫ Y.toSpecK = X.toSpecK) :
    X ⟶ Y :=
  ⟨f, by
    have h := congrArg (ΓSpec.locallyRingedSpaceAdjunction.homEquiv X.toLocallyRingedSpace
      (op (CommRingCat.of (ULift.{u} K)))).symm hf
    rw [Adjunction.homEquiv_naturality_left_symm, homEquiv_symm_toSpecK,
      homEquiv_symm_toSpecK] at h
    change (LocallyRingedSpace.Γ.map f.op).op ≫ Y.algebraMapULift.op = X.algebraMapULift.op at h
    rw [← op_comp] at h
    have h' := congrArg (fun g : CommRingCat.of (ULift.{u} K) ⟶ _ => g.hom) (op_injective h)
    ext c
    exact RingHom.congr_fun h' (ULift.up c)⟩

@[simp]
theorem Hom.ofSpecK_val {X Y : KLocallyRingedSpace.{u} K}
    (f : X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace) (hf : f ≫ Y.toSpecK = X.toSpecK) :
    (Hom.ofSpecK f hf).1 = f :=
  rfl

/-- A morphism of locally ringed spaces `X ⟶ Spec K` makes `X` a `K`-local-ringed space: the
`K`-structure is its adjunct (the ring-homomorphism form of a morphism to `Spec K`). -/
def ofSpecKHom (X : LocallyRingedSpace.{u}) (Φ : X ⟶ specK.{u} K) : KLocallyRingedSpace.{u} K where
  toLocallyRingedSpace := X
  algebraMap := ((ΓSpec.locallyRingedSpaceAdjunction.homEquiv X
    (op (CommRingCat.of (ULift.{u} K)))).symm Φ).unop.hom.comp ULift.ringEquiv.symm.toRingHom

theorem toSpecK_ofSpecKHom (X : LocallyRingedSpace.{u}) (Φ : X ⟶ specK.{u} K) :
    (ofSpecKHom X Φ).toSpecK = Φ := by
  have h : (ofSpecKHom X Φ).algebraMapULift.op =
      (ΓSpec.locallyRingedSpaceAdjunction.homEquiv X
        (op (CommRingCat.of (ULift.{u} K)))).symm Φ := by
    conv_rhs => rw [← Quiver.Hom.op_unop ((ΓSpec.locallyRingedSpaceAdjunction.homEquiv X
      (op (CommRingCat.of (ULift.{u} K)))).symm Φ)]
    exact congrArg Quiver.Hom.op rfl
  exact (Equiv.eq_symm_apply _).mp h

/-! ### Coproducts in `ℜ/K` -/

section Coprod

variable {ι : Type v} [Countable ι] (X : ι → KLocallyRingedSpace.{u} K)

/-- The diagram of the underlying locally ringed spaces of a family of `K`-local-ringed
spaces. -/
abbrev coprodDiagram : Discrete ι ⥤ LocallyRingedSpace.{u} :=
  Discrete.functor fun i => (X i).toLocallyRingedSpace

/-- The structural morphism of the coproduct to `Spec K`: the descent of the components'. -/
def coprodToSpecK : LocallyRingedSpace.coproduct (coprodDiagram X) ⟶ specK.{u} K :=
  (LocallyRingedSpace.coproductCofanIsColimit (coprodDiagram X)).desc
    (Cofan.mk (specK.{u} K) fun i => (X i).toSpecK)

/-- **The coproduct of a countable family of `K`-local-ringed spaces**: Mathlib's coproduct
`LocallyRingedSpace.coproduct` of the underlying locally ringed spaces, with the `K`-structure
the adjunct of the descent of the components' structural morphisms to `Spec K`. -/
def coprod : KLocallyRingedSpace.{u} K :=
  ofSpecKHom (LocallyRingedSpace.coproduct (coprodDiagram X)) (coprodToSpecK X)

theorem coprod_toLocallyRingedSpace :
    (coprod X).toLocallyRingedSpace = LocallyRingedSpace.coproduct (coprodDiagram X) :=
  rfl

theorem coprod_toSpecK : (coprod X).toSpecK = coprodToSpecK X :=
  toSpecK_ofSpecKHom _ _

/-- The injection of the `i`-th summand as a morphism of locally ringed spaces: the leg of
Mathlib's coproduct cofan. -/
abbrev coprodιLRS (i : ι) : (X i).toLocallyRingedSpace ⟶ (coprod X).toLocallyRingedSpace :=
  (LocallyRingedSpace.coproductCofan (coprodDiagram X)).ι.app ⟨i⟩

theorem coprodιLRS_comp_toSpecK (i : ι) : coprodιLRS X i ≫ (coprod X).toSpecK = (X i).toSpecK := by
  rw [coprod_toSpecK]
  exact (LocallyRingedSpace.coproductCofanIsColimit (coprodDiagram X)).fac _ ⟨i⟩

/-- **The injection of the `i`-th summand into the coproduct**, a `K`-morphism. -/
def coprodι (i : ι) : X i ⟶ coprod X :=
  Hom.ofSpecK (coprodιLRS X i) (coprodιLRS_comp_toSpecK X i)

theorem coprodι_val (i : ι) : (coprodι X i).1 = coprodιLRS X i :=
  rfl

variable {X} in
/-- **The descent of a family of `K`-morphisms out of the summands**, a `K`-morphism out of the
coproduct. -/
def coprodDesc {Y : KLocallyRingedSpace.{u} K} (f : ∀ i, X i ⟶ Y) : coprod X ⟶ Y :=
  Hom.ofSpecK ((LocallyRingedSpace.coproductCofanIsColimit (coprodDiagram X)).desc
    (Cofan.mk Y.toLocallyRingedSpace fun i => (f i).1)) (by
    apply (LocallyRingedSpace.coproductCofanIsColimit (coprodDiagram X)).hom_ext
    rintro ⟨i⟩
    exact ((LocallyRingedSpace.coproductCofanIsColimit (coprodDiagram X)).fac_assoc
      (Cofan.mk Y.toLocallyRingedSpace fun i => (f i).1) ⟨i⟩ Y.toSpecK).trans
      ((Hom.comp_toSpecK (f i)).trans (coprodιLRS_comp_toSpecK X i).symm))

variable {X} in
theorem coprodDesc_val {Y : KLocallyRingedSpace.{u} K} (f : ∀ i, X i ⟶ Y) :
    (coprodDesc f).1 = (LocallyRingedSpace.coproductCofanIsColimit (coprodDiagram X)).desc
      (Cofan.mk Y.toLocallyRingedSpace fun i => (f i).1) :=
  rfl

variable {X} in
/-- The descent factors the injections (the coproduct's universal property, existence). -/
theorem coprodι_coprodDesc {Y : KLocallyRingedSpace.{u} K} (f : ∀ i, X i ⟶ Y) (i : ι) :
    coprodι X i ≫ coprodDesc f = f i :=
  Hom.ext ((LocallyRingedSpace.coproductCofanIsColimit (coprodDiagram X)).fac _ ⟨i⟩)

variable {X} in
/-- Two `K`-morphisms out of the coproduct agreeing on every summand are equal (the coproduct's
universal property, uniqueness). -/
theorem coprod_hom_ext {Y : KLocallyRingedSpace.{u} K} {g h : coprod X ⟶ Y}
    (H : ∀ i, coprodι X i ≫ g = coprodι X i ≫ h) : g = h :=
  Hom.ext ((LocallyRingedSpace.coproductCofanIsColimit (coprodDiagram X)).hom_ext
    fun ⟨i⟩ => congrArg Subtype.val (H i))

/-! #### The injections as open immersions; points of the coproduct -/

/-- The injections of a coproduct are open immersions (Mathlib's `sigma_ι_isOpenImmersion`). -/
instance isOpenImmersion_coprodι (i : ι) : LocallyRingedSpace.IsOpenImmersion (coprodι X i).1 :=
  inferInstanceAs (SheafedSpace.IsOpenImmersion
    (colimit.ι (coprodDiagram X ⋙ LocallyRingedSpace.forgetToSheafedSpace) ⟨i⟩))

/-- The underlying map of an open immersion of `K`-local-ringed spaces is an open embedding. -/
theorem Hom.isOpenEmbedding_toFun {A B : KLocallyRingedSpace.{u} K} (a : A ⟶ B)
    [LocallyRingedSpace.IsOpenImmersion a.1] : Topology.IsOpenEmbedding (Hom.toFun a) :=
  PresheafedSpace.IsOpenImmersion.base_open (f := a.1.toShHom.hom)

/-- Every point of the coproduct lies in the image of a summand. -/
theorem exists_coprodι_toFun_eq (x : coprod X) :
    ∃ (i : ι) (a : X i), Hom.toFun (coprodι X i) a = x := by
  obtain ⟨⟨i⟩, a, ha⟩ := SheafedSpace.colimit_exists_rep
    (coprodDiagram X ⋙ LocallyRingedSpace.forgetToSheafedSpace) x
  exact ⟨i, a, ha⟩

/-- The injections are injective on points. -/
theorem coprodι_toFun_injective (i : ι) : Function.Injective (Hom.toFun (coprodι X i)) :=
  (Hom.isOpenEmbedding_toFun (coprodι X i)).injective

/-- (Implementation) The cocone over the underlying spaces with vertex the space of
propositions, sending the `j`-th summand to the proposition `j = i₀`. -/
def propCocone (i₀ : ι) :
    Cocone ((coprodDiagram X ⋙ LocallyRingedSpace.forgetToSheafedSpace) ⋙
      SheafedSpace.forget CommRingCat.{u}) where
  pt := TopCat.of (ULift.{u} Prop)
  ι := Discrete.natTrans fun j => TopCat.ofHom ⟨fun _ => ⟨j.as = i₀⟩, continuous_const⟩

/-- The images of distinct summands are disjoint (descend to the two-point space distinguishing
the `i`-th summand from the others; the space of propositions carries the Sierpiński topology,
but only constant maps into it are used). -/
theorem coprodι_toFun_ne {i j : ι} (hij : i ≠ j) (a : X i) (b : X j) :
    Hom.toFun (coprodι X i) a ≠ Hom.toFun (coprodι X j) b := by
  intro h
  set F' := coprodDiagram X ⋙ LocallyRingedSpace.forgetToSheafedSpace
  have hc : IsColimit ((SheafedSpace.forget CommRingCat.{u}).mapCocone (colimit.cocone F')) :=
    isColimitOfPreserves (SheafedSpace.forget CommRingCat.{u}) (colimit.isColimit F')
  have hi := ConcreteCategory.congr_hom (hc.fac (propCocone X i) ⟨i⟩) a
  have hj := ConcreteCategory.congr_hom (hc.fac (propCocone X i) ⟨j⟩) b
  change hc.desc (propCocone X i) (Hom.toFun (coprodι X i) a) = ULift.up (i = i) at hi
  change hc.desc (propCocone X i) (Hom.toFun (coprodι X j) b) = ULift.up (j = i) at hj
  rw [h, hj] at hi
  exact hij (Eq.mpr (congrArg ULift.down hi) (rfl : i = i)).symm

/-! #### Hausdorff and σ-compact -/

/-- The coproduct of Hausdorff spaces is Hausdorff (points in one summand are separated there,
points in distinct summands by the summands' disjoint open images). -/
theorem t2Space_coprod [∀ i, T2Space (X i)] : T2Space (coprod X) := by
  refine ⟨fun x y hxy => ?_⟩
  obtain ⟨i, a, rfl⟩ := exists_coprodι_toFun_eq X x
  obtain ⟨j, b, rfl⟩ := exists_coprodι_toFun_eq X y
  by_cases hij : i = j
  · subst hij
    have hab : a ≠ b := fun h => hxy (congrArg _ h)
    obtain ⟨u, v, hu, hv, hau, hbv, huv⟩ := t2_separation hab
    have he := Hom.isOpenEmbedding_toFun (coprodι X i)
    exact ⟨_, _, he.isOpenMap u hu, he.isOpenMap v hv, ⟨a, hau, rfl⟩, ⟨b, hbv, rfl⟩,
      (Set.disjoint_image_iff he.injective).mpr huv⟩
  · exact ⟨_, _, (Hom.isOpenEmbedding_toFun (coprodι X i)).isOpenMap.isOpen_range,
      (Hom.isOpenEmbedding_toFun (coprodι X j)).isOpenMap.isOpen_range, ⟨a, rfl⟩, ⟨b, rfl⟩,
      Set.disjoint_iff_forall_ne.mpr fun _ ⟨a', ha'⟩ _ ⟨b', hb'⟩ =>
        ha' ▸ hb' ▸ coprodι_toFun_ne X hij a' b'⟩

/-- The countable coproduct of σ-compact spaces is σ-compact (a countable union of the σ-compact
images of the summands): Hironaka's countability at infinity. -/
theorem sigmaCompactSpace_coprod [∀ i, SigmaCompactSpace (X i)] : SigmaCompactSpace (coprod X) := by
  rw [← isSigmaCompact_univ_iff]
  have : (Set.univ : Set (coprod X)) = ⋃ i, Set.range (Hom.toFun (coprodι X i)) := by
    ext x
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_range, true_iff]
    exact exists_coprodι_toFun_eq X x
  rw [this]
  exact isSigmaCompact_iUnion _ fun i =>
    Set.image_univ ▸ isSigmaCompact_univ.image (Hom.continuous_toFun (coprodι X i))

end Coprod

end KLocallyRingedSpace

/-! ### Coproducts in `An/K` -/


open KLocallyRingedSpace

variable {K : Type} [RCLike K] {ι : Type v} [Countable ι] (X : ι → AnalyticSpace.{u} K)

/-- **The coproduct of a countable family of analytic `K`-spaces** [Hir64, Ch. 0, §1]: the
coproduct in `ℜ/K` of the underlying `K`-local-ringed spaces, with Hironaka's clauses — (i) the
local-model clause componentwise, (ii) σ-compact for countable `ι`, (iii) Hausdorff. -/
def sigma : AnalyticSpace.{u} K where
  toKLocallyRingedSpace := KLocallyRingedSpace.coprod fun i => (X i).toKLocallyRingedSpace
  locallyModel := by
    intro x
    obtain ⟨i, a, rfl⟩ := exists_coprodι_toFun_eq (fun i => (X i).toKLocallyRingedSpace) x
    obtain ⟨U, haU, n, k, G, f, W, ⟨e⟩⟩ := (X i).locallyModel a
    let b := ofRestrict (X i).toKLocallyRingedSpace U ≫
      coprodι (fun i => (X i).toKLocallyRingedSpace) i
    have hb : LocallyRingedSpace.IsOpenImmersion b.1 :=
      inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
        ((ofRestrict (X i).toKLocallyRingedSpace U).1 ≫
          (coprodι (fun i => (X i).toKLocallyRingedSpace) i).1))
    let U' : Opens (KLocallyRingedSpace.coprod fun i => (X i).toKLocallyRingedSpace) :=
      ⟨Set.range (KLocallyRingedSpace.Hom.toFun b), isOpen_range_toFun b⟩
    exact ⟨U', ⟨⟨a, haU⟩, rfl⟩, n, k, G, f, W,
      ⟨isoOfRangeEq (ofRestrict _ U') b (by rw [range_toFun_ofRestrict]; rfl) ≪≫ e⟩⟩
  t2 := t2Space_coprod fun i => (X i).toKLocallyRingedSpace
  sigmaCompact := sigmaCompactSpace_coprod fun i => (X i).toKLocallyRingedSpace

theorem sigma_toKLocallyRingedSpace :
    (sigma X).toKLocallyRingedSpace =
      KLocallyRingedSpace.coprod fun i => (X i).toKLocallyRingedSpace :=
  rfl

/-- **The injection of the `i`-th summand** into the coproduct in `An/K`. -/
def sigmaι (i : ι) : X i ⟶ sigma X :=
  coprodι (fun i => (X i).toKLocallyRingedSpace) i

variable {X} in
/-- **The descent** of a family of morphisms out of the summands, in `An/K`. -/
def sigmaDesc {Y : AnalyticSpace.{u} K} (f : ∀ i, X i ⟶ Y) : sigma X ⟶ Y :=
  coprodDesc (X := fun i => (X i).toKLocallyRingedSpace) (Y := Y.toKLocallyRingedSpace) f

theorem sigmaι_def (i : ι) :
    sigmaι X i = coprodι (fun i => (X i).toKLocallyRingedSpace) i :=
  rfl

variable {X} in
theorem sigmaDesc_def {Y : AnalyticSpace.{u} K} (f : ∀ i, X i ⟶ Y) :
    sigmaDesc f = coprodDesc (X := fun i => (X i).toKLocallyRingedSpace) f :=
  rfl


end AnalyticSpace
