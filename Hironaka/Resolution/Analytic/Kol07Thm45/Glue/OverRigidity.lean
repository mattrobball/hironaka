/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.OverFamily
public import Hironaka.AnalyticSpace.Glue.GlueIsoOver
import Hironaka.AnalyticSpace.Lemmas
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalModel
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic
/-!
# Rigidity transfer on a gluing over a base

The resolutions of two pieces are identified over their overlap by the functoriality of the
resolution: it is independent of the embedding up to a canonical isomorphism [Kol07, Theorem 36,
proof], the blow-up sequences of the pieces agree on the overlaps [Kol07, Proposition 37, (37.2)],
and the canonical desingularization commutes with local analytic isomorphisms [Wlo09, Theorem 6.0.6,
(2)]. The gluing needs one more fact, which the sources use without stating it: an isomorphism over
the base between two resolutions of one open subset is unique. It is a hypothesis here. Read on a
gluing datum `G : GlueOver X R π dom` (`Hironaka.AnalyticSpace.Glue.Over`): the chosen transitions
`t i j` are isomorphisms over `X` between the parts of the pieces over the overlaps, and where the
parts over an open subset `P` of the base have no non-trivial automorphism over `X`
(`RigidOver (π i) P`), every isomorphism over `X` between the parts over `P` is the restricted
transition. Consequently the compatibility of closed subspaces of the pieces along a transition,
`comap (t i j) (C j) = C i` on the gluing open subset, follows from local isomorphisms over `X`
carrying `C j` to `C i`:

* `KLocallyRingedSpace.RigidOver πA O`: no non-trivial automorphism over `Z` of the part over `O`;
* the locality tools `stalkIdeal_toFun_eq_of_comap_eq_of_isIso_stalkMap` and
  `idealSheaf_eq_of_forall_exists_comap_eq`: two ideal sheaves agreeing along stalk-isomorphic
  morphisms through every point are equal;
* `GlueOver.tComap` (the transition in the `Opens.comap` spelling of `restrictOver`, an `eqToHom`
  conjugate), `GlueOver.tOver P hP` (the transition restricted to the parts over `P`, `restrictOver`
  of `Hironaka.AnalyticSpace.Glue.GlueIsoOver`), `tOver_over`, `isIso_tOver`,
  `tOver_comp_ofRestrict`;
* `GlueOver.eq_tOver_of_isoOver`: over a rigid `P`, `θ = tOver` (`isoOver_unique_of_aut`,
  `Hironaka.Resolution.Analytic.Kol07Thm45.LocalModel`);
* `GlueOver.compatClosedSubspaces_pair_of_forall_exists_isoOver`: pair compatibility from local
  isomorphisms over `X` (locality and the preceding item).

The rigidity of the local resolutions over `X` is supplied by
`Hironaka.Resolution.Analytic.Kol07Thm45.RigidOverLocalResolution`, from the uniqueness of the
isomorphism over the base between two local resolutions; the pair compatibility feeds the gluing of
the exceptional families of the local resolutions (`CoproductGluedFamilyCompat`,
`ExhaustionChainFamilies`, `RigidOverLocalResolution`).
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set AlgebraicGeometry
open Manifold AnalyticSpace.KLocallyRingedSpace

universe u

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- The identification of the restrictions along an equality of opens lies over the space. -/
theorem eqToHom_restrictOpen_comp_ofRestrict {Y : KLocallyRingedSpace.{u} K}
    {O₁ O₂ : Opens Y} (h : O₁ = O₂) :
    eqToHom (congrArg Y.restrictOpen h) ≫ ofRestrict Y O₂ = ofRestrict Y O₁ := by
  subst h
  simp

/-- **The parts of `A` over `O` are rigid over `Z`**: every automorphism over `Z` of `A|πA⁻¹O` is
the identity; the hypothesis of `isoOver_unique_of_aut`, named. -/
def RigidOver {A Z : KLocallyRingedSpace.{u} K} (πA : A ⟶ Z) (O : Opens Z) : Prop :=
  ∀ t : A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O) ⟶
      A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O),
    IsIso t → ofRestrict _ _ ≫ πA = (t ≫ ofRestrict _ _) ≫ πA → t = 𝟙 _

/-- **Equal pull-backs along a morphism that is an isomorphism on the stalk at `z` give equal stalk
ideals at the image of `z`**: the stalk ideal of a pull-back is the image of the stalk ideal under
the stalk map (`QuotientSpace.stalkIdeal_comap`), and a bijective ring map is injective on ideals
(`Ideal.comap_map_of_bijective`). -/
theorem stalkIdeal_toFun_eq_of_comap_eq_of_isIso_stalkMap {Y Z : KLocallyRingedSpace.{u} K}
    (f : Z ⟶ Y)
    {A B : IdealSheaf Y.toLocallyRingedSpace.𝒪}
    (h : QuotientSpace.comap f.1 A = QuotientSpace.comap f.1 B) (z : Z)
    (hz : IsIso (f.1.stalkMap z)) :
    A.stalkIdeal (Hom.toFun f z) = B.stalkIdeal (Hom.toFun f z) := by
  have hbij : Function.Bijective (f.1.stalkMap z).hom := ConcreteCategory.bijective_of_isIso _
  have hA := QuotientSpace.stalkIdeal_comap f.1 A z
  have hB := QuotientSpace.stalkIdeal_comap f.1 B z
  have hmap : (A.stalkIdeal (Hom.toFun f z)).map (f.1.stalkMap z).hom =
      (B.stalkIdeal (Hom.toFun f z)).map (f.1.stalkMap z).hom :=
    hA.symm.trans ((congrArg (fun D : IdealSheaf _ => D.stalkIdeal z) h).trans hB)
  have h2 := congrArg (Ideal.comap (f.1.stalkMap z).hom) hmap
  exact (Ideal.comap_map_of_bijective _ hbij).symm.trans
    (h2.trans (Ideal.comap_map_of_bijective _ hbij))

/-- **Two ideal sheaves that agree along stalk-isomorphic morphisms through every point are equal**:
`IdealSheaf.ext` stalk by stalk, each stalk reached through the given morphism. -/
theorem idealSheaf_eq_of_forall_exists_comap_eq {Y : KLocallyRingedSpace.{u} K}
    {A B : IdealSheaf Y.toLocallyRingedSpace.𝒪}
    (h : ∀ y : Y, ∃ (Z : KLocallyRingedSpace.{u} K) (f : Z ⟶ Y) (z : Z),
      Hom.toFun f z = y ∧ IsIso (f.1.stalkMap z) ∧
        QuotientSpace.comap f.1 A = QuotientSpace.comap f.1 B) :
    A = B :=
  IdealSheaf.ext fun y => by
    obtain ⟨Z, f, z, rfl, hz, hAB⟩ := h y
    exact stalkIdeal_toFun_eq_of_comap_eq_of_isIso_stalkMap f hAB z hz

end AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace.GlueOver

variable {K : Type} [RCLike K] {X : AnalyticSpace.{u} K} {ι : Type u}
  {R : ι → AnalyticSpace.{u} K} {π : ∀ i, (R i).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace}
  {dom : ι → Opens X}

/-- The gluing open subset in Mathlib's `Opens.comap` spelling (`overOpens_eq_comap` at the
overlap). -/
theorem glueOpens_eq_comap (i j : ι) :
    glueOpens X R π dom i j =
      Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun (π i)⟩
          (dom i ⊓ dom j) :=
  overOpens_eq_comap π i (dom i ⊓ dom j)

/-- The opposite gluing open subset in the `Opens.comap` spelling of the same overlap
`dom i ⊓ dom j` (`inf_comm`). -/
theorem glueOpens_symm_eq_comap (i j : ι) :
    glueOpens X R π dom j i =
      Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π j), Hom.continuous_toFun (π j)⟩
          (dom i ⊓ dom j) :=
  (glueOpens_eq_comap j i).trans (by rw [inf_comm])

/-- The parts over `P ≤ dom i ⊓ dom j` lie in the gluing open subset. -/
theorem comap_le_glueOpens (i j : ι) {P : Opens X} (hP : P ≤ dom i ⊓ dom j) :
    Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun
        (π i)⟩ P ≤ glueOpens X R π dom i j :=
  fun _ hy => hP (Opens.mem_comap.mp hy)

variable (G : GlueOver X R π dom)

/-- **The transition in the `Opens.comap` spelling** of `restrictOver`: `t i j` conjugated by the
identifications of the gluing open subsets with the `Opens.comap` of the overlap
(`glueOpens_eq_comap`). -/
def tComap (i j : ι) :
    (R i).toKLocallyRingedSpace.restrictOpen
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun (π i)⟩
            (dom i ⊓ dom j)) ⟶
      (R j).toKLocallyRingedSpace.restrictOpen
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π j), Hom.continuous_toFun (π j)⟩
            (dom i ⊓ dom j)) :=
  eqToHom (congrArg _ (glueOpens_eq_comap (π := π) (dom := dom) i j).symm) ≫ G.t i j ≫
    eqToHom (congrArg _ (glueOpens_symm_eq_comap (π := π) (dom := dom) i j))

/-- The `Opens.comap` transition followed by the inclusion is the identification followed by `t i j`
and the inclusion of the gluing open subset. -/
theorem tComap_comp_ofRestrict (i j : ι) :
    G.tComap i j ≫ ofRestrict (R j).toKLocallyRingedSpace _ =
      eqToHom (congrArg _ (glueOpens_eq_comap (π := π) (dom := dom) i j).symm) ≫ G.t i j ≫
        ofRestrict (R j).toKLocallyRingedSpace (glueOpens X R π dom j i) := by
  rw [tComap, Category.assoc, Category.assoc,
    eqToHom_restrictOpen_comp_ofRestrict
        (glueOpens_symm_eq_comap i j)]

/-- The `Opens.comap` transition lies over `X` (`G.compat`, transported along the identifications).
-/
theorem compat_tComap (i j : ι) :
    ofRestrict (R i).toKLocallyRingedSpace _ ≫ π i =
      (G.tComap i j ≫ ofRestrict (R j).toKLocallyRingedSpace _) ≫ π j := by
  rw [tComap_comp_ofRestrict, Category.assoc, ← G.compat i j, ← Category.assoc,
    eqToHom_restrictOpen_comp_ofRestrict
        (glueOpens_eq_comap i j).symm]

/-- The `Opens.comap` transition is an isomorphism (`t i j` is one: the glue data's `t_isIso`,
lifted to `K`-morphisms by `isIso_of_isIso_val`). -/
theorem isIso_tComap (i j : ι) : IsIso (G.tComap i j) := by
  have h1 : IsIso (G.t i j).1 := G.toKGlueData.toLRSGlueData.toGlueData.t_isIso i j
  have h2 : IsIso (G.t i j) := isIso_of_isIso_val (G.t i j)
  unfold tComap
  infer_instance

/-- **The transition restricted to the parts over `P ≤ dom i ⊓ dom j`** (`restrictOver` at `t i j`).
-/
def tOver (i j : ι) {P : Opens X} (hP : P ≤ dom i ⊓ dom j) :
    (R i).toKLocallyRingedSpace.restrictOpen
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun (π i)⟩ P) ⟶
      (R j).toKLocallyRingedSpace.restrictOpen
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π j), Hom.continuous_toFun (π j)⟩ P) :=
  restrictOver (π i) (π j) hP (G.tComap i j) (G.compat_tComap i j)

/-- The restricted transition lies over `X`. -/
theorem tOver_over (i j : ι) {P : Opens X} (hP : P ≤ dom i ⊓ dom j) :
    ofRestrict (R i).toKLocallyRingedSpace _ ≫ π i =
      (G.tOver i j hP ≫ ofRestrict (R j).toKLocallyRingedSpace _) ≫ π j :=
  restrictOver_over (π i) (π j) hP (G.tComap i j) (G.compat_tComap i j)

/-- The restricted transition is an isomorphism. -/
theorem isIso_tOver (i j : ι) {P : Opens X} (hP : P ≤ dom i ⊓ dom j) : IsIso (G.tOver i j hP) :=
  have := G.isIso_tComap i j
  isIso_restrictOver (π i) (π j) hP (G.tComap i j) (G.compat_tComap i j)

/-- **The restricted transition followed by the inclusion is the inclusion of the parts over `P`
into the gluing open subset, followed by `t i j` and the inclusion of the gluing open subset**
(`restrictOver_comp_ofRestrict` with the identifications absorbed). -/
theorem tOver_comp_ofRestrict (i j : ι) {P : Opens X} (hP : P ≤ dom i ⊓ dom j) :
    G.tOver i j hP ≫ ofRestrict (R j).toKLocallyRingedSpace _ =
      KLocallyRingedSpace.restrictIncl (R i).toKLocallyRingedSpace
          (comap_le_glueOpens (π := π) i j hP) ≫
        G.t i j ≫ ofRestrict (R j).toKLocallyRingedSpace (glueOpens X R π dom j i) := by
  rw [tOver, restrictOver_comp_ofRestrict, tComap_comp_ofRestrict, ← Category.assoc]
  congr 1

/-- **Rigidity transfer**: over a rigid `P ≤ dom i ⊓ dom j`, every isomorphism `θ` over `X` between
the parts of `R i` and of `R j` over `P` is the restricted transition `tOver`
(`isoOver_unique_of_aut` at `θ` and `tOver`). -/
theorem eq_tOver_of_isoOver (i j : ι) {P : Opens X} (hP : P ≤ dom i ⊓ dom j)
    (haut : RigidOver (π i) P)
    (θ : (R i).toKLocallyRingedSpace.restrictOpen
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun (π i)⟩ P) ⟶
      (R j).toKLocallyRingedSpace.restrictOpen
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π j), Hom.continuous_toFun (π j)⟩ P))
    (hθ : IsIso θ)
    (hθc : ofRestrict (R i).toKLocallyRingedSpace _ ≫ π i =
      (θ ≫ ofRestrict (R j).toKLocallyRingedSpace _) ≫ π j) :
    θ = G.tOver i j hP :=
  isoOver_unique_of_aut (π i) (π j) P haut θ (G.tOver i j hP) hθ (G.isIso_tOver i j hP) hθc
    (G.tOver_over i j hP)

/-- **Pair compatibility from local isomorphisms over `X`**: if every point of the gluing open
subset has a rigid `P ≤ dom i ⊓ dom j` through its image and an isomorphism `θ` over `X` of the
parts over `P` carrying `C j` to `C i`, then the transition `t i j` carries `C j` to `C i` on the
whole gluing open subset: locality (`idealSheaf_eq_of_forall_exists_comap_eq` along the open
inclusions of the parts over `P`), `θ = tOver` (`eq_tOver_of_isoOver`), `tOver_comp_ofRestrict`. -/
theorem compatClosedSubspaces_pair_of_forall_exists_isoOver (C : ∀ i, ClosedSubspace (R i))
    (i j : ι)
    (h : ∀ y : R i, y ∈ glueOpens X R π dom i j →
      ∃ (P : Opens X) (_ : P ≤ dom i ⊓ dom j), KLocallyRingedSpace.Hom.toFun
          (π i) y ∈ P ∧ RigidOver (π i) P ∧
        ∃ θ : (R i).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun (π i)⟩ P) ⟶
          (R j).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π j), Hom.continuous_toFun (π j)⟩ P),
          IsIso θ ∧
          ofRestrict (R i).toKLocallyRingedSpace _ ≫ π i =
            (θ ≫ ofRestrict (R j).toKLocallyRingedSpace _) ≫ π j ∧
          QuotientSpace.comap (θ ≫ ofRestrict (R j).toKLocallyRingedSpace _).1 (C j) =
            QuotientSpace.comap (ofRestrict (R i).toKLocallyRingedSpace _).1 (C i)) :
    QuotientSpace.comap (G.t i j).1 (restrictGlue π dom j i (C j)) =
      restrictGlue π dom i j (C i) := by
  refine idealSheaf_eq_of_forall_exists_comap_eq fun y => ?_
  obtain ⟨P, hP, hyP, haut, θ, hθ, hθc, hC⟩ := h y.1 y.2
  set f : (R i).toKLocallyRingedSpace.restrictOpen
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun (π i)⟩ P) ⟶
      (R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j) :=
    KLocallyRingedSpace.restrictIncl (R i).toKLocallyRingedSpace
      (comap_le_glueOpens (π := π) i j hP) with hf
  refine ⟨_, f, ⟨y.1, Opens.mem_comap.mpr hyP⟩,
    Subtype.ext (congrFun (congrArg KLocallyRingedSpace.Hom.toFun
      (KLocallyRingedSpace.restrictIncl_comp_ofRestrict (R i).toKLocallyRingedSpace
        (comap_le_glueOpens (π := π) i j hP)))
      (⟨y.1, Opens.mem_comap.mpr hyP⟩ :
        Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun (π i)⟩ P)),
    ?_, ?_⟩
  · rw [hf, KLocallyRingedSpace.restrictIncl_val]
    exact restrictInclHom_stalkMap_isIso (R i).toLocallyRingedSpace
      (comap_le_glueOpens (π := π) i j hP) _
  · -- both pull-backs are the pull-back of `C` along the parts over `P`
    have e1 : (f ≫ G.t i j ≫ ofRestrict (R j).toKLocallyRingedSpace _) =
        θ ≫ ofRestrict (R j).toKLocallyRingedSpace _ := by
      rw [hf, ← G.tOver_comp_ofRestrict i j hP, G.eq_tOver_of_isoOver i j hP haut θ hθ hθc]
    have e2 : f ≫ ofRestrict (R i).toKLocallyRingedSpace _ =
        ofRestrict (R i).toKLocallyRingedSpace _ :=
      KLocallyRingedSpace.restrictIncl_comp_ofRestrict _ _
    calc QuotientSpace.comap f.1 (QuotientSpace.comap (G.t i j).1 (restrictGlue π dom j i (C j)))
        = QuotientSpace.comap (f ≫ G.t i j ≫ ofRestrict (R j).toKLocallyRingedSpace _).1 (C j) := by
          rw [restrictGlue, ← QuotientSpace.comap_comp, ← QuotientSpace.comap_comp]
          rfl
      _ = QuotientSpace.comap (θ ≫ ofRestrict (R j).toKLocallyRingedSpace _).1 (C j) := by rw [e1]
      _ = QuotientSpace.comap (ofRestrict (R i).toKLocallyRingedSpace _).1 (C i) := hC
      _ = QuotientSpace.comap (f ≫ ofRestrict (R i).toKLocallyRingedSpace _).1 (C i) := by rw [e2]
      _ = QuotientSpace.comap f.1 (restrictGlue π dom i j (C i)) := by
          rw [restrictGlue, ← QuotientSpace.comap_comp]
          rfl

end AnalyticSpace.GlueOver

end
