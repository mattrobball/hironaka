/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Defs
public import Hironaka.AnalyticSpace.KSpace
import Hironaka.AnalyticSpace.LocalModelRestrict
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Open subspaces: helper isomorphisms and local embeddings

Three small consequences of the universal property of open immersions
(`KLocallyRingedSpace.isoOfRangeEq`: two open immersions of `K`-local-ringed spaces with the same
image are `K`-isomorphic), and Hironaka's local embeddings.

* `restrictOpenTopIso : X | ⊤ ≅ X`; `restrictOpenIso`: a `K`-isomorphism `X ≅ Y` restricts to
  `X | e⁻¹V ≅ Y | V`; `restrictOpen_restrictOpen_iso`: `(X | U) | V ≅ X | (image of V)`
  (`imageOpens`). Each is `isoOfRangeEq` of two open immersions into the same space.
* `exists_kIso_localModel`: every point of an analytic `K`-space has an open neighbourhood
  `K`-isomorphic to a local analytic `K`-space, the literal form of Hironaka's clause (i)
  [Hir64, Ch. 0, §1, p. 120], obtained from the form of the definition (an open of a local model)
  through `Hironaka/AnalyticSpace/LocalModelRestrict.lean`;
  `exists_finite_cover_by_localModels_of_isCompact_closure`: a set with compact closure is
  covered by finitely many such neighbourhoods (a finite subcover of the compact closure by the
  neighbourhoods of its points). Hironaka's remark that a relatively compact open embeds properly
  into some `ℝ^N` [Hir64, Ch. 0, §1, footnote 10] is not needed: the resolution of an analytic
  space is assembled locally and glued.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold Topology

universe u

namespace AnalyticSpace

variable {K : Type} [RCLike K]

namespace KLocallyRingedSpace

variable (X : KLocallyRingedSpace.{u} K)

/-- The restriction to the whole space is the space: `X | ⊤ ≅ X`. -/
def restrictOpenTopIso : X.restrictOpen ⊤ ≅ X :=
  haveI : LocallyRingedSpace.IsOpenImmersion (𝟙 X : Hom X X).1 :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (𝟙 X.toLocallyRingedSpace))
  isoOfRangeEq (ofRestrict X ⊤) (𝟙 X) (by
    rw [range_toFun_ofRestrict, Hom.toFun_id, Set.range_id]
    rfl)

variable {X} {Y : KLocallyRingedSpace.{u} K}

/-- A `K`-isomorphism restricts to the open subspaces over an open `V` of the target. -/
def restrictOpenIso (e : X ≅ Y) (V : Opens Y) :
    X.restrictOpen ((Opens.map e.hom.1.base).obj V) ≅ Y.restrictOpen V :=
  haveI : LocallyRingedSpace.IsOpenImmersion
      (ofRestrict X ((Opens.map e.hom.1.base).obj V) ≫ e.hom).1 :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      ((ofRestrict X ((Opens.map e.hom.1.base).obj V)).1 ≫ e.hom.1))
  isoOfRangeEq (ofRestrict X ((Opens.map e.hom.1.base).obj V) ≫ e.hom) (ofRestrict Y V) (by
    rw [Hom.range_toFun_comp, range_toFun_ofRestrict, range_toFun_ofRestrict]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      refine ⟨(KIso.homeomorph e).symm y, ?_, (KIso.homeomorph e).apply_symm_apply y⟩
      change e.hom.1.base ((KIso.homeomorph e).symm y) ∈ V
      rw [show e.hom.1.base ((KIso.homeomorph e).symm y) = y from
        (KIso.homeomorph e).apply_symm_apply y]
      exact hy)

/-- The restriction of a restriction is the restriction to the image open. -/
instance isOpenImmersion_ofRestrict_comp_ofRestrict (U : Opens X) (V : Opens (X.restrictOpen U)) :
    LocallyRingedSpace.IsOpenImmersion (ofRestrict (X.restrictOpen U) V ≫ ofRestrict X U).1 :=
  inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
    ((ofRestrict (X.restrictOpen U) V).1 ≫ (ofRestrict X U).1))

/-- The image in `X` of an open `V` of the open subspace `X | U`. -/
def imageOpens (U : Opens X) (V : Opens (X.restrictOpen U)) : Opens X :=
  ⟨Set.range (Hom.toFun (ofRestrict (X.restrictOpen U) V ≫ ofRestrict X U)), isOpen_range_toFun _⟩

/-- The restriction of a restriction is the restriction to the image open. -/
def restrictOpen_restrictOpen_iso (U : Opens X) (V : Opens (X.restrictOpen U)) :
    (X.restrictOpen U).restrictOpen V ≅ X.restrictOpen (imageOpens U V) :=
  isoOfRangeEq (ofRestrict (X.restrictOpen U) V ≫ ofRestrict X U) (ofRestrict X _)
    (by rw [range_toFun_ofRestrict]; rfl)

end KLocallyRingedSpace

open KLocallyRingedSpace


variable (X : AnalyticSpace.{u} K)

/-- Hironaka's clause (i) in its literal form [Hir64, Ch. 0, §1, p. 120]: every point has an open
neighbourhood `U` with `X|U` `K`-isomorphic to a local analytic `K`-space. -/
theorem exists_kIso_localModel (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U) (n k : ℕ) (G : Opens (Kn.{u} K n)) (f : Fin k → AnalyticFun K n G),
      Nonempty (KIso (X.toKLocallyRingedSpace.restrictOpen U) (localModel K n G f)) := by
  obtain ⟨U, hxU, n, k, G, f, W, ⟨e⟩⟩ := X.locallyModel x
  obtain ⟨G', hG, ⟨e'⟩, -⟩ := localModel_restrictOpen_iso K n G f W
  exact ⟨U, hxU, n, k, G', _, ⟨e ≪≫ e'⟩⟩

/-- A set with compact closure is covered by finitely many open subspaces each `K`-isomorphic to
a local analytic `K`-space. -/
theorem exists_finite_cover_by_localModels_of_isCompact_closure (U : Set X)
    (hU : IsCompact (closure U)) :
    ∃ s : Finset (Opens X), (U ⊆ ⋃ V ∈ s, (V : Set X)) ∧
      ∀ V ∈ s, ∃ (n k : ℕ) (G : Opens (Kn.{u} K n)) (f : Fin k → AnalyticFun K n G),
        Nonempty (KIso (X.toKLocallyRingedSpace.restrictOpen V) (localModel K n G f)) := by
  classical
  choose V hxV hV using fun x : X => exists_kIso_localModel X x
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun x : X => (V x : Set X)) (fun x => (V x).isOpen)
    fun y _ => Set.mem_iUnion.mpr ⟨y, hxV y⟩
  refine ⟨t.image V, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht (subset_closure hy))
    exact Set.mem_iUnion₂.mpr ⟨V x, Finset.mem_image_of_mem V hxt, hyx⟩
  · intro W hW
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hW
    exact hV x


end AnalyticSpace
