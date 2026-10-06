/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Model
public import Hironaka.AnalyticSpace.KSpace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Basic lemmas on `K`-morphisms and analytic `K`-spaces

Consequences of the definitions of `K`-local-ringed spaces, their morphisms and analytic `K`-spaces:
the `K`-linearity of the restriction and stalk maps of a `K`-morphism (the constants are carried to
the constants because a `K`-morphism commutes with the structural homomorphisms on global sections,
and the constants over `U`, or at `x`, are the restrictions, or the germs, of the global constants);
a `K`-morphism whose underlying morphism of locally ringed spaces is an isomorphism is a
`K`-isomorphism, so that `IsIso` in `An/K` can be tested on the underlying morphism; and the
existence of a local `Kⁿ`-coordination at every point [Hir64, Ch. 0, §1, p. 120].
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace AnalyticSpace

variable {K : Type} [RCLike K]

namespace KLocallyRingedSpace

/-- The global-section map of a `K`-morphism is the `⊤`-component of its sheaf map. -/
theorem Hom.pullbackΓ_eq {X Y : KLocallyRingedSpace.{u} K} (f : X ⟶ Y) :
    f.pullbackΓ = (f.1.c.app (op ⊤)).hom :=
  rfl

/-- A `K`-morphism carries the constants over `U` to the constants over `f⁻¹U`. -/
theorem Hom.algebraMap_res {X Y : KLocallyRingedSpace.{u} K} (f : X ⟶ Y) (U : Opens Y) (c : K) :
    (f.1.c.app (op U)).hom (Y.toLocallyRingedSpace.presheaf.map (homOfLE le_top).op
      (Y.algebraMap c)) =
      X.toLocallyRingedSpace.presheaf.map (homOfLE le_top).op (X.algebraMap c) := by
  have h := f.1.c.naturality (homOfLE (le_top : U ≤ ⊤)).op
  have h' := congrArg (fun φ => (CommRingCat.Hom.hom φ) (Y.algebraMap c)) h
  refine h'.trans ?_
  exact congrArg (X.toLocallyRingedSpace.presheaf.map _) (f.pullbackΓ_algebraMap c)

/-- The stalk map of a `K`-morphism carries the constant germs to the constant germs. -/
theorem Hom.algebraMap_stalk {X Y : KLocallyRingedSpace.{u} K} (f : X ⟶ Y) (x : X) (c : K) :
    (f.1.stalkMap x).hom (Y.toLocallyRingedSpace.presheaf.germ ⊤ (f.1.base x) trivial
      (Y.algebraMap c)) =
      X.toLocallyRingedSpace.presheaf.germ ⊤ x trivial (X.algebraMap c) := by
  change (f.1.toShHom.hom.stalkMap x) (Y.toLocallyRingedSpace.presheaf.germ ⊤ _
    (Opens.mem_top _) (Y.algebraMap c)) =
    X.toLocallyRingedSpace.presheaf.germ ⊤ x (Opens.mem_top _) (X.algebraMap c)
  erw [PresheafedSpace.stalkMap_germ_apply]
  exact congrArg (fun s => X.toLocallyRingedSpace.presheaf.germ
    ((Opens.map f.1.base).obj ⊤) x (Opens.mem_top _) s) (f.pullbackΓ_algebraMap c)

/-- A `K`-morphism whose underlying morphism of locally ringed spaces is an isomorphism is an
isomorphism of `K`-local-ringed spaces (the inverse commutes with the `K`-structures
automatically). -/
theorem isIso_of_isIso_val {X Y : KLocallyRingedSpace.{u} K} (f : X ⟶ Y) [IsIso f.1] :
    IsIso f := by
  refine ⟨⟨Hom.ofFac (𝟙 Y) f (inv f.1) (IsIso.inv_hom_id f.1), Hom.ext ?_, Hom.ext ?_⟩⟩
  · rw [Hom.comp_val, Hom.ofFac_val, IsIso.hom_inv_id, Hom.id_val]
  · rw [Hom.comp_val, Hom.ofFac_val, IsIso.inv_hom_id, Hom.id_val]

theorem isIso_iff_isIso_val {X Y : KLocallyRingedSpace.{u} K} (f : X ⟶ Y) :
    IsIso f ↔ IsIso f.1 :=
  ⟨fun _ => KIso.isIso_hom_val (asIso f), fun _ => isIso_of_isIso_val f⟩

end KLocallyRingedSpace


variable {X : AnalyticSpace.{u} K}

/-- `f` is an isomorphism of `An/K` iff its underlying morphism of locally ringed spaces is an
isomorphism. -/
theorem isIso_iff {Y : AnalyticSpace.{u} K} (f : X ⟶ Y) :
    IsIso f ↔ CategoryTheory.IsIso f.1 := by
  have h : IsIso f ↔ @CategoryTheory.IsIso (KLocallyRingedSpace.{u} K) _
      X.toKLocallyRingedSpace Y.toKLocallyRingedSpace f :=
    ⟨fun ⟨⟨g, h1, h2⟩⟩ => ⟨⟨g, h1, h2⟩⟩, fun ⟨⟨g, h1, h2⟩⟩ => ⟨⟨g, h1, h2⟩⟩⟩
  exact h.trans (KLocallyRingedSpace.isIso_iff_isIso_val _)

/-- Every point has a local `Kⁿ`-coordination [Hir64, Ch. 0, §1, p. 120]. -/
theorem exists_localCoordination (X : AnalyticSpace.{u} K) (x : X) :
    Nonempty (X.LocalCoordination x) := by
  obtain ⟨U, hxU, n, k, G, f, W, ⟨e⟩⟩ := X.locallyModel x
  exact ⟨⟨U, hxU, n, e.hom ≫ KLocallyRingedSpace.ofRestrict _ W ≫ localModel.ι K n G f, k, G, f,
    W, e, rfl⟩⟩


end AnalyticSpace
