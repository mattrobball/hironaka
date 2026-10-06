/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Defs
import Hironaka.AnalyticSpace.Quotient
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The local models of analytic `K`-spaces: embeddings and coordinations

The local analytic `K`-spaces `localModel K n G f = (S(𝓘), (𝒜_G/𝓘)|_{S(𝓘)})`, `𝓘 = (f₁, …, f_k)`,
of [Hir64, Ch. 0, §1] sit in `(Kⁿ, 𝒜_{Kⁿ})`, and an analytic `K`-space has a local
`Kⁿ`-coordination at every point (`exists_localCoordination`).

* `AnalyticFun.eval g p`, the value at a point of `G` of a regular analytic `K`-function on `G`.
* `localModel.ι : localModel K n G f ⟶ affine K n`, the embedding into `(Kⁿ, 𝒜_{Kⁿ})`, onto the
  locally closed set `S(𝓘)` (closed in the open `G`): the quotient's canonical morphism followed by
  the open immersion `(G, 𝒜_G) ⟶ (Kⁿ, 𝒜_{Kⁿ})`.
* `coordSection K n i`, the `i`-th coordinate function `z_i` on `Kⁿ` as a global analytic function.
* `LocalCoordination X x`: a **local `Kⁿ`-coordination** `(U, h)` at `x` [Hir64, Ch. 0, §1, p. 120]
  is an open neighbourhood `U` of `x` with a `K`-morphism `h : X|U → (Kⁿ, 𝒜_{Kⁿ})` inducing a
  `K`-isomorphism of `X|U` onto a local analytic `K`-space in `(Kⁿ, 𝒜_{Kⁿ})`; here `h` is factored
  as a `K`-isomorphism onto an open subspace `W` of a local model `L`, the open immersion
  `L|W ⟶ L`, and the embedding `localModel.ι` of `L` onto the locally closed set `S(𝓘) ⊆ G ⊆ Kⁿ`.

The embedding `localModel.ι` is injective on points (`injective_base_localModel_ι`,
`injective_toFun_localModel_ι`) with surjective stalk maps (`surjective_stalkMap_localModel_ι`:
those of the quotient's canonical morphism are, and the open immersion is an isomorphism on
stalks), hence a monomorphism of `K`-spaces (`eq_of_comp_localModel_ι_eq`, by Mathlib's
`SheafedSpace.mono_of_base_injective_of_stalk_epi`). The support of `localModel K n G f` is the
common zero set of the `f_i` (`mem_cosupport_modelIdeal_iff`), and an open subspace of a local
model is again a local model (`localModel_restrictOpen_iso`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open scoped Manifold ContDiff

universe u

namespace AnalyticSpace

section Model

variable (K : Type) [RCLike K] (n : ℕ)

variable {K n} in
/-- The value at a point of `G` of a regular analytic `K`-function on `G`. -/
def AnalyticFun.eval {G : Opens (Kn.{u} K n)} (g : AnalyticFun K n G) (p : G) : K := g.1 p

/-- The embedding of the local model into `(Kⁿ, 𝒜_{Kⁿ})`, onto the set `S(𝓘)`, closed in the open
`G` and so locally closed in `Kⁿ`: the quotient's canonical morphism followed by the open
immersion `(G, 𝒜_G) ⟶ (Kⁿ, 𝒜_{Kⁿ})` (Hironaka's "local analytic `K`-space in
`(Kⁿ, 𝒜_{Kⁿ})`"). -/
def localModel.ι (G : Opens (Kn.{u} K n)) {k : ℕ} (f : Fin k → AnalyticFun K n G) :
    localModel K n G f ⟶ affine K n :=
  KLocallyRingedSpace.quotientι _ _ ≫ KLocallyRingedSpace.ofRestrict (affine K n) G

/-- The `i`-th coordinate function `z_i` on `Kⁿ` as a global analytic function. -/
def coordSection (i : Fin n) : (affine K n).toLocallyRingedSpace.presheaf.obj (op ⊤) :=
  (⟨fun p => p.1.down i, by
    have h : ContMDiff 𝓘(K, Kn.{u} K n) 𝓘(K) ω (fun p : Kn.{u} K n => p.down i) :=
      ((ContinuousLinearMap.proj (R := K) (φ := fun _ : Fin n => K) i).comp
        (ContinuousLinearEquiv.ulift :
          Kn.{u} K n ≃L[K] (Fin n → K)).toContinuousLinearMap).contMDiff
    exact h.comp contMDiff_subtype_val⟩ :
    C^ω⟮𝓘(K, Kn.{u} K n), ((⊤ : Opens (Kn.{u} K n)) : Opens (Kn.{u} K n)); 𝓘(K), K⟯)

end Model

section Embedding

variable {K : Type} [RCLike K]

/-- The stalk map of a composite is surjective when both stalk maps are. -/
theorem surjective_stalkMap_comp {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (hf : Function.Surjective (f.stalkMap x).hom)
    (hg : Function.Surjective (g.stalkMap (f.base x)).hom) :
    Function.Surjective ((f ≫ g).stalkMap x).hom := by
  rw [LocallyRingedSpace.stalkMap_comp]
  exact hf.comp hg

/-- The closed embedding of a local model into `(Kⁿ, 𝒜_{Kⁿ})` is injective on points. -/
theorem injective_base_localModel_ι (n : ℕ) (G : Opens (Kn.{u} K n)) {k : ℕ}
    (f : Fin k → AnalyticFun K n G) : Function.Injective (localModel.ι K n G f).1.base := by
  intro a b hab
  exact Subtype.val_injective ((PresheafedSpace.IsOpenImmersion.base_open
    (f := (KLocallyRingedSpace.ofRestrict (affine K n) G).1.toShHom.hom)).injective hab)

/-- The stalk maps of the closed embedding of a local model into `(Kⁿ, 𝒜_{Kⁿ})` are surjective. -/
theorem surjective_stalkMap_localModel_ι (n : ℕ) (G : Opens (Kn.{u} K n)) {k : ℕ}
    (f : Fin k → AnalyticFun K n G) (z : localModel K n G f) :
    Function.Surjective ((localModel.ι K n G f).1.stalkMap z).hom := by
  change Function.Surjective ((((KLocallyRingedSpace.quotientι _ _).1 ≫
    (KLocallyRingedSpace.ofRestrict (affine K n) G).1).stalkMap z).hom)
  exact surjective_stalkMap_comp _ _ _ (QuotientSpace.stalkMap_surjective _ _ _)
    (ConcreteCategory.bijective_of_isIso _).2

namespace KLocallyRingedSpace

/-- The closed embedding `ι : L ⟶ (Kⁿ, 𝒜_{Kⁿ})` of a local model is injective on points. -/
theorem injective_toFun_localModel_ι {n : ℕ} (G : Opens (Kn.{u} K n)) {k : ℕ}
    (f : Fin k → AnalyticFun K n G) : Function.Injective (Hom.toFun (localModel.ι K n G f)) :=
  fun _ _ hzw => Subtype.ext (Subtype.ext hzw)

/-- The closed embedding of a local model is a monomorphism of `K`-spaces: `a ≫ ι = b ≫ ι` forces
`a = b` (injective on points, surjective on stalks). -/
theorem eq_of_comp_localModel_ι_eq {A : KLocallyRingedSpace.{u} K} {n : ℕ} (G : Opens (Kn.{u} K n))
    {k : ℕ} (f : Fin k → AnalyticFun K n G) (a b : A ⟶ localModel K n G f)
    (h : a ≫ localModel.ι K n G f = b ≫ localModel.ι K n G f) : a = b := by
  have hmono : Mono (localModel.ι K n G f).1.toShHom :=
    SheafedSpace.mono_of_base_injective_of_stalk_epi _ (injective_toFun_localModel_ι G f)
      fun z => ConcreteCategory.epi_of_surjective _ (surjective_stalkMap_localModel_ι n G f z)
  have h1 : a.1.toShHom ≫ (localModel.ι K n G f).1.toShHom =
      b.1.toShHom ≫ (localModel.ι K n G f).1.toShHom := by
    rw [← LocallyRingedSpace.comp_toShHom, ← LocallyRingedSpace.comp_toShHom]
    exact congrArg (fun φ : A ⟶ affine K n => φ.1.toShHom) h
  have h2 : a.1.toShHom = b.1.toShHom := (cancel_mono _).mp h1
  exact Hom.ext (LocallyRingedSpace.Hom.ext' (congrArg (fun φ => φ.hom) h2))

end KLocallyRingedSpace

end Embedding

section Coordination

variable {K : Type} [RCLike K]

open KLocallyRingedSpace

/-- A local `Kⁿ`-coordination `(U, h)` of `X` at `x` [Hir64, Ch. 0, §1, p. 120]: an open
neighbourhood `U` of `x` and a `K`-morphism `h : X|U ⟶ (Kⁿ, 𝒜_{Kⁿ})` which induces a
`K`-isomorphism of `X|U` onto a local analytic `K`-space in `(Kⁿ, 𝒜_{Kⁿ})` — `h` factors as the
`K`-isomorphism `iso` onto an open subspace `W` of the local model `L = V(f) ⊆ G`, followed by
the open immersion `L|W ⟶ L` and the embedding `localModel.ι : L ⟶ (Kⁿ, 𝒜_{Kⁿ})`, whose image
`S(𝓘)` is closed in the open `G` (`h_eq`). -/
structure LocalCoordination (X : AnalyticSpace.{u} K) (x : X) where
  /-- The open neighbourhood. -/
  U : Opens X
  mem : x ∈ U
  /-- The dimension of the ambient `Kⁿ`. -/
  n : ℕ
  /-- The coordination `h : X|U ⟶ (Kⁿ, 𝒜_{Kⁿ})`. -/
  h : X.toKLocallyRingedSpace.restrictOpen U ⟶ affine K n
  k : ℕ
  G : Opens (Kn.{u} K n)
  f : Fin k → AnalyticFun K n G
  W : Opens (localModel K n G f)
  /-- The induced `K`-isomorphism onto the local analytic `K`-space. -/
  iso : KIso (X.toKLocallyRingedSpace.restrictOpen U) ((localModel K n G f).restrictOpen W)
  h_eq : h = iso.hom ≫ ofRestrict _ W ≫ localModel.ι K n G f

end Coordination

end AnalyticSpace
