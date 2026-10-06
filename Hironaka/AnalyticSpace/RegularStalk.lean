/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Defs
import Hironaka.AnalyticSpace.KSpace
import Hironaka.Manifold.Germ.StalkNoetherian
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Regular stalks: a manifold point is simple

Hironaka [Hir64, Ch. 0, §1, p. 121]: `x` is a simple point of `X` iff some open neighbourhood
`X|U` of `x` is `K`-isomorphic to a local analytic `K`-space of the form `(G, 𝒜_{Kⁿ}|G)`, `G` an
open subset of `Kⁿ` (by the Jacobian criterion and the implicit function theorem). This file
proves the easy half: the stalk
`𝒜_{Kⁿ,q}` is a regular local ring of dimension `n` (through Rückert's basis theorem,
`isRegularLocalRing_stalk` and `ringKrullDim_stalk` of
`Hironaka/Manifold/Germ/StalkNoetherian.lean`, with `finrank_ulift`), and regularity and the
dimension transport along the stalk isomorphisms of open immersions (`restrictStalkIso`) and of
`K`-isomorphisms (`IsRegularLocalRing.of_ringEquiv`, `ringKrullDim_eq_of_ringEquiv`); so a point
of an analytic `K`-space with a neighbourhood `X|V ≅ (G', 𝒜_{G'})`, `G' ⊆ K^d` open, has a regular
stalk of dimension `d`.

* `isRegularLocalRing_stalk_affine`, `ringKrullDim_stalk_affine`: on `Kⁿ`;
* `isRegularLocalRing_stalk_analyticSpaceOfOpen`, `ringKrullDim_stalk_analyticSpaceOfOpen`: on
  `(G, 𝒜_G)`;
* `KLocallyRingedSpace.isRegularLocalRing_stalk_of_restrictOpen`,
  `ringKrullDim_stalk_restrictOpen`, `isRegularLocalRing_stalk_of_kIso`,
  `ringKrullDim_stalk_of_kIso`: the transports;
* `AnalyticSpace.isRegularLocalRing_stalk_of_kIso_analyticSpaceOfOpen`: the conclusion.

The converse rests on the Jacobian criterion and is proved elsewhere in this directory.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open scoped Manifold ContDiff

universe u

namespace AnalyticSpace

variable (K : Type) [RCLike K] (n : ℕ)

/-- The stalk `𝒜_{Kⁿ,q}` is a regular local ring. -/
theorem isRegularLocalRing_stalk_affine (q : Kn.{u} K n) :
    IsRegularLocalRing ((affine K n).toLocallyRingedSpace.presheaf.stalk q) :=
  inferInstanceAs
    (IsRegularLocalRing ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q))

/-- `𝒜_{Kⁿ,q}` has Krull dimension `n`. -/
theorem ringKrullDim_stalk_affine (q : Kn.{u} K n) :
    ringKrullDim ((affine K n).toLocallyRingedSpace.presheaf.stalk q) =
      ((n : ℕ) : WithBot ℕ∞) := by
  change ringKrullDim ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q) = _
  rw [ringKrullDim_stalk, finrank_ulift, Module.finrank_fin_fun]

/-- The stalks of `(G, 𝒜_G)` are regular local rings (`restrictStalkIso`). -/
theorem isRegularLocalRing_stalk_analyticSpaceOfOpen (G : Opens (Kn.{u} K n))
    (x : analyticSpaceOfOpen K n G) :
    IsRegularLocalRing ((analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.stalk x) :=
  @IsRegularLocalRing.of_ringEquiv _ _ (isRegularLocalRing_stalk_affine K n _) _ _
    ((affine K n).toLocallyRingedSpace.restrictStalkIso
      (Opens.isOpenEmbedding (X := (affine K n).toLocallyRingedSpace.toTopCat) G)
        x).symm.commRingCatIsoToRingEquiv

/-- The stalks of `(G, 𝒜_G)`, `G ⊆ Kⁿ` open, have Krull dimension `n`. -/
theorem ringKrullDim_stalk_analyticSpaceOfOpen (G : Opens (Kn.{u} K n))
    (x : analyticSpaceOfOpen K n G) :
    ringKrullDim ((analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.stalk x) =
      ((n : ℕ) : WithBot ℕ∞) := by
  exact (ringKrullDim_eq_of_ringEquiv ((affine K n).toLocallyRingedSpace.restrictStalkIso
    (Opens.isOpenEmbedding (X := (affine K n).toLocallyRingedSpace.toTopCat) G)
      x).commRingCatIsoToRingEquiv).trans (ringKrullDim_stalk_affine K n _)

variable {K n}

namespace KLocallyRingedSpace

/-- Regularity of a stalk passes from the open subspace `X|U` to `X`. -/
theorem isRegularLocalRing_stalk_of_restrictOpen (X : KLocallyRingedSpace.{u} K) (U : Opens X)
    (x : X.restrictOpen U)
    (h : IsRegularLocalRing ((X.restrictOpen U).toLocallyRingedSpace.presheaf.stalk x)) :
    IsRegularLocalRing (X.toLocallyRingedSpace.presheaf.stalk x.1) :=
  @IsRegularLocalRing.of_ringEquiv _ _ h _ _
    (X.toLocallyRingedSpace.restrictStalkIso (Opens.isOpenEmbedding U) x).commRingCatIsoToRingEquiv

/-- The Krull dimension of a stalk of the open subspace `X|U` is that of the stalk of `X`. -/
theorem ringKrullDim_stalk_restrictOpen (X : KLocallyRingedSpace.{u} K) (U : Opens X)
    (x : X.restrictOpen U) :
    ringKrullDim ((X.restrictOpen U).toLocallyRingedSpace.presheaf.stalk x) =
      ringKrullDim (X.toLocallyRingedSpace.presheaf.stalk x.1) :=
  ringKrullDim_eq_of_ringEquiv
    (X.toLocallyRingedSpace.restrictStalkIso (Opens.isOpenEmbedding U) x).commRingCatIsoToRingEquiv

/-- Regularity of stalks transports along a `K`-isomorphism (its stalk maps are isomorphisms). -/
theorem isRegularLocalRing_stalk_of_kIso {A B : KLocallyRingedSpace.{u} K} (e : KIso A B) (a : A)
    (h : IsRegularLocalRing (B.toLocallyRingedSpace.presheaf.stalk (e.hom.1.base a))) :
    IsRegularLocalRing (A.toLocallyRingedSpace.presheaf.stalk a) :=
  @IsRegularLocalRing.of_ringEquiv _ _ h _ _ (asIso (e.hom.1.stalkMap a)).commRingCatIsoToRingEquiv

/-- The Krull dimension of stalks transports along a `K`-isomorphism. -/
theorem ringKrullDim_stalk_of_kIso {A B : KLocallyRingedSpace.{u} K} (e : KIso A B) (a : A) :
    ringKrullDim (A.toLocallyRingedSpace.presheaf.stalk a) =
      ringKrullDim (B.toLocallyRingedSpace.presheaf.stalk (e.hom.1.base a)) :=
  (ringKrullDim_eq_of_ringEquiv (asIso (e.hom.1.stalkMap a)).commRingCatIsoToRingEquiv).symm

end KLocallyRingedSpace


/-- A point `x` with a neighbourhood `X|V` `K`-isomorphic to `(G', 𝒜_{G'})`, `G' ⊆ K^d` open, is
simple, with `dim 𝒪_{X,x} = d` [Hir64, Ch. 0, §1, p. 121]. -/
theorem isRegularLocalRing_stalk_of_kIso_analyticSpaceOfOpen {X : AnalyticSpace.{u} K}
    {V : Opens X} {x : X} (hx : x ∈ V) {d : ℕ} {G' : Opens (Kn.{u} K d)}
    (e : KLocallyRingedSpace.KIso (X.toKLocallyRingedSpace.restrictOpen V)
      (analyticSpaceOfOpen K d G')) :
    IsRegularLocalRing (X.toLocallyRingedSpace.presheaf.stalk x) ∧
      ringKrullDim (X.toLocallyRingedSpace.presheaf.stalk x) = ((d : ℕ) : WithBot ℕ∞) := by
  have h1 := isRegularLocalRing_stalk_analyticSpaceOfOpen K d G' (e.hom.1.base ⟨x, hx⟩)
  have h2 := ringKrullDim_stalk_analyticSpaceOfOpen K d G' (e.hom.1.base ⟨x, hx⟩)
  refine ⟨KLocallyRingedSpace.isRegularLocalRing_stalk_of_restrictOpen X.toKLocallyRingedSpace V
    ⟨x, hx⟩ (KLocallyRingedSpace.isRegularLocalRing_stalk_of_kIso e ⟨x, hx⟩ h1), ?_⟩
  exact (KLocallyRingedSpace.ringKrullDim_stalk_restrictOpen X.toKLocallyRingedSpace V
    ⟨x, hx⟩).symm.trans ((KLocallyRingedSpace.ringKrullDim_stalk_of_kIso e ⟨x, hx⟩).trans h2)


end AnalyticSpace
