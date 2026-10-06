/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Manifold.Defs
public import Hironaka.Manifold.Snc.Defs
public import Hironaka.Manifold.IdealSheaf.Monoid
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
/-!
# Simple normal crossings families of closed subspaces and their divisors

The boundary predicate of the resolution theorem, `ClosedSubspace.IsSncBoundary`, is Kollár's
Definition 24 read on the stalks of a locally finite family of closed subspaces
[Kol07, Definition 24]: the inverse image of the singular locus is the support of a simple normal
crossings divisor `E` of the resolving space ([Kol07, Theorem 45 (3)]; [Wlo09, Theorem 2.0.1 (2)]).
This module names the family behind that definition and builds its divisor, so that a boundary is
produced from a family by one application:

* `ClosedSubspace.IsSncFamily H`: a family `H : ι → ClosedSubspace X` is locally finite and, at
  every point `x`, a regular system of parameters of `𝒪_{X,x}` cuts out each member through `x`
  by one parameter, distinct members by distinct parameters — the inner clauses of
  `IsSncBoundaryWith` without the product clause on `E` and the clause on `D`;
* `ClosedSubspace.divisorOf H hH`: the reduced divisor of a locally finite family — the ideal
  sheaf with stalk at `x` the product of the members' stalk ideals over the finitely many members
  through `x` (`IdealSheaf.ofStalks`), Kollár's `E = Σ Eᵢ`;
* the snc condition presupposes a regular system of parameters at every point, so an snc family
  lives on a non-singular space (`IsSncBoundary.space_isNonsingular`,
  `Hironaka/AnalyticSpace/SncBoundaryChart.lean`).

The support of the divisor, its boundary predicate, the bridge to the hypersurface families of a
manifold, transport along morphisms and locality are in
`Hironaka/AnalyticSpace/SncFamilyDivisor.lean`, `SncFamilyManifold.lean`, `SncFamilyTransport.lean`
and `SncBoundaryChart.lean`. Used by `Hironaka/AnalyticSpace/Glue/OverFamily.lean` and the modules
just named.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold

universe u

namespace Manifold.IdealSheaf

variable {X : TopCat.{u}} {𝒪 : TopCat.Sheaf CommRingCat.{u} X}

/-- The stalk ideal at `x` as a monoid homomorphism `IdealSheaf 𝒪 →* Ideal 𝒪ₓ`: `1 = ⊤` and
products go to products (`stalkIdeal_one`, `stalkIdeal_mul`, `Hironaka/Manifold/IdealSheaf/`). -/
def stalkIdealMonoidHom (x : X) : IdealSheaf 𝒪 →* Ideal (𝒪.presheaf.stalk x) where
  toFun J := J.stalkIdeal x
  map_one' := by rw [stalkIdeal_one, Ideal.one_eq_top]
  map_mul' I J := stalkIdeal_mul I J x

end Manifold.IdealSheaf

namespace AnalyticSpace

variable {K : Type} [RCLike K] {X : AnalyticSpace.{u} K}

namespace ClosedSubspace

/-- **A simple normal crossings family of closed subspaces** ([Kol07, Definition 24 (1)–(3)];
Hironaka's normal crossings on global components, [Hir64, Ch. 0, §5, Definition 2]): the family is
locally finite, and at every point `x` a regular system of parameters `z₁, …, zₙ` of `𝒪_{X,x}`
(`n` generators of the maximal ideal, `n` the Krull dimension) cuts out each member through `x` by
one parameter, distinct members by distinct parameters. The body of `IsSncBoundaryWith` without
its product clause on the divisor `E` and its clause on `D`: the family behind the boundary
predicate, exposed as data. -/
def IsSncFamily {ι : Type u} (H : ι → ClosedSubspace X) : Prop :=
  LocallyFinite (fun j => (H j).support) ∧
    ∀ x : X, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x),
      (Ideal.span (Set.range z) = IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
        (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x)) ∧
      ∃ c : {j // x ∈ (H j).support} → Fin n, Function.Injective c ∧
        ∀ j, (H j.1).stalkIdeal x = Ideal.span {z (c j)}

/-- The stalk ideals of the members through a point have local generators: the finite product of
the members' local generators on a neighbourhood meeting finitely many members. -/
theorem hasLocalGenerators_prod_of_locallyFinite {ι : Type u} (H : ι → ClosedSubspace X)
    (hH : LocallyFinite fun j => (H j).support) :
    IdealSheaf.HasLocalGenerators (𝒪 := X.toLocallyRingedSpace.𝒪)
      fun x => ∏ j ∈ (hH.point_finite x).toFinset, (H j).stalkIdeal x := by
  classical
  intro a
  obtain ⟨t, hta, hS⟩ := hH a
  obtain ⟨V, hVt, hVo, haV⟩ := mem_nhds_iff.mp hta
  -- the finite product of the ideal sheaves of the members meeting `t` is an ideal sheaf
  set P : ClosedSubspace X := ∏ j ∈ hS.toFinset, H j with hPdef
  obtain ⟨U, haU, k, f, -, hgen⟩ := IdealSheaf.exists_generators P a
  refine ⟨U ⊓ ⟨V, hVo⟩, Opens.mem_inf.mpr ⟨haU, haV⟩, Fin k, inferInstance,
    fun i => X.toLocallyRingedSpace.𝒪.presheaf.map (homOfLE inf_le_left).op (f i), ?_⟩
  intro b hb
  obtain ⟨hbU, hbV⟩ := Opens.mem_inf.mp hb
  have hgerm : ∀ i, X.toLocallyRingedSpace.𝒪.presheaf.germ (U ⊓ ⟨V, hVo⟩) b hb
      (X.toLocallyRingedSpace.𝒪.presheaf.map (homOfLE inf_le_left).op (f i)) =
      X.toLocallyRingedSpace.𝒪.presheaf.germ U b hbU (f i) := fun i =>
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  simp_rw [hgerm]
  rw [← hgen b hbU, hPdef, IdealSheaf.stalkIdeal_finset_prod]
  -- the members through `b` meet `t`; the members of `t` not through `b` contribute `⊤ = 1`
  refine Finset.prod_subset ?_ ?_
  · intro j hj
    rw [Set.Finite.mem_toFinset] at hj ⊢
    exact ⟨b, hj, hVt hbV⟩
  · intro j _ hj
    rw [Set.Finite.mem_toFinset] at hj
    change (H j).stalkIdeal b = 1
    rw [Ideal.one_eq_top]
    exact not_not.mp hj

/-- **The reduced divisor of a locally finite family of closed subspaces** (Kollár's `E = Σ Eᵢ`,
[Kol07, Definition 24]): the ideal sheaf whose stalk at `x` is the product of the stalk ideals of
the finitely many members through `x` (`IdealSheaf.ofStalks`); the empty family gives the unit
ideal `⊤` (the empty subspace). -/
def divisorOf {ι : Type u} (H : ι → ClosedSubspace X)
    (hH : LocallyFinite fun j => (H j).support) : ClosedSubspace X :=
  IdealSheaf.ofStalks X.toLocallyRingedSpace.𝒪
    (fun x => ∏ j ∈ (hH.point_finite x).toFinset, (H j).stalkIdeal x)
    (hasLocalGenerators_prod_of_locallyFinite H hH)

/-- The stalk of the divisor at `x` is the product over the members through `x`. -/
theorem stalkIdeal_divisorOf {ι : Type u} (H : ι → ClosedSubspace X)
    (hH : LocallyFinite fun j => (H j).support) (x : X) :
    (divisorOf H hH).stalkIdeal x = ∏ j ∈ (hH.point_finite x).toFinset, (H j).stalkIdeal x :=
  IdealSheaf.stalkIdeal_ofStalks _ _ x

/-- The boundary case: the empty family has the unit ideal — the empty subspace — as its
divisor. -/
theorem divisorOf_of_isEmpty {ι : Type u} [IsEmpty ι] (H : ι → ClosedSubspace X)
    (hH : LocallyFinite fun j => (H j).support) : divisorOf H hH = ⊤ := by
  refine IdealSheaf.ext fun x => ?_
  rw [stalkIdeal_divisorOf, IdealSheaf.stalkIdeal_top,
    Finset.prod_eq_one fun j _ => (IsEmpty.false j).elim, Ideal.one_eq_top]

end ClosedSubspace

end AnalyticSpace

namespace AnalyticSpace

variable {K : Type} [RCLike K]

section ManifoldBridgeDef

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] {n : ℕ} {ψ : E ≃L[K] (Fin n → K)}
  {M : AnalyticManifold.{u} K E}

/-- The members of a hypersurface family as closed subspaces of `Sp(M)`, through their ideal
sheaves. -/
def _root_.Manifold.HypersurfaceFamily.toClosedSubspaces (F : HypersurfaceFamily M)
    (h : ∀ j, IsClosedSubmanifold ψ (F.hyp j) 1) : F.ι → ClosedSubspace (toSpace ψ M) :=
  fun j => (h j).idealSheaf

end ManifoldBridgeDef

end AnalyticSpace

