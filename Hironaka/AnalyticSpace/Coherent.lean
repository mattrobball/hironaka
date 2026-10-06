/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.ClosedSubspace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Coherent sheaves of rings, coherent ideal sheaves, Noetherian analytic spaces

The definitions of coherence used for analytic `K`-spaces, following [Fre17, Ch. I, §10]
(finitely generated and coherent systems of submodules of `𝒪^m`, and Oka's coherence theorem for
the kernel system of an `𝒪(U)`-linear map `F : 𝒪(U)^p → 𝒪(U)^q`) and [Fre17, Ch. V, 7.2–7.3]
(coherent sheaves of rings and coherent modules), and the Noetherian spaces of [BM97, 3.9];
Bierstone and Milman recall that `𝒪_X` is a coherent sheaf of rings iff every ideal of finite type
in `𝒪_X` is coherent [BM97, (3.8)].

* `relKer F`: the kernel of the linear map `R^p → R^q` of a matrix `F : Fin q → Fin p → R` over a
  commutative ring (`Matrix.mulVecLin`), with `mem_relKer_iff`; `relationSubmodule 𝒪 F y hy` is
  `relKer` of the germ `F_y = ((F_{ik})_y)` at `y ∈ U` of a matrix `F : Fin q → Fin p → 𝒪(U)` of
  sections, Freitag's `M_a := kernel(F_a)`.
* `HasLocalGeneratorsOn 𝒪 U p M`: [Fre17, Ch. I, 10.1–10.2] for a system `M` of submodules
  `M_y ⊆ 𝒪_y^p` over the points `y` of an open `U`: every `x ∈ U` has an open `V ≤ U` and finitely
  many vectors of sections `r : Fin k → Fin p → 𝒪(V)` whose germs generate `M_y` at every `y ∈ V`
  (the module analogue of `IdealSheaf.HasLocalGenerators`, which is the case `p = 1` on the whole
  space).
* `IsCoherent 𝒪`: [Fre17, Ch. V, 7.2] in the shape of 10.3: for every open `U` and every matrix
  `F` of sections over `U`, the kernel system of `F` is locally finitely generated on `U`. This is
  NOT Noetherianity of the stalks: each `ker F_y` is finitely generated in a Noetherian stalk, but
  coherence asks for finitely many relation vectors of *sections* whose germs generate the kernels
  at all nearby points at once.
* `IdealSheaf.IsCoherent J`: [Fre17, Ch. V, 7.3] for an ideal sheaf `J` of finite type, in Serre's
  form: for every open `U` and every finite family of sections `g : Fin p → 𝒪(U)` of `J`, the
  relation system `y ↦ ker (a ↦ Σ_j (g j)_y · a j)` is locally finitely generated on `U`; so `J`
  is locally finitely presented.
* `AnalyticSpace.IsNoetherian X` [BM97, 3.9]: every decreasing sequence of closed subspaces of `X`
  stabilizes (`W.le V` is `V ≤ W` as ideal sheaves; equality of ideal sheaves is stalkwise).

The structure sheaf of every analytic `K`-space is coherent
(`Hironaka/AnalyticSpace/CoherentAnalytic.lean`); a Noetherian analytic `K`-space is compact, and
the converse holds under the Noether lemma for the models.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Manifold

section Algebra

variable {R : Type*} [CommRing R]

/-- The kernel of the linear map `Fin p → R → Fin q → R` of a matrix given as a function
(Freitag's `kernel (F_a)` at one ring). -/
abbrev relKer {p q : ℕ} (F : Fin q → Fin p → R) : Submodule R (Fin p → R) :=
  LinearMap.ker (Matrix.mulVecLin (Matrix.of F))

theorem mem_relKer_iff {p q : ℕ} (F : Fin q → Fin p → R) (a : Fin p → R) :
    a ∈ relKer F ↔ ∀ i, ∑ j, F i j * a j = 0 := by
  simp only [relKer, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro h i
    have := congrFun h i
    simpa [Matrix.mulVec, dotProduct] using this
  · intro h
    funext i
    simpa [Matrix.mulVec, dotProduct] using h i

end Algebra

variable {X : TopCat.{u}} (𝒪 : TopCat.Sheaf CommRingCat.{u} X)

/-- The relation module `M_a := kernel (F_a)` of the matrix `F` at `y` [Fre17, Ch. I, 10.3]: the
kernel of the germ `F_y : 𝒪_y^p → 𝒪_y^q`, `a ↦ (i ↦ Σ_j (F i j)_y · a j)`. -/
def relationSubmodule {U : Opens X} {p q : ℕ} (F : Fin q → Fin p → 𝒪.presheaf.obj (op U)) (y : X)
    (hy : y ∈ U) : Submodule (𝒪.presheaf.stalk y) (Fin p → 𝒪.presheaf.stalk y) :=
  relKer fun i j => 𝒪.presheaf.germ U y hy (F i j)

/-- A system `M` of submodules `M_y ⊆ 𝒪_y^p` over the points of the open `U` is *locally finitely
generated* (Freitag's "coherent system", [Fre17, Ch. I, 10.1–10.2]) if every `x ∈ U` has an open
neighbourhood `V ≤ U` and finitely many vectors of sections `r : Fin k → Fin p → 𝒪(V)` whose germs
generate `M_y` at every `y ∈ V`. -/
def HasLocalGeneratorsOn (U : Opens X) (p : ℕ)
    (M : ∀ y : X, y ∈ U → Submodule (𝒪.presheaf.stalk y) (Fin p → 𝒪.presheaf.stalk y)) : Prop :=
  ∀ x : X, x ∈ U → ∃ (V : Opens X) (hVU : V ≤ U) (_ : x ∈ V) (k : ℕ)
    (r : Fin k → Fin p → 𝒪.presheaf.obj (op V)),
    ∀ y (hy : y ∈ V), M y (hVU hy) =
      Submodule.span (𝒪.presheaf.stalk y) (Set.range fun l => fun j => 𝒪.presheaf.germ V y hy
      (r l j))

/-- The sheaf of rings `𝒪` is *coherent* ([Fre17, Ch. V, 7.2], in the shape of 10.3;
[BM97, (3.8)]) if for every open `U` and every matrix `F : Fin q → Fin p → 𝒪(U)` of sections the
kernel system `y ↦ ker (F_y : 𝒪_y^p → 𝒪_y^q)` is locally finitely generated on `U`. -/
def IsCoherent : Prop :=
  ∀ (U : Opens X) (p q : ℕ) (F : Fin q → Fin p → 𝒪.presheaf.obj (op U)),
    HasLocalGeneratorsOn 𝒪 U p fun y hy => relationSubmodule 𝒪 F y hy

namespace IdealSheaf

variable {𝒪}

/-- An ideal sheaf `J` of finite type is *coherent* ([Fre17, Ch. V, 7.3]; [BM97, (3.8)]: "every
ideal of finite type in `𝒪_X` is coherent") if for every open `U` and every finite family of
sections `g : Fin p → 𝒪(U)` of `J` the relation system `y ↦ ker (a ↦ Σ_j (g j)_y · a j)` is
locally finitely generated on `U` — `J` is locally finitely presented. -/
def IsCoherent (J : IdealSheaf 𝒪) : Prop :=
  ∀ (U : Opens X) (p : ℕ) (g : Fin p → 𝒪.presheaf.obj (op U)), (∀ j, g j ∈ J.carrier U) →
    HasLocalGeneratorsOn 𝒪 U p fun y hy => relationSubmodule 𝒪 (fun _ : Fin 1 => g) y hy

end IdealSheaf

end Manifold

namespace AnalyticSpace

variable {K : Type} [RCLike K]

/-- "We say that `X` is Noetherian if every decreasing sequence of closed subspaces of `X` (in
`𝒜`) stabilizes" [BM97, 3.9]: every decreasing sequence `W 0 ⊇ W 1 ⊇ …` of closed analytic
subspaces of `X` (`ClosedSubspace.le (W (m+1)) (W m)`) is eventually constant. -/
def IsNoetherian (X : AnalyticSpace.{u} K) : Prop :=
  ∀ W : ℕ → ClosedSubspace X, (∀ m, ClosedSubspace.le (W (m + 1)) (W m)) → ∃ N, ∀ m ≥ N, W m = W N

end AnalyticSpace
