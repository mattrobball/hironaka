/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Manifold.Restrict
public import Hironaka.AnalyticSpace.QuotientBot
public import Hironaka.AnalyticSpace.OpenSubspaceLemmas
import Hironaka.Manifold.IdealSheaf.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Charts of a manifold as isomorphisms with open subsets of `Kⁿ`

A chart `φ` of an analytic manifold `M` modelled on `E ≃ Kⁿ` identifies its domain with an open
subset of `Kⁿ` as `K`-local-ringed spaces. The pieces:

* two mutually inverse analytic maps induce a `K`-isomorphism of the spaces of the manifolds
  (`ofManifoldIso`, by the functoriality of `ofManifoldHom`);
* the chart `φ`, followed by the coordinates `ψ : E ≃L[K] Kⁿ` (lifted to `Kn K n`), is an analytic
  bijection `φ.source ≃ G` onto the open `G = ψ(φ.target) ⊆ Kⁿ` with analytic inverse
  (`chartToOpens`, `chartFromOpens`), hence `Sp(φ.source) ≅ Sp(G)` (`chartKIso`);
* `Sp(G) ≅ (G, 𝒜_G)` (`ofManifold_restrictOpen_iso` for the manifold `Kⁿ`), and `(G, 𝒜_G)` is the
  local analytic `K`-space with no equations (`localModelZeroIso`: the quotient by the zero ideal
  sheaf), which is the open subspace `⊤` of itself (`restrictOpenTopIso`).

Together (`chartLocalModelIso`): `Sp(M) | φ.source ≅ (localModel K n G ![]) | ⊤`, which is
Hironaka's clause (i) in the definition of an analytic space [Hir64, Ch. 0, §1, pp. 119–120] for the
space of a manifold; it is the `locallyModel` field of `toSpace`
(`Hironaka.AnalyticSpace.Manifold.Defs`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

noncomputable section

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K] {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace K E'] {M : Type u} [TopologicalSpace M]
  [ChartedSpace E M] {N : Type u} [TopologicalSpace N] [ChartedSpace E' N]

/-- `ofManifoldHom` depends on the map only. -/
theorem ofManifoldHom_congr {f g : M → N} (h : f = g) (hf : ContMDiff 𝓘(K, E) 𝓘(K, E') ω f) :
    ofManifoldHom f hf = ofManifoldHom g (h ▸ hf) := by
  subst h
  rfl

/-- **Two mutually inverse analytic maps induce a `K`-isomorphism** `Sp(M) ≅ Sp(N)` (the
functoriality of `ofManifoldHom`). -/
def ofManifoldIso (f : M → N) (g : N → M) (hf : ContMDiff 𝓘(K, E) 𝓘(K, E') ω f)
    (hg : ContMDiff 𝓘(K, E') 𝓘(K, E) ω g) (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) :
    KIso (ofManifold K E M) (ofManifold K E' N) where
  hom := ofManifoldHom f hf
  inv := ofManifoldHom g hg
  hom_inv_id := by
    rw [← ofManifoldHom_comp, ofManifoldHom_congr (funext hgf : g ∘ f = id)]
    rfl
  inv_hom_id := by
    rw [← ofManifoldHom_comp, ofManifoldHom_congr (funext hfg : f ∘ g = id)]
    rfl

theorem ofManifoldIso_hom (f : M → N) (g : N → M) (hf : ContMDiff 𝓘(K, E) 𝓘(K, E') ω f)
    (hg : ContMDiff 𝓘(K, E') 𝓘(K, E) ω g) (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) :
    (ofManifoldIso f g hf hg hgf hfg).hom = ofManifoldHom f hf :=
  rfl

section Chart

variable {n : ℕ} (ψ : E ≃L[K] (Fin n → K)) (φ : OpenPartialHomeomorph M E)

/-- The source of a chart, as an open of `M`. -/
def chartSourceOpens : Opens M := ⟨φ.source, φ.open_source⟩

/-- The open `G = ψ(φ.target) ⊆ Kⁿ` of the chart `φ` in the coordinates `ψ` (lifted to `Kn K n`). -/
def chartOpens : Opens (Kn.{u} K n) :=
  ⟨{y | ψ.symm y.down ∈ φ.target},
    φ.open_target.preimage (ψ.symm.continuous.comp Homeomorph.ulift.continuous)⟩

omit [ChartedSpace E M] in
theorem mem_chartOpens {y : Kn.{u} K n} : y ∈ chartOpens ψ φ ↔ ψ.symm y.down ∈ φ.target :=
  Iff.rfl

/-- The chart `φ.source → G`, `x ↦ ψ (φ x)`. -/
def chartToOpens (x : chartSourceOpens φ) : chartOpens ψ φ :=
  ⟨ULift.up (ψ (φ x)), by
    rw [mem_chartOpens, ULift.down_up, ψ.symm_apply_apply]
    exact φ.map_source x.2⟩

/-- The inverse chart `G → φ.source`, `y ↦ φ⁻¹ (ψ⁻¹ y)`. -/
def chartFromOpens (y : chartOpens ψ φ) : chartSourceOpens φ :=
  ⟨φ.symm (ψ.symm y.1.down), φ.map_target ((mem_chartOpens ψ φ).mp y.2)⟩

omit [ChartedSpace E M] in
theorem chartFromOpens_chartToOpens (x : chartSourceOpens φ) :
    chartFromOpens ψ φ (chartToOpens ψ φ x) = x := by
  apply Subtype.ext
  change φ.symm (ψ.symm ((ULift.up (ψ (φ x)) : Kn.{u} K n).down)) = x
  rw [ULift.down_up, ψ.symm_apply_apply, φ.left_inv x.2]

omit [ChartedSpace E M] in
theorem chartToOpens_chartFromOpens (y : chartOpens ψ φ) :
    chartToOpens ψ φ (chartFromOpens ψ φ y) = y := by
  apply Subtype.ext
  change ULift.up (ψ (φ (φ.symm (ψ.symm y.1.down)))) = y.1
  rw [φ.right_inv ((mem_chartOpens ψ φ).mp y.2), ψ.apply_symm_apply, ULift.up_down]

variable {φ}

/-- The coordinates `ψ`, lifted to `Kn K n`, are analytic. -/
theorem contMDiff_ulift_coord :
    ContMDiff 𝓘(K, E) 𝓘(K, Kn.{u} K n) ω (fun e : E => (ULift.up (ψ e) : Kn.{u} K n)) :=
  ((ψ.trans ContinuousLinearEquiv.ulift.symm : E ≃L[K] Kn.{u} K n) :
    E →L[K] Kn.{u} K n).contMDiff

/-- The inverse coordinates, from `Kn K n`, are analytic. -/
theorem contMDiff_coord_down :
    ContMDiff 𝓘(K, Kn.{u} K n) 𝓘(K, E) ω (fun y : Kn.{u} K n => ψ.symm y.down) :=
  ((ContinuousLinearEquiv.ulift.trans ψ.symm : Kn.{u} K n ≃L[K] E) :
    Kn.{u} K n →L[K] E).contMDiff

theorem contMDiff_chartToOpens (hφ : φ ∈ maximalAtlas 𝓘(K, E) ω M) :
    ContMDiff 𝓘(K, E) 𝓘(K, Kn.{u} K n) ω (chartToOpens ψ φ) := by
  refine (contMDiff_subtypeVal_comp_iff' _).mp ?_
  have h1 : ContMDiff 𝓘(K, E) 𝓘(K, E) ω (φ ∘ (Subtype.val : chartSourceOpens φ → M)) :=
    (contMDiffOn_of_mem_maximalAtlas hφ).comp_contMDiff contMDiff_subtype_val fun x => x.2
  exact (contMDiff_ulift_coord ψ).comp h1

theorem contMDiff_chartFromOpens (hφ : φ ∈ maximalAtlas 𝓘(K, E) ω M) :
    ContMDiff 𝓘(K, Kn.{u} K n) 𝓘(K, E) ω (chartFromOpens ψ φ) := by
  refine (contMDiff_subtypeVal_comp_iff' _).mp ?_
  have h1 : ContMDiff 𝓘(K, Kn.{u} K n) 𝓘(K, E) ω
      ((fun y : Kn.{u} K n => ψ.symm y.down) ∘ (Subtype.val : chartOpens ψ φ → Kn.{u} K n)) :=
    (contMDiff_coord_down ψ).comp contMDiff_subtype_val
  exact (contMDiffOn_symm_of_mem_maximalAtlas hφ).comp_contMDiff h1
    fun y => (mem_chartOpens ψ φ).mp y.2

/-- **A chart identifies its domain with an open subset of `Kⁿ`** as `K`-local-ringed spaces:
`Sp(φ.source) ≅ Sp(G)`, `G = ψ(φ.target)`. -/
def chartKIso (hφ : φ ∈ maximalAtlas 𝓘(K, E) ω M) :
    KIso (ofManifold K E (chartSourceOpens φ)) (ofManifold K (Kn.{u} K n) (chartOpens ψ φ)) :=
  ofManifoldIso (chartToOpens ψ φ) (chartFromOpens ψ φ) (contMDiff_chartToOpens ψ hφ)
    (contMDiff_chartFromOpens ψ hφ) (chartFromOpens_chartToOpens ψ φ)
    (chartToOpens_chartFromOpens ψ φ)

end Chart

end AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace

open KLocallyRingedSpace

variable (K : Type) [RCLike K] (n : ℕ)

/-- The empty family of equations. -/
def noEquations (G : Opens (Kn.{u} K n)) : Fin 0 → AnalyticFun K n G := fun i => i.elim0

/-- The ideal sheaf generated by no equations has zero stalks. -/
theorem stalkIdeal_modelIdeal_noEquations (G : Opens (Kn.{u} K n)) (x : analyticSpaceOfOpen K n G) :
    (modelIdeal K n G (noEquations K n G)).stalkIdeal x = ⊥ := by
  refine (IdealSheaf.stalkIdeal_ofGlobal _ _ x).trans ?_
  rw [Set.range_eq_empty, Ideal.span_empty]

/-- **The local analytic `K`-space with no equations is `(G, 𝒜_G)`**: the quotient of `(G, 𝒜_G)` by
the zero ideal sheaf is `(G, 𝒜_G)` itself (`quotientBotIso`). -/
def localModelZeroIso (G : Opens (Kn.{u} K n)) :
    KIso (localModel K n G (noEquations K n G)) (analyticSpaceOfOpen K n G) :=
  quotientBotIso _ _ (stalkIdeal_modelIdeal_noEquations K n G)

variable {K n} {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] {M : Type u}
  [TopologicalSpace M] [ChartedSpace E M]

/-- **The open subspace of `Sp(M)` over a chart domain is a local analytic `K`-space**, Hironaka's
clause (i) [Hir64, Ch. 0, §1, p. 120] for the space of a manifold: with no equations, on the open
`G = ψ(φ.target)` of `Kⁿ`, and `W = ⊤`. -/
def chartLocalModelIso (ψ : E ≃L[K] (Fin n → K)) {φ : OpenPartialHomeomorph M E}
    (hφ : φ ∈ maximalAtlas 𝓘(K, E) ω M) :
    KIso ((ofManifold K E M).restrictOpen (chartSourceOpens φ))
      ((localModel K n (chartOpens ψ φ) (noEquations K n _)).restrictOpen ⊤) :=
  (ofManifold_restrictOpen_iso _).trans ((chartKIso ψ hφ).trans
    ((ofManifold_restrictOpen_iso (chartOpens ψ φ)).symm.trans
      ((localModelZeroIso K n (chartOpens ψ φ)).symm.trans (restrictOpenTopIso _).symm)))

end AnalyticSpace
