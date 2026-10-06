/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.DisjointUnion.Defs
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Hironaka.Manifold.FiniteSuccession.Functor.SigmaDesc
import Hironaka.Manifold.LocalDiffeomorph
public import Hironaka.Manifold.SigmaManifold
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Topology.Sheaves.Init

/-!
# The coproduct of local analytic isomorphisms is a local analytic isomorphism

A local inverse `Φ` of `f i` at `x` lifts to a local inverse of the coproduct `fun p => f p.1 p.2`
at `⟨i, x⟩`: source `Sigma.mk i '' Φ.source`, inverse `y ↦ ⟨i, Φ.symm y⟩`
(`PartialDiffeomorph.sigmaLift`). Hence the coproduct of a family of local diffeomorphisms is a
local diffeomorphism (`IsLocalDiffeomorph.sigmaDesc`); this is the map `g : ∐ Uᵢ → X` of the proof
of [Kol07, Proposition 37], a surjective local analytic isomorphism.
-/

@[expose] public section

open Set Topology
open scoped Manifold ContDiff

universe u

section LocalDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} {n : WithTop ℕ∞}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]

/-- A local inverse of `f i` at `x`, lifted to the disjoint union. -/
noncomputable def PartialDiffeomorph.sigmaLift {f : ∀ i, M i → P}
    (hf : ∀ i, ContMDiff I J n (f i)) {i : ι} (Φ : PartialDiffeomorph I J (M i) P n)
    (hΦ : EqOn (f i) Φ Φ.source) : PartialDiffeomorph I J (Σ i, M i) P n where
  toFun p := f p.1 p.2
  invFun y := ⟨i, Φ.symm y⟩
  source := Sigma.mk i '' Φ.source
  target := Φ.target
  map_source' := by
    rintro _ ⟨y, hy, rfl⟩
    change f i y ∈ Φ.target
    rw [hΦ hy]
    exact Φ.map_source hy
  map_target' z hz := ⟨Φ.symm z, Φ.map_target hz, rfl⟩
  left_inv' := by
    rintro _ ⟨y, hy, rfl⟩
    change (⟨i, Φ.toPartialEquiv.symm (f i y)⟩ : Σ i, M i) = ⟨i, y⟩
    rw [hΦ hy]
    exact congrArg (Sigma.mk i) (Φ.toPartialEquiv.left_inv hy)
  right_inv' z hz := by
    change f i (Φ.toPartialEquiv.symm z) = z
    exact (hΦ (Φ.toPartialEquiv.map_target hz)).trans (Φ.toPartialEquiv.right_inv hz)
  open_source := isOpenMap_sigmaMk _ Φ.open_source
  open_target := Φ.open_target
  contMDiffOn_toFun := (ContMDiff.sigmaDesc hf).contMDiffOn
  contMDiffOn_invFun := (ContMDiff.sigmaMk (I := I) (n := n) (M := M) i).comp_contMDiffOn
    Φ.contMDiffOn_invFun

/-- The coproduct of local diffeomorphisms is a local diffeomorphism. -/
theorem IsLocalDiffeomorph.sigmaDesc {f : ∀ i, M i → P} (hf : ∀ i, IsLocalDiffeomorph I J n (f i)) :
    IsLocalDiffeomorph I J n (fun p : Σ i, M i => f p.1 p.2) := by
  rintro ⟨i, x⟩
  obtain ⟨Φ, hxΦ, hΦ⟩ := (hf i x).exists_partialDiffeomorph
  exact IsLocalDiffeomorphAt.of_eqOn (PartialDiffeomorph.sigmaLift (fun j => (hf j).contMDiff) Φ hΦ)
    ⟨x, hxΦ, rfl⟩ fun _ _ => rfl

end LocalDiffeomorph
