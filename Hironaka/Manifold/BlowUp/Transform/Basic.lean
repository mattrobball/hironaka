/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Transform.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Transforms under a blowing-up: marked ideal sheaves, weak transforms, strict transforms of sets

Transforms under the blowing-up `π : M' → M` of an analytic manifold along a closed submanifold
`Y` of codimension `c` (`IsBlowUp ψ Y c π`, with total transform `I.pullback π h.contMDiff` and
exceptional ideal sheaf `I_F = hY.idealSheaf.pullback π h.contMDiff`), and two unfoldings of the
orders
along a centre:

* `MarkedIdealSheaf` and `MarkedIdealSheaf.birationalTransform`: the marked ideal sheaf `(I, m)`
  and its birational transform `(I_F^{-m} π⁻¹(I), m)` [Kol07, Definition 60, (60.1)], the quotient
  of the total transform by the `m`-th power of the exceptional ideal sheaf `I_F`
  (`IdealSheaf.IsDivExceptional`);
* `IdealSheaf.weakTransformOf hY h I`: Hironaka's weak transform, division by the generic order
  along each component of the centre ([Hir64, Ch. 0, §5, p. 142]; [BM97, Remark 1.8]), for the
  blowing-up `h` and the ideal sheaf `hY.idealSheaf` of its centre — the unbundled reading of
  `AnalyticManifold.IdealSheaf.weakTransform`, the weak transform of the analytic main theorems;
* `strictTransformSet π Y H`: the strict transform of a subset, the closure of `π⁻¹(H ∖ Y)`;
* the order along a centre depends only on the stalk (`IdealSheaf.ordAlongIdeal_congr_stalk`),
  and the generic order is the infimum over the component of the centre
  (`IdealSheaf.genericOrdAlong_def`).

The quotients are classical choices, the unit ideal sheaf when no ideal sheaf has the colon stalks.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology Set IsLocalRing
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

section Generic

variable {X : TopCat} {𝒪 : TopCat.Sheaf CommRingCat X}

/-- The order along `D` at `a` depends only on the stalk of `J` at `a`. -/
theorem IdealSheaf.ordAlongIdeal_congr_stalk (D J J' : IdealSheaf 𝒪) (a : X)
    (h : J.stalkIdeal a = J'.stalkIdeal a) :
    IdealSheaf.ordAlongIdeal D J a = IdealSheaf.ordAlongIdeal D J' a := by
  simp only [IdealSheaf.ordAlongIdeal, h]

/-- The generic order unfolded: the infimum over the component of the centre of the order of `J`
along `D`. -/
theorem IdealSheaf.genericOrdAlong_def (D J : IdealSheaf 𝒪) (a : X) :
    IdealSheaf.genericOrdAlong D J a =
      ⨅ y ∈ connectedComponentIn D.support a, IdealSheaf.ordAlongIdeal D J y := rfl

/-- A marked ideal sheaf `(I, m)` [Kol07, Definition 60]. -/
structure MarkedIdealSheaf (𝒪 : TopCat.Sheaf CommRingCat X) where
  /-- The ideal sheaf. -/
  I : IdealSheaf 𝒪
  /-- The marking. -/
  m : ℕ

end Generic

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] {Y : Set M} {c : ℕ}

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M}

open scoped Classical in
/-- **The birational transform of a marked ideal sheaf**,
`π_*^{-1}(I, m) := (I_F^{-m} · π⁻¹(I), m)` [Kol07, Definition 60, (60.1)]: the ideal sheaf with
stalks `(π⁻¹(I)_a : I_{F,a}^m)` when it exists (which is the case for `m ≤ ν_Y(I)`), the unit
ideal sheaf otherwise. -/
def MarkedIdealSheaf.birationalTransform (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
    (J : MarkedIdealSheaf (structureSheaf 𝕜 E M)) : MarkedIdealSheaf (structureSheaf 𝕜 E M') :=
  ⟨if hex : ∃ J', IdealSheaf.IsDivExceptional (J.I.pullback π h.contMDiff)
      (hY.idealSheaf.pullback π h.contMDiff) (fun _ => J.m) J' then Classical.choose hex else ⊤,
    J.m⟩

/-- **The weak transform** of `I` by the blowing-up `π` with centre `Y`
[Hir64, Ch. 0, §5, p. 142]: `π⁻¹(I)` divided by the `ν`-th power of `I_F`, `ν` the generic order
of `I` along the component of `Y` through the point (a classical choice of the ideal sheaf with
those colon stalks; the unit ideal sheaf if none exists) — the weak transform
`AnalyticManifold.IdealSheaf.weakTransform` of the analytic main theorems along the analytic map `π`
with
the ideal sheaf `hY.idealSheaf` of the centre, read on the bundled manifolds `⟨M⟩`, `⟨M'⟩`. -/
abbrev IdealSheaf.weakTransformOf [T2Space M] [SecondCountableTopology M]
    (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) : IdealSheaf (structureSheaf 𝕜 E M') :=
  AnalyticManifold.IdealSheaf.weakTransform (M := ⟨M⟩) (M' := ⟨M'⟩) ⟨π, h.contMDiff⟩ I hY.idealSheaf

/-- The strict transform of a subset `H ⊆ M` under `π` with centre `Y`: the closure of
`π⁻¹(H ∖ Y)` (the set underlying the strict transform of [BM97, §3, "The strict transform"]). -/
def strictTransformSet (π : M' → M) (Y H : Set M) : Set M' := closure (π ⁻¹' (H \ Y))

end Manifold

end
