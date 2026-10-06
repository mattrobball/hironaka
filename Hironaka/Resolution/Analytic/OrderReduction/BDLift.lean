/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Snc.Trace
public import Hironaka.Manifold.FiniteSuccession.Restrict.ImageVal
public import Hironaka.Resolution.Analytic.LocalIsoEquiv
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.Snc.NormalCrossings
import Hironaka.Resolution.Analytic.OrderReduction.Step22Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Lemma 102: lifting simple normal crossings from a hypersurface with the hypersurface appended

In the proof of [Kol07, Lemma 102], the going-up theorem [Kol07, Theorem 84] turns a blow-up
sequence of order `≥ m` for `(S, I_0|_S, m, (E - E^j)|_S)` into one of order `m` for
`(X_0, I_0, E - E^j)`; then, `S` being `E^j`, "every blow-up center is a smooth subvariety" of the
transform of `E^j`,
so that one has in fact a blow-up sequence of order `m` starting with `(X_0, I_0, E)`. This module
proves the second sentence (not in the sources beyond that remark):
the boundary `E` on `X_0` is the pulled-back `E - E^j` together with the transform `S` of `E^j`,
and a centre lying in `S` with simple normal crossings with the trace of the boundary on `S` has
simple normal crossings with the boundary together with `S`.

* `HypersurfaceFamily.idealSheaf_eq_of_support_eq` — the reduced ideal sheaf of a family depends
  only on its support.
* `hasSncWith_append_of_hasSncWith_traceFamily` — for a closed hypersurface `S` and a family `F`
  having simple normal crossings with `S` properly, a closed submanifold `Z'` of `S` having simple
  normal crossings with the trace `F|_S` has, read in the ambient manifold, simple normal crossings
  with `F + S`: the chart of `S` adapted to `Z'` is extended by the coordinate of `S`, which keeps
  the coordinate of `S`.
* `hasOnlyNormalCrossingsWith_idealSheaf_append_of_traceFamily` — the same in terms of ideal
  sheaves: the reduced ideal sheaf of `F + S` has only normal crossings with the ideal sheaf of `Z`.

These are used in `BDCor85.lean` to obtain [Kol07, Corollary 85] with the hypersurface in the
boundary.
-/

public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

/-- The reduced ideal sheaf of a family of hypersurfaces depends only on the support of the
family. -/
theorem _root_.Manifold.HypersurfaceFamily.idealSheaf_eq_of_support_eq {M : Type u}
    [TopologicalSpace M]
    [ChartedSpace E M] {F F' : HypersurfaceFamily M} (h : F.support = F'.support) :
    F.idealSheaf (𝕜 := 𝕜) (E := E) = F'.idealSheaf := by
  unfold HypersurfaceFamily.idealSheaf
  rw [h]

section Chart

variable {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] {S : Set M}

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- Lifting simple normal crossings from a hypersurface with the hypersurface appended (the proof of
[Kol07, Lemma 102]: `S` being `E^j`, "every blow-up center is a smooth subvariety" of the
transform of `E^j`, so that one has a blow-up sequence of order `m` starting with `(X_0, I_0, E)`):
for a closed hypersurface `S` and a family `F` with simple normal crossings
having simple normal crossings with `S` properly, a closed submanifold `Z'` of `S` (regarded as a
manifold) having simple normal crossings with the trace `F|_S` has, read in the ambient manifold,
simple normal crossings with `F + S`. The chart of `S` adapted to `Z'` and to the trace is extended
to the ambient manifold along the chart of `F` adapted to `S`, and the extension keeps the
coordinate of `S`. -/
theorem hasSncWith_append_of_hasSncWith_traceFamily (hS : IsClosedSubmanifold ψ S 1)
    (F : HypersurfaceFamily M) (_hF : F.IsSnc ψ) (hFS : F.HasSncWithProper ψ S 1)
    {Z' : Set hS.toAnalyticManifold} {c' : ℕ}
    (_hZ' : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) Z' c')
    (hZF : (hS.traceFamily F).HasSncWith (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) Z' c') :
    (F.append S).HasSncWith ψ (hS.imageVal Z') (c' + 1) := by
  rintro _ ⟨a', ha', rfl⟩
  -- the proper snc chart of `F` adapted to `S` at `a'`
  obtain ⟨φ, σ₁, cidx₁, hφ, hc₁, hproper⟩ := hFS (a' : S).1 (a' : S).2
  have haφ : (a' : S).1 ∈ φ.source := hc₁.2.1
  -- the chart of `S` adapted to `Z'`, an snc chart of the trace at `a'`
  obtain ⟨χ, σ', cidx', hχ, hcχ⟩ := hZF a' ha'
  have ha'χ : a' ∈ χ.source := hcχ.2.1
  -- the extended chart, adapted to `imageVal Z'`
  obtain ⟨hmem, hadapt⟩ := hS.isAdaptedChart_extendComplE ha'χ hχ haφ hφ
  have hχ₀app : ∀ p : hS.toAnalyticManifold,
      hS.inducedChart hφ (a' : S).2 p = projCompl σ₁ (ψ (φ (p : S).1)) := fun _ => rfl
  have hχ₀src : ∀ p : hS.toAnalyticManifold,
      p ∈ (hS.inducedChart hφ (a' : S).2).source ↔ (p : S).1 ∈ φ.source := fun _ => Iff.rfl
  set χ₀ := hS.inducedChart hφ (a' : S).2 with hχ₀def
  clear_value χ₀
  refine ⟨φ ≫ₕ extendComplE ψ σ₁ (χ₀.symm ≫ₕ χ), imageValEmb σ₁ σ',
    HypersurfaceFamily.appendIdx F S (a' : S).1
      (fun j => ((complEquiv σ₁).symm (cidx' ⟨j.1, j.2⟩)).1) (σ₁ 0),
    hadapt, hadapt.1, hmem, ?_, ?_⟩
  · rintro ⟨k, hk⟩ x hx
    have hx1 : x ∈ φ.source := hx.1
    have hx2 : projCompl σ₁ (ψ (φ x)) ∈ (χ₀.symm ≫ₕ χ).source :=
      (mem_extendComplE_source ψ σ₁ _).mp hx.2
    have hw : ψ ((φ ≫ₕ extendComplE ψ σ₁ (χ₀.symm ≫ₕ χ)) x) =
        extendComplFun σ₁ (χ₀.symm ≫ₕ χ) (ψ (φ x)) :=
      ψ.apply_symm_apply _
    rcases k with j | u
    · -- a component of `F` through `a'`: the coordinate hyperplane of its trace's coordinate
      set p : hS.toAnalyticManifold := χ₀.symm (projCompl σ₁ (ψ (φ x))) with hpdef
      have hpχ : p ∈ χ.source := hx2.2
      have hp0 : p ∈ χ₀.source := χ₀.symm.map_source hx2.1
      have hpφ : (p : S).1 ∈ φ.source := (hχ₀src p).mp hp0
      change x ∈ F.hyp j ↔ ψ ((φ ≫ₕ extendComplE ψ σ₁ (χ₀.symm ≫ₕ χ)) x)
        ((complEquiv σ₁).symm (cidx' ⟨j, hk⟩)).1 = 0
      rw [hw, extendComplFun_apply_compl]
      change x ∈ F.hyp j ↔ χ p (cidx' ⟨j, hk⟩) = 0
      have hcoordp : ψ (φ (p : S).1) (cidx₁ ⟨j, hk⟩) = ψ (φ x) (cidx₁ ⟨j, hk⟩) := by
        have h1 : χ₀ p = projCompl σ₁ (ψ (φ x)) := χ₀.right_inv hx2.1
        rw [hχ₀app] at h1
        have h2 := congrFun h1 (complEquiv σ₁ ⟨cidx₁ ⟨j, hk⟩, hproper ⟨j, hk⟩⟩)
        simpa only [projCompl, Equiv.symm_apply_apply] using h2
      rw [hc₁.mem_iff ⟨j, hk⟩ hx1, ← hcoordp, ← hc₁.mem_iff ⟨j, hk⟩ hpφ]
      exact hcχ.mem_iff ⟨j, hk⟩ hpχ
    · -- the member `S`: the coordinate hyperplane of `σ₁ 0`, kept by the extension
      change x ∈ S ↔ ψ ((φ ≫ₕ extendComplE ψ σ₁ (χ₀.symm ≫ₕ χ)) x) (σ₁ 0) = 0
      rw [hw, extendComplFun_apply_range, hφ.2 x hx1]
      exact ⟨fun h => h 0, fun h i => by rw [Subsingleton.elim i 0]; exact h⟩
  · rintro ⟨k, hk⟩ ⟨k', hk'⟩ h
    rcases k with j | u <;> rcases k' with j' | u'
    · have h' : ((complEquiv σ₁).symm (cidx' ⟨j, hk⟩)).1 =
          ((complEquiv σ₁).symm (cidx' ⟨j', hk'⟩)).1 := h
      have h1 := (complEquiv σ₁).symm.injective (Subtype.ext h')
      have h3 : j = j' := congrArg Subtype.val (hcχ.injective h1)
      subst h3
      rfl
    · exfalso
      have h' : ((complEquiv σ₁).symm (cidx' ⟨j, hk⟩)).1 = σ₁ 0 := h
      exact ((complEquiv σ₁).symm (cidx' ⟨j, hk⟩)).2 (Set.mem_range.mpr ⟨0, h'.symm⟩)
    · exfalso
      have h' : σ₁ 0 = ((complEquiv σ₁).symm (cidx' ⟨j', hk'⟩)).1 := h
      exact ((complEquiv σ₁).symm (cidx' ⟨j', hk'⟩)).2 (Set.mem_range.mpr ⟨0, h'⟩)
    · cases u
      cases u'
      rfl

end Chart

section Ideal

variable {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {X : AnalyticManifold.{u} 𝕜 E}

/-- The ideal-sheaf form of `hasSncWith_append_of_hasSncWith_traceFamily`: for a closed submanifold
`Z ⊆ S` of a closed hypersurface `S` whose trace on `S` has only normal crossings with the reduced
ideal sheaf of the trace `F|_S`, the ideal sheaf of `Z` has only normal crossings with the reduced
ideal sheaf of `F + S`, by the dictionary between simple normal crossings of families and normal
crossings of reduced ideal sheaves on both sides. -/
theorem hasOnlyNormalCrossingsWith_idealSheaf_append_of_traceFamily {S : Set X}
    (hS : IsClosedSubmanifold ψ S 1) (F : HypersurfaceFamily X) (hF : F.IsSnc ψ)
    (hFS : F.HasSncWithProper ψ S 1) {Z : Set X} {c : ℕ} (hZ : IsClosedSubmanifold ψ Z c)
    (hZS : Z ⊆ S)
    (h : AnalyticManifold.IdealSheaf.HasOnlyNormalCrossingsWith (hS.traceFamily F).idealSheaf
      (hS.preimage_val_of_subset hZ hZS).idealSheaf) :
    AnalyticManifold.IdealSheaf.HasOnlyNormalCrossingsWith (F.append S).idealSheaf
        hZ.idealSheaf := by
  have htr := (hasOnlyNormalCrossingsWith_idealSheaf_iff (hS.isSnc_traceFamily hF hFS)
    (hS.preimage_val_of_subset hZ hZS)).mp h
  have hlift := hasSncWith_append_of_hasSncWith_traceFamily hS F hF hFS
    (hS.preimage_val_of_subset hZ hZS) htr
  have hZ' : IsClosedSubmanifold ψ (hS.imageVal (hS.preimageVal Z)) (c - 1 + 1) :=
    hS.imageVal_isClosedSubmanifold (hS.preimage_val_of_subset hZ hZS)
  have hset : hS.imageVal (hS.preimageVal Z) = Z := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hx
      exact ⟨(⟨x, hZS hx⟩ : S), hx, rfl⟩
  rw [← IsClosedSubmanifold.idealSheaf_congr hZ' hZ hset]
  exact (hasOnlyNormalCrossingsWith_idealSheaf_iff
    (HypersurfaceFamily.isSnc_append_of_hasSncWithProper hF hS hFS) hZ').mpr hlift

end Ideal

end Hironaka.Manifold

end
