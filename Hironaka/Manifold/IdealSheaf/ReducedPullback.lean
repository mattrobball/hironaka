/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.IdealSheaf.DerivLocality

/-!
# The pull-back of a reduced ideal sheaf along a local analytic isomorphism

A local analytic isomorphism `φ : N → M` has bijective germ maps at every point
(`germMap_bijective_of_isLocalDiffeomorphAt`), so the stalk of the pull-back `φ^*J` at `b` is the
image of the stalk of `J` at `φ b` under a ring isomorphism; a radical ideal maps to a radical
ideal, and `φ^*J` is reduced when `J` is (`IdealSheaf.isReduced_pullback_of_isLocalDiffeomorph`).
This is the local-isomorphism counterpart of `IdealSheaf.isReduced_pullback_diffeomorph`, and the
reason the pairs `(M, Y)` of a manifold and a reduced closed subspace pull back along local
analytic isomorphisms (`AnalyticManifold.EmbeddedPair.pullback`).
-/

@[expose] public section

universe u

open scoped Manifold ContDiff

namespace Manifold.IdealSheaf

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The pull-back of a reduced ideal sheaf along a local analytic isomorphism is reduced: the germ
maps of a local analytic isomorphism are ring isomorphisms at every point
(`germMap_bijective_of_isLocalDiffeomorphAt`), and a radical ideal maps to a radical ideal under a
surjective ring homomorphism with trivial kernel. -/
theorem isReduced_pullback_of_isLocalDiffeomorph {M N : AnalyticManifold.{u} 𝕜 E}
    (φ : AnalyticMap N M) (hφ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω φ)
    {J : AnalyticManifold.IdealSheaf M} (hJ : AnalyticManifold.IdealSheaf.IsReduced J) :
    AnalyticManifold.IdealSheaf.IsReduced (J.pullback ⇑φ φ.contMDiff) := by
  intro b
  rw [stalkIdeal_pullback]
  obtain ⟨hinj, hsurj⟩ := germMap_bijective_of_isLocalDiffeomorphAt ⇑φ φ.contMDiff (hφ b)
  have hker : RingHom.ker (germMap ⇑φ φ.contMDiff b) ≤ J.stalkIdeal (φ b) := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  rw [← Ideal.radical_eq_iff, ← Ideal.map_radical_of_surjective hsurj hker,
    Ideal.radical_eq_iff.mpr (hJ (φ b))]

end Manifold.IdealSheaf
