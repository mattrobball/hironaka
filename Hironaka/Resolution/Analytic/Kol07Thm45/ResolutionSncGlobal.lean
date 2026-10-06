/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueProof
public import Hironaka.Resolution.Analytic.Kol07Thm45.Resolution
import Hironaka.AnalyticSpace.SncFamilyDivisor
import Hironaka.Resolution.Analytic.Kol07Thm45.ExhaustionChainFamilies
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueIndep
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Clause (3) in the global form: a simple normal crossings boundary with support
`Π_X⁻¹(X.singularLocus)`

Kollár's `Π⁻¹(Sing X)` is a divisor with simple normal crossings [Kol07, Theorem 45(3)], in the
sense of [Kol07, Definition 24]; Włodarczyk's `res⁻¹(Y_sing)` likewise [Wlo09, Theorem 2.0.1(2)]:
the resolution `Π_X : R(X) → X` of a reduced analytic space carries a simple normal crossings
boundary `E` whose support is the preimage of the singular locus. The boundary is the reduced
divisor (`ClosedSubspace.divisorOf`, `Hironaka/AnalyticSpace/SncFamily.lean`) of the GLUED
exceptional family of the exhaustion: over each member `U_n` of the exhaustion the resolution
`resolutionOn (D n) bed` carries the glued traces of the piece families of ONE functor run per
local embedding datum (`exists_gluedMembers_resolutionOn_compat`, `ResolutionOnMembers.lean`), a
locally finite simple normal crossings family supported on the preimage of `X.singularLocus`; the
levels' members are matched by the label maps of the common blow-up sequence of two adjacent levels
(`exists_chainFamilies`, `ExhaustionChainFamilies.lean`), and
`Hironaka/Resolution/Analytic/Kol07Thm45/Glue/OverFamilyChain.lean` glues them along the
exhaustion's gluing datum into a locally finite simple normal crossings family on the glued space
(`chainGlueFamily`, `isSncFamily_chainGlueFamily`, `locallyFinite_chainGlueFamily`) with support the
preimage of `X.singularLocus` under the descended map (`iUnion_support_chainGlueFamily`). The datum
is read on `resolution`/`resolutionMap` through `resolutionPair_eq_of_glues`, as
`resolution_isSncDivisorSet_preimage_sing_of_independent` (`ResolutionSnc.lean`) reads it.

With the independence of the local resolution as the hypothesis `hind` (discharged in
`ResolutionAssembly.lean`). Not in the sources beyond the statements cited; bookkeeping.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set
open AnalyticSpace KLocallyRingedSpace

universe u

namespace Hironaka.Manifold.BEDanFamStar

variable {𝕜 : Type} [RCLike 𝕜]

/-- **Clause (3) of `exists_functorial_resolution` in the global form** ([Kol07, Theorem 45(3)];
[Kol07, Definition 24]; [Wlo09, Theorem 2.0.1(2)]), with the independence of the local resolution
as `hind` — for a reduced `X` under `hbed`, a closed subspace `E` of `bed.resolution X` that is a
simple normal crossings boundary with support `Π_X⁻¹(X.singularLocus)`: the reduced divisor
`divisorOf` of the glued chain family of the levels' families (`exists_chainFamilies`), on the glued
space (`resolutionPair_eq_of_glues`). -/
theorem resolution_exists_isSncBoundary_preimage_sing_of_independent
    (X : AnalyticSpace.{u} 𝕜) (hX : X.IsReduced) (bed : BEDanFamStar.{u} 𝕜)
    (hbed : bed.IsEmbeddedDesing) (hind : LocalResolutionIndependentOn X bed) :
    ∃ E : ClosedSubspace (bed.resolution X),
      ClosedSubspace.IsSncBoundary E ∧
      Manifold.IdealSheaf.support E =
        ⇑(bed.resolutionMap X) ⁻¹'
          singularLocus X := by
  have h := resolutionGlues_of_isEmbeddedDesing_of_independent X hX bed hbed hind
  obtain ⟨H, hH, -, hsupp, e, hpair, hsurj⟩ := exists_chainFamilies bed h.some hbed hind
  have hmono : ∀ n : ℕ, h.some.U n ≤ h.some.U (n + 1) := fun n x hx =>
    h.some.closure_U_subset_succ n (subset_closure hx)
  have hF := h.some.glue.isSncFamily_chainGlueFamily hmono H hH e hpair hsurj
  have hU := h.some.glue.iUnion_support_chainGlueFamily hmono H hH e hpair hsurj
    (singularLocus X) hsupp
  suffices key : ∀ p : Σ R :
      AnalyticSpace.{u} 𝕜, (R ⟶ X),
      p = bed.resolutionPair X → ∃ E : ClosedSubspace p.1,
        ClosedSubspace.IsSncBoundary E ∧
            Manifold.IdealSheaf.support E =
          ⇑p.2 ⁻¹'
              singularLocus X from
    key _ rfl
  intro p hp
  rw [bed.resolutionPair_eq_of_glues X hX h] at hp
  subst hp
  exact ⟨ClosedSubspace.divisorOf _ hF.1, ClosedSubspace.isSncBoundary_divisorOf hF,
    (ClosedSubspace.support_divisorOf _ hF.1).trans hU⟩

end Hironaka.Manifold.BEDanFamStar

end
