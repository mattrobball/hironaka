/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Manifold.Defs
import Hironaka.AnalyticSpace.RegPoints
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The simple locus of a closed analytic subspace of a manifold is open in the subspace topology

The simple points `Y.regularLocus` of the closed analytic subspace `Y = Sp(M)/𝓘` cut out by an ideal
sheaf `𝓘` on an analytic manifold `M` (`AnalyticSpace.regularLocus` on
`IdealSheaf.toAnalyticSpace 𝓘`: the points whose local ring is regular, [Hir64, p. 121]) form an
open subset of `Y` (`isOpen_reg`), and `Y` carries the subspace topology of `M` (its carrier is the
support of `𝓘` as a subtype): so a simple point has an open neighbourhood `V` in `M` over which
every point of `Y` is simple (`exists_opens_reg_of_mem_reg`). This is the one fact needed, beyond
the local analysis at a regular point (`bedanFamOfInput_center_disjoint_fiber_near_regular` of
`Hironaka/Resolution/Analytic/Wlo09/Clauses.lean`, stated for an open `V` of the ambient manifold on
which `Y` is non-singular), to prove clause (2) of [Wlo09, Theorem 2.0.2], that the centres are
disjoint from the preimages of `Y.regularLocus`: a regular point of `Y ∩ U` lies in such a `V`. The
stalk-level facts used alongside it (a point of `Y` is simple iff `𝒪_{M,p}/𝓘_p` is regular, and this
is invariant under local analytic isomorphisms of the ambient manifold) are
`mem_reg_toAnalyticSpace_iff`, `isRegularLocalRing_quotient_stalkIdeal_comap_iff`,
`mem_cosupport_comap_iff` and `sing_toAnalyticSpace_eq_empty_iff` of `Clauses.lean`.
-/

public section

noncomputable section

open Set Topology TopologicalSpace AnalyticSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-- A simple point of the closed subspace has an open neighbourhood `V` in the ambient manifold
over which every point of the subspace is simple: the simple locus is open (`isOpen_reg`), in the
subspace topology. -/
theorem exists_opens_reg_of_mem_reg (J : AnalyticManifold.IdealSheaf M) {z : J.toAnalyticSpace}
    (hz : z ∈ regularLocus J.toAnalyticSpace) :
    ∃ V : Opens M, J.toAnalyticSpaceι z ∈ V ∧
      ∀ z' : J.toAnalyticSpace, J.toAnalyticSpaceι z' ∈ V →
        z' ∈ regularLocus J.toAnalyticSpace := by
  have hopen : IsOpen (regularLocus J.toAnalyticSpace) :=
    AnalyticSpace.isOpen_reg J.toAnalyticSpace
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp hopen
  refine ⟨⟨t, ht⟩, ?_, fun z' hz' => ?_⟩
  · rw [← hts] at hz; exact hz
  · rw [← hts]; exact hz'

end Hironaka.Manifold

end
