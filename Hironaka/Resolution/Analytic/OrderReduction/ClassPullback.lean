/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Basic
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The classes of Theorem 103 under pull-back along local analytic isomorphisms

The proof of [Kol07, Theorem 103] uses, without stating them, that its classes are stable under
pull-back: the hypothesis of Step 2 is local, and in Step 3 `BO_{n,m}` "is defined on
`(X^*, g^* I, g^{-1} E)`" by Step 2. Here: the class `BOClass m` and the class of
triples with a global hypersurface of maximal contact are closed under pull-back along local
analytic isomorphisms `g : N → M`. The order of the pulled-back ideal sheaf at `y` is the order of
`𝓘` at `g y`, a nonempty preimage `g⁻¹(E^j)` comes from a nonempty `E^j`, and the preimage
`g⁻¹(H)` of
a hypersurface of maximal contact is one, its ideal sheaf being the pull-back of the ideal sheaf of
`H` and the derivative ideal sheaves pulling back. In particular both classes are closed under
pull-back along local isomorphisms covering `cosupp(𝓘, m)`, the hypothesis
`ClosedUnderLocalIsoPullbackOverCosupp` under which the value of a functor is independent of the
hypersurface of maximal contact (`FamilyIndependence.lean`).

* `AnalyticTriple.boClass_of_isPullbackOf`, `AnalyticTriple.hasMaximalContact_of_isPullbackOf`;
* `AnalyticTriple.boClass_closedUnderLocalIsoPullbackOverCosupp`,
  `AnalyticTriple.localMCClass_closedUnderLocalIsoPullbackOverCosupp`.
-/

public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [hfd : FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {m : ℕ}

-- The finite-dimensionality `[FiniteDimensional 𝕜 E]` of the model space belongs to every statement
-- here, as to Kollár's varieties; a proof that does not need it names it (`have _hfd := hfd`) so
-- that it remains part of the statement.

/-- The class `BOClass m` is closed under pull-back along local analytic isomorphisms (used
implicitly in Step 3 of the proof of [Kol07, Theorem 103], "`BO_{n,m}` is defined on
`(X^*, g^* I, g^{-1} E)`"): the order pulls back pointwise and the nonempty members of the
pulled-back family are among the nonempty members. -/
theorem AnalyticTriple.boClass_of_isPullbackOf {M N : AnalyticManifold.{u} 𝕜 E}
    {T : AnalyticTriple ψ₀ M} (hT : AnalyticTriple.BOClass m T) {T' : AnalyticTriple ψ₀ N}
    {g : AnalyticMap N M} (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g)
    (hT' : T'.IsPullbackOf T g) : AnalyticTriple.BOClass m T' := by
  have _hfd := hfd
  obtain ⟨hm, hord, hfin⟩ := hT
  rcases T' with ⟨I', hne, F', hsnc⟩
  obtain ⟨hI, hF⟩ := hT'
  dsimp only at hI hF
  subst hI hF
  refine ⟨hm, fun x => ?_, ?_⟩
  · exact (IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ T.I (hg x)).trans_le (hord _)
  · have := hfin
    refine Finite.of_injective
      (fun j : {j // (T.F.comap g).hyp j ≠ ∅} => (⟨j.1, fun h0 => j.2 ?_⟩ : {j // T.F.hyp j ≠ ∅}))
      fun a b h => Subtype.ext (Subtype.mk.inj h)
    change ⇑g ⁻¹' T.F.hyp j.1 = ∅
    rw [h0, Set.preimage_empty]

/-- The class of triples with a global hypersurface of maximal contact is closed under pull-back
along local analytic isomorphisms (the hypersurfaces `H^{(j)}` on the pieces `X^{(j)}` of Step 3
of the proof of [Kol07, Theorem 103]): the preimage of the hypersurface is one, its ideal sheaf
being the pull-back of the ideal sheaf of `H` (`comap_idealSheaf_of_isLocalDiffeomorph`) and the
derivative ideal sheaves pulling back. -/
theorem AnalyticTriple.hasMaximalContact_of_isPullbackOf {M N : AnalyticManifold.{u} 𝕜 E}
    {T : AnalyticTriple ψ₀ M} (hT : AnalyticTriple.HasMaximalContact m T)
    {T' : AnalyticTriple ψ₀ N} {g : AnalyticMap N M}
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) (hT' : T'.IsPullbackOf T g) :
    AnalyticTriple.HasMaximalContact m T' := by
  have _hfd := hfd
  obtain ⟨H, hH, hHmc⟩ := hT
  rcases T' with ⟨I', hne, F', hsnc⟩
  obtain ⟨hI, hF⟩ := hT'
  dsimp only at hI hF
  subst hI hF
  refine ⟨⇑g ⁻¹' H, hH.preimage_of_isLocalDiffeomorph hg, ?_⟩
  have h1 := comap_idealSheaf_of_isLocalDiffeomorph ψ₀ g hg hH
  have h2 := iteratedDeriv_pullback_of_isLocalDiffeomorph (⇑g) g.contMDiff T.I hg (m - 1)
  exact h1.symm.trans_le
    ((IdealSheaf.pullback_le_pullback (φ := ⇑g) (hφ := g.contMDiff) hHmc).trans_eq h2.symm)

/-- The class `BOClass m` is closed under pull-back along local analytic isomorphisms covering
the cosupport. -/
theorem AnalyticTriple.boClass_closedUnderLocalIsoPullbackOverCosupp :
    AnalyticTriple.ClosedUnderLocalIsoPullbackOverCosupp (AnalyticTriple.BOClass (ψ₀ := ψ₀) m)
      m := by
  have _hfd := hfd
  intro M N T T' g hg _ hT' hT
  exact AnalyticTriple.boClass_of_isPullbackOf hT hg hT'

/-- The class `LocalMCClass m` of triples with a global hypersurface of maximal contact is closed
under pull-back along local analytic isomorphisms covering the cosupport. -/
theorem AnalyticTriple.localMCClass_closedUnderLocalIsoPullbackOverCosupp :
    AnalyticTriple.ClosedUnderLocalIsoPullbackOverCosupp (AnalyticTriple.LocalMCClass (ψ₀ := ψ₀) m)
      m := by
  have _hfd := hfd
  intro M N T T' g hg _ hT' hT
  exact ⟨AnalyticTriple.boClass_of_isPullbackOf hT.1 hg hT',
    AnalyticTriple.hasMaximalContact_of_isPullbackOf hT.2 hg hT'⟩

end Manifold

end
