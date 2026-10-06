/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.LimitFamily
public import Hironaka.Manifold.Jacobian.Defs
import Hironaka.Manifold.Jacobian.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The Jacobian stalk of the glued blow-down on a piece

The blow-down `σ : M̃ → M` of the principalization theorem is glued from the blow-downs of the
pieces of a compact exhaustion: Włodarczyk glues the `Ũ_i = prin⁻¹(U_i)` over a cover by
relatively compact opens into a manifold `M̃` with a proper bimeromorphic `prin : M̃ → M`
[Wlo09, §4.1]; Kollár passes from neighbourhoods of compact sets to "any analytic space that is an
increasing union of its compact subsets" [Kol07, 44]. Here `σ` is `CompatibleFamily.limitBlowDown`,
the direct limit of the pieces' composites `Π^{(m)} : M'_m → M_m ⊆ M` along the analytic open
embeddings `ι_m = toLimitMap m : M'_m → M̃`. At a point `q` of the piece `m`, the Jacobian stalk of
`σ` at `ι_m q`, transported along the bijective germ map of `ι_m`, is the Jacobian stalk of the
piece's composite `σ^{(m)}` at `q` (`CompatibleFamily.jacobianStalk_limitBlowDown_toLimitMap`):
`σ ∘ ι_m = Π^{(m)} = inclusion ∘ σ^{(m)}` (`limitDesc_comp_toLimitMap`, the definition of
`blowDownOn`), and the chain rule (`Hironaka/Manifold/Jacobian/Comp.lean`) keeps the piece's
stalk because `ι_m` and the inclusion `M_m ⊆ M` are local analytic isomorphisms
(`isAnalyticOpenEmbedding_toLimitMap`, `isLocalDiffeomorph_inclusion`; their Jacobian stalks are
`⊤`). With the Jacobian ledger of each piece
(`Hironaka/Resolution/Analytic/BM97/LedgerSequence.lean`) this gives the ledger of `σ` at every
point of `M̃` (every point lies in some piece, `toLimit_surjective`), which the Jacobian clause of
the principalization theorem reads pointwise
(`Hironaka/Resolution/Analytic/BM97/JacobianAssembly.lean`).
-/

public section

open Set TopologicalSpace Filter Topology
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

universe u

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M}

/-- **The Jacobian stalk of the glued blow-down on a piece**: the Jacobian stalk of
`σ = C.limitBlowDown Kex hemb hcomp` at a point of the piece `m`, transported along the analytic
open embedding `ι_m = toLimitMap m`, is the Jacobian stalk of the piece's composite `σ^{(m)}` —
`σ ∘ ι_m = Π^{(m)} = inclusion ∘ σ^{(m)}` (`limitDesc_comp_toLimitMap` and the definition of
`blowDownOn`), and the chain rule keeps the piece's stalk because `ι_m` and the inclusion are
local diffeomorphisms, with Jacobian stalk `⊤` (the two corollaries
`jacobianStalk_comp_of_isLocalDiffeomorphAt_right` and `_left` of the chain rule). The gluing of
the local principalizations is [Wlo09, §4.1]. -/
theorem CompatibleFamily.jacobianStalk_limitBlowDown_toLimitMap (C : CompatibleFamily T)
    (Kex : CompactExhaustion M)
    (hemb : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂),
      IsAnalyticOpenEmbedding (C.endResultEmbedding hU₁ hU₂ h))
    (hcomp : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂)
      (p : (C.seqOn U₁ hU₁).stage (Fin.last _)),
      (C.seqOn U₂ hU₂).toSuccession.composite (C.endResultEmbedding hU₁ hU₂ h p) =
        M.restrictLE h ((C.seqOn U₁ hU₁).toSuccession.composite p))
    (m : ℕ) (q : C.endResultOn Kex m) :
    Ideal.map (germMap ((C.endResultChain Kex hemb).toLimitMap m)
        ((C.endResultChain Kex hemb).toLimitMap m).contMDiff q)
        (jacobianStalk (𝕜 := 𝕜) (E := E) (C.limitBlowDown Kex hemb hcomp)
          ((C.endResultChain Kex hemb).toLimitMap m q)) =
      jacobianStalk (𝕜 := 𝕜) (E := E)
        (C.seqOn (relCompactOpen Kex m)
          (isCompact_closure_relCompactOpen Kex m)).toSuccession.composite q := by
  have hloc : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω ((C.endResultChain Kex hemb).toLimitMap m) q :=
    ((C.endResultChain Kex hemb).isAnalyticOpenEmbedding_toLimitMap m).1 q
  -- the chain rule along the open embedding `ι_m` (a local diffeomorphism): its Jacobian is `⊤`
  have hr := jacobianStalk_comp_of_isLocalDiffeomorphAt_right
    ((C.endResultChain Kex hemb).toLimitMap m).contMDiff (C.limitBlowDown Kex hemb hcomp).contMDiff
    q hloc
  -- `σ ∘ ι_m = Π^{(m)}`, the blow-down of the piece read in `M` (`limitDesc`)
  have h1 : (C.limitBlowDown Kex hemb hcomp).comp ((C.endResultChain Kex hemb).toLimitMap m) =
      C.blowDownOn Kex m :=
    (C.endResultChain Kex hemb).limitDesc_comp_toLimitMap (C.blowDownOn Kex)
      (C.blowDownOn_endResultEmbedding Kex hemb hcomp) m
  have hfun : (⇑(C.limitBlowDown Kex hemb hcomp) ∘ ⇑((C.endResultChain Kex hemb).toLimitMap m) :
      (C.endResultChain Kex hemb).X m → M) = ⇑(C.blowDownOn Kex m) :=
    congrArg DFunLike.coe h1
  -- `Π^{(m)} = inclusion ∘ σ^{(m)}`, and the inclusion is a local diffeomorphism
  have hl : jacobianStalk (𝕜 := 𝕜) (E := E) ⇑(C.blowDownOn Kex m) q =
      jacobianStalk (𝕜 := 𝕜) (E := E)
        ⇑(C.seqOn (relCompactOpen Kex m)
          (isCompact_closure_relCompactOpen Kex m)).toSuccession.composite q :=
    jacobianStalk_comp_of_isLocalDiffeomorphAt_left
      (C.seqOn (relCompactOpen Kex m)
        (isCompact_closure_relCompactOpen Kex m)).toSuccession.composite.contMDiff
      (M.inclusion (relCompactOpen Kex m)).contMDiff q
      (isLocalDiffeomorph_inclusion M (relCompactOpen Kex m) _)
  exact hr.symm.trans ((congrArg (fun φ : (C.endResultChain Kex hemb).X m → M =>
    jacobianStalk (𝕜 := 𝕜) (E := E) φ q) hfun).trans hl)

end Hironaka.Manifold
