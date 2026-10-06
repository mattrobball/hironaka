/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BD
public import Hironaka.Manifold.FiniteSuccession.Functor.PushforwardPullback
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The core over a sequence under pull-back and under deletion of empty blow-ups

Three general facts about the core over a sequence `coreOfListOf` (`BDFamTransport.lean`), the
core of Lemma 102 over an arbitrary sequence of centres on the transform of `E^j`:

* `coreOfListOf_pullback_eraseEmpty` — it pulls back along a local analytic isomorphism to the core
  over the pulled-back sequence on the pulled-back data, up to the deletion of empty blow-ups (the
  functoriality of the construction, the proof of [Kol07, Lemma 102 (2)]; the deletion of empty
  blow-ups commutes with pull-back, `BlowUpSequence.eraseEmpty_pullback_eraseEmpty`, and so does the
  push-forward, `BlowUpSequence.pushforward_pullback`);
* `coreOfListOf_eraseEmpty` — it does not see the empty blow-ups of the sequence
  (`BlowUpSequence.eraseEmpty_pushforward_eraseEmpty`);
* `coreOfListOf_congr` — it depends only on the sets of the centre and of the transform, the
  transform being given as the preimage of a fixed hypersurface under the blowing-up.

These carry the compatibility and the commutation clauses of `BDanFam` (`BDFamCompat.lean`,
`BDFamComm.lean`).
-/

public section

universe u

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace BDan

open _root_.Manifold

variable {M N : AnalyticManifold.{u} 𝕜 E} {Z : Set M}
  (hZ : IsClosedSubmanifold ψ₀ Z 1) {S' : Set (Manifold.blowUp ψ₀ hZ)}
      (hS' : IsClosedSubmanifold ψ₀ S' 1)
  (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin
      (n - 1) → 𝕜)) hS'.toAnalyticManifold)

/-- The pull-back of the core over a sequence along a local analytic isomorphism `ρ`, with its
empty blow-ups deleted, is the core over the sequence pulled back along the restricted lift of `ρ`
to the transforms, on the pulled-back centre and transform (the functoriality in the proof of
[Kol07, Lemma 102 (2)]). -/
theorem coreOfListOf_pullback_eraseEmpty (ρ : AnalyticMap N M)
    (hρ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ) :
    ((coreOfListOf hZ hS' L).pullback ρ hρ).eraseEmpty =
      coreOfListOf (hZ.preimage_of_isLocalDiffeomorph hρ)
        (hS'.preimage_of_isLocalDiffeomorph
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep ρ hρ hZ))
        (L.pullback
          ((hS'.preimage_of_isLocalDiffeomorph
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep ρ hρ hZ)).restrictMap hS'
            (AnalyticManifold.BlowUpSequence.liftStep ρ hρ hZ)
                (AnalyticManifold.BlowUpSequence.liftStep ρ hρ hZ).contMDiff fun _ hx => hx)
          (IsClosedSubmanifold.isLocalDiffeomorph_restrictMap
              (AnalyticManifold.BlowUpSequence.liftStep ρ hρ hZ)
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep ρ hρ hZ) hS')) := by
  unfold coreOfListOf
  rw [AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
      AnalyticManifold.BlowUpSequence.pullback_cons,
    AnalyticManifold.BlowUpSequence.pushforward_pullback]

/-- The core over a sequence does not see the empty blow-ups of the sequence: deleting them commutes
with the push-forward (`BlowUpSequence.eraseEmpty_pushforward_eraseEmpty`). -/
theorem coreOfListOf_eraseEmpty : coreOfListOf hZ hS' L.eraseEmpty = coreOfListOf hZ hS' L := by
  unfold coreOfListOf
  rw [AnalyticManifold.BlowUpSequence.eraseEmpty_cons,
      AnalyticManifold.BlowUpSequence.eraseEmpty_cons,
    AnalyticManifold.BlowUpSequence.eraseEmpty_pushforward_eraseEmpty]

/-- The core over a sequence depends only on the sets of the centre and of the transform (given as
the preimage of a fixed hypersurface `H` under the blowing-up) and on the sequence. -/
theorem coreOfListOf_congr {C H : Set M} {Z₁ Z₂ : Set M} (hZ₁ : IsClosedSubmanifold ψ₀ Z₁ 1)
    (hZ₂ : IsClosedSubmanifold ψ₀ Z₂ 1) {S₁ : Set (Manifold.blowUp ψ₀ hZ₁)} {S₂ : Set
        (Manifold.blowUp ψ₀ hZ₂)}
    (hS₁ : IsClosedSubmanifold ψ₀ S₁ 1) (hS₂ : IsClosedSubmanifold ψ₀ S₂ 1)
    (hZeq₁ : Z₁ = C) (hZeq₂ : Z₂ = C) (hSeq₁ : S₁ = ⇑(Manifold.blowUpπ ψ₀ hZ₁) ⁻¹' H)
    (hSeq₂ : S₂ = ⇑(Manifold.blowUpπ ψ₀ hZ₂) ⁻¹' H)
    (L₁ : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin
        (n - 1) → 𝕜)) hS₁.toAnalyticManifold)
    (L₂ : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin
        (n - 1) → 𝕜)) hS₂.toAnalyticManifold)
    (hL : HEq L₁ L₂) : coreOfListOf hZ₁ hS₁ L₁ = coreOfListOf hZ₂ hS₂ L₂ := by
  subst hZeq₁
  subst hZeq₂
  subst hSeq₁
  subst hSeq₂
  cases hL
  rfl

/-- Pull-backs of a sequence along maps out of the bundled closed submanifolds of two equal sets,
agreeing pointwise, are equal (as heterogeneous equality, the two domains being equal only
propositionally). -/
theorem heq_pullback_of_heq_bundled {X : AnalyticManifold.{u} 𝕜 E} {c : ℕ}
    {A : AnalyticManifold.{u} 𝕜 (Fin (n - c) → 𝕜)} {S₁ S₂ : Set X} (e : S₁ = S₂)
    (h₁ : IsClosedSubmanifold ψ₀ S₁ c) (h₂ : IsClosedSubmanifold ψ₀ S₂ c)
    (Z : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - c) → 𝕜)) A)
    (f₁ : AnalyticMap h₁.toAnalyticManifold A) (f₂ : AnalyticMap h₂.toAnalyticManifold A)
    (hf₁ : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - c) → 𝕜) 𝓘(𝕜, Fin (n - c) → 𝕜) ω f₁)
    (hf₂ : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - c) → 𝕜) 𝓘(𝕜, Fin (n - c) → 𝕜) ω f₂)
    (hf : ∀ (x : X) (hx₁ : x ∈ S₁) (hx₂ : x ∈ S₂), f₁ ⟨x, hx₁⟩ = f₂ ⟨x, hx₂⟩) :
    HEq (Z.pullback f₁ hf₁) (Z.pullback f₂ hf₂) := by
  subst e
  have hfe : f₁ = f₂ := ContMDiffMap.ext fun p => hf p.1 p.2 p.2
  subst hfe
  rfl

/-- The core over a sequence does not see the empty blow-ups of the sequence when two pull-backs are
interposed (the two-step form of `coreOfListOf_eraseEmpty`). -/
theorem coreOfListOf_pullback_pullback_eraseEmpty
    {A B : AnalyticManifold.{u} 𝕜 (Fin (n - 1) → 𝕜)}
    (X : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) A)
        (a : AnalyticMap B A)
    (ha : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω a)
    (b : AnalyticMap hS'.toAnalyticManifold B)
    (hb : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω b) :
    coreOfListOf hZ hS' ((X.eraseEmpty.pullback a ha).pullback b hb) =
      coreOfListOf hZ hS' ((X.pullback a ha).pullback b hb) := by
  rw [AnalyticManifold.BlowUpSequence.pullback_comp, AnalyticManifold.BlowUpSequence.pullback_comp,
    ← coreOfListOf_eraseEmpty hZ hS' (X.eraseEmpty.pullback (a.comp b) _),
    AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty, coreOfListOf_eraseEmpty]

end BDan

end Hironaka.Manifold
