/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Defs

/-!
# The pull-back and push-forward of successions with the morphism spelled out

The relations `FiniteSuccession.IsPullbackUpToEmptyAlong` and
`FiniteSuccession.IsPushforwardUpToEmptyAlong` assert a morphism of successions
(`FiniteSuccession.Hom`) with conditions on its maps and on the centres. This module restates them
with the index map and the maps between the stages as separate witnesses
(`isPullbackUpToEmptyAlong_iff`, `isPushforwardUpToEmptyAlong_iff`), the form in which they are
constructed and taken apart.
-/

@[expose] public section

universe u

open scoped Manifold ContDiff
open TopologicalSpace

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- `IsPullbackUpToEmptyAlong` with the morphism of successions spelled out: an index map and
local analytic isomorphisms between the stages with the conditions of `FiniteSuccession.Hom`. -/
theorem isPullbackUpToEmptyAlong_iff {M N : AnalyticManifold.{u} 𝕜 E} {U : Opens M}
    {U' : Opens N} {R : FiniteSuccession (N.restrict U')} {S : FiniteSuccession (M.restrict U)}
    {g : AnalyticMap N M} :
    R.IsPullbackUpToEmptyAlong S g ↔
      ∃ (blk : Fin (S.length + 1) → Fin (R.length + 1))
        (f : ∀ k, AnalyticMap (R.stage (blk k)) (S.stage k)),
        blk 0 = 0 ∧ blk (Fin.last _) = Fin.last _ ∧
        (∀ k : Fin S.length,
          (blk k.succ : ℕ) = blk k.castSucc ∨ (blk k.succ : ℕ) = blk k.castSucc + 1) ∧
        (∀ k, IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (f k)) ∧
        (∀ k p, M.inclusion U (S.stageMap k (f k p)) = g (N.inclusion U' (R.stageMap (blk k) p))) ∧
        (∀ (k : Fin S.length) (hle : blk k.castSucc ≤ blk k.succ) (p : R.stage (blk k.succ)),
          S.map k (f k.succ p) = f k.castSucc (R.stageMapLE hle p)) ∧
        (∀ (k : Fin S.length) (ha : (blk k.castSucc : ℕ) < R.length),
          (blk k.succ : ℕ) = blk k.castSucc + 1 →
            R.centerAt (blk k.castSucc) ha =
              (S.center k).pullback (f k.castSucc) (f k.castSucc).contMDiff) ∧
        (∀ k : Fin S.length, (blk k.succ : ℕ) = blk k.castSucc →
          ((S.center k).pullback (f k.castSucc) (f k.castSucc).contMDiff).support = ∅) :=
  ⟨fun ⟨⟨blk, f, h0, hl, hs, hov, hm⟩, hld, hcj, hcn⟩ =>
      ⟨blk, f, h0, hl, hs, hld, hov, hm, hcj, hcn⟩,
    fun ⟨blk, f, h0, hl, hs, hld, hov, hm, hcj, hcn⟩ =>
      ⟨⟨blk, f, h0, hl, hs, hov, hm⟩, hld, hcj, hcn⟩⟩

/-- `IsPushforwardUpToEmptyAlong` with the morphism of successions spelled out: an index map and
embeddings between the stages with the conditions of `FiniteSuccession.Hom`. -/
theorem isPushforwardUpToEmptyAlong_iff {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {M : AnalyticManifold.{u} 𝕜 E} {N : AnalyticManifold.{u} 𝕜 E'} {U : Opens M} {U' : Opens N}
    {S : FiniteSuccession (M.restrict U)} {R : FiniteSuccession (N.restrict U')}
    {τ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, E), M⟯} :
    S.IsPushforwardUpToEmptyAlong R τ ↔
      ∃ (blk : Fin (S.length + 1) → Fin (R.length + 1))
        (f : ∀ k, C^ω⟮𝓘(𝕜, E'), R.stage (blk k); 𝓘(𝕜, E), S.stage k⟯),
        blk 0 = 0 ∧ blk (Fin.last _) = Fin.last _ ∧
        (∀ k : Fin S.length,
          (blk k.succ : ℕ) = blk k.castSucc ∨ (blk k.succ : ℕ) = blk k.castSucc + 1) ∧
        (∀ k, Topology.IsEmbedding (f k)) ∧
        (∀ k (q : S.stage k), q ∈ closure (Set.range (f k)) →
          M.inclusion U (S.stageMap k q) ∈ ⇑τ '' (U' : Set N) → q ∈ Set.range (f k)) ∧
        (∀ k p, M.inclusion U (S.stageMap k (f k p)) = τ (N.inclusion U' (R.stageMap (blk k) p))) ∧
        (∀ (k : Fin S.length) (hle : blk k.castSucc ≤ blk k.succ) (p : R.stage (blk k.succ)),
          S.map k (f k.succ p) = f k.castSucc (R.stageMapLE hle p)) ∧
        (∀ (k : Fin S.length) (ha : (blk k.castSucc : ℕ) < R.length),
          (blk k.succ : ℕ) = blk k.castSucc + 1 →
            ⇑(f k.castSucc) ⁻¹' (S.center k).support = (R.centerAt (blk k.castSucc) ha).support) ∧
        (∀ k : Fin S.length, (blk k.succ : ℕ) = blk k.castSucc →
          ⇑(f k.castSucc) ⁻¹' (S.center k).support = ∅) ∧
        (∀ (k : Fin S.length) (q : S.stage k.castSucc), q ∈ (S.center k).support →
          M.inclusion U (S.stageMap k.castSucc q) ∈ ⇑τ '' (U' : Set N) →
            q ∈ Set.range (f k.castSucc)) :=
  ⟨fun ⟨⟨blk, f, h0, hl, hs, hov, hm⟩, he, hcl, hcj, hcn, hc⟩ =>
      ⟨blk, f, h0, hl, hs, he, hcl, hov, hm, hcj, hcn, hc⟩,
    fun ⟨blk, f, h0, hl, hs, he, hcl, hov, hm, hcj, hcn, hc⟩ =>
      ⟨⟨blk, f, h0, hl, hs, hov, hm⟩, he, hcl, hcj, hcn, hc⟩⟩

end AnalyticManifold.FiniteSuccession
