/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.DirectLimit.Cocone
public import Hironaka.Resolution.Analytic.Functor.EndResultEmbedding
public import Hironaka.Manifold.Exhaustion
public import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The direct limit of a compatible family

From a compatible family `C : CompatibleFamily T` and a compact exhaustion `Kex` of `M`, the
extension-compatible family `AnalyticManifold.ExtensionCompatibleFamily M` of the main
theorems ([Wlo09, Theorem 2.0.3, (1) and (4)]; [Wlo09, §4.1]; [Kol07, 44]; [BM97, §1] on
non-compact analytic spaces): the end results `M'_n` of the values on the relatively compact opens
`M_n = relCompactOpen Kex n` form an `ℕ`-chain along the end-result embeddings
(`CompatibleFamily.endResultChain`), whose direct limit is the space `M̃`
(`CompatibleFamily.endResultLimit`); the composite blow-downs `M'_n → M_n ⊆ M` glue to
`σ : M̃ → M` (`CompatibleFamily.limitBlowDown`, Włodarczyk's `prin : M̃ → M`) with
`σ⁻¹(M_n) = M'_n` (`CompatibleFamily.limitBlowDown_preimage_relCompactOpen`); and the fields of
the extension-compatible family follow one by one (`ExtensionCompatibleFamily.ofCompatibleFamily`):
`nhd K` is the first `M_n ⊇ K` (`relCompactOpenIndex`, monotone in `K` by `Nat.find_mono`),
`seq K` the family's value on it, `toSpace K` the inclusion of the piece `M'_n` into the limit,
`map_toSpace` the glued square, `toSpace_isIso` (`U_r = Ũ` in [Wlo09, Theorem 2.0.3, (1)]) from
`σ⁻¹(M_n) = M'_n`, and `isExtensionOf_restrict` the extension clause at `U₁ := nhd K₁`,
`U₂ := nhd K₂`.

The four properties of the end-result embeddings (analytic open embeddings, over `M`, onto the
preimage of the smaller open, and the restriction an extension) enter every declaration below as
the hypotheses `hemb`, `hcomp`, `hrange`, `hext`; they are proved in
`Hironaka.Resolution.Analytic.Functor.EndResultEmbeddingLemmas`, which this module does not
import, and supplied where the family is built as `resolveFamExt`
(`Hironaka.Resolution.Analytic.Wlo09.FamilyExt`).

* `exists_subset_relCompactOpen`, `relCompactOpenIndex`, `subset_relCompactOpen_index`,
  `relCompactOpenIndex_mono`: the first `M_n` containing a compact set.
* `CompatibleFamily.endResultOn`, `CompatibleFamily.endResultChain`, `CompatibleFamily.blowDownOn`,
  `CompatibleFamily.blowDownOn_endResultEmbedding`, `CompatibleFamily.range_endResultChain_ι`.
* `CompatibleFamily.endResultLimit`, `CompatibleFamily.limitBlowDown`,
  `CompatibleFamily.limitBlowDown_preimage_relCompactOpen`.
* `ExtensionCompatibleFamily.ofCompatibleFamily`.
-/

@[expose] public noncomputable section

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

/-! ### The first relatively compact open of the exhaustion containing a compact set -/

section ExhaustionIndex

variable {X : Type*} [TopologicalSpace X] (Kex : CompactExhaustion X)

/-- Every compact set lies in some `M_n = relCompactOpen Kex n`
(`CompactExhaustion.exists_superset_of_isCompact`, `K n ⊆ int K (n+1)`). -/
theorem exists_subset_relCompactOpen (K : Compacts X) :
    ∃ n, (K : Set X) ⊆ relCompactOpen Kex n := by
  obtain ⟨n, hn⟩ := Kex.exists_superset_of_isCompact K.isCompact
  exact ⟨n, hn.trans (Kex.subset_interior_succ n)⟩

open Classical in
/-- The first index `n` with
`K ⊆ M_n`. -/
def relCompactOpenIndex (K : Compacts X) : ℕ := Nat.find (exists_subset_relCompactOpen Kex K)

open Classical in
/-- `K ⊆ M_{relCompactOpenIndex K}` (`subset_nhd`). -/
theorem subset_relCompactOpen_index (K : Compacts X) :
    (K : Set X) ⊆ relCompactOpen Kex (relCompactOpenIndex Kex K) :=
  Nat.find_spec (exists_subset_relCompactOpen Kex K)

open Classical in
/-- The index is monotone in `K` (`nhd_mono`; [Wlo09, Theorem 2.0.3, (4)], for opens `U₁ ⊂ U₂`). -/
theorem relCompactOpenIndex_mono : Monotone (relCompactOpenIndex Kex) := fun K₁ K₂ h =>
  Nat.find_mono (p := fun m => (K₁ : Set X) ⊆ relCompactOpen Kex m)
    (q := fun m => (K₂ : Set X) ⊆ relCompactOpen Kex m)
    (fun _ hn => (SetLike.coe_subset_coe.mpr h).trans hn)
    (hp := exists_subset_relCompactOpen Kex K₁) (hq := exists_subset_relCompactOpen Kex K₂)

end ExhaustionIndex

/-! ### The end results of a compatible family along the exhaustion, as a chain -/

section Bridge

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M}
  (C : CompatibleFamily T) (Kex : CompactExhaustion M)

/-- The end result `M'_m` of the family's value on `M_m = relCompactOpen Kex m`
(relatively compact). -/
abbrev CompatibleFamily.endResultOn (m : ℕ) : AnalyticManifold.{u} 𝕜 E :=
  (C.seqOn (relCompactOpen Kex m) (isCompact_closure_relCompactOpen Kex m)).stage (Fin.last _)

/-- The end results along the exhaustion
`M_0 ⊆ M_1 ⊆ ⋯`, with embeddings as the transition maps, as an `ℕ`-chain of analytic open
embeddings — given `isAnalyticOpenEmbedding_endResultEmbedding` as `hemb`. -/
def CompatibleFamily.endResultChain
    (hemb : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂),
      IsAnalyticOpenEmbedding (C.endResultEmbedding hU₁ hU₂ h)) : OpenEmbeddingChain 𝕜 E where
  X m := C.endResultOn Kex m
  ι m := C.endResultEmbedding (isCompact_closure_relCompactOpen Kex m)
    (isCompact_closure_relCompactOpen Kex (m + 1)) (relCompactOpen_le_succ Kex m)
  isAnalyticOpenEmbedding _ := hemb _ _ _ _ _

/-- The composite blow-down `Π^{(m)} : M'_m → M_m ⊆ M` of the end result over
`M_m`, read in `M`. -/
def CompatibleFamily.blowDownOn (m : ℕ) : AnalyticMap (C.endResultOn Kex m) M :=
  (M.inclusion (relCompactOpen Kex m)).comp
    (C.seqOn (relCompactOpen Kex m) (isCompact_closure_relCompactOpen Kex m)).toSuccession.composite

/-- The blow-downs are compatible with the embeddings:
`composite_endResultEmbedding` (`hcomp`) read in `M`, where the inclusion `M_m ⊆ M_{m+1}`
disappears. -/
theorem CompatibleFamily.blowDownOn_endResultEmbedding
    (hemb : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂),
      IsAnalyticOpenEmbedding (C.endResultEmbedding hU₁ hU₂ h))
    (hcomp : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂)
      (p : (C.seqOn U₁ hU₁).stage (Fin.last _)),
      (C.seqOn U₂ hU₂).toSuccession.composite (C.endResultEmbedding hU₁ hU₂ h p) =
        M.restrictLE h ((C.seqOn U₁ hU₁).toSuccession.composite p))
    (m : ℕ) (x : (C.endResultChain Kex hemb).X m) :
    C.blowDownOn Kex (m + 1) ((C.endResultChain Kex hemb).ι m x) = C.blowDownOn Kex m x :=
  congrArg (M.inclusion (relCompactOpen Kex (m + 1))) (hcomp _ _ _ _ _ x)

/-- The range of the embedding `M'_m → M'_{m+1}` is the preimage of `M_m` under the
blow-down of `M'_{m+1}` — `range_endResultEmbedding` (`hrange`) with
`range_restrictLE`. -/
theorem CompatibleFamily.range_endResultChain_ι
    (hemb : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂),
      IsAnalyticOpenEmbedding (C.endResultEmbedding hU₁ hU₂ h))
    (hrange : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂),
      Set.range (C.endResultEmbedding hU₁ hU₂ h) =
        (C.seqOn U₂ hU₂).toSuccession.composite ⁻¹' Set.range (M.restrictLE h))
    (m : ℕ) :
    Set.range ((C.endResultChain Kex hemb).ι m) =
      C.blowDownOn Kex (m + 1) ⁻¹' (relCompactOpen Kex m : Set M) :=
  (hrange _ _ _ _ _).trans (congrArg (Set.preimage _) (range_restrictLE _))

/-- The
direct limit `M̃ = ⋃ₙ M'_n` of the end results. -/
def CompatibleFamily.endResultLimit
    (hemb : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂),
      IsAnalyticOpenEmbedding (C.endResultEmbedding hU₁ hU₂ h)) : AnalyticManifold.{u} 𝕜 E :=
  (C.endResultChain Kex hemb).limitManifold

/-- The blow-down `σ : M̃ → M`
of the direct limit, the `Π^{(m)}` glued. -/
def CompatibleFamily.limitBlowDown
    (hemb : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂),
      IsAnalyticOpenEmbedding (C.endResultEmbedding hU₁ hU₂ h))
    (hcomp : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂)
      (p : (C.seqOn U₁ hU₁).stage (Fin.last _)),
      (C.seqOn U₂ hU₂).toSuccession.composite (C.endResultEmbedding hU₁ hU₂ h p) =
        M.restrictLE h ((C.seqOn U₁ hU₁).toSuccession.composite p)) :
    AnalyticMap (C.endResultLimit Kex hemb) M :=
  (C.endResultChain Kex hemb).limitDesc (C.blowDownOn Kex)
    (C.blowDownOn_endResultEmbedding Kex hemb hcomp)

/-- `σ⁻¹(M_m)` is the `m`-th piece `M'_m` of the limit. -/
theorem CompatibleFamily.limitBlowDown_preimage_relCompactOpen
    (hemb : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂),
      IsAnalyticOpenEmbedding (C.endResultEmbedding hU₁ hU₂ h))
    (hcomp : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂)
      (p : (C.seqOn U₁ hU₁).stage (Fin.last _)),
      (C.seqOn U₂ hU₂).toSuccession.composite (C.endResultEmbedding hU₁ hU₂ h p) =
        M.restrictLE h ((C.seqOn U₁ hU₁).toSuccession.composite p))
    (hrange : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂),
      Set.range (C.endResultEmbedding hU₁ hU₂ h) =
        (C.seqOn U₂ hU₂).toSuccession.composite ⁻¹' Set.range (M.restrictLE h))
    (m : ℕ) :
    C.limitBlowDown Kex hemb hcomp ⁻¹' (relCompactOpen Kex m : Set M) =
      Set.range ((C.endResultChain Kex hemb).toLimitMap m) :=
  (C.endResultChain Kex hemb).preimage_limitDesc_eq_range_toLimitMap (C.blowDownOn Kex)
    (C.blowDownOn_endResultEmbedding Kex hemb hcomp) (fun m => (relCompactOpen Kex m : Set M))
    (fun m _ hx => relCompactOpen_le_succ Kex m hx) (C.range_endResultChain_ι Kex hemb hrange) m

/-- The extension-compatible family `ExtensionCompatibleFamily M` from a compatible family and a
compact exhaustion: the space is the direct limit of the end results, the map its blow-down, the
neighbourhood of a compact `K` the first `M_n ⊇ K`, the succession over it the family's value
there, the identification of the end result with `σ⁻¹(M_n)` the inclusion of the piece, and the
extension clause that of the end-result embeddings. The four properties of the end-result
embeddings are the hypotheses `hemb`, `hcomp`, `hrange`, `hext` (see the module docstring). -/
def _root_.AnalyticManifold.ExtensionCompatibleFamily.ofCompatibleFamily
    (hemb : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂),
      IsAnalyticOpenEmbedding (C.endResultEmbedding hU₁ hU₂ h))
    (hcomp : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂)
      (p : (C.seqOn U₁ hU₁).stage (Fin.last _)),
      (C.seqOn U₂ hU₂).toSuccession.composite (C.endResultEmbedding hU₁ hU₂ h p) =
        M.restrictLE h ((C.seqOn U₁ hU₁).toSuccession.composite p))
    (hrange : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂),
      Set.range (C.endResultEmbedding hU₁ hU₂ h) =
        (C.seqOn U₂ hU₂).toSuccession.composite ⁻¹' Set.range (M.restrictLE h))
    (hext : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂),
      ((C.seqOn U₂ hU₂).toSuccession.restrict h).IsExtensionOf (C.seqOn U₁ hU₁).toSuccession) :
    ExtensionCompatibleFamily M where
  space := C.endResultLimit Kex hemb
  map := C.limitBlowDown Kex hemb hcomp
  nhd K := relCompactOpen Kex (relCompactOpenIndex Kex K)
  subset_nhd K := subset_relCompactOpen_index Kex K
  nhd_mono := fun _ _ h => relCompactOpen_mono Kex (relCompactOpenIndex_mono Kex h)
  seq K := (C.seqOn (relCompactOpen Kex (relCompactOpenIndex Kex K))
    (isCompact_closure_relCompactOpen Kex _)).toSuccession
  toSpace K := (C.endResultChain Kex hemb).toLimitMap (relCompactOpenIndex Kex K)
  map_toSpace _ := (C.endResultChain Kex hemb).limitDesc_comp_toLimitMap _ _ _
  toSpace_isIso _ :=
    (C.endResultChain Kex hemb).isAnalyticIsoOver_toLimitMap_limitDesc (C.blowDownOn Kex)
      (C.blowDownOn_endResultEmbedding Kex hemb hcomp) (fun m => (relCompactOpen Kex m : Set M))
      (fun m _ hx => relCompactOpen_le_succ Kex m hx) (C.range_endResultChain_ι Kex hemb hrange) _
  isExtensionOf_restrict _ _ _ := hext _ _ _ _ _

end Bridge

end Hironaka.Manifold
