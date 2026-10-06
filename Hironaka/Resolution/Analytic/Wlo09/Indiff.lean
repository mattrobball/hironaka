/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.Rounds
import Hironaka.Resolution.Analytic.OrderReduction.Step21Indiff
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The rounds are indifferent to empty boundary members

Two triples with the same ideal sheaf whose boundary families differ by empty members only (an order
embedding of the indices matching the members, the members off its range empty) have the same
rounds, an exact equality of lists (`resolveFrom_indiff`). This is the empty blow-up convention
[Kol07, 32] on the side of the boundary: empty members of the boundary family carry no information,
and the order-reduction functors ignore them (the field `indifferentToEmptyMembers` of `BOanFam`).
Each round's list agrees by that field, and the derived triples differ by empty members again: the
exceptional members are added identically to both boundary families, and the index correspondence
`corrIdx` of the total transforms (`Hironaka/Resolution/Analytic/OrderReduction/Step21Indiff.lean`)
is the order embedding of the next round. The induction unfolds `resolveFrom` at the successor case
only; its step is `resolveFrom_indiff_step`, with the two round lists abstracted so that their
equality can be substituted, and the congruence `resolveFrom_congr_triple` along an equality of
triples. `Hironaka/Resolution/Analytic/Wlo09/Transport.lean` and
`Hironaka/Resolution/Analytic/Wlo09/TopRound.lean` use it to remove the empty members that the
erasure of empty blow-ups creates in a boundary family.
-/

public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)

/-- The rounds depend on the triple only up to equality (its proofs are irrelevant): a congruence
along an equality of triples. -/
theorem resolveFrom_congr_triple (d : ℕ) {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    {cur₁ cur₂ : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X} (e : cur₁ = cur₂)
    (hord₁ : ∀ x, cur₁.I.ord x ≤ (d : ℕ∞)) (hfin₁ : Finite {j // cur₁.F.hyp j ≠ ∅})
    (hord₂ : ∀ x, cur₂.I.ord x ≤ (d : ℕ∞)) (hfin₂ : Finite {j // cur₂.F.hyp j ≠ ∅})
    (Ω : ℕ → Opens X) (hΩ : ∀ k, k < d → IsCompact (closure (Ω k : Set X)))
    (hΩsub : ∀ k, k + 1 < d → closure (Ω k : Set X) ⊆ Ω (k + 1))
    {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (ι : AnalyticMap N X)
    (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι) (hrange : Set.range ι ⊆ Ω 0) :
    resolveFrom bo d cur₁ hord₁ hfin₁ Ω hΩ hΩsub ι hι hrange =
      resolveFrom bo d cur₂ hord₂ hfin₂ Ω hΩ hΩsub ι hι hrange := by
  subst e
  rfl

/-- The successor step of `resolveFrom_indiff` with the two round lists abstracted, so that their
equality (the field `indifferentToEmptyMembers`) can be substituted: the second factors agree by
the induction hypothesis at the derived triples, whose boundary families correspond along the index
correspondence `corrIdx` of the total transforms (the exceptional members added to both sides). -/
theorem resolveFrom_indiff_step (d : ℕ) {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (cur : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    (F' : HypersurfaceFamily X) (hsnc' : F'.IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
    (e : F'.ι ↪o cur.F.ι) (hhyp : ∀ i, cur.F.hyp (e i) = F'.hyp i)
    (hempty : ∀ b, b ∉ Set.range e → cur.F.hyp b = ∅)
    (ih : ∀ {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
      (cur : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
      (F' : HypersurfaceFamily X) (hsnc' : F'.IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
      (e : F'.ι ↪o cur.F.ι), (∀ i, cur.F.hyp (e i) = F'.hyp i) →
      (∀ b, b ∉ Set.range e → cur.F.hyp b = ∅) →
      ∀ (hord : ∀ x, cur.I.ord x ≤ (d : ℕ∞)) (hfin : Finite {j // cur.F.hyp j ≠ ∅})
      (hfin' : Finite {j // (⟨cur.I, cur.isNonzeroEverywhere, F', hsnc'⟩ :
        AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X).F.hyp j ≠ ∅})
      (Ω : ℕ → Opens X) (hΩ : ∀ k, k < d → IsCompact (closure (Ω k : Set X)))
      (hΩsub : ∀ k, k + 1 < d → closure (Ω k : Set X) ⊆ Ω (k + 1))
      {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (ι : AnalyticMap N X)
      (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι) (hrange : Set.range ι ⊆ Ω 0),
      resolveFrom bo d cur hord hfin Ω hΩ hΩsub ι hι hrange =
        resolveFrom bo d ⟨cur.I, cur.isNonzeroEverywhere, F', hsnc'⟩ hord hfin' Ω hΩ hΩsub ι hι
          hrange)
    (O : Opens X) (Ω : ℕ → Opens X) {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (ι : AnalyticMap N X)
    (hr : Set.range ι ⊆ O)
    (L₁ L₂ : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (X.restrict O)) (hL : L₁ = L₂)
    (hge₁ : L₁.toSuccession.IsOfOrderGe
      (cur.pullback (X.inclusion O) (isLocalDiffeomorph_inclusion X O)).I (d + 1)
      (cur.pullback (X.inclusion O) (isLocalDiffeomorph_inclusion X O)).F.idealSheaf)
    (hge₂ : L₂.toSuccession.IsOfOrderGe
      ((⟨cur.I, cur.isNonzeroEverywhere, F', hsnc'⟩ :
        AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X).pullback (X.inclusion O)
        (isLocalDiffeomorph_inclusion X O)).I (d + 1)
      ((⟨cur.I, cur.isNonzeroEverywhere, F', hsnc'⟩ :
        AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X).pullback (X.inclusion O)
        (isLocalDiffeomorph_inclusion X O)).F.idealSheaf)
    (h₁ h₂ : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (AnalyticMap.corestrict ι O hr))
    (hord₁ : ∀ x,
        ((cur.pullback (X.inclusion O) (isLocalDiffeomorph_inclusion X O)).induced
        (d + 1) L₁ hge₁).I.ord x ≤ (d : ℕ∞))
    (hfin₁ : Finite {j // ((cur.pullback (X.inclusion O) (isLocalDiffeomorph_inclusion X O)).induced
      (d + 1) L₁ hge₁).F.hyp j ≠ ∅})
    (hΩ₁ : ∀ k, k < d → IsCompact (closure (liftChain L₁ Ω k : Set (L₁.stage (Fin.last _)))))
    (hΩsub₁ : ∀ k, k + 1 < d →
      closure (liftChain L₁ Ω k : Set (L₁.stage (Fin.last _))) ⊆ liftChain L₁ Ω (k + 1))
    (hk₁ : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      (L₁.pullbackLiftLast (AnalyticMap.corestrict ι O hr) h₁))
    (hr₁ : Set.range (L₁.pullbackLiftLast (AnalyticMap.corestrict ι O hr) h₁) ⊆ liftChain L₁ Ω 0)
    (hord₂ : ∀ x,
        (((⟨cur.I, cur.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple
        (ContinuousLinearEquiv.refl 𝕜
        (Fin n → 𝕜)) X).pullback (X.inclusion O) (isLocalDiffeomorph_inclusion X O)).induced
        (d + 1) L₂ hge₂).I.ord x ≤ (d : ℕ∞))
    (hfin₂ : Finite {j // (((⟨cur.I, cur.isNonzeroEverywhere, F', hsnc'⟩ :
      AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X).pullback (X.inclusion O)
      (isLocalDiffeomorph_inclusion X O)).induced (d + 1) L₂ hge₂).F.hyp j ≠ ∅})
    (hΩ₂ : ∀ k, k < d → IsCompact (closure (liftChain L₂ Ω k : Set (L₂.stage (Fin.last _)))))
    (hΩsub₂ : ∀ k, k + 1 < d →
      closure (liftChain L₂ Ω k : Set (L₂.stage (Fin.last _))) ⊆ liftChain L₂ Ω (k + 1))
    (hk₂ : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      (L₂.pullbackLiftLast (AnalyticMap.corestrict ι O hr) h₂))
    (hr₂ : Set.range (L₂.pullbackLiftLast (AnalyticMap.corestrict ι O hr) h₂) ⊆
      liftChain L₂ Ω 0) :
    (L₁.pullback (AnalyticMap.corestrict ι O hr) h₁).concat
      (resolveFrom bo d ((cur.pullback (X.inclusion O) (isLocalDiffeomorph_inclusion X O)).induced
        (d + 1) L₁ hge₁) hord₁ hfin₁ (liftChain L₁ Ω) hΩ₁ hΩsub₁
        (L₁.pullbackLiftLast (AnalyticMap.corestrict ι O hr) h₁) hk₁ hr₁) =
    (L₂.pullback (AnalyticMap.corestrict ι O hr) h₂).concat
      (resolveFrom bo d (((⟨cur.I, cur.isNonzeroEverywhere, F', hsnc'⟩ :
        AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X).pullback (X.inclusion O)
        (isLocalDiffeomorph_inclusion X O)).induced (d + 1) L₂ hge₂) hord₂ hfin₂ (liftChain L₂ Ω)
        hΩ₂ hΩsub₂ (L₂.pullbackLiftLast (AnalyticMap.corestrict ι O hr) h₂) hk₂ hr₂) := by
  subst hL
  -- the members of the restricted families correspond along `e`, and are empty off its range
  have hmem : ∀ j, ((⟨cur.I, cur.isNonzeroEverywhere, F', hsnc'⟩ :
      AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X).pullback (X.inclusion O)
      (isLocalDiffeomorph_inclusion X O)).F.hyp j =
      (cur.pullback (X.inclusion O) (isLocalDiffeomorph_inclusion X O)).F.hyp (e j) := fun j =>
    (congrArg (fun s => ⇑(X.inclusion O) ⁻¹' s) (hhyp j).symm :
      ⇑(X.inclusion O) ⁻¹' F'.hyp j = ⇑(X.inclusion O) ⁻¹' cur.F.hyp (e j))
  have hout : ∀ b, b ∉ Set.range e →
      (cur.pullback (X.inclusion O) (isLocalDiffeomorph_inclusion X O)).F.hyp b = ∅ := fun b hb =>
    (by rw [hempty b hb, Set.preimage_empty] : ⇑(X.inclusion O) ⁻¹' cur.F.hyp b = ∅)
  -- the two induced triples: equal ideals (the same restricted ideal), the boundary of the second
  have hI : (cur.pullback (X.inclusion O) (isLocalDiffeomorph_inclusion X O)).I =
      ((⟨cur.I, cur.isNonzeroEverywhere, F', hsnc'⟩ :
        AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X).pullback (X.inclusion O)
        (isLocalDiffeomorph_inclusion X O)).I := rfl
  have hT : (⟨((cur.pullback (X.inclusion O) (isLocalDiffeomorph_inclusion X O)).induced (d + 1)
        L₁ hge₁).I,
      ((cur.pullback (X.inclusion O) (isLocalDiffeomorph_inclusion X O)).induced (d + 1)
        L₁ hge₁).isNonzeroEverywhere,
      L₁.toSuccession.totalTransformSeqFrom ((⟨cur.I, cur.isNonzeroEverywhere, F', hsnc'⟩ :
        AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X).pullback (X.inclusion O)
        (isLocalDiffeomorph_inclusion X O)).F (Fin.last _),
      (((⟨cur.I, cur.isNonzeroEverywhere, F', hsnc'⟩ :
        AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X).pullback (X.inclusion O)
        (isLocalDiffeomorph_inclusion X O)).induced (d + 1) L₁ hge₂).isSnc⟩ :
        AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (L₁.stage (Fin.last _))) =
      ((⟨cur.I, cur.isNonzeroEverywhere, F', hsnc'⟩ :
        AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X).pullback (X.inclusion O)
        (isLocalDiffeomorph_inclusion X O)).induced (d + 1) L₁ hge₂ :=
    AnalyticTriple.ext'
      (congrArg (fun I => L₁.toSuccession.markedTransformSeq I (d + 1) (Fin.last _)) hI) rfl
  refine congrArg ((L₁.pullback (AnalyticMap.corestrict ι O hr) h₁).concat)
    ((ih ((cur.pullback (X.inclusion O) (isLocalDiffeomorph_inclusion X O)).induced (d + 1) L₁ hge₁)
      (L₁.toSuccession.totalTransformSeqFrom ((⟨cur.I, cur.isNonzeroEverywhere, F', hsnc'⟩ :
        AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X).pullback (X.inclusion O)
        (isLocalDiffeomorph_inclusion X O)).F (Fin.last _))
      (((⟨cur.I, cur.isNonzeroEverywhere, F', hsnc'⟩ :
        AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X).pullback (X.inclusion O)
        (isLocalDiffeomorph_inclusion X O)).induced (d + 1) L₁ hge₂).isSnc
      (L₁.toSuccession.corrIdx
        (F := (cur.pullback (X.inclusion O) (isLocalDiffeomorph_inclusion X O)).F)
        (G := ((⟨cur.I, cur.isNonzeroEverywhere, F', hsnc'⟩ :
          AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X).pullback (X.inclusion O)
          (isLocalDiffeomorph_inclusion X O)).F) e (Fin.last _))
      (fun i => (L₁.toSuccession.hyp_corrIdxAux_of_forall
        (F := (cur.pullback (X.inclusion O) (isLocalDiffeomorph_inclusion X O)).F)
        (G := ((⟨cur.I, cur.isNonzeroEverywhere, F', hsnc'⟩ :
          AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X).pullback (X.inclusion O)
          (isLocalDiffeomorph_inclusion X O)).F) e hmem (Fin.last _) i).symm)
      (fun b hb => L₁.toSuccession.hyp_eq_empty_of_notMem_range_corrIdx
        (F := (cur.pullback (X.inclusion O) (isLocalDiffeomorph_inclusion X O)).F)
        (G := ((⟨cur.I, cur.isNonzeroEverywhere, F', hsnc'⟩ :
          AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X).pullback (X.inclusion O)
          (isLocalDiffeomorph_inclusion X O)).F) e hout (Fin.last _) b hb)
      hord₁ hfin₁ hfin₂ (liftChain L₁ Ω) hΩ₁ hΩsub₁
      (L₁.pullbackLiftLast (AnalyticMap.corestrict ι O hr) h₁) hk₁ hr₁).trans
      (resolveFrom_congr_triple bo d hT hord₁ hfin₂ hord₂ hfin₂ (liftChain L₁ Ω) hΩ₁ hΩsub₁
        (L₁.pullbackLiftLast (AnalyticMap.corestrict ι O hr) h₁) hk₁ hr₁))

/-- **Indifference to empty boundary members** (the empty blow-up convention [Kol07, 32]). Two
triples with the same ideal sheaf whose boundary families differ by empty members only (an order
embedding
`e` of the indices, the members off its range empty) have the same rounds: each round's value
agrees by the field `indifferentToEmptyMembers`, and the derived triples differ by empty members
again (the exceptional members are added to both). -/
theorem resolveFrom_indiff (d : ℕ) {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (cur : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    (F' : HypersurfaceFamily X) (hsnc' : F'.IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
    (e : F'.ι ↪o cur.F.ι) (hhyp : ∀ i, cur.F.hyp (e i) = F'.hyp i)
    (hempty : ∀ b, b ∉ Set.range e → cur.F.hyp b = ∅)
    (hord : ∀ x, cur.I.ord x ≤ (d : ℕ∞)) (hfin : Finite {j // cur.F.hyp j ≠ ∅})
    (hfin' : Finite {j // (⟨cur.I, cur.isNonzeroEverywhere, F', hsnc'⟩ :
      AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X).F.hyp j ≠ ∅})
    (Ω : ℕ → Opens X) (hΩ : ∀ k, k < d → IsCompact (closure (Ω k : Set X)))
    (hΩsub : ∀ k, k + 1 < d → closure (Ω k : Set X) ⊆ Ω (k + 1))
    {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (ι : AnalyticMap N X)
    (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι) (hrange : Set.range ι ⊆ Ω 0) :
    resolveFrom bo d cur hord hfin Ω hΩ hΩsub ι hι hrange =
      resolveFrom bo d ⟨cur.I, cur.isNonzeroEverywhere, F', hsnc'⟩ hord hfin' Ω hΩ hΩsub ι hι
        hrange := by
  induction d generalizing X N with
  | zero => rw [resolveFrom, resolveFrom]
  | succ d ih =>
    have hL := (bo (d + 1)).indifferentToEmptyMembers cur F' hsnc' e hhyp hempty
      (boClass_succ_of_ord_le cur hord hfin) (boClass_succ_of_ord_le _ hord hfin') (Ω d)
      (hΩ d (Nat.lt_succ_self d))
    rw [resolveFrom, resolveFrom]
    exact resolveFrom_indiff_step bo d cur F' hsnc' e hhyp hempty ih (Ω d) Ω ι
      (range_subset_chain hΩsub hrange) _ _ hL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end Hironaka.Manifold

end
