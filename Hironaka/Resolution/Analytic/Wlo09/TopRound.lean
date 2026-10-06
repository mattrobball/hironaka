/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.Rounds
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
import Hironaka.Resolution.Analytic.OrderReduction.ClassPullback
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.OrderReduction.ValueTransport
import Hironaka.Resolution.Analytic.Wlo09.EmptyRound
import Hironaka.Resolution.Analytic.Wlo09.Indiff
import Hironaka.Resolution.Analytic.Wlo09.Transport
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Dropping an empty top round

Kollár's remark after [Kol07, Theorem 68], that the order reduction does nothing when
`max-ord I < m`, for the rounds of the resolution family
(`Hironaka/Resolution/Analytic/Wlo09/Rounds.lean`): when the order of `cur` is `≤ d` on a low-order
chain `ΩZ` inside the chain `Ω`, containing the reading image, the rounds from `d + 1` along `Ω`,
read through `ι`, agree up to empty blow-ups with the rounds from `d` on the restriction of `cur` to
the outer open `ΩZ d`, along the traced chain, read through the corestricted `ι`
(`eraseEmpty_resolveFrom_succ_eq_restrict`). Canonicity
(`Hironaka/Resolution/Analytic/Wlo09/Canonicity.lean`) uses it to bring an admissible chain of any
length down to the canonical one.

The proof is bookkeeping on the lemmas of `Hironaka/Resolution/Analytic/Wlo09/EmptyRound.lean`,
`Hironaka/Resolution/Analytic/Wlo09/Indiff.lean` and
`Hironaka/Resolution/Analytic/Wlo09/Transport.lean`. The top round `BO_{n,d+1}` at `Ω d` has no
centre over a point of order `≤ d` (the field `isOfOrderGe`), so its list erases to `nil` both on
the reading manifold and over the region `Z' := ΩZ d ∩ Ω d` of the round's open
(`eraseEmpty_pullback_roundList_eq_nil`, twice). Two identifications follow from
`eraseEmptyTransport` with the empty list: `θ`, of the round's last stage over the reading manifold
with the reading manifold itself, and `τ`, of the round's last stage over the region with the
region, both over the identity of the base (`stageMap_last_toAnalyticMap_eraseEmptyTransport`), so
the lifted reading map is the corestricted reading map up to `θ` and `τ` (`eq_of_stageMap_last_eq`,
uniqueness of maps over the blow-down). Along `τ` the derived ideal is the restricted ideal
(`markedTransformSeq_last_pullbackLiftLast`, `markedTransformSeq_last_eraseEmptyTransport`) and the
restricted boundary is an empty subfamily of the derived boundary
(`exists_orderEmbedding_eraseEmptyTransport`), whose empty members `resolveFrom_indiff` removes.
Then `eraseEmpty_resolveFrom_congr` transports three times: from the round's last stage to the last
stage over the region (the exact pull-back along `kZ`, the lift of the region's inclusion), from
that last stage to the region along `τ`, and from the region, an open of the open `Ω d`, to the
restriction of `X` to `ΩZ d` along `restrictMap`. `eraseEmpty_concat_congr` with the empty first
piece on the right assembles the top round and the rest.

The hypotheses `hordZ`, `hfinZ`, `hΩZ'`, `hΩZsub'`, `hrangeZ'` restate `hZord`, `hfin`, `hΩZ`,
`hΩZsub`, `hrangeZ` on the restricted data; they are the data of the right-hand side, which the
caller supplies. The hypothesis `hclosure` (the closure of the reading image inside `ΩZ d`) is used
only through `subset_closure`; `hrZ` gives the same.

* `HypersurfaceFamily.finite_nonempty_comap`: finitely many nonempty members survive an inverse
  image.
* `eraseEmpty_resolveFrom_succ_eq_restrict`: the theorem.
-/

public section

noncomputable section

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Manifold

open Hironaka.Manifold

section Tools

/-- Finitely many nonempty members of a family stay finitely many after an inverse image: an empty
member pulls back to an empty member (the finiteness clause of `BOClass`). -/
theorem HypersurfaceFamily.finite_nonempty_comap {M N : Type u} (F : HypersurfaceFamily M)
    (g : N → M) (hF : Finite {j // F.hyp j ≠ ∅}) : Finite {j // (F.comap g).hyp j ≠ ∅} :=
  Finite.of_injective (fun j : {j // (F.comap g).hyp j ≠ ∅} =>
    (⟨j.1, fun h => j.2 (by change g ⁻¹' F.hyp j.1 = ∅; rw [h, Set.preimage_empty])⟩ :
      {j // F.hyp j ≠ ∅}))
    fun _ _ h => Subtype.ext (Subtype.mk.inj h)

end Tools

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)

/-- **Dropping an empty top round** (the remark after [Kol07, Theorem 68]). If the order is `≤ d` on
the closure of the reading image, the rounds from `d + 1` read through `ι` agree up to empty
blow-ups with the rounds from `d` on the restriction of `cur` to the outer open `ΩZ d` of any
admissible low-order chain `ΩZ` of opens of `X` (compact closures, shrinking, `ΩZ k ≤ Ω k`,
`ord ≤ d` on `ΩZ d`, the reading image in `ΩZ 0`), read through the corestricted `ι`. Proof:
`eraseEmpty_pullback_roundList_eq_nil` empties the top round over the reading image and over the
region `ΩZ d ∩ Ω d` of the round's open; the derived triple over the region is the restricted
triple up to the transport `τ` along the empty erasure (the derived ideal by
`markedTransformSeq_last_eraseEmptyTransport`, the restricted boundary an empty subfamily of the
derived one, whose empty members `resolveFrom_indiff` removes); `eraseEmpty_resolveFrom_congr`
transports three times (to the last stage over the region, along `τ`, and from the open of an open
to `X.restrict (ΩZ d)`). -/
theorem _root_.Hironaka.Manifold.eraseEmpty_resolveFrom_succ_eq_restrict (d : ℕ)
    {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (cur : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    (hord : ∀ x, cur.I.ord x ≤ ((d + 1 : ℕ) : ℕ∞)) (hfin : Finite {j // cur.F.hyp j ≠ ∅})
    (Ω : ℕ → Opens X) (hΩ : ∀ k, k < d + 1 → IsCompact (closure (Ω k : Set X)))
    (hΩsub : ∀ k, k + 1 < d + 1 → closure (Ω k : Set X) ⊆ Ω (k + 1))
    {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (ι : AnalyticMap N X)
    (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι) (hrange : Set.range ι ⊆ Ω 0)
    (ΩZ : ℕ → Opens X) (hΩZ : ∀ k, k ≤ d → IsCompact (closure (ΩZ k : Set X)))
    (hΩZsub : ∀ k, k < d → closure (ΩZ k : Set X) ⊆ ΩZ (k + 1))
    (hΩZle : ∀ k, k < d → ΩZ k ≤ Ω k) (hZord : ∀ x ∈ ΩZ d, cur.I.ord x ≤ (d : ℕ∞))
    (hrangeZ : Set.range ι ⊆ ΩZ 0) (hclosure : closure (Set.range ι) ⊆ ΩZ d)
    (hordZ : ∀ x : X.restrict (ΩZ d),
      (cur.pullback (X.inclusion (ΩZ d)) (isLocalDiffeomorph_inclusion X _)).I.ord x ≤ (d : ℕ∞))
    (hfinZ : Finite {j //
      (cur.pullback (X.inclusion (ΩZ d)) (isLocalDiffeomorph_inclusion X _)).F.hyp j ≠ ∅})
    (hΩZ' : ∀ k, k < d → IsCompact (closure (traceOn (ΩZ d) (ΩZ k) : Set (X.restrict (ΩZ d)))))
    (hΩZsub' : ∀ k, k + 1 < d →
      closure (traceOn (ΩZ d) (ΩZ k) : Set (X.restrict (ΩZ d))) ⊆ traceOn (ΩZ d) (ΩZ (k + 1)))
    (hrZ : Set.range ι ⊆ ΩZ d)
    (hrangeZ' : Set.range (AnalyticMap.corestrict ι (ΩZ d) hrZ) ⊆ traceOn (ΩZ d) (ΩZ 0)) :
    (resolveFrom bo (d + 1) cur hord hfin Ω hΩ hΩsub ι hι hrange).eraseEmpty =
      (resolveFrom bo d (cur.pullback (X.inclusion (ΩZ d)) (isLocalDiffeomorph_inclusion X _))
        hordZ hfinZ (fun k => traceOn (ΩZ d) (ΩZ k)) hΩZ' hΩZsub'
        (AnalyticMap.corestrict ι (ΩZ d) hrZ) (isLocalDiffeomorph_corestrict ι (ΩZ d) hι hrZ)
        hrangeZ').eraseEmpty := by
  /- ### The top round and its data -/
  have hOX := hΩ d (Nat.lt_succ_self d)
  have hclsX := boClass_succ_of_ord_le cur hord hfin
  set LX := roundList bo cur hclsX (Ω d) hOX with hLXdef
  set curXO := cur.pullback (X.inclusion (Ω d)) (isLocalDiffeomorph_inclusion X (Ω d))
    with hcurXO
  have hgeX : LX.toSuccession.IsOfOrderGe curXO.I (d + 1) curXO.F.idealSheaf :=
    (bo (d + 1)).isOfOrderGe cur hclsX (Ω d) hOX
  have hrX : Set.range ι ⊆ Ω d := range_subset_chain hΩsub hrange
  have hιX' : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      (AnalyticMap.corestrict ι (Ω d) hrX) := isLocalDiffeomorph_corestrict ι (Ω d) hι hrX
  have hordXO : ∀ p : X.restrict (Ω d), X.inclusion (Ω d) p ∈ ΩZ d → curXO.I.ord p ≤ (d : ℕ∞) :=
    fun p hp =>
    (IdealSheaf.ord_comap_of_isLocalDiffeomorphAt cur.I (X.inclusion (Ω d))
      (isLocalDiffeomorph_inclusion X (Ω d) p)).trans_le (hZord _ hp)
  -- the region of low order inside the round's open, and the top round's list over it
  set Z' : Opens (X.restrict (Ω d)) := traceOn (Ω d) (ΩZ d) with hZ'def
  have hinclZ' : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      ((X.restrict (Ω d)).inclusion Z') := isLocalDiffeomorph_inclusion _ Z'
  set B := LX.pullback ((X.restrict (Ω d)).inclusion Z') hinclZ' with hBdef
  have hB0 : B.eraseEmpty = BlowUpSequence.nil ((X.restrict (Ω d)).restrict Z') :=
    eraseEmpty_pullback_roundList_eq_nil bo cur hclsX (Ω d) hOX _ hinclZ' fun y =>
      hordXO _ y.2
  -- (the reading image lies in the region: `hclosure` through `subset_closure`; the
  -- statement's own `hrZ` says the same and corestricts `ι` on the right side)
  have hrZc : Set.range ι ⊆ ΩZ d := subset_closure.trans hclosure
  have hA0 : (LX.pullback (AnalyticMap.corestrict ι (Ω d) hrX) hιX').eraseEmpty =
      BlowUpSequence.nil N :=
    eraseEmpty_pullback_roundList_eq_nil bo cur hclsX (Ω d) hOX _ hιX' fun y =>
      hordXO _ (hrZc ⟨y, rfl⟩)
  have hA : (LX.pullback (AnalyticMap.corestrict ι (Ω d) hrX) hιX').eraseEmpty =
      (BlowUpSequence.nil N).eraseEmpty := hA0
  have hB : (BlowUpSequence.nil ((X.restrict (Ω d)).restrict Z')).eraseEmpty = B.eraseEmpty :=
    hB0.symm
  /- ### The reading maps into the region and the lifts -/
  have hrι₂ : Set.range (AnalyticMap.corestrict ι (Ω d) hrX) ⊆ Z' := by
    rintro _ ⟨y, rfl⟩
    exact hrZc ⟨y, rfl⟩
  set ι₂ := AnalyticMap.corestrict (AnalyticMap.corestrict ι (Ω d) hrX) Z' hrι₂ with hι₂def
  have hι₂ : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι₂ :=
    isLocalDiffeomorph_corestrict _ Z' hιX' hrι₂
  have hfac : ((X.restrict (Ω d)).inclusion Z').comp ι₂ = AnalyticMap.corestrict ι (Ω d) hrX :=
    ContMDiffMap.ext fun _ => rfl
  have pc : B.pullback ι₂ hι₂ = LX.pullback (AnalyticMap.corestrict ι (Ω d) hrX) hιX' :=
    (BlowUpSequence.pullback_comp LX _ hinclZ' ι₂ hι₂).trans
      (BlowUpSequence.pullback_congr LX hfac _ hιX')
  obtain ⟨kY, hkYdef⟩ : ∃ kY : AnalyticMap
      ((LX.pullback (AnalyticMap.corestrict ι (Ω d) hrX) hιX').stage (Fin.last _))
      (B.stage (Fin.last _)),
      kY = (B.pullbackLiftLast ι₂ hι₂).comp
        (Diffeomorph.toAnalyticMap (BlowUpSequence.stageOfEq pc).symm) := ⟨_, rfl⟩
  have hkY : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω kY := by
    subst hkYdef
    exact BlowUpSequence.isLocalDiffeomorph_comp
        (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)
      (Diffeomorph.isLocalDiffeomorph _)
  have hkYstage : ∀ z, B.toSuccession.stageMap (Fin.last _) (kY z) =
      ι₂ ((LX.pullback (AnalyticMap.corestrict ι (Ω d) hrX) hιX').toSuccession.stageMap
        (Fin.last _) z) := fun z => by
    subst hkYdef
    rw [ContMDiffMap.comp_apply]
    change B.toSuccession.stageMap (Fin.last _)
      (B.pullbackLiftLast ι₂ hι₂ ((BlowUpSequence.stageOfEq pc).symm z)) = _
    rw [BlowUpSequence.stageMap_last_pullbackLiftLast, BlowUpSequence.stageMap_last_stageOfEq_symm]
  -- the last-stage lift of the reading map factors through the region
  obtain ⟨kZ, hkZdef⟩ : ∃ kZ : AnalyticMap (B.stage (Fin.last _)) (LX.stage (Fin.last _)),
      kZ = LX.pullbackLiftLast ((X.restrict (Ω d)).inclusion Z') hinclZ' := ⟨_, rfl⟩
  have hkZ : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω kZ := by
    subst hkZdef
    exact BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _
  have hk : LX.pullbackLiftLast (AnalyticMap.corestrict ι (Ω d) hrX) hιX' = kZ.comp kY :=
    BlowUpSequence.eq_of_stageMap_last_eq LX _ (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast
        _ _ _) _
      fun z => by
        rw [BlowUpSequence.stageMap_last_pullbackLiftLast, ContMDiffMap.comp_apply, hkZdef,
          BlowUpSequence.stageMap_last_pullbackLiftLast, hkYstage]
        exact (congrArg (fun f : AnalyticMap N (X.restrict (Ω d)) => f _) hfac).symm
  /- ### The identifications of the last stages: `θ` on the reading side, `τ` on the region -/
  obtain ⟨θ, hθdef⟩ : ∃ θ : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜)
      ((LX.pullback (AnalyticMap.corestrict ι (Ω d) hrX) hιX').stage (Fin.last _))
      ((BlowUpSequence.nil N).stage (Fin.last _)) ω,
      θ = BlowUpSequence.eraseEmptyTransport (LX.pullback (AnalyticMap.corestrict ι (Ω d) hrX) hιX')
        (BlowUpSequence.nil N) hA := ⟨_, rfl⟩
  obtain ⟨τ, hτdef⟩ : ∃ τ : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜)
      ((BlowUpSequence.nil ((X.restrict (Ω d)).restrict Z')).stage (Fin.last _))
      (B.stage (Fin.last _)) ω,
      τ = BlowUpSequence.eraseEmptyTransport (BlowUpSequence.nil ((X.restrict
          (Ω d)).restrict Z')) B hB :=
    ⟨_, rfl⟩
  -- the reading map through `θ⁻¹` and `kY` is the reading map through `ι₂` and `τ`
  have hθι : kY.comp (Diffeomorph.toAnalyticMap θ.symm) = (Diffeomorph.toAnalyticMap τ).comp ι₂ :=
    BlowUpSequence.eq_of_stageMap_last_eq B _
      (BlowUpSequence.isLocalDiffeomorph_comp hkY (Diffeomorph.isLocalDiffeomorph _)) _ fun z => by
      change B.toSuccession.stageMap (Fin.last _) (kY (Diffeomorph.toAnalyticMap θ.symm z)) =
        B.toSuccession.stageMap (Fin.last _) (Diffeomorph.toAnalyticMap τ (ι₂ z))
      -- `τ` lies over the identity of the region (the empty list's blow-down is the identity)
      have h2 : B.toSuccession.stageMap (Fin.last _) (Diffeomorph.toAnalyticMap τ (ι₂ z)) =
          ι₂ z := by
        rw [hτdef]
        exact BlowUpSequence.stageMap_last_toAnalyticMap_eraseEmptyTransport
            (BlowUpSequence.nil _) B hB
          (ι₂ z)
      -- `θ⁻¹` lies over the identity of the reading manifold
      have h1 := BlowUpSequence.stageMap_last_eraseEmptyTransport _ _ hA (θ.symm z)
      rw [← hθdef, Diffeomorph.apply_symm_apply] at h1
      rw [hkYstage, h2]
      exact congrArg ι₂ h1.symm
  /- ### The transported derived triple on the region's last stage -/
  set cur₂ := curXO.pullback ((X.restrict (Ω d)).inclusion Z') hinclZ' with hcur₂
  have hgeB : B.toSuccession.IsOfOrderGe cur₂.I (d + 1) cur₂.F.idealSheaf :=
    AnalyticTriple.isOfOrderGe_pullback curXO (d + 1) LX hgeX _ hinclZ'
  -- the ideal: the transported derived ideal is the restricted ideal
  have hI₂ : ((curXO.induced (d + 1) LX hgeX).pullback kZ hkZ).I.pullback _
      (Diffeomorph.toAnalyticMap τ).contMDiff = cur₂.I := by
    change ((LX.toSuccession.markedTransformSeq curXO.I (d + 1) (Fin.last _)).pullback kZ
        kZ.contMDiff).pullback _ (Diffeomorph.toAnalyticMap τ).contMDiff = cur₂.I
    rw [hkZdef, hτdef]
    exact (congrArg (Manifold.IdealSheaf.pullback _ _)
      (BlowUpSequence.markedTransformSeq_last_pullbackLiftLast LX _ hinclZ' curXO.I _ (d + 1)
        hgeX).symm).trans
      (BlowUpSequence.markedTransformSeq_last_eraseEmptyTransport (BlowUpSequence.nil _) B hB cur₂.I
        (d + 1) (FiniteSuccession.isMarkedGe_nil _ _) hgeB.isMarkedGe)
  -- the boundary: the restricted family is an empty subfamily of the transported derived boundary
  have hFc₂ : ∀ j, IsClosed (cur₂.F.hyp j) := fun j => (cur₂.isSnc.isClosedSubmanifold j).isClosed
  obtain ⟨eF, h1F, h2F⟩ := BlowUpSequence.exists_orderEmbedding_eraseEmptyTransport
    (BlowUpSequence.nil ((X.restrict (Ω d)).restrict Z')) B (BlowUpSequence.noEmptyCenters_nil) hB
        cur₂.F
    hFc₂ ((curXO.induced (d + 1) LX hgeX).pullback kZ hkZ).F
    (by
      subst hkZdef
      exact BlowUpSequence.totalTransformSeqFrom_last_pullbackLiftLast LX _ hinclZ' curXO.F)
  set F' : HypersurfaceFamily (B.stage (Fin.last _)) :=
    cur₂.F.comap ⇑(Diffeomorph.toAnalyticMap τ.symm) with hF'def
  have hsnc' : F'.IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) :=
    HypersurfaceFamily.isSnc_comap cur₂.isSnc (Diffeomorph.toAnalyticMap τ.symm)
      (Diffeomorph.isLocalDiffeomorph _)
  have hτid : ⇑τ ∘ ⇑(Diffeomorph.toAnalyticMap τ.symm) = id :=
    funext fun x => τ.apply_symm_apply x
  have hhypF : ∀ i, ((curXO.induced (d + 1) LX hgeX).pullback kZ hkZ).F.hyp (eF i) =
      F'.hyp i := fun i => by
    have h1F' : ⇑τ ⁻¹' ((curXO.induced (d + 1) LX hgeX).pullback kZ hkZ).F.hyp (eF i) =
        cur₂.F.hyp i := by
      rw [hτdef]
      exact h1F i
    change _ = ⇑(Diffeomorph.toAnalyticMap τ.symm) ⁻¹' cur₂.F.hyp i
    rw [← h1F', ← Set.preimage_comp, hτid, Set.preimage_id]
  have hemptyF : ∀ b, b ∉ Set.range eF →
      ((curXO.induced (d + 1) LX hgeX).pullback kZ hkZ).F.hyp b = ∅ := h2F
  -- the reduced triple is the pull-back of the restricted triple along `τ`
  have hpb₂ : cur₂.IsPullbackOf (⟨((curXO.induced (d + 1) LX hgeX).pullback kZ hkZ).I,
      ((curXO.induced (d + 1) LX hgeX).pullback kZ hkZ).isNonzeroEverywhere, F', hsnc'⟩ :
        AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (B.stage (Fin.last _)))
      (Diffeomorph.toAnalyticMap τ) :=
    ⟨hI₂.symm, (HypersurfaceFamily.comap_symm_comap_family τ.symm cur₂.F).symm⟩
  /- ### The chains: over the low-order chain, on the region and on its last stage -/
  have hΩt : ∀ k, k < d → IsCompact (closure (traceOn (Ω d) (ΩZ k) : Set (X.restrict (Ω d)))) :=
    fun k hk => isCompact_closure_preimage_val_of_closure_subset (hΩZ k hk.le)
      ((closure_mono (hΩZle k hk)).trans ((hΩsub k (by omega)).trans
        (chain_le_of_le hΩsub (by omega) (Nat.lt_succ_self d))))
  have hΩtZ : ∀ k, k < d → closure (traceOn (Ω d) (ΩZ k) : Set (X.restrict (Ω d))) ⊆ Z' :=
    fun k hk => (continuous_subtype_val.closure_preimage_subset _).trans (Set.preimage_mono
      ((hΩZsub k hk).trans (chain_le_of_le (fun k hk => hΩZsub k (by omega)) (by omega)
        (Nat.lt_succ_self d))))
  have hΩtsub : ∀ k, k + 1 < d → closure (traceOn (Ω d) (ΩZ k) : Set (X.restrict (Ω d))) ⊆
      traceOn (Ω d) (ΩZ (k + 1)) := fun k hk =>
    (continuous_subtype_val.closure_preimage_subset _).trans
      (Set.preimage_mono (hΩZsub k (by omega)))
  have hΩB : ∀ k, k < d → IsCompact (closure (liftChain B (fun k => traceOn (Ω d) (ΩZ k)) k :
      Set (B.stage (Fin.last _)))) := fun k hk =>
    isCompact_closure_liftOpens B (hΩt k hk) (hΩtZ k hk)
  have hΩBsub : ∀ k, k + 1 < d → closure (liftChain B (fun k => traceOn (Ω d) (ΩZ k)) k :
      Set (B.stage (Fin.last _))) ⊆ liftChain B (fun k => traceOn (Ω d) (ΩZ k)) (k + 1) :=
    fun k hk => closure_liftOpens_subset B (hΩtsub k hk)
  -- (the empty list's `ψ₀` is fixed by `isCompact_closure_liftOpens`'s binder, so the
  -- statements are left to inference: `liftChain … k` unfolds to these `liftOpens`)
  have hΩ₂ := fun k (hk : k < d) =>
    isCompact_closure_liftOpens (BlowUpSequence.nil ((X.restrict (Ω d)).restrict Z')) (hΩt k hk)
      (hΩtZ k hk)
  have hΩ₂sub := fun k (hk : k + 1 < d) =>
    closure_liftOpens_subset (BlowUpSequence.nil ((X.restrict (Ω d)).restrict Z')) (hΩtsub k hk)
  -- the reading maps land in the innermost opens
  -- (`SetLike.coe` spelled out: the region and the empty list's last stage agree only after
  -- unfolding, which the coercion's instance search does not do)
  have hrι₂' : Set.range ι₂ ⊆ SetLike.coe (liftChain
      (BlowUpSequence.nil ((X.restrict (Ω d)).restrict Z')) (fun k => traceOn (Ω d) (ΩZ k)) 0) := by
    rintro _ ⟨y, rfl⟩
    exact (mem_liftChain_iff (BlowUpSequence.nil ((X.restrict (Ω d)).restrict Z'))
      (fun k => traceOn (Ω d) (ΩZ k)) 0 (ι₂ y)).mpr (hrangeZ ⟨y, rfl⟩)
  have hrkY : Set.range kY ⊆ liftChain B (fun k => traceOn (Ω d) (ΩZ k)) 0 := by
    rintro _ ⟨z, rfl⟩
    rw [SetLike.mem_coe, mem_liftChain_iff, hkYstage]
    exact hrangeZ ⟨_, rfl⟩
  -- the transported chains: `τ` carries the region's chain into the last stage's
  have hΩτ : ∀ k, k < d → ⇑(Diffeomorph.toAnalyticMap τ) ''
      (liftChain (BlowUpSequence.nil ((X.restrict (Ω d)).restrict Z')) (fun k => traceOn (Ω d)
          (ΩZ k))
        k : Set _) ⊆ liftChain B (fun k => traceOn (Ω d) (ΩZ k)) k := by
    rintro k _ _ ⟨p, hp, rfl⟩
    rw [SetLike.mem_coe, mem_liftChain_iff] at hp ⊢
    rw [hτdef, BlowUpSequence.stageMap_last_toAnalyticMap_eraseEmptyTransport]
    exact hp
  -- `kZ` carries the last stage's chain into the lifted chain of the round
  have hΩkZ : ∀ k, k < d → ⇑kZ '' (liftChain B (fun k => traceOn (Ω d) (ΩZ k)) k : Set _) ⊆
      liftChain LX Ω k := by
    rintro k hk _ ⟨p, hp, rfl⟩
    rw [SetLike.mem_coe, mem_liftChain_iff] at hp ⊢
    rw [hkZdef, BlowUpSequence.stageMap_last_pullbackLiftLast]
    exact hΩZle k hk hp
  /- ### The orders and finiteness on the transported triples -/
  have hordT : ∀ x, ((curXO.induced (d + 1) LX hgeX).pullback kZ hkZ).I.ord x ≤ (d : ℕ∞) :=
    fun x => (IdealSheaf.ord_comap_of_isLocalDiffeomorphAt _ kZ (hkZ x)).trans_le
      (derivedTriple_ord_le bo cur hclsX (Ω d) hOX (kZ x))
  have hclsXO : AnalyticTriple.BOClass (d + 1) curXO :=
    AnalyticTriple.boClass_of_isPullbackOf hclsX (isLocalDiffeomorph_inclusion X (Ω d))
      (AnalyticTriple.isPullbackOf_pullback cur _ _)
  have hfinT : Finite {j // ((curXO.induced (d + 1) LX hgeX).pullback kZ hkZ).F.hyp j ≠ ∅} :=
    (AnalyticTriple.boClass_of_isPullbackOf
      (AnalyticTriple.boClass_induced curXO (d + 1) LX hgeX hclsXO) hkZ
      (AnalyticTriple.isPullbackOf_pullback _ kZ hkZ)).2.2
  have hord₂ : ∀ y, cur₂.I.ord y ≤ (d : ℕ∞) := fun y =>
    (IdealSheaf.ord_comap_of_isLocalDiffeomorphAt curXO.I _ (hinclZ' y)).trans_le
      (hordXO _ y.2)
  have hfin₂ : Finite {j // cur₂.F.hyp j ≠ ∅} :=
    (AnalyticTriple.boClass_of_isPullbackOf hclsXO hinclZ'
      (AnalyticTriple.isPullbackOf_pullback curXO _ hinclZ')).2.2
  have hfinF' : Finite {j // F'.hyp j ≠ ∅} :=
    HypersurfaceFamily.finite_nonempty_comap cur₂.F _ hfin₂
  /- ### The three transports -/
  -- (i) from the round's last stage to the region's last stage (the exact pull-back)
  have hT1 := eraseEmpty_resolveFrom_congr bo d kZ hkZ (curXO.induced (d + 1) LX hgeX)
    ((curXO.induced (d + 1) LX hgeX).pullback kZ hkZ)
    (AnalyticTriple.isPullbackOf_pullback _ kZ hkZ)
    (derivedTriple_ord_le bo cur hclsX (Ω d) hOX) (derivedTriple_finite bo cur hclsX (Ω d) hOX)
    hordT hfinT (liftChain LX Ω) (liftChain_isCompact LX hΩ hΩsub rfl)
    (liftChain_closure_subset LX hΩsub) (liftChain B (fun k => traceOn (Ω d) (ΩZ k))) hΩB hΩBsub
    hΩkZ (LX.pullbackLiftLast (AnalyticMap.corestrict ι (Ω d) hrX) hιX')
    (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)
    (range_pullbackLiftLast_subset_liftOpens LX ι hι (Ω 0) hrange hrX) kY hkY hrkY
    (ContMDiffMap.id : AnalyticMap _ _) (BlowUpSequence.isLocalDiffeomorph_id _)
    (ContMDiffMap.ext fun z => congrArg (fun f : AnalyticMap _ _ => f z) hk)
  -- (ii) the reduced triple: the empty exceptional members dropped (`resolveFrom_indiff`)
  have hT2 := resolveFrom_indiff bo d ((curXO.induced (d + 1) LX hgeX).pullback kZ hkZ) F' hsnc' eF
    hhypF hemptyF hordT hfinT hfinF' (liftChain B (fun k => traceOn (Ω d) (ΩZ k))) hΩB hΩBsub kY
    hkY hrkY
  -- (iii) from the region (read through `ι₂`) to the region's last stage (read through `kY`)
  have hT3 := eraseEmpty_resolveFrom_congr bo d (Diffeomorph.toAnalyticMap τ)
    (Diffeomorph.isLocalDiffeomorph _) _ cur₂ hpb₂ hordT hfinF' hord₂ hfin₂
    (liftChain B (fun k => traceOn (Ω d) (ΩZ k))) hΩB hΩBsub
    (liftChain (BlowUpSequence.nil ((X.restrict (Ω d)).restrict Z')) (fun k => traceOn (Ω d)
        (ΩZ k)))
    hΩ₂ hΩ₂sub hΩτ kY hkY hrkY ι₂ hι₂ hrι₂' (Diffeomorph.toAnalyticMap θ.symm)
    (Diffeomorph.isLocalDiffeomorph _) hθι
  -- (iv) from the region to the restricted manifold of the statement
  have hres : ⇑(X.inclusion (Ω d)) '' (Z' : Set (X.restrict (Ω d))) ⊆ ΩZ d := by
    rintro _ ⟨p, hp, rfl⟩
    exact hp
  have hcur₂Z : cur₂ =
      (cur.pullback (X.inclusion (ΩZ d)) (isLocalDiffeomorph_inclusion X _)).pullback
      (AnalyticMap.restrictMap (X.inclusion (Ω d)) Z' (ΩZ d) hres)
      (AnalyticMap.isLocalDiffeomorph_restrictMap (isLocalDiffeomorph_inclusion X (Ω d)) Z' (ΩZ d)
        hres) := by
    rw [hcur₂, hcurXO, AnalyticTriple.pullback_pullback _ _ _ _ _,
      AnalyticTriple.pullback_pullback _ _ _ _ _]
    exact AnalyticTriple.pullback_eq_of_eq cur (ContMDiffMap.ext fun _ => rfl) _ _
  have hΩres : ∀ k, k < d → ⇑(AnalyticMap.restrictMap (X.inclusion (Ω d)) Z' (ΩZ d) hres) ''
      SetLike.coe (liftChain (BlowUpSequence.nil ((X.restrict (Ω d)).restrict Z'))
        (fun k => traceOn (Ω d) (ΩZ k)) k) ⊆ traceOn (ΩZ d) (ΩZ k) := by
    rintro k _ _ ⟨p, hp, rfl⟩
    exact (mem_liftChain_iff (BlowUpSequence.nil ((X.restrict (Ω d)).restrict Z'))
      (fun k => traceOn (Ω d) (ΩZ k)) k p).mp hp
  have hT4 := eraseEmpty_resolveFrom_congr bo d
    (AnalyticMap.restrictMap (X.inclusion (Ω d)) Z' (ΩZ d) hres)
    (AnalyticMap.isLocalDiffeomorph_restrictMap (isLocalDiffeomorph_inclusion X (Ω d)) Z' (ΩZ d)
      hres) (cur.pullback (X.inclusion (ΩZ d)) (isLocalDiffeomorph_inclusion X _)) cur₂
    (by rw [hcur₂Z]; exact AnalyticTriple.isPullbackOf_pullback _ _ _) hordZ hfinZ hord₂ hfin₂
    (fun k => traceOn (ΩZ d) (ΩZ k)) hΩZ' hΩZsub'
    (liftChain (BlowUpSequence.nil ((X.restrict (Ω d)).restrict Z')) (fun k => traceOn (Ω d)
        (ΩZ k)))
    hΩ₂ hΩ₂sub hΩres (AnalyticMap.corestrict ι (ΩZ d) hrZ)
    (isLocalDiffeomorph_corestrict ι (ΩZ d) hι hrZ) hrangeZ' ι₂ hι₂ hrι₂'
    (ContMDiffMap.id : AnalyticMap N N) (BlowUpSequence.isLocalDiffeomorph_id _)
    (ContMDiffMap.ext fun _ => rfl)
  /- ### Assembly -/
  rw [BlowUpSequence.pullback_id] at hT1 hT4
  have hid : (Diffeomorph.toAnalyticMap θ.symm).comp (Diffeomorph.toAnalyticMap θ) =
      ContMDiffMap.id := ContMDiffMap.ext fun z => θ.symm_apply_apply z
  -- the statement's right side pulled back along `θ` is the reduced rounds on the reading manifold
  have hRZ : ((resolveFrom bo d (cur.pullback (X.inclusion (ΩZ d))
        (isLocalDiffeomorph_inclusion X _)) hordZ hfinZ (fun k => traceOn (ΩZ d) (ΩZ k)) hΩZ'
        hΩZsub' (AnalyticMap.corestrict ι (ΩZ d) hrZ)
        (isLocalDiffeomorph_corestrict ι (ΩZ d) hι hrZ) hrangeZ').pullback
        (Diffeomorph.toAnalyticMap θ) (Diffeomorph.isLocalDiffeomorph _)).eraseEmpty =
      (resolveFrom bo d (⟨((curXO.induced (d + 1) LX hgeX).pullback kZ hkZ).I,
        ((curXO.induced (d + 1) LX hgeX).pullback kZ hkZ).isNonzeroEverywhere, F', hsnc'⟩ :
          AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (B.stage (Fin.last _)))
        hordT hfinF' (liftChain B (fun k => traceOn (Ω d) (ΩZ k))) hΩB hΩBsub kY hkY
        hrkY).eraseEmpty := by
    -- (`hT4` reads the region's rounds on the region, `hT3` on the empty list's last stage: the
    -- two agree only up to unfolding, so the step is a `congrArg`, not a rewrite)
    refine (BlowUpSequence.eraseEmpty_pullback_eraseEmpty _ _ _).symm.trans ?_
    refine (congrArg (fun L => (BlowUpSequence.pullback L (Diffeomorph.toAnalyticMap θ)
      (Diffeomorph.isLocalDiffeomorph _)).eraseEmpty) (hT4.symm.trans hT3)).trans ?_
    exact (BlowUpSequence.eraseEmpty_pullback_eraseEmpty _ _ _).trans
        (congrArg BlowUpSequence.eraseEmpty
      ((BlowUpSequence.pullback_comp _ _ _ _ _).trans
        ((BlowUpSequence.pullback_congr _ hid _ (BlowUpSequence.isLocalDiffeomorph_id _)).trans
          (BlowUpSequence.pullback_id _))))
  -- `θ` is the transport along the empty erasure of the top round's list on the reading side
  subst hθdef
  rw [resolveFrom]
  refine (BlowUpSequence.eraseEmpty_concat_congr _ (BlowUpSequence.nil N) hA _ _ ?_).trans
    (congrArg BlowUpSequence.eraseEmpty (BlowUpSequence.concat_nil _))
  exact (hT1.symm.trans (congrArg BlowUpSequence.eraseEmpty hT2)).trans hRZ.symm

end Manifold

end
