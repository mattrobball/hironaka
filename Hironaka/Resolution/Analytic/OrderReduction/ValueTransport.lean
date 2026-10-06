/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Step21Fam
public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
public import Hironaka.Resolution.Analytic.Functor.EraseEmptyConcat
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Resolution.Analytic.OrderReduction.ChainTransportPrep
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.OrderReduction.LiftUnique
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Transport of a link along a value functor

The argument, stated once, behind the second clause of [Kol07, 34.1] (the value on a pull-back is
the pull-back of the value with the empty blow-ups deleted) for one link of a chain of Step 2 of
the proof of [Kol07, Theorem 103]: along a local analytic isomorphism `h : N → M` carrying an open
`W' ⊆ N` into `W ⊆ M`, a chain state over `W'` for the pulled-back triple and a chain state over
`W` whose sequences agree **up to empty blow-ups after pulling back** keep that relation through
one link (smaller opens `V' ⊆ W'`, `V ⊆ W` with `h(V') ⊆ V`), whatever the value appended by the
link, as long as that value is read from a "value functor" with the two naturality properties: it
commutes with local analytic isomorphisms, and it does not see empty blow-ups. Here the value
functor is not fixed: the argument is stated for **arbitrary appended values**, the two naturality
properties entering as hypotheses on those values, and the three value functors of the
development are instances:

* the family of one boundary member at the induced triple (`ChainTransport.lean`, the chain of
  Step 2.1);
* the family functor of Step 2.2 at the triple of Step 2.2 (`Step2LinkTransport.lean`, the link
  of Step 2.2);
* an arbitrary family functor with the two naturality properties at the induced triple
  (`Modified/InducedValueFunctor.lean`, the rounds of the modified algorithm).

The argument, in two halves:

* **The algebra of sequences** (`BlowUpSequence.shrinkAppend_eraseEmpty_pullback`): the
  shrink-and-append step of `L₂` on `N` with a value `F₂`, with the empty blow-ups deleted and
  pulled back along `h|_{V'}`, is the restricted sequence with the empty blow-ups deleted followed
  by the appended value transported to the common last stage (`pullback_concat`,
  `eraseEmpty_concat`, `concat_map_stageOfEq`, `map_eq_pullback_symm`), so the relation reduces to
  a comparison of the two appended values pulled back to that stage.
* **The comparison of the two appended values** (`BlowUpSequence.valueTransport_rel`): for values
  `G₂` on the reading open of `L₂`, `G₁` on that of `L₁`, given (i) `G₂` and the value `GP` at
  `h^* L₁` are the values `Ge₂`, `GeP` at the cleaned sequences transported along `eraseEmptyLast`
  (the value functor ignores empty blow-ups; `hA2`, `hA1`), (ii) `G₁` pulled back along the
  restricted last-stage lift is `GP` (the value functor commutes with local isomorphisms; `hFP`),
  and (iii) `Ge₂` and `GeP` agree under the identification of the cleaned sequences (a substitution
  along `hrel`; `hcongr`, whose side conditions `mem_imageOpens_eraseEmptyLast_liftRange_iff` and
  `stageOfEq_eraseEmptyLast_liftCorestrict_apply` are supplied), the two values pulled back to the
  common cleaned last stage agree. The maps are identified by the uniqueness of maps over the
  blow-down (`eq_of_stageMap_last_comp_eq`, `LiftUnique.lean`:
  `liftCorestrict_pullbackLiftLast_comp_eq`) and the opens by `mem_liftRange_iff`.

Over states of a chain (`ChainState`), the set-up of one link — the square of restrictions, the
identification of the two pull-backs of the sequence over `W`, the relation of the restricted
sequences, the triple over `W'` as a pull-back of the triple over `W` — is
`ChainState.shrinkAppend_rel_of_value_rel` and the lemmas before it: the relation is kept by the
shrink-and-append step as soon as the two appended values compare (`hF`).
-/

public section

universe u

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace AnalyticManifold.BlowUpSequence

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

variable {M N P Q : AnalyticManifold.{u} 𝕜 E}

/-! ### The algebra of sequences -/

/-- **The algebra of sequences of one link's transport**: for sequences `L₁` on `M` and `L₂` on `N`
which agree, with the empty blow-ups deleted, after pulling `L₁` back along `hW : N → M`, and for
the restrictions `ρ : P → M`, `ρ' : Q → N`, `hV : Q → P` forming a commuting square, the
shrink-and-append step of `L₂` (with a value `F₂` on its reading open), with the empty blow-ups
deleted, is the shrink-and-append step of `L₁` (with `F₁`) pulled back along `hV` with the empty
blow-ups deleted, provided the two values agree after pulling back to the common last stage of the
restricted sequences with the empty blow-ups deleted (`hF`). `e₀` identifies the two pull-backs of
`L₁` to `Q`; `hA` the two restricted sequences. -/
theorem shrinkAppend_eraseEmpty_pullback (L₁ : BlowUpSequence ψ₀ M) (L₂ : BlowUpSequence ψ₀ N)
    (hW : AnalyticMap N M) (hhW : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω hW)
    (ρ : AnalyticMap P M) (hρ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ)
    (ρ' : AnalyticMap Q N) (hρ' : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ')
    (hV : AnalyticMap Q P) (hhV : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω hV)
    (F₁ : BlowUpSequence ψ₀ ((L₁.stage (Fin.last _)).restrict (L₁.liftRange ρ hρ)))
    (F₂ : BlowUpSequence ψ₀ ((L₂.stage (Fin.last _)).restrict (L₂.liftRange ρ' hρ')))
    (e₀ : (L₁.pullback ρ hρ).pullback hV hhV = (L₁.pullback hW hhW).pullback ρ' hρ')
    (hA : (L₂.pullback ρ' hρ').eraseEmpty = ((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmpty)
    (hκ₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      ((L₂.liftCorestrict ρ' hρ').comp
        (Diffeomorph.toAnalyticMap (L₂.pullback ρ' hρ').eraseEmptyLast.symm)))
    (hκ₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      (((L₁.liftCorestrict ρ hρ).comp ((L₁.pullback ρ hρ).pullbackLiftLast hV hhV)).comp
        (Diffeomorph.toAnalyticMap ((stageOfEq e₀).trans
          (((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.trans
            (stageOfEq hA.symm))).symm)))
    (hF : (F₂.pullback ((L₂.liftCorestrict ρ' hρ').comp
        (Diffeomorph.toAnalyticMap (L₂.pullback ρ' hρ').eraseEmptyLast.symm)) hκ₂).eraseEmpty =
      (F₁.pullback (((L₁.liftCorestrict ρ hρ).comp
          ((L₁.pullback ρ hρ).pullbackLiftLast hV hhV)).comp
        (Diffeomorph.toAnalyticMap ((stageOfEq e₀).trans
          (((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.trans
            (stageOfEq hA.symm))).symm)) hκ₁).eraseEmpty) :
    (L₂.shrinkAppend ρ' hρ' F₂).eraseEmpty =
      ((L₁.shrinkAppend ρ hρ F₁).pullback hV hhV).eraseEmpty := by
  unfold shrinkAppend
  rw [pullback_concat, ← concat_map_stageOfEq e₀, eraseEmpty_concat, eraseEmpty_concat,
    ← concat_map_stageOfEq hA.symm]
  refine congrArg _ ?_
  rw [← eraseEmpty_map, map_map, map_map, map_eq_pullback_symm, map_eq_pullback_symm,
    pullback_comp]
  rw [pullback_comp, pullback_comp]
  exact hF

/-- `stageMap_last_stageOfEq` for the inverse isomorphism. -/
theorem stageMap_last_stageOfEq_symm {L₁ L₂ : BlowUpSequence ψ₀ M} (e : L₁ = L₂)
    (q : L₂.stage (Fin.last _)) :
    L₁.toSuccession.stageMap (Fin.last _) ((stageOfEq e).symm q) =
      L₂.toSuccession.stageMap (Fin.last _) q := by
  have := stageMap_last_stageOfEq e ((stageOfEq e).symm q)
  rw [Diffeomorph.apply_symm_apply] at this
  exact this.symm

/-- `stageMap_last_eraseEmptyLast` for the inverse isomorphism. -/
theorem stageMap_last_eraseEmptyLast_symm (L : BlowUpSequence ψ₀ M)
    (q : L.eraseEmpty.stage (Fin.last _)) :
    L.toSuccession.stageMap (Fin.last _) (L.eraseEmptyLast.symm q) =
      L.eraseEmpty.toSuccession.stageMap (Fin.last _) q := by
  have := stageMap_last_eraseEmptyLast L (L.eraseEmptyLast.symm q)
  rw [Diffeomorph.apply_symm_apply] at this
  exact this.symm

/-- The last-stage lift of `hW` carries the reading open of `ρ'` on the pulled-back sequence into
the reading open of `ρ` on the sequence, when `ρ ∘ hV = hW ∘ ρ'`. -/
theorem image_liftRange_pullbackLiftLast_subset (L₁ : BlowUpSequence ψ₀ M) (hW : AnalyticMap N M)
    (hhW : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω hW) (ρ : AnalyticMap P M)
    (hρ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ) (ρ' : AnalyticMap Q N)
    (hρ' : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ') (hV : AnalyticMap Q P)
    (hsq : ρ.comp hV = hW.comp ρ') :
    ⇑(L₁.pullbackLiftLast hW hhW) ''
        ((L₁.pullback hW hhW).liftRange ρ' hρ' : Set ((L₁.pullback hW hhW).stage (Fin.last _))) ⊆
      (L₁.liftRange ρ hρ : Set (L₁.stage (Fin.last _))) := by
  rintro _ ⟨p, hp, rfl⟩
  change p ∈ (L₁.pullback hW hhW).liftRange ρ' hρ' at hp
  change L₁.pullbackLiftLast hW hhW p ∈ L₁.liftRange ρ hρ
  rw [mem_liftRange_iff] at hp ⊢
  rw [stageMap_last_pullbackLiftLast]
  obtain ⟨q, hq⟩ := hp
  rw [← hq]
  exact ⟨hV q, DFunLike.congr_fun hsq q⟩

end AnalyticManifold.BlowUpSequence

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- Membership in the image of an open under an analytic isomorphism. -/
theorem mem_imageOpens_toAnalyticMap_iff
    {X Y : AnalyticManifold.{u} 𝕜 E} (e : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) X Y ω) (O : Opens X) (p : Y) :
    p ∈ AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap e) e.isLocalDiffeomorph O ↔
      e.symm p ∈ O := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    change e.symm (e q) ∈ O
    rw [Diffeomorph.symm_apply_apply]
    exact hq
  · intro hp
    exact ⟨e.symm p, hp, e.apply_symm_apply p⟩

end Hironaka.Manifold

namespace AnalyticManifold.BlowUpSequence

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The comparison of the two appended values -/

section ValueTransport

variable {M N P Q : AnalyticManifold.{u} 𝕜 E} (L₁ : BlowUpSequence ψ₀ M) (L₂ : BlowUpSequence ψ₀ N)
  (hW : AnalyticMap N M) (hhW : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω hW)
  (ρ : AnalyticMap P M) (hρ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ)
  (ρ' : AnalyticMap Q N) (hρ' : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ')
  (hV : AnalyticMap Q P) (hhV : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω hV)

/-- The two image opens of the reading opens on the cleaned sequences correspond under the
identification `stageOfEq hrel` of the cleaned sequences (`mem_liftRange_iff`). -/
theorem mem_imageOpens_eraseEmptyLast_liftRange_iff
    (hrel : L₂.eraseEmpty = (L₁.pullback hW hhW).eraseEmpty)
    (p : L₂.eraseEmpty.stage (Fin.last _)) :
    p ∈ AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap L₂.eraseEmptyLast)
      L₂.eraseEmptyLast.isLocalDiffeomorph (L₂.liftRange ρ' hρ') ↔
    stageOfEq hrel p ∈ AnalyticMap.imageOpens
      (Diffeomorph.toAnalyticMap (L₁.pullback hW hhW).eraseEmptyLast)
      (L₁.pullback hW hhW).eraseEmptyLast.isLocalDiffeomorph
      ((L₁.pullback hW hhW).liftRange ρ' hρ') := by
  rw [mem_imageOpens_toAnalyticMap_iff, mem_imageOpens_toAnalyticMap_iff, mem_liftRange_iff,
    mem_liftRange_iff, stageMap_last_eraseEmptyLast_symm, stageMap_last_eraseEmptyLast_symm,
    stageMap_last_stageOfEq]

/-- The blow-down of the common cleaned last stage through the pull-back of `L₁` to `Q` (`hA`
followed by `eraseEmptyLast`). -/
theorem stageMap_last_stageOfEq_trans_eraseEmptyLast_symm
    (hA : (L₂.pullback ρ' hρ').eraseEmpty = ((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmpty)
    (z : (L₂.pullback ρ' hρ').eraseEmpty.stage (Fin.last _)) :
    ((L₁.pullback hW hhW).pullback ρ' hρ').toSuccession.stageMap (Fin.last _)
      (((stageOfEq hA).trans ((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.symm) z) =
    (L₂.pullback ρ' hρ').eraseEmpty.toSuccession.stageMap (Fin.last _) z :=
  (stageMap_last_eraseEmptyLast_symm ((L₁.pullback hW hhW).pullback ρ' hρ') _).trans
    (stageMap_last_stageOfEq hA z)

/-- **The two transported maps into the cleaned reading opens agree** under `stageOfEq hrel`: the
uniqueness of maps over the blow-down of the cleaned sequence (`eq_of_stageMap_last_comp_eq`). -/
theorem stageOfEq_eraseEmptyLast_liftCorestrict_apply
    (hrel : L₂.eraseEmpty = (L₁.pullback hW hhW).eraseEmpty)
    (hA : (L₂.pullback ρ' hρ').eraseEmpty = ((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmpty)
    (hκ₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      ((L₂.liftCorestrict ρ' hρ').comp
        (Diffeomorph.toAnalyticMap (L₂.pullback ρ' hρ').eraseEmptyLast.symm)))
    (z : (L₂.pullback ρ' hρ').eraseEmpty.stage (Fin.last _)) :
    stageOfEq hrel (((AnalyticMap.restrictMap
      (Diffeomorph.toAnalyticMap L₂.eraseEmptyLast) (L₂.liftRange ρ' hρ')
        (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap L₂.eraseEmptyLast)
          L₂.eraseEmptyLast.isLocalDiffeomorph (L₂.liftRange ρ' hρ')) Set.Subset.rfl).comp
      ((L₂.liftCorestrict ρ' hρ').comp
        (Diffeomorph.toAnalyticMap (L₂.pullback ρ' hρ').eraseEmptyLast.symm))) z).1 =
    (((AnalyticMap.restrictMap (Diffeomorph.toAnalyticMap (L₁.pullback hW hhW).eraseEmptyLast)
        ((L₁.pullback hW hhW).liftRange ρ' hρ')
        (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap (L₁.pullback hW hhW).eraseEmptyLast)
          (L₁.pullback hW hhW).eraseEmptyLast.isLocalDiffeomorph
            ((L₁.pullback hW hhW).liftRange ρ' hρ')) Set.Subset.rfl).comp
      (((L₁.pullback hW hhW).liftCorestrict ρ' hρ').comp (Diffeomorph.toAnalyticMap
        ((stageOfEq hA).trans
          ((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.symm)))) z).1 := by
  have hf₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ((AnalyticMap.restrictMap
      (Diffeomorph.toAnalyticMap L₂.eraseEmptyLast) (L₂.liftRange ρ' hρ')
        (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap L₂.eraseEmptyLast)
          L₂.eraseEmptyLast.isLocalDiffeomorph (L₂.liftRange ρ' hρ')) Set.Subset.rfl).comp
      ((L₂.liftCorestrict ρ' hρ').comp
        (Diffeomorph.toAnalyticMap (L₂.pullback ρ' hρ').eraseEmptyLast.symm))) :=
    isLocalDiffeomorph_comp
      (AnalyticMap.isLocalDiffeomorph_restrictMap L₂.eraseEmptyLast.isLocalDiffeomorph
        (L₂.liftRange ρ' hρ') (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap L₂.eraseEmptyLast)
          L₂.eraseEmptyLast.isLocalDiffeomorph (L₂.liftRange ρ' hρ')) Set.Subset.rfl) hκ₂
  refine congrFun (eq_of_stageMap_last_comp_eq (L₁.pullback hW hhW).eraseEmpty
    (f := fun z => stageOfEq hrel (((AnalyticMap.restrictMap
      (Diffeomorph.toAnalyticMap L₂.eraseEmptyLast) (L₂.liftRange ρ' hρ')
      (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap L₂.eraseEmptyLast)
        L₂.eraseEmptyLast.isLocalDiffeomorph (L₂.liftRange ρ' hρ')) Set.Subset.rfl).comp
      ((L₂.liftCorestrict ρ' hρ').comp
        (Diffeomorph.toAnalyticMap (L₂.pullback ρ' hρ').eraseEmptyLast.symm))) z).1)
    (g := fun z => (((AnalyticMap.restrictMap
      (Diffeomorph.toAnalyticMap (L₁.pullback hW hhW).eraseEmptyLast)
      ((L₁.pullback hW hhW).liftRange ρ' hρ')
      (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap (L₁.pullback hW hhW).eraseEmptyLast)
        (L₁.pullback hW hhW).eraseEmptyLast.isLocalDiffeomorph
          ((L₁.pullback hW hhW).liftRange ρ' hρ')) Set.Subset.rfl).comp
      (((L₁.pullback hW hhW).liftCorestrict ρ' hρ').comp (Diffeomorph.toAnalyticMap
        ((stageOfEq hA).trans
          ((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.symm)))) z).1)
    ?_ ?_ ?_ ?_) z
  · exact (stageOfEq hrel).continuous.comp
      (continuous_subtype_val.comp
      ((AnalyticMap.restrictMap (Diffeomorph.toAnalyticMap L₂.eraseEmptyLast)
        (L₂.liftRange ρ' hρ') _ Set.Subset.rfl).comp ((L₂.liftCorestrict ρ' hρ').comp
          (Diffeomorph.toAnalyticMap
            (L₂.pullback ρ' hρ').eraseEmptyLast.symm))).contMDiff.continuous)
  · exact continuous_subtype_val.comp ((AnalyticMap.restrictMap
      (Diffeomorph.toAnalyticMap (L₁.pullback hW hhW).eraseEmptyLast)
      ((L₁.pullback hW hhW).liftRange ρ' hρ')
      (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap (L₁.pullback hW hhW).eraseEmptyLast)
        (L₁.pullback hW hhW).eraseEmptyLast.isLocalDiffeomorph
          ((L₁.pullback hW hhW).liftRange ρ' hρ')) Set.Subset.rfl).comp
      (((L₁.pullback hW hhW).liftCorestrict ρ' hρ').comp (Diffeomorph.toAnalyticMap
        ((stageOfEq hA).trans
          ((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.symm)))).contMDiff.continuous
  · exact fun _ _ hD' => hD'.preimage
      ((stageOfEq hrel).isLocalDiffeomorph.isOpenMap.comp
        ((AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap L₂.eraseEmptyLast)
          L₂.eraseEmptyLast.isLocalDiffeomorph
          (L₂.liftRange ρ' hρ')).isOpen.isOpenMap_subtype_val.comp hf₁.isOpenMap))
  · intro z
    exact (stageMap_last_stageOfEq hrel _).trans
      ((stageMap_last_eraseEmptyLast L₂ _).trans
        ((stageMap_last_pullbackLiftLast L₂ ρ' hρ' _).trans
          ((congrArg ρ' (stageMap_last_eraseEmptyLast_symm (L₂.pullback ρ' hρ') z)).trans
            ((congrArg ρ'
                (stageMap_last_stageOfEq_trans_eraseEmptyLast_symm L₁ L₂ hW hhW ρ' hρ' hA
                  z)).symm.trans
              ((stageMap_last_pullbackLiftLast (L₁.pullback hW hhW) ρ' hρ' _).symm.trans
                (stageMap_last_eraseEmptyLast (L₁.pullback hW hhW) _).symm)))))

variable (hsq : ρ.comp hV = hW.comp ρ')

include hsq in
/-- **The restricted map into the reading open of `ρ` factors through the last-stage lift of
`hW`**: the uniqueness of maps over the blow-down of `L₁` (`eq_of_stageMap_last_comp_eq`). -/
theorem liftCorestrict_pullbackLiftLast_comp_eq
    (e₀ : (L₁.pullback ρ hρ).pullback hV hhV = (L₁.pullback hW hhW).pullback ρ' hρ')
    (hA : (L₂.pullback ρ' hρ').eraseEmpty = ((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmpty)
    (hκ₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      (((L₁.liftCorestrict ρ hρ).comp ((L₁.pullback ρ hρ).pullbackLiftLast hV hhV)).comp
        (Diffeomorph.toAnalyticMap ((stageOfEq e₀).trans
          (((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.trans
            (stageOfEq hA.symm))).symm))) :
    ((L₁.liftCorestrict ρ hρ).comp ((L₁.pullback ρ hρ).pullbackLiftLast hV hhV)).comp
      (Diffeomorph.toAnalyticMap ((stageOfEq e₀).trans
        (((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.trans
          (stageOfEq hA.symm))).symm) =
    (AnalyticMap.restrictMap (L₁.pullbackLiftLast hW hhW)
      ((L₁.pullback hW hhW).liftRange ρ' hρ') (L₁.liftRange ρ hρ)
      (image_liftRange_pullbackLiftLast_subset L₁ hW hhW ρ hρ ρ' hρ' hV hsq)).comp
      (((L₁.pullback hW hhW).liftCorestrict ρ' hρ').comp (Diffeomorph.toAnalyticMap
        ((stageOfEq hA).trans ((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.symm))) := by
  have hsub := image_liftRange_pullbackLiftLast_subset L₁ hW hhW ρ hρ ρ' hρ' hV hsq
  -- the blow-down of the common cleaned stage, through the two pull-backs
  have hD : ∀ z, ((L₁.pullback ρ hρ).pullback hV hhV).toSuccession.stageMap (Fin.last _)
      (((stageOfEq e₀).trans
        (((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.trans
          (stageOfEq hA.symm))).symm z) =
      (L₂.pullback ρ' hρ').eraseEmpty.toSuccession.stageMap (Fin.last _) z := fun z =>
    (stageMap_last_stageOfEq_symm e₀ _).trans
      ((stageMap_last_eraseEmptyLast_symm ((L₁.pullback hW hhW).pullback ρ' hρ') _).trans
        (stageMap_last_stageOfEq_symm hA.symm z))
  refine ContMDiffMap.ext fun z => Subtype.ext (congrFun
    (eq_of_stageMap_last_comp_eq L₁
      (f := fun z => ((((L₁.liftCorestrict ρ hρ).comp
        ((L₁.pullback ρ hρ).pullbackLiftLast hV hhV)).comp
        (Diffeomorph.toAnalyticMap ((stageOfEq e₀).trans
          (((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.trans
            (stageOfEq hA.symm))).symm)) z).1)
      (g := fun z => (((AnalyticMap.restrictMap (L₁.pullbackLiftLast hW hhW)
        ((L₁.pullback hW hhW).liftRange ρ' hρ') (L₁.liftRange ρ hρ) hsub).comp
        (((L₁.pullback hW hhW).liftCorestrict ρ' hρ').comp (Diffeomorph.toAnalyticMap
          ((stageOfEq hA).trans
            ((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.symm)))) z).1)
      ?_ ?_ ?_ ?_) z)
  · exact continuous_subtype_val.comp
      (((L₁.liftCorestrict ρ hρ).comp ((L₁.pullback ρ hρ).pullbackLiftLast hV hhV)).comp
        (Diffeomorph.toAnalyticMap ((stageOfEq e₀).trans
          (((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.trans
            (stageOfEq hA.symm))).symm)).contMDiff.continuous
  · exact continuous_subtype_val.comp ((AnalyticMap.restrictMap (L₁.pullbackLiftLast hW hhW)
      ((L₁.pullback hW hhW).liftRange ρ' hρ') (L₁.liftRange ρ hρ) hsub).comp
      (((L₁.pullback hW hhW).liftCorestrict ρ' hρ').comp (Diffeomorph.toAnalyticMap
        ((stageOfEq hA).trans
          ((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.symm)))).contMDiff.continuous
  · exact fun _ _ hD' => hD'.preimage
      ((L₁.liftRange ρ hρ).isOpen.isOpenMap_subtype_val.comp hκ₁.isOpenMap)
  · intro z
    exact (stageMap_last_pullbackLiftLast L₁ ρ hρ _).trans
      ((congrArg ρ (stageMap_last_pullbackLiftLast (L₁.pullback ρ hρ) hV hhV _)).trans
        ((congrArg (fun x => ρ (hV x)) (hD z)).trans
          ((DFunLike.congr_fun hsq _).trans
            ((congrArg hW ((congrArg ρ'
                (stageMap_last_stageOfEq_trans_eraseEmptyLast_symm L₁ L₂ hW hhW ρ' hρ' hA
                  z)).symm.trans
              (stageMap_last_pullbackLiftLast (L₁.pullback hW hhW) ρ' hρ' _).symm)).trans
              (stageMap_last_pullbackLiftLast L₁ hW hhW _).symm))))

include hsq in
/-- **The transport of a link's value**, the heart of the transport of a chain, for arbitrary
appended values: for sequences `L₂` on `N` and `L₁` on `M` whose restrictions agree, with the
empty blow-ups deleted, after pulling `L₁` back along `hW` (`hA`), a value `G₂` on the reading
open of `ρ'` on `L₂` and a value `G₁` on the reading open of `ρ` on `L₁`, both pulled back to the
common cleaned last stage of the restricted sequences and with the empty blow-ups deleted, agree,
provided

* `G₂` and the value `GP` on the reading open of `ρ'` on `hW^* L₁` are the values `Ge₂`, `GeP` on
  the cleaned sequences transported along `eraseEmptyLast` and cleaned (the value functor ignores
  empty blow-ups; `hA2`, `hA1`);
* `G₁` pulled back along the restricted last-stage lift of `hW` and cleaned is `GP` (the value
  functor commutes with local analytic isomorphisms; `hFP`);
* `Ge₂` and `GeP`, pulled back to the common cleaned stage, agree (`hcongr`; in the instances a
  substitution along the relation `hrel` of the cleaned sequences, the opens corresponding by
  `mem_imageOpens_eraseEmptyLast_liftRange_iff` and the maps by
  `stageOfEq_eraseEmptyLast_liftCorestrict_apply`).

The maps are identified by the uniqueness of maps over the blow-down
(`liftCorestrict_pullbackLiftLast_comp_eq`). -/
theorem valueTransport_rel
    (e₀ : (L₁.pullback ρ hρ).pullback hV hhV = (L₁.pullback hW hhW).pullback ρ' hρ')
    (hA : (L₂.pullback ρ' hρ').eraseEmpty = ((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmpty)
    (hκ₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      ((L₂.liftCorestrict ρ' hρ').comp
        (Diffeomorph.toAnalyticMap (L₂.pullback ρ' hρ').eraseEmptyLast.symm)))
    (hκ₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      (((L₁.liftCorestrict ρ hρ).comp ((L₁.pullback ρ hρ).pullbackLiftLast hV hhV)).comp
        (Diffeomorph.toAnalyticMap ((stageOfEq e₀).trans
          (((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.trans
            (stageOfEq hA.symm))).symm)))
    {G₂ : BlowUpSequence ψ₀ ((L₂.stage (Fin.last _)).restrict (L₂.liftRange ρ' hρ'))}
    {G₁ : BlowUpSequence ψ₀ ((L₁.stage (Fin.last _)).restrict (L₁.liftRange ρ hρ))}
    {GP : BlowUpSequence ψ₀ (((L₁.pullback hW hhW).stage
        (Fin.last _)).restrict
      ((L₁.pullback hW hhW).liftRange ρ' hρ'))}
    {Ge₂ : BlowUpSequence ψ₀ ((L₂.eraseEmpty.stage (Fin.last _)).restrict
      (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap L₂.eraseEmptyLast)
        L₂.eraseEmptyLast.isLocalDiffeomorph (L₂.liftRange ρ' hρ')))}
    {GeP : BlowUpSequence ψ₀ (((L₁.pullback hW
        hhW).eraseEmpty.stage (Fin.last _)).restrict
      (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap (L₁.pullback hW hhW).eraseEmptyLast)
        (L₁.pullback hW hhW).eraseEmptyLast.isLocalDiffeomorph
        ((L₁.pullback hW hhW).liftRange ρ' hρ')))}
    (hA2 : G₂ = (Ge₂.pullback
      (AnalyticMap.restrictMap (Diffeomorph.toAnalyticMap L₂.eraseEmptyLast) (L₂.liftRange ρ' hρ')
        _ Set.Subset.rfl)
      (AnalyticMap.isLocalDiffeomorph_restrictMap L₂.eraseEmptyLast.isLocalDiffeomorph
        (L₂.liftRange ρ' hρ') _ Set.Subset.rfl)).eraseEmpty)
    (hA1 : GP = (GeP.pullback
      (AnalyticMap.restrictMap (Diffeomorph.toAnalyticMap (L₁.pullback hW hhW).eraseEmptyLast)
        ((L₁.pullback hW hhW).liftRange ρ' hρ') _ Set.Subset.rfl)
      (AnalyticMap.isLocalDiffeomorph_restrictMap
        (L₁.pullback hW hhW).eraseEmptyLast.isLocalDiffeomorph
        ((L₁.pullback hW hhW).liftRange ρ' hρ') _ Set.Subset.rfl)).eraseEmpty)
    (hFP : (G₁.pullback
      (AnalyticMap.restrictMap (L₁.pullbackLiftLast hW hhW) ((L₁.pullback hW hhW).liftRange ρ' hρ')
        (L₁.liftRange ρ hρ) (image_liftRange_pullbackLiftLast_subset L₁ hW hhW ρ hρ ρ' hρ' hV hsq))
      (AnalyticMap.isLocalDiffeomorph_restrictMap (isLocalDiffeomorph_pullbackLiftLast L₁ hW hhW)
        _ _ _)).eraseEmpty = GP)
    (hcongr : ∀ (hf₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ((AnalyticMap.restrictMap
        (Diffeomorph.toAnalyticMap L₂.eraseEmptyLast) (L₂.liftRange ρ' hρ')
          (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap L₂.eraseEmptyLast)
            L₂.eraseEmptyLast.isLocalDiffeomorph (L₂.liftRange ρ' hρ')) Set.Subset.rfl).comp
        ((L₂.liftCorestrict ρ' hρ').comp
          (Diffeomorph.toAnalyticMap (L₂.pullback ρ' hρ').eraseEmptyLast.symm))))
      (hf₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ((AnalyticMap.restrictMap
        (Diffeomorph.toAnalyticMap (L₁.pullback hW hhW).eraseEmptyLast)
          ((L₁.pullback hW hhW).liftRange ρ' hρ')
          (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap (L₁.pullback hW hhW).eraseEmptyLast)
            (L₁.pullback hW hhW).eraseEmptyLast.isLocalDiffeomorph
              ((L₁.pullback hW hhW).liftRange ρ' hρ')) Set.Subset.rfl).comp
        (((L₁.pullback hW hhW).liftCorestrict ρ' hρ').comp (Diffeomorph.toAnalyticMap
          ((stageOfEq hA).trans
            ((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.symm))))),
      Ge₂.pullback _ hf₁ = GeP.pullback _ hf₂) :
    (G₂.pullback ((L₂.liftCorestrict ρ' hρ').comp
        (Diffeomorph.toAnalyticMap (L₂.pullback ρ' hρ').eraseEmptyLast.symm)) hκ₂).eraseEmpty =
    (G₁.pullback (((L₁.liftCorestrict ρ hρ).comp ((L₁.pullback ρ hρ).pullbackLiftLast hV hhV)).comp
      (Diffeomorph.toAnalyticMap ((stageOfEq e₀).trans
        (((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.trans
          (stageOfEq hA.symm))).symm)) hκ₁).eraseEmpty := by
  have hsub := image_liftRange_pullbackLiftLast_subset L₁ hW hhW ρ hρ ρ' hρ' hV hsq
  -- the maps into the reading opens
  have hψ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (AnalyticMap.restrictMap
      (L₁.pullbackLiftLast hW hhW) ((L₁.pullback hW hhW).liftRange ρ' hρ') (L₁.liftRange ρ hρ)
      hsub) :=
    AnalyticMap.isLocalDiffeomorph_restrictMap (isLocalDiffeomorph_pullbackLiftLast L₁ hW hhW) _ _
      hsub
  have hκ₁' : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      (((L₁.pullback hW hhW).liftCorestrict ρ' hρ').comp (Diffeomorph.toAnalyticMap
        ((stageOfEq hA).trans ((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.symm))) :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_liftCorestrict _ ρ' hρ')
      (Diffeomorph.isLocalDiffeomorph _)
  have hψκ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ((AnalyticMap.restrictMap
      (L₁.pullbackLiftLast hW hhW) ((L₁.pullback hW hhW).liftRange ρ' hρ') (L₁.liftRange ρ hρ)
      hsub).comp (((L₁.pullback hW hhW).liftCorestrict ρ' hρ').comp (Diffeomorph.toAnalyticMap
        ((stageOfEq hA).trans ((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.symm)))) :=
    isLocalDiffeomorph_comp hψ hκ₁'
  have hf₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ((AnalyticMap.restrictMap
      (Diffeomorph.toAnalyticMap L₂.eraseEmptyLast) (L₂.liftRange ρ' hρ')
        (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap L₂.eraseEmptyLast)
          L₂.eraseEmptyLast.isLocalDiffeomorph (L₂.liftRange ρ' hρ')) Set.Subset.rfl).comp
      ((L₂.liftCorestrict ρ' hρ').comp
        (Diffeomorph.toAnalyticMap (L₂.pullback ρ' hρ').eraseEmptyLast.symm))) :=
    isLocalDiffeomorph_comp
      (AnalyticMap.isLocalDiffeomorph_restrictMap L₂.eraseEmptyLast.isLocalDiffeomorph
        (L₂.liftRange ρ' hρ') (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap L₂.eraseEmptyLast)
          L₂.eraseEmptyLast.isLocalDiffeomorph (L₂.liftRange ρ' hρ')) Set.Subset.rfl) hκ₂
  have hf₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ((AnalyticMap.restrictMap
      (Diffeomorph.toAnalyticMap (L₁.pullback hW hhW).eraseEmptyLast)
        ((L₁.pullback hW hhW).liftRange ρ' hρ')
        (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap (L₁.pullback hW hhW).eraseEmptyLast)
          (L₁.pullback hW hhW).eraseEmptyLast.isLocalDiffeomorph
            ((L₁.pullback hW hhW).liftRange ρ' hρ')) Set.Subset.rfl).comp
      (((L₁.pullback hW hhW).liftCorestrict ρ' hρ').comp (Diffeomorph.toAnalyticMap
        ((stageOfEq hA).trans ((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.symm)))) :=
    isLocalDiffeomorph_comp
      (AnalyticMap.isLocalDiffeomorph_restrictMap
        (L₁.pullback hW hhW).eraseEmptyLast.isLocalDiffeomorph
        ((L₁.pullback hW hhW).liftRange ρ' hρ')
        (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap (L₁.pullback hW hhW).eraseEmptyLast)
          (L₁.pullback hW hhW).eraseEmptyLast.isLocalDiffeomorph
            ((L₁.pullback hW hhW).liftRange ρ' hρ')) Set.Subset.rfl) hκ₁'
  -- the restricted map factors through the lift
  have hκfac := liftCorestrict_pullbackLiftLast_comp_eq L₁ L₂ hW hhW ρ hρ ρ' hρ' hV hhV hsq e₀ hA
    hκ₁
  -- the two values, transported to the common cleaned sequence
  have hL := (congrArg (fun X : BlowUpSequence ψ₀ ((L₂.stage (Fin.last _)).restrict
      (L₂.liftRange ρ' hρ')) => (X.pullback ((L₂.liftCorestrict ρ' hρ').comp
        (Diffeomorph.toAnalyticMap (L₂.pullback ρ' hρ').eraseEmptyLast.symm)) hκ₂).eraseEmpty)
      hA2).trans
    ((eraseEmpty_pullback_eraseEmpty _ _ hκ₂).trans
      (congrArg eraseEmpty (pullback_comp _ _ _ _ hκ₂)))
  have hR := (congrArg eraseEmpty (pullback_congr _ hκfac hκ₁ hψκ)).trans
    ((congrArg eraseEmpty (pullback_comp _ _ hψ _ hκ₁').symm).trans
      ((eraseEmpty_pullback_eraseEmpty _ _ hκ₁').symm.trans
        ((congrArg (fun X : BlowUpSequence ψ₀ (((L₁.pullback
            hW hhW).stage
            (Fin.last _)).restrict
            ((L₁.pullback hW hhW).liftRange ρ' hρ')) => (X.pullback
              (((L₁.pullback hW hhW).liftCorestrict ρ' hρ').comp (Diffeomorph.toAnalyticMap
                ((stageOfEq hA).trans
                  ((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.symm))) hκ₁').eraseEmpty)
          (hFP.trans hA1)).trans
          ((eraseEmpty_pullback_eraseEmpty _ _ hκ₁').trans
            (congrArg eraseEmpty (pullback_comp _ _ _ _ hκ₁'))))))
  exact hL.trans ((congrArg eraseEmpty (hcongr hf₁ hf₂)).trans hR.symm)

end ValueTransport

end AnalyticManifold.BlowUpSequence

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace ChainState

/-! ### The set-up of one link over states of a chain -/

variable {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (s : ℕ) (h : AnalyticMap N M)
  (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)

/-- The triple over `W'` is the pull-back of the triple over `W` along `h|_{W'}`. -/
theorem triple_pullback_restrictMap_eq {W : Opens M} {W' : Opens N}
    (hWW' : ⇑h '' (W' : Set N) ⊆ W) :
    (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).pullback
      (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW') =
    (T.pullback h hh).pullback (N.inclusion W') (isLocalDiffeomorph_inclusion N W') := by
  have hmap : (M.inclusion W).comp (AnalyticMap.restrictMap h W' W hWW') =
      h.comp (N.inclusion W') := ContMDiffMap.ext fun _ => rfl
  rw [AnalyticTriple.pullback_pullback, AnalyticTriple.pullback_pullback]
  exact AnalyticTriple.pullback_eq_of_eq T hmap _ _

/-- The class of the triple over `W`, pulled back along `h|_{W'}`, from the class of the pulled-back
triple. -/
theorem boClass_triple_pullback_restrictMap (hT' : AnalyticTriple.BOClass s (T.pullback h hh))
    {W : Opens M} {W' : Opens N} (hWW' : ⇑h '' (W' : Set N) ⊆ W) :
    AnalyticTriple.BOClass s ((T.pullback (M.inclusion W)
      (isLocalDiffeomorph_inclusion M W)).pullback (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')) := by
  rw [triple_pullback_restrictMap_eq T h hh hWW']
  exact boClass_pullback_inclusion_of_boClass (T.pullback h hh) W' hT'

/-- The order clause of a state over `W'` for the pulled-back triple, read at the triple over `W`
pulled back along `h|_{W'}`. -/
theorem isOfOrderGe_triple_pullback_restrictMap {W : Opens M} {W' : Opens N}
    (hWW' : ⇑h '' (W' : Set N) ⊆ W) (st' : ChainState (T.pullback h hh) s W') :
    st'.L.toSuccession.IsOfOrderGe ((T.pullback (M.inclusion W)
      (isLocalDiffeomorph_inclusion M W)).pullback (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).I s
      ((T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).pullback
        (AnalyticMap.restrictMap h W' W hWW')
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).F.idealSheaf := by
  rw [triple_pullback_restrictMap_eq T h hh hWW']
  exact st'.hge

variable {T s} {W : Opens M} {W' : Opens N} (hWW' : ⇑h '' (W' : Set N) ⊆ W)
  {V : Opens M} (hVW : closure (V : Set M) ⊆ W) {V' : Opens N} (hV'W' : closure (V' : Set N) ⊆ W')
  (hVV' : ⇑h '' (V' : Set N) ⊆ V)

/-- The square of restrictions: `V ⊆ W` after `h|_{V'}` is `h|_{W'}` after `V' ⊆ W'`. -/
theorem restrictLE_comp_restrictMap :
    (M.restrictLE (le_of_closure_subset hVW)).comp (AnalyticMap.restrictMap h V' V hVV') =
      (AnalyticMap.restrictMap h W' W hWW').comp (N.restrictLE (le_of_closure_subset hV'W')) :=
  ContMDiffMap.ext fun _ => Subtype.ext rfl

/-- The two pull-backs of the sequence over `W` to `V'` agree (`e₀` of the transport). -/
theorem pullback_restrictLE_pullback_restrictMap (st : ChainState T s W) :
    (st.L.pullback (M.restrictLE (le_of_closure_subset hVW))
      (isLocalDiffeomorph_restrictLE _)).pullback (AnalyticMap.restrictMap h V' V hVV')
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV') =
      (st.L.pullback (AnalyticMap.restrictMap h W' W hWW')
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).pullback
        (N.restrictLE (le_of_closure_subset hV'W')) (isLocalDiffeomorph_restrictLE _) := by
  rw [AnalyticManifold.BlowUpSequence.pullback_comp, AnalyticManifold.BlowUpSequence.pullback_comp]
  exact AnalyticManifold.BlowUpSequence.pullback_congr _
    (restrictLE_comp_restrictMap h hWW' hVW hV'W' hVV') _ _

/-- The relation of the sequences over `W'` and `W` restricts to `V'` (`hA` of the transport). -/
theorem eraseEmpty_pullback_restrictLE (st : ChainState T s W)
    (st' : ChainState (T.pullback h hh) s W')
    (hrel : st'.L.eraseEmpty = (st.L.pullback (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).eraseEmpty) :
    (st'.L.pullback (N.restrictLE (le_of_closure_subset hV'W'))
      (isLocalDiffeomorph_restrictLE _)).eraseEmpty =
      ((st.L.pullback (AnalyticMap.restrictMap h W' W hWW')
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).pullback
        (N.restrictLE (le_of_closure_subset hV'W'))
        (isLocalDiffeomorph_restrictLE _)).eraseEmpty := by
  rw [← AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty st'.L _
      (isLocalDiffeomorph_restrictLE _), hrel,
    AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty]

/-- **The relation "the sequence over `W'` with the empty blow-ups deleted is the pull-back of the
sequence over `W` with the empty blow-ups deleted" is kept by the shrink-and-append step** with
values `F'` over `W'` and `F` over `W`, for smaller opens `V ⊆ W`, `V' ⊆ W'` with `h(V') ⊆ V`, as
soon as the two values agree after pulling back to the common cleaned last stage of the
restricted sequences (`hF`, for the identifications `pullback_restrictLE_pullback_restrictMap`
and `eraseEmpty_pullback_restrictLE`). The algebra of sequences is
`shrinkAppend_eraseEmpty_pullback`. -/
theorem shrinkAppend_rel_of_value_rel (st : ChainState T s W)
    (st' : ChainState (T.pullback h hh) s W')
    (hrel : st'.L.eraseEmpty = (st.L.pullback (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).eraseEmpty)
    (F : AnalyticManifold.BlowUpSequence ψ₀ ((st.L.stage (Fin.last _)).restrict
      (st.L.liftRange (M.restrictLE (le_of_closure_subset hVW)) (isLocalDiffeomorph_restrictLE _))))
    (F' : AnalyticManifold.BlowUpSequence ψ₀ ((st'.L.stage (Fin.last _)).restrict
      (st'.L.liftRange (N.restrictLE (le_of_closure_subset hV'W'))
        (isLocalDiffeomorph_restrictLE _))))
    (hF : ∀ (hκ₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
        ((st'.L.liftCorestrict (N.restrictLE (le_of_closure_subset hV'W'))
          (isLocalDiffeomorph_restrictLE _)).comp (Diffeomorph.toAnalyticMap
          (st'.L.pullback (N.restrictLE (le_of_closure_subset hV'W'))
            (isLocalDiffeomorph_restrictLE _)).eraseEmptyLast.symm)))
      (hκ₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
        (((st.L.liftCorestrict (M.restrictLE (le_of_closure_subset hVW))
            (isLocalDiffeomorph_restrictLE _)).comp
          ((st.L.pullback (M.restrictLE (le_of_closure_subset hVW))
            (isLocalDiffeomorph_restrictLE _)).pullbackLiftLast
            (AnalyticMap.restrictMap h V' V hVV')
            (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV'))).comp
          (Diffeomorph.toAnalyticMap ((AnalyticManifold.BlowUpSequence.stageOfEq
            (pullback_restrictLE_pullback_restrictMap h hh hWW' hVW hV'W' hVV' st)).trans
            (((st.L.pullback (AnalyticMap.restrictMap h W' W hWW')
              (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).pullback
              (N.restrictLE (le_of_closure_subset hV'W'))
              (isLocalDiffeomorph_restrictLE _)).eraseEmptyLast.trans
              (AnalyticManifold.BlowUpSequence.stageOfEq
                (eraseEmpty_pullback_restrictLE h hh hWW' hV'W' st st' hrel).symm))).symm))),
      (F'.pullback _ hκ₂).eraseEmpty = (F.pullback _ hκ₁).eraseEmpty) :
    (st'.L.shrinkAppend (N.restrictLE (le_of_closure_subset hV'W'))
      (isLocalDiffeomorph_restrictLE _) F').eraseEmpty =
    ((st.L.shrinkAppend (M.restrictLE (le_of_closure_subset hVW))
      (isLocalDiffeomorph_restrictLE _) F).pullback (AnalyticMap.restrictMap h V' V hVV')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV')).eraseEmpty :=
  AnalyticManifold.BlowUpSequence.shrinkAppend_eraseEmpty_pullback st.L st'.L _ _ _ _ _ _ _ _ F F'
    (pullback_restrictLE_pullback_restrictMap h hh hWW' hVW hV'W' hVV' st)
    (eraseEmpty_pullback_restrictLE h hh hWW' hV'W' st st' hrel)
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftCorestrict _ _ _)
      (Diffeomorph.isLocalDiffeomorph _))
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftCorestrict _ _ _)
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _))
      (Diffeomorph.isLocalDiffeomorph _))
    (hF _ _)

end ChainState

end Hironaka.Manifold
