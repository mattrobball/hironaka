/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.ValueTransport
public import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
import Hironaka.Resolution.Analytic.OrderReduction.ChainTransportPrep
import Hironaka.Resolution.Analytic.OrderReduction.InducedValue
import Hironaka.Resolution.Analytic.OrderReduction.Modified.InducedConcat
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Transport of one link of the chain of Step 2.1

The second clause of [Kol07, 34.1] (the value on a pull-back is the pull-back of the value with
the empty blow-ups deleted) and the compatibility of [Wlo09, Theorem 2.0.3 (4)], for the chain of
Step 2.1 of the proof of [Kol07, Theorem 103] in the compatible-family form (`Step21Fam.lean`):
along a local analytic isomorphism `h : N → M` carrying an open `W' ⊆ N` into `W ⊆ M`, a chain
state over `W'` for the pulled-back triple and a chain state over `W` whose sequences agree **up to
empty blow-ups after pulling back** keep that relation through one link (the same member `j`,
smaller opens `V' ⊆ W'`, `V ⊆ W` with `h(V') ⊆ V`).

This is an instance of the general transport of a link along a value functor
(`ValueTransport.lean`), for the value functor "the family of one boundary member `bd` read at the
induced triple of the sequence, at the member's index" (`ChainState.linkValue`):

* `BDanFamData.fam_seqOn_induced_pullback_liftRange` — the value functor commutes with local
  analytic isomorphisms, on the reading opens (`fam_seqOn_induced_pullback` on the image open, then
  the family's `compat`);
* `BDanFamData.linkValue_rel` — the comparison of the two appended values,
  `BlowUpSequence.valueTransport_rel` with the naturality of the value functor supplied by
  `fam_seqOn_induced_eraseEmpty` (it ignores empty blow-ups), `fam_seqOn_induced_pullback_liftRange`
  and `fam_seqOn_induced_pullback_congr` (a substitution);
* `ChainState.link_rel` — the relation is kept by one link (`ChainState.link`),
  `ChainState.shrinkAppend_rel_of_value_rel` with the two values compared by `linkValue_rel` after
  reading the value over `W'` at the pulled-back triple (`fam_seqOn_congr`).

The transport is applied to two chains of opens over the same manifold in `ChainIndep.lean` and
along a local analytic isomorphism in `Step21FamIndep.lean`.
-/

@[expose] public section

universe u

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace BDanFamData

open _root_.Manifold

variable [FiniteDimensional 𝕜 E] {s : ℕ} (bd : BDanFamData ψ₀ s)
  {M N P Q : AnalyticManifold.{u} 𝕜 E} (T₁ : AnalyticTriple ψ₀ M)
  (hT₁ : AnalyticTriple.BOClass s T₁) (hW : AnalyticMap N M)
  (hhW : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω hW)
  (hT₂ : AnalyticTriple.BOClass s (T₁.pullback hW hhW)) (L₁ : AnalyticManifold.BlowUpSequence ψ₀ M)
  (hL₁ : L₁.toSuccession.IsOfOrderGe T₁.I s T₁.F.idealSheaf) (j : T₁.F.ι)
  (ρ : AnalyticMap P M) (hρ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ)
  (ρ' : AnalyticMap Q N) (hρ' : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ')
  (hV : AnalyticMap Q P) (hhV : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω hV)
  (hsq : ρ.comp hV = hW.comp ρ')

/-- **The value at the pulled-back sequence is the value at the sequence pulled back along the
lift**, on the reading opens: the family's value at the induced triple of `hW^* L₁` on the reading
open of `ρ'` is the value at the induced triple of `L₁` on the reading open of `ρ`, pulled back
along the restricted last-stage lift, with the empty blow-ups deleted
(`fam_seqOn_induced_pullback` on the image open, then the family's `compat` to the reading open of
`ρ`). -/
theorem fam_seqOn_induced_pullback_liftRange
    (hO₁ : IsCompact (closure (L₁.liftRange ρ hρ : Set (L₁.stage (Fin.last _)))))
    (hOP : IsCompact (closure ((L₁.pullback hW hhW).liftRange ρ' hρ' :
      Set ((L₁.pullback hW hhW).stage (Fin.last _))))) :
    (((bd.fam (T₁.induced s L₁ hL₁) (AnalyticTriple.boClass_induced T₁ s L₁ hL₁ hT₁)
        (L₁.toSuccession.originalIdx T₁.F (Fin.last _) j)).seqOn (L₁.liftRange ρ hρ) hO₁).pullback
      (AnalyticMap.restrictMap (L₁.pullbackLiftLast hW hhW) ((L₁.pullback hW hhW).liftRange ρ' hρ')
        (L₁.liftRange ρ hρ)
        (AnalyticManifold.BlowUpSequence.image_liftRange_pullbackLiftLast_subset L₁ hW hhW ρ hρ ρ'
            hρ' hV hsq))
      (AnalyticMap.isLocalDiffeomorph_restrictMap
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L₁ hW hhW) _ _
            _)).eraseEmpty =
    (bd.fam ((T₁.pullback hW hhW).induced s (L₁.pullback hW hhW)
        (AnalyticTriple.isOfOrderGe_pullback T₁ s L₁ hL₁ hW hhW))
      (AnalyticTriple.boClass_induced _ s (L₁.pullback hW hhW)
        (AnalyticTriple.isOfOrderGe_pullback T₁ s L₁ hL₁ hW hhW) hT₂)
      ((L₁.pullback hW hhW).toSuccession.originalIdx (T₁.pullback hW hhW).F (Fin.last _) j)).seqOn
      ((L₁.pullback hW hhW).liftRange ρ' hρ') hOP := by
  have hB := bd.fam_seqOn_induced_pullback T₁ hT₁ L₁ hL₁ j hW hhW hT₂
    (AnalyticTriple.isOfOrderGe_pullback T₁ s L₁ hL₁ hW hhW)
    ((L₁.pullback hW hhW).liftRange ρ' hρ') hOP
  have hle : AnalyticMap.imageOpens (L₁.pullbackLiftLast hW hhW)
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L₁ hW hhW)
      ((L₁.pullback hW hhW).liftRange ρ' hρ') ≤ L₁.liftRange ρ hρ := fun _ hx =>
    AnalyticManifold.BlowUpSequence.image_liftRange_pullbackLiftLast_subset L₁ hW hhW ρ hρ ρ' hρ'
        hV hsq hx
  have hC := (bd.fam (T₁.induced s L₁ hL₁) (AnalyticTriple.boClass_induced T₁ s L₁ hL₁ hT₁)
    (L₁.toSuccession.originalIdx T₁.F (Fin.last _) j)).compat _ _
    (AnalyticMap.isCompact_closure_image (L₁.pullbackLiftLast hW hhW) hOP) hO₁ hle
  have hmaps : ((L₁.stage (Fin.last _)).restrictLE hle).comp
      (AnalyticMap.restrictMap (L₁.pullbackLiftLast hW hhW)
        ((L₁.pullback hW hhW).liftRange ρ' hρ') _ Set.Subset.rfl) =
      AnalyticMap.restrictMap (L₁.pullbackLiftLast hW hhW) ((L₁.pullback hW hhW).liftRange ρ' hρ')
        (L₁.liftRange ρ hρ)
        (AnalyticManifold.BlowUpSequence.image_liftRange_pullbackLiftLast_subset L₁ hW hhW ρ hρ ρ'
            hρ' hV hsq) :=
    ContMDiffMap.ext fun _ => Subtype.ext rfl
  rw [hB, hC, AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
    AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _,
    AnalyticManifold.BlowUpSequence.pullback_congr _ hmaps]

include hsq in
/-- **The comparison of the two appended values**, the heart of the transport of the chain: for
sequences `L₂` on `N` and `L₁` on `M` which agree, with the empty blow-ups deleted, after pulling
`L₁` back along `hW`, the family's value at the induced triple of `L₂` on the reading open of `ρ'`
and its value at the induced triple of `L₁` on the reading open of `ρ`, both pulled back to the
common last stage of the restricted sequences and with the empty blow-ups deleted, agree. The
general `valueTransport_rel` with the naturality of the value functor:
`fam_seqOn_induced_eraseEmpty` (both are the value at the induced triple of the common cleaned
sequence), `fam_seqOn_induced_pullback_liftRange` (on the `L₁` side) and
`fam_seqOn_induced_pullback_congr` (the substitution along `hrel`). -/
theorem linkValue_rel (L₂ : AnalyticManifold.BlowUpSequence ψ₀ N)
    (hL₂ : L₂.toSuccession.IsOfOrderGe (T₁.pullback hW hhW).I s (T₁.pullback hW hhW).F.idealSheaf)
    (hrel : L₂.eraseEmpty = (L₁.pullback hW hhW).eraseEmpty)
    (hO₁ : IsCompact (closure (L₁.liftRange ρ hρ : Set (L₁.stage (Fin.last _)))))
    (hO₂ : IsCompact (closure (L₂.liftRange ρ' hρ' : Set (L₂.stage (Fin.last _)))))
    (hρ'c : IsCompact (closure (Set.range ρ')))
    (e₀ : (L₁.pullback ρ hρ).pullback hV hhV = (L₁.pullback hW hhW).pullback ρ' hρ')
    (hA : (L₂.pullback ρ' hρ').eraseEmpty = ((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmpty)
    (hκ₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      ((L₂.liftCorestrict ρ' hρ').comp
        (Diffeomorph.toAnalyticMap (L₂.pullback ρ' hρ').eraseEmptyLast.symm)))
    (hκ₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      (((L₁.liftCorestrict ρ hρ).comp ((L₁.pullback ρ hρ).pullbackLiftLast hV hhV)).comp
        (Diffeomorph.toAnalyticMap ((AnalyticManifold.BlowUpSequence.stageOfEq e₀).trans
          (((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.trans
            (AnalyticManifold.BlowUpSequence.stageOfEq hA.symm))).symm))) :
    (((bd.fam ((T₁.pullback hW hhW).induced s L₂ hL₂)
          (AnalyticTriple.boClass_induced _ s L₂ hL₂ hT₂)
          (L₂.toSuccession.originalIdx (T₁.pullback hW hhW).F (Fin.last _) j)).seqOn
        (L₂.liftRange ρ' hρ') hO₂).pullback
      ((L₂.liftCorestrict ρ' hρ').comp
        (Diffeomorph.toAnalyticMap (L₂.pullback ρ' hρ').eraseEmptyLast.symm)) hκ₂).eraseEmpty =
    (((bd.fam (T₁.induced s L₁ hL₁) (AnalyticTriple.boClass_induced T₁ s L₁ hL₁ hT₁)
          (L₁.toSuccession.originalIdx T₁.F (Fin.last _) j)).seqOn (L₁.liftRange ρ hρ) hO₁).pullback
      (((L₁.liftCorestrict ρ hρ).comp ((L₁.pullback ρ hρ).pullbackLiftLast hV hhV)).comp
        (Diffeomorph.toAnalyticMap ((AnalyticManifold.BlowUpSequence.stageOfEq e₀).trans
          (((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.trans
            (AnalyticManifold.BlowUpSequence.stageOfEq hA.symm))).symm)) hκ₁).eraseEmpty := by
  -- the pulled-back list, its order clause and its reading open
  have hP : (L₁.pullback hW hhW).toSuccession.IsOfOrderGe (T₁.pullback hW hhW).I s
      (T₁.pullback hW hhW).F.idealSheaf := AnalyticTriple.isOfOrderGe_pullback T₁ s L₁ hL₁ hW hhW
  have hOP : IsCompact (closure ((L₁.pullback hW hhW).liftRange ρ' hρ' :
      Set ((L₁.pullback hW hhW).stage (Fin.last _)))) :=
    (L₁.pullback hW hhW).isCompact_closure_liftRange ρ' hρ' hρ'c
  exact AnalyticManifold.BlowUpSequence.valueTransport_rel L₁ L₂ hW hhW ρ hρ ρ' hρ' hV hhV hsq e₀
    hA hκ₂ hκ₁
    (bd.fam_seqOn_induced_eraseEmpty (T₁.pullback hW hhW) hT₂ L₂ hL₂ j (L₂.liftRange ρ' hρ') hO₂)
    (bd.fam_seqOn_induced_eraseEmpty (T₁.pullback hW hhW) hT₂ (L₁.pullback hW hhW) hP j
      ((L₁.pullback hW hhW).liftRange ρ' hρ') hOP)
    (bd.fam_seqOn_induced_pullback_liftRange T₁ hT₁ hW hhW hT₂ L₁ hL₁ j ρ hρ ρ' hρ' hV hsq hO₁ hOP)
    fun hf₁ hf₂ => bd.fam_seqOn_induced_pullback_congr hT₂ hrel _ _ j _ _
      (AnalyticManifold.BlowUpSequence.mem_imageOpens_eraseEmptyLast_liftRange_iff L₁ L₂ hW hhW ρ'
        hρ' hrel) _ _ hf₁ hf₂
      (AnalyticManifold.BlowUpSequence.stageOfEq_eraseEmptyLast_liftCorestrict_apply L₁ L₂ hW hhW
        ρ' hρ' hrel hA hκ₂)

end BDanFamData

namespace ChainState

open _root_.Manifold

variable [FiniteDimensional 𝕜 E] {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (s : ℕ)
  (bd : BDanFamData ψ₀ s) (hT : AnalyticTriple.BOClass s T)

/-- The value appended by one link of the chain of Step 2.1: the family read at the induced triple
of the state's sequence, at the member's index, on the reading open (the local definitions of
`ChainState.link`). -/
noncomputable def linkValue {W : Opens M} (st : ChainState T s W) (j : T.F.ι) {V : Opens M}
    (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W) :
    AnalyticManifold.BlowUpSequence ψ₀ ((st.L.stage (Fin.last _)).restrict
      (st.L.liftRange (M.restrictLE (le_of_closure_subset hVW))
        (isLocalDiffeomorph_restrictLE _))) :=
  (bd.fam ((T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).induced s st.L st.hge)
    (AnalyticTriple.boClass_induced _ s st.L st.hge (boClass_pullback_inclusion_of_boClass T W hT))
    (st.L.toSuccession.originalIdx
      (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).F (Fin.last _) j)).seqOn
    (st.L.liftRange (M.restrictLE (le_of_closure_subset hVW)) (isLocalDiffeomorph_restrictLE _))
    (st.L.isCompact_closure_liftRange (M.restrictLE (le_of_closure_subset hVW))
      (isLocalDiffeomorph_restrictLE _)
      (isCompact_closure_range_restrictLE (le_of_closure_subset hVW) hV hVW))

omit [FiniteDimensional 𝕜 E] in
/-- One link is the shrink-and-append step with the link's value. -/
theorem link_L {W : Opens M} (st : ChainState T s W) (j : T.F.ι) {V : Opens M}
    (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W) :
    (st.link T s bd hT j hV hVW).L =
      st.L.shrinkAppend (M.restrictLE (le_of_closure_subset hVW)) (isLocalDiffeomorph_restrictLE _)
        (linkValue T s bd hT st j hV hVW) := rfl

variable (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
  (hT' : AnalyticTriple.BOClass s (T.pullback h hh))

/-- The second clause of [Kol07, 34.1] for one link of the chain of Step 2.1: **the relation "the
sequence over `W'` with the empty blow-ups deleted is the pull-back of the sequence over `W` with
the empty blow-ups deleted" along a local analytic isomorphism `h` with `h(W') ⊆ W` is kept by one
link** at a member `j`, for smaller opens `V ⊆ W`, `V' ⊆ W'` with `h(V') ⊆ V`. The general
`shrinkAppend_rel_of_value_rel`, the two appended values compared by `linkValue_rel` (the family's
`commutesWithLocalIsos` and `compat` at the induced triples, the common sequence, the uniqueness of
maps over the blow-down) after reading the value over `W'` at the pulled-back triple
(`triple_pullback_restrictMap_eq`, `fam_seqOn_congr`). -/
theorem link_rel {W : Opens M} {W' : Opens N} (hWW' : ⇑h '' (W' : Set N) ⊆ W)
    (st : ChainState T s W) (st' : ChainState (T.pullback h hh) s W')
    (hrel : st'.L.eraseEmpty = (st.L.pullback (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).eraseEmpty) (j : T.F.ι)
    {V : Opens M} (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W)
    {V' : Opens N} (hV' : IsCompact (closure (V' : Set N))) (hV'W' : closure (V' : Set N) ⊆ W')
    (hVV' : ⇑h '' (V' : Set N) ⊆ V) :
    (st'.link (T.pullback h hh) s bd hT' j hV' hV'W').L.eraseEmpty =
      ((st.link T s bd hT j hV hVW).L.pullback (AnalyticMap.restrictMap h V' V hVV')
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV')).eraseEmpty := by
  have hTWeq := triple_pullback_restrictMap_eq T h hh hWW'
  have hT₂ := boClass_triple_pullback_restrictMap T s h hh hT' hWW'
  have hL₂ := isOfOrderGe_triple_pullback_restrictMap T s h hh hWW' st'
  -- the link's value over `W'`, read at the pulled-back triple
  have hF₂ : linkValue (T.pullback h hh) s bd hT' st' j hV' hV'W' =
      (bd.fam (((T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).pullback
          (AnalyticMap.restrictMap h W' W hWW')
          (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).induced s st'.L hL₂)
        (AnalyticTriple.boClass_induced _ s st'.L hL₂ hT₂)
        (st'.L.toSuccession.originalIdx ((T.pullback (M.inclusion W)
          (isLocalDiffeomorph_inclusion M W)).pullback (AnalyticMap.restrictMap h W' W hWW')
          (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).F (Fin.last _) j)).seqOn
        (st'.L.liftRange (N.restrictLE (le_of_closure_subset hV'W'))
          (isLocalDiffeomorph_restrictLE _))
        (st'.L.isCompact_closure_liftRange (N.restrictLE (le_of_closure_subset hV'W'))
          (isLocalDiffeomorph_restrictLE _)
          (isCompact_closure_range_restrictLE (le_of_closure_subset hV'W') hV' hV'W')) :=
    bd.fam_seqOn_congr (AnalyticTriple.induced_congr hTWeq.symm s st'.L st'.hge hL₂) _ _ _ _
      (AnalyticManifold.FiniteSuccession.heq_originalIdx_congr st'.L.toSuccession
        (congrArg AnalyticTriple.F hTWeq.symm) _ HEq.rfl) _ _
  refine (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
      (link_L (T.pullback h hh) s bd hT' st' j hV' hV'W')).trans
    ((shrinkAppend_rel_of_value_rel h hh hWW' hVW hV'W' hVV' st st' hrel
      (linkValue T s bd hT st j hV hVW) (linkValue (T.pullback h hh) s bd hT' st' j hV' hV'W')
      fun hκ₂ hκ₁ => ?_).trans
      (congrArg (fun X : AnalyticManifold.BlowUpSequence ψ₀ (M.restrict V) => (X.pullback
        (AnalyticMap.restrictMap h V' V hVV')
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV')).eraseEmpty)
        (link_L T s bd hT st j hV hVW)).symm)
  exact (congrArg (fun X : AnalyticManifold.BlowUpSequence ψ₀ ((st'.L.stage
      (Fin.last _)).restrict
      (st'.L.liftRange (N.restrictLE (le_of_closure_subset hV'W'))
        (isLocalDiffeomorph_restrictLE _))) => (X.pullback
          ((st'.L.liftCorestrict (N.restrictLE (le_of_closure_subset hV'W'))
            (isLocalDiffeomorph_restrictLE _)).comp (Diffeomorph.toAnalyticMap
            (st'.L.pullback (N.restrictLE (le_of_closure_subset hV'W'))
              (isLocalDiffeomorph_restrictLE _)).eraseEmptyLast.symm)) hκ₂).eraseEmpty) hF₂).trans
    (bd.linkValue_rel (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W))
      (boClass_pullback_inclusion_of_boClass T W hT) (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW') hT₂ st.L st.hge j
      (M.restrictLE (le_of_closure_subset hVW)) (isLocalDiffeomorph_restrictLE _)
      (N.restrictLE (le_of_closure_subset hV'W')) (isLocalDiffeomorph_restrictLE _)
      (AnalyticMap.restrictMap h V' V hVV')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV')
      (restrictLE_comp_restrictMap h hWW' hVW hV'W' hVV') st'.L hL₂ hrel
      (st.L.isCompact_closure_liftRange (M.restrictLE (le_of_closure_subset hVW))
        (isLocalDiffeomorph_restrictLE _)
        (isCompact_closure_range_restrictLE (le_of_closure_subset hVW) hV hVW))
      (st'.L.isCompact_closure_liftRange (N.restrictLE (le_of_closure_subset hV'W'))
        (isLocalDiffeomorph_restrictLE _)
        (isCompact_closure_range_restrictLE (le_of_closure_subset hV'W') hV' hV'W'))
      (isCompact_closure_range_restrictLE (le_of_closure_subset hV'W') hV' hV'W')
      (pullback_restrictLE_pullback_restrictMap h hh hWW' hVW hV'W' hVV' st)
      (eraseEmpty_pullback_restrictLE h hh hWW' hV'W' st st' hrel) hκ₂ hκ₁)

end ChainState

end Hironaka.Manifold
