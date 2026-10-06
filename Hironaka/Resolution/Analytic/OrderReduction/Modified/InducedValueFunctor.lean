/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.ValueTransport
public import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
public import Hironaka.Resolution.Analytic.Functor.EraseEmptyOrder
public import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Hironaka.Resolution.Analytic.OrderReduction.FamilyIndependence
import Hironaka.Resolution.Analytic.OrderReduction.Step21Functoriality
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The value of a family functor at induced triples: the transport lemmas

The transport identities for the value of a family read at the induced triple of a list
(`InducedValue.lean`, `ChainTransportPrep.lean`, `ChainTransport.lean`; the functoriality argument
in the proof of [Kol07, Lemma 102], the empty blow-up convention [Kol07, 32], its counterpart for
boundary members, and the second condition of [Kol07, 34.1]), restated for an arbitrary family
functor `B : AnalyticFamilyFunctor ψ₀
Dom` with the two naturality properties (`CommutesWithLocalIsos`, `IndifferentToEmptyMembers`), the
class proofs of the induced triples taken as hypotheses. The versions of those three modules are for
the family of one boundary member `BDanFamData` on the class `BOClass s`, whose class proofs come
from
`boClass_induced`; the descent of the rounds on the nonmonomial part reads the order reduction at
the nonmonomial triple of the induced triple (`nonmonomialFunctor`), whose class proof is the
invariant of the descent and not a closure property, hence the hypotheses.

* `seqOn_induced_pullback`: the value at the induced triple of a pulled-back list is the value at
  the induced triple of the list, pulled back along the lift of the last stages and cleaned of empty
  blow-ups (`induced_pullback` and `commutesWithLocalIsos`);
* `induced_eq_pullback_induced_eraseEmpty`, `isEmptyExtension_eraseEmptyIdx_induced`: the induced
  triple of a list is the induced triple of the cleaned list pulled back along `eraseEmptyLast`, up
  to the empty boundary members (`markedTransformSeq_last_eraseEmpty`, `eraseEmptyIdx`);
* `seqOn_induced_eraseEmpty`: hence the value at the induced triple of a list is the value at the
  induced triple of the cleaned list, transported (`indifferentToEmptyMembers`,
  `commutesWithLocalIsos`);
* `seqOn_induced_pullback_liftRange`, `seqOn_induced_pullback_congr`, `inducedValue_rel`: the forms
  on reading opens, and the comparison of the two appended values of one link of a chain (the heart
  of `linkValue_rel`), for `B`.

The value identities are the proofs of the corresponding statements of `InducedValue.lean` and
`ChainTransport.lean` with the family replaced. The comparison of the two appended values is an
instance of the general transport of a link along a value functor (`ValueTransport.lean`):
`inducedValue_rel` is `BlowUpSequence.valueTransport_rel` with the naturality of the value functor
"`B` at the induced triple" supplied by `seqOn_induced_eraseEmpty`,
`seqOn_induced_pullback_liftRange` and `seqOn_induced_pullback_congr`.
-/

@[expose] public section

universe u

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- A class of triples closed under pull-back along local analytic isomorphisms (the class of
[Kol07, Lemma 102] has this property; here it is a hypothesis of the transport lemmas). -/
def ClassPullbackClosed (Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop) :
    Prop :=
  ∀ {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g), Dom T → Dom (T.pullback g hg)

end Hironaka.Manifold

namespace Manifold.AnalyticTriple

open _root_.Manifold
open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The induced triple of a cleaned list -/

variable {M : AnalyticManifold.{u} 𝕜 E} (TW : AnalyticTriple ψ₀ M) (s : ℕ)
    (L : AnalyticManifold.BlowUpSequence ψ₀ M)
  (hL : L.toSuccession.IsOfOrderGe TW.I s TW.F.idealSheaf)
  (hLe : L.eraseEmpty.toSuccession.IsOfOrderGe TW.I s TW.F.idealSheaf)

/-- **The induced triple of a list is the induced triple of the cleaned list pulled back along
`eraseEmptyLast`, up to the empty boundary members** ([Kol07, 32] and its counterpart for boundary
members): the ideal by
`markedTransformSeq_last_eraseEmpty`, the boundary replaced by the pulled-back boundary of the
cleaned list (the triple form of `fam_seqOn_induced_eraseEmpty`). -/
theorem induced_eq_pullback_induced_eraseEmpty :
    (⟨(TW.induced s L hL).I, (TW.induced s L hL).isNonzeroEverywhere,
      (TW.induced s L.eraseEmpty hLe).F.comap ⇑(Diffeomorph.toAnalyticMap L.eraseEmptyLast),
      HypersurfaceFamily.isSnc_comap (TW.induced s L.eraseEmpty hLe).isSnc _
        L.eraseEmptyLast.isLocalDiffeomorph⟩ : AnalyticTriple ψ₀ (L.stage (Fin.last _))) =
      (TW.induced s L.eraseEmpty hLe).pullback (Diffeomorph.toAnalyticMap L.eraseEmptyLast)
        L.eraseEmptyLast.isLocalDiffeomorph := by
  refine AnalyticTriple.ext' ?_ rfl
  change L.toSuccession.markedTransformSeq TW.I s (Fin.last _) =
    (L.eraseEmpty.toSuccession.markedTransformSeq TW.I s (Fin.last _)).pullback _
        (Diffeomorph.toAnalyticMap L.eraseEmptyLast).contMDiff
  rw [AnalyticManifold.BlowUpSequence.markedTransformSeq_last_eraseEmpty L TW.I TW.F.idealSheaf s
      hL]
  exact (comap_symm_comap L.eraseEmptyLast.symm
    (L.toSuccession.markedTransformSeq TW.I s (Fin.last _))).symm

/-- The boundary of the induced triple is an empty extension of the pulled-back boundary of the
induced triple of the cleaned list, along `eraseEmptyIdx` ([Kol07, 32] and its counterpart for
boundary members). -/
theorem isEmptyExtension_eraseEmptyIdx_induced :
    HypersurfaceFamily.IsEmptyExtension
      (G := (TW.induced s L.eraseEmpty hLe).F.comap ⇑(Diffeomorph.toAnalyticMap L.eraseEmptyLast))
      (G' := (TW.induced s L hL).F)
      (AnalyticManifold.BlowUpSequence.eraseEmptyIdx L TW.F fun k => (TW.isSnc.1 k).isClosed) := by
  have hF : ∀ k, IsClosed (TW.F.hyp k) := fun k => (TW.isSnc.1 k).isClosed
  refine ⟨fun i => ?_,
    fun b hb => AnalyticManifold.BlowUpSequence.hyp_eq_empty_of_notMem_range_eraseEmptyIdx L TW.F
        hF b hb⟩
  change (L.toSuccession.totalTransformSeqFrom TW.F (Fin.last _)).hyp
      (AnalyticManifold.BlowUpSequence.eraseEmptyIdx L TW.F hF i) =
    ⇑L.eraseEmptyLast ⁻¹' (L.eraseEmpty.toSuccession.totalTransformSeqFrom TW.F (Fin.last _)).hyp i
  rw [← AnalyticManifold.BlowUpSequence.hyp_eraseEmptyIdx L TW.F hF i]
  exact (L.eraseEmptyLast.toEquiv.preimage_symm_preimage _).symm

end Manifold.AnalyticTriple

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace AnalyticFamilyFunctor

open _root_.Manifold

variable {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
  (B : AnalyticFamilyFunctor ψ₀ Dom)

/-! ### Transport of the class proofs -/

/-- The class proof of an induced triple transports along an equality of lists (a substitution). -/
theorem dom_induced_of_eq {M : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M} {s : ℕ}
    {L₁ L₂ : AnalyticManifold.BlowUpSequence ψ₀ M} (e : L₁ = L₂)
        (hL₁ : L₁.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)
    (hL₂ : L₂.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf) (hD : Dom (T.induced s L₁ hL₁)) :
    Dom (T.induced s L₂ hL₂) := by
  subst e
  exact hD

/-- A class closed under pull-back contains the induced triple of a pulled-back list when it
contains the induced triple of the list (`induced_pullback`). -/
theorem dom_induced_pullback (hDom : ClassPullbackClosed (ψ₀ := ψ₀) Dom)
    {M N : AnalyticManifold.{u} 𝕜 E} (TW : AnalyticTriple ψ₀ M) (s : ℕ)
        (L : AnalyticManifold.BlowUpSequence ψ₀ M)
    (hL : L.toSuccession.IsOfOrderGe TW.I s TW.F.idealSheaf) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (hL' : (L.pullback h hh).toSuccession.IsOfOrderGe (TW.pullback h hh).I s
      (TW.pullback h hh).F.idealSheaf) (hD : Dom (TW.induced s L hL)) :
    Dom ((TW.pullback h hh).induced s (L.pullback h hh) hL') := by
  rw [← AnalyticTriple.induced_pullback TW s L hL h hh hL']
  exact hDom _ _ _ hD

/-! ### The two value identities -/

/-- **The value at the induced triple of a pulled-back list is the value at the induced triple of
the list on the image, pulled back along the lift of the last stages** (`induced_pullback`, the
functor's `commutesWithLocalIsos`); the functoriality argument in the proof of [Kol07, Lemma 102],
that pull-back and restriction commute. The form of `fam_seqOn_induced_pullback` for `B`. -/
theorem seqOn_induced_pullback (hB : B.CommutesWithLocalIsos)
    {M N : AnalyticManifold.{u} 𝕜 E} (TW : AnalyticTriple ψ₀ M) (s : ℕ)
        (L : AnalyticManifold.BlowUpSequence ψ₀ M)
    (hL : L.toSuccession.IsOfOrderGe TW.I s TW.F.idealSheaf) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (hL' : (L.pullback h hh).toSuccession.IsOfOrderGe (TW.pullback h hh).I s
      (TW.pullback h hh).F.idealSheaf) (hD : Dom (TW.induced s L hL))
    (hD' : Dom ((TW.pullback h hh).induced s (L.pullback h hh) hL'))
    (U' : Opens ((L.pullback h hh).stage (Fin.last _)))
    (hU' : IsCompact (closure (U' : Set ((L.pullback h hh).stage (Fin.last _))))) :
    (B.fam ((TW.pullback h hh).induced s (L.pullback h hh) hL') hD').seqOn U' hU' =
    (((B.fam (TW.induced s L hL) hD).seqOn
        (AnalyticMap.imageOpens (L.pullbackLiftLast h hh)
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L h hh) U')
        (AnalyticMap.isCompact_closure_image _ hU')).pullback
      (AnalyticMap.restrictMap (L.pullbackLiftLast h hh) U' _ Set.Subset.rfl)
      (AnalyticMap.isLocalDiffeomorph_restrictMap
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L h hh) U' _
        Set.Subset.rfl)).eraseEmpty := by
  have heq := (AnalyticTriple.induced_pullback TW s L hL h hh hL').symm
  have hpull : Dom ((TW.induced s L hL).pullback (L.pullbackLiftLast h hh)
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L h hh)) := by
    rw [← heq]
    exact hD'
  exact (B.fam_seqOn_congr_triple heq hD' hpull _ _).trans
    (hB (TW.induced s L hL) _ (L.pullbackLiftLast h hh)
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L h hh)
      (AnalyticTriple.isPullbackOf_pullback _ _ _) hD hpull U' hU')

/-- **The value at the induced triple of a list is the value at the induced triple of the cleaned
list, transported along `eraseEmptyLast`** ([Kol07, 32] and its counterpart for boundary members;
the second condition of [Kol07, 34.1]):
`induced_eq_pullback_induced_eraseEmpty`, `isEmptyExtension_eraseEmptyIdx_induced`, the functor's
`indifferentToEmptyMembers` and `commutesWithLocalIsos`. The form of `fam_seqOn_induced_eraseEmpty`
for `B`. -/
theorem seqOn_induced_eraseEmpty (hB : B.CommutesWithLocalIsos)
    (hB' : B.IndifferentToEmptyMembers)
    {M : AnalyticManifold.{u} 𝕜 E} (TW : AnalyticTriple ψ₀ M) (s : ℕ)
        (L : AnalyticManifold.BlowUpSequence ψ₀ M)
    (hL : L.toSuccession.IsOfOrderGe TW.I s TW.F.idealSheaf)
    (hLe : L.eraseEmpty.toSuccession.IsOfOrderGe TW.I s TW.F.idealSheaf)
    (hD : Dom (TW.induced s L hL)) (hDe : Dom (TW.induced s L.eraseEmpty hLe))
    (hpull : Dom ((TW.induced s L.eraseEmpty hLe).pullback
      (Diffeomorph.toAnalyticMap L.eraseEmptyLast) L.eraseEmptyLast.isLocalDiffeomorph))
    (V : Opens (L.stage (Fin.last _))) (hV : IsCompact (closure (V : Set (L.stage (Fin.last _))))) :
    (B.fam (TW.induced s L hL) hD).seqOn V hV =
    (((B.fam (TW.induced s L.eraseEmpty hLe) hDe).seqOn
        (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap L.eraseEmptyLast)
          L.eraseEmptyLast.isLocalDiffeomorph V)
        (AnalyticMap.isCompact_closure_image _ hV)).pullback
      (AnalyticMap.restrictMap (Diffeomorph.toAnalyticMap L.eraseEmptyLast) V _ Set.Subset.rfl)
      (AnalyticMap.isLocalDiffeomorph_restrictMap L.eraseEmptyLast.isLocalDiffeomorph V _
        Set.Subset.rfl)).eraseEmpty := by
  have htriple := AnalyticTriple.induced_eq_pullback_induced_eraseEmpty TW s L hL hLe
  have hext := AnalyticTriple.isEmptyExtension_eraseEmptyIdx_induced TW s L hL hLe
  have hT' : Dom (⟨(TW.induced s L hL).I, (TW.induced s L hL).isNonzeroEverywhere,
      (TW.induced s L.eraseEmpty hLe).F.comap ⇑(Diffeomorph.toAnalyticMap L.eraseEmptyLast),
      HypersurfaceFamily.isSnc_comap (TW.induced s L.eraseEmpty hLe).isSnc _
        L.eraseEmptyLast.isLocalDiffeomorph⟩ : AnalyticTriple ψ₀ _) := by
    rw [htriple]
    exact hpull
  have hind := hB' (TW.induced s L hL) _ _ (AnalyticManifold.BlowUpSequence.eraseEmptyIdx L TW.F _)
      hext.1 hext.2 hD hT'
    V hV
  have hcomm := hB (TW.induced s L.eraseEmpty hLe) _ (Diffeomorph.toAnalyticMap L.eraseEmptyLast)
    L.eraseEmptyLast.isLocalDiffeomorph (AnalyticTriple.isPullbackOf_pullback _ _ _) hDe hpull V hV
  rw [hind]
  exact (B.fam_seqOn_congr_triple htriple hT' hpull V hV).trans hcomm

/-! ### The reading-open forms -/

variable {M N P Q : AnalyticManifold.{u} 𝕜 E} (T₁ : AnalyticTriple ψ₀ M)
  (s : ℕ) (hW : AnalyticMap N M) (hhW : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω hW)
  (L₁ : AnalyticManifold.BlowUpSequence ψ₀ M) (hL₁ : L₁.toSuccession.IsOfOrderGe T₁.I s
      T₁.F.idealSheaf)
  (hD₁ : Dom (T₁.induced s L₁ hL₁))
  (hDP : Dom ((T₁.pullback hW hhW).induced s (L₁.pullback hW hhW)
    (AnalyticTriple.isOfOrderGe_pullback T₁ s L₁ hL₁ hW hhW)))
  (ρ : AnalyticMap P M) (hρ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ)
  (ρ' : AnalyticMap Q N) (hρ' : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ')
  (hV : AnalyticMap Q P) (hhV : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω hV)
  (hsq : ρ.comp hV = hW.comp ρ')

/-- **The value at the pulled-back list is the value at the list pulled back along the lift**, on
the reading opens (`seqOn_induced_pullback` on the image open, then the compatibility of the value
to the reading open of `ρ`). The form of `fam_seqOn_induced_pullback_liftRange` for `B`. -/
theorem seqOn_induced_pullback_liftRange (hB : B.CommutesWithLocalIsos)
    (hO₁ : IsCompact (closure (L₁.liftRange ρ hρ : Set (L₁.stage (Fin.last _)))))
    (hOP : IsCompact (closure ((L₁.pullback hW hhW).liftRange ρ' hρ' :
      Set ((L₁.pullback hW hhW).stage (Fin.last _))))) :
    (((B.fam (T₁.induced s L₁ hL₁) hD₁).seqOn (L₁.liftRange ρ hρ) hO₁).pullback
      (AnalyticMap.restrictMap (L₁.pullbackLiftLast hW hhW) ((L₁.pullback hW hhW).liftRange ρ' hρ')
        (L₁.liftRange ρ hρ)
        (AnalyticManifold.BlowUpSequence.image_liftRange_pullbackLiftLast_subset L₁ hW hhW ρ hρ ρ'
            hρ' hV hsq))
      (AnalyticMap.isLocalDiffeomorph_restrictMap
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L₁ hW hhW) _ _
            _)).eraseEmpty =
    (B.fam ((T₁.pullback hW hhW).induced s (L₁.pullback hW hhW)
        (AnalyticTriple.isOfOrderGe_pullback T₁ s L₁ hL₁ hW hhW)) hDP).seqOn
      ((L₁.pullback hW hhW).liftRange ρ' hρ') hOP := by
  have hB1 := B.seqOn_induced_pullback hB T₁ s L₁ hL₁ hW hhW
    (AnalyticTriple.isOfOrderGe_pullback T₁ s L₁ hL₁ hW hhW) hD₁ hDP
    ((L₁.pullback hW hhW).liftRange ρ' hρ') hOP
  have hle : AnalyticMap.imageOpens (L₁.pullbackLiftLast hW hhW)
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L₁ hW hhW)
      ((L₁.pullback hW hhW).liftRange ρ' hρ') ≤ L₁.liftRange ρ hρ := fun _ hx =>
    AnalyticManifold.BlowUpSequence.image_liftRange_pullbackLiftLast_subset L₁ hW hhW ρ hρ ρ' hρ'
        hV hsq hx
  have hC := (B.fam (T₁.induced s L₁ hL₁) hD₁).compat _ _
    (AnalyticMap.isCompact_closure_image (L₁.pullbackLiftLast hW hhW) hOP) hO₁ hle
  have hmaps : ((L₁.stage (Fin.last _)).restrictLE hle).comp
      (AnalyticMap.restrictMap (L₁.pullbackLiftLast hW hhW)
        ((L₁.pullback hW hhW).liftRange ρ' hρ') _ Set.Subset.rfl) =
      AnalyticMap.restrictMap (L₁.pullbackLiftLast hW hhW) ((L₁.pullback hW hhW).liftRange ρ' hρ')
        (L₁.liftRange ρ hρ)
        (AnalyticManifold.BlowUpSequence.image_liftRange_pullbackLiftLast_subset L₁ hW hhW ρ hρ ρ'
            hρ' hV hsq) :=
    ContMDiffMap.ext fun _ => Subtype.ext rfl
  rw [hB1, hC, AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
    AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _,
    AnalyticManifold.BlowUpSequence.pullback_congr _ hmaps]

/-- **Congruence of pulled-back induced values along equal lists** (a substitution). The form of
`fam_seqOn_induced_pullback_congr` for `B`. -/
theorem seqOn_induced_pullback_congr {X Z : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ X}
    {L₁ L₂ : AnalyticManifold.BlowUpSequence ψ₀ X} (e : L₁ = L₂)
        (hL₁ : L₁.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)
    (hL₂ : L₂.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf) (hD₁ : Dom (T.induced s L₁ hL₁))
    (hD₂ : Dom (T.induced s L₂ hL₂)) {U₁ : Opens (L₁.stage (Fin.last _))}
    {U₂ : Opens (L₂.stage (Fin.last _))}
    (hU₁ : IsCompact (closure (U₁ : Set (L₁.stage (Fin.last _)))))
    (hU₂ : IsCompact (closure (U₂ : Set (L₂.stage (Fin.last _)))))
    (hU : ∀ p, p ∈ U₁ ↔ AnalyticManifold.BlowUpSequence.stageOfEq e p ∈ U₂)
    (f₁ : AnalyticMap Z ((L₁.stage (Fin.last _)).restrict U₁))
    (f₂ : AnalyticMap Z ((L₂.stage (Fin.last _)).restrict U₂))
    (hf₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f₁)
    (hf₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f₂)
    (hf : ∀ z, AnalyticManifold.BlowUpSequence.stageOfEq e (f₁ z).1 = (f₂ z).1) :
    ((B.fam (T.induced s L₁ hL₁) hD₁).seqOn U₁ hU₁).pullback f₁ hf₁ =
      ((B.fam (T.induced s L₂ hL₂) hD₂).seqOn U₂ hU₂).pullback f₂ hf₂ := by
  subst e
  have hUU : U₁ = U₂ := by
    ext p
    have := hU p
    rw [AnalyticManifold.BlowUpSequence.stageOfEq_rfl] at this
    exact this
  subst hUU
  have hff : f₁ = f₂ := ContMDiffMap.ext fun z => Subtype.ext (by
    have := hf z
    rw [AnalyticManifold.BlowUpSequence.stageOfEq_rfl] at this
    exact this)
  subst hff
  rfl

/-! ### The comparison of the two appended values -/

include hsq in
/-- **The comparison of the two appended values** (the heart of the chain transport, the form of
`linkValue_rel` for `B`): for lists `L₂` on `N` and `L₁` on `M` whose cleaned forms agree after
pulling `L₁` back along `hW`, the value at the induced triple of `L₂` on the reading open of `ρ'`
and the value at the induced triple of `L₁` on the reading open of `ρ`, both pulled back to the
common cleaned last stage of the restricted lists and cleaned, agree. Both are the value at the
induced triple of the common cleaned list: the general `valueTransport_rel` with the naturality of
the value functor `seqOn_induced_eraseEmpty`, `seqOn_induced_pullback_liftRange` (on the side of
`L₁`) and `seqOn_induced_pullback_congr` (the substitution along `hrel`). The class proofs: of the
induced triples of `L₁`, `L₂` and of the cleaned `L₂` (hypotheses), the others by the closure of the
class under pull-back (`hDom`) and along the equality of the cleaned lists. -/
theorem inducedValue_rel (hB : B.CommutesWithLocalIsos) (hB' : B.IndifferentToEmptyMembers)
    (hDom : ClassPullbackClosed (ψ₀ := ψ₀) Dom) (L₂ : AnalyticManifold.BlowUpSequence ψ₀ N)
    (hL₂ : L₂.toSuccession.IsOfOrderGe (T₁.pullback hW hhW).I s (T₁.pullback hW hhW).F.idealSheaf)
    (hD₂ : Dom ((T₁.pullback hW hhW).induced s L₂ hL₂))
    (hDe₂ : Dom ((T₁.pullback hW hhW).induced s L₂.eraseEmpty
      (AnalyticManifold.BlowUpSequence.isOfOrderGe_eraseEmpty L₂ _ s
          (T₁.pullback hW hhW).isSnc hL₂)))
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
    (((B.fam ((T₁.pullback hW hhW).induced s L₂ hL₂) hD₂).seqOn (L₂.liftRange ρ' hρ') hO₂).pullback
      ((L₂.liftCorestrict ρ' hρ').comp
        (Diffeomorph.toAnalyticMap (L₂.pullback ρ' hρ').eraseEmptyLast.symm)) hκ₂).eraseEmpty =
    (((B.fam (T₁.induced s L₁ hL₁) hD₁).seqOn (L₁.liftRange ρ hρ) hO₁).pullback
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
  -- the class proofs of the pulled-back list, of the erased lists and of their pull-backs
  have hDP : Dom ((T₁.pullback hW hhW).induced s (L₁.pullback hW hhW) hP) :=
    dom_induced_pullback hDom T₁ s L₁ hL₁ hW hhW hP hD₁
  have hLe₂ := AnalyticManifold.BlowUpSequence.isOfOrderGe_eraseEmpty L₂ _ s
      (T₁.pullback hW hhW).isSnc hL₂
  have hLeP := AnalyticManifold.BlowUpSequence.isOfOrderGe_eraseEmpty (L₁.pullback hW hhW) _ s
    (T₁.pullback hW hhW).isSnc hP
  have hDPe : Dom ((T₁.pullback hW hhW).induced s (L₁.pullback hW hhW).eraseEmpty hLeP) :=
    dom_induced_of_eq hrel hLe₂ hLeP hDe₂
  have hpull₂ : Dom (((T₁.pullback hW hhW).induced s L₂.eraseEmpty hLe₂).pullback
      (Diffeomorph.toAnalyticMap L₂.eraseEmptyLast) L₂.eraseEmptyLast.isLocalDiffeomorph) :=
    hDom _ _ _ hDe₂
  have hpullP : Dom (((T₁.pullback hW hhW).induced s (L₁.pullback hW hhW).eraseEmpty hLeP).pullback
      (Diffeomorph.toAnalyticMap (L₁.pullback hW hhW).eraseEmptyLast)
      (L₁.pullback hW hhW).eraseEmptyLast.isLocalDiffeomorph) :=
    hDom _ _ _ hDPe
  exact AnalyticManifold.BlowUpSequence.valueTransport_rel L₁ L₂ hW hhW ρ hρ ρ' hρ' hV hhV hsq e₀
    hA hκ₂ hκ₁
    (B.seqOn_induced_eraseEmpty hB hB' (T₁.pullback hW hhW) s L₂ hL₂ hLe₂ hD₂ hDe₂ hpull₂
      (L₂.liftRange ρ' hρ') hO₂)
    (B.seqOn_induced_eraseEmpty hB hB' (T₁.pullback hW hhW) s (L₁.pullback hW hhW) hP hLeP hDP hDPe
      hpullP ((L₁.pullback hW hhW).liftRange ρ' hρ') hOP)
    (B.seqOn_induced_pullback_liftRange T₁ s hW hhW L₁ hL₁ hD₁ hDP ρ hρ ρ' hρ' hV hsq hB hO₁ hOP)
    fun hf₁ hf₂ => B.seqOn_induced_pullback_congr s hrel hLe₂ hLeP hDe₂ hDPe _ _
      (AnalyticManifold.BlowUpSequence.mem_imageOpens_eraseEmptyLast_liftRange_iff L₁ L₂ hW hhW ρ'
        hρ' hrel) _ _ hf₁ hf₂
      (AnalyticManifold.BlowUpSequence.stageOfEq_eraseEmptyLast_liftCorestrict_apply L₁ L₂ hW hhW
        ρ' hρ' hrel hA hκ₂)

end AnalyticFamilyFunctor

end Hironaka.Manifold
