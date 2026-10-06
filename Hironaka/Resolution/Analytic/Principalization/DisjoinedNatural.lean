/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Principalization.Corr
public import Hironaka.Resolution.Analytic.Principalization.DisjoinInput
public import Hironaka.Resolution.Analytic.OrderReduction.ConcatPullback
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Resolution.Analytic.OrderReduction.FamilyChain
import Hironaka.Resolution.Analytic.OrderReduction.Step21Functoriality
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Naturality of the disjoined triple

The disjoined triple of a list (`disjoinedTripleOf`) is natural for the two operations the
independence of the shrinking open compares (functoriality for smooth morphisms [Kol07, 34.1] and
the empty blow-up convention [Kol07, 32]):

* **pull-back along a local analytic isomorphism** `h`: the disjoined triple of `h^* L` for the
  pulled-back triple is the pull-back of the disjoined triple of `L` along the last-stage lift `h_r`
  (the boundary families by `totalTransformSeqFrom_last_pullbackLiftLast`, the original members by
  `originalIdx_last_pullback_heq`, the ideal sheaves by `stageMap_last_pullbackLiftLast`;
  [Kol07, 30.1] for the pull-back of a blow-up sequence);
* **padding by an empty blow-up**: the disjoined triple of `cons h∅ (π^* L)` (the disjoining list
  with one more, empty, first round; `π : Bl_∅ M → M` the blow-down) is an *empty extension* of the
  pull-back of the disjoined triple of `L` along `π_r` — the extra exceptional divisor is empty
  (`isEmptyExtension_totalTransform_of_eq_empty`, propagated along the list by
  `exists_isEmptyExtension_totalTransformSeqFrom_last`).

Both are instances of `disjoinedTripleOf_isEmptyExtensionOfPullback`: a correspondence of the
boundary families at the last stages (`PullbackCorr`, `Corr.lean`) with matched original members,
plus the equation of the ideal sheaves, gives the relation `IsEmptyExtensionOfPullback` of the
disjoined triples (the same ideal sheaf, the boundary an empty extension of the pulled-back
boundary) — the hypothesis under which the input family's `IndifferentToEmptyMembers` and
`CommutesWithLocalIsos` identify its values. Used by `Canonicity.lean` (through `ValueNatural.lean`)
for the independence of the shrinking open.
-/

@[expose] public section

universe u

open Set AnalyticManifold
open scoped Manifold ContDiff

namespace Manifold

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### Empty extensions of pull-backs of triples -/

/-- `T'` on `N` is an **empty extension of the pull-back** of `T` along `g`: the same ideal sheaf,
and the boundary of `T'` an empty extension of the pulled-back boundary (the same nonempty members
plus extra empty members). -/
def AnalyticTriple.IsEmptyExtensionOfPullback {M N : AnalyticManifold.{u} 𝕜 E}
    (T' : AnalyticTriple ψ₀ N) (T : AnalyticTriple ψ₀ M) (g : AnalyticMap N M) : Prop :=
  T'.I = T.I.pullback g g.contMDiff ∧ ∃ e : (T.F.comap g).ι ↪o T'.F.ι,
      HypersurfaceFamily.IsEmptyExtension e

/-- A correspondence of the boundary families at the last stages with matched original members,
together with the equation of the ideal sheaves, makes the disjoined triple of the one list an
empty extension of the pull-back of the disjoined triple of the other. -/
theorem _root_.Hironaka.Manifold.disjoinedTripleOf_isEmptyExtensionOfPullback
    {X X' : AnalyticManifold.{u} 𝕜 E}
    (T₁ : AnalyticTriple ψ₀ X') (L : BlowUpSequence ψ₀ X')
    (h₁ : (L.toSuccession.totalTransformSeqFrom T₁.F (Fin.last _)).IsSnc ψ₀)
    (h₁' : ((L.toSuccession.totalTransformSeqFrom T₁.F (Fin.last _)).subfamily
      (fun k => k ∈ Set.range (L.toSuccession.originalIdx T₁.F (Fin.last _)))).meetLocus 2 = ∅)
    (T₂ : AnalyticTriple ψ₀ X) (R : BlowUpSequence ψ₀ X)
    (h₂ : (R.toSuccession.totalTransformSeqFrom T₂.F (Fin.last _)).IsSnc ψ₀)
    (h₂' : ((R.toSuccession.totalTransformSeqFrom T₂.F (Fin.last _)).subfamily
      (fun k => k ∈ Set.range (R.toSuccession.originalIdx T₂.F (Fin.last _)))).meetLocus 2 = ∅)
    (g : AnalyticMap (R.stage (Fin.last _)) (L.stage (Fin.last _)))
    (hI : T₂.I.pullback _ (R.toSuccession.stageMap (Fin.last _)).contMDiff =
      (T₁.I.pullback _ (L.toSuccession.stageMap (Fin.last _)).contMDiff).pullback g g.contMDiff)
    (e₀ : T₁.F.ι ≃ T₂.F.ι)
    (hF : HypersurfaceFamily.PullbackCorr ⇑g
      (L.toSuccession.totalTransformSeqFrom T₁.F (Fin.last _))
      (R.toSuccession.totalTransformSeqFrom T₂.F (Fin.last _))
      (L.toSuccession.originalIdx T₁.F (Fin.last _))
      (R.toSuccession.originalIdx T₂.F (Fin.last _) ∘ ⇑e₀)) :
    (disjoinedTripleOf T₂ R h₂ h₂').IsEmptyExtensionOfPullback (disjoinedTripleOf T₁ L h₁ h₁')
      g := by
  refine ⟨hI, ?_⟩
  have h := hF.exists_isEmptyExtension_collapse
  rw [e₀.surjective.range_comp] at h
  exact h

end Manifold

namespace AnalyticManifold.BlowUpSequence

open Hironaka.Manifold
open Manifold Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### Propagation of an empty extension along a list -/

/-- An empty extension on the same space is a correspondence across the identity. -/
theorem exists_isEmptyExtension_totalTransformSeqFrom_last :
    ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) (G G' : HypersurfaceFamily M)
      (e₀ : G.ι ↪o G'.ι), HypersurfaceFamily.IsEmptyExtension e₀ →
      HypersurfaceFamily.PullbackCorr id (L.toSuccession.totalTransformSeqFrom G (Fin.last _))
        (L.toSuccession.totalTransformSeqFrom G' (Fin.last _))
        (L.toSuccession.originalIdx G (Fin.last _))
        (fun j => L.toSuccession.originalIdx G' (Fin.last _) (e₀ j))
  | _, nil _, G, G', e₀, he => ⟨e₀, fun k => he.1 k, he.2, fun _ => rfl⟩
  | _, @cons _ _ _ _ _ _ _ _ Y _ hY rest, G, G', e₀, he => by
    have ih := exists_isEmptyExtension_totalTransformSeqFrom_last rest
      (G.totalTransform (blowUpπ ψ₀ hY) Y) (G'.totalTransform (blowUpπ ψ₀ hY) Y)
      (Hironaka.Sequence.sumLexMapEmb (γ := PUnit.{u + 1}) e₀)
      (HypersurfaceFamily.isEmptyExtension_totalTransform (blowUpπ ψ₀ hY) Y he)
    obtain ⟨e, h1, h2, h3⟩ := ih
    refine HypersurfaceFamily.PullbackCorr.congr
      (FiniteSuccession.cons_totalTransformSeqFrom_last hY rest.toSuccession G).symm
      (FiniteSuccession.cons_totalTransformSeqFrom_last hY rest.toSuccession G').symm
      (fun j => (FiniteSuccession.heq_originalIdx_cons_last hY rest.toSuccession G j).symm)
      (fun j => (FiniteSuccession.heq_originalIdx_cons_last hY rest.toSuccession G' (e₀ j)).symm)
      ⟨e, h1, h2, fun j => h3 (toLex (Sum.inl j))⟩

/-! ### The stage map of `cons` at the last stage -/

/-- The composite blow-down of `cons hY rest` at the last stage is the blow-down of the first
round after the composite of `rest` (`stageMapAux_cons_succ`). -/
theorem stageMap_last_cons {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY))
    (q : (cons hY rest).stage (Fin.last _)) :
    (cons hY rest).toSuccession.stageMap (Fin.last _) q =
      blowUpπ ψ₀ hY (rest.toSuccession.stageMap (Fin.last _) q) := by
  have h1 := stageMapAux_cons_succ hY rest rest.length (Fin.last _).2 q
  change (cons hY rest).toSuccession.stageMapAux (rest.length + 1) _ q =
    blowUpπ ψ₀ hY (rest.toSuccession.stageMapAux rest.length _ q)
  rw [h1]

/-! ### The blow-down of an empty centre is a local analytic isomorphism -/

/-- The blow-down of an empty centre is a local analytic isomorphism (it is the analytic
isomorphism `emptyBlowUpDiffeomorph` as a function). -/
theorem isLocalDiffeomorph_blowUpπ_of_eq_empty {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (hY₀ : Y = ∅) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (blowUpπ ψ₀ hY) := by
  have h := (emptyBlowUpDiffeomorph hY hY₀).isLocalDiffeomorph
  have hc : ⇑(emptyBlowUpDiffeomorph hY hY₀) = ⇑(blowUpπ ψ₀ hY) :=
    funext (emptyBlowUpDiffeomorph_apply hY hY₀)
  rw [hc] at h
  exact h

/-! ### Naturality of the disjoined triple -/

/-- Functoriality of the disjoined triple for local analytic isomorphisms ([Kol07, 34.1]): the
disjoined triple of `h^* L` for the pulled-back triple is (an empty extension of, with no extra
member) the pull-back of the disjoined triple of `L` along the last-stage lift `h_r`. -/
theorem isEmptyExtensionOfPullback_disjoinedTripleOf_pullback {M N : AnalyticManifold.{u} 𝕜 E}
    (T : AnalyticTriple ψ₀ M) (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (h₁ : (L.toSuccession.totalTransformSeqFrom T.F (Fin.last _)).IsSnc ψ₀)
    (h₁' : ((L.toSuccession.totalTransformSeqFrom T.F (Fin.last _)).subfamily
      (fun k => k ∈ Set.range (L.toSuccession.originalIdx T.F (Fin.last _)))).meetLocus 2 = ∅)
    (h₂ : ((L.pullback h hh).toSuccession.totalTransformSeqFrom (T.pullback h hh).F
      (Fin.last _)).IsSnc ψ₀)
    (h₂' : (((L.pullback h hh).toSuccession.totalTransformSeqFrom (T.pullback h hh).F
      (Fin.last _)).subfamily (fun k => k ∈ Set.range
        ((L.pullback h hh).toSuccession.originalIdx (T.pullback h hh).F (Fin.last _)))).meetLocus 2
      = ∅) :
    (disjoinedTripleOf (T.pullback h hh) (L.pullback h hh) h₂ h₂').IsEmptyExtensionOfPullback
      (disjoinedTripleOf T L h₁ h₁') (L.pullbackLiftLast h hh) :=
  disjoinedTripleOf_isEmptyExtensionOfPullback T L h₁ h₁' (T.pullback h hh) (L.pullback h hh) h₂ h₂'
    (L.pullbackLiftLast h hh)
    (by
      change (T.I.pullback h h.contMDiff).pullback _ _ = _
      rw [IdealSheaf.pullback_comp, IdealSheaf.pullback_comp]
      exact congrArg (fun f : AnalyticMap _ _ => T.I.pullback f f.contMDiff)
        (ContMDiffMap.ext fun q => (stageMap_last_pullbackLiftLast L h hh q).symm))
    (Equiv.refl _)
    ((HypersurfaceFamily.PullbackCorr.refl_comap _ _ _).congr rfl
      (totalTransformSeqFrom_last_pullbackLiftLast L h hh T.F).symm (fun _ => HEq.rfl)
      (fun j => (originalIdx_last_pullback_heq L h hh T.F j).symm))

/-- The empty blow-up convention [Kol07, 32] for the disjoined triple: the disjoined triple of the
list padded by an empty first round, `cons h∅ (π^* L)`, is an empty extension of the pull-back of
the disjoined triple of `L` along the last-stage lift of the blow-down `π` — the extra exceptional
divisor is empty. -/
theorem isEmptyExtensionOfPullback_disjoinedTripleOf_cons_of_eq_empty
    {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (L : BlowUpSequence ψ₀ M) {Y : Set M}
    {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c) (hY₀ : Y = ∅)
    (hπ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (blowUpπ ψ₀ hY))
    (h₁ : (L.toSuccession.totalTransformSeqFrom T.F (Fin.last _)).IsSnc ψ₀)
    (h₁' : ((L.toSuccession.totalTransformSeqFrom T.F (Fin.last _)).subfamily
      (fun k => k ∈ Set.range (L.toSuccession.originalIdx T.F (Fin.last _)))).meetLocus 2 = ∅)
    (h₂ : ((cons hY (L.pullback (blowUpπ ψ₀ hY) hπ)).toSuccession.totalTransformSeqFrom T.F
      (Fin.last _)).IsSnc ψ₀)
    (h₂' : (((cons hY (L.pullback (blowUpπ ψ₀ hY) hπ)).toSuccession.totalTransformSeqFrom T.F
      (Fin.last _)).subfamily (fun k => k ∈ Set.range
        ((cons hY (L.pullback (blowUpπ ψ₀ hY) hπ)).toSuccession.originalIdx T.F
          (Fin.last _)))).meetLocus 2 = ∅) :
    (disjoinedTripleOf T (cons hY (L.pullback (blowUpπ ψ₀ hY) hπ))
      h₂ h₂').IsEmptyExtensionOfPullback
      (disjoinedTripleOf T L h₁ h₁') (L.pullbackLiftLast (blowUpπ ψ₀ hY) hπ) := by
  have hF : ∀ j, IsClosed (T.F.hyp j) := fun j => (T.isSnc.isClosedSubmanifold j).isClosed
  have he₀ : HypersurfaceFamily.IsEmptyExtension (OrderIso.refl T.F.ι).toOrderEmbedding :=
    ⟨fun _ => rfl, fun b hb => absurd ⟨b, rfl⟩ hb⟩
  have he := HypersurfaceFamily.isEmptyExtension_totalTransform_of_eq_empty
    (blowUpπ ψ₀ hY).contMDiff.continuous hY₀ he₀ hF
  obtain ⟨e, h1, h2, h3⟩ := exists_isEmptyExtension_totalTransformSeqFrom_last
    (L.pullback (blowUpπ ψ₀ hY) hπ) _ _ _ he
  have hpb := (HypersurfaceFamily.PullbackCorr.refl_comap
      ⇑(L.pullbackLiftLast (blowUpπ ψ₀ hY) hπ)
      (L.toSuccession.totalTransformSeqFrom T.F (Fin.last _))
      (L.toSuccession.originalIdx T.F (Fin.last _))).congr rfl
    (totalTransformSeqFrom_last_pullbackLiftLast L (blowUpπ ψ₀ hY) hπ T.F).symm
    (fun _ => HEq.rfl)
    (fun j => (originalIdx_last_pullback_heq L (blowUpπ ψ₀ hY) hπ T.F j).symm)
  refine disjoinedTripleOf_isEmptyExtensionOfPullback T L h₁ h₁' T
    (cons hY (L.pullback (blowUpπ ψ₀ hY) hπ)) h₂ h₂' (L.pullbackLiftLast (blowUpπ ψ₀ hY) hπ) ?_
    (Equiv.refl _) ?_
  · change T.I.pullback _ ((cons hY (L.pullback (blowUpπ ψ₀ hY) hπ)).toSuccession.stageMap
        (Fin.last _)).contMDiff =
      (T.I.pullback _ (L.toSuccession.stageMap (Fin.last _)).contMDiff).pullback _
          (L.pullbackLiftLast (blowUpπ ψ₀ hY) hπ).contMDiff
    rw [IdealSheaf.pullback_comp]
    exact congrArg (fun f : AnalyticMap _ _ => T.I.pullback f f.contMDiff) (ContMDiffMap.ext fun q
        =>
      (stageMap_last_cons hY _ q).trans
        (stageMap_last_pullbackLiftLast L (blowUpπ ψ₀ hY) hπ q).symm)
  · refine HypersurfaceFamily.PullbackCorr.congr rfl
      (FiniteSuccession.cons_totalTransformSeqFrom_last hY
        (L.pullback (blowUpπ ψ₀ hY) hπ).toSuccession T.F).symm (fun _ => HEq.rfl)
      (fun j => (FiniteSuccession.heq_originalIdx_cons_last hY
        (L.pullback (blowUpπ ψ₀ hY) hπ).toSuccession T.F j).symm) ?_
    exact hpb.trans_isEmptyExtension ⟨h1, h2⟩ fun j => h3 j

end AnalyticManifold.BlowUpSequence

