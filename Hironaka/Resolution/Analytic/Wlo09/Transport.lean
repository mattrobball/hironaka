/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
public import Hironaka.Resolution.Analytic.Wlo09.Rounds
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
import Hironaka.Resolution.Analytic.OrderReduction.ClassPullback
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.OrderReduction.LiftUnique
import Hironaka.Resolution.Analytic.OrderReduction.ValueTransport
import Hironaka.Resolution.Analytic.Wlo09.Comp
import Hironaka.Resolution.Analytic.Wlo09.EmptyRound
import Hironaka.Resolution.Analytic.Wlo09.Indiff
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Transport of the rounds along a local analytic isomorphism

The rounds of the resolution family (`resolveFrom`,
`Hironaka/Resolution/Analytic/Wlo09/Rounds.lean`) on `(Y, curY)` along a chain `ΩY`, read through
`ιY`, and the rounds on `(X, cur)` along `Ω`, read through `ι`, agree up to empty blow-ups when
`curY` is the pull-back of `cur` along a local analytic isomorphism `g : Y → X` carrying each `ΩY k`
into `Ω k`, and the two reading manifolds are identified by a local analytic isomorphism `e` over
`g` (`eraseEmpty_resolveFrom_congr`). This is the behaviour of a blow-up sequence functor under
smooth morphisms [Kol07, 34.1], the value on a pull-back being the pulled-back value with the empty
blow-ups deleted; in Włodarczyk's form, the restriction of the sequence over a larger open
determines the sequence over a smaller one [Wlo09, Theorem 2.0.3 (4)]. Its special cases carry the
canonicity proof of `Hironaka/Resolution/Analytic/Wlo09/Canonicity.lean`: `g = id` with `ΩY k ≤ Ω k`
shrinks the chain, `g` an open inclusion restricts the outer open.

Per round, the field `commutesWithLocalIsos` of `BOanFam`, applied to the corestriction
`g|_{ΩY d} : ΩY d → g(ΩY d)`, surjective onto its open relatively compact image (the first clause of
[Kol07, 34.1]), and the field `compat` along `g(ΩY d) ≤ Ω d` make the round on `Y` the erased
pull-back of the round on `X` along `g|`. So the derived manifolds are identified only through the
common erased list (`eraseEmptyTransport`: `eraseEmptyLast` on both sides and the cast `stageOfEq`),
the derived ideals correspond (`markedTransformSeq_last_eraseEmptyTransport`,
`markedTransformSeq_last_pullbackLiftLast`), and the derived boundary on `Y` is an empty subfamily
of the transported derived boundary on `X` (`exists_orderEmbedding_eraseEmptyTransport`, from
`boundaryCorr_eraseEmpty`), whose empty members `resolveFrom_indiff`
(`Hironaka/Resolution/Analytic/Wlo09/Indiff.lean`) removes before the induction hypothesis applies
to the exact pull-back `(curX').pullback g'`. The reading maps on the derived manifolds are
identified by uniqueness of maps over the blow-down (`eq_of_stageMap_last_eq`), and the two
concatenations are compared by `eraseEmpty_concat_congr`. The induction unfolds `resolveFrom` at the
successor case only.

* `BlowUpSequence.eraseEmptyTransport`, `stageMap_last_eraseEmptyTransport`,
  `stageMap_last_toAnalyticMap_eraseEmptyTransport`, `eraseEmptyTransport_apply`: the
  identification of the last stages of two lists with the same erasure, over the base.
* `BlowUpSequence.eq_of_stageMap_last_eq`, `BlowUpSequence.comap_comap_symm`: uniqueness of maps
  over the blow-down (not in the sources: the blow-down is an isomorphism over a dense open, so two
  maps into the last stage that agree after it agree), the inverse-image identity along a
  diffeomorphism.
* `BlowUpSequence.markedTransformSeq_last_eraseEmptyTransport`,
  `BlowUpSequence.exists_orderEmbedding_eraseEmptyTransport`: the transport of the derived ideal and
  the derived boundary ([Kol07, 32 and 34.1]).
* `BlowUpSequence.eraseEmpty_concat_congr`: the two erased concatenations.
* `mem_liftChain_iff`: membership in the lifted chain.
* `eraseEmpty_resolveFrom_congr`: the transport theorem.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open _root_.Manifold
open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

/-! ### The identification of the last stages of two lists with the same erasure -/

/-- Two lists with the same deletion of empty blow-ups have isomorphic last stages ([Kol07, 34.1]):
through the common erased list, along `eraseEmptyLast` on both sides and the cast `stageOfEq` of
the equality of erasures. -/
def eraseEmptyTransport (A B : BlowUpSequence ψ₀ M) (h : A.eraseEmpty = B.eraseEmpty) :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (A.stage (Fin.last _)) (B.stage (Fin.last _)) ω :=
  have := finiteDimensional_of_chartIso ψ₀
  A.eraseEmptyLast.trans ((stageOfEq h).trans B.eraseEmptyLast.symm)

theorem eraseEmptyTransport_apply (A B : BlowUpSequence ψ₀ M) (h : A.eraseEmpty = B.eraseEmpty)
    (p : A.stage (Fin.last _)) :
    eraseEmptyTransport A B h p = B.eraseEmptyLast.symm (stageOfEq h (A.eraseEmptyLast p)) := rfl

/-- The identification lies over the identity of the base: the blow-downs agree. -/
theorem stageMap_last_eraseEmptyTransport (A B : BlowUpSequence ψ₀ M)
    (h : A.eraseEmpty = B.eraseEmpty)
    (p : A.stage (Fin.last _)) :
    B.toSuccession.stageMap (Fin.last _) (eraseEmptyTransport A B h p) =
      A.toSuccession.stageMap (Fin.last _) p := by
  rw [eraseEmptyTransport_apply, stageMap_last_eraseEmptyLast_symm, stageMap_last_stageOfEq,
    stageMap_last_eraseEmptyLast]

/-- The inverse image along a diffeomorphism then along its inverse is the identity
(`comap_symm_comap` the other way round). -/
theorem comap_comap_symm (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω)
    (J : IdealSheaf M) :
    (J.pullback _ (Diffeomorph.toAnalyticMap φ.symm).contMDiff).pullback _
        (Diffeomorph.toAnalyticMap φ).contMDiff = J := by
  rw [IdealSheaf.pullback_comp]
  exact (IdealSheaf.pullback_congr J _ _ (funext fun x => φ.symm_apply_apply x)).trans
    (IdealSheaf.pullback_id_eq_self J)

/-- `stageMap_last_eraseEmptyTransport` for the identification as an analytic map. -/
theorem stageMap_last_toAnalyticMap_eraseEmptyTransport (A B : BlowUpSequence ψ₀ M)
    (h : A.eraseEmpty = B.eraseEmpty) (p : A.stage (Fin.last _)) :
    B.toSuccession.stageMap (Fin.last _)
      (Diffeomorph.toAnalyticMap (eraseEmptyTransport A B h) p) =
      A.toSuccession.stageMap (Fin.last _) p :=
  stageMap_last_eraseEmptyTransport A B h p

/-- **Uniqueness of maps over the blow-down** (`eq_of_stageMap_last_comp_eq`; not in the sources):
a local analytic isomorphism and an analytic map into the last stage of a list that agree after
the blow-down agree, since the blow-down is an isomorphism over a dense open. -/
theorem eq_of_stageMap_last_eq (L : BlowUpSequence ψ₀ M) {Z : AnalyticManifold.{u} 𝕜 E}
    (f : AnalyticMap Z (L.stage (Fin.last _))) (hf : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f)
    (g : AnalyticMap Z (L.stage (Fin.last _)))
    (h : ∀ z, L.toSuccession.stageMap (Fin.last _) (f z) =
      L.toSuccession.stageMap (Fin.last _) (g z)) : f = g :=
  ContMDiffMap.ext fun z => congrFun (eq_of_stageMap_last_comp_eq L f.contMDiff.continuous
    g.contMDiff.continuous (fun _ _ hD => dense_preimage_of_isLocalDiffeomorph f hf hD) h) z

/-- The marked transform at the last stage is transported along `eraseEmptyTransport`
([Kol07, 34.1]): both lists are the common erased list up to empty blow-ups, which transform
`(I, m)` by pull-back (`markedTransformSeq_last_eraseEmpty`). -/
theorem markedTransformSeq_last_eraseEmptyTransport (A B : BlowUpSequence ψ₀ M)
    (h : A.eraseEmpty = B.eraseEmpty) (I : IdealSheaf M) (m : ℕ)
    (hA : A.toSuccession.IsMarkedGe I m) (hB : B.toSuccession.IsMarkedGe I m) :
    (B.toSuccession.markedTransformSeq I m (Fin.last _)).pullback _ (Diffeomorph.toAnalyticMap
        (eraseEmptyTransport A B h)).contMDiff =
      A.toSuccession.markedTransformSeq I m (Fin.last _) := by
  have := finiteDimensional_of_chartIso ψ₀
  have hB' := markedTransformSeq_last_eraseEmpty_of_isMarkedGe B I m hB
  have hA' := markedTransformSeq_last_eraseEmpty_of_isMarkedGe A I m hA
  have hAB := markedTransformSeq_last_stageOfEq h I m
  -- `comap` along the three factors of the transport, one at a time
  have e1 :
      Manifold.IdealSheaf.pullback _ (Diffeomorph.toAnalyticMap (eraseEmptyTransport A B
          h)).contMDiff
      (B.toSuccession.markedTransformSeq I m (Fin.last _)) =
      (((B.toSuccession.markedTransformSeq I m (Fin.last _)).pullback _ (Diffeomorph.toAnalyticMap
          B.eraseEmptyLast.symm).contMDiff).pullback _ (Diffeomorph.toAnalyticMap (stageOfEq
              h)).contMDiff).pullback _ (Diffeomorph.toAnalyticMap A.eraseEmptyLast).contMDiff := by
    rw [IdealSheaf.pullback_comp, IdealSheaf.pullback_comp]
    rfl
  rw [e1, ← hB', hAB, comap_comap_symm, hA', comap_comap_symm]

/-- For a list `A` without empty centres and a list `B` with the same erasure, the boundary family
from `F` at the last stage of `A` embeds order-preservingly into that of `B` transported along
`eraseEmptyTransport`, the members matched and the members of `B`'s family off the range empty
(`boundaryCorr_eraseEmpty_self`); read on any family equal to `B`'s. The empty blow-ups add empty
members to the boundary ([Kol07, 32 and 34.1]). -/
theorem exists_orderEmbedding_eraseEmptyTransport (A B : BlowUpSequence ψ₀ M)
    (hA : A.NoEmptyCenters) (h : A.eraseEmpty = B.eraseEmpty) (F : HypersurfaceFamily M)
    (hF : ∀ j, IsClosed (F.hyp j)) (GB : HypersurfaceFamily (B.stage (Fin.last _)))
    (hGB : B.toSuccession.totalTransformSeqFrom F (Fin.last _) = GB) :
    ∃ e : (A.toSuccession.totalTransformSeqFrom F (Fin.last _)).ι ↪o GB.ι,
      (∀ i, ⇑(eraseEmptyTransport A B h) ⁻¹' GB.hyp (e i) =
        (A.toSuccession.totalTransformSeqFrom F (Fin.last _)).hyp i) ∧
      ∀ b, b ∉ Set.range e → GB.hyp b = ∅ := by
  subst hGB
  have hA' : A.eraseEmpty = A := eraseEmpty_of_noEmptyCenters A hA
  have hc := boundaryCorr_of_eq hA' F
    (boundaryCorr_of_eq h.symm F (boundaryCorr_eraseEmpty_self B F hF))
  obtain ⟨e, h1, h2, -⟩ := hc
  refine ⟨e, fun i => ?_, h2⟩
  -- the two identifications of the last stages agree (uniqueness of maps over the blow-down)
  have hT : ⇑((B.eraseEmptyLast.trans ((stageOfEq h.symm).trans (stageOfEq hA'))).symm) =
      ⇑(eraseEmptyTransport A B h) := by
    have := eq_of_stageMap_last_eq B
      (Diffeomorph.toAnalyticMap (B.eraseEmptyLast.trans ((stageOfEq h.symm).trans
        (stageOfEq hA'))).symm) (Diffeomorph.isLocalDiffeomorph _)
      (Diffeomorph.toAnalyticMap (eraseEmptyTransport A B h)) fun p => by
        rw [stageMap_last_toAnalyticMap_eraseEmptyTransport]
        change B.toSuccession.stageMap (Fin.last _) (B.eraseEmptyLast.symm
          ((stageOfEq h.symm).symm ((stageOfEq hA').symm p))) = _
        rw [stageMap_last_eraseEmptyLast_symm, stageMap_last_stageOfEq_symm,
          stageMap_last_stageOfEq_symm]
    exact congrArg (fun f : AnalyticMap _ _ => ⇑f) this
  rw [← hT]
  exact h1 i

/-- Deleting the empty blow-ups of two concatenations whose first pieces have the same erasure
(`eraseEmptyTransport` identifies their last stages) and whose second pieces agree up to empty
blow-ups after that identification gives equal lists (`eraseEmpty_concat`,
`concat_pullback_stageOfEq`). -/
theorem eraseEmpty_concat_congr {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (A B : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (h : A.eraseEmpty = B.eraseEmpty)
    (R : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (A.stage (Fin.last _)))
    (S : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (B.stage (Fin.last _)))
    (hRS : R.eraseEmpty = (S.pullback (Diffeomorph.toAnalyticMap (eraseEmptyTransport A B h))
      (Diffeomorph.isLocalDiffeomorph _)).eraseEmpty) :
    (A.concat R).eraseEmpty = (B.concat S).eraseEmpty := by
  rw [eraseEmpty_concat, eraseEmpty_concat,
    ← Hironaka.Manifold.concat_pullback_stageOfEq h _ (Diffeomorph.isLocalDiffeomorph _)]
  refine congrArg _ ?_
  rw [eraseEmpty_map, hRS, map_eq_pullback_symm, eraseEmpty_pullback _ _ _
      A.eraseEmptyLast.symm.toEquiv.surjective,
    pullback_comp _ _ _ _ _,
    map_eq_pullback_symm, eraseEmpty_pullback _ _ _ (stageOfEq h).toEquiv.surjective,
    pullback_comp _ _ _ _ _]
  refine congrArg eraseEmpty (pullback_congr _ ?_ _ _)
  exact ContMDiffMap.ext fun q => congrArg (fun p => B.eraseEmptyLast.symm (stageOfEq h p))
    (A.eraseEmptyLast.apply_symm_apply q)

end AnalyticManifold.BlowUpSequence

namespace Hironaka.Manifold

open _root_.Manifold

section Chain

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} {O : Opens X}
  (L : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (X.restrict O))

/-- Membership in the lifted chain: the point lies over the open of `X`. -/
theorem mem_liftChain_iff (Ω : ℕ → Opens X) (k : ℕ) (p : L.stage (Fin.last _)) :
    p ∈ liftChain L Ω k ↔
      (L.toSuccession.stageMap (Fin.last _) p : X.restrict O).1 ∈ Ω k :=
  Iff.rfl

end Chain

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)

/-- **Transport of the rounds along a local analytic isomorphism** ([Kol07, 34.1];
[Wlo09, Theorem 2.0.3 (4)]). The rounds on `(Y, curY)` along a chain `ΩY`, read through `ιY`, and
the rounds on `(X, cur)` along `Ω`, read through `ι`, agree up to empty blow-ups when `curY` is
the pull-back of `cur` along a local analytic isomorphism `g : Y → X` carrying each `ΩY k` into
`Ω k`, and the two reading manifolds are identified by a local analytic isomorphism `e` over `g`
(`ι ∘ e = g ∘ ιY`). Per round: the field `commutesWithLocalIsos` along `g|_{ΩY d}` and `compat`
along `g(ΩY d) ≤ Ω d` (`eraseEmpty_pullback_eraseEmpty`, `pullback_comp`), then
`eraseEmpty_concat` and the induction hypothesis at the derived triples, identified through
`markedTransformSeq_last_pullbackLiftLast` and `markedTransformSeq_last_eraseEmptyTransport` (the
ideal), `exists_orderEmbedding_eraseEmptyTransport` (the boundary), `resolveFrom_indiff` and
`resolveFrom_congr_triple`, with the lifts of `g` and `e`. -/
theorem eraseEmpty_resolveFrom_congr (d : ℕ) {X Y : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (g : AnalyticMap Y X) (hg : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g)
    (cur : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    (curY : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) Y)
    (hpb : curY.IsPullbackOf cur g)
    (hord : ∀ x, cur.I.ord x ≤ (d : ℕ∞)) (hfin : Finite {j // cur.F.hyp j ≠ ∅})
    (hordY : ∀ y, curY.I.ord y ≤ (d : ℕ∞)) (hfinY : Finite {j // curY.F.hyp j ≠ ∅})
    (Ω : ℕ → Opens X) (hΩ : ∀ k, k < d → IsCompact (closure (Ω k : Set X)))
    (hΩsub : ∀ k, k + 1 < d → closure (Ω k : Set X) ⊆ Ω (k + 1))
    (ΩY : ℕ → Opens Y) (hΩY : ∀ k, k < d → IsCompact (closure (ΩY k : Set Y)))
    (hΩYsub : ∀ k, k + 1 < d → closure (ΩY k : Set Y) ⊆ ΩY (k + 1))
    (hΩg : ∀ k, k < d → ⇑g '' (ΩY k : Set Y) ⊆ Ω k)
    {N NY : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (ι : AnalyticMap N X)
    (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι) (hrange : Set.range ι ⊆ Ω 0)
    (ιY : AnalyticMap NY Y) (hιY : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ιY)
    (hrangeY : Set.range ιY ⊆ ΩY 0)
    (e : AnalyticMap NY N) (he : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω e)
    (hcomm : ι.comp e = g.comp ιY) :
    (resolveFrom bo d curY hordY hfinY ΩY hΩY hΩYsub ιY hιY hrangeY).eraseEmpty =
      ((resolveFrom bo d cur hord hfin Ω hΩ hΩsub ι hι hrange).pullback e he).eraseEmpty := by
  induction d generalizing X Y N NY with
  | zero => rw [resolveFrom, resolveFrom, BlowUpSequence.pullback_nil]
  | succ d ih =>
    /- ### The round on both sides -/
    have hOX := hΩ d (Nat.lt_succ_self d)
    have hOY := hΩY d (Nat.lt_succ_self d)
    have hgOY : ⇑g '' (ΩY d : Set Y) ⊆ Ω d := hΩg d (Nat.lt_succ_self d)
    have hclsX := boClass_succ_of_ord_le cur hord hfin
    have hclsY := boClass_succ_of_ord_le curY hordY hfinY
    set LX := roundList bo cur hclsX (Ω d) hOX with hLXdef
    set LY := roundList bo curY hclsY (ΩY d) hOY with hLYdef
    set curXO := cur.pullback (X.inclusion (Ω d)) (isLocalDiffeomorph_inclusion X (Ω d))
      with hcurXO
    set curYO := curY.pullback (Y.inclusion (ΩY d)) (isLocalDiffeomorph_inclusion Y (ΩY d))
      with hcurYO
    set gd := AnalyticMap.restrictMap g (ΩY d) (Ω d) hgOY with hgddef
    have hgd : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω gd :=
      AnalyticMap.isLocalDiffeomorph_restrictMap hg (ΩY d) (Ω d) hgOY
    have hgeX : LX.toSuccession.IsOfOrderGe curXO.I (d + 1) curXO.F.idealSheaf :=
      (bo (d + 1)).isOfOrderGe cur hclsX (Ω d) hOX
    have hgeY : LY.toSuccession.IsOfOrderGe curYO.I (d + 1) curYO.F.idealSheaf :=
      (bo (d + 1)).isOfOrderGe curY hclsY (ΩY d) hOY
    have hLYne : LY.NoEmptyCenters :=
      ((bo (d + 1)).functor.fam curY hclsY).noEmptyCenters (ΩY d) hOY
    -- the restricted `Y`-triple is the pull-back of the restricted `X`-triple along `gd`
    have hYO : curYO = curXO.pullback gd hgd := by
      have h1 : curYO.IsPullbackOf cur (g.comp (Y.inclusion (ΩY d))) :=
        hpb.comp (AnalyticTriple.isPullbackOf_pullback curY _ _)
      have h2 : (curXO.pullback gd hgd).IsPullbackOf cur ((X.inclusion (Ω d)).comp gd) :=
        (AnalyticTriple.isPullbackOf_pullback cur _ _).comp
          (AnalyticTriple.isPullbackOf_pullback curXO _ _)
      have hmaps : g.comp (Y.inclusion (ΩY d)) = (X.inclusion (Ω d)).comp gd :=
        ContMDiffMap.ext fun _ => rfl
      rw [hmaps] at h1
      exact h1.eq h2
    have hIYO : curYO.I = curXO.I.pullback gd gd.contMDiff :=
        congrArg AnalyticTriple.I hYO
    have hFYO : curYO.F = curXO.F.comap ⇑gd := congrArg AnalyticTriple.F hYO
    /- ### The round's list on `Y` is the erased pull-back of the round's list on `X` -/
    have hle : AnalyticMap.imageOpens g hg (ΩY d) ≤ Ω d := fun _ hx => hgOY hx
    have hLY : LY = (LX.pullback gd hgd).eraseEmpty := by
      have h1 := (bo (d + 1)).commutesWithLocalIsos cur curY g hg hpb hclsX hclsY (ΩY d) hOY
      have h2 := ((bo (d + 1)).functor.fam cur hclsX).compat (AnalyticMap.imageOpens g hg (ΩY d))
        (Ω d) (AnalyticMap.isCompact_closure_image g hOY) hOX hle
      rw [h2, BlowUpSequence.eraseEmpty_pullback_eraseEmpty, BlowUpSequence.pullback_comp] at h1
      refine h1.trans (congrArg BlowUpSequence.eraseEmpty (BlowUpSequence.pullback_congr _ ?_ _
          hgd))
      exact ContMDiffMap.ext fun _ => rfl
    have hLYP : LY.eraseEmpty = (LX.pullback gd hgd).eraseEmpty := by
      rw [hLY, BlowUpSequence.eraseEmpty_eraseEmpty]
    have hgeP : (LX.pullback gd hgd).toSuccession.IsOfOrderGe curYO.I (d + 1)
        curYO.F.idealSheaf := by
      rw [hIYO, hFYO]
      exact AnalyticTriple.isOfOrderGe_pullback curXO (d + 1) LX hgeX gd hgd
    /- ### The identification of the derived manifolds and the transported triple -/
    obtain ⟨g', hg'def⟩ : ∃ g' : AnalyticMap (LY.stage (Fin.last _)) (LX.stage (Fin.last _)),
        g' = (LX.pullbackLiftLast gd hgd).comp (Diffeomorph.toAnalyticMap
          (BlowUpSequence.eraseEmptyTransport LY (LX.pullback gd hgd) hLYP)) := ⟨_, rfl⟩
    have hg' : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g' := by
      subst hg'def
      exact BlowUpSequence.isLocalDiffeomorph_comp
        (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)
            (Diffeomorph.isLocalDiffeomorph _)
    have hg'coe : ⇑g' = ⇑(LX.pullbackLiftLast gd hgd) ∘ ⇑(Diffeomorph.toAnalyticMap
        (BlowUpSequence.eraseEmptyTransport LY (LX.pullback gd hgd) hLYP)) := by
      subst hg'def
      rfl
    -- the blow-downs commute with `g'`
    have hstage : ∀ p, LX.toSuccession.stageMap (Fin.last _) (g' p) =
        gd (LY.toSuccession.stageMap (Fin.last _) p) := fun p => by
      subst hg'def
      rw [ContMDiffMap.comp_apply, BlowUpSequence.stageMap_last_pullbackLiftLast,
        BlowUpSequence.stageMap_last_toAnalyticMap_eraseEmptyTransport]
    have hcurX' : derivedTriple bo cur hclsX (Ω d) hOX = curXO.induced (d + 1) LX hgeX := rfl
    have hcurY' : derivedTriple bo curY hclsY (ΩY d) hOY = curYO.induced (d + 1) LY hgeY := rfl
    -- the ideal of the derived `Y`-triple is the pull-back of the derived `X`-ideal along `g'`
    have hI : ((curXO.induced (d + 1) LX hgeX).pullback g' hg').I =
        (curYO.induced (d + 1) LY hgeY).I := by
      change (LX.toSuccession.markedTransformSeq curXO.I (d + 1) (Fin.last _)).pullback g'
          g'.contMDiff =
        LY.toSuccession.markedTransformSeq curYO.I (d + 1) (Fin.last _)
      rw [hg'def, ← IdealSheaf.pullback_comp,
        ← BlowUpSequence.markedTransformSeq_last_pullbackLiftLast LX gd hgd curXO.I _ (d + 1) hgeX,
        ← hIYO, BlowUpSequence.markedTransformSeq_last_eraseEmptyTransport LY
            (LX.pullback gd hgd) hLYP
          curYO.I (d + 1) hgeY.isMarkedGe hgeP.isMarkedGe]
    -- the boundary of the derived `Y`-triple is an empty subfamily of the transported boundary
    have hFc : ∀ j, IsClosed (curYO.F.hyp j) := fun j =>
      (curYO.isSnc.isClosedSubmanifold j).isClosed
    obtain ⟨eF, h1F, h2F⟩ := BlowUpSequence.exists_orderEmbedding_eraseEmptyTransport LY
      (LX.pullback gd hgd) hLYne hLYP curYO.F hFc
      ((LX.toSuccession.totalTransformSeqFrom curXO.F (Fin.last _)).comap
        ⇑(LX.pullbackLiftLast gd hgd))
      (by rw [hFYO]; exact BlowUpSequence.totalTransformSeqFrom_last_pullbackLiftLast LX gd hgd
            curXO.F)
    have hhypF : ∀ i, ((curXO.induced (d + 1) LX hgeX).pullback g' hg').F.hyp (eF i) =
        (curYO.induced (d + 1) LY hgeY).F.hyp i := fun i => by
      change ⇑g' ⁻¹' (LX.toSuccession.totalTransformSeqFrom curXO.F (Fin.last _)).hyp (eF i) =
        (LY.toSuccession.totalTransformSeqFrom curYO.F (Fin.last _)).hyp i
      rw [hg'coe, Set.preimage_comp]
      exact h1F i
    have hemptyF : ∀ b, b ∉ Set.range eF →
        ((curXO.induced (d + 1) LX hgeX).pullback g' hg').F.hyp b = ∅ := fun b hb => by
      change ⇑g' ⁻¹' (LX.toSuccession.totalTransformSeqFrom curXO.F (Fin.last _)).hyp b = ∅
      have h2 : ⇑(LX.pullbackLiftLast gd hgd) ⁻¹'
          (LX.toSuccession.totalTransformSeqFrom curXO.F (Fin.last _)).hyp b = ∅ := h2F b hb
      rw [hg'coe, Set.preimage_comp, h2, Set.preimage_empty]
    -- the hypotheses of the rounds from `d` on the transported triple
    have hordTf : ∀ x, ((curXO.induced (d + 1) LX hgeX).pullback g' hg').I.ord x ≤ (d : ℕ∞) :=
      fun x => (IdealSheaf.ord_comap_of_isLocalDiffeomorphAt _ g' (hg' x)).trans_le
        (derivedTriple_ord_le bo cur hclsX (Ω d) hOX (g' x))
    have hclsXO : AnalyticTriple.BOClass (d + 1) curXO :=
      AnalyticTriple.boClass_of_isPullbackOf hclsX (isLocalDiffeomorph_inclusion X (Ω d))
        (AnalyticTriple.isPullbackOf_pullback cur _ _)
    have hfinTf : Finite {j // ((curXO.induced (d + 1) LX hgeX).pullback g' hg').F.hyp j ≠ ∅} :=
      (AnalyticTriple.boClass_of_isPullbackOf
        (AnalyticTriple.boClass_induced curXO (d + 1) LX hgeX hclsXO) hg'
        (AnalyticTriple.isPullbackOf_pullback _ g' hg')).2.2
    /- ### The reading maps on the derived manifolds -/
    have hrX : Set.range ι ⊆ Ω d := range_subset_chain hΩsub hrange
    have hrY : Set.range ιY ⊆ ΩY d := range_subset_chain hΩYsub hrangeY
    have hιX' : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
        (AnalyticMap.corestrict ι (Ω d) hrX) := isLocalDiffeomorph_corestrict ι (Ω d) hι hrX
    have hιY' : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
        (AnalyticMap.corestrict ιY (ΩY d) hrY) := isLocalDiffeomorph_corestrict ιY (ΩY d) hιY hrY
    have hsq : gd.comp (AnalyticMap.corestrict ιY (ΩY d) hrY) =
        (AnalyticMap.corestrict ι (Ω d) hrX).comp e := ContMDiffMap.ext fun w =>
      Subtype.ext (congrArg (fun f : AnalyticMap NY X => f w) hcomm).symm
    have hA : (LY.pullback (AnalyticMap.corestrict ιY (ΩY d) hrY) hιY').eraseEmpty =
        ((LX.pullback (AnalyticMap.corestrict ι (Ω d) hrX) hιX').pullback e he).eraseEmpty := by
      rw [hLY, BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
        BlowUpSequence.pullback_comp _ _ _ _ _,
        BlowUpSequence.pullback_congr _ hsq _ (BlowUpSequence.isLocalDiffeomorph_comp hιX' he),
        ← BlowUpSequence.pullback_comp _ _ hιX' _ he]
    obtain ⟨e', he'def⟩ : ∃ e' : AnalyticMap
        ((LY.pullback (AnalyticMap.corestrict ιY (ΩY d) hrY) hιY').stage (Fin.last _))
        ((LX.pullback (AnalyticMap.corestrict ι (Ω d) hrX) hιX').stage (Fin.last _)),
        e' = ((LX.pullback (AnalyticMap.corestrict ι (Ω d) hrX) hιX').pullbackLiftLast e he).comp
          (Diffeomorph.toAnalyticMap (BlowUpSequence.eraseEmptyTransport _ _ hA)) := ⟨_, rfl⟩
    have he' : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω e' := by
      subst he'def
      exact BlowUpSequence.isLocalDiffeomorph_comp
        (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)
            (Diffeomorph.isLocalDiffeomorph _)
    -- `kX ∘ e' = g' ∘ kY` by uniqueness of maps over the blow-down
    have hcomm' : (LX.pullbackLiftLast (AnalyticMap.corestrict ι (Ω d) hrX) hιX').comp e' =
        g'.comp (LY.pullbackLiftLast (AnalyticMap.corestrict ιY (ΩY d) hrY) hιY') :=
      BlowUpSequence.eq_of_stageMap_last_eq LX _
        (BlowUpSequence.isLocalDiffeomorph_comp (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast
            _ _ _)
          he') _ fun z => by
        rw [ContMDiffMap.comp_apply, ContMDiffMap.comp_apply, hstage,
          BlowUpSequence.stageMap_last_pullbackLiftLast,
              BlowUpSequence.stageMap_last_pullbackLiftLast,
          he'def, ContMDiffMap.comp_apply, BlowUpSequence.stageMap_last_pullbackLiftLast,
          BlowUpSequence.stageMap_last_toAnalyticMap_eraseEmptyTransport]
        exact (congrArg (fun f : AnalyticMap NY (X.restrict (Ω d)) => f _) hsq).symm
    -- the lifted chains correspond
    have hΩg' : ∀ k, k < d → ⇑g' '' (liftChain LY ΩY k : Set (LY.stage (Fin.last _))) ⊆
        liftChain LX Ω k := by
      rintro k hk _ ⟨p, hp, rfl⟩
      rw [SetLike.mem_coe, mem_liftChain_iff] at hp ⊢
      rw [hstage]
      exact hΩg k (Nat.lt_succ_of_lt hk) ⟨_, hp, rfl⟩
    /- ### The induction hypothesis at the derived data, and the erased value on `Y` -/
    have hIH := ih g' hg' (curXO.induced (d + 1) LX hgeX)
      ((curXO.induced (d + 1) LX hgeX).pullback g' hg')
      (AnalyticTriple.isPullbackOf_pullback _ g' hg')
      (derivedTriple_ord_le bo cur hclsX (Ω d) hOX) (derivedTriple_finite bo cur hclsX (Ω d) hOX)
      hordTf hfinTf (liftChain LX Ω) (liftChain_isCompact LX hΩ hΩsub rfl)
      (liftChain_closure_subset LX hΩsub) (liftChain LY ΩY) (liftChain_isCompact LY hΩY hΩYsub rfl)
      (liftChain_closure_subset LY hΩYsub) hΩg'
      (LX.pullbackLiftLast (AnalyticMap.corestrict ι (Ω d) hrX) hιX')
      (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)
      (range_pullbackLiftLast_subset_liftOpens LX ι hι (Ω 0) hrange hrX)
      (LY.pullbackLiftLast (AnalyticMap.corestrict ιY (ΩY d) hrY) hιY')
      (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)
      (range_pullbackLiftLast_subset_liftOpens LY ιY hιY (ΩY 0) hrangeY hrY) e' he' hcomm'
    have hRY : resolveFrom bo d (curYO.induced (d + 1) LY hgeY)
        (derivedTriple_ord_le bo curY hclsY (ΩY d) hOY)
        (derivedTriple_finite bo curY hclsY (ΩY d) hOY) (liftChain LY ΩY)
        (liftChain_isCompact LY hΩY hΩYsub rfl) (liftChain_closure_subset LY hΩYsub)
        (LY.pullbackLiftLast (AnalyticMap.corestrict ιY (ΩY d) hrY) hιY')
        (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)
        (range_pullbackLiftLast_subset_liftOpens LY ιY hιY (ΩY 0) hrangeY hrY) =
        resolveFrom bo d ((curXO.induced (d + 1) LX hgeX).pullback g' hg') hordTf hfinTf
        (liftChain LY ΩY) (liftChain_isCompact LY hΩY hΩYsub rfl)
        (liftChain_closure_subset LY hΩYsub)
        (LY.pullbackLiftLast (AnalyticMap.corestrict ιY (ΩY d) hrY) hιY')
        (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)
        (range_pullbackLiftLast_subset_liftOpens LY ιY hιY (ΩY 0) hrangeY hrY) :=
      ((resolveFrom_indiff bo d ((curXO.induced (d + 1) LX hgeX).pullback g' hg')
        (curYO.induced (d + 1) LY hgeY).F
        (curYO.induced (d + 1) LY hgeY).isSnc eF hhypF hemptyF hordTf hfinTf
        (derivedTriple_finite bo curY hclsY (ΩY d) hOY) (liftChain LY ΩY)
        (liftChain_isCompact LY hΩY hΩYsub rfl) (liftChain_closure_subset LY hΩYsub) _
        (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)
        (range_pullbackLiftLast_subset_liftOpens LY ιY hιY (ΩY 0) hrangeY hrY)).trans
        (resolveFrom_congr_triple bo d (AnalyticTriple.ext'
          (T₁ := ⟨((curXO.induced (d + 1) LX hgeX).pullback g' hg').I,
            ((curXO.induced (d + 1) LX hgeX).pullback g' hg').isNonzeroEverywhere,
            (curYO.induced (d + 1) LY hgeY).F, (curYO.induced (d + 1) LY hgeY).isSnc⟩)
          (T₂ := curYO.induced (d + 1) LY hgeY) hI rfl) hordTf
          (derivedTriple_finite bo curY hclsY (ΩY d) hOY)
          (derivedTriple_ord_le bo curY hclsY (ΩY d) hOY)
          (derivedTriple_finite bo curY hclsY (ΩY d) hOY) (liftChain LY ΩY)
          (liftChain_isCompact LY hΩY hΩYsub rfl) (liftChain_closure_subset LY hΩYsub) _
          (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)
          (range_pullbackLiftLast_subset_liftOpens LY ιY hιY (ΩY 0) hrangeY hrY))).symm
    /- ### Assembly -/
    rw [resolveFrom, resolveFrom, BlowUpSequence.pullback_concat]
    refine BlowUpSequence.eraseEmpty_concat_congr _ _ hA _ _ ?_
    exact (congrArg BlowUpSequence.eraseEmpty hRY).trans (hIH.trans
        (congrArg BlowUpSequence.eraseEmpty
      ((BlowUpSequence.pullback_congr _ he'def he' (BlowUpSequence.isLocalDiffeomorph_comp
        (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)
        (Diffeomorph.isLocalDiffeomorph _))).trans
      (BlowUpSequence.pullback_comp _ _ (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _) _
        (Diffeomorph.isLocalDiffeomorph _)).symm)))

end Hironaka.Manifold

end
