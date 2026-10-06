/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.FamilyClosedEmbedding
public import Hironaka.Resolution.Analytic.Principalization.IsoOff
public import Hironaka.Resolution.Analytic.Functor.ModifiedMarkedFam
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.ChainClosedEmbeddingChain
import Hironaka.Resolution.Analytic.OrderReduction.BDErase
import Hironaka.Resolution.Analytic.OrderReduction.ClosedEmbeddingFam
import Hironaka.Resolution.Analytic.Principalization.ClauseFive
import Hironaka.Resolution.Analytic.Principalization.ClauseThree
import Hironaka.Resolution.Analytic.Restrict.FlagPushforward
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Hironaka.Manifold.Submanifold.Charts

/-!
# The chaining of the closed-embedding commutation, IV: codimension zero and the two towers

The predicate `AnalyticFamilyFunctor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s)` at
`s = 0` is the second degenerate codimension the printed reduction ([Kol07, 108], the chain of
hypersurfaces) does not mention: a closed submanifold of codimension `0` is a clopen set
(`isClosedSubmanifold_zero_iff'`), so

* `IsClosedSubmanifold.zeroDiffeomorph`, `IsClosedSubmanifold.isLocalDiffeomorph_inclusionMap_zero`:
  the bundled codimension-zero submanifold is the open submanifold and its inclusion is a local
  analytic isomorphism;
* (E2) `AnalyticFamilyFunctor.commutesWithClosedEmbeddingsOfEmptyDivisorFam_zero`: a functor at
  the standard model that commutes with local isomorphisms (`CommutesWithLocalIsos`) and whose
  centres lie over the cosupport of the restricted ideal (`FiniteSuccession.CentersOver`,
  [Kol07, Definition 66, (4′)]) commutes with codimension-zero closed embeddings through itself:
  its value on `U ∩ S` is the pull-back of its value on `U` along the open inclusion, and the
  push-forward of that pull-back along the clopen `S ∩ U` is the value on `U` itself
  (`Hironaka.Resolution.Analytic.Restrict.FlagPushforward`; `pushforwardRestrict_eq`,
  `pullback_comp`, the `eraseEmpty` lemmas);
* (E3′) `BMOanFam_commutesWithClosedEmbeddingsOfEmptyDivisorFam_all`,
  `BMOmodFam_commutesWithClosedEmbeddingsOfEmptyDivisorFam_all`: the two towers, for the marked
  order-reduction records `BMOanFam 𝕜 n 1` ([Kol07, Theorem 35, (5)], [Kol07, Claim 71.2]) and
  the modified marked resolution records `BMOmodFam 𝕜 n` ([Wlo09, §7.1]): the tower lemma (E3) of
  `Hironaka.Resolution.Analytic.Functor.ChainClosedEmbeddingChain` on the marked class
  `BMOClass 1`, with (E2) discharging the codimension-zero clause through the order clause
  `isOfOrderGe` of the records (`CentersOver.of_isOfOrderGe`).
-/

@[expose] public section

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Manifold

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-! ### The codimension-zero inclusion is a local analytic isomorphism -/

/-- A closed submanifold of codimension `0` (a clopen set, `isClosedSubmanifold_zero_iff'`) as an
open subset. -/
def IsClosedSubmanifold.toOpens {S : Set M} (hS : IsClosedSubmanifold ψ S 0) : Opens M :=
  ⟨S, (isClosedSubmanifold_zero_iff'.mp hS).isOpen⟩

/-- The bundled codimension-zero submanifold IS the open submanifold: the identity of the carrier
is an analytic isomorphism between the two structures (`contMDiff_codRestrict_opens` one way,
`IsClosedSubmanifold.contMDiff_codRestrict` the other). -/
def IsClosedSubmanifold.zeroDiffeomorph {S : Set M} (hS : IsClosedSubmanifold ψ S 0) :
    Diffeomorph 𝓘(𝕜, Fin (n - 0) → 𝕜) 𝓘(𝕜, E) hS.toAnalyticManifold (M.restrict hS.toOpens) ω where
  toFun p := ⟨p.1, p.2⟩
  invFun q := ⟨q.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    intro p
    have hval : ContMDiffAt 𝓘(𝕜, Fin (n - 0) → 𝕜) 𝓘(𝕜, E) ω
        ((Subtype.val : M.restrict hS.toOpens → M) ∘
          fun q : hS.toAnalyticManifold => (⟨q.1, q.2⟩ : M.restrict hS.toOpens)) p :=
      hS.inclusionMap.contMDiff.contMDiffAt
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (P := ContDiffWithinAtProp 𝓘(𝕜, Fin (n - 0) → 𝕜) 𝓘(𝕜, E) ω) _ univ p).mp hval
  contMDiff_invFun := hS.contMDiff_codRestrict (M.inclusion hS.toOpens).contMDiff fun q => q.2

/-- The inclusion of a codimension-zero closed submanifold is a local analytic isomorphism: it is
the open inclusion (`isLocalDiffeomorph_inclusion`) composed with `zeroDiffeomorph`. -/
theorem IsClosedSubmanifold.isLocalDiffeomorph_inclusionMap_zero {S : Set M}
    (hS : IsClosedSubmanifold ψ S 0) :
    IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 0) → 𝕜) 𝓘(𝕜, E) ω hS.inclusionMap := by
  have h : (⇑hS.inclusionMap : hS.toAnalyticManifold → M) =
      ⇑(M.inclusion hS.toOpens) ∘ ⇑hS.zeroDiffeomorph := funext fun _ => rfl
  rw [h]
  intro p
  have h2 : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω ⇑(M.inclusion hS.toOpens)
      (hS.zeroDiffeomorph p) :=
    isLocalDiffeomorph_inclusion M hS.toOpens _
  have h1 : IsLocalDiffeomorphAt 𝓘(𝕜, Fin (n - 0) → 𝕜) 𝓘(𝕜, E) ω ⇑hS.zeroDiffeomorph p :=
    hS.zeroDiffeomorph.isLocalDiffeomorph p
  exact h1.comp 𝓘(𝕜, E) M h2

end Manifold

/-! ### (E2) -/

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

/-- **(E2)**, the degenerate case `s = 0`: a functor at the
standard model that commutes with local isomorphisms and whose every centre lies over the
cosupport of the restricted ideal commutes with codimension-zero closed embeddings through
itself. -/
theorem AnalyticFamilyFunctor.commutesWithClosedEmbeddingsOfEmptyDivisorFam_zero
    {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)},
      AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M → Prop}
    (B : AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) Dom)
    (hB : B.CommutesWithLocalIsos)
    (hcen : ∀ {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
      (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : Dom T)
      (U : Opens M) (hU : IsCompact (closure (U : Set M))),
      ((B.fam T hT).seqOn U hU).toSuccession.CentersOver
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I.support) :
    B.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := 0) B := by
  intro M S hS I hI J hJ hle hJI hT hT' U hU
  have hloc := hS.isLocalDiffeomorph_inclusionMap_zero
  have hpb : (⟨J, hJ, HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩ :
      AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) hS.toAnalyticManifold).IsPullbackOf
        ⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩ hS.inclusionMap :=
    ⟨hJI, (HypersurfaceFamily.empty_comap _).symm⟩
  -- the trace open `U ∩ S` of `M`
  have hVU : U ⊓ hS.toOpens ≤ U := inf_le_left
  have hV : IsCompact (closure ((U ⊓ hS.toOpens : Opens M) : Set M)) :=
    hU.of_isClosed_subset isClosed_closure (closure_mono hVU)
  have himg : ⇑hS.inclusionMap '' (hS.preimageOpens U : Set hS.toAnalyticManifold) =
      ((U ⊓ hS.toOpens : Opens M) : Set M) := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨hp, p.2⟩
    · rintro ⟨hyU, hyS⟩
      exact ⟨⟨y, hyS⟩, hyU, rfl⟩
  have hUS := hS.isCompact_closure_preimageOpens U hU
  have h1 := hB.seqOn_eq_of_image_eq hloc hpb hT hT' hUS hV himg
  have h2 := (B.fam _ hT).compat (U ⊓ hS.toOpens) U hV hU hVU
  -- both sides have no empty centres: compare after `eraseEmpty`
  have hLne := (B.fam _ hT).noEmptyCenters U hU
  have hRne := BlowUpSequence.noEmptyCenters_pushforwardRestrict' hS U _
    ((B.fam _ hT').noEmptyCenters (hS.preimageOpens U) hUS)
  have hf : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      ((M.restrictLE hVU).comp (AnalyticMap.restrictMap hS.inclusionMap (hS.preimageOpens U)
        (U ⊓ hS.toOpens) himg.le)) :=
    BlowUpSequence.isLocalDiffeomorph_comp (isLocalDiffeomorph_restrictLE hVU)
      (AnalyticMap.isLocalDiffeomorph_restrictMap hloc _ _ himg.le)
  rw [← BlowUpSequence.eraseEmpty_of_noEmptyCenters _ hLne,
    ← BlowUpSequence.eraseEmpty_of_noEmptyCenters _ hRne, h1, h2,
    BlowUpSequence.eraseEmpty_pushforwardRestrict_eraseEmpty,
    ← BlowUpSequence.eraseEmpty_pushforwardRestrict_eraseEmpty,
    BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
    BlowUpSequence.eraseEmpty_pushforwardRestrict_eraseEmpty,
    BlowUpSequence.pullback_comp _ _ _ _ _, BlowUpSequence.pushforwardRestrict_eq]
  -- the composite along the bridge is the inclusion of the clopen `S ∩ U ⊆ M.restrict U`
  have hloc' := (hS.restrictOpen U).isLocalDiffeomorph_inclusionMap_zero
  have hX : ((((B.fam _ hT).seqOn U hU).pullback _ hf).pullback
        ⟨(hS.restrictBundleDiffeomorph U).symm, (hS.restrictBundleDiffeomorph U).symm.contMDiff⟩
        (hS.restrictBundleDiffeomorph U).symm.isLocalDiffeomorph) =
      ((B.fam _ hT).seqOn U hU).pullback (hS.restrictOpen U).inclusionMap hloc' :=
    (BlowUpSequence.pullback_comp _ _ hf _ _).trans
      (BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ => rfl) _ hloc')
  -- every centre lies over `S`: `hcen` and `𝓘_S ≤ I`
  have hL : ((B.fam _ hT).seqOn U hU).toSuccession.CentersOver (⇑(M.inclusion U) ⁻¹' S) := by
    refine (hcen _ hT U hU).mono fun x hx => ?_
    by_contra hxS
    have htop : I.stalkIdeal (M.inclusion U x) = ⊤ :=
      top_le_iff.mp ((hS.stalkIdeal_idealSheaf_of_notMem hxS).symm.le.trans
        (IdealSheaf.le_def.mp hle _))
    have h := IdealSheaf.stalkIdeal_pullback ⇑(M.inclusion U) (M.inclusion U).contMDiff I x
    rw [htop, Ideal.map_top] at h
    exact hx h
  -- the codimension-zero identity of `FlagPushforward`
  have hT8 := BlowUpSequence.pushforward_pullback_inclusionMap_of_centersOver
      (hS.restrictOpen U) hloc'
    _ hL
  exact (congrArg BlowUpSequence.eraseEmpty hT8).symm.trans
    (congrArg (fun Z => (BlowUpSequence.pushforward (hS.restrictOpen U) Z).eraseEmpty) hX.symm)

/-! ### (E3′) the two towers -/

/-- **The marked tower** ([Kol07, Theorem 35, (5)], [Kol07, Claim 71.2], [Kol07, 108]): for
`bmo : ∀ n, BMOanFam 𝕜 n 1` with the codimension-one inputs at every positive level, the
commutation at every codimension. The tower lemma (E3) on the marked class `BMOClass 1` (closed
under pull-back, `bmoClass_pullback`; the restricted empty-divisor triple lies in it,
`bmoClass_one_of_isEmpty`), with the codimension-zero clause from (E2) and `CentersOver` from the
order clause `BMOanFam.isOfOrderGe` at mark `1` (`CentersOver.of_isOfOrderGe`). -/
theorem BMOanFam_commutesWithClosedEmbeddingsOfEmptyDivisorFam_all
    (bmo : ∀ n, BMOanFam.{u} 𝕜 n 1)
    (h1 : ∀ m, 0 < m →
      (bmo m).functor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := 1)
        (bmo (m - 1)).functor) :
    ∀ n s, (bmo n).functor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s)
      (bmo (n - s)).functor :=
  AnalyticFamilyFunctor.commutesWithClosedEmbeddingsOfEmptyDivisorFam_tower
    (Dom := fun _ => AnalyticTriple.BMOClass 1) (fun n => (bmo n).functor)
    (fun n => (bmo n).commutesWithLocalIsos)
    (fun _ _ _ _ g hg hT => AnalyticTriple.bmoClass_pullback hT g hg)
    (fun _ _ _ _ _ _ _ _ _ _ =>
      AnalyticTriple.bmoClass_one_of_isEmpty _ ⟨fun j => PEmpty.elim j⟩)
    (fun n => AnalyticFamilyFunctor.commutesWithClosedEmbeddingsOfEmptyDivisorFam_zero
      (bmo n).functor (bmo n).commutesWithLocalIsos fun T hT U hU =>
        FiniteSuccession.CentersOver.of_isOfOrderGe _ ((bmo n).isOfOrderGe T hT U hU) le_rfl)
    h1

/-- **The modified tower** ([Wlo09, §7.1]; [Kol07, Theorem 35, (5)]): for `bmod : ∀ n, BMOmodFam 𝕜
n` with the codimension-one inputs at every positive level, the commutation at every codimension.
The same assembly as the marked tower; `CentersOver` from the order clause
`BMOmodFam.isOfOrderGe` (which coincides with `center_mem_support` at mark `1`). -/
theorem BMOmodFam_commutesWithClosedEmbeddingsOfEmptyDivisorFam_all
    (bmod : ∀ n, BMOmodFam.{u} 𝕜 n)
    (h1 : ∀ m, 0 < m →
      (bmod m).functor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := 1)
        (bmod (m - 1)).functor) :
    ∀ n s, (bmod n).functor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s)
      (bmod (n - s)).functor :=
  AnalyticFamilyFunctor.commutesWithClosedEmbeddingsOfEmptyDivisorFam_tower
    (Dom := fun _ => AnalyticTriple.BMOClass 1) (fun n => (bmod n).functor)
    (fun n => (bmod n).commutesWithLocalIsos)
    (fun _ _ _ _ g hg hT => AnalyticTriple.bmoClass_pullback hT g hg)
    (fun _ _ _ _ _ _ _ _ _ _ =>
      AnalyticTriple.bmoClass_one_of_isEmpty _ ⟨fun j => PEmpty.elim j⟩)
    (fun n => AnalyticFamilyFunctor.commutesWithClosedEmbeddingsOfEmptyDivisorFam_zero
      (bmod n).functor (bmod n).commutesWithLocalIsos fun T hT U hU =>
        FiniteSuccession.CentersOver.of_isOfOrderGe _ ((bmod n).isOfOrderGe T hT U hU) le_rfl)
    h1

end Hironaka.Manifold
