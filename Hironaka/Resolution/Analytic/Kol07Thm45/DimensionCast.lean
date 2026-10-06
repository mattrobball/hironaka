/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.EmbeddedDesingFam
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Resolution.Analytic.OrderReduction.FamilyChain
import Hironaka.Resolution.Analytic.OrderReduction.Step22Pullback
import Hironaka.Resolution.Analytic.Restrict.DiffeomorphTransport
import Hironaka.Resolution.Analytic.Restrict.StrictSubspaceSeqTransport
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The dimension cast: the functoriality clause across two models of propositionally equal
dimension

Kollár's proof of Theorem 36 increases the ambient dimension freely ("we are allowed to increase
`n` anytime by taking a further embedding `𝔸ⁿ ↪ 𝔸ⁿ⁺ᵐ`") and reads the resolution of the padded
embedding on the coordinate slice through the weak commutation with closed embeddings
([Kol07, Theorem 36, proof] and [Kol07, 34.4]). Here the slice is a bundled submanifold, modelled
on `𝕜^{n' − (n' − n)}`, while the piece is modelled on `𝕜ⁿ`: the two dimensions are
PROPOSITIONALLY equal (`Nat.sub_sub_self`), so the functoriality clause of `IsEmbeddedDesing`
(`CommutesWithLocalIsos`, the commutation with smooth morphisms of [Kol07, 34.1], stated for two
manifolds on ONE model) cannot be applied between them, and `bed.fam k`, `bed.fam n` are related
only by substituting the variable `k`. This module provides the device once:

* `BEDanFamStar.exists_diffeomorph_last_of_cast`: for a variable `k` with `hk : k = n`, a
  diffeomorphism `g : N' → N` ACROSS the models `𝕜ⁿ`, `𝕜ᵏ` (Mathlib's `Diffeomorph` allows two
  models), ideals with `I' = g^* I` (`IdealSheaf.pullback`, two models) in the empty-divisor
  triples of the domain class of the functor, and relatively compact opens `U' = g⁻¹(U)`: the
  final stages of the two values are diffeomorphic OVER `g` (the square through the open
  inclusions and the composite blow-downs), and the final ideal-theoretic strict transforms
  (`strictTransformSubspaceSeq`) correspond under the diffeomorphism. The statement is
  cross-model; its proof is `subst hk`, after which `g` is a same-model diffeomorphism and the
  functoriality clause applies verbatim — the value on `U'` is the pull-back of the value on
  `g(U') = U` along `g|_{U'}` with the empty blow-ups deleted — then
  `strictTransformSubspaceSeq_last_pullback_eraseEmpty` for the strict transforms and the
  last-stage lift of a bijective local isomorphism as a diffeomorphism
  (`pullbackLiftLastDiffeomorphOfBijective`). It is applied at `k := n' − (n' − n)` by
  instantiating the variable, never by a `subst` at a compound term.
* `BlowUpSequence.exists_diffeomorph_last_of_pullback_eraseEmpty`: the same-model content — the
  diffeomorphism `pullbackLiftLast ∘ eraseEmptyLast⁻¹` of the last stages of
  `(L.pullback h).eraseEmpty` and `L` over the bijective `h`, its square
  (`stageMap_last_pullbackLiftLast`, `stageMap_last_eraseEmptyLast`) and the strict-transform
  identity (`strictTransformSubspaceSeq_last_pullback_eraseEmpty`).

Not in the sources; bookkeeping on the functoriality clause and the transports of
`StrictSubspaceSeqTransport.lean`. The padding whose slice is compared here is Włodarczyk's
passage to a common ambient dimension [Wlo09, §7.1].
-/

public section

noncomputable section

open TopologicalSpace Set AnalyticManifold
open scoped Manifold ContDiff Topology

universe u

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {N N' : AnalyticManifold.{u} 𝕜 E}

/-- The same-model content of the dimension cast (the pull-back of a blow-up sequence and the
deletion of its empty blow-ups, [Kol07, Definition 30.1] and [Kol07, 34.1]): for a bijective local
analytic isomorphism `h : N'|U' → N|U` lying over `g` and a list `L` over `N|U`, the last stages of
`(L.pullback h).eraseEmpty` and of `L` are diffeomorphic through
`pullbackLiftLast ∘ eraseEmptyLast⁻¹`, over `g` (the composites commute with the lifts,
`stageMap_last_pullbackLiftLast`, `stageMap_last_eraseEmptyLast`), and the final strict transforms
correspond under the diffeomorphism (`strictTransformSubspaceSeq_last_pullback_eraseEmpty`). -/
theorem exists_diffeomorph_last_of_pullback_eraseEmpty (g : N' → N) {U : Opens N} {U' : Opens N'}
    (L : BlowUpSequence ψ₀ (N.restrict U)) (h : AnalyticMap (N'.restrict U') (N.restrict U))
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (hb : Function.Bijective h)
    (hsq : ∀ p, N.inclusion U (h p) = g (N'.inclusion U' p))
    (J : IdealSheaf (N.restrict U))
        (J' : IdealSheaf (N'.restrict U'))
    (hJ' : J' = J.pullback h h.contMDiff) :
    ∃ G : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ((L.pullback h hh).eraseEmpty.stage (Fin.last _))
        (L.stage (Fin.last _)) ω,
      (∀ p, N.inclusion U (L.toSuccession.composite (G p)) =
        g (N'.inclusion U' ((L.pullback h hh).eraseEmpty.toSuccession.composite p))) ∧
      (L.pullback h hh).eraseEmpty.toSuccession.strictTransformSubspaceSeq J' (Fin.last _) =
        (L.toSuccession.strictTransformSubspaceSeq J (Fin.last _)).pullback ⇑G G.contMDiff := by
  have := finiteDimensional_of_chartIso ψ₀
  subst hJ'
  refine ⟨(L.pullback h hh).eraseEmptyLast.symm.trans
    (L.pullbackLiftLastDiffeomorphOfBijective h hh hb), fun p => ?_, ?_⟩
  · rw [Diffeomorph.coe_trans, Function.comp_apply, coe_pullbackLiftLastDiffeomorphOfBijective,
      FiniteSuccession.composite_eq, FiniteSuccession.composite_eq, stageMap_last_pullbackLiftLast,
      hsq]
    refine congrArg (fun q => g (N'.inclusion U' q)) ?_
    rw [← stageMap_last_eraseEmptyLast (L.pullback h hh) ((L.pullback h hh).eraseEmptyLast.symm p),
      Diffeomorph.apply_symm_apply]
  · rw [strictTransformSubspaceSeq_last_pullback_eraseEmpty L h hh hb.2]
    rw [IdealSheaf.pullback_pullback]
    exact IdealSheaf.pullback_congr _ _ _ rfl

end AnalyticManifold.BlowUpSequence

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜]

/-- **The dimension cast** (Kollár's free enlargement of the ambient dimension and the
commutation of the resolution with smooth morphisms, [Kol07, Theorem 36, proof] and
[Kol07, 34.1]; Włodarczyk's common ambient dimension [Wlo09, §7.1]): for a family functor that
commutes with local analytic isomorphisms in every dimension, and a diffeomorphism `g : N' → N`
between a manifold modelled on `𝕜ⁿ` and one modelled on `𝕜ᵏ` with `k = n` PROPOSITIONALLY (the
slice of a padding: `k = n' − (n' − n)`), whose ideals correspond (`I' = g^* I`, the triples with
the empty divisor), the final stages of the values on corresponding relatively compact opens
`U' = g⁻¹(U)` are diffeomorphic over `g`, and the final ideal-theoretic strict transforms
correspond under the diffeomorphism. The statement is cross-model (`Diffeomorph` and
`IdealSheaf.pullback` allow two models); the proof is `subst hk`, the functoriality clause (whose
`IsPullbackOf` is `⟨hII', empty_comap⟩`), and
`BlowUpSequence.exists_diffeomorph_last_of_pullback_eraseEmpty` at `h := g|_{U'}`. -/
theorem BEDanFamStar.exists_diffeomorph_last_of_cast (bed : BEDanFamStar.{u} 𝕜)
    (hcomm : ∀ m : ℕ, (bed.fam m).CommutesWithLocalIsos) {k n : ℕ} (hk : k = n)
    {N : AnalyticManifold.{u} 𝕜 (Fin k → 𝕜)} {N' : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (g : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin k → 𝕜) N' N ω)
    (I : AnalyticManifold.IdealSheaf N)
        (hI : I.IsNonzeroEverywhere)
    (I' : AnalyticManifold.IdealSheaf N')
        (hI' : I'.IsNonzeroEverywhere)
    (hII' : I' = I.pullback ⇑g g.contMDiff)
    (hT : DomBEDan 𝕜 ⟨I, hI, HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩)
    (hT' : DomBEDan 𝕜 ⟨I', hI', HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩)
    (U : Opens N) (hU : IsCompact (closure (U : Set N))) (U' : Opens N')
    (hU' : IsCompact (closure (U' : Set N'))) (hUU' : (U' : Set N') = ⇑g ⁻¹' (U : Set N)) :
    ∃ G : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin k → 𝕜)
        ((((bed.fam n).fam _ hT').seqOn U' hU').stage (Fin.last _))
        ((((bed.fam k).fam _ hT).seqOn U hU).stage (Fin.last _)) ω,
      (∀ p, N.inclusion U ((((bed.fam k).fam _ hT).seqOn U hU).toSuccession.composite (G p)) =
        g (N'.inclusion U' ((((bed.fam n).fam _ hT').seqOn U' hU').toSuccession.composite p))) ∧
      (((bed.fam n).fam _ hT').seqOn U' hU').toSuccession.strictTransformSubspaceSeq
          (I'.restrict U') (Fin.last _) =
        ((((bed.fam k).fam _ hT).seqOn U hU).toSuccession.strictTransformSubspaceSeq
          (I.restrict U) (Fin.last _)).pullback ⇑G G.contMDiff := by
  subst hk
  -- the image open of `U'` under `g` is `U`
  have himg : AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap g) g.isLocalDiffeomorph U' = U := by
    ext x
    change x ∈ ⇑g '' (U' : Set N') ↔ x ∈ (U : Set N)
    rw [hUU', Set.image_preimage_eq _ fun y => ⟨g.symm y, g.apply_symm_apply y⟩]
  -- the functoriality clause of `IsEmbeddedDesing` along `g`
  have h4 := hcomm _ ⟨I, hI, HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩
    ⟨I', hI', HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩
    (Diffeomorph.toAnalyticMap g) g.isLocalDiffeomorph
    ⟨hII', (HypersurfaceFamily.empty_comap ⇑g).symm⟩ hT hT' U' hU'
  obtain rfl := himg.symm
  generalize hL' : ((bed.fam _).fam _ hT').seqOn U' hU' = L' at h4 ⊢
  subst h4
  -- the restricted `g` is a bijective local isomorphism over `g`
  have hinj : Function.Injective (AnalyticMap.restrictMap (Diffeomorph.toAnalyticMap g) U'
      (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap g) g.isLocalDiffeomorph U')
      Set.Subset.rfl) := fun p q hpq =>
    Subtype.ext (g.injective (congrArg Subtype.val hpq))
  have hsurj : Function.Surjective (AnalyticMap.restrictMap (Diffeomorph.toAnalyticMap g) U'
      (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap g) g.isLocalDiffeomorph U')
      Set.Subset.rfl) :=
    AnalyticMap.surjective_restrictMap (g := Diffeomorph.toAnalyticMap g) rfl
  -- the restricted ideals correspond
  have hJ' : I'.restrict U' = Manifold.IdealSheaf.pullback _ (AnalyticMap.restrictMap
      (Diffeomorph.toAnalyticMap g) U'
        (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap g) g.isLocalDiffeomorph U')
        Set.Subset.rfl).contMDiff
      (I.restrict (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap g)
        g.isLocalDiffeomorph U')) := by
    dsimp only
        [IdealSheaf.restrict]
    rw [IdealSheaf.pullback_pullback, hII', IdealSheaf.pullback_pullback]
    exact IdealSheaf.pullback_congr I _ _
      (funext fun p => (AnalyticMap.restrictMap_apply (Diffeomorph.toAnalyticMap g) U' _
        Set.Subset.rfl p).symm)
  exact BlowUpSequence.exists_diffeomorph_last_of_pullback_eraseEmpty ⇑g _ _ _ ⟨hinj, hsurj⟩
    (fun p => AnalyticMap.restrictMap_apply _ _ _ _ p) _ _ hJ'

end Hironaka.Manifold

end
