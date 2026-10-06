/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.Family
public import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Defs
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Hom
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.ExtensionOf
import Hironaka.Resolution.Analytic.Functor.PullbackLiftStages
import Hironaka.Resolution.Analytic.Functor.PullbackSequence
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Pull-backs of blow-up sequences up to empty blow-ups

The vocabulary predicate `FiniteSuccession.IsPullbackUpToEmptyAlong R S g` (Włodarczyk's "the
induced sequence `g^*(S)` is an extension of `R`" [Wlo09, Theorem 3.5.1 (2)]) is read off the
pull-back of a blow-up sequence along a local analytic isomorphism (`BlowUpSequence.pullback`, the
sequence of the fibre products [Wlo09, Proposition 3.4.1]):

* `BlowUpSequence.isPullbackUpToEmptyAlong_of_isExtensionOf`: if the pull-back of `L` along
  `h : U' → U` is an extension of `R` ([Wlo09, Definition 3.2.6]) and `h` is the restriction of
  `g : N → M`, then `R` is the pull-back of `L` along `g` up to empty blow-ups. The lift of a
  stage `R_{j_k}` to `L_k` is the stage lift of the pull-back (`pullbackLift`) after the inverse of
  the identification of the extension; the clauses come from the stage lifts
  (`stageMap_pullbackLift`, `map_pullbackLift`) and the centres of the pull-back
  (`center_pullback`).
* `BlowUpSequence.isPullbackUpToEmptyAlong_eraseEmpty_pullback`: the pull-back with its empty
  blow-ups erased ([Kol07, 32]) is such an `R` (`isExtensionOf_toSuccession_eraseEmpty`).
* `CompatibleFamily.isPullbackUpToEmptyAlong_seqOn`: for two compatible families whose values on
  `U'` and on its image `g(U')` are related by the commutation equation of a family functor
  (`AnalyticFamilyFunctor.CommutesWithLocalIsos`, Kollár's [Kol07, 34.1] read per open), the value
  on `U'` is the pull-back along `g` up to empty blow-ups of the value on every relatively compact
  open `U ⊇ g(U')`: the compatibility of the family along `g(U') ⊆ U`
  (`CompatibleFamily.compat`), `eraseEmpty_pullback_eraseEmpty` and `pullback_comp`.
-/

public section

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- **An extension of the pull-back is a pull-back up to empty blow-ups**: if the pull-back of
the sequence `L` over `U ⊆ M` along the local analytic isomorphism `h : U' → U` is an extension of
`R` ([Wlo09, Definition 3.2.6]) and `h` is the restriction of `g : N → M`, then `R` is the
pull-back of `L` along `g` up to blow-ups with empty centre ([Wlo09, Theorem 3.5.1 (2)]): the lift
of the stage `R_{j_k}` is the stage lift of the pull-back after the inverse of the identification
of the extension. -/
theorem isPullbackUpToEmptyAlong_of_isExtensionOf {M N : AnalyticManifold.{u} 𝕜 E}
    {U : Opens M} {U' : Opens N} (L : BlowUpSequence ψ₀ (M.restrict U))
    (h : AnalyticMap (N.restrict U') (M.restrict U))
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (g : AnalyticMap N M)
    (hgh : ∀ p, M.inclusion U (h p) = g (N.inclusion U' p))
    {R : FiniteSuccession (N.restrict U')}
    (hR : (L.pullback h hh).toSuccession.IsExtensionOf R) :
    R.IsPullbackUpToEmptyAlong L.toSuccession g := by
  obtain ⟨blk, e, h0, hlast, hstep, hover, hmap, hcj, hcn⟩ := hR
  have hlen : (L.pullback h hh).length = L.length := length_pullback L h hh
  -- the stage indices of `L` read on its pull-back
  let c : Fin (L.length + 1) → Fin ((L.pullback h hh).toSuccession.length + 1) :=
    fun k => ⟨k.1, Nat.lt_of_lt_of_eq k.2 (congrArg (· + 1) hlen.symm)⟩
  let cl : Fin L.length → Fin (L.pullback h hh).toSuccession.length :=
    fun k => ⟨k.1, Nat.lt_of_lt_of_eq k.2 hlen.symm⟩
  refine FiniteSuccession.isPullbackUpToEmptyAlong_iff.mpr ⟨fun k => blk (c k),
    fun k => (L.pullbackLift h hh k).comp (e (c k)).symm.toAnalyticMap, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · exact h0
  · have : c (Fin.last _) = Fin.last _ := Fin.ext (by simp [c, hlen])
    simp only [this]
    exact hlast
  · intro k
    exact hstep (cl k)
  · -- local analytic isomorphisms
    intro k x
    exact IsLocalDiffeomorphAt.comp (hf := (e (c k)).symm.isLocalDiffeomorph x)
      (hg := isLocalDiffeomorph_pullbackLift L h hh k _)
  · -- over `g`
    intro k p
    change M.inclusion U (L.toSuccession.stageMap k (L.pullbackLift h hh k ((e (c k)).symm p))) = _
    rw [stageMap_pullbackLift, ← hover (c k) ((e (c k)).symm p), Diffeomorph.apply_symm_apply]
    exact hgh _
  · -- the blow-downs
    intro k hle p
    change L.toSuccession.map k (L.pullbackLift h hh k.succ ((e (c k.succ)).symm p)) =
      L.pullbackLift h hh k.castSucc ((e (c k.castSucc)).symm (R.stageMapLE hle p))
    have h1 : R.stageMapLE hle (e (c k.succ) ((e (c k.succ)).symm p)) =
        e (c k.castSucc) ((L.pullback h hh).toSuccession.map (cl k) ((e (c k.succ)).symm p)) :=
      hmap (cl k) hle ((e (c k.succ)).symm p)
    rw [Diffeomorph.apply_symm_apply] at h1
    rw [h1, Diffeomorph.symm_apply_apply]
    exact (map_pullbackLift L h hh k _).symm
  · -- the centres at a jump
    intro k ha hj
    have h1 : (L.pullback h hh).toSuccession.center (cl k) =
        (R.centerAt (blk (c k.castSucc)) ha).pullback (e (c k.castSucc))
          (e (c k.castSucc)).contMDiff :=
      hcj (cl k) ha hj
    have h2 := center_pullback L h hh k
    change _ = (L.toSuccession.center k).pullback
      (⇑(L.pullbackLift h hh k.castSucc) ∘ ⇑(e (c k.castSucc)).symm)
      ((L.pullbackLift h hh k.castSucc).contMDiff.comp (e (c k.castSucc)).symm.contMDiff)
    rw [← _root_.Manifold.IdealSheaf.pullback_pullback (L.toSuccession.center k)
      (L.pullbackLift h hh k.castSucc) (L.pullbackLift h hh k.castSucc).contMDiff
      ((e (c k.castSucc)).symm) (e (c k.castSucc)).symm.contMDiff, ← h2]
    change _ = ((L.pullback h hh).toSuccession.center (cl k)).pullback _ _
    rw [h1, _root_.Manifold.IdealSheaf.pullback_pullback,
      _root_.Manifold.IdealSheaf.pullback_congr _ _ contMDiff_id
        (show ⇑(e (c k.castSucc)) ∘ ⇑(e (c k.castSucc)).symm = id from
          funext fun x => (e (c k.castSucc)).apply_symm_apply x)]
    exact (_root_.Manifold.IdealSheaf.pullback_id_eq_self _).symm
  · -- the empty centres at a non-jump
    intro k hj
    have h1 := hcn (cl k) hj
    have h2 := center_pullback L h hh k
    change ((L.toSuccession.center k).pullback
      (⇑(L.pullbackLift h hh k.castSucc) ∘ ⇑(e (c k.castSucc)).symm)
      ((L.pullbackLift h hh k.castSucc).contMDiff.comp (e (c k.castSucc)).symm.contMDiff)).support
        = ∅
    rw [← _root_.Manifold.IdealSheaf.pullback_pullback (L.toSuccession.center k)
      (L.pullbackLift h hh k.castSucc) (L.pullbackLift h hh k.castSucc).contMDiff
      ((e (c k.castSucc)).symm) (e (c k.castSucc)).symm.contMDiff, ← h2]
    change (((L.pullback h hh).toSuccession.center (cl k)).pullback _ _).support = ∅
    rw [_root_.Manifold.IdealSheaf.support_pullback, h1, Set.preimage_empty]

/-- **The pull-back with its empty blow-ups erased** ([Kol07, 32]) is the pull-back up to empty
blow-ups: `isPullbackUpToEmptyAlong_of_isExtensionOf` at the extension
`isExtensionOf_toSuccession_eraseEmpty`. -/
theorem isPullbackUpToEmptyAlong_eraseEmpty_pullback {M N : AnalyticManifold.{u} 𝕜 E}
    {U : Opens M} {U' : Opens N} (L : BlowUpSequence ψ₀ (M.restrict U))
    (h : AnalyticMap (N.restrict U') (M.restrict U))
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (g : AnalyticMap N M)
    (hgh : ∀ p, M.inclusion U (h p) = g (N.inclusion U' p)) :
    (L.pullback h hh).eraseEmpty.toSuccession.IsPullbackUpToEmptyAlong L.toSuccession g :=
  isPullbackUpToEmptyAlong_of_isExtensionOf L h hh g hgh (isExtensionOf_toSuccession_eraseEmpty _)

end AnalyticManifold.BlowUpSequence

namespace Hironaka.Manifold.CompatibleFamily

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- **The value on `U'` is the pull-back along `g` of the value on any `U ⊇ g(U')`**, up to empty
blow-ups ([Wlo09, Theorem 3.5.1 (2)]), for two compatible families related on `U'` and its image
`g(U')` by the commutation equation of [Kol07, 34.1]: the compatibility of the family along
`g(U') ⊆ U` rewrites the value on `g(U')` as the erased pull-back of the value on `U`, the two
erasures and pull-backs combine (`eraseEmpty_pullback_eraseEmpty`, `pullback_comp`), and
`isPullbackUpToEmptyAlong_eraseEmpty_pullback` reads the result. -/
theorem isPullbackUpToEmptyAlong_seqOn {M N : AnalyticManifold.{u} 𝕜 E}
    {T : AnalyticTriple ψ₀ M} {T' : AnalyticTriple ψ₀ N} (C : CompatibleFamily T)
    (C' : CompatibleFamily T') (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) (U' : Opens N)
    (hU' : IsCompact (closure (U' : Set N)))
    (hC : C'.seqOn U' hU' =
      ((C.seqOn (AnalyticMap.imageOpens g hg U')
          (AnalyticMap.isCompact_closure_image g hU')).pullback
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' _ Set.Subset.rfl)).eraseEmpty)
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) (hgU : ⇑g '' (U' : Set N) ⊆ U) :
    (C'.seqOn U' hU').toSuccession.IsPullbackUpToEmptyAlong (C.seqOn U hU).toSuccession g := by
  have hle : AnalyticMap.imageOpens g hg U' ≤ U := hgU
  rw [hC, C.compat _ U (AnalyticMap.isCompact_closure_image g hU') hU hle,
    AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
    AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _,
    AnalyticManifold.BlowUpSequence.pullback_congr _
      (f := (M.restrictLE hle).comp
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl))
      (g := AnalyticMap.restrictMap g U' U hgU)
      (ContMDiffMap.ext fun _ => rfl) _ (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' U hgU)]
  exact AnalyticManifold.BlowUpSequence.isPullbackUpToEmptyAlong_eraseEmpty_pullback _ _ _ g
    fun _ => rfl

end Hironaka.Manifold.CompatibleFamily

end

end
