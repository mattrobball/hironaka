/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Functoriality
public import Hironaka.Resolution.Analytic.OrderReduction.BD
import Hironaka.Manifold.BlowUp.Transform.Bundled
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Resolution.Analytic.Functor.PullbackTransport
import Hironaka.Resolution.Analytic.OrderReduction.BDCore
import Hironaka.Resolution.Analytic.OrderReduction.TunedLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Lemma 102 (2): commutation with surjective local analytic isomorphisms

Clause (2) of [Kol07, Lemma 102] says that `BD_{n,m,j}` commutes with smooth morphisms; its proof
reads that the functoriality of `BD_{n,m,j}(X, I, E)` follows "from the corresponding
functoriality properties" of `BMO_{n-1,m}(S, I_0|_S, E_S)`. For a surjective local analytic
isomorphism `h : N → M` (the analytic counterpart of a smooth surjection), pulling back by `h` and
restricting to `h^{-1}(E^j)` is the same as restricting to `E^j` and pulling back by the
restriction of `h`, so the value of the input on the restricted triple pulls back
(`BMOanData.commutesWithLocalIsos`), hence so does its push-forward, and the first blow-up pulls
back since `Z_{-1}` does (`BD.Zminus1_comap`).

The identification of the pull-back of a pushed-forward list with the push-forward of the
pulled-back list along the restricted map, `BlowUpSequence.pushforward_pullback`, enters here as the
hypothesis `PushforwardPullback ψ₀`; it is supplied in `BDErase.lean`, where the clause is stated
unconditionally (`BDan_pullback_of_surjective`).

The first centre of the pulled-back data is only propositionally the preimage of the first centre
(`BD.Zminus1_comap`), and likewise the transform of `E^j`; the dependent types are handled by
reading `BDan.core` **over an arbitrary closed hypersurface `Z` and an arbitrary hypersurface `S'`
of its blow-up**, with the identifications `Z = Z_{-1}`, `S' = S_0` as hypotheses (`core_eq_of_eq`,
a substitution: the core over the input's value on `restrictedTripleOf`).

* `PushforwardPullback ψ₀` — the identification as a hypothesis.
* `BDan.bmoClass_restrictedTripleOf`, `BDan.core_eq_of_eq`, `BDan.core_congr` — the core over
  an arbitrary `Z` and `S'` (`BDan.restrictedTripleOf`, `BD.lean`).
* `HypersurfaceFamily.emptyMember_comap` — emptying a member commutes with the inverse image.
* `BDan.restrictedTripleOf_isPullbackOf` — the restricted triple of the pulled-back data is the
  pull-back of the restricted triple along the restriction of `h` (the proof of
  [Kol07, Lemma 102]: pulling back by `h` and then restricting to `E^j_Y` gives "the same result"
  as restricting to `E^j` and then pulling back by `h|_{E^j_Y}`).
* `BDan.core_pullback_of_surjective_of_pushforwardPullback`,
  `BDan_pullback_of_surjective_of_pushforwardPullback` — the clause for the core and for `BDan`,
  given the identification.
-/

@[expose] public section

noncomputable section

open Set Topology IsLocalRing
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

/-- The pull-back along a local analytic isomorphism `g` of the push-forward of a list of centres on
a closed hypersurface `S` is the push-forward, on `g^{-1}(S)`, of the pull-back of the list along
the restriction of `g` to `g^{-1}(S) → S`; as a hypothesis on the model (it is
`BlowUpSequence.pushforward_pullback`, supplied in `BDErase.lean`). The proof of [Kol07, Lemma 102]
uses it when it pulls back the pushed-forward sequence. -/
def PushforwardPullback [FiniteDimensional 𝕜 E] (ψ : E ≃L[𝕜] (Fin n → 𝕜)) : Prop :=
  ∀ {M N : AnalyticManifold.{u} 𝕜 E} {S : Set M} (hS : IsClosedSubmanifold ψ S 1)
    (g : AnalyticMap N M) (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g)
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin
        (n - 1) → 𝕜)) hS.toAnalyticManifold),
    (L.pushforward hS).pullback g hg =
      (L.pullback ((hS.preimage_of_isLocalDiffeomorph hg).restrictMap hS g g.contMDiff
          fun _ hx => hx)
        (BD.isLocalDiffeomorph_restrictMap g hg hS)).pushforward
        (hS.preimage_of_isLocalDiffeomorph hg)

/-- Emptying the member `j` commutes with the inverse image of a family. -/
theorem _root_.Manifold.HypersurfaceFamily.emptyMember_comap {M N : Type u}
    (F : HypersurfaceFamily M) (h : N → M)
    (j : F.ι) : (F.comap h).emptyMember j = (F.emptyMember j).comap h := by
  unfold HypersurfaceFamily.emptyMember HypersurfaceFamily.comap
  congr 1
  funext k
  by_cases hk : k = j
  · simp [hk]
  · simp [hk]

namespace BDan

open _root_.Manifold

variable [FiniteDimensional 𝕜 E] {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  (T : AnalyticTriple ψ₀ M) (s : ℕ) (j : T.F.ι)

/-! ### The core over an arbitrary closed hypersurface -/

section Of

variable {Z : Set M} (hZ : IsClosedSubmanifold ψ₀ Z 1) {S' : Set (Manifold.blowUp ψ₀ hZ)}
  (hS' : IsClosedSubmanifold ψ₀ S' 1)

/-- The restricted triple over `Z` and `S'` lies in the marked class `BMOClass s`. -/
theorem bmoClass_restrictedTripleOf (hT : BDClass s T) (hZeq : Z = BD.Zminus1 T.I s (T.F.hyp j))
    (hSeq : S' = transformSOf T j hZ) :
    AnalyticTriple.BMOClass s (restrictedTripleOf T s j hZ hS' hT hZeq hSeq) := by
  subst hZeq
  subst hSeq
  exact bmoClass_restrictedTriple T s j hT

/-- `BDan.core` read over any closed hypersurface `Z = Z_{-1}` and any hypersurface `S' = S_0` of
its blow-up (a substitution): the core over the input's value on `restrictedTripleOf`. -/
theorem core_eq_of_eq (inp : BMOanData 𝕜 (n - 1) s) (hT : BDClass s T)
    (hZeq : Z = BD.Zminus1 T.I s (T.F.hyp j)) (hSeq : S' = transformSOf T j hZ) :
    core T s j inp hT =
      coreOfListOf hZ hS' (inp.functor.seq (restrictedTripleOf T s j hZ hS' hT hZeq hSeq)
        (bmoClass_restrictedTripleOf T s j hZ hS' hT hZeq hSeq)) := by
  subst hZeq
  subst hSeq
  rfl

end Of

/-- The core respects equality of triples, with the member index and the proof of membership in the
class transported. -/
theorem core_congr (inp : BMOanData 𝕜 (n - 1) s) {T₁ T₂ : AnalyticTriple ψ₀ M} (e : T₁ = T₂)
    (j₁ : T₁.F.ι) (j₂ : T₂.F.ι) (hj : HEq j₁ j₂) (h₁ : BDClass s T₁) (h₂ : BDClass s T₂) :
    core T₁ s j₁ inp h₁ = core T₂ s j₂ inp h₂ := by
  subst e
  obtain rfl := eq_of_heq hj
  rfl

/-! ### The restricted triple of the pulled-back data -/

section Pullback

variable {N : AnalyticManifold.{u} 𝕜 E} (h : AnalyticMap N M)
  (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)

/-- The transform of `h^{-1}(E^j)` under the blow-up of `h^{-1}(Z_{-1})` is the preimage, under the
lift of `h` to the blow-ups, of the transform `S_0` of `E^j`. -/
theorem preimage_liftStep_transformS :
    ⇑(AnalyticManifold.BlowUpSequence.liftStep h hh (BD.isClosedSubmanifold_Zminus1 T s j)) ⁻¹'
        transformS T s j =
      transformSOf (T.pullback h hh) j
        ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hh) := by
  ext q
  change Manifold.blowUpπ ψ₀ _ (AnalyticManifold.BlowUpSequence.liftStep h hh _ q) ∈ T.F.hyp j ↔
    h (Manifold.blowUpπ ψ₀ ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
        hh) q) ∈
      T.F.hyp j
  rw [AnalyticManifold.BlowUpSequence.blowUpπ_liftStep]

/-- The weak transform of `h^* 𝓘` under the blow-up of `h^{-1}(Z_{-1})` is the pull-back of `I_0`
along the lift of `h` to the blow-ups. -/
theorem weakTransformIOf_pullback :
    weakTransformIOf (T.pullback h hh)
        ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hh) =
      Manifold.IdealSheaf.pullback _ (AnalyticManifold.BlowUpSequence.liftStep h hh
          (BD.isClosedSubmanifold_Zminus1 T s j)).contMDiff
        (weakTransformI T s j) := by
  rw [← weakTransform_eq_weakTransformI,
    weakTransform_comap_liftStep h hh (BD.isClosedSubmanifold_Zminus1 T s j) T.I]
  exact (weakTransform_eq
    (Manifold.blowUpπ ψ₀ ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hh))
    ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hh)
    (IsClosedSubmanifold.isIdealSheafOf_idealSheaf _) (isBlowUp_blowUpπ ψ₀ _)
    (T.I.pullback h h.contMDiff)).symm

/-- The family `E - E^j` of the pulled-back data, pulled back along the blow-up of `h^{-1}(Z_{-1})`,
is the pull-back along the lift of `h` of the family `(E - E^j)|_{X_0}`. -/
theorem boundaryMinusOf_pullback :
    boundaryMinusOf (T.pullback h hh) j
        ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hh) =
      (boundaryMinus T s j).comap
        ⇑(AnalyticManifold.BlowUpSequence.liftStep h hh (BD.isClosedSubmanifold_Zminus1 T s j)) :=
            by
  unfold boundaryMinus boundaryMinusOf
  change ((T.F.comap h).emptyMember j).comap _ = _
  rw [HypersurfaceFamily.emptyMember_comap, HypersurfaceFamily.comap_comap,
    HypersurfaceFamily.comap_comap]
  congr 1
  funext q
  exact (AnalyticManifold.BlowUpSequence.blowUpπ_liftStep h hh _ q).symm

/-- The proof of [Kol07, Lemma 102] (pulling back by `h` and then restricting to `E^j_Y` gives "the
same result" as restricting to `E^j` and then pulling back by `h|_{E^j_Y}`): the
restricted triple of the pulled-back data, over `h^{-1}(Z_{-1})` and the preimage of `S_0` under
the lift of `h`, is the pull-back of the restricted triple along the restriction of the lift of `h`
to the hypersurfaces (`BD.pullback_inclusionMap_pullback`, `BD.comap_inclusionMap_comap`). -/
theorem restrictedTripleOf_isPullbackOf (hT : BDClass s T) (hT' : BDClass s (T.pullback h hh)) :
    (restrictedTripleOf (T.pullback h hh) s j
        ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hh)
        ((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep h hh _)) hT'
        (BD.Zminus1_comap h hh T.I s (T.isSnc.1 j)).symm
        (preimage_liftStep_transformS T s j h hh)).IsPullbackOf
      (restrictedTriple T s j hT)
      (((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep h hh _)).restrictMap
        (isClosedSubmanifold_transformS T s j)
        (AnalyticManifold.BlowUpSequence.liftStep h hh (BD.isClosedSubmanifold_Zminus1 T s j))
        (AnalyticManifold.BlowUpSequence.liftStep h hh _).contMDiff fun _ hx => hx) := by
  refine ⟨?_, ?_⟩
  · change (weakTransformIOf (T.pullback h hh) _).pullback _ _ =
      ((weakTransformI T s j).pullback _ _).pullback _ _
    rw [← BD.pullback_inclusionMap_pullback _ (weakTransformI T s j)
      (isClosedSubmanifold_transformS T s j), weakTransformIOf_pullback]
  · change (boundaryMinusOf (T.pullback h hh) j _).comap
        ⇑((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep h hh _)).inclusionMap =
      ((boundaryMinus T s j).comap ⇑(isClosedSubmanifold_transformS T s j).inclusionMap).comap _
    rw [← BD.comap_inclusionMap_comap _ (boundaryMinus T s j)
      (isClosedSubmanifold_transformS T s j), boundaryMinusOf_pullback]

/-- [Kol07, Lemma 102 (2)] for the core at the mark `s`, along a surjective local analytic
isomorphism `h`, given the identification `PushforwardPullback`: the core of the pulled-back data is
the pull-back of the core. The first centre pulls back by `BD.Zminus1_comap`; the pushed-forward
tail pulls back by the identification and by the commutation of the input functor with the
restriction of the lift of `h`, a surjective local analytic isomorphism between the restricted
triples (`restrictedTripleOf_isPullbackOf`). -/
theorem core_pullback_of_surjective_of_pushforwardPullback (hpp : PushforwardPullback.{u} ψ₀)
    (inp : BMOanData 𝕜 (n - 1) s) (hs : Function.Surjective h) (hT : BDClass s T)
    (hT' : BDClass s (T.pullback h hh)) :
    core (T.pullback h hh) s j inp hT' = (core T s j inp hT).pullback h hh := by
  -- the pulled-back core over `h⁻¹(Z_{-1})` and the preimage of `S_0`
  rw [core_eq_of_eq (T.pullback h hh) s j
      ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hh)
      ((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep h hh _)) inp hT'
      (BD.Zminus1_comap h hh T.I s (T.isSnc.1 j)).symm (preimage_liftStep_transformS T s j h hh)]
  -- the pull-back of the core: the first step and the push-forward pull back
  unfold core coreOfListOf
  rw [AnalyticManifold.BlowUpSequence.eraseEmpty_pullback _ h hh hs,
      AnalyticManifold.BlowUpSequence.pullback_cons,
    hpp (isClosedSubmanifold_transformS T s j)
      (AnalyticManifold.BlowUpSequence.liftStep h hh (BD.isClosedSubmanifold_Zminus1 T s j))
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep h hh
          (BD.isClosedSubmanifold_Zminus1 T s j)) _]
  -- the input's functoriality on the restricted triples
  have hX := inp.commutesWithLocalIsos.1 (restrictedTriple T s j hT) _ _
    (BD.isLocalDiffeomorph_restrictMap _
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep h hh _)
      (isClosedSubmanifold_transformS T s j))
    (BD.surjective_restrictMap _
      (AnalyticManifold.BlowUpSequence.surjective_liftStep h hh
          (BD.isClosedSubmanifold_Zminus1 T s j) hs)
      (isClosedSubmanifold_transformS T s j) _)
    (restrictedTripleOf_isPullbackOf T s j h hh hT hT') (bmoClass_restrictedTriple T s j hT)
    (bmoClass_restrictedTripleOf (T.pullback h hh) s j _ _ hT' _ _)
  rw [hX]

end Pullback

end BDan

section Assembly

variable [FiniteDimensional 𝕜 E] {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  {m : ℕ}

/-- [Kol07, Lemma 102 (2)], the first bullet of [Kol07, 34.1], given the identification
`PushforwardPullback`: `BD_{n,m,j}` commutes with surjective local analytic isomorphisms. It is
the clause for the core at the tuned triple, tuning commuting with pull-back
(`AnalyticTriple.tuned_pullback`). -/
theorem BDan_pullback_of_surjective_of_pushforwardPullback (hpp : PushforwardPullback.{u} ψ₀)
    (inp : BMOanData 𝕜 (n - 1) (tuningParam m)) {N : AnalyticManifold.{u} 𝕜 E}
    (T : AnalyticTriple ψ₀ M) (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (hs : Function.Surjective h) (hT : AnalyticTriple.BOClass m T)
    (hT' : AnalyticTriple.BOClass m (T.pullback h hh)) (j : T.F.ι) :
    BDan m inp (T.pullback h hh) hT' j = (BDan m inp T hT j).pullback h hh := by
  have e := AnalyticTriple.tuned_pullback T hT.1 h hh
  have hTt : BDan.BDClass (tuningParam m) ((T.tuned m hT.1).pullback h hh) := by
    rw [← e]
    exact ⟨AnalyticTriple.boClass_tuned hT', AnalyticTriple.isDBalanced_tuned hT'⟩
  unfold BDan
  exact (BDan.core_congr (tuningParam m) inp e j j HEq.rfl _ hTt).trans
    (BDan.core_pullback_of_surjective_of_pushforwardPullback (T.tuned m hT.1) (tuningParam m) j h hh
      hpp inp hs _ hTt)

end Assembly

end Hironaka.Manifold

end
