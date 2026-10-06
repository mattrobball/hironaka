/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
import Hironaka.Resolution.Algebraic.Kol07.GoingUp
import Hironaka.Resolution.Algebraic.MaximalContact.Sequence
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedBridge
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainDescentTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainLift
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.Restrict
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.Snc.RelativeDimension
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The descent of the chain form along a pushforward

The induction step of the statement CP1 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) on the scheme: Włodarczyk's proof
descends to the hypersurface of maximal contact and runs the algorithm there; in Kollár's order the
run on `H` is pushed forward to `X` ([Kol07, Definition 30, 30.3]; the proof of [Kol07, Lemma 102]).
The chain form of the level data on `H` at a point of stage `i` of the run `L` on `H` gives the
chain form of the data on `X` at the image point of the corresponding stage of `L.pushforward ι`:
the stage embedding `g = L.pushforwardStageHom ι i` is a closed immersion with kernel the strict
transform `H_i` (`ker_pushforwardStageHom`), `H_i` is a smooth hypersurface with `H_i ≤ J_i`
(maximal contact persists along an order-`≥ 1` run,
`IsOrderGeSeq.strictTransformSeq_le_and_isSmoothDivisor`) and `H_i ≤ c̃_i`; the three pullbacks
along `g` of the data on `X_i` are the data of `L` on `H_i` — the boundary through the restriction
identity (`totalTransformSeq_comap_pullbackStageHom_of_forall_lt`), the marked transform through
`IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom`, the strict transform through
`strictTransformSeq_pushforward_comap`
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainDescentTools`), the first two carried across
`pullback_pushforward` by the heterogeneous-equality transports of
`Hironaka.Resolution.Algebraic.Kol07.GoingUp` — and the lift of
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainLift` in its closed-immersion form lifts the level
form. The hypersurfaces of maximal contact are those of [Kol07, Theorem 80]. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Pushforward`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Scheme.IdealSheafData
  Hironaka.Sequence

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}

/-- **The descent of the chain form along a pushforward**: for `H ⊆ X` a smooth hypersurface with
`H ⊆ V(J)`, `H ∪ E` snc, `c ⊇ H` (a component inside `H`), and a run `L` on `H` whose pushforward
to `X` is a smooth run of order `≥ 1` for `(J, 1, E)`, the chain form of the level data on `H` at a
point of stage `i` gives the chain form of the data on `X` at the image point of the corresponding
stage ([Kol07, Definition 30, 30.3]; [Kol07, Theorem 80 (2)] for the hypersurface of maximal
contact). -/
theorem chainRelativeAt_pushforward (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] {H : X.IdealSheafData} (hH : IsSmoothDivisor H)
    {E : DivisorFamily X} (hE : E.IsSnc) (hEH : (E.append H).IsSnc) {J c : X.IdealSheafData}
    (hHJ : H ≤ J) (hHc : H ≤ c) (L : BlowUpSequence H.subscheme)
    (hS : (L.pushforward H.subschemeι).IsOrderGeSeq f J 1 E) (i : Fin (L.length + 1))
    {p : L.stage i}
    (h : ChainRelativeAt (L.totalTransformSeq (E.comap H.subschemeι) i)
      (L.markedTransformSeq (J.comap H.subschemeι) 1 i)
      (L.strictTransformSeq (c.comap H.subschemeι) i) p) :
    ChainRelativeAt
      ((L.pushforward H.subschemeι).totalTransformSeq E (L.pushforwardStageIdx H.subschemeι i))
      ((L.pushforward H.subschemeι).markedTransformSeq J 1 (L.pushforwardStageIdx H.subschemeι i))
      ((L.pushforward H.subschemeι).strictTransformSeq c (L.pushforwardStageIdx H.subschemeι i))
      (L.pushforwardStageHom H.subschemeι i p) := by
  obtain ⟨j, hj⟩ := i
  have hsmf : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hker : H.subschemeι.ker = H := IdealSheafData.ker_subschemeι H
  have hjS : j < (L.pushforward H.subschemeι).length + 1 := by
    rw [length_pushforward]
    exact hj
  -- the stage embedding: a closed immersion with kernel `H_j`
  have hgci : IsClosedImmersion (L.pushforwardStageHom H.subschemeι ⟨j, hj⟩) :=
    isClosedImmersion_pushforwardStageHom L H.subschemeι ⟨j, hj⟩
  have hgker : (L.pushforwardStageHom H.subschemeι ⟨j, hj⟩).ker =
      (L.pushforward H.subschemeι).strictTransformSeq H ⟨j, hjS⟩ := by
    have := ker_pushforwardStageHom L H.subschemeι ⟨j, hj⟩
    rw [hker] at this
    exact this
  -- the run's clauses
  have hsm : (L.pushforward H.subschemeι).IsSmooth f := hS.1
  have hsnc : ∀ l : Fin (L.pushforward H.subschemeι).length,
      ((L.pushforward H.subschemeι).totalTransformSeq E l.castSucc).HasSncWith
        ((L.pushforward H.subschemeι).center l) := fun l => (hS.2 l).1
  have hZ : ∀ l : Fin (L.pushforward H.subschemeι).length,
      (L.pushforward H.subschemeι).strictTransformSeq H.subschemeι.ker l.castSucc ≤
        (L.pushforward H.subschemeι).center l := by
    intro l
    rw [hker]
    exact strictTransformSeq_le_center_pushforward_subschemeι H L l
  have hEH' : (E.append H.subschemeι.ker).IsSnc := by
    rw [hker]
    exact hEH
  -- the data at stage `j` on `X`
  have hEi : ((L.pushforward H.subschemeι).totalTransformSeq E ⟨j, hjS⟩).IsSnc :=
    IsOrderGeSeq.isSnc_totalTransformSeq f n hS hE ⟨j, hjS⟩
  obtain ⟨hHJi, hHi⟩ :=
    IsOrderGeSeq.strictTransformSeq_le_and_isSmoothDivisor f n hS hH hHJ ⟨j, hjS⟩
  have hHci : (L.pushforward H.subschemeι).strictTransformSeq H ⟨j, hjS⟩ ≤
      (L.pushforward H.subschemeι).strictTransformSeq c ⟨j, hjS⟩ :=
    strictTransformSeq_mono_mk _ hHc j hjS
  have hsmi : Smooth ((L.pushforward H.subschemeι).stageMap ⟨j, hjS⟩ ≫ f) :=
    IsSmooth.smooth_stageMap' hsm ⟨j, hjS⟩
  -- the inner run is smooth (the pull-back of the smooth pushforward along `H ↪ X`)
  have hLsm : L.IsSmooth (H.subschemeι ≫ f) := by
    have h0 := isSmooth_pullback_of_strictTransformSeq_le (L.pushforward H.subschemeι) H f
      (fun l => strictTransformSeq_le_center_pushforward_subschemeι H L l) hsm
    rwa [pullback_pushforward L H.subschemeι] at h0
  have hHdim : SmoothOfRelativeDimension (n - 1) (H.subschemeι ≫ f) :=
    smoothOfRelativeDimension_of_isSmoothDivisor f n H hH
  have hHsm : Smooth (H.subschemeι ≫ f) := SmoothOfRelativeDimension.smooth (n - 1) _
  have hLstage : Smooth (L.stageMap ⟨j, hj⟩ ≫ H.subschemeι ≫ f) :=
    IsSmooth.smooth_stageMap' hLsm ⟨j, hj⟩
  have hY : ∀ w : L.stage ⟨j, hj⟩, IsRegularLocalRing ((L.stage ⟨j, hj⟩).presheaf.stalk w) :=
    fun w => isRegularLocalRing_stalk (L.stageMap ⟨j, hj⟩ ≫ H.subschemeι ≫ f) w
  -- the pull-back of the pushforward is `L`; the stage embeddings agree
  have e : (L.pushforward H.subschemeι).pullback H.subschemeι = L := pullback_pushforward L _
  have hjP : j < ((L.pushforward H.subschemeι).pullback H.subschemeι).length + 1 := by
    rw [e]
    exact hj
  have es : ((L.pushforward H.subschemeι).pullback H.subschemeι).stage ⟨j, hjP⟩ =
      L.stage ⟨j, hj⟩ := stage_congr e j hjP hj
  have hφ : HEq ((L.pushforward H.subschemeι).pullbackStageHom H.subschemeι ⟨j, hjS⟩)
      (L.pushforwardStageHom H.subschemeι ⟨j, hj⟩) :=
    pullbackStageHom_pushforward_heq_mk L H.subschemeι j hjS hj
  -- (a) the boundary
  have hEcomap : ((L.pushforward H.subschemeι).totalTransformSeq E ⟨j, hjS⟩).comap
      (L.pushforwardStageHom H.subschemeι ⟨j, hj⟩) =
        L.totalTransformSeq (E.comap H.subschemeι) ⟨j, hj⟩ := by
    have hres := totalTransformSeq_comap_pullbackStageHom_of_forall_lt f
      (L.pushforward H.subschemeι) H.subschemeι E hsm hEH' j (fun l _ => hsnc l) hZ hjS
    have h1 := comap_congr_heq es hφ ((L.pushforward H.subschemeι).totalTransformSeq E ⟨j, hjS⟩)
    have h2 := totalTransformSeq_congr_heq e (E.comap H.subschemeι) j hjP hj
    exact eq_of_heq (h1.symm.trans ((heq_of_eq hres).trans h2))
  -- (b) the marked transform (Lemma 62 iterated)
  have hJcomap : ((L.pushforward H.subschemeι).markedTransformSeq J 1 ⟨j, hjS⟩).comap
      (L.pushforwardStageHom H.subschemeι ⟨j, hj⟩) =
        L.markedTransformSeq (J.comap H.subschemeι) 1 ⟨j, hj⟩ := by
    have hres := IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom_mk f n H.subschemeι hS j hjS
    have h1 := heq_comap es hφ ((L.pushforward H.subschemeι).markedTransformSeq J 1 ⟨j, hjS⟩)
    have h2 := markedTransformSeq_congr_heq e (J.comap H.subschemeι) 1 j hjP hj
    exact eq_of_heq (h1.symm.trans ((heq_of_eq hres.symm).trans h2))
  -- (c) the strict transform (S2b)
  have hccomap : ((L.pushforward H.subschemeι).strictTransformSeq c ⟨j, hjS⟩).comap
      (L.pushforwardStageHom H.subschemeι ⟨j, hj⟩) =
        L.strictTransformSeq (c.comap H.subschemeι) ⟨j, hj⟩ :=
    strictTransformSeq_pushforward_comap L H.subschemeι (by rw [hker]; exact hHc) ⟨j, hj⟩
  -- S1 in the closed-immersion form
  have h' : ChainRelativeAt
      (((L.pushforward H.subschemeι).totalTransformSeq E ⟨j, hjS⟩).comap
        (L.pushforwardStageHom H.subschemeι ⟨j, hj⟩))
      (((L.pushforward H.subschemeι).markedTransformSeq J 1 ⟨j, hjS⟩).comap
        (L.pushforwardStageHom H.subschemeι ⟨j, hj⟩))
      (((L.pushforward H.subschemeι).strictTransformSeq c ⟨j, hjS⟩).comap
        (L.pushforwardStageHom H.subschemeι ⟨j, hj⟩)) p := by
    rw [hEcomap, hJcomap, hccomap]
    exact h
  exact chainRelativeAt_of_closedImmersion ((L.pushforward H.subschemeι).stageMap ⟨j, hjS⟩ ≫ f)
    hEi hHi hHJi hHci (L.pushforwardStageHom H.subschemeι ⟨j, hj⟩) hgker hY h'

end Hironaka.Resolution
