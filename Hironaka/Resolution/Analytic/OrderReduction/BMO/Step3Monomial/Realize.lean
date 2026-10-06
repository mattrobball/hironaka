/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Step3Phases
public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmpty
public import Hironaka.Manifold.FiniteSuccession.Order
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.BlowUpPieces
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Ideal
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.Snc.Dictionary
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Hironaka.Resolution.Analytic.MaximalContact.MarkedOneLemmas
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Center
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Kernel
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Transform
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Running the monomial procedure on an analytic manifold

The combinatorial model `Hironaka.Monomial.MonomialState.step3` runs Kollár's monomial procedure
[Kol07, 111, Step 3] on the combinatorial state and terminates. This file realises its list of
centres as a list of blow-ups on the manifold (`PieceFamily.realize`). Each centre of the run is
Kollár's choice at its level, a centre of the state, whose locus is a closed submanifold having
simple normal crossings with the boundary family (`BMO/Step3Monomial/Center.lean`); the transformed
piece family realises the transformed boundary and its state is the combinatorial blow-up
(`BMO/Step3Monomial/Kernel.lean`, `BMO/Step3Monomial/RealizesBlowUp.lean`); and the marked transform
of the monomial ideal is the monomial ideal of the transformed family
(`BMO/Step3Monomial/Transform.lean`). Hence, along the whole run (`realizeAux_spec`): no centre is
empty ([Kol07, 32]); the sequence is a smooth blow-up sequence of order `≥ m` for the monomial ideal
with the family's boundary ([Kol07, Definition 66 (2′)–(4′)]); and at the last stage the marked
transform of the monomial ideal is the monomial ideal of a family whose state is the final state of
the combinatorial run, so its order at every point is below `m` ("at the end of Step 3.n we are
done", [Kol07, 111, Step 3]). These are `realize_noEmptyCenters`, `realize_isOfOrderGe` and
`realize_ord_lt`.
-/

@[expose] public section

open Set Topology AnalyticManifold Hironaka.Monomial
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

variable (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)) in
/-- A list of centres has smooth loci along the run: each locus is a closed submanifold of
codimension the common cardinality of its faces, the next family being the transformed one. This is
the proof-carrying invariant that the construction of the list of blow-ups needs at every step. -/
def PieceFamily.SmoothCenters :
    {N : AnalyticManifold.{u} 𝕜 E} → PieceFamily N → ℕ → List (Finset (Finset ℕ)) → Prop
  | _, _, _, [] => True
  | _, Φ, m, S :: L => ∃ hZ : Manifold.IsClosedSubmanifold ψ₀ (Φ.centerOf S) (faceCard S),
      PieceFamily.SmoothCenters (Φ.blowUpPieces S m hZ) m L

namespace PieceFamily

open _root_.Manifold

variable {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {N : AnalyticManifold.{u} 𝕜 E} {Φ : PieceFamily N} {m : ℕ}
  {S : Finset (Finset ℕ)} {L : List (Finset (Finset ℕ))}

theorem smoothCenters_nil : SmoothCenters ψ₀ Φ m [] := trivial

theorem smoothCenters_cons_iff :
    SmoothCenters ψ₀ Φ m (S :: L) ↔
      ∃ hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) (faceCard S),
        SmoothCenters ψ₀ (Φ.blowUpPieces S m hZ) m L :=
  Iff.rfl

theorem SmoothCenters.head (h : SmoothCenters ψ₀ Φ m (S :: L)) :
    IsClosedSubmanifold ψ₀ (Φ.centerOf S) (faceCard S) :=
  (smoothCenters_cons_iff.mp h).elim fun hZ _ => hZ

theorem SmoothCenters.tail (h : SmoothCenters ψ₀ Φ m (S :: L)) :
    SmoothCenters ψ₀ (Φ.blowUpPieces S m h.head) m L :=
  (smoothCenters_cons_iff.mp h).elim fun _ hL => hL

variable (ψ₀) in
/-- The realisation of a list of centres as a list of blow-ups, by structural recursion on the list,
the smoothness of each centre supplied by `SmoothCenters`. -/
noncomputable def realizeAux :
    {N : AnalyticManifold.{u} 𝕜 E} → (Φ : PieceFamily N) → (m : ℕ) →
      (L : List (Finset (Finset ℕ))) → SmoothCenters ψ₀ Φ m L → BlowUpSequence ψ₀ N
  | _, _, _, [], _ => BlowUpSequence.nil _
  | _, Φ, m, S :: L, h =>
    BlowUpSequence.cons h.head (realizeAux (Φ.blowUpPieces S m h.head) m L h.tail)

theorem realizeAux_nil (h : SmoothCenters ψ₀ Φ m []) :
    realizeAux ψ₀ Φ m [] h = BlowUpSequence.nil N := rfl

theorem realizeAux_cons (h : SmoothCenters ψ₀ Φ m (S :: L)) :
    realizeAux ψ₀ Φ m (S :: L) h =
      BlowUpSequence.cons h.head (realizeAux ψ₀ (Φ.blowUpPieces S m h.head) m L h.tail) := rfl

/-! ### The run of Kollár's Step 3 has smooth loci, and its realisation's postconditions -/

/-- Along a run of the combinatorial procedure from a realising family (every centre Kollár's choice
at some level), the realisation has no empty centre, is a smooth blow-up sequence of order `≥ m` for
the monomial ideal with the family's boundary, and ends at a family realising the last boundary
whose state is the final state of the run and whose monomial ideal is the last marked transform. -/
theorem realizeAux_spec (L : List (Finset (Finset ℕ))) :
    ∀ {N : AnalyticManifold.{u} 𝕜 E} (Φ : PieceFamily N) {F : HypersurfaceFamily N}
      {e : Fin Φ.nextLabel ↪o F.ι} (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e) (hV : Φ.IsValid n m)
      {st' : MonomialState} (_hrun : MonomialState.IsRun (Φ.toState n m hV) L st')
      (h : SmoothCenters ψ₀ Φ m L),
      (realizeAux ψ₀ Φ m L h).NoEmptyCenters ∧
      (realizeAux ψ₀ Φ m L h).toSuccession.IsOfOrderGe (Φ.monomialIdeal hF hΦ) m F.idealSheaf ∧
      ∃ (Φ' : PieceFamily ((realizeAux ψ₀ Φ m L h).toSuccession.stage (Fin.last _)))
        (F' : HypersurfaceFamily ((realizeAux ψ₀ Φ m L h).toSuccession.stage (Fin.last _)))
        (e' : Fin Φ'.nextLabel ↪o F'.ι) (hF' : F'.IsSnc ψ₀) (hΦ' : Φ'.Realizes F' e')
        (hV' : Φ'.IsValid n m),
        Φ'.toState n m hV' = st' ∧
        (realizeAux ψ₀ Φ m L h).toSuccession.markedTransformSeq (Φ.monomialIdeal hF hΦ) m
            (Fin.last _) = Φ'.monomialIdeal hF' hΦ' := by
  induction L with
  | nil =>
    intro N Φ F e hF hΦ hV st' hrun h
    cases hrun
    rw [realizeAux_nil, BlowUpSequence.toSuccession_nil]
    exact ⟨BlowUpSequence.noEmptyCenters_nil, FiniteSuccession.isOfOrderGe_nil _ _ _,
      Φ, F, e, hF, hΦ, hV, rfl, FiniteSuccession.markedTransformSeq_zero _ _ _⟩
  | cons S L ih =>
    intro N Φ F e hF hΦ hV st' hrun h
    cases hrun with
    | cons r _ _ hne hL =>
      -- the centre is Kollár's choice at level `r`: a centre of the state with sums `≥ m`
      have hS : (Φ.toState n m hV).IsCenter ((Φ.toState n m hV).choice r) :=
        MonomialState.isCenter_choice _ r
      have hge : ∀ P ∈ (Φ.toState n m hV).choice r, m ≤ Φ.total P := fun P hP =>
        ((Φ.toState n m hV).mem_choice.mp hP).2.1
      have hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf ((Φ.toState n m hV).choice r))
        (faceCard ((Φ.toState n m hV).choice r)) := h.head
      have hsnc := hΦ.hasSncWith_centerOf hF hS
      have hF' := Φ.isSnc_totalTransform_centerOf hF hΦ hS hZ
      have hΦ' := hΦ.realizes_blowUpPieces hS hZ
      have hV' := hΦ.valid_blowUpPieces hF hS hZ
      have hst : (Φ.blowUpPieces _ m hZ).toState n m hV' =
          (Φ.toState n m hV).blowUp ((Φ.toState n m hV).choice r) :=
        hΦ.toState_blowUpPieces hF hS hZ hV'
      rw [← hst] at hL
      obtain ⟨hne', hord', Φ'', F'', e'', hF'', hΦ'', hV'', hst'', hlast⟩ :=
        ih (Φ.blowUpPieces _ m hZ) hF' hΦ' hV' hL h.tail
      have hbt := hΦ.birationalTransform_monomialIdeal hF hS hZ hge
      have hred : IdealSheaf.reducedTransform (blowUpπ ψ₀ hZ) (F.idealSheaf (𝕜 := 𝕜) (E := E))
          hZ.idealSheaf = (F.totalTransform (blowUpπ ψ₀ hZ) (Φ.centerOf _)).idealSheaf :=
        reducedTransform_eq_idealSheaf_totalTransform hZ (isBlowUp_blowUpπ ψ₀ hZ) hF hsnc
      rw [realizeAux_cons, BlowUpSequence.toSuccession_cons]
      refine ⟨?_, ?_, Φ'', F'', e'', hF'', hΦ'', hV'', hst'', ?_⟩
      · -- no empty centre: the locus of a nonempty centre is nonempty
        rw [BlowUpSequence.noEmptyCenters_cons_iff]
        exact ⟨(Φ.centerOf_nonempty hS hne).ne_empty, hne'⟩
      · -- order `≥ m`: (3′) by the snc of the locus, (4′) by the order along it, the rest by the
        -- transition's monomial ideal
        rw [FiniteSuccession.isOfOrderGe_cons_iff, FiniteSuccession.cons_markedTransformSeq_one,
          hbt, hred]
        exact ⟨⟨HasSncWith.hasOnlyNormalCrossingsWith_idealSheaf hF hZ hsnc,
          fun a ha => hΦ.le_ordAlongIdeal_monomialIdeal_centerOf hF hS hZ hge ha⟩, hord'⟩
      · -- the last marked transform
        rw [FiniteSuccession.cons_markedTransformSeq_last, hbt]
        exact hlast

/-- The run of the combinatorial procedure from a realising family has smooth loci. -/
theorem smoothCenters_step3 {F : HypersurfaceFamily N} {e : Fin Φ.nextLabel ↪o F.ι}
    (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e) (hV : Φ.IsValid n m) :
    SmoothCenters ψ₀ Φ m (MonomialState.step3 (Φ.toState n m hV)).2 := by
  suffices key : ∀ (L : List (Finset (Finset ℕ))) {N : AnalyticManifold.{u} 𝕜 E}
      (Φ : PieceFamily N) {F : HypersurfaceFamily N} {e : Fin Φ.nextLabel ↪o F.ι}
      (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e) (hV : Φ.IsValid n m) {st' : MonomialState},
      MonomialState.IsRun (Φ.toState n m hV) L st' → SmoothCenters ψ₀ Φ m L from
    key _ Φ hF hΦ hV (MonomialState.step3_isRun _)
  intro L
  induction L with
  | nil => intro _ _ _ _ _ _ _ _ _; exact smoothCenters_nil
  | cons S L ih =>
    intro N Φ F e hF hΦ hV st' hrun
    cases hrun with
    | cons r _ _ _ hL =>
      have hS : (Φ.toState n m hV).IsCenter ((Φ.toState n m hV).choice r) :=
        MonomialState.isCenter_choice _ r
      have hZ := hΦ.isClosedSubmanifold_centerOf hF hS
      have hV' := hΦ.valid_blowUpPieces hF hS hZ
      have hst := hΦ.toState_blowUpPieces hF hS hZ hV'
      rw [← hst] at hL
      exact smoothCenters_cons_iff.mpr ⟨hZ, ih (Φ.blowUpPieces _ m hZ)
        (Φ.isSnc_totalTransform_centerOf hF hΦ hS hZ) (hΦ.realizes_blowUpPieces hS hZ) hV' hL⟩

variable {F : HypersurfaceFamily N} {e : Fin Φ.nextLabel ↪o F.ι}

variable (Φ) in
/-- The realisation of Kollár's monomial procedure [Kol07, 111, Step 3] on the manifold: the run of
`Hironaka.Monomial.MonomialState.step3` from the family's state, realised centre by centre. -/
noncomputable def realize (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e) (hV : Φ.IsValid n m) :
    BlowUpSequence ψ₀ N :=
  realizeAux ψ₀ Φ m _ (Φ.smoothCenters_step3 hF hΦ hV)

/-- The postconditions of the realisation, read off the run of the combinatorial procedure. -/
theorem realize_spec (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e) (hV : Φ.IsValid n m) :
    (Φ.realize hF hΦ hV).NoEmptyCenters ∧
    (Φ.realize hF hΦ hV).toSuccession.IsOfOrderGe (Φ.monomialIdeal hF hΦ) m F.idealSheaf ∧
    ∃ (Φ' : PieceFamily ((Φ.realize hF hΦ hV).toSuccession.stage (Fin.last _)))
      (F' : HypersurfaceFamily ((Φ.realize hF hΦ hV).toSuccession.stage (Fin.last _)))
      (e' : Fin Φ'.nextLabel ↪o F'.ι) (hF' : F'.IsSnc ψ₀) (hΦ' : Φ'.Realizes F' e')
      (hV' : Φ'.IsValid n m),
      Φ'.toState n m hV' = (MonomialState.step3 (Φ.toState n m hV)).1 ∧
      (Φ.realize hF hΦ hV).toSuccession.markedTransformSeq (Φ.monomialIdeal hF hΦ) m
          (Fin.last _) = Φ'.monomialIdeal hF' hΦ' :=
  realizeAux_spec _ Φ hF hΦ hV (MonomialState.step3_isRun _) (Φ.smoothCenters_step3 hF hΦ hV)

/-- No centre of the realisation is empty ([Kol07, 32]). -/
theorem realize_noEmptyCenters (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e) (hV : Φ.IsValid n m) :
    (Φ.realize hF hΦ hV).NoEmptyCenters :=
  (Φ.realize_spec hF hΦ hV).1

/-- The realisation is a smooth blow-up sequence of order `≥ m` for the monomial ideal with the
family's boundary ([Kol07, Definition 66 (2′)–(4′)]). -/
theorem realize_isOfOrderGe (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e) (hV : Φ.IsValid n m) :
    (Φ.realize hF hΦ hV).toSuccession.IsOfOrderGe (Φ.monomialIdeal hF hΦ) m F.idealSheaf :=
  (Φ.realize_spec hF hΦ hV).2.1

/-- At every point of the last stage the marked transform of the monomial ideal has order `< m`: its
order is the exponent sum of the face through the point in the final family, whose state is the
final state of the combinatorial run, all of whose faces have exponent sums `< m`
(`Hironaka.Monomial.MonomialState.step3_maxOrd_lt`; "at the end of Step 3.n we are done",
[Kol07, 111, Step 3]). -/
theorem realize_ord_lt (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e) (hV : Φ.IsValid n m)
    (x : (Φ.realize hF hΦ hV).toSuccession.stage (Fin.last _)) :
    ((Φ.realize hF hΦ hV).toSuccession.markedTransformSeq (Φ.monomialIdeal hF hΦ) m
        (Fin.last _)).ord x < (m : ℕ∞) := by
  obtain ⟨-, -, Φ', F', e', hF', hΦ', hV', hst', hlast⟩ := Φ.realize_spec hF hΦ hV
  rw [hlast]
  refine (Φ'.ord_monomialIdeal hF' hΦ' x).trans_lt ?_
  rcases (Φ'.faceAt x).eq_empty_or_nonempty with hT | hT
  · -- no piece through `x`: the order is `0 < m`
    have hm : 1 ≤ m := hV.1
    rw [hT]
    simp only [total, Finset.sum_empty, Nat.cast_zero]
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  · -- the face through `x` is a face of the final state, of sum `< m`
    have hlt : (Φ'.toState n m hV').total (Φ'.faceAt x) < m := by
      have h1 := MonomialState.step3_maxOrd_lt (Φ.toState n m hV) (T := Φ'.faceAt x)
      rw [← hst'] at h1
      exact h1 (Φ'.faceAt_mem_nerve hT)
    exact ENat.natCast_lt_natCast.mpr hlt

end PieceFamily

end Hironaka.Manifold.BMO
