/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bCenter
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.MarkedWeak
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Dictionary
import Hironaka.Manifold.Snc.TotalTransform
import Hironaka.Resolution.Analytic.MaximalContact.MarkedOneLemmas
import Hironaka.Resolution.Analytic.OrderReduction.Induced
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# One step of the monomial phase at the mark `1`

One blow-up of the monomial phase of the modified algorithm [Wlo09, Theorem 7.4.1]: the blow-up of
the centre of `Step2bCenter.lean` (the positive locus of the latest-born active member, Kollár's
`Z_{-1}` at the mark `1`), with the triple carried along it as the sequences of the library carry
it: the ideal by the **marked** transform at the mark `1` (the transform (60.1) of
[Kol07, Definition 60], clause (1′) of [Kol07, Definition 66]; `birationalTransform`, the transform
of `markedTransformSeq`, `cons_markedTransformSeq_one`), the boundary by the total transform
([Kol07, Definition 25], the new member last). This is the controlled transform
`(M(𝓘)/𝓘(D)) · N(𝓘)` of the remarks after [Wlo09, Theorem 2.0.3], the blow-down being an
isomorphism ([Kol07, Definition–Lemma 110]); the identity of the two, the exponents after the step
and the termination of the phase are proved in `Step2bExponent.lean` and `Step2bMeasure.lean`.
Here the step is made a triple of the class of `BMO_{n,1}`:

* the marked transform of an ideal sheaf nonzero everywhere, along a centre of order `≥ m`, is
  nonzero everywhere (`isNonzeroEverywhere_birationalTransform`, the one-step form of
  `isNonzeroEverywhere_markedTransformSeq`);
* the total transform of the boundary along a centre with simple normal crossings has simple normal
  crossings (`isSnc_totalTransform` at `hasSncWith_Zminus1`);
* finitely many members stay nonempty (`finite_nonempty_totalTransform`).

The two bridges to the recursions of `AnalyticManifold.FiniteSuccession` are proved on the
constructor form: a list starting with the blow-up of the step is of order `≥ 1` for `(M, 𝓘, E)`
iff its tail is of order `≥ 1` for the triple after the step (`isOfOrderGe_cons_step_iff`, from
`isOfOrderGe_cons_iff` with the two head clauses of `Step2bCenter.lean`,
`cons_markedTransformSeq_one` and `reducedTransform_eq_idealSheaf_totalTransform`), and it has no
empty centre iff its tail has none (`noEmptyCenters_cons_step_iff`, the centre being nonempty).
-/

@[expose] public section

noncomputable section

open Set Topology AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### A general tool: the marked transform of a nonzero ideal sheaf is nonzero -/

/-- Along a blow-up whose centre has order `≥ m` for `(J, m)`, the marked transform of a `J` nonzero
everywhere is nonzero everywhere (the one-step form of `isNonzeroEverywhere_markedTransformSeq`):
the stalk of the marked transform is the colon of the stalk of the total transform by a power of
the exceptional ideal, which contains the stalk of the total transform, the image of the nonzero
stalk of `J` under the injective germ map of the blow-up ((60.1) of [Kol07, Definition 60]). -/
theorem isNonzeroEverywhere_birationalTransform {M N : AnalyticManifold.{u} 𝕜 E} {Y : Set M}
    {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c) {π : N → M} (h : IsBlowUp ψ₀ Y c π)
    (J : MarkedIdealSheaf (structureSheaf 𝕜 E M))
    (hm : ∀ a ∈ Y, (J.m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J.I a)
    (hJ : J.I.IsNonzeroEverywhere) :
    (MarkedIdealSheaf.birationalTransform hY h J).I.IsNonzeroEverywhere := by
  intro a' hbot
  have hdiv := isDivExceptional_birationalTransform hY h J hm
  have hst := hdiv a'
  rw [hbot] at hst
  have hle : (J.I.pullback π h.contMDiff).stalkIdeal a' ≤ ⊥ := by
    rw [hst]
    intro r hr
    exact Submodule.mem_colon.mpr fun p _ => Ideal.mul_mem_right p _ hr
  rw [IdealSheaf.stalkIdeal_pullback, le_bot_iff,
    Ideal.map_eq_bot_iff_of_injective (IsBlowUp.germMap_injective hY h a')] at hle
  exact hJ (π a') hle

namespace BMOmod

open _root_.Manifold

variable [FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
  (hfin : (activeMembers T).Finite) (hne : (activeMembers T).Nonempty)

/-! ### The blowing-up of the Step 2b centre and the transformed triple -/

/-- The closed-submanifold witness of the centre of the step (the head of the step's
`BlowUpSequence.cons`). -/
abbrev stepCenter : IsClosedSubmanifold ψ₀ (step2bCenter T hfin hne) 1 :=
  isClosedSubmanifold_step2bCenter T hfin hne

/-- **The stage after one blow-up of the monomial phase**: the blow-up of the centre (an
isomorphism, `cons_codimOne_exists_diffeomorph`). -/
abbrev stepStage : AnalyticManifold.{u} 𝕜 E := blowUp ψ₀ (stepCenter T hfin hne)

/-- The blow-down of the step. -/
abbrev stepπ : AnalyticMap (stepStage T hfin hne) M := blowUpπ ψ₀ (stepCenter T hfin hne)

/-- **The ideal after the step**: the marked transform `π_*^{-1}(𝓘, 1)` along the blow-up of the
centre ((60.1) of [Kol07, Definition 60] at the mark `1`; `birationalTransform`, the transform of
`markedTransformSeq`, `cons_markedTransformSeq_one`). It is the controlled transform of the remarks
after [Wlo09, Theorem 2.0.3]. -/
def stepIdeal : AnalyticManifold.IdealSheaf (stepStage T hfin hne) :=
  (MarkedIdealSheaf.birationalTransform (stepCenter T hfin hne)
    (isBlowUp_blowUpπ ψ₀ (stepCenter T hfin hne)) ⟨T.I, 1⟩).I

/-- The ideal after the step is nonzero everywhere (the centre has order `≥ 1`,
`one_le_ordAlong_step2bCenter`). -/
theorem isNonzeroEverywhere_stepIdeal : (stepIdeal T hfin hne).IsNonzeroEverywhere :=
  isNonzeroEverywhere_birationalTransform (stepCenter T hfin hne) _ ⟨T.I, 1⟩
    (one_le_ordAlong_step2bCenter T hfin hne) T.isNonzeroEverywhere

/-- **The boundary after the step**: the total transform of `E` [Kol07, Definition 25], the strict
transforms of the members followed by the exceptional divisor `π⁻¹(D) ≅ D` as the last member (the
order of birth). -/
def stepFamily : HypersurfaceFamily (stepStage T hfin hne) :=
  T.F.totalTransform (stepπ T hfin hne) (step2bCenter T hfin hne)

/-- The boundary after the step has simple normal crossings (`isSnc_totalTransform`; the centre has
simple normal crossings with `E`, `hasSncWith_step2bCenter`). -/
theorem isSnc_stepFamily : (stepFamily T hfin hne).IsSnc ψ₀ :=
  HypersurfaceFamily.isSnc_totalTransform (stepCenter T hfin hne) (isBlowUp_blowUpπ ψ₀ _) T.isSnc
    (hasSncWith_step2bCenter T hfin hne)

/-- The step of the monomial phase written at an arbitrary closed-submanifold witness of a set equal
to the centre (the witness of the pulled-back centre differs from that of the pull-back's own
centre). -/
def stepTripleOf {Y : Set M} (hY : IsClosedSubmanifold ψ₀ Y 1)
    (hYeq : Y = step2bCenter T hfin hne) : AnalyticTriple ψ₀ (blowUp ψ₀ hY) where
  I := (MarkedIdealSheaf.birationalTransform hY (isBlowUp_blowUpπ ψ₀ hY) ⟨T.I, 1⟩).I
  isNonzeroEverywhere := by
    subst hYeq
    exact isNonzeroEverywhere_stepIdeal T hfin hne
  F := T.F.totalTransform (blowUpπ ψ₀ hY) Y
  isSnc := by
    subst hYeq
    exact isSnc_stepFamily T hfin hne

/-- Two witnesses of the centre give heterogeneously equal steps. -/
theorem heq_stepTripleOf {Y₁ Y₂ : Set M} (h₁ : IsClosedSubmanifold ψ₀ Y₁ 1)
    (h₂ : IsClosedSubmanifold ψ₀ Y₂ 1) (e₁ : Y₁ = step2bCenter T hfin hne)
    (e₂ : Y₂ = step2bCenter T hfin hne) :
    HEq (stepTripleOf T hfin hne h₁ e₁) (stepTripleOf T hfin hne h₂ e₂) := by
  subst e₁
  subst e₂
  rfl

/-- **The triple after one blow-up of the monomial phase**, `(Bl_D M, π_*^{-1}(𝓘, 1), E_1)`:
`stepTripleOf` at the centre's own witness. -/
def stepTriple : AnalyticTriple ψ₀ (stepStage T hfin hne) :=
  stepTripleOf T hfin hne (stepCenter T hfin hne) rfl

@[simp] theorem stepTriple_I : (stepTriple T hfin hne).I = stepIdeal T hfin hne := rfl

@[simp] theorem stepTriple_F : (stepTriple T hfin hne).F = stepFamily T hfin hne := rfl

/-- The triple after the step lies in the class of `BMO_{n,1}` (finitely many nonempty members,
`finite_nonempty_totalTransform`). -/
theorem bmoClass_stepTriple (hT : AnalyticTriple.BMOClass 1 T) :
    AnalyticTriple.BMOClass 1 (stepTriple T hfin hne) :=
  ⟨le_rfl, finite_nonempty_totalTransform (stepπ T hfin hne) (step2bCenter T hfin hne) T.F hT.2⟩

/-- The triple after the step, at any witness of the centre, lies in the class of `BMO_{n,1}`. -/
theorem bmoClass_stepTripleOf {Y : Set M} (hY : IsClosedSubmanifold ψ₀ Y 1)
    (hYeq : Y = step2bCenter T hfin hne) (hT : AnalyticTriple.BMOClass 1 T) :
    AnalyticTriple.BMOClass 1 (stepTripleOf T hfin hne hY hYeq) := by
  subst hYeq
  exact bmoClass_stepTriple T hfin hne hT

/-! ### The bridges to the recursions of the library, on the constructor form -/

/-- The marked transform at the stage `1` of any list starting with the blow-up of the step is the
ideal after the step (`cons_markedTransformSeq_one`). -/
theorem cons_markedTransformSeq_one_step (rest : BlowUpSequence ψ₀ (stepStage T hfin hne)) :
    (BlowUpSequence.cons (stepCenter T hfin hne) rest).toSuccession.markedTransformSeq T.I 1
      (Fin.succ (0 : Fin (rest.length + 1))) = stepIdeal T hfin hne :=
  FiniteSuccession.cons_markedTransformSeq_one (stepCenter T hfin hne) rest.toSuccession T.I 1

/-- The reduced transform of the boundary ideal along the step is the ideal sheaf of the boundary
after the step (`reducedTransform_eq_idealSheaf_totalTransform`). -/
theorem reducedTransform_step :
    IdealSheaf.reducedTransform (stepπ T hfin hne) (T.F.idealSheaf (𝕜 := 𝕜) (E := E))
        (stepCenter T hfin hne).idealSheaf =
      (stepFamily T hfin hne).idealSheaf (𝕜 := 𝕜) (E := E) :=
  reducedTransform_eq_idealSheaf_totalTransform (stepCenter T hfin hne) (isBlowUp_blowUpπ ψ₀ _)
    T.isSnc (hasSncWith_step2bCenter T hfin hne)

/-- [Kol07, Definition 66] on the constructor form (`isOfOrderGe_cons_iff`): a list starting with
the blow-up of the step is of order `≥ 1` for `(M, 𝓘, E)` iff its tail is of order `≥ 1` for the
triple after the step, the two head clauses holding at the centre
(`hasOnlyNormalCrossingsWith_step2bCenter`, `one_le_ordAlong_step2bCenter`). -/
theorem isOfOrderGe_cons_step_iff (rest : BlowUpSequence ψ₀ (stepStage T hfin hne)) :
    (BlowUpSequence.cons (stepCenter T hfin hne) rest).toSuccession.IsOfOrderGe T.I 1
        (T.F.idealSheaf (𝕜 := 𝕜) (E := E)) ↔
      rest.toSuccession.IsOfOrderGe (stepTriple T hfin hne).I 1
        ((stepTriple T hfin hne).F.idealSheaf (𝕜 := 𝕜) (E := E)) := by
  rw [BlowUpSequence.toSuccession_cons, FiniteSuccession.isOfOrderGe_cons_iff,
    FiniteSuccession.cons_markedTransformSeq_one, reducedTransform_step]
  exact and_iff_right
    ⟨hasOnlyNormalCrossingsWith_step2bCenter T hfin hne, one_le_ordAlong_step2bCenter T hfin hne⟩

/-- [Kol07, 32] on the constructor form: a list starting with the blow-up of the step has no empty
centre iff its tail has none (the centre is nonempty, `step2bCenter_nonempty`). -/
theorem noEmptyCenters_cons_step_iff (rest : BlowUpSequence ψ₀ (stepStage T hfin hne)) :
    (BlowUpSequence.cons (stepCenter T hfin hne) rest).NoEmptyCenters ↔ rest.NoEmptyCenters := by
  rw [BlowUpSequence.noEmptyCenters_cons_iff]
  exact and_iff_right (step2bCenter_nonempty T hfin hne).ne_empty

end BMOmod

end Hironaka.Manifold

end
