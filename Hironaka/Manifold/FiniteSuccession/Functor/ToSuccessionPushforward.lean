/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Pushforward
public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmpty
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.Restrict.CongrChart
import Hironaka.Manifold.Submanifold.CodimUnique
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The push-forward of a list of centres is the push-forward of its succession

The push-forward of a blow-up sequence of a closed submanifold `S ⊆ M` to `M`
[Kol07, Definition 30, 30.3] exists in two forms: `FiniteSuccession.pushforward` on finite
successions, recursing on the stage index from the start `(M, S, e_0 = id)`, and
`BlowUpSequence.pushforward` on lists of centres, recursing on the list from any `PushforwardStage`.
The commutation of the order-reduction functor with closed embeddings ([Kol07, 34.3];
[Kol07, Theorem 103, (3)]) is stated on the former, the push-forward being the correspondence of
[Kol07, Corollary 85], while a blow-up sequence functor's value is a list. This file
identifies the two:

* `FiniteSuccession.ext_of`: two successions with equal lengths and stages and heterogeneously
  equal centres and maps are equal;
* `PushforwardStage.pushforwardOfStage P T`: the succession recursion from an arbitrary start
  stage `P` (`FiniteSuccession.pushforward_eq_pushforwardOfStage` is the identification at the
  canonical start), and the **peeling lemma** `pushforwardOfStage_cons`: on `cons hZ R` with a
  nonempty centre `Z`, the push-forward starts with `(j_0)_* Z` and continues from the next
  stage; the chosen codimension of the first blow-up of the succession, a classical choice from
  `isMonoidal`, equals the codimension `c` of `hZ` by `IsClosedSubmanifold.codim_eq_of_nonempty`;
* **`BlowUpSequence.toSuccession_pushforward`**: for a list `L` with no empty centre (the output
  convention of every blow-up sequence functor, [Kol07, 32]),
  `(L.pushforward hS).toSuccession = L.toSuccession.pushforward hS`. The hypothesis is needed:
  for an empty centre every codimension is legitimate (`isClosedSubmanifold_empty'`), the chosen
  codimension of the succession is free, and the two push-forwards may blow up `M` along "the
  empty set of codimension `c'`" for different `c'`.

The identification is used where a functor's value, a list, is compared with the push-forward of
a succession, in the descent of the order-reduction functors to a hypersurface of maximal
contact.
-/

@[expose] public section

noncomputable section

open Set AnalyticManifold Manifold
open scoped Manifold ContDiff

universe u v w

namespace Manifold

/-- Heterogeneous equality of dependent functions over propositionally equal families, from the
pointwise heterogeneous equalities. -/
theorem heq_pi_of_forall {α : Sort w} {β₁ β₂ : α → Sort v} (e : β₁ = β₂) (f₁ : ∀ a, β₁ a)
    (f₂ : ∀ a, β₂ a) (h : ∀ a, HEq (f₁ a) (f₂ a)) : HEq f₁ f₂ := by
  subst e
  exact heq_of_eq (funext fun a => eq_of_heq (h a))

end Manifold

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Extensionality of finite successions**: two successions of the same
length whose stages agree and whose centres and blow-downs are heterogeneously equal are equal
(`isMonoidal` is a proof). -/
theorem ext_of {M : AnalyticManifold.{u} 𝕜 E} {S T : FiniteSuccession M} (hl : S.length = T.length)
    (hlater : ∀ i, S.later i = T.later (Fin.cast hl i)) (hc : HEq S.center T.center)
    (hm : HEq S.map T.map) : S = T := by
  obtain ⟨l₁, later₁, c₁, m₁, mono₁⟩ := S
  obtain ⟨l₂, later₂, c₂, m₂, mono₂⟩ := T
  dsimp only at hl hlater hc hm
  subst hl
  obtain rfl : later₁ = later₂ := funext fun i => hlater i
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hm
  rfl

variable {n s : ℕ} {T₀ : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)} (T : FiniteSuccession T₀)

/-- The centre `Z_i` of a succession on a manifold modelled on `𝕜^{n-s}`, as a closed submanifold
for the identity chart (`pushforwardCenterSub` from any base). -/
theorem centerSub (i : ℕ) (hi : i < T.length) :
    IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      (T.center ⟨i, hi⟩).support (T.codim ⟨i, hi⟩) :=
  (T.isClosedSubmanifold_center ⟨i, hi⟩).congr_chart _

/-- The blow-down `T_{i+1} → T_i` as a blowing-up for the identity chart (`pushforwardIsBlowUp`
from any base). -/
theorem isBlowUpSub (i : ℕ) (hi : i < T.length) :
    IsBlowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) (T.center ⟨i, hi⟩).support
      (T.codim ⟨i, hi⟩) (T.map ⟨i, hi⟩) :=
  (T.isBlowUp_map ⟨i, hi⟩).congr_chart _

end AnalyticManifold.FiniteSuccession

namespace Manifold.PushforwardStage

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n s : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {T₀ : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)}

/-! ### The recursion from an arbitrary start stage -/

section General

variable (P : PushforwardStage ψ s T₀) (T : FiniteSuccession T₀)

/-- The stages of the push-forward of `T` started at `P` (`pushforwardAux` with `P` in
place of `(M, S, id)`). -/
def stageAux : ∀ (i : ℕ) (hi : i < T.length + 1),
    PushforwardStage ψ s (finStages T₀ T.later ⟨i, hi⟩)
  | 0, _ => P
  | i + 1, hi =>
    (stageAux i (Nat.lt_of_succ_lt hi)).blowUpStep (T.centerSub i (Nat.lt_of_succ_lt_succ hi))
      (T.isBlowUpSub i (Nat.lt_of_succ_lt_succ hi))

/-- The later stages of the push-forward started at `P`. -/
def laterAux (i : Fin T.length) : AnalyticManifold.{u} 𝕜 E :=
  (stageAux P T (i.1 + 1) (Nat.succ_lt_succ i.2)).space

/-- The centre of the push-forward at step `i`, as a closed submanifold. -/
theorem centerOfSub (i : ℕ) (hi : i < T.length) :
    IsClosedSubmanifold ψ
      ((stageAux P T i (Nat.lt_succ_of_lt hi)).isClosedSubmanifold.imageVal
        ((stageAux P T i (Nat.lt_succ_of_lt hi)).iso '' (T.center ⟨i, hi⟩).support))
      (T.codim ⟨i, hi⟩ + s) :=
  (stageAux P T i (Nat.lt_succ_of_lt hi)).isClosedSubmanifold_imageVal_image (T.centerSub i hi)

/-- The centre of the push-forward at step `i`: the ideal sheaf of `Z_i^X`. -/
def centerOf (i : ℕ) (hi : i < T.length) :
    AnalyticManifold.IdealSheaf (stageAux P T i (Nat.lt_succ_of_lt hi)).space :=
  (centerOfSub P T i hi).idealSheaf

/-- The blow-down of the push-forward at step `i`. -/
def mapOf (i : ℕ) (hi : i < T.length) :
    AnalyticMap (stageAux P T (i + 1) (Nat.succ_lt_succ hi)).space
      (stageAux P T i (Nat.lt_succ_of_lt hi)).space :=
  blowUpπ ψ (centerOfSub P T i hi)

/-- The centres, typed on `finStages`. -/
def centerAux : ∀ (i : ℕ) (hi : i < T.length),
    AnalyticManifold.IdealSheaf (finStages P.space (laterAux P T) ⟨i, Nat.lt_succ_of_lt hi⟩)
  | 0, hi => centerOf P T 0 hi
  | i + 1, hi => centerOf P T (i + 1) hi

/-- The blow-downs, typed on `finStages`. -/
def mapAux : ∀ (i : ℕ) (hi : i < T.length),
    AnalyticMap (finStages P.space (laterAux P T) ⟨i + 1, Nat.succ_lt_succ hi⟩)
      (finStages P.space (laterAux P T) ⟨i, Nat.lt_succ_of_lt hi⟩)
  | 0, hi => mapOf P T 0 hi
  | i + 1, hi => mapOf P T (i + 1) hi

/-- Each blow-down is the monoidal transformation with centre the ideal sheaf of `Z_i^X`. -/
theorem isMonoidalAux : ∀ (i : ℕ) (hi : i < T.length),
    (mapAux P T i hi).IsMonoidalTransformation (centerAux P T i hi)
  | 0, hi => isMonoidalTransformation_blowUpπ ψ (centerOfSub P T 0 hi)
  | i + 1, hi => isMonoidalTransformation_blowUpπ ψ (centerOfSub P T (i + 1) hi)

/-- [Kol07, Definition 30, 30.3] from an arbitrary start stage `P`: the push-forward of the
succession `T` on `T₀` to `P.space` (`FiniteSuccession.pushforward` is the instance at
the canonical start, `FiniteSuccession.pushforward_eq_pushforwardOfStage`). -/
def pushforwardOfStage : FiniteSuccession P.space where
  length := T.length
  later := laterAux P T
  center i := centerAux P T i.1 i.2
  map i := mapAux P T i.1 i.2
  isMonoidal i := isMonoidalAux P T i.1 i.2

end General

/-! ### Congruences -/

/-- `blowUpStep` depends on the centre and its codimension only up to propositional equality. -/
theorem blowUpStep_congr (P : PushforwardStage ψ s T₀) {Z₁ Z₂ : Set T₀} {c₁ c₂ : ℕ} (eZ : Z₁ = Z₂)
    (ec : c₁ = c₂) (h₁ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z₁ c₁)
    (h₂ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z₂ c₂)
    {T' : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)} {π : AnalyticMap T' T₀}
    (hπ₁ : IsBlowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z₁ c₁ π)
    (hπ₂ : IsBlowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z₂ c₂ π) :
    P.blowUpStep h₁ hπ₁ = P.blowUpStep h₂ hπ₂ := by
  subst eZ; subst ec; rfl

/-- The pushed-forward centre depends on the centre and its codimension only up to propositional
equality. -/
theorem idealSheaf_imageVal_congr (P : PushforwardStage ψ s T₀) {Z₁ Z₂ : Set T₀} {c₁ c₂ : ℕ}
    (eZ : Z₁ = Z₂) (ec : c₁ = c₂)
    (h₁ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z₁ c₁)
    (h₂ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z₂ c₂) :
    (P.isClosedSubmanifold_imageVal_image h₁).idealSheaf =
      (P.isClosedSubmanifold_imageVal_image h₂).idealSheaf := by
  subst eZ; subst ec; rfl

/-- The blow-down along the pushed-forward centre, up to propositional equality of the centre and
its codimension. -/
theorem heq_blowUpπ_imageVal_congr (P : PushforwardStage ψ s T₀) {Z₁ Z₂ : Set T₀} {c₁ c₂ : ℕ}
    (eZ : Z₁ = Z₂) (ec : c₁ = c₂)
    (h₁ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z₁ c₁)
    (h₂ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z₂ c₂) :
    HEq (blowUpπ ψ (P.isClosedSubmanifold_imageVal_image h₁))
      (blowUpπ ψ (P.isClosedSubmanifold_imageVal_image h₂)) := by
  subst eZ; subst ec; rfl

/-- The pushed-forward centre, along an equality of stages. -/
theorem heq_idealSheaf_imageVal_of_eq {X : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)}
    {P₁ P₂ : PushforwardStage ψ s X} (e : P₁ = P₂) {Z : Set X} {c : ℕ}
    (hZ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c) :
    HEq (P₁.isClosedSubmanifold_imageVal_image hZ).idealSheaf
      (P₂.isClosedSubmanifold_imageVal_image hZ).idealSheaf := by
  subst e; rfl

/-- The blow-down along the pushed-forward centre, along an equality of stages. -/
theorem heq_blowUpπ_imageVal_of_eq {X : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)}
    {P₁ P₂ : PushforwardStage ψ s X} (e : P₁ = P₂) {Z : Set X} {c : ℕ}
    (hZ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c) :
    HEq (blowUpπ ψ (P₁.isClosedSubmanifold_imageVal_image hZ))
      (blowUpπ ψ (P₂.isClosedSubmanifold_imageVal_image hZ)) := by
  subst e; rfl

/-! ### The push-forward of `nil` and of `cons` -/

/-- The push-forward of the empty succession is the empty succession on `P.space`. -/
theorem pushforwardOfStage_nil (P : PushforwardStage ψ s T₀) :
    pushforwardOfStage P (FiniteSuccession.nil T₀) = FiniteSuccession.nil P.space :=
  FiniteSuccession.ext_of rfl (fun i => i.elim0)
    (heq_pi_of_forall (funext fun i => i.elim0) _ _ fun i => i.elim0)
    (heq_pi_of_forall (funext fun i => i.elim0) _ _ fun i => i.elim0)

variable {Z : Set T₀} {c : ℕ}
  (hZ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c)
  (R : FiniteSuccession (blowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) hZ))

/-- The support of the first centre of `cons hZ R` is `Z`. -/
theorem support_center_cons_zero :
    ((FiniteSuccession.cons _ hZ R).center (0 : Fin (R.length + 1))).support = Z := by
  rw [FiniteSuccession.cons_center_zero]
  exact hZ.cosupport_idealSheaf

/-- [Kol07, 32] removing the obstruction: for a nonempty first centre, the succession's chosen
codimension of the first blow-up of `cons hZ R` is the codimension `c` of `hZ`
(`IsClosedSubmanifold.codim_eq_of_nonempty`, across the chosen chart and the identity chart). -/
theorem codim_cons_zero (hne : Z.Nonempty) :
    (FiniteSuccession.cons _ hZ R).codim (0 : Fin (R.length + 1)) = c := by
  have hZ' : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      ((FiniteSuccession.cons _ hZ R).center (0 : Fin (R.length + 1))).support c := by
    rw [support_center_cons_zero]; exact hZ
  have hne' :
      ((FiniteSuccession.cons _ hZ R).center (0 : Fin (R.length + 1))).support.Nonempty := by
    rw [support_center_cons_zero]; exact hne
  exact ((FiniteSuccession.cons _ hZ R).isClosedSubmanifold_center
    (0 : Fin (R.length + 1))).codim_eq_of_nonempty hZ' hne'

/-- The stages of the push-forward of `cons hZ R` after the first are those of the push-forward
of `R` started at the first blow-up step (the peeling of the recursion; the first step's data are
identified through `codim_cons_zero`). -/
theorem stageAux_cons_succ (P : PushforwardStage ψ s T₀) (hne : Z.Nonempty) :
    ∀ (i : ℕ) (hi : i + 1 < (FiniteSuccession.cons _ hZ R).length + 1),
      stageAux P (FiniteSuccession.cons _ hZ R) (i + 1) hi =
        stageAux (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)) R i (Nat.lt_of_succ_lt_succ hi)
  | 0, hi => by
    change P.blowUpStep _ _ = P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)
    exact blowUpStep_congr P (support_center_cons_zero hZ R) (codim_cons_zero hZ R hne) _ _ _ _
  | i + 1, hi => by
    change (stageAux P (FiniteSuccession.cons _ hZ R) (i + 1) _).blowUpStep _ _ =
      (stageAux (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)) R i _).blowUpStep _ _
    rw [stageAux_cons_succ P hne i]
    rfl

/-- The blow-downs of the push-forward of `cons hZ R` after the first are those of the push-forward
of `R` started at the first blow-up step (typed on the stages, `stageAux_cons_succ`). -/
theorem heq_mapOf_cons_succ (P : PushforwardStage ψ s T₀) (hne : Z.Nonempty) (i : ℕ)
    (hi : i + 1 < (FiniteSuccession.cons _ hZ R).length) :
    HEq (mapOf P (FiniteSuccession.cons _ hZ R) (i + 1) hi)
      (mapOf (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)) R i (Nat.lt_of_succ_lt_succ hi)) :=
  heq_blowUpπ_imageVal_of_eq (stageAux_cons_succ hZ R P hne i (Nat.lt_succ_of_lt hi))
    ((FiniteSuccession.cons _ hZ R).centerSub (i + 1) hi)

/-- **The peeling lemma**: for a nonempty first centre `Z`, the push-forward of `cons hZ R` started
at `P` is `cons` of the pushed-forward centre `(j_0)_* Z` and the push-forward of `R` started at the
first blow-up step. -/
theorem pushforwardOfStage_cons (P : PushforwardStage ψ s T₀) (hne : Z.Nonempty) :
    pushforwardOfStage P (FiniteSuccession.cons _ hZ R) =
      FiniteSuccession.cons ψ (P.isClosedSubmanifold_imageVal_image hZ)
        (pushforwardOfStage (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)) R) := by
  have hlat : laterAux P (FiniteSuccession.cons _ hZ R) =
      finStages (blowUp ψ (P.isClosedSubmanifold_imageVal_image hZ))
        (laterAux (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)) R) := by
    funext i
    obtain ⟨i, hi⟩ := i
    cases i with
    | zero => exact congrArg PushforwardStage.space (stageAux_cons_succ hZ R P hne 0 _)
    | succ i => exact congrArg PushforwardStage.space (stageAux_cons_succ hZ R P hne (i + 1) _)
  have hlat' : (pushforwardOfStage P (FiniteSuccession.cons _ hZ R)).later =
      (FiniteSuccession.cons ψ (P.isClosedSubmanifold_imageVal_image hZ)
        (pushforwardOfStage (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)) R)).later := hlat
  refine FiniteSuccession.ext_of rfl (fun i => congrFun hlat i) ?_ ?_
  · refine heq_pi_of_forall (by rw [hlat']; rfl) _ _ fun i => ?_
    obtain ⟨i, hi⟩ := i
    cases i with
    | zero =>
      exact heq_of_eq (idealSheaf_imageVal_congr P (support_center_cons_zero hZ R)
        (codim_cons_zero hZ R hne) ((FiniteSuccession.cons _ hZ R).centerSub 0 hi) hZ)
    | succ i =>
      cases i with
      | zero =>
        exact heq_idealSheaf_imageVal_of_eq (stageAux_cons_succ hZ R P hne 0 _)
          ((FiniteSuccession.cons _ hZ R).centerSub (0 + 1) hi)
      | succ j =>
        exact heq_idealSheaf_imageVal_of_eq (stageAux_cons_succ hZ R P hne (j + 1) _)
          ((FiniteSuccession.cons _ hZ R).centerSub (j + 1 + 1) hi)
  · refine heq_pi_of_forall (by rw [hlat']; rfl) _ _ fun i => ?_
    obtain ⟨i, hi⟩ := i
    cases i with
    | zero =>
      exact heq_blowUpπ_imageVal_congr P (support_center_cons_zero hZ R) (codim_cons_zero hZ R hne)
        ((FiniteSuccession.cons _ hZ R).centerSub 0 hi) hZ
    | succ i =>
      cases i with
      | zero => exact heq_mapOf_cons_succ hZ R P hne 0 hi
      | succ j => exact heq_mapOf_cons_succ hZ R P hne (j + 1) hi

end Manifold.PushforwardStage

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {S : Set M} {s : ℕ}
  (hS : IsClosedSubmanifold ψ S s) (T : FiniteSuccession hS.toAnalyticManifold)

/-- The stages are the general recursion's at the canonical start `(M, S, id)`. -/
theorem pushforwardAux_eq_stageAux : ∀ (i : ℕ) (hi : i < T.length + 1),
    T.pushforwardAux hS i hi =
      PushforwardStage.stageAux
        (⟨M, S, hS, Diffeomorph.refl _ _ _⟩ : PushforwardStage ψ s hS.toAnalyticManifold) T i hi
  | 0, _ => rfl
  | i + 1, hi => by
    change (T.pushforwardAux hS i _).blowUpStep _ _ =
      (PushforwardStage.stageAux _ T i _).blowUpStep _ _
    rw [pushforwardAux_eq_stageAux i]

/-- The push-forward is the general recursion's at the canonical start `(M, S, id)`. -/
theorem pushforward_eq_pushforwardOfStage :
    T.pushforward hS =
      PushforwardStage.pushforwardOfStage
        (⟨M, S, hS, Diffeomorph.refl _ _ _⟩ : PushforwardStage ψ s hS.toAnalyticManifold) T := by
  have hst := pushforwardAux_eq_stageAux hS T
  have hlat : T.pushforwardLater hS = PushforwardStage.laterAux _ T :=
    funext fun i => congrArg PushforwardStage.space (hst (i.1 + 1) _)
  have hlat' : (T.pushforward hS).later =
      (PushforwardStage.pushforwardOfStage
        (⟨M, S, hS, Diffeomorph.refl _ _ _⟩ : PushforwardStage ψ s hS.toAnalyticManifold)
        T).later :=
    hlat
  refine ext_of rfl (fun i => congrFun hlat i) ?_ ?_
  · refine heq_pi_of_forall (by rw [hlat']; rfl) _ _ fun i => ?_
    obtain ⟨i, hi⟩ := i
    cases i with
    | zero => exact HEq.rfl
    | succ i =>
      exact PushforwardStage.heq_idealSheaf_imageVal_of_eq (hst (i + 1) _) (T.centerSub (i + 1) hi)
  · refine heq_pi_of_forall (by rw [hlat']; rfl) _ _ fun i => ?_
    obtain ⟨i, hi⟩ := i
    cases i with
    | zero => exact HEq.rfl
    | succ i =>
      exact PushforwardStage.heq_blowUpπ_imageVal_of_eq (hst (i + 1) _) (T.centerSub (i + 1) hi)

end AnalyticManifold.FiniteSuccession

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n s : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The list push-forward from any start stage, as a succession, is the general succession
push-forward of the list's succession — for a list with no empty centre. -/
theorem toSuccession_pushforwardAux :
    ∀ {T₀ : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)} (P : PushforwardStage ψ s T₀)
      (L : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) T₀), L.NoEmptyCenters →
      (pushforwardAux P L).toSuccession = PushforwardStage.pushforwardOfStage P L.toSuccession
  | _, P, nil _, _ => (PushforwardStage.pushforwardOfStage_nil P).symm
  | _, P, cons hZ rest, hL => by
    obtain ⟨hne, hrest⟩ := (noEmptyCenters_cons_iff hZ rest).mp hL
    change FiniteSuccession.cons ψ (P.isClosedSubmanifold_imageVal_image hZ)
        (pushforwardAux (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)) rest).toSuccession =
      PushforwardStage.pushforwardOfStage P (FiniteSuccession.cons _ hZ rest.toSuccession)
    rw [toSuccession_pushforwardAux _ rest hrest,
      PushforwardStage.pushforwardOfStage_cons hZ rest.toSuccession P
        (Set.nonempty_iff_ne_empty.mpr hne)]

/-- **The push-forward of lists agrees with the push-forward of successions**:
for a closed submanifold `hS : IsClosedSubmanifold ψ S s` and a list of centres `L` on the bundled
`S` with no empty centre ([Kol07, 32]), the succession of the list push-forward is
the push-forward of the list's succession. The hypothesis is load-bearing: at an empty
centre the chosen codimension is free (`isClosedSubmanifold_empty'`), and the two
push-forwards need not agree. -/
theorem toSuccession_pushforward {M : AnalyticManifold.{u} 𝕜 E} {S : Set M}
    (hS : IsClosedSubmanifold ψ S s)
    (L : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) hS.toAnalyticManifold)
    (hL : L.NoEmptyCenters) : (L.pushforward hS).toSuccession = L.toSuccession.pushforward hS := by
  rw [FiniteSuccession.pushforward_eq_pushforwardOfStage hS L.toSuccession]
  exact toSuccession_pushforwardAux _ L hL

end AnalyticManifold.BlowUpSequence

end
