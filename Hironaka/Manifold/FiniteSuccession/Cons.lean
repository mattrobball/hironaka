/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Exists
public import Hironaka.Manifold.FiniteSuccession.Defs
import Hironaka.Manifold.BlowUp.Transform.Object
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial
/-!
# Kollár's constructors of analytic blow-up sequences

Kollár's view of a blow-up sequence as its list of centres [Kol07, Definition 29], as constructors
of `AnalyticManifold.FiniteSuccession M`:

* `blowUp ψ hY`, `blowUpπ ψ hY`: the blowing-up of `M` along the closed submanifold `Y`
  (`BlowUpSpace`, the blowing-up of [BM88, Definition 4.1]) as a bundled analytic manifold with
  its blow-down, a blowing-up with centre `Y` (`isBlowUp_blowUpπ`) and a monoidal transformation
  with centre the ideal sheaf `hY.idealSheaf` of `Y` (`isMonoidalTransformation_blowUpπ`);
* `FiniteSuccession.nil M` (the empty sequence) and `FiniteSuccession.cons ψ hY rest`, the
  sequence whose first blow-up is `blowUpπ ψ hY` followed by `rest`; the later stages are
  `finStages (blowUp ψ hY) rest.later`, so that the dependent fields `center`, `map`,
  `isMonoidal` are `Fin.cases` of the head and of the fields of `rest`, definitionally
  (`cons_length`, `cons_center_zero`, `cons_map_zero`, `cons_center_succ`, `cons_map_succ`,
  `cons_stage_zero`, `cons_stage_succ`).

The constructors are the form in which the order-reduction and resolution algorithms build their
sequences.
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜))

/-! ### The blowing-up along a closed submanifold as a bundled analytic manifold -/

section BlowUpBundled

variable {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}

/-- The blowing-up of `M` along the closed submanifold `Y` (`BlowUpSpace`, the blowing-up of
[BM88, Definition 4.1]) as a bundled analytic manifold. -/
def blowUp (hY : IsClosedSubmanifold ψ Y c) : AnalyticManifold.{u} 𝕜 E :=
  ⟨BlowUpSpace ψ hY⟩

/-- The blow-down `π : Bl_Y M → M` (`blowUpMap`) as a bundled analytic map. -/
def blowUpπ (hY : IsClosedSubmanifold ψ Y c) : AnalyticMap (blowUp ψ hY) M :=
  ⟨blowUpMap ψ hY, (isBlowUp_blowUpMap ψ hY).contMDiff⟩

theorem blowUpπ_apply (hY : IsClosedSubmanifold ψ Y c) (p : blowUp ψ hY) :
    blowUpπ ψ hY p = blowUpMap ψ hY p := rfl

/-- The blow-down `blowUpπ ψ hY` is a blowing-up with centre `Y` [BM88, Definition 4.1]. -/
theorem isBlowUp_blowUpπ (hY : IsClosedSubmanifold ψ Y c) : IsBlowUp ψ Y c (blowUpπ ψ hY) :=
  isBlowUp_blowUpMap ψ hY

/-- The blow-down `blowUpπ ψ hY` is a monoidal transformation of `M` with centre the ideal sheaf
`I_Y` of `Y`, in the sense in which the main theorems use the phrase (`IsMonoidalTransformation`).
The witnesses are the chart `ψ`, the codimension `c`, the facts that `Y` is the cosupport of `I_Y`
and that `I_Y` is the ideal sheaf of `Y`, and `isBlowUp_blowUpπ`. -/
theorem isMonoidalTransformation_blowUpπ (hY : IsClosedSubmanifold ψ Y c) :
    (blowUpπ ψ hY).IsMonoidalTransformation hY.idealSheaf := by
  have hs : hY.idealSheaf.support = Y := hY.cosupport_idealSheaf
  refine ⟨n, ψ, c, ?_, ?_, ?_⟩
  · rw [hs]; exact hY
  · rw [hs]; exact hY.isIdealSheafOf_idealSheaf
  · change IsBlowUp ψ hY.idealSheaf.support c (blowUpπ ψ hY)
    rw [hs]; exact isBlowUp_blowUpπ ψ hY

end BlowUpBundled

end Manifold

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜))

/-! ### Kollár's constructors: the empty sequence and `cons` -/

/-- The empty blow-up sequence `X_0 = M`, of length `0` [Kol07, Definition 29]. -/
def nil (M : AnalyticManifold.{u} 𝕜 E) : FiniteSuccession M where
  length := 0
  later := Fin.elim0
  center i := i.elim0
  map i := i.elim0
  isMonoidal i := i.elim0

variable {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}

/-- The blow-up sequence whose first blow-up is the blowing-up of `M` along the closed
submanifold `Y` (centre the ideal sheaf `hY.idealSheaf` of `Y`), followed by the sequence `rest`
starting with `Bl_Y M` [Kol07, Definition 29]. The later stages are
`finStages (blowUp ψ hY) rest.later`, so that `center`, `map` and `isMonoidal` are `Fin.cases` of
the head and of the fields of `rest`. -/
def cons (hY : IsClosedSubmanifold ψ Y c) (rest : FiniteSuccession (blowUp ψ hY)) :
    FiniteSuccession M where
  length := rest.length + 1
  later := finStages (blowUp ψ hY) rest.later
  center := Fin.cases hY.idealSheaf rest.center
  map := Fin.cases (blowUpπ ψ hY) rest.map
  isMonoidal := Fin.cases (isMonoidalTransformation_blowUpπ ψ hY) rest.isMonoidal

variable {ψ}

theorem nil_length : (nil M).length = 0 := rfl

theorem cons_length (hY : IsClosedSubmanifold ψ Y c) (rest : FiniteSuccession (blowUp ψ hY)) :
    (cons ψ hY rest).length = rest.length + 1 := rfl

theorem cons_center_zero (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) :
    (cons ψ hY rest).center (0 : Fin (rest.length + 1)) = hY.idealSheaf := rfl

theorem cons_map_zero (hY : IsClosedSubmanifold ψ Y c) (rest : FiniteSuccession (blowUp ψ hY)) :
    (cons ψ hY rest).map (0 : Fin (rest.length + 1)) = blowUpπ ψ hY := rfl

theorem cons_center_succ (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) (j : Fin rest.length) :
    (cons ψ hY rest).center j.succ = rest.center j := rfl

theorem cons_map_succ (hY : IsClosedSubmanifold ψ Y c) (rest : FiniteSuccession (blowUp ψ hY))
    (j : Fin rest.length) : (cons ψ hY rest).map j.succ = rest.map j := rfl

theorem cons_stage_zero (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) : (cons ψ hY rest).stage 0 = M := rfl

theorem cons_stage_succ (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) (j : Fin (rest.length + 1)) :
    (cons ψ hY rest).stage j.succ = rest.stage j := rfl

end AnalyticManifold.FiniteSuccession

end
