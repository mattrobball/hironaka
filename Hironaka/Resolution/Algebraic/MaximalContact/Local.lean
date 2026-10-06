/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.Basic
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.Remark33Exceptional
import Mathlib.Algebra.Order.Module.Field
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Hypersurfaces of maximal contact: locality of the dynamic form

[Kol07, Definition 78] ends with "Being a hypersurface of maximal contact is a local property."
The definition itself (`IsDynamicMaximalContact`,
`Hironaka/Resolution/Algebraic/MaximalContact/Basic.lean`) quantifies over every open `X⁰ ⊆ X` and
every smooth blow-up sequence of order `m` for `(X⁰, I|_{X⁰})` with no divisorial part; this file
proves that the property can be checked on the members of an open cover `X = ⋃ U_α`
(`isDynamicMaximalContact_iff_forall_opens`):

* **(⇒)** (`IsDynamicMaximalContact.comap`): an open subscheme `j : Y ⟶ U_α` of a member of the
  cover is an open subscheme `j ≫ (U_α).ι` of `X` (Mathlib's `IsOpenImmersion.comp`), and the
  restricted data are the restricted data of `X` (`comap_comp`); so the hypothesis on `X` applies
  verbatim. Nothing about sequences is used.
* **(⇐)** (`isDynamicMaximalContact_of_forall_opens`): let `j : Y ⟶ X` be an open subscheme and
  `S` a smooth blow-up sequence of order `m` for `(Y, I|_Y)`. The opens `V_α := j⁻¹(U_α)` cover
  `Y`. Along each open immersion `(V_α).ι` the pulled-back sequence `S.pullback (V_α).ι` is again
  a smooth blow-up sequence of order `m` for the restricted data (the functoriality
  [Kol07, 34.1], `IsOrderSeq.pullback`; an open immersion is smooth of relative dimension `0`, and
  no deletion of empty blow-ups is needed, since an empty pulled-back centre satisfies the clauses
  of [Kol07, Definition 66] vacuously), and `V_α` is an open subscheme of `U_α` through
  `j.resLE : V_α ⟶ U_α` (`resLE_comp_ι`, `IsOpenImmersion.of_comp`). The hypothesis on `U_α`
  therefore puts every centre of the pulled-back sequence inside the strict transform of
  `H ∩ V_α`. The centres of the pulled-back sequence are the inverse images of the centres
  (`center_pullback`) and its strict transforms are the inverse images of the strict transforms
  (`strictTransformSeq_pullback`, for the pull-back of [Kol07, Definition 30.1]) under the stage
  lifts `h_i : (S.pullback (V_α).ι).stage i ⟶ S.stage i`, which are open immersions
  (`isOpenImmersion_pullbackStageHom`) whose images `Π_i⁻¹(V_α)` cover the stage
  (`range_pullbackStageHom`). Containment of closed subschemes is local: an inclusion of ideal
  sheaves holds once it holds after `comap` along a jointly surjective family of open immersions
  (`le_of_comap_le_of_forall_exists`), which gives `Z_i ⊆ H_i` on `Y`.

Kollár's standing hypotheses (`X` smooth over `k` of characteristic zero) enter only through
`IsOrderSeq.pullback`, which needs them to carry the order clause along the pull-back.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.BlowUpSequence

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The direction (⇒) of the locality in [Kol07, Definition 78]: a hypersurface of maximal contact
for `(X, I, m)` restricts to one on every open subscheme `g : Y ⟶ X`, since an open subscheme of
`Y` is an open subscheme of `X`, and the restricted data restrict again. -/
theorem IsDynamicMaximalContact.comap {I H : X.IdealSheafData} {m : ℕ}
    (hH : IsDynamicMaximalContact f I m H) {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] :
    IsDynamicMaximalContact (g ≫ f) (I.comap g) m (H.comap g) := by
  intro Z j _ S hS i
  have := hH Z (j ≫ g) S (by simpa only [Category.assoc, comap_comp] using hS) i
  simpa only [comap_comp] using this

section Local

variable [CharZero k] (n : ℕ) [SmoothOfRelativeDimension n f]

include n in
/-- The direction (⇐) of the locality in [Kol07, Definition 78]: if `H ∩ U_α` is a hypersurface of
maximal contact for `(U_α, I|_{U_α}, m)` for every member of an open cover
`X = ⋃ U_α`, then `H` is one for `(X, I, m)`. Given an open `j : Y ⟶ X` and a sequence `S` of
order `m` on `Y`, pull `S` back to the pieces `j⁻¹(U_α)` of the induced cover of `Y`, read the
centres and strict transforms of the pulled-back sequences as inverse images under the stage
lifts, and descend the containment `Z_i ⊆ H_i` along those open immersions, which cover each
stage. -/
theorem isDynamicMaximalContact_of_forall_opens {I H : X.IdealSheafData} {m : ℕ} {ι : Type*}
    (U : ι → X.Opens) (hU : iSup U = ⊤)
    (h : ∀ α, IsDynamicMaximalContact ((U α).ι ≫ f) (I.comap (U α).ι) m (H.comap (U α).ι)) :
    IsDynamicMaximalContact f I m H := by
  intro Y j _ S hS i
  have : ∀ α, IsOpenImmersion (S.pullbackStageHom (j ⁻¹ᵁ U α).ι i.castSucc) := fun α =>
    isOpenImmersion_pullbackStageHom S _ _
  refine Remark33.le_of_comap_le_of_forall_exists
    (fun α => S.pullbackStageHom (j ⁻¹ᵁ U α).ι i.castSucc) ?_ fun α => ?_
  · -- the stage lifts of the pieces `j⁻¹(U_α)` cover the stage
    intro x
    have hx : j (S.stageMap i.castSucc x) ∈ iSup U := by
      rw [hU]
      exact TopologicalSpace.Opens.mem_top _
    obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have hmem : x ∈ Set.range (S.pullbackStageHom (j ⁻¹ᵁ U α).ι i.castSucc) := by
      rw [range_pullbackStageHom, Scheme.Opens.range_ι]
      exact hα
    obtain ⟨y, hy⟩ := hmem
    exact ⟨α, y, hy⟩
  · -- on the piece `V := j⁻¹(U_α)`, an open subscheme of `U_α` through `j.resLE`
    set V : Y.Opens := j ⁻¹ᵁ U α with hV
    let j' : V.toScheme ⟶ (U α).toScheme := j.resLE (U α) V le_rfl
    have hj' : j' ≫ (U α).ι = V.ι ≫ j := Scheme.Hom.resLE_comp_ι j le_rfl
    have : IsOpenImmersion (j' ≫ (U α).ι) := by
      rw [hj']
      infer_instance
    have : IsOpenImmersion j' := IsOpenImmersion.of_comp j' (U α).ι
    have hS' := IsOrderSeq.pullback (j ≫ f) (0 + n) V.ι (d := 0) hS
    rw [empty_comap, ← comap_comp, ← hj', comap_comp, ← Category.assoc, ← hj',
      Category.assoc] at hS'
    have key := h α V.toScheme j' (S.pullback V.ι) hS' (S.pullbackCenterIdx V.ι i)
    rw [← comap_comp, hj', comap_comp, strictTransformSeq_pullback_castSucc,
      center_pullback] at key
    exact key

include n in
/-- Kollár's "Being a hypersurface of maximal contact is a local property" ([Kol07, Definition 78]):
for an open cover `X = ⋃ U_α`, `H` is a hypersurface of maximal contact for `(X, I, m)` iff
`H ∩ U_α` is one for `(U_α, I|_{U_α}, m)` for every `α`. -/
theorem isDynamicMaximalContact_iff_forall_opens (I : X.IdealSheafData) (m : ℕ)
    (H : X.IdealSheafData) {ι : Type*} (U : ι → X.Opens) (hU : iSup U = ⊤) :
    IsDynamicMaximalContact f I m H ↔
      ∀ α, IsDynamicMaximalContact ((U α).ι ≫ f) (I.comap (U α).ι) m (H.comap (U α).ι) :=
  ⟨fun hH α => hH.comap f (U α).ι, isDynamicMaximalContact_of_forall_opens f n U hU⟩

end Local

end AlgebraicGeometry.Scheme.IdealSheafData
