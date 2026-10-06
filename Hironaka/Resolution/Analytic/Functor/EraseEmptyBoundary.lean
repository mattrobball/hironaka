/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Induced
public import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyEmbedding
public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
public import Hironaka.Resolution.Analytic.Functor.EraseEmptyConcat
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The boundary family along the deletion of empty blow-ups

The boundary family `totalTransformSeqFrom F` at the last stage of a list has one exceptional
member per step (`HypersurfaceFamily.totalTransform` appends a `PUnit` summand to the index set at
each step). After the deletion of the empty blow-ups ([Kol07, 34.1]) the cleaned list has fewer
members, one per deleted step, so the two boundary families are not equal: **the cleaned list's
boundary family embeds order-preservingly into the list's boundary family pulled back along
`eraseEmptyLast⁻¹`, matching the members, with the members outside the range (the exceptional
divisors of the deleted steps, `π⁻¹(∅) = ∅`, and their empty strict transforms) empty, and the
original members matched along `originalIdx`** (`BlowUpSequence.eraseEmptyIdx`, `hyp_eraseEmptyIdx`,
`hyp_eq_empty_of_notMem_range_eraseEmptyIdx`, `eraseEmptyIdx_originalIdx`). These are exactly the
hypotheses of `IndifferentToEmptyMembers` on the erased induced triple against the exact
pull-back (the values agree by the convention of [Kol07, 32]).

The proof is a recursion on the list with the two families generalised along an order embedding
that is an *empty extension* (`HypersurfaceFamily.IsEmptyExtension`: members matched, empty
outside the range): a kept step extends the embedding by the new exceptional divisor
(`isEmptyExtension_totalTransform`), a deleted step drops one
(`isEmptyExtension_totalTransform_of_eq_empty`: along the empty blowing-up the strict transforms
of closed members are their preimages and the exceptional divisor is empty), and the transport of
the cleaned tail along `Bl_∅ M ≃ M` is the transport of its boundary family along `map`
(`totalTransformSeqFrom_last_map`). The identifications of index types along the propositional
equalities of families (the `cons` computation rule `cons_totalTransformSeqFromAux_succ`, the `map`
transport) are carried as heterogeneous equalities of `originalIdx` (`heq_originalIdx_cons_last`,
`heq_originalIdx_last_map`).

Closedness of the members (`hF : ∀ j, IsClosed (F.hyp j)`) is needed: along an empty blowing-up
the strict transform of a non-closed set is the preimage of its closure. The lexicographic-sum
order embedding is the generic `Hironaka.Sequence.sumLexMapEmb`.
-/

@[expose] public section

noncomputable section

open Set Topology AnalyticManifold
open scoped Manifold ContDiff

universe u

/-! ### The `cons` computation rule of the boundary family and of `originalIdx` -/

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}

/-- The boundary family from `F` along `cons hY rest` at stage `k + 1` is the family along `rest`
from the total transform of `F` under the first blowing-up (the constructor form of
`totalTransformSeqFrom_succ`). -/
theorem cons_totalTransformSeqFromAux_succ (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : FiniteSuccession (blowUp ψ₀ hY)) (F : HypersurfaceFamily M) :
    ∀ (k : ℕ) (h : k + 1 < (cons ψ₀ hY rest).length + 1),
      (cons ψ₀ hY rest).totalTransformSeqFromAux F (k + 1) h =
        rest.totalTransformSeqFromAux
          (F.totalTransform (blowUpπ ψ₀ hY) hY.idealSheaf.support) k
          (Nat.lt_of_succ_lt_succ h)
  | 0, _ => rfl
  | k + 1, h => by
    change ((cons ψ₀ hY rest).totalTransformSeqFromAux F (k + 1)
        (Nat.lt_of_succ_lt h)).totalTransform
      ((cons ψ₀ hY rest).map ⟨k + 1, _⟩) ((cons ψ₀ hY rest).center ⟨k + 1, _⟩).support = _
    rw [cons_totalTransformSeqFromAux_succ hY rest F k (Nat.lt_of_succ_lt h)]
    rfl

/-- The boundary family at the last stage of `cons hY rest`. -/
theorem cons_totalTransformSeqFrom_last (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : FiniteSuccession (blowUp ψ₀ hY)) (F : HypersurfaceFamily M) :
    (cons ψ₀ hY rest).totalTransformSeqFrom F (Fin.last _) =
      rest.totalTransformSeqFrom (F.totalTransform (blowUpπ ψ₀ hY) Y)
        (Fin.last _) := by
  have h := cons_totalTransformSeqFromAux_succ hY rest F rest.length (Nat.lt_succ_self _)
  rwa [hY.cosupport_idealSheaf] at h

/-- `originalIdx` is compatible with an equality of families (heterogeneously). -/
theorem heq_originalIdx_congr {X : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession X)
    {G₁ G₂ : HypersurfaceFamily X} (e : G₁ = G₂) (i : Fin (S.length + 1)) {j₁ : G₁.ι} {j₂ : G₂.ι}
    (hj : HEq j₁ j₂) : HEq (S.originalIdx G₁ i j₁) (S.originalIdx G₂ i j₂) := by
  subst e
  rw [eq_of_heq hj]

/-- `toLex ∘ inl` is compatible with an equality of families (heterogeneously). -/
theorem _root_.Manifold.HypersurfaceFamily.heq_toLex_inl {X : Type u}
    {G₁ G₂ : HypersurfaceFamily X} (e : G₁ = G₂) {x : G₁.ι} {y : G₂.ι} (h : HEq x y) :
    HEq (toLex (Sum.inl x) : G₁.ι ⊕ₗ PUnit.{u + 1})
      (toLex (Sum.inl y) : G₂.ι ⊕ₗ PUnit.{u + 1}) := by
  subst e
  rw [eq_of_heq h]

theorem heq_originalIdxAux_cons_succ (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : FiniteSuccession (blowUp ψ₀ hY)) (F : HypersurfaceFamily M)
    (j : F.ι) : ∀ (k : ℕ) (h : k + 1 < (cons ψ₀ hY rest).length + 1),
    HEq ((cons ψ₀ hY rest).originalIdxAux F (k + 1) h j)
      (rest.originalIdxAux
        (F.totalTransform (blowUpπ ψ₀ hY) hY.idealSheaf.support) k
        (Nat.lt_of_succ_lt_succ h) (toLex (Sum.inl j)))
  | 0, _ => HEq.rfl
  | k + 1, h =>
    HypersurfaceFamily.heq_toLex_inl (cons_totalTransformSeqFromAux_succ hY rest F k
      (Nat.lt_of_succ_lt h)) (heq_originalIdxAux_cons_succ hY rest F j k (Nat.lt_of_succ_lt h))

/-- The index of an original member at the last stage of `cons hY rest` is its index, as a member
of the total transform of `F`, at the last stage of `rest` (heterogeneously, across the `cons`
computation rule of the boundary family). -/
theorem heq_originalIdx_cons_last (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : FiniteSuccession (blowUp ψ₀ hY)) (F : HypersurfaceFamily M)
    (j : F.ι) :
    HEq ((cons ψ₀ hY rest).originalIdx F (Fin.last _) j)
      (rest.originalIdx (F.totalTransform (blowUpπ ψ₀ hY) Y) (Fin.last _)
        (toLex (Sum.inl j))) :=
  (heq_originalIdxAux_cons_succ hY rest F j rest.length (Nat.lt_succ_self _)).trans
    (heq_originalIdx_congr rest
      (congrArg (F.totalTransform (blowUpπ ψ₀ hY)) hY.cosupport_idealSheaf)
      (Fin.last _) HEq.rfl)

end AnalyticManifold.FiniteSuccession

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### Empty extensions of hypersurface families -/

namespace HypersurfaceFamily

/-- The relation between two hypersurface families on the same space that
`IndifferentToEmptyMembers` (`Hironaka.Resolution.Analytic.Functor.Family`) asks for: `G` embeds
order-preservingly into `G'` along `e₀`, the members are matched along `e₀`, and the members of
`G'` outside the range of `e₀` are empty. -/
def IsEmptyExtension {X : Type u} {G G' : HypersurfaceFamily X} (e₀ : G.ι ↪o G'.ι) : Prop :=
  (∀ j, G'.hyp (e₀ j) = G.hyp j) ∧ ∀ b, b ∉ Set.range e₀ → G'.hyp b = ∅

/-- The order embedding `α ↪o α ⊕ₗ PUnit` of the original members. -/
def inlLexEmb (α : Type u) [LinearOrder α] : α ↪o α ⊕ₗ PUnit.{u + 1} :=
  OrderEmbedding.ofMapLEIff (fun a => toLex (Sum.inl a)) fun _ _ => Sum.Lex.inl_le_inl_iff

theorem inlLexEmb_apply (α : Type u) [LinearOrder α] (a : α) :
    inlLexEmb α a = toLex (Sum.inl a) := rfl

variable {M : AnalyticManifold.{u} 𝕜 E}

/-- Every member of a total transform of a family is closed when the centre is: the strict
transforms are closures, the exceptional divisor a preimage of a closed set. -/
theorem isClosed_hyp_totalTransform {X' : Type u} [TopologicalSpace X'] {π : X' → M}
    (hπ : Continuous π) {Y : Set M} (hY : IsClosed Y) (G : HypersurfaceFamily M) (k) :
    IsClosed ((G.totalTransform π Y).hyp k) := by
  obtain ⟨k', rfl⟩ : ∃ k', toLex k' = k := ⟨ofLex k, rfl⟩
  rcases k' with j | u
  · exact isClosed_closure
  · exact hY.preimage hπ

/-- An empty extension is propagated through the total transform under a blowing-up: the strict
transforms of matched members are matched, the new exceptional divisors are matched, the strict
transform of an empty member is empty. -/
theorem isEmptyExtension_totalTransform {X' : Type u} [TopologicalSpace X'] (π : X' → M)
    (Y : Set M) {G G' : HypersurfaceFamily M} {e₀ : G.ι ↪o G'.ι} (he : IsEmptyExtension e₀) :
    IsEmptyExtension (G := G.totalTransform π Y) (G' := G'.totalTransform π Y)
      (Hironaka.Sequence.sumLexMapEmb (γ := PUnit.{u + 1}) e₀) := by
  refine ⟨fun k => ?_, fun b hb => ?_⟩
  · obtain ⟨k', rfl⟩ : ∃ k', toLex k' = k := ⟨ofLex k, rfl⟩
    rcases k' with j | u
    · exact congrArg (strictTransformSet π Y) (he.1 j)
    · rfl
  · obtain ⟨b', rfl⟩ : ∃ b', toLex b' = b := ⟨ofLex b, rfl⟩
    rcases b' with j | u
    · have hj : j ∉ Set.range e₀ := fun ⟨a, ha⟩ => hb ⟨toLex (Sum.inl a), by
        change toLex (Sum.inl (e₀ a)) = _
        exact congrArg (fun x => toLex (Sum.inl x)) ha⟩
      change strictTransformSet π Y (G'.hyp j) = ∅
      rw [he.2 j hj]
      simp [strictTransformSet]
    · exact absurd ⟨toLex (Sum.inr u), Hironaka.Sequence.sumLexMapEmb_apply_inr e₀ u⟩ hb

/-- Along a blowing-up with EMPTY centre, an empty extension `G ↪ G'` is propagated to
`π⁻¹(G) ↪ G'.totalTransform π ∅` through the original members: the strict transforms of the closed
members are their preimages, the (empty) exceptional divisor is outside the range. -/
theorem isEmptyExtension_totalTransform_of_eq_empty {X' : AnalyticManifold.{u} 𝕜 E} {π : X' → M}
    (hπ : Continuous π) {Y : Set M} (hY₀ : Y = ∅) {G G' : HypersurfaceFamily M}
    {e₀ : G.ι ↪o G'.ι} (he : IsEmptyExtension e₀) (hG' : ∀ j, IsClosed (G'.hyp j)) :
    IsEmptyExtension (G := G.comap π) (G' := G'.totalTransform π Y)
      (e₀.trans (inlLexEmb G'.ι)) := by
  subst hY₀
  refine ⟨fun j => ?_, fun b hb => ?_⟩
  · change strictTransformSet π ∅ (G'.hyp (e₀ j)) = π ⁻¹' G.hyp j
    rw [Hironaka.Manifold.strictTransformSet_empty_of_isClosed hπ (hG' _), he.1 j]
  · obtain ⟨b', rfl⟩ : ∃ b', toLex b' = b := ⟨ofLex b, rfl⟩
    rcases b' with j | u
    · have hj : j ∉ Set.range e₀ := fun ⟨a, ha⟩ => hb ⟨a, by
        change toLex (Sum.inl (e₀ a)) = _
        exact congrArg (fun x => toLex (Sum.inl x)) ha⟩
      change strictTransformSet π ∅ (G'.hyp j) = ∅
      rw [he.2 j hj]
      simp [strictTransformSet]
    · exact Set.preimage_empty

theorem comap_symm_comap_family {N : AnalyticManifold.{u} 𝕜 E}
    (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) (F : HypersurfaceFamily N) :
    (F.comap ⇑φ).comap ⇑φ.symm = F :=
  (HypersurfaceFamily.comap_comap F ⇑φ ⇑φ.symm).trans
    ((congrArg (fun g : N → N => HypersurfaceFamily.comap g F)
      (funext φ.apply_symm_apply : ⇑φ ∘ ⇑φ.symm = id)).trans rfl)

end HypersurfaceFamily

/-! ### The boundary correspondence -/

/-- The correspondence between a family `GA` on `A` and a family `GB` on `B` along
`T : A ≃ B`, with the original members `oA`, `oB` (indexed by `ι₀`): an order embedding
`GB.ι ↪o GA.ι` matching the members through `T⁻¹`, with the members of `GA` outside its range empty
and the original members matched. -/
def _root_.Hironaka.Manifold.BoundaryCorr {A B : AnalyticManifold.{u} 𝕜 E} (T : Diffeomorph 𝓘(𝕜,
    E) 𝓘(𝕜, E) A B ω)
    (GA : HypersurfaceFamily A) (GB : HypersurfaceFamily B) {ι₀ : Type u} (oA : ι₀ → GA.ι)
    (oB : ι₀ → GB.ι) : Prop :=
  ∃ e' : GB.ι ↪o GA.ι, (∀ i, ⇑T.symm ⁻¹' GA.hyp (e' i) = GB.hyp i) ∧
    (∀ b, b ∉ Set.range e' → GA.hyp b = ∅) ∧ ∀ j, e' (oB j) = oA j

end Manifold

namespace Hironaka.Manifold.BoundaryCorr

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

variable {A B C : AnalyticManifold.{u} 𝕜 E} {T : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) A B ω}
  {GA : HypersurfaceFamily A} {GB : HypersurfaceFamily B} {ι₀ ι₁ : Type u} {oA : ι₀ → GA.ι}
  {oB : ι₀ → GB.ι}

theorem comp (h : BoundaryCorr T GA GB oA oB) (k : ι₁ → ι₀) :
    BoundaryCorr T GA GB (oA ∘ k) (oB ∘ k) := by
  obtain ⟨e', h1, h2, h3⟩ := h
  exact ⟨e', h1, h2, fun j => h3 (k j)⟩

theorem trans_comap (h : BoundaryCorr T GA GB oA oB) (ψ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) B C ω) :
    BoundaryCorr (T.trans ψ) GA (GB.comap ⇑ψ.symm) oA oB := by
  obtain ⟨e', h1, h2, h3⟩ := h
  exact ⟨e', fun i => congrArg (fun S => ⇑ψ.symm ⁻¹' S) (h1 i), h2, h3⟩

theorem congr {GA' : HypersurfaceFamily A} {GB' : HypersurfaceFamily B} {oA' : ι₀ → GA'.ι}
    {oB' : ι₀ → GB'.ι} (hA : GA = GA') (hB : GB = GB') (hoA : ∀ j, HEq (oA j) (oA' j))
    (hoB : ∀ j, HEq (oB j) (oB' j)) (h : BoundaryCorr T GA GB oA oB) :
    BoundaryCorr T GA' GB' oA' oB' := by
  subst hA
  subst hB
  obtain rfl : oA = oA' := funext fun j => eq_of_heq (hoA j)
  obtain rfl : oB = oB' := funext fun j => eq_of_heq (hoB j)
  exact h

end Hironaka.Manifold.BoundaryCorr

namespace AnalyticManifold.BlowUpSequence

open Manifold Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

variable {M N : AnalyticManifold.{u} 𝕜 E}

/-- Transport of the correspondence along an equality of lists (the cast `stageOfEq`). -/
theorem boundaryCorr_of_eq {A : AnalyticManifold.{u} 𝕜 E} {L₁ L₂ : BlowUpSequence ψ₀ M}
    (e : L₁ = L₂)
    {T : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) A (L₁.stage (Fin.last _)) ω} {GA : HypersurfaceFamily A}
    (G : HypersurfaceFamily M) {oA : G.ι → GA.ι}
    (h : BoundaryCorr T GA (L₁.toSuccession.totalTransformSeqFrom G (Fin.last _)) oA
      (L₁.toSuccession.originalIdx G (Fin.last _))) :
    BoundaryCorr (T.trans (stageOfEq e)) GA (L₂.toSuccession.totalTransformSeqFrom G (Fin.last _))
      oA (L₂.toSuccession.originalIdx G (Fin.last _)) := by
  subst e
  obtain ⟨e', h1, h2, h3⟩ := h
  exact ⟨e', fun i => h1 i, h2, h3⟩

/-- The boundary family at the last stage of the transported list `Z.map φ` is the pull-back along
`(mapLast φ)⁻¹` of the boundary family from `φ⁻¹(F)` at the last stage of `Z`
(`totalTransform_comap_of_square` at each step). -/
theorem totalTransformSeqFrom_last_map : ∀ {M N : AnalyticManifold.{u} 𝕜 E}
    (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) (Z : BlowUpSequence ψ₀ M) (F : HypersurfaceFamily N),
    (Z.map φ).toSuccession.totalTransformSeqFrom F (Fin.last _) =
      (Z.toSuccession.totalTransformSeqFrom (F.comap ⇑φ) (Fin.last _)).comap ⇑(Z.mapLast φ).symm
  | _, _, φ, nil _, F => (HypersurfaceFamily.comap_symm_comap_family φ F).symm
  | _, _, φ, @cons _ _ _ _ _ _ _ _ Y _ hY rest, F => by
    have e1 : ((cons hY rest).map φ).toSuccession.totalTransformSeqFrom F (Fin.last _) =
        (rest.map (liftDiffeomorph φ hY)).toSuccession.totalTransformSeqFrom
          (F.totalTransform (blowUpπ ψ₀ (hY.image_diffeomorph φ)) (⇑φ '' Y)) (Fin.last _) :=
      FiniteSuccession.cons_totalTransformSeqFrom_last (hY.image_diffeomorph φ)
        (rest.map (liftDiffeomorph φ hY)).toSuccession F
    have e2 : (cons hY rest).toSuccession.totalTransformSeqFrom (F.comap ⇑φ) (Fin.last _) =
        rest.toSuccession.totalTransformSeqFrom ((F.comap ⇑φ).totalTransform (blowUpπ ψ₀ hY) Y)
          (Fin.last _) :=
      FiniteSuccession.cons_totalTransformSeqFrom_last hY rest.toSuccession _
    have hsq : (F.totalTransform (blowUpπ ψ₀ (hY.image_diffeomorph φ)) (⇑φ '' Y)).comap
          ⇑(liftDiffeomorph φ hY) = (F.comap ⇑φ).totalTransform (blowUpπ ψ₀ hY) Y :=
      HypersurfaceFamily.totalTransform_comap_of_square (Diffeomorph.toAnalyticMap φ)
        (hY.image_diffeomorph φ) hY (preimage_image_diffeomorph φ Y).symm
        (Diffeomorph.toAnalyticMap (liftDiffeomorph φ hY)) (liftDiffeomorph φ hY).isLocalDiffeomorph
        (blowUpπ_liftDiffeomorph φ hY) F
    rw [e1, e2]
    change _ = (rest.toSuccession.totalTransformSeqFrom _ (Fin.last _)).comap
      ⇑(rest.mapLast (liftDiffeomorph φ hY)).symm
    rw [totalTransformSeqFrom_last_map (liftDiffeomorph φ hY) rest, hsq]

/-- The index of an original member at the last stage of the transported list is its index for the
pulled-back family at the last stage of the list (heterogeneously, across
`totalTransformSeqFrom_last_map`). -/
theorem heq_originalIdx_last_map : ∀ {M N : AnalyticManifold.{u} 𝕜 E}
    (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) (Z : BlowUpSequence ψ₀ M) (F : HypersurfaceFamily N)
    (j : F.ι),
    HEq ((Z.map φ).toSuccession.originalIdx F (Fin.last _) j)
      (Z.toSuccession.originalIdx (F.comap ⇑φ) (Fin.last _) j)
  | _, _, _, nil _, _, _ => HEq.rfl
  | _, _, φ, @cons _ _ _ _ _ _ _ _ Y _ hY rest, F, j =>
    have hsq : (F.totalTransform (blowUpπ ψ₀ (hY.image_diffeomorph φ)) (⇑φ '' Y)).comap
          ⇑(liftDiffeomorph φ hY) = (F.comap ⇑φ).totalTransform (blowUpπ ψ₀ hY) Y :=
      HypersurfaceFamily.totalTransform_comap_of_square (Diffeomorph.toAnalyticMap φ)
        (hY.image_diffeomorph φ) hY (preimage_image_diffeomorph φ Y).symm
        (Diffeomorph.toAnalyticMap (liftDiffeomorph φ hY)) (liftDiffeomorph φ hY).isLocalDiffeomorph
        (blowUpπ_liftDiffeomorph φ hY) F
    (FiniteSuccession.heq_originalIdx_cons_last (hY.image_diffeomorph φ)
      (rest.map (liftDiffeomorph φ hY)).toSuccession F j).trans
      ((heq_originalIdx_last_map (liftDiffeomorph φ hY) rest _ (toLex (Sum.inl j))).trans
        ((FiniteSuccession.heq_originalIdx_congr rest.toSuccession hsq (Fin.last _) HEq.rfl).trans
          (FiniteSuccession.heq_originalIdx_cons_last hY rest.toSuccession (F.comap ⇑φ) j).symm))

/-- [Kol07, 32] and 34.1, the recursion: for an empty extension
`e₀ : G ↪ G'` of families with closed members, the boundary family from `G` at the last stage of the
cleaned list corresponds along `eraseEmptyLast` to the boundary family from `G'` at the last stage
of the list, the original members matched along `e₀`. -/
theorem boundaryCorr_eraseEmpty : ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (G G' : HypersurfaceFamily M) (e₀ : G.ι ↪o G'.ι), HypersurfaceFamily.IsEmptyExtension e₀ →
    (∀ j, IsClosed (G'.hyp j)) →
    BoundaryCorr L.eraseEmptyLast (L.toSuccession.totalTransformSeqFrom G' (Fin.last _))
      (L.eraseEmpty.toSuccession.totalTransformSeqFrom G (Fin.last _))
      (fun j => L.toSuccession.originalIdx G' (Fin.last _) (e₀ j))
      (L.eraseEmpty.toSuccession.originalIdx G (Fin.last _))
  | _, nil _, G, G', e₀, he, _ => ⟨e₀, fun i => he.1 i, he.2, fun _ => rfl⟩
  | _, @cons _ _ _ _ _ _ _ _ Y _ hY rest, G, G', e₀, he, hG' => by
    have hπ : Continuous (blowUpπ ψ₀ hY) := (blowUpπ ψ₀ hY).contMDiff.continuous
    have hG₁' : ∀ k, IsClosed ((G'.totalTransform (blowUpπ ψ₀ hY) Y).hyp k) :=
      HypersurfaceFamily.isClosed_hyp_totalTransform hπ hY.isClosed G'
    have eA : rest.toSuccession.totalTransformSeqFrom (G'.totalTransform (blowUpπ ψ₀ hY) Y)
        (Fin.last _) = (cons hY rest).toSuccession.totalTransformSeqFrom G' (Fin.last _) :=
      (FiniteSuccession.cons_totalTransformSeqFrom_last hY rest.toSuccession G').symm
    by_cases hY₀ : Y = ∅
    · have hce : G.comap ⇑(emptyBlowUpDiffeomorph hY hY₀) = G.comap ⇑(blowUpπ ψ₀ hY) :=
        congrArg (fun f : blowUp ψ₀ hY → _ => HypersurfaceFamily.comap f G)
          (funext (emptyBlowUpDiffeomorph_apply hY hY₀))
      have ih := boundaryCorr_eraseEmpty rest (G.comap ⇑(blowUpπ ψ₀ hY))
        (G'.totalTransform (blowUpπ ψ₀ hY) Y) (e₀.trans (HypersurfaceFamily.inlLexEmb G'.ι))
        (HypersurfaceFamily.isEmptyExtension_totalTransform_of_eq_empty hπ hY₀ he hG') hG₁'
      have eB : (rest.eraseEmpty.toSuccession.totalTransformSeqFrom (G.comap ⇑(blowUpπ ψ₀ hY))
            (Fin.last _)).comap ⇑(rest.eraseEmpty.mapLast (emptyBlowUpDiffeomorph hY hY₀)).symm =
          (rest.eraseEmpty.map (emptyBlowUpDiffeomorph hY hY₀)).toSuccession.totalTransformSeqFrom
            G (Fin.last _) := by
        rw [totalTransformSeqFrom_last_map (emptyBlowUpDiffeomorph hY hY₀) rest.eraseEmpty G, hce]
      rw [eraseEmptyLast_cons_of_eq_empty hY rest hY₀]
      refine boundaryCorr_of_eq (eraseEmpty_cons_of_eq_empty hY rest hY₀).symm G ?_
      refine BoundaryCorr.congr eA eB (fun j => ?_) (fun j => ?_)
        (ih.trans_comap (rest.eraseEmpty.mapLast (emptyBlowUpDiffeomorph hY hY₀)))
      · exact (FiniteSuccession.heq_originalIdx_cons_last hY rest.toSuccession G' (e₀ j)).symm
      · exact ((heq_originalIdx_last_map (emptyBlowUpDiffeomorph hY hY₀) rest.eraseEmpty G j).trans
          (FiniteSuccession.heq_originalIdx_congr rest.eraseEmpty.toSuccession hce (Fin.last _)
            HEq.rfl)).symm
    · have ih := boundaryCorr_eraseEmpty rest (G.totalTransform (blowUpπ ψ₀ hY) Y)
        (G'.totalTransform (blowUpπ ψ₀ hY) Y)
        (Hironaka.Sequence.sumLexMapEmb (γ := PUnit.{u + 1}) e₀)
        (HypersurfaceFamily.isEmptyExtension_totalTransform (blowUpπ ψ₀ hY) Y he) hG₁'
      have eB : rest.eraseEmpty.toSuccession.totalTransformSeqFrom
            (G.totalTransform (blowUpπ ψ₀ hY) Y) (Fin.last _) =
          (cons hY rest.eraseEmpty).toSuccession.totalTransformSeqFrom G (Fin.last _) :=
        (FiniteSuccession.cons_totalTransformSeqFrom_last hY rest.eraseEmpty.toSuccession G).symm
      rw [eraseEmptyLast_cons_of_ne_empty hY rest hY₀]
      refine boundaryCorr_of_eq (eraseEmpty_cons_of_ne_empty hY rest hY₀).symm G ?_
      refine BoundaryCorr.congr eA eB (fun j => ?_) (fun j => ?_)
        (ih.comp fun j : G.ι => toLex (Sum.inl j))
      · exact (FiniteSuccession.heq_originalIdx_cons_last hY rest.toSuccession G' (e₀ j)).symm
      · exact (FiniteSuccession.heq_originalIdx_cons_last hY rest.eraseEmpty.toSuccession G j).symm

/-! ### The boundary tool -/

section Tool

variable (L : BlowUpSequence ψ₀ M) (F : HypersurfaceFamily M)

/-- The correspondence for the same family on both sides. -/
theorem boundaryCorr_eraseEmpty_self (hF : ∀ j, IsClosed (F.hyp j)) :
    BoundaryCorr L.eraseEmptyLast (L.toSuccession.totalTransformSeqFrom F (Fin.last _))
      (L.eraseEmpty.toSuccession.totalTransformSeqFrom F (Fin.last _))
      (L.toSuccession.originalIdx F (Fin.last _))
      (L.eraseEmpty.toSuccession.originalIdx F (Fin.last _)) :=
  boundaryCorr_eraseEmpty L F F (OrderIso.refl F.ι).toOrderEmbedding
    ⟨fun _ => rfl, fun b hb => absurd ⟨b, rfl⟩ hb⟩ hF

/-- [Kol07, 32] and 34.1: **the order embedding of the boundary family
at the last stage of the cleaned list into the boundary family at the last stage of the list**
(the `e` of `IndifferentToEmptyMembers`), for a family `F` with closed members. -/
def eraseEmptyIdx (hF : ∀ j, IsClosed (F.hyp j)) :
    (L.eraseEmpty.toSuccession.totalTransformSeqFrom F (Fin.last _)).ι ↪o
      (L.toSuccession.totalTransformSeqFrom F (Fin.last _)).ι :=
  Classical.choose (boundaryCorr_eraseEmpty_self L F hF)

/-- The members are matched through `eraseEmptyLast⁻¹`: the member `eraseEmptyIdx i` of the list's
boundary family pulled back to the cleaned list's last stage is the member `i` of the cleaned
list's boundary family (the first hypothesis of `IndifferentToEmptyMembers`, in the `comap` form
of `AnalyticTriple.pullback`). -/
theorem hyp_eraseEmptyIdx (hF : ∀ j, IsClosed (F.hyp j))
    (i : (L.eraseEmpty.toSuccession.totalTransformSeqFrom F (Fin.last _)).ι) :
    ((L.toSuccession.totalTransformSeqFrom F (Fin.last _)).comap
        ⇑(Diffeomorph.toAnalyticMap L.eraseEmptyLast.symm)).hyp (eraseEmptyIdx L F hF i) =
      (L.eraseEmpty.toSuccession.totalTransformSeqFrom F (Fin.last _)).hyp i :=
  (Classical.choose_spec (boundaryCorr_eraseEmpty_self L F hF)).1 i

/-- The members of the list's boundary family outside the range of `eraseEmptyIdx` — the exceptional
divisors of the deleted steps and their strict transforms — are empty (the second
hypothesis of `IndifferentToEmptyMembers`). -/
theorem hyp_eq_empty_of_notMem_range_eraseEmptyIdx (hF : ∀ j, IsClosed (F.hyp j))
    (b : (L.toSuccession.totalTransformSeqFrom F (Fin.last _)).ι)
    (hb : b ∉ Set.range (eraseEmptyIdx L F hF)) :
    (L.toSuccession.totalTransformSeqFrom F (Fin.last _)).hyp b = ∅ :=
  (Classical.choose_spec (boundaryCorr_eraseEmpty_self L F hF)).2.1 b hb

/-- `hyp_eq_empty_of_notMem_range_eraseEmptyIdx` for the pulled-back family. -/
theorem hyp_comap_eq_empty_of_notMem_range_eraseEmptyIdx (hF : ∀ j, IsClosed (F.hyp j))
    (b : (L.toSuccession.totalTransformSeqFrom F (Fin.last _)).ι)
    (hb : b ∉ Set.range (eraseEmptyIdx L F hF)) :
    ((L.toSuccession.totalTransformSeqFrom F (Fin.last _)).comap
      ⇑(Diffeomorph.toAnalyticMap L.eraseEmptyLast.symm)).hyp b = ∅ := by
  rw [HypersurfaceFamily.comap_hyp, hyp_eq_empty_of_notMem_range_eraseEmptyIdx L F hF b hb,
    Set.preimage_empty]

/-- The original members are matched: `eraseEmptyIdx` sends the index of the transform of the
original member `j` in the cleaned list's boundary family to its index in the list's boundary
family. -/
theorem eraseEmptyIdx_originalIdx (hF : ∀ j, IsClosed (F.hyp j)) (j : F.ι) :
    eraseEmptyIdx L F hF (L.eraseEmpty.toSuccession.originalIdx F (Fin.last _) j) =
      L.toSuccession.originalIdx F (Fin.last _) j :=
  (Classical.choose_spec (boundaryCorr_eraseEmpty_self L F hF)).2.2 j

end Tool

end AnalyticManifold.BlowUpSequence

end
