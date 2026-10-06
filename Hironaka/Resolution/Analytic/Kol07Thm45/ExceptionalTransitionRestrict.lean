/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionRestrict
import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
import Hironaka.Resolution.Analytic.OrderReduction.Step22Pullback
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The exceptional members under restriction to a smaller open

**Statement.** Restricting a piece's run to a smaller relatively compact open `W' ⊆ W` deletes the
blow-ups whose centres miss `W'` (the functor's `CommutesWithOpenEmbeddings`: the run over `W'` is
the cleaned pull-back `((run over W).pullback incl).eraseEmpty`; the compatibility of
[Kol07, 34.1] and [Wlo09, Theorem 2.0.2(5)]). The theorem
`BlowUpSequence.exists_orderEmb_totalTransformSeqFrom_last_pullback_eraseEmpty` says what this does
to the BOUNDARY FAMILY at the last stage: along the lift `λ := h_r ∘ eraseEmptyLast⁻¹` of a local
isomorphism `h` there is an order embedding `ε` of the cleaned run's index type into the original
run's with `λ⁻¹(H_{ε i}) = H'_i` for every member `i` and `λ⁻¹(H_b) = ∅` outside the range of `ε` —
the members whose creation steps were deleted have empty trace over `W'` (the empty blow-ups
arising from restriction, [Kol07, Warning 20]: these are ONE source of empty traces, not the only
one). `PieceEmbedding.exists_orderEmb_totalTransformSeq_last_liftOfLe` is its instance at a piece,
along the lift `liftOfLe` of the open inclusion `W' ↪ W`.

**Why.** The restriction to a smaller open is the first and last leg — (γ) in the notation of
`LocalResolutionShear.lean` — of the transition of `localResolution_independent_local`,
(γ)·(α)⁻¹·(β)·(α)·(γ)⁻¹, and the only leg where the correspondence of the boundary families is a
proper injection.

**Conventions.** The list-level theorem is stated for an arbitrary start family `F`
(`totalTransformSeqFrom`); the exceptional family is the instance `F := HypersurfaceFamily.empty M`
(`totalTransformSeqFrom_empty`, definitional) with `(empty M).comap h = empty N`
(`HypersurfaceFamily.empty_comap`). The lift is spelled as the lemmas it rests on spell it: the
composite of `Diffeomorph.toAnalyticMap eraseEmptyLast.symm` and `pullbackLiftLast`, coerced to
functions.

**Sources.** The lift of a local isomorphism to the blow-ups, [Kol07, Definition 30.1]; the empty
blow-up convention, [Kol07, 32] and [Kol07, 34.1]; [Wlo09, Theorem 2.0.2(5)]. The proofs compose
`totalTransformSeqFrom_last_pullbackLiftLast` (`OrderReduction/ConcatPullback.lean`) with
`eraseEmptyIdx`/`hyp_eraseEmptyIdx`/`hyp_eq_empty_of_notMem_range_eraseEmptyIdx`
(`Functor/EraseEmptyBoundary.lean`); not in the sources.
-/

public section

open TopologicalSpace Set Topology
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

/-- **The boundary family of the CLEANED pull-back `(h^* L).eraseEmpty` at its last stage against
the boundary family of `L`** ([Kol07, Definition 30.1]; the empty blow-up convention [Kol07, 32],
[Kol07, 34.1]), along the lift `λ := h_r ∘ eraseEmptyLast⁻¹` of the local isomorphism `h` — an order
embedding `ε` of the cleaned list's index type into `L`'s with `λ⁻¹(H^L_{ε i}) = H^{cleaned}_i` for
every `i`, and `λ⁻¹(H^L_b) = ∅` for every `b` outside the range of `ε`. From
`totalTransformSeqFrom_last_pullbackLiftLast` and `eraseEmptyIdx` with `hyp_eraseEmptyIdx`,
`hyp_eq_empty_of_notMem_range_eraseEmptyIdx`. -/
theorem exists_orderEmb_totalTransformSeqFrom_last_pullback_eraseEmpty (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (F : HypersurfaceFamily M)
    (hF : ∀ j, IsClosed (F.hyp j)) :
    ∃ ε : ((L.pullback h hh).eraseEmpty.toSuccession.totalTransformSeqFrom (F.comap h)
        (Fin.last _)).ι ↪o (L.toSuccession.totalTransformSeqFrom F (Fin.last _)).ι,
      (∀ i, (⇑(L.pullbackLiftLast h hh) ∘
          ⇑(Diffeomorph.toAnalyticMap (L.pullback h hh).eraseEmptyLast.symm)) ⁻¹'
            (L.toSuccession.totalTransformSeqFrom F (Fin.last _)).hyp (ε i) =
          ((L.pullback h hh).eraseEmpty.toSuccession.totalTransformSeqFrom (F.comap h)
            (Fin.last _)).hyp i) ∧
        ∀ b, b ∉ Set.range ε →
          (⇑(L.pullbackLiftLast h hh) ∘
            ⇑(Diffeomorph.toAnalyticMap (L.pullback h hh).eraseEmptyLast.symm)) ⁻¹'
              (L.toSuccession.totalTransformSeqFrom F (Fin.last _)).hyp b = ∅ := by
  have hF' : ∀ j, IsClosed ((F.comap h).hyp j) := fun j =>
    (hF j).preimage h.contMDiff.continuous
  have h1 := hyp_eraseEmptyIdx (L.pullback h hh) (F.comap h) hF'
  have h2 := hyp_eq_empty_of_notMem_range_eraseEmptyIdx (L.pullback h hh) (F.comap h) hF'
  have key : ∀ (G : HypersurfaceFamily ((L.pullback h hh).stage (Fin.last _)))
      (hG : (L.pullback h hh).toSuccession.totalTransformSeqFrom (F.comap h) (Fin.last _) = G),
      ∃ o : ((L.pullback h hh).toSuccession.totalTransformSeqFrom (F.comap h)
          (Fin.last _)).ι ≃o G.ι,
        ∀ j, ((L.pullback h hh).toSuccession.totalTransformSeqFrom (F.comap h)
          (Fin.last _)).hyp j = G.hyp (o j) := by
    intro G hG
    subst hG
    exact ⟨OrderIso.refl _, fun _ => rfl⟩
  obtain ⟨o, ho⟩ := key _ (totalTransformSeqFrom_last_pullbackLiftLast L h hh F)
  refine ⟨(eraseEmptyIdx (L.pullback h hh) (F.comap h) hF').trans o.toOrderEmbedding,
    fun i => ?_, fun b hb => ?_⟩
  · rw [Set.preimage_comp]
    exact (congrArg
      (fun s => ⇑(Diffeomorph.toAnalyticMap (L.pullback h hh).eraseEmptyLast.symm) ⁻¹' s)
      (ho (eraseEmptyIdx (L.pullback h hh) (F.comap h) hF' i)).symm).trans (h1 i)
  · have hb' : o.symm b ∉ Set.range (eraseEmptyIdx (L.pullback h hh) (F.comap h) hF') :=
      fun ⟨i, hi⟩ => hb ⟨i, by
        change o (eraseEmptyIdx (L.pullback h hh) (F.comap h) hF' i) = b
        rw [hi]
        exact o.apply_symm_apply b⟩
    have h3 : ⇑(L.pullbackLiftLast h hh) ⁻¹'
        (L.toSuccession.totalTransformSeqFrom F (Fin.last _)).hyp b = ∅ := by
      have h4 := h2 _ hb'
      rw [ho (o.symm b)] at h4
      exact ((congrArg (HypersurfaceFamily.hyp _) (o.apply_symm_apply b)).symm.trans h4)
    rw [Set.preimage_comp, h3, Set.preimage_empty]

end AnalyticManifold.BlowUpSequence

namespace Manifold

open Hironaka.Manifold

section LegGamma

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V) (bed : BEDanFamStar.{u} 𝕜) (W : Opens (pieceAmbient.{u} 𝕜 E.G))
  (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G)))) (W' : Opens (pieceAmbient.{u} 𝕜 E.G))
  (hW' : IsCompact (closure (W' : Set (pieceAmbient 𝕜 E.G))))

/-- The transport of a hypersurface family along an equality: an order isomorphism of the index
types matching the members. -/
theorem HypersurfaceFamily.exists_orderIso_of_eq {A : Type u}
    {F₁ F₂ : HypersurfaceFamily A} (h : F₁ = F₂) :
    ∃ o : F₁.ι ≃o F₂.ι, ∀ j, F₁.hyp j = F₂.hyp (o j) := by
  subst h
  exact ⟨OrderIso.refl _, fun _ => rfl⟩

/-- The boundary family at the last stage of an equal list, read through `stageOfEq`. -/
theorem _root_.AnalyticManifold.BlowUpSequence.totalTransformSeqFrom_last_stageOfEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n' : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n' → 𝕜)}
    {M : AnalyticManifold.{u} 𝕜 E} {L₁ L₂ : AnalyticManifold.BlowUpSequence ψ₀ M} (e : L₁ = L₂)
    (G : HypersurfaceFamily M) :
    L₂.toSuccession.totalTransformSeqFrom G (Fin.last _) =
      (L₁.toSuccession.totalTransformSeqFrom G (Fin.last _)).comap
        ⇑(Diffeomorph.toAnalyticMap (AnalyticManifold.BlowUpSequence.stageOfEq e).symm) := by
  subst e
  rfl

/-- The manifold level at the piece: along the lift `liftOfLe` of the open inclusion `W' ↪ W`, the
last-stage boundary family over `W'` corresponds to the one over `W` — `eraseEmptyIdx` transported
along `localResolutionSeq_of_le` and `empty_comap`. -/
theorem _root_.Hironaka.Manifold.PieceEmbedding.exists_orderEmb_totalTransformSeq_last_liftOfLe
    (hle : W' ≤ W) :
    ∃ ε : ((E.localResolutionSeq bed W' hW').toSuccession.totalTransformSeq (Fin.last _)).ι ↪o
        ((E.localResolutionSeq bed W hW).toSuccession.totalTransformSeq (Fin.last _)).ι,
      (∀ i, ⇑(E.liftOfLe bed W hW W' hW' hle) ⁻¹'
          ((E.localResolutionSeq bed W hW).toSuccession.totalTransformSeq (Fin.last _)).hyp (ε i) =
        ((E.localResolutionSeq bed W' hW').toSuccession.totalTransformSeq (Fin.last _)).hyp i) ∧
      ∀ b, b ∉ Set.range ε → ⇑(E.liftOfLe bed W hW W' hW' hle) ⁻¹'
        ((E.localResolutionSeq bed W hW).toSuccession.totalTransformSeq (Fin.last _)).hyp b =
          ∅ := by
  obtain ⟨ε₀, h₀a, h₀b⟩ :=
    AnalyticManifold.BlowUpSequence.exists_orderEmb_totalTransformSeqFrom_last_pullback_eraseEmpty
      (E.localResolutionSeq bed W hW) ((pieceAmbient 𝕜 E.G).restrictLE hle)
      (isLocalDiffeomorph_restrictLE hle) (HypersurfaceFamily.empty _) (fun j => j.elim)
  obtain ⟨o₁, ho₁⟩ := HypersurfaceFamily.exists_orderIso_of_eq
    (congrArg (fun G => ((E.localResolutionSeq bed W hW).pullback
        ((pieceAmbient 𝕜 E.G).restrictLE hle)
        (isLocalDiffeomorph_restrictLE hle)).eraseEmpty.toSuccession.totalTransformSeqFrom G
        (Fin.last _))
      (HypersurfaceFamily.empty_comap ⇑((pieceAmbient 𝕜 E.G).restrictLE hle)))
  obtain ⟨o₂, ho₂⟩ := HypersurfaceFamily.exists_orderIso_of_eq
    (AnalyticManifold.BlowUpSequence.totalTransformSeqFrom_last_stageOfEq
      (E.localResolutionSeq_of_le bed W hW W' hW' hle) (HypersurfaceFamily.empty _))
  have hlift : ⇑(E.liftOfLe bed W hW W' hW' hle) =
      (⇑((E.localResolutionSeq bed W hW).pullbackLiftLast ((pieceAmbient 𝕜 E.G).restrictLE hle)
          (isLocalDiffeomorph_restrictLE hle)) ∘
        ⇑(Diffeomorph.toAnalyticMap ((E.localResolutionSeq bed W hW).pullback
          ((pieceAmbient 𝕜 E.G).restrictLE hle)
          (isLocalDiffeomorph_restrictLE hle)).eraseEmptyLast.symm)) ∘
        ⇑(Diffeomorph.toAnalyticMap
          (AnalyticManifold.BlowUpSequence.stageOfEq (E.localResolutionSeq_of_le bed W hW W' hW'
              hle))) := rfl
  have hσ : ∀ s, ⇑(Diffeomorph.toAnalyticMap
        (AnalyticManifold.BlowUpSequence.stageOfEq (E.localResolutionSeq_of_le bed W hW W' hW'
            hle))) ⁻¹'
      (⇑(Diffeomorph.toAnalyticMap
        (AnalyticManifold.BlowUpSequence.stageOfEq (E.localResolutionSeq_of_le bed W hW W' hW'
            hle)).symm) ⁻¹' s) =
      s := by
    intro s
    rw [← Set.preimage_comp]
    exact (congrArg (fun g : _ → _ => g ⁻¹' s) (funext fun x =>
      (AnalyticManifold.BlowUpSequence.stageOfEq
        (E.localResolutionSeq_of_le bed W hW W' hW' hle)).symm_apply_apply x)).trans
      Set.preimage_id
  refine ⟨(o₂.symm.trans o₁.symm).toOrderEmbedding.trans ε₀, fun i => ?_, fun b hb => ?_⟩
  · rw [hlift, Set.preimage_comp]
    refine (congrArg _ (h₀a (o₁.symm (o₂.symm i)))).trans ?_
    refine (congrArg _ ((ho₁ _).trans (congrArg _ (o₁.apply_symm_apply (o₂.symm i))))).trans ?_
    refine (congrArg _ ((ho₂ _).trans (congrArg _ (o₂.apply_symm_apply i)))).trans ?_
    exact hσ _
  · have hb' : b ∉ Set.range ε₀ := fun ⟨k, hk⟩ => hb ⟨o₂ (o₁ k), by
      change ε₀ (o₁.symm (o₂.symm (o₂ (o₁ k)))) = b
      exact (congrArg (fun z => ε₀ (o₁.symm z)) (o₂.symm_apply_apply (o₁ k))).trans
        ((congrArg ε₀ (o₁.symm_apply_apply k)).trans hk)⟩
    rw [hlift, Set.preimage_comp]
    exact (congrArg _ (h₀b b hb')).trans Set.preimage_empty

end LegGamma

end Manifold
