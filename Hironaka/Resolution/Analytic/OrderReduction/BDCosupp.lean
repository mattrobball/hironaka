/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BDCore
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.PullbackSequence
import Hironaka.Resolution.Analytic.GoingUp.Corollary89
import Hironaka.Resolution.Analytic.GoingUp.MaxOrder
import Hironaka.Resolution.Analytic.MaximalContactLemmas
import Hironaka.Resolution.Analytic.OrderReduction.BDCor85
import Hironaka.Resolution.Analytic.OrderReduction.BDLemmas
import Hironaka.Resolution.Analytic.OrderReduction.TunedLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Lemma 102 (1): the transform of `E^j` misses the cosupport

Clause (1) of [Kol07, Lemma 102]: at the end of `BD_{n,m,j}(X, I, E)`, the birational transform
of `E^j` is disjoint from `cosupp(I_r, m)`. Kollár's argument: the birational transform of `E^j`
at the end is the last stage `S_r` of the sequence restricted to `S = E^j`, and along `S_r` the
order of `I_r` is read by the restricted transforms ([Kol07, Corollary 89]: `S_r ∩ cosupp(I_r, m)`
is the intersection of the cosupports of the restricted transforms of `(D^j I|_S, m - j)`, in
particular contained in `cosupp(I_r|_{S_r}, m)`), which clause (1) of the input functor makes
empty. On the manifold side the first blow-up `π_{-1}` has centre `Z_{-1} ⊆ E^j`, so the transform
of `E^j` after it lies in `S_0 = π_{-1}^{-1}(E^j)`; the later stages carry it inside the transforms
of `S_0`, which are the images of the stages of the pushed-forward sequence. The whole is proved for
the tuned triple `(M, W_s(𝓘), E)`, `s = tuningParam m`, and carried back to `(𝓘, m)` by
`ord_lt_of_tuned`, and the
empty first blow-up is transported along its isomorphism.

* `strictTransformSet_mono`, `FiniteSuccession.strictTransformSeq_mono` — the strict transform is
  monotone in the hypersurface.
* `FiniteSuccession.cosupp_disjoint_cons` — the clause for a sequence from the clause for its tail.
* `BlowUpSequence.strictTransformSet_preimage_liftStep`,
  `BlowUpSequence.strictTransformSeq_pullback` — the strict transforms along the pull-back of a
  sequence are the preimages of the strict transforms along the lifts (local analytic isomorphisms
  are open maps, so preimages commute with closures).
* `BlowUpSequence.cosupp_disjoint_of_pullback` — the clause descends along a surjective local
  analytic isomorphism; `BlowUpSequence.cosupp_disjoint_map_emptyBlowUp` — its transport along the
  isomorphism of an empty blow-up.
* `BDan.cosupp_disjoint_pushforward_toSuccession` — the clause for the pushed-forward tail
  ([Kol07, Corollary 89] against the clause (1) of the input).
* `BDan.coreOfListOf_cosupp_disjoint_of_bridge`, `BDan_cosupp_disjoint_of_bridge` — **Lemma 102
  (1)** for the core over a sequence and for `BDan`, given the identification `PushforwardBridge ψ₀`
  of `BDCore.lean` (discharged in `BDBridge.lean`).
-/

public section

noncomputable section

open Set Topology AnalyticManifold IsLocalRing
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

section Mono

variable {M' M : Type u} [TopologicalSpace M']

/-- The strict transform of a hypersurface is monotone in the hypersurface. -/
theorem strictTransformSet_mono (π : M' → M) (Y : Set M) {H H' : Set M} (h : H ⊆ H') :
    strictTransformSet π Y H ⊆ strictTransformSet π Y H' :=
  closure_mono (Set.preimage_mono (Set.sdiff_subset_sdiff_left h))

end Mono

end Hironaka.Manifold

namespace AnalyticManifold.FiniteSuccession

open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- The strict transforms along a succession are monotone in the hypersurface (indexed by a natural
number with a bound). -/
theorem strictTransformSeqAux_mono (S : FiniteSuccession M) {H H' : Set M} (h : H ⊆ H') :
    ∀ (i : ℕ) (hi : i < S.length + 1),
      S.strictTransformSeqAux H i hi ⊆ S.strictTransformSeqAux H' i hi
  | 0, _ => h
  | i + 1, _ => strictTransformSet_mono _ _ (S.strictTransformSeqAux_mono h i _)

/-- The strict transforms along a succession are monotone in the hypersurface. -/
theorem strictTransformSeq_mono (S : FiniteSuccession M) {H H' : Set M} (h : H ⊆ H')
    (i : Fin (S.length + 1)) : S.strictTransformSeq H i ⊆ S.strictTransformSeq H' i :=
  S.strictTransformSeqAux_mono h i.1 i.2

/-- The clause (1) of [Kol07, Lemma 102] for a sequence `cons hY rest` from the clause for `rest`:
the cosupport of the last weak transform of `J` misses the last strict transform of `H` along the
whole sequence when it does so along `rest` for the transforms of `J` and `H` under the first
blow-up. -/
theorem cosupp_disjoint_cons {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) (J : IdealSheaf M) (H : Set M)
    (s : ℕ)
    (h : Disjoint
      {x | (s : ℕ∞) ≤ (rest.weakTransformSeq
        (IdealSheaf.weakTransform (blowUpπ ψ hY) J hY.idealSheaf)
          (Fin.last _)).ord x}
      (rest.strictTransformSeq
        (strictTransformSet (blowUpπ ψ hY) Y H) (Fin.last _))) :
    Disjoint {x | (s : ℕ∞) ≤ ((cons ψ hY rest).weakTransformSeq J (Fin.last _)).ord x}
      ((cons ψ hY rest).strictTransformSeq H (Fin.last _)) := by
  have hlast : (Fin.last (cons ψ hY rest).length) = (Fin.last rest.length).succ := rfl
  rw [hlast, cons_weakTransformSeq_succ, cons_strictTransformSeq_succ]
  exact h

end AnalyticManifold.FiniteSuccession

namespace AnalyticManifold.BlowUpSequence

open _root_.Manifold
open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

variable {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

/-- The strict transform of `h^{-1}(H)` under the blow-up of `h^{-1}(Y)` is the preimage, along the
lift of `h` to the blow-ups, of the strict transform of `H` under the blow-up of `Y`: the lift is a
local analytic isomorphism, hence an open continuous map, so preimages commute with closures. -/
theorem strictTransformSet_preimage_liftStep (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (H : Set M) :
    strictTransformSet (blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)) (⇑h ⁻¹' Y)
        (⇑h ⁻¹' H) =
      ⇑(liftStep h hh hY) ⁻¹' strictTransformSet (blowUpπ ψ₀ hY) Y H := by
  unfold strictTransformSet
  have hopen : IsOpenMap (liftStep h hh hY) :=
    (isLocalDiffeomorph_liftStep h hh hY).isLocalHomeomorph.isOpenMap
  rw [hopen.preimage_closure_eq_closure_preimage (liftStep h hh hY).contMDiff.continuous]
  congr 1
  ext q
  simp only [Set.mem_preimage, Set.mem_sdiff, blowUpπ_liftStep]

/-- The strict transforms along the pull-back `h^* L` of a sequence are the preimages of the strict
transforms along `L` under the lifts of `h` to the stages (indexed by a natural number with a
bound). -/
theorem strictTransformSeqAux_pullback :
    ∀ {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (H : Set M) (i : ℕ) (hi : i < L.length + 1)
    (hi' : i < (L.pullback h hh).length + 1),
    (L.pullback h hh).toSuccession.strictTransformSeqAux (⇑h ⁻¹' H) i hi' =
      ⇑(L.pullbackLiftAux h hh i hi hi') ⁻¹' (L.toSuccession.strictTransformSeqAux H i hi)
  | _, _, nil _, _, _, _, 0, _, _ => rfl
  | _, _, cons _ _, _, _, _, 0, _, _ => rfl
  | _, _, cons hY rest, h, hh, H, i + 1, hi, hi' => by
    revert hi hi'
    change ∀ (hi : i + 1 < (FiniteSuccession.cons ψ₀ hY rest.toSuccession).length + 1)
      (hi' : i + 1 < (FiniteSuccession.cons ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)
          (rest.pullback (liftStep h hh hY)
            (isLocalDiffeomorph_liftStep h hh hY)).toSuccession).length + 1),
      (FiniteSuccession.cons ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)
          (rest.pullback (liftStep h hh hY)
            (isLocalDiffeomorph_liftStep h hh hY)).toSuccession).strictTransformSeqAux
        (⇑h ⁻¹' H) (i + 1) hi' =
      ⇑(rest.pullbackLiftAux (liftStep h hh hY)
          (isLocalDiffeomorph_liftStep h hh hY) i (Nat.lt_of_succ_lt_succ hi)
          (Nat.lt_of_succ_lt_succ hi')) ⁻¹'
        ((FiniteSuccession.cons ψ₀ hY rest.toSuccession).strictTransformSeqAux H (i + 1) hi)
    intro hi hi'
    rw [FiniteSuccession.cons_strictTransformSeqAux_succ,
      FiniteSuccession.cons_strictTransformSeqAux_succ, hY.cosupport_idealSheaf,
      (hY.preimage_of_isLocalDiffeomorph hh).cosupport_idealSheaf,
      strictTransformSet_preimage_liftStep h hh hY H]
    exact strictTransformSeqAux_pullback rest _ _ _ i _ _
  | _, _, nil _, _, _, _, i + 1, hi, _ => absurd hi (by change ¬ i + 1 < 0 + 1; omega)

/-- The strict transforms along the pull-back `h^* L` of a sequence are the preimages of the strict
transforms along `L` under the lifts of `h` to the stages. -/
theorem strictTransformSeq_pullback (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (H : Set M) (i : Fin (L.length + 1)) :
    (L.pullback h hh).toSuccession.strictTransformSeq (⇑h ⁻¹' H)
        ⟨i.1, Nat.lt_of_lt_of_eq i.2 (congrArg (· + 1) (length_pullback L h hh).symm)⟩ =
      ⇑(L.pullbackLift h hh i) ⁻¹' (L.toSuccession.strictTransformSeq H i) :=
  strictTransformSeqAux_pullback L h hh H i.1 i.2 _

/-- **The clause (1) of [Kol07, Lemma 102] descends along a surjective local analytic
isomorphism**: if along `h^* L` the cosupport of the last weak transform of `h^* J` misses the last
strict transform of `h^{-1}(H)`, then along `L` the cosupport of the last weak transform of `J`
misses the last strict transform of `H`. Every point of the last stage of `L` lifts to the last
stage of `h^* L` (`surjective_pullbackLift`), the order is read at the lift
(`ord_pullback_of_isLocalDiffeomorphAt`), and the strict transforms pull back
(`strictTransformSeq_pullback`). -/
theorem cosupp_disjoint_of_pullback (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (hs : Function.Surjective h) (J : IdealSheaf M) (H : Set M) (s : ℕ)
    (hL : Disjoint
      {x | (s : ℕ∞) ≤ ((L.pullback h hh).toSuccession.weakTransformSeq
        (J.pullback h h.contMDiff) (Fin.last _)).ord x}
      ((L.pullback h hh).toSuccession.strictTransformSeq (⇑h ⁻¹' H) (Fin.last _))) :
    Disjoint {y | (s : ℕ∞) ≤ (L.toSuccession.weakTransformSeq J (Fin.last _)).ord y}
      (L.toSuccession.strictTransformSeq H (Fin.last _)) := by
  have := finiteDimensional_of_chartIso ψ₀
  have hlast : (Fin.last (L.pullback h hh).length : Fin ((L.pullback h hh).length + 1)) =
      ⟨(Fin.last L.length).1, Nat.lt_of_lt_of_eq (Fin.last L.length).2
        (congrArg (· + 1) (length_pullback L h hh).symm)⟩ :=
    Fin.ext (length_pullback L h hh)
  rw [hlast, L.weakTransformSeq_pullback h hh J (Fin.last _),
    L.strictTransformSeq_pullback h hh H (Fin.last _)] at hL
  refine Set.disjoint_left.mpr fun y hy hyH => ?_
  obtain ⟨x, rfl⟩ := L.surjective_pullbackLift h hh hs (Fin.last _) y
  have hx1 : x ∈
      {x | (s : ℕ∞) ≤ (Manifold.IdealSheaf.pullback _ (L.pullbackLift h hh (Fin.last _)).contMDiff
      (L.toSuccession.weakTransformSeq J (Fin.last _))).ord x} := by
    change (s : ℕ∞) ≤ _
    exact hy.trans_eq (IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
      (L.isLocalDiffeomorph_pullbackLift h hh _ x)).symm
  exact Set.disjoint_left.mp hL hx1 hyH

/-- Transport of the clause (1) of [Kol07, Lemma 102] along the isomorphism of an empty blow-up
([Kol07, 32]), as `isOfOrderGe_map_emptyBlowUp`: the transported sequence is the pull-back along
the inverse isomorphism, and the clause descends along it (`cosupp_disjoint_of_pullback`). -/
theorem cosupp_disjoint_map_emptyBlowUp {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (hY₀ : Y = ∅) (P : BlowUpSequence ψ₀ (blowUp ψ₀ hY))
    {J : IdealSheaf M} {H : Set M} {s : ℕ}
    (hP : Disjoint
      {x | (s : ℕ∞) ≤ (P.toSuccession.weakTransformSeq
        (J.pullback _ (blowUpπ ψ₀ hY).contMDiff) (Fin.last _)).ord x}
      (P.toSuccession.strictTransformSeq (⇑(blowUpπ ψ₀ hY) ⁻¹' H) (Fin.last _))) :
    Disjoint
      {x | (s : ℕ∞) ≤ ((P.map (emptyBlowUpDiffeomorph hY hY₀)).toSuccession.weakTransformSeq J
        (Fin.last _)).ord x}
      ((P.map (emptyBlowUpDiffeomorph hY hY₀)).toSuccession.strictTransformSeq H (Fin.last _)) := by
  have := finiteDimensional_of_chartIso ψ₀
  set g := emptyBlowUpDiffeomorph hY hY₀ with hg
  rw [map_eq_pullback_symm]
  have hid : (Diffeomorph.toAnalyticMap g.symm).comp (Diffeomorph.toAnalyticMap g) =
      ContMDiffMap.id :=
    ContMDiffMap.ext fun x => g.symm_apply_apply x
  have hsurj : Function.Surjective (Diffeomorph.toAnalyticMap g) := g.toEquiv.surjective
  refine cosupp_disjoint_of_pullback _ (Diffeomorph.toAnalyticMap g)
    g.isLocalDiffeomorph hsurj J H s ?_
  rw [pullback_comp, pullback_congr _ hid _ (isLocalDiffeomorph_id _), pullback_id]
  have hgπ : ⇑(Diffeomorph.toAnalyticMap g) = ⇑(blowUpπ ψ₀ hY) :=
    funext fun p => emptyBlowUpDiffeomorph_apply hY hY₀ p
  have h1 : J.pullback _ (Diffeomorph.toAnalyticMap g).contMDiff =
      J.pullback _ (blowUpπ ψ₀ hY).contMDiff :=
    IdealSheaf.pullback_congr J _ _ hgπ
  rw [h1, hgπ]
  exact hP

end AnalyticManifold.BlowUpSequence

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

namespace BDan

open _root_.Manifold

variable [FiniteDimensional 𝕜 E] {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  (T : AnalyticTriple ψ₀ M) (s : ℕ) (j : T.F.ι)

/-- The clause (1) of [Kol07, Lemma 102] for the pushed-forward tail (the proof of the lemma: "such
that `Π^{-1}_{r*}(E^j)` is disjoint from `cosupp(I_r, m)`"): along the push-forward of a sequence
`P` on `S_0` of order `≥ s` for the restricted triple, the cosupport `{ord ≥ s}` of the last weak
transform of `I_0` misses the last transform `S_r` of `S_0`. By [Kol07, Corollary 89]
(`setOf_le_ord_markedTransformSeq_pushforward_inter_eq_iInter`) a point of `S_r` where the
controlled transform of `(I_0, s)` has order `≥ s` is one where the controlled transform of
`(I_0|_{S_0}, s)` along `P` has order `≥ s`, and the clause (1) of the input (`BMOanData.ord_lt`)
admits no such point. Along the push-forward the controlled and the weak transforms agree, the
sequence having order exactly `s`. -/
theorem cosupp_disjoint_pushforward_toSuccession (hT : BDClass s T)
    (P : FiniteSuccession (isClosedSubmanifold_transformS T s j).toAnalyticManifold)
    (hPge : P.IsOfOrderGe (restrictedTriple T s j hT).I s (restrictedTriple T s j hT).F.idealSheaf)
    (hPlt : ∀ y, (P.markedTransformSeq (restrictedTriple T s j hT).I s (Fin.last _)).ord y <
      (s : ℕ∞)) :
    Disjoint
      {x | (s : ℕ∞) ≤ ((P.pushforward (isClosedSubmanifold_transformS T s j)).weakTransformSeq
        (weakTransformI T s j) (Fin.last _)).ord x}
      ((P.pushforward (isClosedSubmanifold_transformS T s j)).strictTransformSeq
        (transformS T s j) (Fin.last _)) := by
  have hge : (P.pushforward (isClosedSubmanifold_transformS T s j)).IsOfOrderGe
      (weakTransformI T s j) s ((boundaryMinus T s j).append (transformS T s j)).idealSheaf :=
    FiniteSuccession.pushforward_isOfOrderGe_append (isClosedSubmanifold_transformS T s j) P
      (isDBalanced_weakTransformI T s j hT) (ord_weakTransformI_le T s j hT)
      (isSnc_boundaryMinus T s j) (hasSncWithProper_boundaryMinus T s j) hPge
  have hord : (P.pushforward (isClosedSubmanifold_transformS T s j)).IsOfOrder
      (weakTransformI T s j) ((boundaryMinus T s j).append (transformS T s j)).idealSheaf s :=
    FiniteSuccession.isOfOrder_of_isOfOrderGe_of_ord_le _ hge (ord_weakTransformI_le T s j hT)
  refine Set.disjoint_left.mpr fun x hx hxS => ?_
  rw [← hord.markedTransformSeq_eq_weakTransformSeq] at hx
  -- the push-forward has the length of `P` (`length_pushforward`, by `rfl`): re-index
  change (s : ℕ∞) ≤ ((P.pushforward (isClosedSubmanifold_transformS T s j)).markedTransformSeq
    (weakTransformI T s j) s (Fin.last P.length)).ord x at hx
  change x ∈ (P.pushforward (isClosedSubmanifold_transformS T s j)).strictTransformSeq
    (transformS T s j) (Fin.last P.length) at hxS
  rw [← P.range_pushforwardIncl (isClosedSubmanifold_transformS T s j)] at hxS
  obtain ⟨y, rfl⟩ := hxS
  have hmem : y ∈ {y : P.stage (Fin.last _) | (s : ℕ∞) ≤
      ((P.pushforward (isClosedSubmanifold_transformS T s j)).markedTransformSeq
        (weakTransformI T s j) s (Fin.last P.length)).ord
          (P.pushforwardIncl (isClosedSubmanifold_transformS T s j) (Fin.last _) y)} := hx
  rw [P.setOf_le_ord_markedTransformSeq_pushforward_inter_eq_iInter
    (isClosedSubmanifold_transformS T s j) hge hT.1.1 (Fin.last _)] at hmem
  have h0 := Set.mem_iInter₂.mp hmem 0 hT.1.1
  exact absurd (hPlt y) (not_lt.mpr h0)

/-- **Clause (1) of [Kol07, Lemma 102] for the core over a sequence**, given the identification of
the two push-forwards: if `L` has no empty centres, is a smooth blow-up sequence of order `≥ s`
for the restricted triple and its controlled transform at the last stage has order `< s`
everywhere, then the strict transform of `E^j` at the end of the core over `L` is disjoint from
`cosupp(I_r, s)`. The first blow-up carries the transform of `E^j` into
`S_0 = π_{-1}^{-1}(E^j)` (`strictTransform_subset_preimage`), the pushed-forward tail keeps it
inside `S_r` and away from the cosupport (`cosupp_disjoint_pushforward_toSuccession`), and when
the first blow-up is empty the clause is transported along its isomorphism. -/
theorem coreOfListOf_cosupp_disjoint_of_bridge (hbr : PushforwardBridge.{u} ψ₀) (hT : BDClass s T)
    (L : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      (isClosedSubmanifold_transformS T s j).toAnalyticManifold) (hLne : L.NoEmptyCenters)
    (hL : L.toSuccession.IsOfOrderGe (restrictedTriple T s j hT).I s
      (restrictedTriple T s j hT).F.idealSheaf)
    (hlt : ∀ y, (L.toSuccession.markedTransformSeq (restrictedTriple T s j hT).I s
      (Fin.last _)).ord y < (s : ℕ∞)) :
    Disjoint
      {x | (s : ℕ∞) ≤ ((coreOfListOf (BD.isClosedSubmanifold_Zminus1 T s j)
        (isClosedSubmanifold_transformS T s j) L).toSuccession.weakTransformSeq T.I
          (Fin.last _)).ord x}
      ((coreOfListOf (BD.isClosedSubmanifold_Zminus1 T s j) (isClosedSubmanifold_transformS T s j)
        L).toSuccession.strictTransformSeq (T.F.hyp j) (Fin.last _)) := by
  have hZ := BD.isClosedSubmanifold_Zminus1 T s j
  have hS := isClosedSubmanifold_transformS T s j
  have hPne := BlowUpSequence.noEmptyCenters_pushforward_of_bridge hbr hS _ hLne
  -- the tail's clause, at the level of sequences of centres (through the identification)
  have hQ : Disjoint
      {x | (s : ℕ∞) ≤ ((BlowUpSequence.pushforward hS L).toSuccession.weakTransformSeq
        (weakTransformI T s j) (Fin.last _)).ord x}
      ((BlowUpSequence.pushforward hS L).toSuccession.strictTransformSeq (transformS T s j)
        (Fin.last _)) := by
    rw [hbr hS _ hLne]
    exact cosupp_disjoint_pushforward_toSuccession T s j hT _ hL hlt
  unfold coreOfListOf
  by_cases hZ0 : BD.Zminus1 T.I s (T.F.hyp j) = ∅
  · rw [BlowUpSequence.eraseEmpty_cons_of_eq_empty _ _ hZ0,
      BlowUpSequence.eraseEmpty_of_noEmptyCenters _ hPne]
    apply BlowUpSequence.cosupp_disjoint_map_emptyBlowUp
    rw [weakTransformI_eq_comap_of_eq_empty T s j hZ0] at hQ
    exact hQ
  · rw [BlowUpSequence.eraseEmpty_cons_of_ne_empty _ _ hZ0,
      BlowUpSequence.eraseEmpty_of_noEmptyCenters _ hPne]
    refine FiniteSuccession.cosupp_disjoint_cons hZ _ T.I (T.F.hyp j) s ?_
    rw [weakTransform_eq_weakTransformI]
    exact hQ.mono_right (FiniteSuccession.strictTransformSeq_mono _
      (strictTransform_subset_preimage (piMinusOne T s j).contMDiff.continuous
        (T.isSnc.1 j).isClosed) _)

end BDan

section Core

variable [FiniteDimensional 𝕜 E] {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  {m : ℕ}

/-- **The clause (1) of [Kol07, Lemma 102]**, given the identification of the two push-forwards:
the birational transform of `E^j` at the end of `BD_{n,m,j}(M, 𝓘, E)` misses the cosupport
`{ord I_r ≥ m}` of the last weak transform of `𝓘`. The clause for the tuned triple
`(M, W_s(𝓘), E)` at the mark `s = tuningParam m` (`coreOfListOf_cosupp_disjoint_of_bridge` at the
value of the input functor) is carried back to `(𝓘, m)` by `ord_lt_of_tuned`, in the
contrapositive, along the sequence of order `m` (`BDan_isOfOrder_of_bridge`). -/
theorem BDan_cosupp_disjoint_of_bridge (hbr : PushforwardBridge.{u} ψ₀)
    (inp : BMOanData 𝕜 (n - 1) (tuningParam m)) (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BOClass m T) (j : T.F.ι) :
    Disjoint
      {x | (m : ℕ∞) ≤ ((BDan m inp T hT j).toSuccession.weakTransformSeq T.I (Fin.last _)).ord x}
      ((BDan m inp T hT j).toSuccession.strictTransformSeq (T.F.hyp j) (Fin.last _)) := by
  have hT' : BDan.BDClass (tuningParam m) (T.tuned m hT.1) :=
    ⟨AnalyticTriple.boClass_tuned hT, AnalyticTriple.isDBalanced_tuned hT⟩
  have hge := (BDan_isOfOrder_of_bridge hbr inp T hT j).isOfOrderGe
  refine Set.disjoint_left.mpr fun x hx hxH => ?_
  have hx' : (tuningParam m : ℕ∞) ≤ ((BDan m inp T hT j).toSuccession.weakTransformSeq
      (T.tuned m hT.1).I (Fin.last _)).ord x :=
    not_lt.mp fun hlt => not_lt.mpr hx (AnalyticTriple.ord_lt_of_tuned T hT _ hge x hlt)
  exact Set.disjoint_left.mp
    (BDan.coreOfListOf_cosupp_disjoint_of_bridge (T.tuned m hT.1) (tuningParam m) j hbr hT' _
      (inp.functor.noEmptyCenters _ _) (inp.isOfOrderGe _ _) (inp.ord_lt _ _)) hx' hxH

end Core

end Hironaka.Manifold

end
