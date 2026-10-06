/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.FamilyClosedEmbedding
public import Hironaka.Resolution.Analytic.Functor.ChainClosedEmbeddingCover
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.ChainClosedEmbeddingDegenerate
import Hironaka.Resolution.Analytic.OrderReduction.FamilyIndependence
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepBComm
import Hironaka.Resolution.Analytic.Restrict.FlagPushforward
import Hironaka.Resolution.Analytic.Submanifold.FlagIdeal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The chaining of the closed-embedding commutation, III: the chaining lemma

[Kol07, 108] reduces the commutation of the order-reduction functors with closed embeddings to
the hypersurface case along a flag `Y = Y₀ ⊂ Y₁ ⊂ ⋯ ⊂ Y_c = X`, the question being local. This
module proves the step of that reduction, (E1): if `B₂` commutes with closed embeddings of
codimension `s` through `B₁` and `B₁` with hypersurfaces through `B₀`, then `B₂` commutes with
closed embeddings of codimension `s + 1` through `B₀`; and the induction it drives, (E3), for a
tower of functors at the standard models. The sources say only that the question is local; the
route through a flag cover is spelled out here:

* (E-a), (E-b) `IsClosedSubmanifold.diffeomorphRestrict`,
  `BlowUpSequence.pushforward_pullback_diffeomorph`: an analytic isomorphism of the ambient
  manifolds carrying one closed submanifold onto another restricts to an isomorphism of the bundled
  submanifolds, and push-forward ([Kol07, Definition 30, 30.3]) commutes with the pull-back along
  it (`pushforwardAux_pullback` at the trivial stages);
* (E-c) `BlowUpSequence.pushforwardRestrict_pushforwardRestrict_of_flag`: the per-open form of
  `pushforward_pushforward_of_flag` (`Hironaka.Resolution.Analytic.Restrict.FlagPushforward`):
  pushing a list forward from `S ∩ U` to `Y ∩ U` and then to `U` is pushing it forward from
  `S ∩ U` to `U`, the list read on the `S ⊂ Y` structure through the identification `e`;
* the flag case `AnalyticFamilyFunctor.commutesWithClosedEmbeddings_flag_case`: on a manifold
  carrying a global flag `S ⊂ Y ⊂ M`, the codimension-`s` clause at `Y` (C), the hypersurface
  clause of the middle functor at `S ⊂ Y` (D) and (E-c) give the per-open identity at `S`; the
  ideals are handled by `Hironaka.Resolution.Analytic.Submanifold.FlagIdeal`;
* (E1) `AnalyticFamilyFunctor.commutesWithClosedEmbeddingsOfEmptyDivisorFam_chain`: a relatively
  compact open `U` has a flag cover (`FlagCover`,
  `Hironaka.Resolution.Analytic.Functor.ChainClosedEmbeddingCover`); on its coproduct `Σ` the
  preimage of `S` sits in a global flag, pull-back along the surjective local isomorphism
  `coverMap` is injective ([Kol07, Proposition 37]), both sides of the identity pull back to values
  of the functors on the pulled-back triples (`CommutesWithLocalIsos`;
  `pushforwardRestrict_pullback_restrictMap` for the right side), and the flag case on `Σ`
  identifies them;
* (E3) `AnalyticFamilyFunctor.commutesWithClosedEmbeddingsOfEmptyDivisorFam_tower`: induction on
  the codimension with (E1) at the bottom of the flag and the degenerate case of
  `Hironaka.Resolution.Analytic.Functor.ChainClosedEmbeddingDegenerate` when `n ≤ s`.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Manifold

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### (E-a) an ambient analytic isomorphism carrying one closed submanifold onto another induces
an analytic isomorphism of the bundled submanifolds -/

section Induced

variable {A B : AnalyticManifold.{u} 𝕜 E} {SA : Set A} {SB : Set B} {c : ℕ}

/-- `G` maps `SA = G⁻¹(SB)` into `SB`. -/
theorem IsClosedSubmanifold.mapsTo_of_preimage_eq (G : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) A B ω)
    (h : SA = ⇑G ⁻¹' SB) : ∀ x ∈ SA, G x ∈ SB := fun x hx => by
  have hx' : x ∈ ⇑G ⁻¹' SB := h ▸ hx
  exact hx'

/-- `G.symm` maps `SB` into `SA = G⁻¹(SB)`. -/
theorem IsClosedSubmanifold.symm_mapsTo_of_preimage_eq (G : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) A B ω)
    (h : SA = ⇑G ⁻¹' SB) : ∀ y ∈ SB, G.symm y ∈ SA := fun y hy => by
  rw [h]
  change G (G.symm y) ∈ SB
  rw [G.apply_symm_apply]
  exact hy

/-- The restriction of `G` to the bundled submanifolds. -/
def IsClosedSubmanifold.restrictMapOfPreimage (G : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) A B ω)
    (hA : IsClosedSubmanifold ψ SA c) (hB : IsClosedSubmanifold ψ SB c) (h : SA = ⇑G ⁻¹' SB) :
    AnalyticMap hA.toAnalyticManifold hB.toAnalyticManifold :=
  hA.restrictMap hB G G.contMDiff (IsClosedSubmanifold.mapsTo_of_preimage_eq G h)

/-- The restriction of `G.symm` to the bundled submanifolds. -/
def IsClosedSubmanifold.restrictMapOfPreimageSymm (G : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) A B ω)
    (hA : IsClosedSubmanifold ψ SA c) (hB : IsClosedSubmanifold ψ SB c) (h : SA = ⇑G ⁻¹' SB) :
    AnalyticMap hB.toAnalyticManifold hA.toAnalyticManifold :=
  hB.restrictMap hA G.symm G.symm.contMDiff (IsClosedSubmanifold.symm_mapsTo_of_preimage_eq G h)

/-- An analytic isomorphism `G : A ≃ B` with `SA = G⁻¹(SB)` restricts to an analytic isomorphism
of the bundled closed submanifolds (both directions `IsClosedSubmanifold.restrictMap`s, inverse to
each other on the carriers). -/
def IsClosedSubmanifold.diffeomorphRestrict (G : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) A B ω)
    (hA : IsClosedSubmanifold ψ SA c) (hB : IsClosedSubmanifold ψ SB c) (h : SA = ⇑G ⁻¹' SB) :
    Diffeomorph 𝓘(𝕜, Fin (n - c) → 𝕜) 𝓘(𝕜, Fin (n - c) → 𝕜) hA.toAnalyticManifold
      hB.toAnalyticManifold ω where
  toFun := IsClosedSubmanifold.restrictMapOfPreimage G hA hB h
  invFun := IsClosedSubmanifold.restrictMapOfPreimageSymm G hA hB h
  left_inv p := Subtype.ext (G.symm_apply_apply p.1)
  right_inv q := Subtype.ext (G.apply_symm_apply q.1)
  contMDiff_toFun := (IsClosedSubmanifold.restrictMapOfPreimage G hA hB h).contMDiff
  contMDiff_invFun := (IsClosedSubmanifold.restrictMapOfPreimageSymm G hA hB h).contMDiff

/-- The restricted isomorphism is `G` on the points. -/
theorem IsClosedSubmanifold.diffeomorphRestrict_apply (G : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) A B ω)
    (hA : IsClosedSubmanifold ψ SA c) (hB : IsClosedSubmanifold ψ SB c) (h : SA = ⇑G ⁻¹' SB)
    (p : hA.toAnalyticManifold) :
    (hB.inclusionMap (hA.diffeomorphRestrict G hB h p) : B) = G (hA.inclusionMap p) := rfl

/-! ### (E-b) the square: push-forward against pull-back along an ambient isomorphism -/

/-- [Kol07, Definition 30, 30.3] transported along an analytic isomorphism of the ambient
manifolds (the square lemma `pushforwardAux_pullback` at the trivial stages): pulling back the
push-forward along `G` is pushing forward the pull-back along the induced isomorphism of the
bundled submanifolds. -/
theorem _root_.AnalyticManifold.BlowUpSequence.pushforward_pullback_diffeomorph
    (G : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) A B ω)
    (hA : IsClosedSubmanifold ψ SA c) (hB : IsClosedSubmanifold ψ SB c) (h : SA = ⇑G ⁻¹' SB)
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin
        (n - c) → 𝕜)) hB.toAnalyticManifold) :
    (L.pushforward hB).pullback (⟨⇑G, G.contMDiff⟩ : AnalyticMap A B) G.isLocalDiffeomorph =
      (L.pullback ⟨⇑(hA.diffeomorphRestrict G hB h), (hA.diffeomorphRestrict G hB h).contMDiff⟩
        (hA.diffeomorphRestrict G hB h).isLocalDiffeomorph).pushforward hA := by
  have hst : PushforwardStage.IsPullbackStage
      (⟨B, SB, hB, Diffeomorph.refl _ _ _⟩ : PushforwardStage ψ c hB.toAnalyticManifold)
      (⟨A, SA, hA, Diffeomorph.refl _ _ _⟩ : PushforwardStage ψ c hA.toAnalyticManifold)
      (⟨⇑G, G.contMDiff⟩ : AnalyticMap A B)
      ⟨⇑(hA.diffeomorphRestrict G hB h), (hA.diffeomorphRestrict G hB h).contMDiff⟩ :=
    { isLocalDiffeomorph := G.isLocalDiffeomorph
      sub_eq := h
      square := fun q => rfl }
  exact PushforwardStage.pushforwardAux_pullback _ _ _ _
    (hA.diffeomorphRestrict G hB h).isLocalDiffeomorph hst L

/-- Three pull-backs against two: two chains of local analytic isomorphisms with the same
composite pull a list back to the same list (`pullback_comp` twice each way, `pullback_congr`
in the middle). -/
theorem _root_.AnalyticManifold.BlowUpSequence.pullback_pullback_pullback_eq_pullback_pullback
    {M N₁ N₂ N₃ P : AnalyticManifold.{u} 𝕜 E} (L : AnalyticManifold.BlowUpSequence ψ M)
    (f₁ : AnalyticMap N₁ M) (hf₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f₁)
    (f₂ : AnalyticMap N₂ N₁) (hf₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f₂)
    (f₃ : AnalyticMap P N₂) (hf₃ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f₃)
    (g₁ : AnalyticMap N₃ M) (hg₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g₁)
    (g₂ : AnalyticMap P N₃) (hg₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g₂)
    (h : ∀ q, (f₁.comp (f₂.comp f₃)) q = (g₁.comp g₂) q) :
    ((L.pullback f₁ hf₁).pullback f₂ hf₂).pullback f₃ hf₃ =
      (L.pullback g₁ hg₁).pullback g₂ hg₂ :=
  calc ((L.pullback f₁ hf₁).pullback f₂ hf₂).pullback f₃ hf₃
      = (L.pullback f₁ hf₁).pullback (f₂.comp f₃)
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hf₂ hf₃) :=
        AnalyticManifold.BlowUpSequence.pullback_comp _ f₂ hf₂ f₃ hf₃
    _ = L.pullback (f₁.comp (f₂.comp f₃))
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hf₁
              (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hf₂ hf₃)) :=
        AnalyticManifold.BlowUpSequence.pullback_comp _ f₁ hf₁ (f₂.comp f₃) _
    _ = L.pullback (g₁.comp g₂) (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hg₁ hg₂) :=
        AnalyticManifold.BlowUpSequence.pullback_congr L (ContMDiffMap.ext h) _ _
    _ = (L.pullback g₁ hg₁).pullback g₂ hg₂ :=
        (AnalyticManifold.BlowUpSequence.pullback_comp _ g₁ hg₁ g₂ hg₂).symm

end Induced

/-! ### (E-c) the composition of the per-open push-forwards along the flag -/

section Flag

variable {M : AnalyticManifold.{u} 𝕜 E} {Y S : Set M} {s : ℕ}
  (hY : IsClosedSubmanifold ψ Y s) (hS : IsClosedSubmanifold ψ S (s + 1)) (hsub : S ⊆ Y)
  (hSY : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
    (⇑hY.inclusionMap ⁻¹' S) 1)
  (e : Diffeomorph 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜)
    (hSY.toAnalyticManifold : AnalyticManifold.{u} 𝕜 (Fin (n - (s + 1)) → 𝕜))
    hS.toAnalyticManifold ω)
  (he : ∀ x : hSY.toAnalyticManifold.carrier,
    (hS.inclusionMap (e x) : M) = hY.inclusionMap (hSY.inclusionMap x))
  (U : Opens M)

include he in
/-- The identification of the two bundled structures on `S` maps the trace of `U` on `S ⊂ Y` into
the trace of `U` on `S`. -/
theorem IsClosedSubmanifold.image_flagDiffeomorph_preimageOpens_subset :
    (⇑e : hSY.toAnalyticManifold → hS.toAnalyticManifold) ''
        (hSY.preimageOpens (hY.preimageOpens U) : Set hSY.toAnalyticManifold) ⊆
      hS.preimageOpens U := by
  rintro _ ⟨x, hx, rfl⟩
  change (hS.inclusionMap (e x) : M) ∈ U
  rw [he x]
  exact hx

include he in
/-- The identification of the two bundled structures on `S` maps the trace of `U` on `S ⊂ Y` ONTO
the trace of `U` on `S`. -/
theorem IsClosedSubmanifold.image_flagDiffeomorph_preimageOpens_eq :
    (⇑e : hSY.toAnalyticManifold → hS.toAnalyticManifold) ''
        (hSY.preimageOpens (hY.preimageOpens U) : Set hSY.toAnalyticManifold) =
      hS.preimageOpens U := by
  refine subset_antisymm
    (IsClosedSubmanifold.image_flagDiffeomorph_preimageOpens_subset hY hS hSY e he U) ?_
  intro y hy
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  change (hY.inclusionMap (hSY.inclusionMap (e.symm y)) : M) ∈ U
  rw [← he (e.symm y), e.apply_symm_apply]
  exact hy

include hS hsub in
/-- The trace of `S` on the open `U` is a hypersurface of the trace of `Y` (the flag restricted to
`U`; `preimage_val_of_subset` at codimension `s + 1 - s = 1`). -/
theorem IsClosedSubmanifold.restrictOpen_flag :
    IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      (⇑(hY.restrictOpen U).inclusionMap ⁻¹' (⇑(M.inclusion U) ⁻¹' S)) 1 := by
  have h := (hY.restrictOpen U).preimage_val_of_subset (hS.restrictOpen U) fun q hq => hsub hq
  rwa [Nat.add_sub_cancel_left] at h

/-- The trace of `S ∩ U` in the restricted flag is the preimage, under the bridge of `Y`, of the
trace of `S` in `Y ∩ U_Y` (a set-level identity of the two bundled hypersurfaces). -/
theorem IsClosedSubmanifold.flag_trace_eq :
    (⇑(hY.restrictOpen U).inclusionMap ⁻¹' (⇑(M.inclusion U) ⁻¹' S)) =
      ⇑(hY.restrictBundleDiffeomorph U).symm ⁻¹'
        (⇑((hY.toAnalyticManifold).inclusion (hY.preimageOpens U)) ⁻¹'
          (⇑hY.inclusionMap ⁻¹' S)) :=
  Set.ext fun _ => Iff.rfl

/-- `f₁`: the identification `e` restricted to the traces of `U`. -/
def IsClosedSubmanifold.flagMapS :
    AnalyticMap ((hSY.toAnalyticManifold : AnalyticManifold.{u} 𝕜 (Fin (n - (s + 1)) → 𝕜)).restrict
        (hSY.preimageOpens (hY.preimageOpens U)))
      ((hS.toAnalyticManifold).restrict (hS.preimageOpens U)) :=
  AnalyticMap.restrictMap (⟨⇑e, e.contMDiff⟩ : AnalyticMap
      (hSY.toAnalyticManifold : AnalyticManifold.{u} 𝕜 (Fin (n - (s + 1)) → 𝕜))
      hS.toAnalyticManifold) _ _
    (IsClosedSubmanifold.image_flagDiffeomorph_preimageOpens_subset hY hS hSY e he U)

include he in
/-- `f₁` is a local analytic isomorphism (`e` restricted to opens). -/
theorem IsClosedSubmanifold.isLocalDiffeomorph_flagMapS :
    IsLocalDiffeomorph 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) ω
      (IsClosedSubmanifold.flagMapS hY hS hSY e he U) :=
  AnalyticMap.isLocalDiffeomorph_restrictMap e.isLocalDiffeomorph _ _ _

/-- `f₂`: the bridge of `S ⊂ Y` at `U_Y`, inverted. -/
def IsClosedSubmanifold.flagBridgeSY :
    AnalyticMap ((hSY.restrictOpen (hY.preimageOpens U)).toAnalyticManifold)
      ((hSY.toAnalyticManifold).restrict (hSY.preimageOpens (hY.preimageOpens U))) :=
  ⟨⇑(hSY.restrictBundleDiffeomorph (hY.preimageOpens U)).symm,
    (hSY.restrictBundleDiffeomorph (hY.preimageOpens U)).symm.contMDiff⟩

/-- `f₃`: the isomorphism of the two bundled hypersurfaces `S ∩ U` induced by the bridge of `Y`. -/
def IsClosedSubmanifold.flagBridgeHyp :
    AnalyticMap ((IsClosedSubmanifold.restrictOpen_flag hY hS hsub U).toAnalyticManifold)
      ((hSY.restrictOpen (hY.preimageOpens U)).toAnalyticManifold) :=
  ⟨⇑((IsClosedSubmanifold.restrictOpen_flag hY hS hsub U).diffeomorphRestrict
      (hY.restrictBundleDiffeomorph U).symm (hSY.restrictOpen (hY.preimageOpens U))
      (IsClosedSubmanifold.flag_trace_eq hY U)),
    ((IsClosedSubmanifold.restrictOpen_flag hY hS hsub U).diffeomorphRestrict
      (hY.restrictBundleDiffeomorph U).symm (hSY.restrictOpen (hY.preimageOpens U))
      (IsClosedSubmanifold.flag_trace_eq hY U)).contMDiff⟩

/-- `g₁`: the bridge of `S` at `U`, inverted. -/
def IsClosedSubmanifold.flagBridgeS :
    AnalyticMap ((hS.restrictOpen U).toAnalyticManifold)
      ((hS.toAnalyticManifold).restrict (hS.preimageOpens U)) :=
  ⟨⇑(hS.restrictBundleDiffeomorph U).symm, (hS.restrictBundleDiffeomorph U).symm.contMDiff⟩

/-- `f₂` is a local analytic isomorphism (an inverted bridge). -/
theorem IsClosedSubmanifold.isLocalDiffeomorph_flagBridgeSY :
    IsLocalDiffeomorph 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) ω
      (IsClosedSubmanifold.flagBridgeSY hY hSY U) :=
  (hSY.restrictBundleDiffeomorph (hY.preimageOpens U)).symm.isLocalDiffeomorph

include hS hsub in
/-- `f₃` is a local analytic isomorphism (`diffeomorphRestrict`). -/
theorem IsClosedSubmanifold.isLocalDiffeomorph_flagBridgeHyp :
    IsLocalDiffeomorph 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) ω
      (IsClosedSubmanifold.flagBridgeHyp hY hS hsub hSY U) :=
  ((IsClosedSubmanifold.restrictOpen_flag hY hS hsub U).diffeomorphRestrict
    (hY.restrictBundleDiffeomorph U).symm (hSY.restrictOpen (hY.preimageOpens U))
    (IsClosedSubmanifold.flag_trace_eq hY U)).isLocalDiffeomorph

/-- `g₁` is a local analytic isomorphism (an inverted bridge). -/
theorem IsClosedSubmanifold.isLocalDiffeomorph_flagBridgeS :
    IsLocalDiffeomorph 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) ω
      (IsClosedSubmanifold.flagBridgeS hS U) :=
  (hS.restrictBundleDiffeomorph U).symm.isLocalDiffeomorph

include hsub he in
/-- **(E), the restricted form of `pushforward_pushforward_of_flag`** ([Kol07, Definition 30, 30.3]
twice): pushing a list forward from the hypersurface `S ∩ U` of `Y ∩ U` to `Y ∩ U` and then to `U`
is pushing it forward from `S ∩ U` to `U` — the list read on the `S ⊂ Y` structure through `e`.
From the unrestricted lemma on
`M.restrict U`, the three `pushforwardRestrict`s unfolded by
`pushforwardRestrictOf_eq`, the middle push-forward transported along the bridge of `Y` by
`pushforward_pullback_diffeomorph`, and the pull-backs composed (`pullback_comp`, `pullback_congr`:
all the maps are the identity on the points of `S ∩ U`). -/
theorem _root_.AnalyticManifold.BlowUpSequence.pushforwardRestrict_pushforwardRestrict_of_flag
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - (s + 1)) → 𝕜))
      ((hS.toAnalyticManifold).restrict (hS.preimageOpens U))) :
    AnalyticManifold.BlowUpSequence.pushforwardRestrict hY U
        (AnalyticManifold.BlowUpSequence.pushforwardRestrict hSY (hY.preimageOpens U)
      (L.pullback (IsClosedSubmanifold.flagMapS hY hS hSY e he U)
        (IsClosedSubmanifold.isLocalDiffeomorph_flagMapS hY hS hSY e he U))) =
      AnalyticManifold.BlowUpSequence.pushforwardRestrict hS U L := by
  -- the flag restricted to `U`, with its own identification of the two structures on `S ∩ U`
  have hsub_U : (⇑(M.inclusion U) ⁻¹' S) ⊆ (⇑(M.inclusion U) ⁻¹' Y) := fun q hq => hsub hq
  obtain ⟨eU, heU⟩ := IsClosedSubmanifold.exists_diffeomorph_toAnalyticManifold_of_flag
    (hY.restrictOpen U) (hS.restrictOpen U) hsub_U
    (IsClosedSubmanifold.restrictOpen_flag hY hS hsub U)
  -- the three per-open push-forwards as ordinary push-forwards
  rw [AnalyticManifold.BlowUpSequence.pushforwardRestrict_eq hS U,
      AnalyticManifold.BlowUpSequence.pushforwardRestrict_eq hY U,
    AnalyticManifold.BlowUpSequence.pushforwardRestrict_eq hSY (hY.preimageOpens U)]
  -- the middle push-forward transported along the bridge of `Y`
  rw [AnalyticManifold.BlowUpSequence.pushforward_pullback_diffeomorph
      (hY.restrictBundleDiffeomorph U).symm
    (IsClosedSubmanifold.restrictOpen_flag hY hS hsub U) (hSY.restrictOpen (hY.preimageOpens U))
    (IsClosedSubmanifold.flag_trace_eq hY U)]
  -- the unrestricted `pushforward_pushforward_of_flag` on `M.restrict U`
  rw [← AnalyticManifold.BlowUpSequence.pushforward_pushforward_of_flag (hY.restrictOpen U)
      (hS.restrictOpen U)
    (IsClosedSubmanifold.restrictOpen_flag hY hS hsub U) eU heU
    (L.pullback ⟨(hS.restrictBundleDiffeomorph U).symm,
        (hS.restrictBundleDiffeomorph U).symm.contMDiff⟩
      (hS.restrictBundleDiffeomorph U).symm.isLocalDiffeomorph)]
  -- the two transported lists agree: all the maps are the identity on the points of `S ∩ U`
  congr 2
  have hmaps : ∀ q, ((IsClosedSubmanifold.flagMapS hY hS hSY e he U).comp
      ((IsClosedSubmanifold.flagBridgeSY hY hSY U).comp
        (IsClosedSubmanifold.flagBridgeHyp hY hS hsub hSY U))) q =
      ((IsClosedSubmanifold.flagBridgeS hS U).comp
        (⟨⇑eU, eU.contMDiff⟩ : AnalyticMap
          ((IsClosedSubmanifold.restrictOpen_flag hY hS hsub U).toAnalyticManifold :
            AnalyticManifold.{u} 𝕜 (Fin (n - (s + 1)) → 𝕜))
          (hS.restrictOpen U).toAnalyticManifold)) q := by
    intro q
    refine Subtype.ext (Subtype.ext ?_)
    change (hS.inclusionMap (e _) : M) = ((hS.restrictOpen U).inclusionMap (eU q) : M.restrict U).1
    rw [he, heU]
    rfl
  exact AnalyticManifold.BlowUpSequence.pullback_pullback_pullback_eq_pullback_pullback L
    (IsClosedSubmanifold.flagMapS hY hS hSY e he U)
    (IsClosedSubmanifold.isLocalDiffeomorph_flagMapS hY hS hSY e he U)
    (IsClosedSubmanifold.flagBridgeSY hY hSY U)
    (IsClosedSubmanifold.isLocalDiffeomorph_flagBridgeSY hY hSY U)
    (IsClosedSubmanifold.flagBridgeHyp hY hS hsub hSY U)
    (IsClosedSubmanifold.isLocalDiffeomorph_flagBridgeHyp hY hS hsub hSY U)
    (IsClosedSubmanifold.flagBridgeS hS U) (IsClosedSubmanifold.isLocalDiffeomorph_flagBridgeS hS U)
    (⟨⇑eU, eU.contMDiff⟩ : AnalyticMap
      ((IsClosedSubmanifold.restrictOpen_flag hY hS hsub U).toAnalyticManifold :
        AnalyticManifold.{u} 𝕜 (Fin (n - (s + 1)) → 𝕜))
      (hS.restrictOpen U).toAnalyticManifold)
    eU.isLocalDiffeomorph hmaps

end Flag

/-! ### The pull-back of an empty-divisor triple -/

/-- The pull-back of an empty-divisor triple along a local analytic isomorphism is the
empty-divisor triple of the pulled-back ideal (`HypersurfaceFamily.empty_comap`). -/
theorem AnalyticTriple.pullback_emptyDivisor [FiniteDimensional 𝕜 E]
    {M N : AnalyticManifold.{u} 𝕜 E} (I : AnalyticManifold.IdealSheaf M)
        (hI : I.IsNonzeroEverywhere)
    (g : AnalyticMap N M) (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) :
    (⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩ :
        AnalyticTriple ψ M).pullback g hg =
      ⟨I.pullback g g.contMDiff, IdealSheaf.isNonzeroEverywhere_comap hI g hg,
        HypersurfaceFamily.empty N, HypersurfaceFamily.isSnc_empty⟩ :=
  AnalyticTriple.ext' rfl (HypersurfaceFamily.empty_comap _)

end Manifold

namespace Hironaka.Manifold.FlagCover

open Hironaka.Manifold
open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The flag cover: the descent map restricted to the bundled preimage of `S` -/

variable {M : AnalyticManifold.{u} 𝕜 E} {S : Set M} {s : ℕ} {hS : IsClosedSubmanifold ψ S (s + 1)}
  {U : Opens M} (C : FlagCover hS U)

/-- The descent map restricted to the bundled preimage of `S`
(`IsClosedSubmanifold.restrictMap`). -/
def descS : AnalyticMap C.isClosedSubmanifold_preimage.toAnalyticManifold hS.toAnalyticManifold :=
  C.isClosedSubmanifold_preimage.restrictMap hS C.desc C.desc.contMDiff fun _ hx => hx

/-- The restricted descent map is a local analytic isomorphism (`isLocalDiffeomorph_restrictMap` at
any codimension). -/
theorem isLocalDiffeomorph_descS :
    IsLocalDiffeomorph 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) 𝓘(𝕜, Fin (n - (s + 1)) → 𝕜) ω C.descS :=
  IsClosedSubmanifold.isLocalDiffeomorph_restrictMap C.desc C.isLocalDiffeomorph_desc _

/-- The restricted descent map carries the trace of the cover's opens on the preimage of `S` ONTO
the trace of `U` on `S` (the cover's opens map onto `U`). -/
theorem image_descS_preimageOpens_eq :
    ⇑C.descS '' (C.isClosedSubmanifold_preimage.preimageOpens C.opens :
        Set C.isClosedSubmanifold_preimage.toAnalyticManifold) =
      (hS.preimageOpens U : Set hS.toAnalyticManifold) := by
  refine subset_antisymm
    (hS.image_restrictMap_preimageOpens_subset C.desc _ C.image_opens_subset) ?_
  intro y hy
  change (hS.inclusionMap y : M) ∈ (U : Set M) at hy
  rw [← C.image_opens_eq] at hy
  obtain ⟨p, hp, hpy⟩ := hy
  have hpS : p ∈ ⇑C.desc ⁻¹' S := by
    change C.desc p ∈ S
    rw [hpy]
    exact y.2
  exact ⟨⟨p, hpS⟩, hp, Subtype.ext hpy⟩

end Hironaka.Manifold.FlagCover

namespace Manifold

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The flag case of the chaining lemma: (C) + (D) + (E) -/

section FlagCase

variable {s : ℕ}
  {Dom₂ : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ M → Prop}
  (B₂ : AnalyticFamilyFunctor ψ Dom₂)
  {Dom₁ : ∀ {M₁ : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)},
    AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) M₁ → Prop}
  (B₁ : AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Dom₁)
  {Dom₀ : ∀ {M₀ : AnalyticManifold.{u} 𝕜 (Fin (n - s - 1) → 𝕜)},
    AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s - 1) → 𝕜)) M₀ → Prop}
  (B₀ : AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s - 1) → 𝕜)) Dom₀)

/-- **The flag case of (E1)** ([Kol07, 108]): on a manifold
carrying a global flag `S ⊂ Y ⊂ M` (`Y` of codimension `s`, `S` a hypersurface of `Y`), the
per-open identity of the predicate at `S` follows from the codimension-`s` clause at `Y` (C), the
codimension-one clause of the middle functor at `S ⊂ Y` (D) and the composition of the two
push-forwards (E). -/
theorem _root_.Hironaka.Manifold.AnalyticFamilyFunctor.commutesWithClosedEmbeddings_flag_case
    (hDom₁ : ∀ {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} (hY : IsClosedSubmanifold ψ Y s)
      (I : AnalyticManifold.IdealSheaf M) (hI : I.IsNonzeroEverywhere)
      (hJ : (I.pullback hY.inclusionMap hY.inclusionMap.contMDiff).IsNonzeroEverywhere),
      hY.idealSheaf ≤ I →
      Dom₂ ⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩ →
      Dom₁ ⟨I.pullback hY.inclusionMap hY.inclusionMap.contMDiff, hJ, HypersurfaceFamily.empty _,
        HypersurfaceFamily.isSnc_empty⟩)
    (hB₀ : B₀.CommutesWithLocalIsos)
    (hDom₀ : ∀ {M N : AnalyticManifold.{u} 𝕜 (Fin (n - s - 1) → 𝕜)}
      (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s - 1) → 𝕜)) M)
      (g : AnalyticMap N M)
      (hg : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - s - 1) → 𝕜) 𝓘(𝕜, Fin (n - s - 1) → 𝕜) ω g),
      Dom₀ T → Dom₀ (T.pullback g hg))
    (hs : B₂.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s) B₁)
    (h1 : B₁.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := 1) B₀)
    {M : AnalyticManifold.{u} 𝕜 E} {Y S : Set M} (hY : IsClosedSubmanifold ψ Y s)
    (hS : IsClosedSubmanifold ψ S (s + 1)) (hsub : S ⊆ Y)
    (hSY : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      (⇑hY.inclusionMap ⁻¹' S) 1)
    (I : AnalyticManifold.IdealSheaf M) (hI : I.IsNonzeroEverywhere)
    (J : AnalyticManifold.IdealSheaf hS.toAnalyticManifold) (hJ : J.IsNonzeroEverywhere)
    (hle : hS.idealSheaf ≤ I) (hJI : J = I.pullback hS.inclusionMap hS.inclusionMap.contMDiff)
    (hT : Dom₂ ⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩)
    (hT' : Dom₀ ⟨J, hJ, HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩)
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (B₂.fam _ hT).seqOn U hU =
      AnalyticManifold.BlowUpSequence.pushforwardRestrict hS U ((B₀.fam _ hT').seqOn
          (hS.preimageOpens U)
        (hS.isCompact_closure_preimageOpens U hU)) := by
  have _hfd := finiteDimensional_of_chartIso ψ
  -- (C) the codimension-`s` clause at `Y`
  have hleY : hY.idealSheaf ≤ I := (hY.idealSheaf_le_of_subset hS hsub).trans hle
  have hJS : (I.pullback hS.inclusionMap hS.inclusionMap.contMDiff).IsNonzeroEverywhere := by
    rw [← hJI]
    exact hJ
  have hJ₁ := IdealSheaf.isNonzeroEverywhere_pullback_inclusionMap_of_le hY hS hsub I hle hJS
  have hT₁ := hDom₁ hY I hI hJ₁ hleY hT
  have hC := hs hY I hI _ hJ₁ hleY rfl hT hT₁ U hU
  -- (D) the codimension-one clause of `B₁` at `S ⊂ Y`
  obtain ⟨e, he⟩ :=
    IsClosedSubmanifold.exists_diffeomorph_toAnalyticManifold_of_flag hY hS hsub hSY
  have hleSY : hSY.idealSheaf ≤ I.pullback hY.inclusionMap hY.inclusionMap.contMDiff := by
    rw [← hY.pullback_idealSheaf_inclusionMap hS hsub hSY]
    exact IdealSheaf.pullback_le_pullback _ _ hle
  -- the ideal on the bundled `S ⊂ Y` is `J` transported through `e`
  have hJ₂eq : (I.pullback hY.inclusionMap hY.inclusionMap.contMDiff).pullback hSY.inclusionMap
      hSY.inclusionMap.contMDiff = J.pullback (⟨⇑e, e.contMDiff⟩ : AnalyticMap
        (hSY.toAnalyticManifold : AnalyticManifold.{u} 𝕜 (Fin (n - (s + 1)) → 𝕜))
        hS.toAnalyticManifold) (ContMDiffMap.contMDiff _) := by
    rw [hJI, IdealSheaf.pullback_pullback]
    change _ = (I.pullback hS.inclusionMap hS.inclusionMap.contMDiff).pullback ⇑e e.contMDiff
    rw [IdealSheaf.pullback_pullback]
    exact IdealSheaf.pullback_congr I _ _ (funext fun x => (he x).symm)
  have hJ₂ : ((I.pullback hY.inclusionMap hY.inclusionMap.contMDiff).pullback hSY.inclusionMap
      hSY.inclusionMap.contMDiff).IsNonzeroEverywhere := by
    rw [hJ₂eq]
    exact IdealSheaf.isNonzeroEverywhere_comap hJ _ e.isLocalDiffeomorph
  have hTripleEq : ((⟨J, hJ, HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩ :
      AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s - 1) → 𝕜))
        hS.toAnalyticManifold).pullback ⟨⇑e, e.contMDiff⟩ e.isLocalDiffeomorph) =
      ⟨(I.pullback hY.inclusionMap hY.inclusionMap.contMDiff).pullback hSY.inclusionMap
        hSY.inclusionMap.contMDiff, hJ₂, HypersurfaceFamily.empty _,
        HypersurfaceFamily.isSnc_empty⟩ :=
    AnalyticTriple.ext' hJ₂eq.symm (HypersurfaceFamily.empty_comap _)
  have hT₂ : Dom₀ (⟨(I.pullback hY.inclusionMap hY.inclusionMap.contMDiff).pullback
      hSY.inclusionMap hSY.inclusionMap.contMDiff, hJ₂, HypersurfaceFamily.empty _,
      HypersurfaceFamily.isSnc_empty⟩ : AnalyticTriple _ hSY.toAnalyticManifold) := by
    rw [← hTripleEq]
    exact hDom₀ _ _ e.isLocalDiffeomorph hT'
  have hD := h1 hSY _ hJ₁ _ hJ₂ hleSY rfl hT₁ hT₂ (hY.preimageOpens U)
    (hY.isCompact_closure_preimageOpens U hU)
  -- the bottom value on `S ⊂ Y` is the bottom value on `S` pulled back through `e`
  have hpb : (⟨(I.pullback hY.inclusionMap hY.inclusionMap.contMDiff).pullback hSY.inclusionMap
      hSY.inclusionMap.contMDiff, hJ₂, HypersurfaceFamily.empty _,
      HypersurfaceFamily.isSnc_empty⟩ : AnalyticTriple
        (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s - 1) → 𝕜)) hSY.toAnalyticManifold).IsPullbackOf
      (⟨J, hJ, HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩ : AnalyticTriple
        (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s - 1) → 𝕜)) hS.toAnalyticManifold)
      (⟨⇑e, e.contMDiff⟩ : AnalyticMap
        (hSY.toAnalyticManifold : AnalyticManifold.{u} 𝕜 (Fin (n - (s + 1)) → 𝕜))
        hS.toAnalyticManifold) :=
    ⟨hJ₂eq, (HypersurfaceFamily.empty_comap _).symm⟩
  have himg := IsClosedSubmanifold.image_flagDiffeomorph_preimageOpens_eq hY hS hSY e he U
  have hB := hB₀.seqOn_eq_of_image_eq e.isLocalDiffeomorph hpb hT' hT₂
    (hSY.isCompact_closure_preimageOpens _ (hY.isCompact_closure_preimageOpens U hU))
    (hS.isCompact_closure_preimageOpens U hU) himg
  -- (`e` restricted to the traces is onto: no empty centre is erased; term mode across the two
  -- spellings of the bottom model `Fin (n - s - 1)` / `Fin (n - (s + 1))`)
  have hB' := Eq.trans hB (AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_of_surjective _
    ((B₀.fam _ hT').noEmptyCenters _ _) _ _ (AnalyticMap.surjective_restrictMap himg))
  -- (E) the composition of the push-forwards
  rw [hC, hD, hB']
  exact AnalyticManifold.BlowUpSequence.pushforwardRestrict_pushforwardRestrict_of_flag hY hS hsub
      hSY e he U _

end FlagCase

end Manifold

/-! ### (E1) the chaining lemma and (E3) the tower -/

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- **(E1), the chaining lemma** ([Kol07, 108]):
the codimension-`s` clause of `B₂` through `B₁` and the codimension-one clause of `B₁` through `B₀`
give the codimension-`(s + 1)` clause of `B₂` through `B₀`. (A) a flag cover of the relatively
compact open `U` and its coproduct `Σ`, on which `desc⁻¹ S` sits in the global flag
`FlagCover.flag` of codimension `s`; pull-back along the surjective local isomorphism `coverMap`
is injective ([Kol07, Proposition 37]), so it suffices to compare the two pull-backs: (A1) the left
side is the value of `B₂` on the pulled-back triple (`CommutesWithLocalIsos`), (A2) the right side
is the push-forward from `desc⁻¹ S` of the value of `B₀` on the pulled-back triple
(`pushforwardRestrict_pullback_restrictMap`, `CommutesWithLocalIsos` along the restricted descent
map), and the flag case (C)–(E) on `Σ` identifies the two. -/
theorem AnalyticFamilyFunctor.commutesWithClosedEmbeddingsOfEmptyDivisorFam_chain {s : ℕ}
    {Dom₂ : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ M → Prop}
    (B₂ : AnalyticFamilyFunctor ψ Dom₂) (hB₂ : B₂.CommutesWithLocalIsos)
    (hDom₂ : ∀ {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ M) (g : AnalyticMap N M)
      (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g), Dom₂ T → Dom₂ (T.pullback g hg))
    {Dom₁ : ∀ {M₁ : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)},
      AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) M₁ → Prop}
    (B₁ : AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Dom₁)
    (hDom₁ : ∀ {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} (hY : IsClosedSubmanifold ψ Y s)
      (I : AnalyticManifold.IdealSheaf M) (hI : I.IsNonzeroEverywhere)
      (hJ : (I.pullback hY.inclusionMap hY.inclusionMap.contMDiff).IsNonzeroEverywhere),
      hY.idealSheaf ≤ I →
      Dom₂ ⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩ →
      Dom₁ ⟨I.pullback hY.inclusionMap hY.inclusionMap.contMDiff, hJ, HypersurfaceFamily.empty _,
        HypersurfaceFamily.isSnc_empty⟩)
    {Dom₀ : ∀ {M₀ : AnalyticManifold.{u} 𝕜 (Fin (n - s - 1) → 𝕜)},
      AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s - 1) → 𝕜)) M₀ → Prop}
    (B₀ : AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s - 1) → 𝕜)) Dom₀)
    (hB₀ : B₀.CommutesWithLocalIsos)
    (hDom₀ : ∀ {M N : AnalyticManifold.{u} 𝕜 (Fin (n - s - 1) → 𝕜)}
      (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s - 1) → 𝕜)) M)
      (g : AnalyticMap N M)
      (hg : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - s - 1) → 𝕜) 𝓘(𝕜, Fin (n - s - 1) → 𝕜) ω g),
      Dom₀ T → Dom₀ (T.pullback g hg))
    (hs : B₂.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s) B₁)
    (h1 : B₁.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := 1) B₀) :
    B₂.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s + 1) B₀ := by
  intro M S hS I hI J hJ hle hJI hT hT' U hU
  have _hfd := finiteDimensional_of_chartIso ψ
  -- (A) the flag cover of `U` and its coproduct
  obtain ⟨C⟩ := exists_flagCover hS U hU
  have hg := C.isLocalDiffeomorph_desc
  have hgS := C.isLocalDiffeomorph_descS
  -- pull-back along the surjective local isomorphism `coverMap` is injective
  refine AnalyticManifold.BlowUpSequence.pullback_injective_of_surjective C.coverMap
      C.isLocalDiffeomorph_coverMap
    C.surjective_coverMap _ _ ?_
  -- (A1) the left side: the value of `B₂` on the pulled-back triple
  have hA1 := Eq.trans (hB₂.seqOn_eq_of_image_eq hg (AnalyticTriple.isPullbackOf_pullback
      (⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩ : AnalyticTriple ψ M)
      C.desc hg) hT (hDom₂ _ C.desc hg hT) C.isCompact_closure_opens hU C.image_opens_eq)
    (AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_of_surjective _
        ((B₂.fam _ hT).noEmptyCenters _ _) _ _
      C.surjective_coverMap)
  -- (A2) the right side: the value of `B₀` on the pulled-back triple, pushed forward
  have hA2 := Eq.trans (hB₀.seqOn_eq_of_image_eq hgS (AnalyticTriple.isPullbackOf_pullback
      (⟨J, hJ, HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩ : AnalyticTriple
        (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s - 1) → 𝕜)) hS.toAnalyticManifold) C.descS hgS)
      hT' (hDom₀ _ C.descS hgS hT')
      (C.isClosedSubmanifold_preimage.isCompact_closure_preimageOpens C.opens
        C.isCompact_closure_opens)
      (hS.isCompact_closure_preimageOpens U hU) C.image_descS_preimageOpens_eq)
    (AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_of_surjective _
        ((B₀.fam _ hT').noEmptyCenters _ _) _ _
      (AnalyticMap.surjective_restrictMap C.image_descS_preimageOpens_eq))
  have hA2' := AnalyticManifold.BlowUpSequence.pushforwardRestrict_pullback_restrictMap hS C.desc hg
    C.isClosedSubmanifold_preimage C.opens U C.image_opens_subset
    ((B₀.fam _ hT').seqOn (hS.preimageOpens U) (hS.isCompact_closure_preimageOpens U hU))
  -- the pulled-back data on the coproduct
  have hle' : C.isClosedSubmanifold_preimage.idealSheaf ≤ I.pullback C.desc C.desc.contMDiff :=
    (hS.idealSheaf_preimage_of_isLocalDiffeomorph C.desc hg).le.trans
      (IdealSheaf.pullback_le_pullback _ _ hle)
  have hJI' : J.pullback C.descS C.descS.contMDiff =
      (I.pullback C.desc C.desc.contMDiff).pullback C.isClosedSubmanifold_preimage.inclusionMap
        C.isClosedSubmanifold_preimage.inclusionMap.contMDiff := by
    rw [hJI, IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback]
    exact IdealSheaf.pullback_congr I _ _ (funext fun _ => rfl)
  have hTσ := hDom₂ _ C.desc hg hT
  rw [AnalyticTriple.pullback_emptyDivisor] at hTσ
  have hT'σ := hDom₀ _ C.descS hgS hT'
  rw [AnalyticTriple.pullback_emptyDivisor] at hT'σ
  -- the flag case on the coproduct
  have hflag := AnalyticFamilyFunctor.commutesWithClosedEmbeddings_flag_case B₂ B₁ B₀ hDom₁ hB₀
    hDom₀ hs h1 C.isClosedSubmanifold_flag C.isClosedSubmanifold_preimage C.preimage_subset_flag
    C.isClosedSubmanifold_preimage_flag _ _ _ _ hle' hJI' hTσ hT'σ C.opens
    C.isCompact_closure_opens
  -- the assembly
  calc ((B₂.fam _ hT).seqOn U hU).pullback C.coverMap C.isLocalDiffeomorph_coverMap
      = (B₂.fam _ (hDom₂ _ C.desc hg hT)).seqOn C.opens C.isCompact_closure_opens := hA1.symm
    _ = (B₂.fam _ hTσ).seqOn C.opens C.isCompact_closure_opens :=
        B₂.fam_seqOn_congr_triple (AnalyticTriple.pullback_emptyDivisor I hI C.desc hg) _ _ _ _
    _ = AnalyticManifold.BlowUpSequence.pushforwardRestrict C.isClosedSubmanifold_preimage C.opens
          ((B₀.fam _ hT'σ).seqOn (C.isClosedSubmanifold_preimage.preimageOpens C.opens) _) :=
        hflag
    _ = AnalyticManifold.BlowUpSequence.pushforwardRestrict C.isClosedSubmanifold_preimage C.opens
          ((B₀.fam _ (hDom₀ _ C.descS hgS hT')).seqOn
            (C.isClosedSubmanifold_preimage.preimageOpens C.opens) _) :=
        congrArg (AnalyticManifold.BlowUpSequence.pushforwardRestrict
            C.isClosedSubmanifold_preimage C.opens)
          (B₀.fam_seqOn_congr_triple
            (AnalyticTriple.pullback_emptyDivisor J hJ C.descS hgS).symm _ _ _ _)
    _ = AnalyticManifold.BlowUpSequence.pushforwardRestrict C.isClosedSubmanifold_preimage C.opens
          (((B₀.fam _ hT').seqOn (hS.preimageOpens U)
              (hS.isCompact_closure_preimageOpens U hU)).pullback
            (AnalyticMap.restrictMap C.descS _ _ C.image_descS_preimageOpens_eq.le) _) :=
        congrArg (AnalyticManifold.BlowUpSequence.pushforwardRestrict
            C.isClosedSubmanifold_preimage C.opens) hA2
    _ = (AnalyticManifold.BlowUpSequence.pushforwardRestrict hS U ((B₀.fam _ hT').seqOn
        (hS.preimageOpens U)
          (hS.isCompact_closure_preimageOpens U hU))).pullback C.coverMap
          C.isLocalDiffeomorph_coverMap := hA2'.symm

/-- **(E3)**: for a tower `F` of family functors at
the standard models with the domain hypotheses of (E1) at every level, the codimension-zero and
codimension-one clauses give the clause at every codimension, `n - s` literal — induction on `s`
with (E1) at the bottom of the flag when `0 < n - s` and the degenerate case of
`Hironaka.Resolution.Analytic.Functor.ChainClosedEmbeddingDegenerate` when `n ≤ s`. -/
theorem AnalyticFamilyFunctor.commutesWithClosedEmbeddingsOfEmptyDivisorFam_tower
    {Dom : ∀ n, ∀ {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)},
      AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M → Prop}
    (F : ∀ n, AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (Dom n))
    (hF : ∀ n, (F n).CommutesWithLocalIsos)
    (hDomPull : ∀ n {M N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
      (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (g : AnalyticMap N M)
      (hg : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g),
      Dom n T → Dom n (T.pullback g hg))
    (hDomRes : ∀ n s {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} {Y : Set M}
      (hY : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) Y s)
      (I : AnalyticManifold.IdealSheaf M) (hI : I.IsNonzeroEverywhere)
      (hJ : (I.pullback hY.inclusionMap hY.inclusionMap.contMDiff).IsNonzeroEverywhere),
      hY.idealSheaf ≤ I →
      Dom n ⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩ →
      Dom (n - s) ⟨I.pullback hY.inclusionMap hY.inclusionMap.contMDiff, hJ,
        HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩)
    (h0 : ∀ n, (F n).CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := 0) (F n))
    (h1 : ∀ m, 0 < m → (F m).CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := 1) (F (m - 1))) :
    ∀ n s, (F n).CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s) (F (n - s)) := by
  intro n s
  induction s with
  | zero => exact h0 n
  | succ s ih =>
    rcases Nat.eq_zero_or_pos (n - s) with hz | hpos
    · exact AnalyticFamilyFunctor.commutesWithClosedEmbeddingsOfEmptyDivisorFam_of_lt (F n) (F n)
        (F (n - (s + 1))) (by omega) (h0 n)
        (fun I hI hJ hle hT => hDomRes n 0 (isClosedSubmanifold_empty' _ 0) I hI hJ hle hT)
    · exact AnalyticFamilyFunctor.commutesWithClosedEmbeddingsOfEmptyDivisorFam_chain (F n) (hF n)
        (hDomPull n) (F (n - s)) (hDomRes n s) (F (n - s - 1)) (hF _) (hDomPull _) ih
        (h1 (n - s) hpos)

end Hironaka.Manifold

end
