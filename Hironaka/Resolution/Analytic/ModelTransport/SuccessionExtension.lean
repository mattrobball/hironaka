/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.ModelTransport.Succession
public import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Defs
import Hironaka.Manifold.BlowUp.Restrict
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Resolution.Analytic.Functor.ExtensionOf
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Włodarczyk's extension relation along the transport of a succession

Włodarczyk's extension relation between finite successions [Wlo09, Definition 3.2.6]
(`FiniteSuccession.IsExtensionOf`) is carried along
the transport `transportAlong g ψ` of `Hironaka/Resolution/Analytic/ModelTransport/Succession.lean`;
the compatibility field of a transported compatible family (`Family.lean`) rests on it.

* `IsExtensionOf.transportAlong`: an extension `T` of `S` transports to an extension
  `T.transportAlong g ψ` of `S.transportAlong g ψ` — the same block index, the stage identifications
  conjugated by the stage identifications of the transports (`transportAlongExtStage`); the seven
  clauses follow from the identities of `Succession.lean` (the composite blow-downs
  `stageMap_transportAlong`, the blow-downs `map_transportAlong`, the centres
  `center_transportAlong`) and from the commutation of the composites between two stages
  (`stageMapLE`) with the identifications (`stageMapLE_transportAlong`, by the distance between the
  stages, as `stageMapLE_pullbackLift` of `Hironaka/Resolution/Analytic/Functor/ExtensionOf.lean`).
* `isExtensionOf_restrict_transportAlong`: the restriction of a transported succession to a smaller
  open is an extension of the transport of the restriction of the smaller succession — stage-wise
  isomorphic over the smaller open to the transport of the restriction
  (`IsExtensionOf.of_stageEquiv_left`): at stage `0` the identity, at a later stage the identity of
  the trace read from "re-model then restrict" to "restrict then re-model" (`restrictTransportSwap`;
  the two traces agree by `stageMap_transportAlong`), the blow-downs and centres of both being `S`'s
  own read on the traces.

The auxiliaries of the restriction of a succession (`stageMapLE`, `centerAt`, the traces and data
of `FiniteSuccession.restrict`) are used directly, as
`Hironaka/Resolution/Analytic/Functor/ExtensionOf.lean` does.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set Filter Topology Manifold
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {N₀ : AnalyticManifold.{u} 𝕜 E}
  {N : AnalyticManifold.{u} 𝕜 E'} (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') N₀ N ω) (ψ : E' ≃L[𝕜] E)
  (S : FiniteSuccession N)

/-! ### The composites between two stages along the transport -/

/-- The composites `σ_{a+1} ∘ ⋯ ∘ σ_b` between two stages (`stageMapLE`) commute with the stage
identifications, by the distance between the stages (as `stageMapLE_pullbackLift_aux`): the identity
at distance `0`, one more blow-down and the square `map_transportAlong` at each step. -/
theorem stageMapLE_transportAlong_aux (a : Fin (S.length + 1)) :
    ∀ (d : ℕ) (hd : a.1 + d < S.length + 1) (hab : a ≤ ⟨a.1 + d, hd⟩)
      (q : (S.transportAlong g ψ).stage ⟨a.1 + d, hd⟩),
      stageMapLE S hab (S.transportAlongStage g ψ ⟨a.1 + d, hd⟩ q) =
        S.transportAlongStage g ψ a (stageMapLE (S.transportAlong g ψ) hab q)
  | 0, hd, hab, q => by
    rw [stageMapLE_self S _ hab, stageMapLE_self (S.transportAlong g ψ) _ hab]
    rfl
  | d + 1, hd, hab, q => by
    have hd₀ : a.1 + d < S.length + 1 := Nat.lt_of_succ_lt hd
    have h₂ : a ≤ (⟨a.1 + d, hd₀⟩ : Fin (S.length + 1)) := Fin.mk_le_mk.mpr (Nat.le_add_right _ _)
    calc stageMapLE S hab (S.transportAlongStage g ψ ⟨a.1 + (d + 1), hd⟩ q)
        = (stageMapLE S h₂).comp (S.map ⟨a.1 + d, Nat.lt_of_succ_lt_succ hd⟩)
            (S.transportAlongStage g ψ ⟨a.1 + (d + 1), hd⟩ q) :=
          congrArg (fun f => f (S.transportAlongStage g ψ ⟨a.1 + (d + 1), hd⟩ q))
            (stageMapLE_succ S (b := ⟨a.1 + d, Nat.lt_of_succ_lt_succ hd⟩) hab h₂)
      _ = stageMapLE S h₂ (S.transportAlongStage g ψ ⟨a.1 + d, hd₀⟩
            ((S.transportAlong g ψ).map ⟨a.1 + d, Nat.lt_of_succ_lt_succ hd⟩ q)) :=
          congrArg (stageMapLE S h₂)
            (S.map_transportAlong g ψ ⟨a.1 + d, Nat.lt_of_succ_lt_succ hd⟩ q)
      _ = S.transportAlongStage g ψ a (stageMapLE (S.transportAlong g ψ) h₂
            ((S.transportAlong g ψ).map ⟨a.1 + d, Nat.lt_of_succ_lt_succ hd⟩ q)) :=
          stageMapLE_transportAlong_aux a d hd₀ h₂ _
      _ = S.transportAlongStage g ψ a (stageMapLE (S.transportAlong g ψ) hab q) :=
          congrArg (S.transportAlongStage g ψ a)
            (congrArg (fun f => f q) (stageMapLE_succ (S.transportAlong g ψ)
              (b := ⟨a.1 + d, Nat.lt_of_succ_lt_succ hd⟩) hab h₂)).symm

/-- The composites between two stages commute with the stage identifications. -/
theorem stageMapLE_transportAlong {a b : Fin (S.length + 1)} (hab : a ≤ b)
    (q : (S.transportAlong g ψ).stage b) :
    stageMapLE S hab (S.transportAlongStage g ψ b q) =
      S.transportAlongStage g ψ a (stageMapLE (S.transportAlong g ψ) hab q) := by
  obtain ⟨bv, hbv⟩ := b
  obtain ⟨d, hd⟩ := Nat.le.dest (Fin.le_iff_val_le_val.mp hab)
  subst hd
  exact S.stageMapLE_transportAlong_aux g ψ a d hbv hab q

/-! ### The extension relation along the transport -/

/-- The stage identification of an extension, conjugated by the stage identifications of the
transports: `e'_k = (stage_S (blk k))⁻¹ ∘ e_k ∘ stage_T k`. -/
def transportAlongExtStage {T : FiniteSuccession N}
    (blk : Fin (T.length + 1) → Fin (S.length + 1))
    (e : ∀ k, Diffeomorph 𝓘(𝕜, E') 𝓘(𝕜, E') (T.stage k) (S.stage (blk k)) ω)
    (k : Fin (T.length + 1)) :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ((T.transportAlong g ψ).stage k)
      ((S.transportAlong g ψ).stage (blk k)) ω :=
  (T.transportAlongStage g ψ k).trans ((e k).trans (S.transportAlongStage g ψ (blk k)).symm)

/-- The conjugated identification, read through the stage identification of `S`, is `e_k` after
the stage identification of `T`. -/
theorem transportAlongStage_transportAlongExtStage {T : FiniteSuccession N}
    (blk : Fin (T.length + 1) → Fin (S.length + 1))
    (e : ∀ k, Diffeomorph 𝓘(𝕜, E') 𝓘(𝕜, E') (T.stage k) (S.stage (blk k)) ω)
    (k : Fin (T.length + 1)) (p : (T.transportAlong g ψ).stage k) :
    S.transportAlongStage g ψ (blk k) (S.transportAlongExtStage g ψ blk e k p) =
      e k (T.transportAlongStage g ψ k p) := by
  unfold transportAlongExtStage
  rw [Diffeomorph.coe_trans, Diffeomorph.coe_trans, Function.comp_apply, Function.comp_apply,
    Diffeomorph.apply_symm_apply]

/-- **Włodarczyk's extension relation [Wlo09, Definition 3.2.6] transports along `g`**: the same
block index, the identifications conjugated by the stage identifications; the "over the base"
clause by `stageMap_transportAlong` on both sides, the intertwining clause by
`stageMapLE_transportAlong` and `map_transportAlong`, the centres by `center_transportAlong` and
the pull-back calculus, the empty centres by `support_pullbackDiffeomorph`. -/
theorem IsExtensionOf.transportAlong {T : FiniteSuccession N} (h : T.IsExtensionOf S) :
    (T.transportAlong g ψ).IsExtensionOf (S.transportAlong g ψ) := by
  obtain ⟨blk, e, h0, hl, hs, ho, hm, hc, hn⟩ := h
  refine ⟨blk, S.transportAlongExtStage g ψ blk e, h0, hl, hs, ?_, ?_, ?_, ?_⟩
  · intro k p
    have key : g ((S.transportAlong g ψ).stageMap (blk k)
          (S.transportAlongExtStage g ψ blk e k p)) =
        g ((T.transportAlong g ψ).stageMap k p) :=
      (S.stageMap_transportAlong g ψ (blk k) _).symm.trans
        ((congrArg (S.stageMap (blk k))
            (S.transportAlongStage_transportAlongExtStage g ψ blk e k p)).trans
          ((ho k _).trans (T.stageMap_transportAlong g ψ k p)))
    exact (g.symm_apply_apply _).symm.trans ((congrArg g.symm key).trans (g.symm_apply_apply _))
  · intro k hle p
    have key : S.transportAlongStage g ψ (blk k.castSucc)
        (stageMapLE (S.transportAlong g ψ) hle (S.transportAlongExtStage g ψ blk e k.succ p)) =
        S.transportAlongStage g ψ (blk k.castSucc)
          (S.transportAlongExtStage g ψ blk e k.castSucc ((T.transportAlong g ψ).map k p)) :=
      (S.stageMapLE_transportAlong g ψ hle _).symm.trans
        ((congrArg (stageMapLE S hle)
            (S.transportAlongStage_transportAlongExtStage g ψ blk e k.succ p)).trans
          ((hm k hle _).trans
            ((congrArg (e k.castSucc) (T.map_transportAlong g ψ k p)).trans
              (S.transportAlongStage_transportAlongExtStage g ψ blk e k.castSucc _).symm)))
    exact ((S.transportAlongStage g ψ (blk k.castSucc)).symm_apply_apply _).symm.trans
      ((congrArg (S.transportAlongStage g ψ (blk k.castSucc)).symm key).trans
        ((S.transportAlongStage g ψ (blk k.castSucc)).symm_apply_apply _))
  · intro k ha hstep
    exact (T.center_transportAlong g ψ k).trans
      ((congrArg
          (IdealSheaf.pullbackDiffeomorph
              (T.transportAlongStage g ψ k.castSucc))
          (hc k ha hstep)).trans
        ((IdealSheaf.pullback_pullback (S.center ⟨(blk k.castSucc).1, ha⟩) ⇑(e k.castSucc)
            (e k.castSucc).contMDiff ⇑(T.transportAlongStage g ψ k.castSucc)
            (T.transportAlongStage g ψ k.castSucc).contMDiff).trans
          ((IdealSheaf.pullback_congr (S.center ⟨(blk k.castSucc).1, ha⟩) _ _
              (funext fun x =>
                (S.transportAlongStage_transportAlongExtStage g ψ blk e k.castSucc x).symm)).trans
            ((IdealSheaf.pullback_pullback (S.center ⟨(blk k.castSucc).1, ha⟩)
                ⇑(S.transportAlongStage g ψ (blk k.castSucc))
                (S.transportAlongStage g ψ (blk k.castSucc)).contMDiff
                ⇑(S.transportAlongExtStage g ψ blk e k.castSucc)
                (S.transportAlongExtStage g ψ blk e k.castSucc).contMDiff).symm.trans
              (congrArg (fun J =>
                  IdealSheaf.pullback ⇑(S.transportAlongExtStage g ψ blk e k.castSucc)
                    (S.transportAlongExtStage g ψ blk e k.castSucc).contMDiff J)
                (S.center_transportAlong g ψ ⟨(blk k.castSucc).1, ha⟩).symm)))))
  · intro k hk
    exact (congrArg IdealSheaf.support (T.center_transportAlong g ψ k)).trans
      ((IdealSheaf.support_pullbackDiffeomorph _ _).trans
        ((congrArg (fun s => ⇑(T.transportAlongStage g ψ k.castSucc) ⁻¹' s) (hn k hk)).trans
          Set.preimage_empty))

/-! ### The restriction of a transported succession -/

/-- The identity of a trace, from "re-model then restrict" to "restrict then re-model": an analytic
isomorphism when the two opens are the same set (the typed identities of
`Hironaka/Resolution/Analytic/ModelTransport/Manifold.lean`, `contMDiff_codRestrict_opens`). -/
def restrictTransportSwap {X : AnalyticManifold.{u} 𝕜 E'} (V : Opens (X.transport ψ))
    (V' : Opens X) (hV : ∀ p : X, X.toTransport ψ p ∈ V ↔ p ∈ V') :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ((X.transport ψ).restrict V) ((X.restrict V').transport ψ) ω where
  toFun q := (X.restrict V').toTransport ψ ⟨X.ofTransport ψ q.1, (hV _).1 q.2⟩
  invFun q := ⟨X.toTransport ψ ((X.restrict V').ofTransport ψ q).1,
    (hV _).2 ((X.restrict V').ofTransport ψ q).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := ((X.restrict V').contMDiff_toTransport ψ).comp
    (contMDiff_codRestrict_opens (X.contMDiff_ofTransport ψ)
      (f' := fun q : (X.transport ψ).restrict V =>
        (⟨X.ofTransport ψ q.1, (hV _).1 q.2⟩ : X.restrict V')) fun _ => rfl)
  contMDiff_invFun := (contMDiff_codRestrict_opens (X.contMDiff_toTransport ψ)
    (f' := fun r : X.restrict V' =>
      (⟨X.toTransport ψ r.1, (hV _).2 r.2⟩ : (X.transport ψ).restrict V)) fun _ => rfl).comp
    ((X.restrict V').contMDiff_ofTransport ψ)

/-- **The restriction of the transported succession to a smaller open is an extension of the
transport of the restricted smaller succession**: the compatibility field of a transported
compatible family (`Family.lean`). The restriction of the transport is stage-wise isomorphic over
`U₁` to the transport of the restriction (`IsExtensionOf.of_stageEquiv_left`): at stage `0` the
identity of `U₁`, at a later stage `restrictTransportSwap` (the traces agree by
`stageMap_transportAlong`), the composite blow-downs read in `M` by `val_stageMap_restrict`, the
blow-downs and the centres of both being `S₂`'s own on the traces (definitionally, up to the
pull-back calculus); then `IsExtensionOf.transportAlong` on the extension of the restriction. -/
theorem isExtensionOf_restrict_transportAlong {M : AnalyticManifold.{u} 𝕜 E} (ψ' : E ≃L[𝕜] E')
    {U₁ U₂ : Opens M} (h : U₁ ≤ U₂)
    (S₂ : FiniteSuccession ((M.transport ψ').restrict U₂))
    (S₁ : FiniteSuccession ((M.transport ψ').restrict U₁))
    (hS : (S₂.restrict h).IsExtensionOf S₁) :
    ((S₂.transportAlong (M.restrictTransportDiffeomorph ψ' U₂) ψ'.symm).restrict h).IsExtensionOf
      (S₁.transportAlong (M.restrictTransportDiffeomorph ψ' U₁) ψ'.symm) := by
  set g₂ := M.restrictTransportDiffeomorph ψ' U₂ with hg₂
  set g₁ := M.restrictTransportDiffeomorph ψ' U₁ with hg₁
  have hRQ : ((S₂.restrict h).transportAlong g₁ ψ'.symm).IsExtensionOf
      (S₁.transportAlong g₁ ψ'.symm) := hS.transportAlong g₁ ψ'.symm
  -- the traces of `U₁` on the re-modelled stages are the traces on the stages
  have hV : ∀ (j : Fin S₂.length) (p : S₂.stage j.succ),
      (S₂.stage j.succ).toTransport ψ'.symm p ∈
          restrictStageOpens (S₂.transportAlong g₂ ψ'.symm) U₁ j.succ ↔
        p ∈ restrictStageOpens S₂ U₁ j.succ := fun j p =>
    Iff.of_eq (congrArg (fun x : M => x ∈ U₁)
      (congrArg Subtype.val (S₂.stageMap_transportAlong g₂ ψ'.symm j.succ p)).symm)
  let D : ∀ j : Fin S₂.length,
      Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E)
        (((S₂.transportAlong g₂ ψ'.symm).restrict h).stage j.succ)
        (((S₂.restrict h).transportAlong g₁ ψ'.symm).stage j.succ) ω :=
    fun j => restrictTransportSwap ψ'.symm
      (restrictStageOpens (S₂.transportAlong g₂ ψ'.symm) U₁ j.succ)
      (restrictStageOpens S₂ U₁ j.succ) (hV j)
  refine IsExtensionOf.of_stageEquiv_left (T := (S₂.transportAlong g₂ ψ'.symm).restrict h)
    (S := (S₂.restrict h).transportAlong g₁ ψ'.symm) rfl
    (fun k => Fin.cases (Diffeomorph.refl _ _ _) (fun j => D j) k) ?_ ?_ ?_ hRQ
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · intro p
      rfl
    · intro p
      apply Subtype.ext
      have a1 : ((((S₂.restrict h).transportAlong g₁ ψ'.symm).stageMap j.succ (D j p)).1 : M) =
          (((S₂.restrict h).stageMap j.succ (D j p)).1 : M) :=
        (congrArg Subtype.val
          ((S₂.restrict h).stageMap_transportAlong g₁ ψ'.symm j.succ (D j p))).symm
      have a2 : (((S₂.restrict h).stageMap j.succ (D j p)).1 : M) =
          ((S₂.stageMap j.succ p.1).1 : M) :=
        val_stageMap_restrict S₂ h j (D j p)
      have b1 : ((((S₂.transportAlong g₂ ψ'.symm).restrict h).stageMap j.succ p).1 : M) =
          (((S₂.transportAlong g₂ ψ'.symm).stageMap j.succ p.1).1 : M) :=
        val_stageMap_restrict (S₂.transportAlong g₂ ψ'.symm) h j p
      have b2 : (((S₂.transportAlong g₂ ψ'.symm).stageMap j.succ p.1).1 : M) =
          ((S₂.stageMap j.succ p.1).1 : M) :=
        (congrArg Subtype.val (S₂.stageMap_transportAlong g₂ ψ'.symm j.succ p.1)).symm
      exact a1.trans (a2.trans (b2.symm.trans b1.symm))
  · rintro ⟨k, hk⟩ p
    cases k with
    | zero => rfl
    | succ j => rfl
  · rintro ⟨k, hk⟩
    cases k with
    | zero =>
      have e1 : ((S₂.transportAlong g₂ ψ'.symm).restrict h).center ⟨0, hk⟩ =
          IdealSheaf.pullback ⇑(restrictOpensIncl h) (restrictOpensIncl h).contMDiff
            (IdealSheaf.pullback ⇑g₂ g₂.contMDiff (S₂.center ⟨0, hk⟩)) := rfl
      have e2 : IdealSheaf.pullback ⇑(restrictOpensIncl h) (restrictOpensIncl h).contMDiff
            (IdealSheaf.pullback ⇑g₂ g₂.contMDiff (S₂.center ⟨0, hk⟩)) =
          IdealSheaf.pullback (⇑g₂ ∘ ⇑(restrictOpensIncl h))
            (g₂.contMDiff.comp (restrictOpensIncl h).contMDiff) (S₂.center ⟨0, hk⟩) :=
        IdealSheaf.pullback_pullback _ _ _ _ _
      have e3 : IdealSheaf.pullback (⇑g₂ ∘ ⇑(restrictOpensIncl h))
            (g₂.contMDiff.comp (restrictOpensIncl h).contMDiff) (S₂.center ⟨0, hk⟩) =
          IdealSheaf.pullback (⇑(restrictOpensIncl (M := M.transport ψ') h) ∘ ⇑g₁)
            ((restrictOpensIncl (M := M.transport ψ') h).contMDiff.comp g₁.contMDiff)
            (S₂.center ⟨0, hk⟩) :=
        IdealSheaf.pullback_congr _ _ _ (funext fun _ => rfl)
      have e4 : IdealSheaf.pullback (⇑(restrictOpensIncl (M := M.transport ψ') h) ∘ ⇑g₁)
            ((restrictOpensIncl (M := M.transport ψ') h).contMDiff.comp g₁.contMDiff)
            (S₂.center ⟨0, hk⟩) =
          IdealSheaf.pullback ⇑g₁ g₁.contMDiff
            (IdealSheaf.pullback ⇑(restrictOpensIncl (M := M.transport ψ') h)
              (restrictOpensIncl (M := M.transport ψ') h).contMDiff (S₂.center ⟨0, hk⟩)) :=
        (IdealSheaf.pullback_pullback (S₂.center ⟨0, hk⟩)
          ⇑(restrictOpensIncl (M := M.transport ψ') h)
          (restrictOpensIncl (M := M.transport ψ') h).contMDiff ⇑g₁ g₁.contMDiff).symm
      have e5 : IdealSheaf.pullback ⇑g₁ g₁.contMDiff
            (IdealSheaf.pullback ⇑(restrictOpensIncl (M := M.transport ψ') h)
              (restrictOpensIncl (M := M.transport ψ') h).contMDiff (S₂.center ⟨0, hk⟩)) =
          (((S₂.restrict h).transportAlong g₁ ψ'.symm).center ⟨0, hk⟩).pullback
            ⇑(Diffeomorph.refl 𝓘(𝕜, E) (M.restrict U₁) ω) (Diffeomorph.refl 𝓘(𝕜, E) (M.restrict U₁)
                ω).contMDiff :=
        Eq.symm (comap_diffeomorph_refl _)
      exact e1.trans (e2.trans (e3.trans (e4.trans e5)))
    | succ j =>
      have hj : j + 1 < S₂.length + 1 := Nat.lt_succ_of_lt hk
      set X := S₂.stage ⟨j + 1, hj⟩ with hX
      set C := S₂.center ⟨j + 1, hk⟩ with hC
      set VT := restrictStageOpens (S₂.transportAlong g₂ ψ'.symm) U₁ ⟨j + 1, hj⟩ with hVT
      set VS := restrictStageOpens S₂ U₁ ⟨j + 1, hj⟩ with hVS
      set ιT := ((S₂.transportAlong g₂ ψ'.symm).stage ⟨j + 1, hj⟩).inclusion VT with hιT
      set ιS := X.inclusion VS with hιS
      set d := (X.transportDiffeomorph ψ'.symm).symm with hd
      set d' := ((X.restrict VS).transportDiffeomorph ψ'.symm).symm with hd'
      set Dj := D ⟨j, Nat.lt_of_succ_lt hk⟩ with hDj
      have e1 : ((S₂.transportAlong g₂ ψ'.symm).restrict h).center ⟨j + 1, hk⟩ =
          IdealSheaf.pullback ⇑ιT ιT.contMDiff (IdealSheaf.pullback ⇑d d.contMDiff C) := rfl
      have e2 : IdealSheaf.pullback ⇑ιT ιT.contMDiff (IdealSheaf.pullback ⇑d d.contMDiff C) =
          IdealSheaf.pullback (⇑d ∘ ⇑ιT) (d.contMDiff.comp ιT.contMDiff) C :=
        IdealSheaf.pullback_pullback _ _ _ _ _
      have e3 : IdealSheaf.pullback (⇑d ∘ ⇑ιT) (d.contMDiff.comp ιT.contMDiff) C =
          IdealSheaf.pullback (⇑ιS ∘ (⇑d' ∘ ⇑Dj))
            (ιS.contMDiff.comp (d'.contMDiff.comp Dj.contMDiff)) C :=
        IdealSheaf.pullback_congr _ _ _ (funext fun _ => rfl)
      have e4 : IdealSheaf.pullback (⇑ιS ∘ (⇑d' ∘ ⇑Dj))
            (ιS.contMDiff.comp (d'.contMDiff.comp Dj.contMDiff)) C =
          IdealSheaf.pullback (⇑d' ∘ ⇑Dj) (d'.contMDiff.comp Dj.contMDiff)
            (IdealSheaf.pullback ⇑ιS ιS.contMDiff C) :=
        (IdealSheaf.pullback_pullback C ⇑ιS ιS.contMDiff (⇑d' ∘ ⇑Dj)
          (d'.contMDiff.comp Dj.contMDiff)).symm
      have e5 : IdealSheaf.pullback (⇑d' ∘ ⇑Dj) (d'.contMDiff.comp Dj.contMDiff)
            (IdealSheaf.pullback ⇑ιS ιS.contMDiff C) =
          IdealSheaf.pullback ⇑Dj Dj.contMDiff
            (IdealSheaf.pullback ⇑d' d'.contMDiff (IdealSheaf.pullback ⇑ιS ιS.contMDiff C)) :=
        (IdealSheaf.pullback_pullback (IdealSheaf.pullback ⇑ιS ιS.contMDiff C) ⇑d' d'.contMDiff
          ⇑Dj Dj.contMDiff).symm
      have e6 : IdealSheaf.pullback ⇑Dj Dj.contMDiff
            (IdealSheaf.pullback ⇑d' d'.contMDiff (IdealSheaf.pullback ⇑ιS ιS.contMDiff C)) =
          (((S₂.restrict h).transportAlong g₁ ψ'.symm).center ⟨j + 1, hk⟩).pullback
            ⇑Dj Dj.contMDiff := rfl
      exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans e6))))

end AnalyticManifold.FiniteSuccession

end
