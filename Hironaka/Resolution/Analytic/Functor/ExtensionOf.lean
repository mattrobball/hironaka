/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.Family
public import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Defs
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.PullbackLiftStages
import Hironaka.Resolution.Analytic.Functor.PullbackSequence
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Włodarczyk's extension relation: its calculus

`FiniteSuccession.IsExtensionOf T S` ([Wlo09, Definition 3.2.6]) says that `T` is a sequence of
blow-ups and isomorphisms whose blow-ups are those of `S`: a block index `blk`, identifications
`e k` over the base, the maps intertwined through the composites `stageMapLE` between two stages,
the centres carried at the jumps, empty at the non-jumps. This module proves what the limit
construction of the compatible families needs of it:

* the two computation rules of `stageMapLE` (`Nat.leRecOn_self`, `Nat.leRecOn_succ`): from stage
  `0` it is the composite blow-down (`stageMapLE_zero_left`), on `cons` between later stages it is
  the tail's (`stageMapLE_cons`), and the stage lifts of a pull-back intertwine it
  (`stageMapLE_pullbackLift`);
* reflexivity (`IsExtensionOf.refl`) and the composition with a stage-wise isomorphism over the
  base on the left (`IsExtensionOf.of_stageEquiv_left`);
* the remark following [Wlo09, Definition 3.2.6], with [Kol07, 32] and [Kol07, 34.1]: a list's
  succession is an extension of its cleaned list's succession
  (`isExtensionOf_toSuccession_eraseEmpty`); a nonempty first centre is a jump
  (`isExtensionOf_toSuccession_cons`), an empty one a non-jump whose identification is
  `Bl_∅ M ≃ M` (`isExtensionOf_toSuccession_cons_of_eq_empty`);
* [Wlo09, Theorem 2.0.3, (4)]: the restriction of a list's succession to an open `U₁ ≤ U₂` is
  stage-wise isomorphic over `U₁` to its pull-back along the open inclusion, hence an extension of
  whatever the pull-back is an extension of (`isExtensionOf_restrict_toSuccession_of_pullback`;
  `val_stageMap_restrict` reads its composite blow-down in `M`).

The auxiliaries `stageMapLE` and `centerAt` of the definition are used directly.
-/

public section

noncomputable section

open Set Topology TopologicalSpace AnalyticManifold Manifold
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E}

/-! ### The composite `stageMapLE` between two stages -/

/-- At equal indices the composite `σ_{a+1} ∘ ⋯ ∘ σ_a` is the identity. -/
theorem stageMapLE_self (S : FiniteSuccession M) (a : Fin (S.length + 1)) (h : a ≤ a) :
    stageMapLE S h = ContMDiffMap.id := by
  unfold stageMapLE
  rw [Nat.leRecOn_self]

/-- One more step: the composite to `b + 1` is the composite to `b` after `σ_{b+1}`. -/
theorem stageMapLE_succ (S : FiniteSuccession M) {a : Fin (S.length + 1)} {b : Fin S.length}
    (h : a ≤ b.succ) (h' : a ≤ b.castSucc) :
    stageMapLE S h = (stageMapLE S h').comp (S.map b) := by
  unfold stageMapLE
  rw [Nat.leRecOn_succ h']
  rfl

/-- `ℕ`-indexed. -/
theorem stageMapLE_zero_left_aux (S : FiniteSuccession M) :
    ∀ (m : ℕ) (hm : m < S.length + 1) (h : (0 : Fin (S.length + 1)) ≤ ⟨m, hm⟩),
      stageMapLE S h = S.stageMap ⟨m, hm⟩
  | 0, hm, h => stageMapLE_self S _ h
  | m + 1, hm, h => by
    rw [stageMapLE_succ S (b := ⟨m, Nat.lt_of_succ_lt_succ hm⟩) h (Fin.zero_le _),
      stageMapLE_zero_left_aux S m (Nat.lt_of_succ_lt hm) (Fin.zero_le _)]
    rfl

/-- From stage `0`: the composite `σ_1 ∘ ⋯ ∘ σ_b` is the composite blow-down `σ^b`
(`stageMap`) — so at a stage identified with stage `0` the intertwining clause of `IsExtensionOf` is
its "over `M`" clause. -/
theorem stageMapLE_zero_left (S : FiniteSuccession M) (b : Fin (S.length + 1)) (h : 0 ≤ b) :
    stageMapLE S h = S.stageMap b :=
  stageMapLE_zero_left_aux S b.1 b.2 h

/-- By the distance `d` between the two stages. -/
theorem stageMapLE_cons_aux {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (R : FiniteSuccession (blowUp ψ₀ hY))
    (a : Fin (R.length + 1)) :
    ∀ (d : ℕ) (hd : a.1 + d < R.length + 1) (h : a.succ ≤ (⟨a.1 + d, hd⟩ : Fin _).succ)
      (h' : a ≤ ⟨a.1 + d, hd⟩), stageMapLE (cons ψ₀ hY R) h = stageMapLE R h'
  | 0, hd, h, h' => (stageMapLE_self _ _ h).trans (stageMapLE_self _ _ h').symm
  | d + 1, hd, h, h' => by
    have hd₀ : a.1 + d < R.length + 1 := Nat.lt_of_succ_lt hd
    have hdR : a.1 + d < R.length := Nat.lt_of_succ_lt_succ hd
    have h₁ : a.succ ≤ (⟨a.1 + d, hd₀⟩ : Fin (R.length + 1)).succ :=
      Fin.mk_le_mk.mpr (Nat.succ_le_succ (Nat.le_add_right _ _))
    have h₂ : a ≤ (⟨a.1 + d, hd₀⟩ : Fin (R.length + 1)) := Fin.mk_le_mk.mpr (Nat.le_add_right _ _)
    exact (stageMapLE_succ (cons ψ₀ hY R) (b := ⟨a.1 + (d + 1), hd⟩) h h₁).trans
      ((congrArg (fun f => f.comp (R.map ⟨a.1 + d, hdR⟩))
        (stageMapLE_cons_aux hY R a d hd₀ h₁ h₂)).trans
        (stageMapLE_succ R (b := ⟨a.1 + d, hdR⟩) h' h₂).symm)

/-- On `cons hY R` between two later stages the composite is `R`'s composite. -/
theorem stageMapLE_cons {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (R : FiniteSuccession (blowUp ψ₀ hY))
    {a b : Fin (R.length + 1)} (h : a.succ ≤ b.succ) (h' : a ≤ b) :
    stageMapLE (cons ψ₀ hY R) h = stageMapLE R h' := by
  obtain ⟨bv, hbv⟩ := b
  have hab : a.1 ≤ bv := h'
  obtain ⟨d, rfl⟩ : ∃ d, bv = a.1 + d := ⟨bv - a.1, by omega⟩
  exact stageMapLE_cons_aux hY R a d hbv h h'

/-! ### The extension relation: reflexivity and composition with a stage-wise isomorphism -/

/-- The pull-back of an ideal sheaf along the identity diffeomorphism is the ideal sheaf. -/
theorem comap_diffeomorph_refl (J : IdealSheaf M) :
    J.pullback ⇑(Diffeomorph.refl 𝓘(𝕜, E) M ω) (Diffeomorph.refl 𝓘(𝕜, E) M ω).contMDiff = J
            := by
  rw [IdealSheaf.pullback_congr J _ contMDiff_id (Diffeomorph.coe_refl _ _ _)]
  exact IdealSheaf.pullback_id_eq_self J

/-- The pull-back along a composite of diffeomorphisms is the iterated pull-back. -/
theorem comap_diffeomorph_trans {A B C : AnalyticManifold.{u} 𝕜 E}
    (e₁ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) A B ω) (e₂ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) B C ω)
    (J : IdealSheaf C) :
    J.pullback ⇑(e₁.trans e₂) (e₁.trans e₂).contMDiff =
      (J.pullback ⇑e₂ e₂.contMDiff).pullback ⇑e₁ e₁.contMDiff := by
  rw [IdealSheaf.pullback_pullback J ⇑e₂ e₂.contMDiff ⇑e₁ e₁.contMDiff]
  exact IdealSheaf.pullback_congr J _ _ (Diffeomorph.coe_trans e₁ e₂)

/-- Every succession is an extension of itself (the block index the identity). -/
theorem IsExtensionOf.refl (S : FiniteSuccession M) : S.IsExtensionOf S := by
  refine ⟨id, fun k => Diffeomorph.refl _ _ _, rfl, rfl, fun k => Or.inr (by simp),
    fun k p => rfl, fun k hle p => ?_, fun k ha _ => ?_, fun k hk => ?_⟩
  · rw [stageMapLE_succ S (b := k) hle le_rfl, stageMapLE_self]
    rfl
  · exact Eq.symm (comap_diffeomorph_refl _)
  · exact absurd hk (by simp)

/-- A succession `T` stage-wise isomorphic OVER `M` to `S` (same length, the
isomorphisms intertwining the maps and carrying the centres) is an extension of everything `S` is
an extension of: compose the block index with the identity and the identifications. -/
theorem IsExtensionOf.of_stageEquiv_left {T S R : FiniteSuccession M} (hlen : T.length = S.length)
    (e : ∀ k : Fin (T.length + 1),
      Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (T.stage k) (S.stage (Fin.cast (congrArg (· + 1) hlen) k)) ω)
    (hover : ∀ (k : Fin (T.length + 1)) (p : T.stage k),
      S.stageMap (Fin.cast (congrArg (· + 1) hlen) k) (e k p) = T.stageMap k p)
    (hmap : ∀ (k : Fin T.length) (p : T.stage k.succ),
      S.map (Fin.cast hlen k) (e k.succ p) = e k.castSucc (T.map k p))
    (hcenter : ∀ k : Fin T.length,
      T.center k =
        (S.center (Fin.cast hlen k)).pullback ⇑(e k.castSucc) (e k.castSucc).contMDiff)
    (hSR : S.IsExtensionOf R) : T.IsExtensionOf R := by
  obtain ⟨b, e₂, h0, hl, hs, ho, hm, hc, hn⟩ := hSR
  refine ⟨fun k => b (Fin.cast (congrArg (· + 1) hlen) k),
    fun k => (e k).trans (e₂ (Fin.cast (congrArg (· + 1) hlen) k)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : Fin.cast (congrArg (· + 1) hlen) (0 : Fin (T.length + 1)) = 0 := Fin.ext rfl
    change b (Fin.cast (congrArg (· + 1) hlen) 0) = 0
    rw [this, h0]
  · have : Fin.cast (congrArg (· + 1) hlen) (Fin.last T.length) = Fin.last S.length :=
      Fin.ext hlen
    change b (Fin.cast (congrArg (· + 1) hlen) (Fin.last T.length)) = Fin.last R.length
    rw [this, hl]
  · intro k
    exact hs (Fin.cast hlen k)
  · intro k p
    exact (ho (Fin.cast (congrArg (· + 1) hlen) k) (e k p)).trans (hover k p)
  · intro k hle p
    have := hm (Fin.cast hlen k) hle (e k.succ p)
    rw [hmap k p] at this
    exact this
  · intro k ha hstep
    rw [hcenter k, hc (Fin.cast hlen k) ha hstep]
    exact Eq.symm (comap_diffeomorph_trans _ _ _)
  · intro k hstep
    rw [hcenter k]
    change (IdealSheaf.pullback _ _ (S.center (Fin.cast hlen k))).support = ∅
    rw [IdealSheaf.support_pullback]
    change ⇑(e k.castSucc) ⁻¹' (S.center (Fin.cast hlen k)).support = ∅
    rw [hn (Fin.cast hlen k) hstep]
    exact Set.preimage_empty

/-! ### The restriction to an open, read in `M` -/

/-- `ℕ`-indexed: the composite blow-down of the restriction at a later stage, in `M`. -/
theorem val_stageMap_restrict_aux {U₁ U₂ : Opens M} (S : FiniteSuccession (M.restrict U₂))
    (h : U₁ ≤ U₂) :
    ∀ (m : ℕ) (hm : m + 1 < S.length + 1) (p : (S.restrict h).stage ⟨m + 1, hm⟩),
      ((S.restrict h).stageMap ⟨m + 1, hm⟩ p).1 = (S.stageMap ⟨m + 1, hm⟩ p.1).1
  | 0, _, _ => rfl
  | m + 1, hm, p =>
    val_stageMap_restrict_aux S h m (Nat.lt_of_succ_lt hm)
      ((S.restrict h).map ⟨m + 1, Nat.lt_of_succ_lt_succ hm⟩ p)

/-- The composite blow-down of the restriction at a later stage, read in `M`, is
the composite blow-down of the succession at the point (the traces are open submanifolds and the
restricted maps are the maps). -/
theorem val_stageMap_restrict {U₁ U₂ : Opens M} (S : FiniteSuccession (M.restrict U₂))
    (h : U₁ ≤ U₂) (k : Fin S.length) (p : (S.restrict h).stage k.succ) :
    ((S.restrict h).stageMap k.succ p).1 = (S.stageMap k.succ p.1).1 :=
  val_stageMap_restrict_aux S h k.1 k.succ.2 p

end AnalyticManifold.FiniteSuccession

namespace AnalyticManifold.BlowUpSequence

open Manifold Hironaka.Manifold
open AnalyticManifold.FiniteSuccession (stageMapLE centerAt)

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

/-- By the distance between the two stages. -/
theorem stageMapLE_pullbackLift_aux (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (a : Fin (L.length + 1)) :
    ∀ (d : ℕ) (hd : a.1 + d < L.length + 1) (hab : a ≤ ⟨a.1 + d, hd⟩)
      (hab' : (⟨a.1, Nat.lt_of_lt_of_eq a.2 (congrArg (· + 1) (length_pullback L h hh).symm)⟩ :
          Fin ((L.pullback h hh).length + 1)) ≤
        ⟨a.1 + d, Nat.lt_of_lt_of_eq hd (congrArg (· + 1) (length_pullback L h hh).symm)⟩)
      (q : (L.pullback h hh).stage
        ⟨a.1 + d, Nat.lt_of_lt_of_eq hd (congrArg (· + 1) (length_pullback L h hh).symm)⟩),
      stageMapLE L.toSuccession hab (L.pullbackLift h hh ⟨a.1 + d, hd⟩ q) =
        L.pullbackLift h hh a (stageMapLE (L.pullback h hh).toSuccession hab' q)
  | 0, hd, hab, hab', q => by
    rw [FiniteSuccession.stageMapLE_self _ _ hab, FiniteSuccession.stageMapLE_self _ _ hab']
    rfl
  | d + 1, hd, hab, hab', q => by
    have hd₀ : a.1 + d < L.length + 1 := Nat.lt_of_succ_lt hd
    have hd₀' : a.1 + d < (L.pullback h hh).length + 1 :=
      Nat.lt_of_lt_of_eq hd₀ (congrArg (· + 1) (length_pullback L h hh).symm)
    have h₂ : a ≤ (⟨a.1 + d, hd₀⟩ : Fin (L.length + 1)) := Fin.mk_le_mk.mpr (Nat.le_add_right _ _)
    have h₂' : (⟨a.1, Nat.lt_of_lt_of_eq a.2 (congrArg (· + 1) (length_pullback L h hh).symm)⟩ :
        Fin ((L.pullback h hh).length + 1)) ≤ ⟨a.1 + d, hd₀'⟩ :=
      Fin.mk_le_mk.mpr (Nat.le_add_right _ _)
    have hb : (⟨a.1 + d, Nat.lt_of_succ_lt_succ hd⟩ : Fin L.length).succ = ⟨a.1 + (d + 1), hd⟩ :=
      rfl
    calc stageMapLE L.toSuccession hab (L.pullbackLift h hh ⟨a.1 + (d + 1), hd⟩ q)
        = (stageMapLE L.toSuccession h₂).comp (L.toSuccession.map ⟨a.1 + d, _⟩)
            (L.pullbackLift h hh ⟨a.1 + (d + 1), hd⟩ q) :=
          congrArg (fun f => f (L.pullbackLift h hh ⟨a.1 + (d + 1), hd⟩ q))
            (FiniteSuccession.stageMapLE_succ L.toSuccession
              (b := ⟨a.1 + d, Nat.lt_of_succ_lt_succ hd⟩) hab h₂)
      _ = stageMapLE L.toSuccession h₂ (L.pullbackLift h hh ⟨a.1 + d, hd₀⟩
            ((L.pullback h hh).toSuccession.map ⟨a.1 + d, _⟩ q)) :=
          congrArg (stageMapLE L.toSuccession h₂)
            (map_pullbackLift L h hh ⟨a.1 + d, Nat.lt_of_succ_lt_succ hd⟩ q).symm
      _ = L.pullbackLift h hh a (stageMapLE (L.pullback h hh).toSuccession h₂'
            ((L.pullback h hh).toSuccession.map ⟨a.1 + d, _⟩ q)) :=
          stageMapLE_pullbackLift_aux L h hh a d hd₀ h₂ h₂' _
      _ = L.pullbackLift h hh a (stageMapLE (L.pullback h hh).toSuccession hab' q) :=
          congrArg (L.pullbackLift h hh a)
            (congrArg (fun f => f q) (FiniteSuccession.stageMapLE_succ
              (L.pullback h hh).toSuccession
              (b := ⟨a.1 + d, Nat.lt_of_lt_of_eq (Nat.lt_of_succ_lt_succ hd)
                (length_pullback L h hh).symm⟩) hab' h₂')).symm

/-- The stage lifts intertwine the composites `stageMapLE` between any two stages
(`map_pullbackLift` along `Nat.leRecOn`). -/
theorem stageMapLE_pullbackLift (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {a b : Fin (L.length + 1)} (hab : a ≤ b)
    (hab' : (⟨a.1, Nat.lt_of_lt_of_eq a.2 (congrArg (· + 1) (length_pullback L h hh).symm)⟩ :
        Fin ((L.pullback h hh).length + 1)) ≤
      ⟨b.1, Nat.lt_of_lt_of_eq b.2 (congrArg (· + 1) (length_pullback L h hh).symm)⟩)
    (q : (L.pullback h hh).stage
      ⟨b.1, Nat.lt_of_lt_of_eq b.2 (congrArg (· + 1) (length_pullback L h hh).symm)⟩) :
    stageMapLE L.toSuccession hab (L.pullbackLift h hh b q) =
      L.pullbackLift h hh a (stageMapLE (L.pullback h hh).toSuccession hab' q) := by
  obtain ⟨bv, hbv⟩ := b
  have hab₀ : a.1 ≤ bv := hab
  obtain ⟨d, rfl⟩ : ∃ d, bv = a.1 + d := ⟨bv - a.1, by omega⟩
  exact stageMapLE_pullbackLift_aux L h hh a d hbv hab hab' q

/-! ### A list's succession is an extension of its cleaned list's succession -/

/-- (a jump). Prepending the same centre to both lists keeps the extension: the first step of
`cons hY rest` is the first step of `cons hY R`, the identification there the identity. -/
theorem isExtensionOf_toSuccession_cons {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
    {rest R : BlowUpSequence ψ₀ (blowUp ψ₀ hY)} (hR : rest.toSuccession.IsExtensionOf
        R.toSuccession) :
    (cons hY rest).toSuccession.IsExtensionOf (cons hY R).toSuccession := by
  obtain ⟨b, e, h0, hl, hs, ho, hm, hc, hn⟩ := hR
  refine ⟨Fin.cases 0 fun k => (b k).succ, Fin.cases (Diffeomorph.refl _ _ _) fun k => e k,
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (b (Fin.last rest.length)).succ = Fin.last (R.length + 1)
    rw [hl]
    rfl
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · refine Or.inr ?_
      change ((b 0).succ : ℕ) = ((0 : Fin (R.length + 1 + 1)) : ℕ) + 1
      rw [Fin.val_succ, h0]
      rfl
    · have := hs j
      change ((b j.succ).succ : ℕ) = (b j.castSucc).succ ∨
        ((b j.succ).succ : ℕ) = (b j.castSucc).succ + 1
      simp only [Fin.val_succ]
      omega
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · intro p
      rfl
    · intro p
      change (cons hY R).toSuccession.stageMapAux ((b j).1 + 1) _ (e j p) =
        (cons hY rest).toSuccession.stageMapAux (j.1 + 1) _ p
      exact (stageMapAux_cons_succ hY R (b j).1 _ (e j p)).trans
        ((congrArg (blowUpπ ψ₀ hY) (ho j p)).trans (stageMapAux_cons_succ hY rest j.1 _ p).symm)
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · intro hle p
      exact (congrArg (fun f => f (e 0 p))
          (FiniteSuccession.stageMapLE_zero_left (cons hY R).toSuccession (b 0).succ hle)).trans
        ((stageMapAux_cons_succ hY R (b 0).1 _ (e 0 p)).trans (congrArg (blowUpπ ψ₀ hY) (ho 0 p)))
    · intro hle p
      have hle₀ : b j.castSucc ≤ b j.succ := Fin.succ_le_succ_iff.mp hle
      exact (congrArg (fun f => f (e j.succ p))
          (FiniteSuccession.stageMapLE_cons hY R.toSuccession (a := b j.castSucc) (b := b j.succ)
            hle hle₀)).trans (hm j hle₀ p)
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · intro ha _
      exact (FiniteSuccession.comap_diffeomorph_refl _).symm
    · intro ha hstep
      have ha' : (b j.castSucc : ℕ) < R.length := Nat.lt_of_succ_lt_succ ha
      have hstep' : (b j.succ : ℕ) = b j.castSucc + 1 := by
        change ((b j.succ).succ : ℕ) = (b j.castSucc).succ + 1 at hstep
        simp only [Fin.val_succ] at hstep
        omega
      exact hc j ha' hstep'
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · intro hk
      change ((b 0).succ : ℕ) = ((0 : Fin (R.length + 1 + 1)) : ℕ) at hk
      exact absurd hk (Nat.succ_ne_zero _)
    · intro hk
      have hk' : (b j.succ : ℕ) = b j.castSucc := by
        change ((b j.succ).succ : ℕ) = (b j.castSucc).succ at hk
        simpa using hk
      exact hn j hk'

/-- (a non-jump). Prepending an EMPTY centre to `rest` and transporting `R` back along the
isomorphism `Bl_∅ M ≃ M` of the empty blowing-up (the step `eraseEmpty` performs) keeps the
extension: the first step of `cons hY rest` is the non-jump `e 1 = Bl_∅ M ≃ M`, over `M` by
`emptyBlowUpDiffeomorph_apply`; the later identifications are `R`'s followed by the inverses of the
stage lifts of `g⁻¹` (`map_eq_pullback_symm`). -/
theorem isExtensionOf_toSuccession_cons_of_eq_empty {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (hY₀ : Y = ∅) {rest R : BlowUpSequence ψ₀ (blowUp ψ₀ hY)}
    (hR : rest.toSuccession.IsExtensionOf R.toSuccession) :
    (cons hY rest).toSuccession.IsExtensionOf
      (R.map (emptyBlowUpDiffeomorph hY hY₀)).toSuccession := by
  have : FiniteDimensional 𝕜 E := ψ₀.symm.toLinearEquiv.finiteDimensional
  rw [map_eq_pullback_symm]
  set g := emptyBlowUpDiffeomorph hY hY₀ with hg
  set g' : AnalyticMap M (blowUp ψ₀ hY) := Diffeomorph.toAnalyticMap g.symm with hg'
  have hg'd : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g' := g.symm.isLocalDiffeomorph
  have hinj : Function.Injective g' := g.symm.injective
  have hsurj : Function.Surjective g' := g.symm.surjective
  have hlen : (R.pullback g' hg'd).length = R.length := length_pullback R g' hg'd
  let d : ∀ j : Fin (R.length + 1), Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E)
      ((R.pullback g' hg'd).stage ⟨j.1, Nat.lt_of_lt_of_eq j.2 (congrArg (· + 1) hlen.symm)⟩)
      (R.stage j) ω :=
    fun j => (isLocalDiffeomorph_pullbackLift R g' hg'd j).toDiffeomorphOfBijective
      ⟨injective_pullbackLift R g' hg'd hinj j, surjective_pullbackLift R g' hg'd hsurj j⟩
  have hd : ∀ (j : Fin (R.length + 1)) q, d j q = R.pullbackLift g' hg'd j q := fun _ _ => rfl
  have hgg' : ∀ y, g (g' y) = y := fun y => g.apply_symm_apply y
  obtain ⟨b, e, h0, hl, hs, ho, hm, hc, hn⟩ := hR
  -- the later stages lie over `M` through `Bl_∅ M ≃ M`
  have hover' : ∀ (j : Fin (rest.length + 1)) (p : rest.stage j),
      (R.pullback g' hg'd).toSuccession.stageMap
          ⟨(b j).1, Nat.lt_of_lt_of_eq (b j).2 (congrArg (· + 1) hlen.symm)⟩
          ((d (b j)).symm (e j p)) =
        blowUpπ ψ₀ hY (rest.toSuccession.stageMap j p) := by
    intro j p
    have h1 := stageMap_pullbackLift R g' hg'd (b j) ((d (b j)).symm (e j p))
    rw [← hd, Diffeomorph.apply_symm_apply, ho j p] at h1
    have h2 := congrArg g h1
    rw [hgg', emptyBlowUpDiffeomorph_apply] at h2
    exact h2.symm
  refine ⟨Fin.cases 0 fun k => ⟨(b k).1, Nat.lt_of_lt_of_eq (b k).2 (congrArg (· + 1) hlen.symm)⟩,
    Fin.cases (Diffeomorph.refl _ _ _) fun k => (e k).trans (d (b k)).symm, rfl, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · apply Fin.ext
    change (b (Fin.last rest.length) : ℕ) = (R.pullback g' hg'd).length
    rw [hl]
    exact hlen.symm
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · refine Or.inl ?_
      change (b 0 : ℕ) = ((0 : Fin ((R.pullback g' hg'd).length + 1)) : ℕ)
      rw [h0]
      rfl
    · exact hs j
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · intro p
      rfl
    · intro p
      change (R.pullback g' hg'd).toSuccession.stageMap _ ((d (b j)).symm (e j p)) =
        (cons hY rest).toSuccession.stageMapAux (j.1 + 1) _ p
      rw [hover' j p, stageMapAux_cons_succ]
      rfl
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · intro hle p
      exact (congrArg (fun f => f ((d (b 0)).symm (e 0 p)))
          (FiniteSuccession.stageMapLE_zero_left (R.pullback g' hg'd).toSuccession
            ⟨(b 0).1, Nat.lt_of_lt_of_eq (b 0).2 (congrArg (· + 1) hlen.symm)⟩ hle)).trans
        (hover' 0 p)
    · intro hle p
      have hle₀ : b j.castSucc ≤ b j.succ := hle
      have h1 := stageMapLE_pullbackLift R g' hg'd hle₀ hle ((d (b j.succ)).symm (e j.succ p))
      have h2 : R.pullbackLift g' hg'd (b j.succ) ((d (b j.succ)).symm (e j.succ p)) =
          e j.succ p := (d (b j.succ)).apply_symm_apply _
      rw [h2] at h1
      refine (Diffeomorph.symm_apply_apply (d (b j.castSucc)) _).symm.trans
        (congrArg (d (b j.castSucc)).symm ?_)
      exact h1.symm.trans (hm j hle₀ p)
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · intro _ hstep
      change (b 0 : ℕ) = ((0 : Fin ((R.pullback g' hg'd).length + 1)) : ℕ) + 1 at hstep
      rw [h0] at hstep
      exact absurd hstep (by simp)
    · intro ha hstep
      have ha' : (b j.castSucc : ℕ) < R.length := hlen ▸ ha
      have hP : (R.pullback g' hg'd).toSuccession.center ⟨(b j.castSucc).1, ha⟩ =
          (R.toSuccession.center ⟨(b j.castSucc).1, ha'⟩).pullback _ (R.pullbackLift g' hg'd (b
              j.castSucc)).contMDiff :=
        center_pullback R g' hg'd ⟨(b j.castSucc).1, ha'⟩
      have hcomp : (⇑(R.pullbackLift g' hg'd (b j.castSucc)) ∘ ⇑(d (b j.castSucc)).symm) = id :=
        funext fun x => (d (b j.castSucc)).apply_symm_apply x
      have hℓ : (((R.toSuccession.center ⟨(b j.castSucc).1, ha'⟩).pullback _ (R.pullbackLift g'
          hg'd (b j.castSucc)).contMDiff).pullback
          ⇑(d (b j.castSucc)).symm (d (b j.castSucc)).symm.contMDiff) =
          R.toSuccession.center ⟨(b j.castSucc).1, ha'⟩ := by
        change IdealSheaf.pullback ⇑(d (b j.castSucc)).symm _
          (IdealSheaf.pullback ⇑(R.pullbackLift g' hg'd (b j.castSucc)) _ _) = _
        rw [IdealSheaf.pullback_pullback, IdealSheaf.pullback_congr _ _ contMDiff_id hcomp]
        exact IdealSheaf.pullback_id_eq_self _
      change rest.toSuccession.center j =
        (centerAt (R.pullback g' hg'd).toSuccession
            ⟨(b j.castSucc).1, Nat.lt_of_lt_of_eq (b j.castSucc).2 (congrArg (· + 1) hlen.symm)⟩
            ha).pullback
          ⇑((e j.castSucc).trans (d (b j.castSucc)).symm) ((e j.castSucc).trans (d (b
              j.castSucc)).symm).contMDiff
      rw [FiniteSuccession.comap_diffeomorph_trans, hc j ha' hstep]
      change (R.toSuccession.center ⟨(b j.castSucc).1, ha'⟩).pullback _ _ =
        (((R.pullback g' hg'd).toSuccession.center ⟨(b j.castSucc).1, ha⟩).pullback _ _).pullback
          _ _
      rw [hP, hℓ]
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · intro _
      change hY.idealSheaf.support = ∅
      rw [hY.cosupport_idealSheaf]
      exact hY₀
    · intro hk
      exact hn j hk

/-- The remark following [Wlo09, Definition 3.2.6], with [Kol07, 32] and [Kol07, 34.1]: a list's
succession is an extension of its cleaned list's succession, by recursion on the list
(`isExtensionOf_toSuccession_cons`, `isExtensionOf_toSuccession_cons_of_eq_empty`). -/
theorem isExtensionOf_toSuccession_eraseEmpty : ∀ {M : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M), L.toSuccession.IsExtensionOf L.eraseEmpty.toSuccession
  | _, nil _ => FiniteSuccession.IsExtensionOf.refl _
  | _, @cons _ _ _ _ _ _ _ _ Y _ hY rest => by
    by_cases hY₀ : Y = ∅
    · rw [eraseEmpty_cons_of_eq_empty hY rest hY₀]
      exact isExtensionOf_toSuccession_cons_of_eq_empty hY hY₀
        (isExtensionOf_toSuccession_eraseEmpty rest)
    · rw [eraseEmpty_cons_of_ne_empty hY rest hY₀]
      exact isExtensionOf_toSuccession_cons hY (isExtensionOf_toSuccession_eraseEmpty rest)

/-! ### The restriction to an open against the pull-back along the open inclusion -/

/-- ([Wlo09, Theorem 2.0.3] (4)). For a list `L` over `U₂` and `U₁ ≤ U₂`, the
restriction of its succession to `U₁` is an extension of everything the succession of
its pull-back along the open inclusion is an extension of — the two are stage-wise isomorphic over
`U₁`: stage `0` is `U₁` on both sides, and at a later stage the lift `h_i` of the inclusion is a
diffeomorphism from the pull-back's stage onto the trace (`pullbackLiftDiffeomorph`). -/
theorem isExtensionOf_restrict_toSuccession_of_pullback {U₁ U₂ : Opens M}
    (L : BlowUpSequence ψ₀ (M.restrict U₂)) (h : U₁ ≤ U₂) {R : FiniteSuccession (M.restrict U₁)}
    (hR : (L.pullback (M.restrictLE h) (isLocalDiffeomorph_restrictLE h)).toSuccession.IsExtensionOf
      R) :
    (L.toSuccession.restrict h).IsExtensionOf R := by
  have : FiniteDimensional 𝕜 E := ψ₀.symm.toLinearEquiv.finiteDimensional
  set ι := M.restrictLE h with hι
  have hιd : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ι := isLocalDiffeomorph_restrictLE h
  have hinj : Function.Injective ι := (isAnalyticOpenEmbedding_restrictLE h).2
  set P := L.pullback ι hιd with hP
  -- the traces of `U₁` on the later stages
  let V : ∀ j : Fin L.length, Opens (L.stage j.succ) := fun j =>
    ⟨(fun p : L.stage j.succ => (L.toSuccession.stageMap j.succ p).1) ⁻¹' (U₁ : Set M),
      U₁.2.preimage (continuous_subtype_val.comp
        (L.toSuccession.stageMap j.succ).contMDiff.continuous)⟩
  have hV : ∀ j : Fin L.length, (V j : Set (L.stage j.succ)) =
      ⇑(L.toSuccession.stageMap j.succ) ⁻¹' Set.range ι := by
    intro j
    ext p
    rw [Set.mem_preimage, hι, range_restrictLE]
    exact Iff.rfl
  let D : ∀ j : Fin L.length, Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E)
      (P.stage ⟨j.succ.1,
        Nat.lt_of_lt_of_eq j.succ.2 (congrArg (· + 1) (length_pullback L ι hιd).symm)⟩)
      ((L.stage j.succ).restrict (V j)) ω :=
    fun j => L.pullbackLiftDiffeomorph ι hιd hinj j.succ (V j) (hV j)
  have hD : ∀ (j : Fin L.length) q, (D j q).1 = L.pullbackLift ι hιd j.succ q := fun _ _ => rfl
  have hDsymm : ∀ (j : Fin L.length) (x : (L.toSuccession.restrict h).stage j.succ),
      L.pullbackLift ι hιd j.succ ((D j).symm x) = x.1 := fun j x =>
    congrArg Subtype.val ((D j).apply_symm_apply x)
  have hlen : (L.toSuccession.restrict h).length = P.toSuccession.length :=
    (length_pullback L ι hιd).symm
  refine FiniteSuccession.IsExtensionOf.of_stageEquiv_left hlen
    (fun k => Fin.cases (Diffeomorph.refl _ _ _) (fun j => (D j).symm) k) ?_ ?_ ?_ hR
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · intro p
      rfl
    · intro p
      apply Subtype.ext
      have h1 := stageMap_pullbackLift L ι hιd j.succ ((D j).symm p)
      exact (congrArg Subtype.val h1).symm.trans
        ((congrArg (fun y => (L.toSuccession.stageMap j.succ y).1) (hDsymm j p)).trans
          (FiniteSuccession.val_stageMap_restrict L.toSuccession h j p).symm)
  · rintro ⟨k, hk⟩ p
    cases k with
    | zero =>
      have h1 := map_pullbackLift L ι hιd ⟨0, hk⟩ ((D ⟨0, hk⟩).symm p)
      have h0 : L.pullbackLift ι hιd (Fin.castSucc ⟨0, hk⟩) = ι := pullbackLift_zero L ι hιd
      rw [h0] at h1
      exact Subtype.ext ((congrArg Subtype.val h1).trans
        (congrArg (fun y => (L.toSuccession.map ⟨0, hk⟩ y).1) (hDsymm ⟨0, hk⟩ p)))
    | succ j =>
      refine ((D ⟨j, Nat.lt_of_succ_lt hk⟩).symm_apply_apply _).symm.trans
        (congrArg (D ⟨j, Nat.lt_of_succ_lt hk⟩).symm ?_)
      have h1 := map_pullbackLift L ι hιd ⟨j + 1, hk⟩ ((D ⟨j + 1, hk⟩).symm p)
      exact Subtype.ext (h1.trans
        (congrArg (L.toSuccession.map ⟨j + 1, hk⟩) (hDsymm ⟨j + 1, hk⟩ p)))
  · rintro ⟨k, hk⟩
    cases k with
    | zero =>
      have h0 : L.pullbackLift ι hιd (Fin.castSucc ⟨0, hk⟩) = ι := pullbackLift_zero L ι hιd
      have hk' : 0 < P.toSuccession.length := Nat.lt_of_lt_of_eq hk (length_pullback L ι hιd).symm
      have hz : (P.toSuccession.center ⟨0, hk'⟩).pullback ⇑(Diffeomorph.refl 𝓘(𝕜, E) (M.restrict
          U₁) ω) (Diffeomorph.refl 𝓘(𝕜, E) (M.restrict U₁) ω).contMDiff =
          P.toSuccession.center ⟨0, hk'⟩ := FiniteSuccession.comap_diffeomorph_refl _
      change (L.toSuccession.center ⟨0, hk⟩).pullback ι ι.contMDiff =
        (P.toSuccession.center ⟨0, hk'⟩).pullback ⇑(Diffeomorph.refl 𝓘(𝕜, E) (M.restrict U₁) ω)
            (Diffeomorph.refl 𝓘(𝕜, E) (M.restrict U₁) ω).contMDiff
      rw [hz, center_pullback L ι hιd ⟨0, hk⟩, h0]
      rfl
    | succ j =>
      change (L.toSuccession.center ⟨j + 1, hk⟩).pullback _ ((L.stage ⟨j + 1, Nat.lt_succ_of_lt
          hk⟩).inclusion (V ⟨j, Nat.lt_of_succ_lt hk⟩)).contMDiff =
        (P.toSuccession.center ⟨j + 1, _⟩).pullback ⇑(D ⟨j, Nat.lt_of_succ_lt hk⟩).symm (D ⟨j,
            Nat.lt_of_succ_lt hk⟩).symm.contMDiff
      rw [center_pullback L ι hιd ⟨j + 1, hk⟩]
      change IdealSheaf.pullback _ _ (L.toSuccession.center ⟨j + 1, hk⟩) =
        IdealSheaf.pullback _ _ (IdealSheaf.pullback _ _ (L.toSuccession.center ⟨j + 1, hk⟩))
      rw [IdealSheaf.pullback_pullback]
      exact IdealSheaf.pullback_congr _ _ _
        (funext fun x => (hDsymm ⟨j, Nat.lt_of_succ_lt hk⟩ x).symm)

end AnalyticManifold.BlowUpSequence

end
