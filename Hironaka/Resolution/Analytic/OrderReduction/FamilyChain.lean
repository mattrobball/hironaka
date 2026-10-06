/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.ConcatPullback
public import Hironaka.Resolution.Analytic.OrderReduction.Basic
import Hironaka.Manifold.FiniteSuccession.Functor.LocalCover
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The shrinking chain of Step 2.1 in the compatible-family form: general tools

In the compatible-family form of the order-reduction functors ([Wlo09, Theorem 2.0.3 (1), (4)];
the remark after [BM97, Theorem 1.6] on locally finite sequences), the value of Step 2.1 of the
proof of [Kol07, Theorem 103] on a relatively compact open `U` is computed along a finite shrinking
chain `U ⊆ W_r ⋐ ⋯ ⋐ W_0 ⊆ M` of relatively compact opens, each with closure in the previous one.
Each factor (Lemma 102's family at one boundary member, later Step 2.2) is a compatible family on
the induced triple at the last stage of the sequence built so far, and can only be read on a
relatively compact open of that last stage; the preimage of the next, smaller open of the chain is
such an open, by the properness of the composite blow-down. The sequence built so far is then
restricted to the smaller open (pulled back along the open inclusion), the factor's value is
carried to the restricted sequence's last stage along the lift of the inclusion, and the two are
concatenated. This module holds the general pieces of that step:

* `AnalyticMap.corestrict f V h` — the corestriction of an analytic map onto an open `V`
  containing its range, a local analytic isomorphism when `f` is (`isLocalDiffeomorph_corestrict`)
  and surjective when the range is `V` (`surjective_corestrict`);
* `FiniteSuccession.isProperMap_stageMap` — the composite blow-down of a finite succession of
  blow-ups is proper, so the preimage of a relatively compact open is relatively compact;
* `BlowUpSequence.stageMap_last_pullbackLiftLast`, `range_pullbackLiftLast_subset` — the last-stage
  lift of a local analytic isomorphism `h` along a sequence of centres lies over `h`
  (`σ^r ∘ h_r = h ∘ σ'^r`, the pull-back of blow-up sequences of [Kol07, Definition 30 (30.1)]
  composed along the sequence), so its range lies in the preimage of the range of `h`;
* `BlowUpSequence.liftRange`, `isCompact_closure_liftRange`, `liftCorestrict` — the **reading
  open**, the range of the last-stage lift of `h` on the last stage of `L`, relatively compact when
  the range of `h` is, and the lift corestricted onto it (a surjective local analytic isomorphism);
* `BlowUpSequence.shrinkAppend L h hh L'` — the **shrink-and-append step**: the pull-back of `L`
  along `h`, followed by a sequence `L'` on the reading open carried along the corestricted lift;
* `AnalyticTriple.boClass_pullback_of_isLocalDiffeomorph`, `BlowUpSequence.stage_last_concat` — the
  class `BOClass m` is stable under pull-back of the triple along a local analytic isomorphism, and
  the last stage of a concatenation is that of the second sequence.

The order clause of the step is proved in `FamilyOrder.lean`; the chain itself is built in
`Step21Fam.lean`, and the same step drives the construction of Theorem 107 in the
compatible-family form (`ChainState.linkWith`, `Step21Fam.lean`).
-/

@[expose] public section

universe u

open Set TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### Corestriction onto an open containing the range -/

section Corestrict

variable {N M : AnalyticManifold.{u} 𝕜 E} (f : AnalyticMap N M) (V : Opens M)

/-- The corestriction of an analytic map `f : N → M` onto an open `V ⊇ range f`, as an analytic map
`N → M.restrict V`. -/
def AnalyticMap.corestrict (h : Set.range f ⊆ V) : AnalyticMap N (M.restrict V) :=
  ⟨fun p => ⟨f p, h (Set.mem_range_self p)⟩, fun p => by
    have hval : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω
        ((Subtype.val : M.restrict V → M) ∘
          fun q : N => (⟨f q, h (Set.mem_range_self q)⟩ : M.restrict V)) p :=
      f.contMDiff.contMDiffAt
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (P := ContDiffWithinAtProp 𝓘(𝕜, E) 𝓘(𝕜, E) ω) _ univ p).mp hval⟩

@[simp] theorem AnalyticMap.corestrict_apply (h : Set.range f ⊆ V) (p : N) :
    M.inclusion V (AnalyticMap.corestrict f V h p) = f p := rfl

/-- The corestriction of a local analytic isomorphism is a local analytic isomorphism (it factors
as `(M.inclusion V)⁻¹ ∘ f`, `inclusionInv` being the local inverse of the open inclusion). -/
theorem isLocalDiffeomorph_corestrict (hf : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f)
    (h : Set.range f ⊆ V) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (AnalyticMap.corestrict f V h) := by
  intro x
  have hxV : (f x : M) ∈ V := h (Set.mem_range_self x)
  have hfun : (fun p : N => inclusionInv M V (AnalyticMap.corestrict f V h x) (f p))
      = (AnalyticMap.corestrict f V h : N → M.restrict V) := by
    funext p
    exact inclusionInv_of_mem M V (AnalyticMap.corestrict f V h x) (h (Set.mem_range_self p))
  have hsymm : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      (inclusionInv M V (AnalyticMap.corestrict f V h x)) (f x) :=
    IsLocalDiffeomorphAt.of_eqOn
      (inclusionPartialDiffeomorph M V (AnalyticMap.corestrict f V h x)).symm hxV
      (Set.eqOn_refl _ _)
  rw [← hfun]
  exact IsLocalDiffeomorphAt.comp (hf := hf x) (hg := hsymm)

/-- The corestriction onto the range is surjective. -/
theorem surjective_corestrict (h' : Set.range f = V) :
    Function.Surjective (AnalyticMap.corestrict f V h'.le) := by
  rintro ⟨q, hq⟩
  have hq' : q ∈ Set.range f := by rw [h']; exact hq
  obtain ⟨p, hp⟩ := hq'
  exact ⟨p, Subtype.ext hp⟩

end Corestrict

/-! ### The composite blow-downs are proper -/

section Proper

variable {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- Every monoidal transformation of a succession is a blow-up, hence proper
(`IsBlowUp.isProperMap`). -/
theorem _root_.AnalyticManifold.FiniteSuccession.isProperMap_map (i : Fin S.length) :
    IsProperMap (S.map i) := by
  obtain ⟨_, _, _, -, -, hb⟩ := S.isMonoidal i
  exact hb.isProperMap

/-- The composite blow-down `σ^i : U_i → M` is proper, by composition. -/
theorem _root_.AnalyticManifold.FiniteSuccession.isProperMap_stageMapAux (i : ℕ)
    (h : i < S.length + 1) : IsProperMap (S.stageMapAux i h) := by
  induction i with
  | zero => exact isProperMap_id
  | succ i ih =>
    exact (ih (Nat.lt_of_succ_lt h)).comp (S.isProperMap_map ⟨i, Nat.lt_of_succ_lt_succ h⟩)

/-- The composite blow-down of a finite succession is proper: the preimage of a relatively compact
open is relatively compact. This is what makes the compatible-family form work over a neighbourhood
of every compact set ([Wlo09, Theorem 2.0.3 (1)]). -/
theorem _root_.AnalyticManifold.FiniteSuccession.isProperMap_stageMap (i : Fin (S.length + 1)) :
    IsProperMap (S.stageMap i) :=
  S.isProperMap_stageMapAux i.1 i.2

end Proper

end Hironaka.Manifold

namespace AnalyticManifold.BlowUpSequence

open _root_.Manifold
open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The last-stage lift lies over the local isomorphism -/

/-- The last-stage lift of a local analytic isomorphism `h` lies over `h`: `σ^r ∘ h_r = h ∘ σ'^r`.
One blow-up at a time, the lift of `h` to the blow-ups satisfies `π ∘ h₁ = h ∘ π'`
(`blowUpπ_liftStep`, the pull-back of a blow-up along `h` in the sense of
[Kol07, Definition 30 (30.1)]); the equation composes along the sequence. -/
theorem stageMap_last_pullbackLiftLast : ∀ {M N : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (q : (L.pullback h hh).stage (Fin.last _)),
    L.toSuccession.stageMap (Fin.last _) (L.pullbackLiftLast h hh q) =
      h ((L.pullback h hh).toSuccession.stageMap (Fin.last _) q)
  | _, _, nil _, _, _, _ => rfl
  | _, _, cons hY rest, h, hh, q => by
    have ih := stageMap_last_pullbackLiftLast rest (liftStep h hh hY)
      (isLocalDiffeomorph_liftStep h hh hY) q
    have h1 := stageMapAux_cons_succ hY rest rest.length (Fin.last _).2
      (rest.pullbackLiftLast (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY) q)
    have h2 := stageMapAux_cons_succ (hY.preimage_of_isLocalDiffeomorph hh)
      (rest.pullback (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY))
      (rest.pullback (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)).length
      (Fin.last _).2 q
    change (cons hY rest).toSuccession.stageMapAux (rest.length + 1) _
        (rest.pullbackLiftLast (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY) q) =
      h ((cons (hY.preimage_of_isLocalDiffeomorph hh)
        (rest.pullback (liftStep h hh hY)
          (isLocalDiffeomorph_liftStep h hh hY))).toSuccession.stageMapAux
          ((rest.pullback (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)).length + 1) _ q)
    rw [h1, h2]
    erw [ih]
    rw [blowUpπ_liftStep]
    rfl

/-- The range of the last-stage lift lies in the preimage of the range of `h`. -/
theorem range_pullbackLiftLast_subset {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) :
    Set.range (L.pullbackLiftLast h hh) ⊆
      L.toSuccession.stageMap (Fin.last _) ⁻¹' Set.range h := by
  rintro _ ⟨q, rfl⟩
  exact ⟨_, (stageMap_last_pullbackLiftLast L h hh q).symm⟩

/-! ### The reading open and the shrink-and-append step -/

variable {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
  (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)

/-- The **reading open** of the chain: the range of the last-stage lift of `h`, an open of the last
stage of `L` (a local analytic isomorphism has open range). The next factor of the chain is read on
it. -/
noncomputable def liftRange : Opens (L.stage (Fin.last _)) :=
  ⟨Set.range (L.pullbackLiftLast h hh), (isLocalDiffeomorph_pullbackLiftLast L h hh).isOpen_range⟩

/-- The reading open is relatively compact when the range of `h` is: it lies in the preimage of
`range h` under the proper composite blow-down. -/
theorem isCompact_closure_liftRange (hc : IsCompact (closure (Set.range h))) :
    IsCompact (closure (L.liftRange h hh : Set (L.stage (Fin.last _)))) := by
  have hprop := L.toSuccession.isProperMap_stageMap (Fin.last _)
  refine (hprop.isCompact_preimage hc).of_isClosed_subset isClosed_closure ?_
  exact (closure_mono (L.range_pullbackLiftLast_subset h hh)).trans
    (hprop.continuous.closure_preimage_subset _)

/-- The last-stage lift corestricted onto the reading open: a surjective local analytic isomorphism
from the last stage of `h^* L` onto the reading open of the last stage of `L`. -/
noncomputable def liftCorestrict :
    AnalyticMap ((L.pullback h hh).stage (Fin.last _))
      ((L.stage (Fin.last _)).restrict (L.liftRange h hh)) :=
  AnalyticMap.corestrict (L.pullbackLiftLast h hh) (L.liftRange h hh) Set.Subset.rfl

theorem isLocalDiffeomorph_liftCorestrict :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (L.liftCorestrict h hh) :=
  isLocalDiffeomorph_corestrict _ _ (isLocalDiffeomorph_pullbackLiftLast L h hh) _

theorem surjective_liftCorestrict : Function.Surjective (L.liftCorestrict h hh) :=
  surjective_corestrict _ _ rfl

/-- The **shrink-and-append step** of the chain: the sequence `L` restricted along `h` (its
pull-back), followed by a sequence `L'` on the reading open carried to the restricted sequence's
last stage along the corestricted lift. -/
noncomputable def shrinkAppend
    (L' : BlowUpSequence ψ₀ ((L.stage (Fin.last _)).restrict (L.liftRange h hh))) :
    BlowUpSequence ψ₀ N :=
  (L.pullback h hh).concat
    (L'.pullback (L.liftCorestrict h hh) (isLocalDiffeomorph_liftCorestrict L h hh))

end AnalyticManifold.BlowUpSequence

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The class of `BO_{n,m}` is closed under pull-back along local analytic isomorphisms -/

/-- The class `BOClass m` is stable under pull-back of the triple along an arbitrary local analytic
isomorphism `h` (the form of `AnalyticTriple.boClass_of_isPullbackOf` of `ClassPullback.lean` for
the pull-back triple `T.pullback h hh` itself): the order bound pulls back pointwise and a member
of the pulled-back family is nonempty only if the member is. The triples carried along the chain
are pull-backs of induced triples along the lifts, whose class membership this supplies. -/
theorem _root_.Manifold.AnalyticTriple.boClass_pullback_of_isLocalDiffeomorph
    {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {m : ℕ} (hT : AnalyticTriple.BOClass m T) :
    AnalyticTriple.BOClass m (T.pullback h hh) := by
  refine ⟨hT.1, fun y => ?_, ?_⟩
  · change (T.I.pullback ⇑h h.contMDiff).ord y ≤ (m : ℕ∞)
    rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ T.I (hh y)]
    exact hT.2.1 _
  · have := hT.2.2
    refine Finite.of_injective
      (fun j : {j // (T.F.comap ⇑h).hyp j ≠ ∅} => (⟨j.1, fun he => j.2 ?_⟩ : {j // T.F.hyp j ≠ ∅}))
      fun j₁ j₂ hj => Subtype.ext (Subtype.mk.inj hj)
    change ⇑h ⁻¹' T.F.hyp j.1 = ∅
    rw [he, Set.preimage_empty]

end Hironaka.Manifold

namespace AnalyticManifold.BlowUpSequence

open _root_.Manifold
open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The last stage of a concatenation -/

/-- The last stage of a concatenation is the last stage of the second list (definitionally at each
constructor; the lemma is the induction). -/
theorem stage_last_concat : ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (L' : BlowUpSequence ψ₀ (L.stage (Fin.last _))),
    (L.concat L').stage (Fin.last _) = L'.stage (Fin.last _)
  | _, nil _, _ => rfl
  | _, cons _ rest, L' => stage_last_concat rest L'

end AnalyticManifold.BlowUpSequence

