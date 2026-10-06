/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepALink
public import Hironaka.Resolution.Analytic.OrderReduction.Step22Fam
public import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
import Hironaka.Resolution.Analytic.OrderReduction.ClassPullback
import Hironaka.Resolution.Analytic.OrderReduction.FamilyIndependence
import Hironaka.Resolution.Analytic.OrderReduction.Modified.NonmonomialIndiff
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The order reduction read at the nonmonomial triple

"Apply order reduction (68) to `N(I)`" [Kol07, 111, Step 1]: a round of the rounds on the
nonmonomial part reads the order reduction `BO_{n,d}` at the nonmonomial triple `(M, N(𝓘), E)`.
Packaged as a family functor in its own right, `nonmonomialFunctor bo` on the class
`NonmonomialClass d` of triples whose nonmonomial triple lies in the domain of `BO_{n,d}`, it
inherits the two naturality properties from `bo`:

* it **commutes with local analytic isomorphisms** (the analogue of [Kol07, Theorem 103 (2)]),
  because the nonmonomial part commutes with pull-back (`NonmonomialComap`);
* it is **indifferent to empty boundary members** (the counterpart, for boundary members, of
  [Kol07, 32]), because the
  nonmonomial part is (`nonmonomialTriple_eq_of_isEmptyExtension`).

The value of the round in `StepALink.lean` is the value of this functor at the induced triple
(`BState.roundValue_eq_nonmonomialFunctor`, a `rfl`), so the transport lemmas for values at induced
triples (`InducedValueFunctor.lean`) apply to the link of the descent.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

open Hironaka.Manifold.BMO

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

/-- The class of triples whose nonmonomial triple lies in the domain of `BO_{n,d}` (`1 ≤ d`,
`ord N(𝓘) ≤ d` everywhere, finitely many nonempty members): the domain of the round on the
nonmonomial part [Kol07, 111, Step 1]. -/
abbrev NonmonomialClass (d : ℕ) {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) : Prop :=
  AnalyticTriple.BOClass d (nonmonomialTriple T)

variable {d : ℕ} (bo : BOanFam.{u} 𝕜 n d)

/-- **The order reduction read at the nonmonomial triple**, as a family functor on
`NonmonomialClass d` [Kol07, 111, Step 1]: the value of `bo` at `(M, N(𝓘), E)`, re-typed as a family
for `(M, 𝓘, E)` (`CompatibleFamily.changeTriple`; the triple is not part of the data of a compatible
family). -/
def nonmonomialFunctor :
    AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (NonmonomialClass d) where
  fam T hT := (bo.functor.fam (nonmonomialTriple T) hT).changeTriple

@[simp] theorem nonmonomialFunctor_fam_seqOn {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : NonmonomialClass d T)
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    ((nonmonomialFunctor bo).fam T hT).seqOn U hU =
      (bo.functor.fam (nonmonomialTriple T) hT).seqOn U hU := rfl

variable (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))

include hcomp in
/-- The class is closed under pull-back along local analytic isomorphisms (`NonmonomialComap` and
`boClass_of_isPullbackOf`). -/
theorem nonmonomialClass_pullback {M N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    {T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M} (hT : NonmonomialClass d T)
    (g : AnalyticMap N M) (hg : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g) :
    NonmonomialClass d (T.pullback g hg) := by
  unfold NonmonomialClass
  rw [hcomp T g hg]
  exact AnalyticTriple.boClass_of_isPullbackOf hT hg (AnalyticTriple.isPullbackOf_pullback _ _ _)

/-- The class is indifferent to empty boundary members: deleting or adding empty members keeps the
nonmonomial triple's ideal (`nonmonomialTriple_eq_of_isEmptyExtension`) and the finiteness of the
nonempty members. -/
theorem nonmonomialClass_of_isEmptyExtension {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    {T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M} (hT : NonmonomialClass d T)
    (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
    {e : F'.ι ↪o T.F.ι} (he : HypersurfaceFamily.IsEmptyExtension e) :
    NonmonomialClass d (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple _ M) := by
  unfold NonmonomialClass
  rw [nonmonomialTriple_eq_of_isEmptyExtension T F' hsnc' he]
  have hfin : Finite {b // T.F.hyp b ≠ ∅} := by
    have h := hT.2.2
    rwa [nonmonomialTriple_F] at h
  exact ⟨hT.1, hT.2.1, finite_nonempty_left_of_isEmptyExtension he hfin⟩

/-- The converse: a triple whose boundary is an empty extension of the boundary of a triple of the
class (same ideal) lies in the class. -/
theorem nonmonomialClass_of_isEmptyExtension' {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (F' : HypersurfaceFamily M)
    (hsnc' : F'.IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))) {e : F'.ι ↪o T.F.ι}
    (he : HypersurfaceFamily.IsEmptyExtension e)
    (hT' : NonmonomialClass d (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple _ M)) :
    NonmonomialClass d T := by
  unfold NonmonomialClass at hT' ⊢
  rw [nonmonomialTriple_eq_of_isEmptyExtension T F' hsnc' he] at hT'
  have hfin : Finite {j // F'.hyp j ≠ ∅} := hT'.2.2
  have hfin' : Finite {b // T.F.hyp b ≠ ∅} := finite_nonempty_right_of_isEmptyExtension he hfin
  refine ⟨hT'.1, hT'.2.1, ?_⟩
  rwa [nonmonomialTriple_F]

include hcomp in
/-- **The family read at the nonmonomial triple commutes with local analytic isomorphisms**
(the analogue of [Kol07, Theorem 103 (2)] for the composite), since the nonmonomial triple of a
pull-back is the
pull-back of the nonmonomial triple (`NonmonomialComap`). -/
theorem nonmonomialFunctor_commutesWithLocalIsos :
    (nonmonomialFunctor bo).CommutesWithLocalIsos := by
  intro M N T T' g hg hpull hT hT' U' hU'
  simp only [nonmonomialFunctor_fam_seqOn]
  have hT'eq : T' = T.pullback g hg := hpull.eq (AnalyticTriple.isPullbackOf_pullback T g hg)
  have hN : (nonmonomialTriple T').IsPullbackOf (nonmonomialTriple T) g := by
    rw [hT'eq, hcomp T g hg]
    exact AnalyticTriple.isPullbackOf_pullback _ _ _
  exact bo.commutesWithLocalIsos (nonmonomialTriple T) (nonmonomialTriple T') g hg hN hT hT' U' hU'

/-- The indifference property with the boundary of the triple named by an equation (substituted),
the shape in which the property applies at `nonmonomialTriple T`, whose boundary is `T.F` only up to
the projection lemma `nonmonomialTriple_F`. -/
theorem _root_.Hironaka.Manifold.AnalyticFamilyFunctor.IndifferentToEmptyMembers.seqOn_eq_of_eq_F
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}
    {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
    {B : AnalyticFamilyFunctor ψ₀ Dom} (hB : B.IndifferentToEmptyMembers)
    {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) {G : HypersurfaceFamily M}
    (hG : T.F = G) (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc ψ₀) (e : F'.ι ↪o G.ι)
    (h1 : ∀ i, G.hyp (e i) = F'.hyp i) (h2 : ∀ b, b ∉ Set.range e → G.hyp b = ∅) (hT : Dom T)
    (hT' : Dom (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple ψ₀ M)) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    (B.fam T hT).seqOn U hU =
      (B.fam ⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ hT').seqOn U hU := by
  subst hG
  exact hB T F' hsnc' e h1 h2 hT hT' U hU

/-- **The family read at the nonmonomial triple is indifferent to empty boundary members** (the
counterpart, for boundary members, of [Kol07, 32]): the nonmonomial triple of the triple with the
replaced boundary is the
nonmonomial triple with the boundary replaced (`nonmonomialTriple_eq_of_isEmptyExtension`), and `bo`
is indifferent. -/
theorem nonmonomialFunctor_indifferentToEmptyMembers :
    (nonmonomialFunctor bo).IndifferentToEmptyMembers := by
  intro M T F' hsnc' e h1 h2 hT hT' U hU
  simp only [nonmonomialFunctor_fam_seqOn]
  have heq := nonmonomialTriple_eq_of_isEmptyExtension T F' hsnc'
    (⟨h1, h2⟩ : HypersurfaceFamily.IsEmptyExtension e)
  have hT'' : AnalyticTriple.BOClass d (⟨(nonmonomialTriple T).I,
      (nonmonomialTriple T).isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple _ M) := by
    rw [← heq]
    exact hT'
  rw [AnalyticFamilyFunctor.fam_seqOn_congr_triple bo.functor heq hT' hT'' U hU]
  exact AnalyticFamilyFunctor.IndifferentToEmptyMembers.seqOn_eq_of_eq_F
    bo.indifferentToEmptyMembers (nonmonomialTriple T) (nonmonomialTriple_F T) F' hsnc' e h1 h2 hT
    hT'' U hU

/-! ### The round's value -/

section Round

variable {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  {T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M} {m : ℕ}
  (hT : AnalyticTriple.BMOClass m T) (bo' : ∀ d : ℕ, BOanFam.{u} 𝕜 n d) {W : Opens M} {d : ℕ}
  (st : BState T m W d) {V : Opens M} (hV : IsCompact (closure (V : Set M)))
  (hVW : closure (V : Set M) ⊆ W)

include hT in
/-- The invariant of the descent puts the induced triple in `NonmonomialClass d`. -/
theorem BState.nonmonomialClass (hd : 1 ≤ d) :
    NonmonomialClass d (ChainState.inducedTriple T m st.toChainState) :=
  st.boClass_nonmonomial hT hd

/-- The value of the round is the value of the functor read at the nonmonomial triple, at the
induced triple. -/
theorem BState.roundValue_eq_nonmonomialFunctor (hd : 1 ≤ d) :
    st.roundValue bo' hV hVW hT hd =
      ((nonmonomialFunctor (bo' d)).fam (ChainState.inducedTriple T m st.toChainState)
        (st.nonmonomialClass hT hd)).seqOn (st.liftOpen hVW)
        (st.isCompact_closure_liftOpen hV hVW) :=
  rfl

end Round

end Hironaka.Manifold.BMOmod

end
