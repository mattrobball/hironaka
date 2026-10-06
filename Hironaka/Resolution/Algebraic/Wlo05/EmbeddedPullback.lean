/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced
import Hironaka.Resolution.Algebraic.Kol07.StrictTransformSupport
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.LoopFunctorial
import Hironaka.Resolution.Algebraic.OrderReduction.Step21Functorial
import Hironaka.Resolution.Algebraic.Smooth.GeometricallyReduced
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Stage.DimFreeTheorems
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRegWindow
import Hironaka.Scheme.BlowUp.FlatColon
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.RestrictedCenters
import Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# `BED` commutes with smooth surjections

Clause (d) of [Wlo05, Theorem 1.0.2] ([Wlo05, 4.1]; the first bullet of [Kol07, 34.1]): for a
smooth surjection `h : X' → X` carrying the pull-back data,
`BED(X', h^* I_Y, ∅) = h^* BED(X, I_Y, ∅)` (`bed_pullback_of_surjective`), where `BED` is the loop
of `Hironaka.Resolution.Algebraic.Wlo05.Embedded`.

**The mechanism** (the proof of [Wlo05, Theorem 4.7.1] transported along `h`): the loop `bedAux` is
a recursion on the number of remaining components, and one round is transported as follows.

* The runs: `BMO_1` commutes with smooth surjections ([Kol07, Theorem 69 (2)],
  `dimFreeBMO_commutesWithSmooth` of `Hironaka.Resolution.Algebraic.Stage.DimFreeTheorems`), so the
  pulled-back run is the pull-back of the run ([Kol07, Definition 30, 30.1]).
* The stop rule: with `C'` the components of the preimages of the members of `C`
  (`IsPullbackComponents`, `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools`), the first
  absorbing stage is the same on both sides and the same components are absorbed (`stopRule_aux`),
  so `Nat.find` agrees.
* The isolated triple: the marked triple induced at the end of the truncation pulls back along the
  last-stage lift (`isPullbackOf_induced_last`), and its colon divisor — the reduced ideal of the
  union of the absorbed strict transforms — pulls back too: the colon commutes with a flat base
  change (`colon_comap_of_flat_of_isLocallyNoetherian`, `Hironaka.Scheme.BlowUp.FlatColon`), the
  reduced ideal of a closed set pulls back to the reduced ideal of the preimage
  (`comap_vanishingIdeal_of_smooth`, `Hironaka.Resolution.Algebraic.Smooth.GeometricallyReduced`),
  and the preimage of the union of the absorbed strict transforms is the union of the strict
  transforms of the absorbed components upstairs (`iSup_support_strictTransformSeq_pullback_last`:
  the strict transform of a finite union is the union of the strict transforms).
* The remaining components: the strict transforms of the components of `h⁻¹(V(c))` are the
  components of `h_n⁻¹(X̄_n(c))` (`isPullbackComponents_remainingAt`, through the generic points of
  the strict transforms, the proof of [Kol07, Corollary 22]), so the invariant
  `IsPullbackComponents` holds again along the last-stage lift, and strong induction on `C.card`
  closes.

The isolated triple and the remaining members are `isolatedAt` and `remainingAt` of
`Hironaka.Resolution.Algebraic.Wlo05.Embedded` at the truncated run and the absorbed family; stating
the transport for these, with the run and the families as parameters, is what lets the pulled-back
run be substituted (`concat_bedAux_congr`). This transport is not in the literature.
Used in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedEraseEmpty` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFunctorClauses`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.Stage

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-! ### The round with the run as a parameter -/

open Classical in
/-- Substitution of the run and of the absorbed and remaining families in the concatenation of a
round (the form of the loop on the left, the parametrised form on the right). -/
theorem concat_bedAux_congr (T' : MarkedTriple k) (hm' : T'.m = 1)
    (C' : Finset T'.X.left.IdealSheafData) (n : ℕ) {Q₂ : BlowUpSequence T'.X.left}
    (eQ : (bmoOneRun T' hm').take n = Q₂)
    (hQ₂ : Q₂.IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E)
    {F₂ G₂ : Finset T'.X.left.IdealSheafData}
    (eF : (C'.filter fun c' => CenterContains (bmoOneRun T' hm') c' n) = F₂)
    (eG : (C'.filter fun c' => ¬ CenterContains (bmoOneRun T' hm') c' n) = G₂) :
    ((bmoOneRun T' hm').take n).concat
        (bedAux (isolatedTriple T' hm' C' n) hm' (remainingComponents T' hm' C' n)) =
      Q₂.concat (bedAux (isolatedAt T' Q₂ hQ₂ F₂) hm' (remainingAt Q₂ G₂)) := by
  subst eQ eF eG
  rfl

open Classical in
/-- The loop unrolled once at the first absorbing stage `n`, for any `n` equal to `Nat.find`. -/
theorem bedAux_eq_concat_of_find (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) (hex : ∃ n, HasAbsorptionAt T hm C n) (n : ℕ)
    (hn : Nat.find hex = n) :
    bedAux T hm C = ((bmoOneRun T hm).take n).concat
      (bedAux (isolatedTriple T hm C n) hm (remainingComponents T hm C n)) := by
  subst hn
  exact bedAux_of_exists T hm C hex

/-! ### The isolated triple pulls back along the last-stage lift -/

/-- The isolated marked triple of the pulled-back truncated run, with the absorbed family `F'`,
carries the pull-back data of the isolated marked triple downstairs along a lift `g` of the last
stages ([Wlo05, 4.1] for the isolated triple), given that the induced triples do
(`isPullbackOf_induced_last` for the last-stage lift) and that the union of the absorbed strict
transforms upstairs is the preimage of the one downstairs: the colon commutes with the flat lift
(`Hironaka.Scheme.BlowUp.FlatColon`) and the reduced ideal of a closed set pulls back to the reduced
ideal of the preimage (`Hironaka.Resolution.Algebraic.Smooth.GeometricallyReduced`). Stated for a
lift `g` typed at the stages `stage (Fin.last _)`, to which `last` unfolds only definitionally. -/
theorem isolatedAt_isPullbackOf {T T' : MarkedTriple k} (h : T'.X.left ⟶ T.X.left)
    (Q : BlowUpSequence T.X.left) (hQ : Q.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E)
    (hQ' : (Q.pullback h).IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E)
    (g : (Q.pullback h).stage (Fin.last _) ⟶ Q.stage (Fin.last _)) [Smooth g]
    (hind : (T'.induced (Q.pullback h) hQ' (Fin.last _)).IsPullbackOf (T.induced Q hQ (Fin.last _))
      g)
    (F : Finset T.X.left.IdealSheafData) (F' : Finset T'.X.left.IdealSheafData)
    (hΓ : (⨆ c' ∈ F', ((Q.pullback h).strictTransformSeq c' (Fin.last _)).support) =
      (⨆ c ∈ F, (Q.strictTransformSeq c (Fin.last _)).support).preimage g.continuous) :
    (isolatedAt T' (Q.pullback h) hQ' F').IsPullbackOf (isolatedAt T Q hQ F) g := by
  obtain ⟨⟨hover, hI, hE⟩, hm⟩ := hind
  refine ⟨⟨hover, ?_, hE⟩, hm⟩
  have hLN : IsLocallyNoetherian (Q.stage (Fin.last _)) :=
    ((T.induced Q hQ (Fin.last _)).X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hLN' : IsLocallyNoetherian ((Q.pullback h).stage (Fin.last _)) :=
    ((T'.induced (Q.pullback h) hQ' (Fin.last _)).X.left ↘ Spec
      (.of k)).isLocallyNoetherian_of_field
  have hN : NoetherianSpace (Q.stage (Fin.last _)) :=
    Hironaka.BD.noetherianSpace_triple (T.induced Q hQ (Fin.last _)).toTriple
  set Γ : Closeds (Q.stage (Fin.last _)) :=
    ⨆ c ∈ F, (Q.strictTransformSeq c (Fin.last _)).support with hΓdef
  have hI' : (T'.induced (Q.pullback h) hQ' (Fin.last _)).I =
      (T.induced Q hQ (Fin.last _)).I.comap g := hI
  have key : ((T.induced Q hQ (Fin.last _)).I.colon (IdealSheafData.vanishingIdeal Γ)).comap g =
      ((T.induced Q hQ (Fin.last _)).I.comap g).colon ((IdealSheafData.vanishingIdeal Γ).comap g) :=
    IdealSheafData.colon_comap_of_flat_of_isLocallyNoetherian g _ _
  have key2 : (IdealSheafData.vanishingIdeal Γ).comap g = IdealSheafData.vanishingIdeal
      (Γ.preimage g.continuous) :=
    Hironaka.Smooth.comap_vanishingIdeal_of_smooth g Γ
  change (T'.induced (Q.pullback h) hQ' (Fin.last _)).I.colon (IdealSheafData.vanishingIdeal _) =
    ((T.induced Q hQ (Fin.last _)).I.colon (IdealSheafData.vanishingIdeal Γ)).comap g
  rw [hI', key, key2]
  exact congrArg (fun Z => ((T.induced Q hQ (Fin.last _)).I.comap g).colon
      (IdealSheafData.vanishingIdeal Z)) hΓ

/-- The set underlying a finite supremum of closed sets. -/
theorem coe_iSup_finset {X : Type*} [TopologicalSpace X] {ι : Type*} (F : Finset ι)
    (f : ι → Closeds X) : ((⨆ c ∈ F, f c : Closeds X) : Set X) = ⋃ c ∈ F, (f c : Set X) := by
  rw [← Finset.sup_eq_iSup, Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion]
  rfl

/-- The strict transform at the end of the pulled-back run of the preimage of `V(c)` is the union
of the strict transforms of the components of `h⁻¹(V(c))`. -/
theorem coe_support_strictTransformSeq_comap_last {X X' : Scheme.{u}} [IsLocallyNoetherian X']
    [NoetherianSpace X'] (Q : BlowUpSequence X) (h : X' ⟶ X) (c : X.IdealSheafData) :
    (((Q.pullback h).strictTransformSeq (c.comap h) (Fin.last _)).support :
        Set ((Q.pullback h).stage (Fin.last _))) =
      ⋃ η' ∈ (c.support.preimage h.continuous).genericPoints,
        (((Q.pullback h).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η'}))
          (Fin.last _)).support : Set ((Q.pullback h).stage (Fin.last _))) :=
  coe_support_strictTransformSeq_biUnion (Q.pullback h) _
    (Closeds.genericPoints_finite _) _ (c.comap h) (coe_support_comap_eq_iUnion h c) (Fin.last _)

/-- The union of the strict transforms of the components of the preimages of the members of `F` is
the preimage, under a lift `g` of the last stages carrying the strict transforms
([Kol07, Definition 30, 30.2]; `strictTransformSeq_pullback_last` for the last-stage lift), of the
union of the strict transforms of the members of `F` ([Wlo05, 4.1] for the divisor of the isolated
triple). -/
theorem iSup_support_strictTransformSeq_pullback_last {X X' : Scheme.{u}} [IsLocallyNoetherian X']
    [NoetherianSpace X'] (Q : BlowUpSequence X) (h : X' ⟶ X)
    (g : (Q.pullback h).stage (Fin.last _) ⟶ Q.stage (Fin.last _))
    (hg : ∀ J : X.IdealSheafData, (Q.pullback h).strictTransformSeq (J.comap h) (Fin.last _) =
      (Q.strictTransformSeq J (Fin.last _)).comap g)
    (F : Finset X.IdealSheafData) (F' : Finset X'.IdealSheafData)
    (hFF' : IsPullbackComponents h F F') :
    (⨆ c' ∈ F', ((Q.pullback h).strictTransformSeq c' (Fin.last _)).support) =
      (⨆ c ∈ F, (Q.strictTransformSeq c (Fin.last _)).support).preimage g.continuous := by
  apply SetLike.coe_injective
  ext x
  constructor
  · intro hx
    have hx' : x ∈ ((⨆ c' ∈ F', ((Q.pullback h).strictTransformSeq c' (Fin.last _)).support :
        Closeds _) : Set _) := hx
    rw [coe_iSup_finset] at hx'
    obtain ⟨c', hc', hx'⟩ := Set.mem_iUnion₂.mp hx'
    obtain ⟨c, hc, η', hη', rfl⟩ := (hFF' c').mp hc'
    change g x ∈ (⨆ c ∈ F, (Q.strictTransformSeq c (Fin.last _)).support : Closeds _)
    rw [← SetLike.mem_coe, coe_iSup_finset]
    refine Set.mem_iUnion₂.mpr ⟨c, hc, ?_⟩
    have hmem : x ∈ ((Q.strictTransformSeq c (Fin.last _)).comap g).support := by
      rw [← hg, ← SetLike.mem_coe, coe_support_strictTransformSeq_comap_last]
      exact Set.mem_iUnion₂.mpr ⟨η', hη', hx'⟩
    exact (mem_support_comap_iff_apply _ _ _).mp hmem
  · intro hx
    change g x ∈ (⨆ c ∈ F, (Q.strictTransformSeq c (Fin.last _)).support : Closeds _) at hx
    rw [← SetLike.mem_coe, coe_iSup_finset] at hx
    obtain ⟨c, hc, hx⟩ := Set.mem_iUnion₂.mp hx
    have hmem : x ∈ ((Q.strictTransformSeq c (Fin.last _)).comap g).support :=
      (mem_support_comap_iff_apply _ _ _).mpr hx
    rw [← hg, ← SetLike.mem_coe, coe_support_strictTransformSeq_comap_last] at hmem
    obtain ⟨η', hη', hmem⟩ := Set.mem_iUnion₂.mp hmem
    change x ∈ ((⨆ c' ∈ F', ((Q.pullback h).strictTransformSeq c' (Fin.last _)).support :
      Closeds _) : Set _)
    rw [coe_iSup_finset]
    exact Set.mem_iUnion₂.mpr ⟨_, (hFF' _).mpr ⟨c, hc, η', hη', rfl⟩, hmem⟩

/-! ### The remaining members pull back as components -/

/-- For the state `(C, C')` of the loop and the predicates `P`, `P'` selecting the non-absorbed
members (related through the stop-rule equivalence), the strict transforms at the end of the
pulled-back run of the members of `C'.filter P'` are the components of the preimages, under a lift
`g` of the last stages, of the strict transforms of the members of `C.filter P` (the proof of
[Kol07, Corollary 22] and [Kol07, Definition 30, 30.2] along `h`), given that no member was
absorbed along the truncated run on either side, that `g` carries the strict transforms (`hg`) and
the generic points (`hgen`; both hold for the last-stage lift). -/
theorem isPullbackComponents_remainingAt {X X' : Scheme.{u}}
    [IsLocallyNoetherian X'] [NoetherianSpace X'] (Q : BlowUpSequence X) (h : X' ⟶ X)
    (g : (Q.pullback h).stage (Fin.last _) ⟶ Q.stage (Fin.last _))
    (hg : ∀ J : X.IdealSheafData, (Q.pullback h).strictTransformSeq (J.comap h) (Fin.last _) =
      (Q.strictTransformSeq J (Fin.last _)).comap g)
    (hgen : ∀ {η : X} {η' : X'},
      η' ∈ ((Closeds.closure {η}).preimage h.continuous).genericPoints →
      (∀ m : Fin Q.length,
        ¬ Q.center m ≤ Q.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
            {η})) m.castSucc) →
      (∀ m : Fin (Q.pullback h).length, ¬ (Q.pullback h).center m ≤
        (Q.pullback h).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
            {η'})) m.castSucc) →
      ∃ (ηQ : Q.stage (Fin.last _)) (ηQ' : (Q.pullback h).stage (Fin.last _)),
        IsGenericPoint ηQ ((Q.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
            {η}))
          (Fin.last _)).support : Set (Q.stage (Fin.last _))) ∧
        IsGenericPoint ηQ' (((Q.pullback h).strictTransformSeq
          (IdealSheafData.vanishingIdeal (Closeds.closure {η'})) (Fin.last _)).support :
            Set ((Q.pullback h).stage (Fin.last _))) ∧
        g ηQ' = ηQ ∧ (Q.pullback h).stageMap (Fin.last _) ηQ' = η')
    (C : Finset X.IdealSheafData) (C' : Finset X'.IdealSheafData)
    (hC : ∀ c ∈ C, ∃ η : X, c = IdealSheafData.vanishingIdeal (Closeds.closure {η}))
    (hCC' : IsPullbackComponents h C C') (P : X.IdealSheafData → Prop)
    (P' : X'.IdealSheafData → Prop) [DecidablePred P] [DecidablePred P']
    (hP : ∀ c ∈ C, ∀ η' ∈ (c.support.preimage h.continuous).genericPoints,
      (P' (IdealSheafData.vanishingIdeal (Closeds.closure {η'})) ↔ P c))
    (hhist : ∀ c ∈ C, ∀ m : Fin Q.length, ¬ Q.center m ≤ Q.strictTransformSeq c m.castSucc)
    (hhist' : ∀ c' ∈ C', ∀ m : Fin (Q.pullback h).length,
      ¬ (Q.pullback h).center m ≤ (Q.pullback h).strictTransformSeq c' m.castSucc) :
    IsPullbackComponents g (remainingAt Q (C.filter P))
      (remainingAt (Q.pullback h) (C'.filter P')) := by
  classical
  intro c''
  simp only [remainingAt, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨c', ⟨hc'C', hPc'⟩, rfl⟩
    obtain ⟨c, hc, η', hη', rfl⟩ := (hCC' c').mp hc'C'
    have hPc : P c := (hP c hc η' hη').mp hPc'
    obtain ⟨η, rfl⟩ := hC c hc
    rw [support_vanishingIdeal_eq] at hη'
    obtain ⟨ηQ, ηQ', hgenQ, hgenQ', hcomm, hmapQ'⟩ := hgen hη' (hhist _ hc) (hhist' _ hc'C')
    have := isReduced_subscheme_vanishingIdeal (X := X') (Closeds.closure {η'})
    refine ⟨_, ⟨_, ⟨hc, hPc⟩, rfl⟩, ηQ', ⟨?_, fun ζ hζ hspec => ?_⟩,
      strictTransformSeq_eq_vanishingIdeal_closure _ _ _ hgenQ'⟩
    · change g ηQ' ∈
        (Q.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η}))
            (Fin.last _)).support
      rw [hcomm]
      exact hgenQ.mem
    · -- `ζ` lies on the strict transform of some component `c₂'` of `h⁻¹(V(c))`
      change g ζ ∈
        (Q.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η}))
            (Fin.last _)).support at hζ
      rw [← mem_support_comap_iff_apply, ← hg, ← SetLike.mem_coe,
        coe_support_strictTransformSeq_comap_last] at hζ
      obtain ⟨η'', hη'', hζ₂⟩ := Set.mem_iUnion₂.mp hζ
      rw [support_vanishingIdeal_eq] at hη''
      have hc₂' : IdealSheafData.vanishingIdeal (Closeds.closure {η''}) ∈ C' := by
        refine (hCC' _).mpr ⟨_, hc, η'', ?_, rfl⟩
        rwa [support_vanishingIdeal_eq]
      obtain ⟨-, ηQ₂', -, hgenQ₂', -, -⟩ := hgen hη'' (hhist _ hc) (hhist' _ hc₂')
      -- `ηQ'` lies on the strict transform of `c₂'`, so `η' = Π'(ηQ')` lies on `V(c₂')`
      have hspecζ : ηQ₂' ⤳ ζ := hgenQ₂'.specializes hζ₂
      have hmemQ' : ηQ' ∈ ((Q.pullback h).strictTransformSeq
          (IdealSheafData.vanishingIdeal (Closeds.closure {η''})) (Fin.last _)).support := by
        rw [← SetLike.mem_coe, ← hgenQ₂'.def]
        exact specializes_iff_mem_closure.mp (hspecζ.trans hspec)
      have hpi := stageMap_mem_support_of_mem_support_strictTransformSeq (Q.pullback h) _
        (Fin.last _) hmemQ'
      rw [hmapQ', support_vanishingIdeal_eq] at hpi
      have hη''η' : η'' = η' := hη'.2 hη''.1 (specializes_iff_mem_closure.mpr hpi)
      subst hη''η'
      exact (hspec.antisymm (hgenQ'.specializes hζ₂)).eq
  · rintro ⟨c₁, ⟨c, ⟨hc, hPc⟩, rfl⟩, ξ, hξ, rfl⟩
    obtain ⟨η, rfl⟩ := hC c hc
    have hξmem := hξ.1
    change g ξ ∈
      (Q.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η}))
          (Fin.last _)).support at hξmem
    rw [← mem_support_comap_iff_apply, ← hg, ← SetLike.mem_coe,
      coe_support_strictTransformSeq_comap_last] at hξmem
    obtain ⟨η'', hη'', hξ₂⟩ := Set.mem_iUnion₂.mp hξmem
    have hc₂' : IdealSheafData.vanishingIdeal (Closeds.closure {η''}) ∈ C' :=
      (hCC' _).mpr ⟨_, hc, η'', hη'', rfl⟩
    have hP' : P' (IdealSheafData.vanishingIdeal (Closeds.closure {η''})) :=
        (hP _ hc η'' hη'').mpr hPc
    rw [support_vanishingIdeal_eq] at hη''
    obtain ⟨ηQ₂, ηQ₂', hgenQ₂, hgenQ₂', hcomm₂, -⟩ := hgen hη'' (hhist _ hc) (hhist' _ hc₂')
    have := isReduced_subscheme_vanishingIdeal (X := X') (Closeds.closure {η''})
    refine ⟨_, ⟨hc₂', hP'⟩, ?_⟩
    have hξeq : ηQ₂' = ξ := by
      refine hξ.2 ?_ (hgenQ₂'.specializes hξ₂)
      change g ηQ₂' ∈
        (Q.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η}))
            (Fin.last _)).support
      rw [hcomm₂]
      exact hgenQ₂.mem
    rw [← hξeq]
    exact strictTransformSeq_eq_vanishingIdeal_closure _ _ _ hgenQ₂'

/-- The remaining members at the end of a truncated run along which no member was absorbed are
reduced ideals of closures of points (integral strict transforms,
`exists_isGenericPoint_strictTransformSeq`). -/
theorem remainingAt_prime {X : Scheme.{u}} [IsLocallyNoetherian X] (Q : BlowUpSequence X)
    (G : Finset X.IdealSheafData) (hG : ∀ c ∈ G, ∃ η : X, c = IdealSheafData.vanishingIdeal
        (Closeds.closure {η}))
    (hhist : ∀ c ∈ G, ∀ m : Fin Q.length, ¬ Q.center m ≤ Q.strictTransformSeq c m.castSucc) :
    ∀ c₁ ∈ remainingAt Q G,
      ∃ ζ : Q.stage (Fin.last _), c₁ = IdealSheafData.vanishingIdeal (Closeds.closure {ζ}) := by
  classical
  intro c₁ hc₁
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc₁
  obtain ⟨η, rfl⟩ := hG c hc
  have := isReduced_subscheme_vanishingIdeal (X := X) (Closeds.closure {η})
  obtain ⟨ζ, hζ, -, -⟩ := exists_isGenericPoint_strictTransformSeq Q _
    (Hironaka.BMO.isGenericPoint_support_vanishingIdeal_closure η) (Fin.last _)
    (fun m _ => hhist _ hc m)
  exact ⟨ζ, strictTransformSeq_eq_vanishingIdeal_closure _ _ _ hζ⟩

/-! ### The loop along a smooth surjection -/

open Classical in
/-- **The loop along a smooth surjection** ([Wlo05, Theorem 1.0.2] clause (d), [Wlo05, 4.1]; the
first bullet of [Kol07, 34.1]): for marked triples of mark `1`, a smooth surjection `h` carrying the
pull-back data, a family `C` of reduced ideals of irreducible closed sets and `C'` the components
of their preimages, the modified run upstairs is the pull-back of the modified run downstairs.
Strong induction on the number of members; one round is transported by the stop-rule equivalence,
the pull-back data of the isolated triple and the components relation for the remaining
members. -/
theorem bedAux_pullback_of_surjective :
    ∀ (N : ℕ) (T T' : MarkedTriple k) (hm : T.m = 1) (hm' : T'.m = 1)
      (h : T'.X.left ⟶ T.X.left) [Smooth h], Function.Surjective h → T'.IsPullbackOf T h →
      ∀ (C : Finset T.X.left.IdealSheafData) (C' : Finset T'.X.left.IdealSheafData), C.card = N →
        (∀ c ∈ C, ∃ η : T.X.left, c = IdealSheafData.vanishingIdeal (Closeds.closure {η})) →
        IsPullbackComponents h C C' → bedAux T' hm' C' = (bedAux T hm C).pullback h := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro T T' hm hm' h _ hs hp C C' hcard hC hCC'
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have : IsLocallyNoetherian T'.X.left := (T'.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have : NoetherianSpace T'.X.left := Hironaka.BD.noetherianSpace_triple T'.toTriple
  -- the runs (Theorem 69 for `BMO_1`)
  have hcs := (dimFreeBMO_commutesWithSmooth stage0 1 (k := k)).1
  have hR : bmoOneRun T' hm' = (bmoOneRun T hm).pullback h :=
    @hcs T T' h ‹Smooth h› hs hp ⟨le_rfl, hm⟩ ⟨le_rfl, hm'⟩
  set S := bmoOneRun T hm with hSdef
  have hstop := stopRule_aux S h C C' hC hCC'
  by_cases hex : ∃ n, HasAbsorptionAt T hm C n
  · set n := Nat.find hex with hn
    have hmin : ∀ m < n, ¬ HasAbsorptionAt T hm C m := fun m hm => Nat.find_min hex hm
    have hnone : ∀ m < n, ∀ c ∈ C, ¬ CenterContains S c m :=
      fun m hm c hc hcc => hmin m hm ⟨c, hc, hcc⟩
    obtain ⟨hhist', hiff⟩ := hstop n hnone
    have habs : HasAbsorptionAt T hm C n := Nat.find_spec hex
    obtain ⟨c₀, hc₀, hcc₀⟩ := habs
    have hn_le : n ≤ S.length := hcc₀.1.le
    -- a component of `h⁻¹(V(c₀))` exists (`h` is surjective)
    obtain ⟨η₀', hη₀'⟩ : ∃ η₀', η₀' ∈ (c₀.support.preimage h.continuous).genericPoints := by
      obtain ⟨η₀, hη₀eq⟩ := hC c₀ hc₀
      obtain ⟨x, hx⟩ := hs η₀
      have hxmem : x ∈ c₀.support.preimage h.continuous := by
        change h x ∈ c₀.support
        rw [hx, hη₀eq, support_vanishingIdeal_eq]
        exact subset_closure (Set.mem_singleton η₀)
      obtain ⟨η₀', hη₀', -⟩ := Closeds.exists_mem_genericPoints_specializes _ hxmem
      exact ⟨η₀', hη₀'⟩
    have hex' : ∃ n', HasAbsorptionAt T' hm' C' n' :=
      ⟨n, IdealSheafData.vanishingIdeal (Closeds.closure {η₀'}), (hCC' _).mpr ⟨c₀, hc₀, η₀', hη₀',
          rfl⟩,
        by rw [hR]; exact (hiff c₀ hc₀ η₀' hη₀').mpr hcc₀⟩
    have hfind : Nat.find hex' = n := by
      rw [Nat.find_eq_iff]
      refine ⟨⟨IdealSheafData.vanishingIdeal (Closeds.closure {η₀'}), (hCC' _).mpr ⟨c₀, hc₀, η₀',
          hη₀', rfl⟩,
        by rw [hR]; exact (hiff c₀ hc₀ η₀' hη₀').mpr hcc₀⟩, fun m hm => ?_⟩
      rintro ⟨c', hc', hcc'⟩
      rw [hR] at hcc'
      exact hhist' c' hc' m hm hcc'
    -- the round's data on the truncations; the lift `g` of the last stages
    have hQ : (S.take n).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E :=
      isOrderGeSeq_take _ _ _ _ (isOrderGeSeq_bmoOneRun T hm) n
    have hQ' : ((S.take n).pullback h).IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E :=
      hp.isOrderGeSeq_pullback hQ
    let g : ((S.take n).pullback h).stage (Fin.last _) ⟶ (S.take n).stage (Fin.last _) :=
      (S.take n).pullbackLastHom h
    have hsm : Smooth g := smooth_pullbackLastHom _ h
    have hsg : Function.Surjective g := surjective_pullbackLastHom _ h hs
    have hg : ∀ J : T.X.left.IdealSheafData,
        ((S.take n).pullback h).strictTransformSeq (J.comap h) (Fin.last _) =
          ((S.take n).strictTransformSeq J (Fin.last _)).comap g :=
      fun J => strictTransformSeq_pullback_last (S.take n) h J
    have hind : (T'.induced ((S.take n).pullback h) hQ' (Fin.last _)).IsPullbackOf
        (T.induced (S.take n) hQ (Fin.last _)) g :=
      MarkedTriple.isPullbackOf_induced_last h hp hQ hQ'
    have hhistQ : ∀ c ∈ C, ∀ m : Fin (S.take n).length,
        ¬ (S.take n).center m ≤ (S.take n).strictTransformSeq c m.castSucc :=
      fun c hc => forall_not_center_le_take S c hn_le (fun m hm => hnone m hm c hc)
    have hhistQ' : ∀ c' ∈ C', ∀ m : Fin ((S.take n).pullback h).length,
        ¬ ((S.take n).pullback h).center m ≤
          ((S.take n).pullback h).strictTransformSeq c' m.castSucc := by
      intro c' hc'
      rw [take_pullback]
      exact forall_not_center_le_take (S.pullback h) c' (by rwa [length_pullback])
        (fun m hm => hhist' c' hc' m hm)
    -- the absorbed families are related as components
    have hFF' : IsPullbackComponents h (C.filter fun c => CenterContains S c n)
        (C'.filter fun c' => CenterContains (S.pullback h) c' n) := by
      intro c'
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hc', hcc'⟩
        obtain ⟨c, hc, η', hη', rfl⟩ := (hCC' c').mp hc'
        exact ⟨c, ⟨hc, (hiff c hc η' hη').mp hcc'⟩, η', hη', rfl⟩
      · rintro ⟨c, ⟨hc, hcc⟩, η', hη', rfl⟩
        exact ⟨(hCC' _).mpr ⟨c, hc, η', hη', rfl⟩, (hiff c hc η' hη').mpr hcc⟩
    have hpg : (isolatedAt T' ((S.take n).pullback h) hQ'
        (C'.filter fun c' => CenterContains (S.pullback h) c' n)).IsPullbackOf
          (isolatedAt T (S.take n) hQ (C.filter fun c => CenterContains S c n)) g :=
      isolatedAt_isPullbackOf h (S.take n) hQ hQ' g hind _ _
        (iSup_support_strictTransformSeq_pullback_last (S.take n) h g hg _ _ hFF')
    have hprime' : ∀ c₁ ∈ remainingAt (S.take n) (C.filter fun c => ¬ CenterContains S c n),
        ∃ ζ : (S.take n).stage (Fin.last _), c₁ = IdealSheafData.vanishingIdeal (Closeds.closure
            {ζ}) :=
      remainingAt_prime (S.take n) _ (fun c hc => hC c (Finset.mem_filter.mp hc).1)
        (fun c hc => hhistQ c (Finset.mem_filter.mp hc).1)
    have hR' : IsPullbackComponents g
        (remainingAt (S.take n) (C.filter fun c => ¬ CenterContains S c n))
        (remainingAt ((S.take n).pullback h)
          (C'.filter fun c' => ¬ CenterContains (S.pullback h) c' n)) :=
      isPullbackComponents_remainingAt (S.take n) h g hg
        (fun hη' hh hh' => exists_genericPoints_strictTransformSeq_pullback_last (S.take n) h hη'
          hh hh')
        C C' hC hCC' _ _ (fun c hc η' hη' => not_congr (hiff c hc η' hη')) hhistQ hhistQ'
    have hlt : (remainingComponents T hm C n).card < N := by
      have := card_remainingComponents_lt T hm C hex
      rw [← hn, hcard] at this
      exact this
    have hIH := @ih _ hlt (isolatedTriple T hm C n)
      (isolatedAt T' ((S.take n).pullback h) hQ'
        (C'.filter fun c' => CenterContains (S.pullback h) c' n)) hm hm' g hsm hsg hpg
      (remainingComponents T hm C n)
      (remainingAt ((S.take n).pullback h)
        (C'.filter fun c' => ¬ CenterContains (S.pullback h) c' n)) rfl hprime' hR'
    -- assemble
    have hpc := pullback_concat ((bmoOneRun T hm).take n)
      (bedAux (isolatedTriple T hm C n) hm (remainingComponents T hm C n)) h
    rw [bedAux_eq_concat_of_find T' hm' C' hex' n hfind,
      bedAux_eq_concat_of_find T hm C hex n hn.symm,
      concat_bedAux_congr T' hm' C' n (by rw [hR, take_pullback]) hQ' (by rw [hR]) (by rw [hR]),
      hpc]
    exact congrArg (fun R => ((S.take n).pullback h).concat R) hIH
  · have hex' : ¬ ∃ n, HasAbsorptionAt T' hm' C' n := by
      rintro ⟨n, c', hc', hcc'⟩
      rw [hR] at hcc'
      obtain ⟨c, hc, η', hη', rfl⟩ := (hCC' c').mp hc'
      have hnone : ∀ m < n, ∀ c ∈ C, ¬ CenterContains S c m :=
        fun m _ c hc hcc => hex ⟨m, c, hc, hcc⟩
      exact hex ⟨n, c, hc, ((hstop n hnone).2 c hc η' hη').mp hcc'⟩
    rw [bedAux_of_not_exists T' hm' C' hex', bedAux_of_not_exists T hm C hex]
    exact hR

/-- **`BED` commutes with smooth surjections** ([Wlo05, Theorem 1.0.2] clause (d), [Wlo05, 4.1];
the first bullet of [Kol07, 34.1]): for a smooth surjection `h : X' → X` carrying the pull-back
data, `BED(X', h^* I_Y, ∅) = h^* BED(X, I_Y, ∅)` — the loop `bedAux_pullback_of_surjective` on the
components of `V(I_Y)` and of `V(h^* I_Y)` (`isPullbackComponents_componentIdeals`). The
hypothesis `hE` is present because clause (d) of [Wlo05, Theorem 1.0.2] is stated for the
embedded desingularization of `Y` with empty boundary, the setting in which
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFunctorClauses` applies this theorem; the proof does
not need it, because the transport of the loop works for any marked triple of mark `1` whose members
are the reduced ideals of the components (`componentIdeals_prime`). -/
theorem bed_pullback_of_surjective (TX TX' : Triple k) (hE : IsEmpty TX.E.ι)
    (h : TX'.X.left ⟶ TX.X.left) [Smooth h] (hs : Function.Surjective h)
    (hp : TX'.IsPullbackOf TX h) : BED TX' = (BED TX).pullback h := by
  have _ := hE
  exact bedAux_pullback_of_surjective _ ⟨TX, 1⟩ ⟨TX', 1⟩ rfl rfl h hs ⟨hp, rfl⟩
    (componentIdeals TX) (componentIdeals TX') rfl (componentIdeals_prime TX)
    (isPullbackComponents_componentIdeals TX TX' h hp)

end Hironaka.Resolution
