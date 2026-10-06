/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFunctor
public import Hironaka.Resolution.Algebraic.Kol07.Thm36.CentersMiss
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Local
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Reduced
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineEndResult
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification
import Hironaka.Resolution.Algebraic.Smooth.GeometricallyReduced
import Hironaka.Resolution.Algebraic.Snc.DictionaryComponents
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilCoreTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedOrderGe
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Algebra.Order.Module.Field
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The clopen split of a smooth scheme along the components inside a closed subscheme

The split `X = X₀ ⊔ X₁` behind the embedded desingularization functor `EDFunctor`
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFunctor`): `X₁ = componentsOutside Y` is the union of
the irreducible components of `X` not contained in `V(Y)`, `X₀` its complement, and the core
`coreIdeal Y = vanishingIdeal (V(Y) ∩ X₁)` is the ideal the sequence `BED` runs on.

* On a smooth `X` two irreducible components through a point coincide
  (`eq_of_mem_irreducibleComponents_of_smooth`): their generic points `η₁, η₂ ⤳ x` have closure
  ideals whose stalks at `x` are minimal primes over `⊥` in the regular — hence domain — stalk, so
  both are `⊥` and `η₁ = η₂` (`eq_of_stalkIdeal_vanishingIdeal_closure_eq`). Hence every component
  is open (`isOpen_of_mem_irreducibleComponents_of_smooth`) and both `X₁` and `X₀` are open
  (`isOpen_componentsOutside`, `isOpen_compl_componentsOutside`).
* Over `X₀ ⊆ V(Y)` the reduced `Y` is zero (`stalkIdeal_eq_bot_of_notMem_componentsOutside`: on
  an affine open inside `X₀` the reduced ideal of `V(Y)` is that of the whole space, the nilradical
  of the reduced stalk); over `X₁` the core agrees with `Y`
  (`stalkIdeal_coreIdeal_of_mem_componentsOutside`).
* The theorem's image hypothesis on a smooth `h` transfers from `Y` to its core
  (`hmeets_coreIdeal`): a point of `V(Y) ∩ X₁` maximal for specialization there is maximal in
  `V(Y)`, `X₁` being open.
* No centre of the run lies over `X₀`
  (`notMem_center_support_of_stageMap_notMem_componentsOutside`):
  the run is of order `≥ 1` for the core (`isOrderGeSeq_BED`), whose cosupport `V(Y) ∩ X₁` misses
  `X₀` (`centersMiss_of_isOrderGeSeq`).
* The smooth locus of a closed subscheme is read on the restrictions along an open immersion
  (`subschemeRestrict`, `mem_image_smoothLocus_iff_of_isOpenImmersion`): over `X₁` the smooth points
  of `Y` and of its core coincide (`mem_image_smoothLocus_coreIdeal_iff`), and a closed subscheme
  smooth on each of two complementary clopens is smooth (`smooth_subschemeι_comp_of_isClopen`).
* The exchange with smooth morphisms (`componentsOutside_comap` — for flat `h` —, `coreIdeal_comap`)
  and the transfer of the clauses: on the run the last strict transforms of `Y` and of its core
  agree over `X₁` while that of `Y` is zero over `X₀`, so the core's clauses (c1), (c2), (e) and
  the clause (b) about the smooth points of `Y` transfer to `Y`
  (`smooth_strictTransformSeq_last_of_coreIdeal`, `hasSncWith_strictTransformSeq_last_of_coreIdeal`,
  `comap_composite_eq_strictTransform_mul_of_coreIdeal`,
  `stageMap_notMem_image_smoothLocus_of_coreIdeal`).

The clauses are those of [Wlo05, Theorem 1.0.2]; the equidimensionality convention is
[Kol07, Notation 64]. These are the tools of
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFunctorClauses`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing Scheme BlowUpSequence
  Scheme.IdealSheafData CategoryTheory.Limits

namespace Hironaka.Resolution

section Components

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]

include f in
/-- On a smooth scheme two irreducible components through a point coincide: at the point the stalk
is a domain, the closure ideals of the two generic points have stalks that are minimal primes over
`⊥`, hence both `⊥`, and equal stalks force equal generic points
(`eq_of_stalkIdeal_vanishingIdeal_closure_eq`). Compare
`eq_of_mem_irreducibleComponents_of_isRegular`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification`), the same fact for a regular closed
subscheme. -/
theorem eq_of_mem_irreducibleComponents_of_smooth {C₁ C₂ : Set X}
    (h₁ : C₁ ∈ irreducibleComponents X) (h₂ : C₂ ∈ irreducibleComponents X) {x : X}
    (hx₁ : x ∈ C₁) (hx₂ : x ∈ C₂) : C₁ = C₂ := by
  have hreg := isRegularLocalRing_stalk f x
  have hmin : ∀ {η : X} (W : Set X), W ∈ irreducibleComponents X → IsGenericPoint η W → η ⤳ x →
      (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal x = ⊥ := by
    intro η W hW hη hηx
    have hgen : η ∈ (⊥ : X.IdealSheafData).support.genericPoints :=
      mem_genericPoints_of_isGenericPoint_of_mem hW hη _ (by
        rw [IdealSheafData.support_bot]
        trivial)
    have hmem := Hironaka.Sequence.stalkIdeal_vanishingIdeal_mem_minimalPrimes ⊥ hgen hηx
    rw [IdealSheafData.stalkIdeal_bot] at hmem
    have hmin' : Minimal (fun q : Ideal (X.presheaf.stalk x) => q.IsPrime ∧ (⊥ : Ideal _) ≤ q)
        ((IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal x) := hmem
    exact le_bot_iff.mp (hmin'.2 ⟨Ideal.isPrime_bot, le_rfl⟩ bot_le)
  have hirr₁ : IsIrreducible C₁ := h₁.1
  have hirr₂ : IsIrreducible C₂ := h₂.1
  have hg₁ := hirr₁.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C₁ h₁)
  have hg₂ := hirr₂.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C₂ h₂)
  have hs₁ : hirr₁.genericPoint ⤳ x := hg₁.specializes hx₁
  have hs₂ : hirr₂.genericPoint ⤳ x := hg₂.specializes hx₂
  have e := Hironaka.Sequence.eq_of_stalkIdeal_vanishingIdeal_closure_eq hs₁ hs₂
    ((hmin C₁ h₁ hg₁ hs₁).trans (hmin C₂ h₂ hg₂ hs₂).symm)
  calc C₁ = closure {hirr₁.genericPoint} := hg₁.def.symm
    _ = closure {hirr₂.genericPoint} := by rw [e]
    _ = C₂ := hg₂.def

variable [NoetherianSpace X]

include f in
/-- On a smooth Noetherian scheme every irreducible component is open (its complement is the finite
union of the other components, which it does not meet). -/
theorem isOpen_of_mem_irreducibleComponents_of_smooth {C : Set X}
    (hC : C ∈ irreducibleComponents X) : IsOpen C := by
  obtain ⟨x, hx⟩ := hC.1.nonempty
  have hCx : C = irreducibleComponent x :=
    eq_of_mem_irreducibleComponents_of_smooth f hC
      (irreducibleComponent_mem_irreducibleComponents x) hx mem_irreducibleComponent
  rw [hCx]
  exact isOpen_irreducibleComponent_of_inter_nonempty_imp_eq
    (fun C₁ h₁ C₂ h₂ hne => by
      obtain ⟨y, hy₁, hy₂⟩ := hne
      exact eq_of_mem_irreducibleComponents_of_smooth f h₁ h₂ hy₁ hy₂) x

variable (Y : X.IdealSheafData)

include f in
/-- `X₁ = componentsOutside Y` is open on a smooth Noetherian scheme (a union of components). -/
theorem isOpen_componentsOutside : IsOpen (componentsOutside Y : Set X) := by
  change IsOpen (⋃₀ {C | C ∈ irreducibleComponents X ∧ ¬ C ⊆ (Y.support : Set X)})
  exact isOpen_sUnion fun C hC => isOpen_of_mem_irreducibleComponents_of_smooth f hC.1

include f in
/-- On a smooth scheme a point lies in `X₁` iff ITS component is not inside `V(Y)`. -/
theorem mem_componentsOutside_iff_of_smooth (x : X) :
    x ∈ componentsOutside Y ↔ ¬ irreducibleComponent x ⊆ (Y.support : Set X) := by
  rw [mem_componentsOutside_iff]
  constructor
  · rintro ⟨C, hC, hCY, hxC⟩
    rwa [eq_of_mem_irreducibleComponents_of_smooth f
      (irreducibleComponent_mem_irreducibleComponents x) hC mem_irreducibleComponent hxC]
  · intro h
    exact ⟨_, irreducibleComponent_mem_irreducibleComponents x, h, mem_irreducibleComponent⟩

include f in
/-- The clopen split: `X₀`, the complement of `componentsOutside Y`, is open — it is the union
of the components inside `V(Y)`, each open. -/
theorem isOpen_compl_componentsOutside : IsOpen ((componentsOutside Y : Set X)ᶜ) := by
  have h : (componentsOutside Y : Set X)ᶜ =
      ⋃₀ {C | C ∈ irreducibleComponents X ∧ C ⊆ (Y.support : Set X)} := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe, mem_componentsOutside_iff_of_smooth f Y x,
      not_not, Set.mem_sUnion, Set.mem_ofPred_eq]
    constructor
    · intro hsub
      exact ⟨_, ⟨irreducibleComponent_mem_irreducibleComponents x, hsub⟩, mem_irreducibleComponent⟩
    · rintro ⟨C, ⟨hC, hCY⟩, hxC⟩
      rwa [eq_of_mem_irreducibleComponents_of_smooth f
        (irreducibleComponent_mem_irreducibleComponents x) hC mem_irreducibleComponent hxC]
  rw [h]
  exact isOpen_sUnion fun C hC => isOpen_of_mem_irreducibleComponents_of_smooth f hC.1

omit f [Smooth f] in
/-- the components inside `V(Y)` lie in `V(Y)` — every point lies on its component. -/
theorem compl_componentsOutside_subset_support :
    (componentsOutside Y : Set X)ᶜ ⊆ (Y.support : Set X) := by
  intro x hx
  by_contra hxY
  exact hx ((mem_componentsOutside_iff Y x).mpr
    ⟨_, irreducibleComponent_mem_irreducibleComponents x,
      fun h => hxY (h mem_irreducibleComponent), mem_irreducibleComponent⟩)

include f in
/-- over `X₀` the reduced `Y` is the zero ideal — `X₀` is an open subset of `V(Y)` in the
reduced `X`, so on an affine open inside `X₀` the reduced ideal of `V(Y)` is that of the whole
space, whose stalk is the nilradical of the reduced stalk. -/
theorem stalkIdeal_eq_bot_of_notMem_componentsOutside [CharZero k] [IsReduced Y.subscheme] {x : X}
    (hx : x ∉ componentsOutside Y) : Y.stalkIdeal x = ⊥ := by
  have hred : IsReduced X := isReduced_of_isRegular (isRegular_of_smooth f)
  obtain ⟨U, hxU⟩ := IdealSheafData.exists_affineOpens_mem x
  obtain ⟨s, hs_le, hxs⟩ := U.2.exists_basicOpen_le
    (V := ⟨_, isOpen_compl_componentsOutside f Y⟩) ⟨x, hx⟩ hxU
  have hVY : ∀ y ∈ (X.affineBasicOpen s).1, y ∈ Y.support ↔ y ∈ (⊤ : Closeds X) := fun y hy =>
    ⟨fun _ => trivial, fun _ => compl_componentsOutside_subset_support Y (hs_le hy)⟩
  have h1 : IdealSheafData.vanishingIdeal (⊤ : Closeds X) = (⊥ : X.IdealSheafData).radical := by
    rw [← IdealSheafData.vanishingIdeal_support, IdealSheafData.support_bot]
  have h2 : (⊥ : Ideal (X.presheaf.stalk x)).radical = ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact nilradical_eq_zero _
  rw [← vanishingIdeal_support_of_isReduced Y,
    stalkIdeal_vanishingIdeal_congr (X.affineBasicOpen s) hxs hVY, h1,
    Hironaka.Sequence.stalkIdeal_radical, IdealSheafData.stalkIdeal_bot, h2]

include f in
/-- Over `X₁` the core agrees with `Y` stalkwise: on an affine open inside the open `X₁`,
`V(Y) ∩ X₁` is `V(Y)`, and `Y` is the reduced ideal of `V(Y)`. -/
theorem stalkIdeal_coreIdeal_of_mem_componentsOutside [IsReduced Y.subscheme] {x : X}
    (hx : x ∈ componentsOutside Y) : (coreIdeal Y).stalkIdeal x = Y.stalkIdeal x := by
  obtain ⟨U, hxU⟩ := IdealSheafData.exists_affineOpens_mem x
  obtain ⟨s, hs_le, hxs⟩ := U.2.exists_basicOpen_le
    (V := ⟨_, isOpen_componentsOutside f Y⟩) ⟨x, hx⟩ hxU
  have hVY : ∀ y ∈ (X.affineBasicOpen s).1,
      y ∈ Y.support ⊓ componentsOutside Y ↔ y ∈ Y.support := fun y hy => by
    change y ∈ ((Y.support ⊓ componentsOutside Y : Closeds X) : Set X) ↔ _
    rw [Closeds.coe_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, hs_le hy⟩⟩
  rw [coreIdeal, stalkIdeal_vanishingIdeal_congr (X.affineBasicOpen s) hxs hVY,
    vanishingIdeal_support_of_isReduced]

include f in
/-- The transfer of the image hypothesis from `Y` to its core (the smoothness of `X` is needed): a
point of `V(core Y) = V(Y) ∩ X₁` maximal for specialization there is maximal in `V(Y)` — a
generization in `V(Y)` of a point of the open `X₁` lies in `X₁` — so the theorem's hypothesis on
`h`'s image implies the core's. -/
theorem hmeets_coreIdeal {X' : Scheme.{u}} (h : X' ⟶ X)
    (hmeets : ∀ η ∈ (Y.support : Set X), (∀ η' ∈ (Y.support : Set X), η' ⤳ η → η' = η) →
      (Set.range h ∩ closure {η}).Nonempty) :
    ∀ η ∈ ((coreIdeal Y).support : Set X),
      (∀ η' ∈ ((coreIdeal Y).support : Set X), η' ⤳ η → η' = η) →
        (Set.range h ∩ closure {η}).Nonempty := by
  intro η hη hmax
  rw [support_coreIdeal, Closeds.coe_inf] at hη
  refine hmeets η hη.1 fun η' hη' hsp => hmax η' ?_ hsp
  rw [support_coreIdeal, Closeds.coe_inf]
  exact ⟨hη', hsp.mem_open (isOpen_componentsOutside f Y) hη.2⟩

end Components

section Run

variable {k : Type u} [Field k] [CharZero k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k))] [Smooth (X ↘ Spec (CommRingCat.of k))]
  [NoetherianSpace X] (Y : X.IdealSheafData)

/-- No centre over `X₀`: the run of the functor misses `X₀` — it is a run of order `≥ 1` for the
core (`isOrderGeSeq_BED`), whose cosupport `V(Y) ∩ X₁` is inside `X₁`
(`centersMiss_of_isOrderGeSeq`); off the equidimensional schemes the run is empty. -/
theorem centersMiss_EDFunctor_compl_componentsOutside :
    CentersMiss ((EDFunctor k).seq X Y) ((componentsOutside Y : Set X)ᶜ) := by
  by_cases hX : ∃ n : ℕ, SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of k))
  · obtain ⟨n, hn⟩ := hX
    rw [EDFunctor_seq_of_pos X Y ⟨n, hn⟩]
    refine centersMiss_of_isOrderGeSeq (X ↘ Spec (CommRingCat.of k)) n (isOrderGeSeq_BED _)
      le_rfl _ fun x hx => ?_
    have hx' : x ∈ ((Y.support ⊓ componentsOutside Y : Closeds X) : Set X) := by
      rw [← support_coreIdeal]
      exact hx
    rw [Closeds.coe_inf] at hx'
    exact fun h => h hx'.2
  · rw [EDFunctor_seq_of_neg X Y hX]
    exact centersMiss_nil _

/-- Pointwise: a point of a centre of the run of the functor does not lie over `X₀`. -/
theorem notMem_center_support_of_stageMap_notMem_componentsOutside
    (i : Fin ((EDFunctor k).seq X Y).length) (x : ((EDFunctor k).seq X Y).stage i.castSucc)
    (hx : ((EDFunctor k).seq X Y).stageMap i.castSucc x ∉ componentsOutside Y) :
    x ∉ (((EDFunctor k).seq X Y).center i).support :=
  fun hxc => centersMiss_EDFunctor_compl_componentsOutside X Y i x hxc hx

end Run

/-! ### The run over the two clopens -/

section RunLocal

variable {k : Type u} [Field k] [CharZero k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k))] [Smooth (X ↘ Spec (CommRingCat.of k))]
  [NoetherianSpace X] (Y : X.IdealSheafData)

variable (k) in
/-- `X₀`, the union of the components inside `V(Y)`, as an open of `X`. -/
noncomputable def insideOpens : X.Opens :=
  ⟨(componentsOutside Y : Set X)ᶜ, isOpen_compl_componentsOutside (X ↘ Spec (CommRingCat.of k)) Y⟩

variable (k) in
/-- `X₁`, the union of the components outside `V(Y)`, as an open of `X`. -/
noncomputable def outsideOpens : X.Opens :=
  ⟨(componentsOutside Y : Set X), isOpen_componentsOutside (X ↘ Spec (CommRingCat.of k)) Y⟩

/-- Pulled back to `X₀`, the run of the functor has only empty centres (no centre lies over
`X₀`). -/
theorem center_pullback_insideOpens_eq_top
    (i : Fin (((EDFunctor k).seq X Y).pullback (insideOpens k X Y).ι).length) :
    (((EDFunctor k).seq X Y).pullback (insideOpens k X Y).ι).center i = ⊤ :=
  forall_center_pullback_eq_top_of_centersMiss _ _ (by
    rw [Scheme.Opens.range_ι]
    exact centersMiss_EDFunctor_compl_componentsOutside X Y) i

omit [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsSeparated (X ↘ Spec (CommRingCat.of k))] in
/-- Over `X₀` the reduced `Y` pulls back to the zero ideal sheaf. -/
theorem comap_insideOpens_ι_eq_bot [IsReduced Y.subscheme] :
    Y.comap (insideOpens k X Y).ι = ⊥ := by
  refine IdealSheafData.ext_stalkIdeal fun w => ?_
  have hb : Y.stalkIdeal ((insideOpens k X Y).ι w) = ⊥ :=
    stalkIdeal_eq_bot_of_notMem_componentsOutside (X ↘ Spec (CommRingCat.of k)) Y w.2
  rw [IdealSheafData.stalkIdeal_comap, IdealSheafData.stalkIdeal_bot, hb, Ideal.map_bot]

omit [CharZero k] [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k))] in
/-- Over `X₁` the core and `Y` pull back to the same ideal sheaf. -/
theorem comap_outsideOpens_ι_coreIdeal [IsReduced Y.subscheme] :
    (coreIdeal Y).comap (outsideOpens k X Y).ι = Y.comap (outsideOpens k X Y).ι := by
  refine IdealSheafData.ext_stalkIdeal fun w => ?_
  have h : (coreIdeal Y).stalkIdeal ((outsideOpens k X Y).ι w) =
      Y.stalkIdeal ((outsideOpens k X Y).ι w) :=
    stalkIdeal_coreIdeal_of_mem_componentsOutside (X ↘ Spec (CommRingCat.of k)) Y w.2
  rw [IdealSheafData.stalkIdeal_comap, IdealSheafData.stalkIdeal_comap, h]

/-- A point of a stage of the run lying over `X₀` is in the image of the stage of the pull-back. -/
theorem exists_pullbackStageHom_insideOpens_eq (i : Fin (((EDFunctor k).seq X Y).length + 1))
    (x : ((EDFunctor k).seq X Y).stage i)
    (hx : ((EDFunctor k).seq X Y).stageMap i x ∉ componentsOutside Y) :
    ∃ w, ((EDFunctor k).seq X Y).pullbackStageHom (insideOpens k X Y).ι i w = x := by
  have hr : x ∈ Set.range (((EDFunctor k).seq X Y).pullbackStageHom (insideOpens k X Y).ι i) := by
    rw [range_pullbackStageHom, Scheme.Opens.range_ι]
    exact hx
  exact hr

/-- A point of a stage of the run lying over `X₁` is in the image of the stage of the pull-back. -/
theorem exists_pullbackStageHom_outsideOpens_eq (i : Fin (((EDFunctor k).seq X Y).length + 1))
    (x : ((EDFunctor k).seq X Y).stage i)
    (hx : ((EDFunctor k).seq X Y).stageMap i x ∈ componentsOutside Y) :
    ∃ w, ((EDFunctor k).seq X Y).pullbackStageHom (outsideOpens k X Y).ι i w = x := by
  have hr : x ∈ Set.range (((EDFunctor k).seq X Y).pullbackStageHom (outsideOpens k X Y).ι i) := by
    rw [range_pullbackStageHom, Scheme.Opens.range_ι]
    exact hx
  exact hr

/-- The strict transform of `Y` over `X₀` is the zero ideal at the points over `X₀` — pulled back
to `X₀` the run has empty centres, so the strict transform is the pull-back of `Y|_{X₀} = 0`. -/
theorem stalkIdeal_strictTransformSeq_eq_bot_of_stageMap_notMem_componentsOutside
    [IsReduced Y.subscheme] (i : Fin (((EDFunctor k).seq X Y).length + 1))
    (x : ((EDFunctor k).seq X Y).stage i)
    (hx : ((EDFunctor k).seq X Y).stageMap i x ∉ componentsOutside Y) :
    (((EDFunctor k).seq X Y).strictTransformSeq Y i).stalkIdeal x = ⊥ := by
  obtain ⟨w, rfl⟩ := exists_pullbackStageHom_insideOpens_eq X Y i x hx
  have hst :=
    strictTransformSeq_pullback ((EDFunctor k).seq X Y) (insideOpens k X Y).ι Y i
  rw [strictTransformSeq_eq_comap_of_forall_center_eq_top _
    (center_pullback_insideOpens_eq_top X Y), comap_insideOpens_ι_eq_bot X Y,
        IdealSheafData.comap_bot] at hst
  have := isOpenImmersion_pullbackStageHom ((EDFunctor k).seq X Y)
    (insideOpens k X Y).ι i
  rw [Hironaka.Sequence.stalkIdeal_eq_map_symm_stalkIdeal_comap
    (((EDFunctor k).seq X Y).pullbackStageHom (insideOpens k X Y).ι i), ← hst,
        IdealSheafData.stalkIdeal_bot,
    Ideal.map_bot]

/-- No exceptional member over `X₀`: no member of the total transform of the empty family
passes through a point over `X₀` — pulled back to `X₀` every centre is empty, so every member of
the pulled-back total transform is the unit ideal. -/
theorem notMem_totalTransformSeq_component_support_of_stageMap_notMem_componentsOutside
    (i : Fin (((EDFunctor k).seq X Y).length + 1))
    (j : (((EDFunctor k).seq X Y).totalTransformSeq (DivisorFamily.empty X) i).ι)
    (x : ((EDFunctor k).seq X Y).stage i)
    (hx : ((EDFunctor k).seq X Y).stageMap i x ∉ componentsOutside Y) :
    x ∉ ((((EDFunctor k).seq X Y).totalTransformSeq (DivisorFamily.empty X) i).component
      j).support := by
  obtain ⟨w, rfl⟩ := exists_pullbackStageHom_insideOpens_eq X Y i x hx
  have htt := totalTransformSeq_pullback ((EDFunctor k).seq X Y)
    (insideOpens k X Y).ι (DivisorFamily.empty X) i
  have hcomp := totalTransformSeq_component_eq_top_of_forall_center_eq_top _
    (center_pullback_insideOpens_eq_top X Y) ((DivisorFamily.empty X).comap (insideOpens k X Y).ι)
    (fun e => e.elim) (((EDFunctor k).seq X Y).pullbackStageIdx (insideOpens k X Y).ι i)
  rw [htt] at hcomp
  have hj : ((((EDFunctor k).seq X Y).totalTransformSeq (DivisorFamily.empty X) i).component
      j).comap (((EDFunctor k).seq X Y).pullbackStageHom (insideOpens k X Y).ι i) = ⊤ := hcomp j
  have := isOpenImmersion_pullbackStageHom ((EDFunctor k).seq X Y)
    (insideOpens k X Y).ι i
  intro hmem
  have hle := (IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp hmem
  rw [Hironaka.Sequence.stalkIdeal_eq_map_symm_stalkIdeal_comap
    (((EDFunctor k).seq X Y).pullbackStageHom (insideOpens k X Y).ι i), hj,
        IdealSheafData.stalkIdeal_top,
    Ideal.map_top] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hle)

/-- Locality over `X₁`: over `X₁` the strict transforms of `Y` and of its core agree — both
are the pull-backs along `X₁ ↪ X` of the same ideal sheaf (`strictTransformSeq_pullback`). -/
theorem stalkIdeal_strictTransformSeq_coreIdeal_of_stageMap_mem_componentsOutside
    [IsReduced Y.subscheme] (i : Fin (((EDFunctor k).seq X Y).length + 1))
    (x : ((EDFunctor k).seq X Y).stage i)
    (hx : ((EDFunctor k).seq X Y).stageMap i x ∈ componentsOutside Y) :
    (((EDFunctor k).seq X Y).strictTransformSeq (coreIdeal Y) i).stalkIdeal x =
      (((EDFunctor k).seq X Y).strictTransformSeq Y i).stalkIdeal x := by
  obtain ⟨w, rfl⟩ := exists_pullbackStageHom_outsideOpens_eq X Y i x hx
  have h1 := strictTransformSeq_pullback ((EDFunctor k).seq X Y)
    (outsideOpens k X Y).ι (coreIdeal Y) i
  have h2 := strictTransformSeq_pullback ((EDFunctor k).seq X Y)
    (outsideOpens k X Y).ι Y i
  rw [comap_outsideOpens_ι_coreIdeal X Y] at h1
  have := isOpenImmersion_pullbackStageHom ((EDFunctor k).seq X Y)
    (outsideOpens k X Y).ι i
  rw [Hironaka.Sequence.stalkIdeal_eq_map_symm_stalkIdeal_comap
    (((EDFunctor k).seq X Y).pullbackStageHom (outsideOpens k X Y).ι i)
    (((EDFunctor k).seq X Y).strictTransformSeq (coreIdeal Y) i),
    Hironaka.Sequence.stalkIdeal_eq_map_symm_stalkIdeal_comap
    (((EDFunctor k).seq X Y).pullbackStageHom (outsideOpens k X Y).ι i)
    (((EDFunctor k).seq X Y).strictTransformSeq Y i), ← h1, ← h2]

end RunLocal

/-! ### The remaining glue: a point on no member; the exchange along a flat morphism -/

section Glue

variable {B : Scheme.{u}}

/-- Clause (c2) at a point with no member through it: a regular system of parameters is an
snc system for `E` at a point lying on no member of `E` — the index type of the members through the
point is empty. -/
theorem isSncAt_of_forall_notMem_support (E : DivisorFamily B) (x : B)
    (hx : ∀ j, x ∉ (E.component j).support) {n : ℕ} (z : Fin n → B.presheaf.stalk x)
    (hz : IsRegularSystemOfParameters z) : E.IsSncAt x z :=
  ⟨hz, fun i => (hx i.1 i.2).elim, fun a _ _ => (hx a.1 a.2).elim, fun i => (hx i.1 i.2).elim⟩

end Glue

section Exchange

variable {X X' : Scheme.{u}} [NoetherianSpace X] [NoetherianSpace X'] (h : X' ⟶ X) [Flat h]

omit [NoetherianSpace X'] in
/-- An irreducible set lies in an irreducible component. -/
theorem exists_mem_irreducibleComponents_subset {s : Set X'} (hs : IsIrreducible s) :
    ∃ C ∈ irreducibleComponents X', s ⊆ C := by
  obtain ⟨t, ht, hst, hmax⟩ := exists_preirreducible s hs.2
  refine ⟨t, ⟨⟨hs.1.mono hst, ht⟩, fun u hu htu => (hmax u hu.2 htu).le⟩, hst⟩

omit [NoetherianSpace X] [NoetherianSpace X'] in
/-- The generic point of a component not inside a closed set lies outside it. -/
theorem genericPoint_notMem_of_not_subset {C : Set X} (hC : C ∈ irreducibleComponents X)
    {S : Set X} (hS : IsClosed S) (hCS : ¬ C ⊆ S) :
    hC.1.genericPoint ∉ S := by
  intro hmem
  apply hCS
  rw [← (hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)).def]
  exact closure_minimal (Set.singleton_subset_iff.mpr hmem) hS

/-- The exchange with a flat morphism, components: for a flat `h : X' → X` a component of `X'`
lies in `V(h^*Y)` iff the component of `X` through its image does — `h` is generalizing
(`Flat.generalizingMap`): the generic point of a component of `X` through `h x'` lifts to a
generization of `x'`, whose closure lies in a component of `X'` not inside `h⁻¹ V(Y)`; conversely
the image of a component of `X'` is an irreducible set inside a component of `X`. -/
theorem componentsOutside_comap (Y : X.IdealSheafData) :
    componentsOutside (Y.comap h) = (componentsOutside Y).preimage h.continuous := by
  refine Closeds.ext (Set.ext fun x' => ?_)
  change x' ∈ componentsOutside (Y.comap h) ↔
    x' ∈ ((componentsOutside Y).preimage h.continuous : Set X')
  rw [mem_componentsOutside_iff]
  change _ ↔ h x' ∈ (componentsOutside Y : Set X)
  rw [SetLike.mem_coe, mem_componentsOutside_iff]
  constructor
  · rintro ⟨C', hC', hC'Y, hxC'⟩
    have himg : IsIrreducible (h '' C') := hC'.1.image h h.continuous.continuousOn
    obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset (X' := X) himg
    refine ⟨C, hC, fun hCY => hC'Y fun c' hc' => ?_, hsub ⟨x', hxC', rfl⟩⟩
    have : h c' ∈ (Y.support : Set X) := hCY (hsub ⟨c', hc', rfl⟩)
    rw [IdealSheafData.support_comap]
    exact this
  · rintro ⟨C, hC, hCY, hxC⟩
    have hgen := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
    obtain ⟨η', hη'x, hη'⟩ := Flat.generalizingMap h (hgen.specializes hxC)
    obtain ⟨C', hC', hsub⟩ := exists_mem_irreducibleComponents_subset
      (X' := X') ((isIrreducible_iff_closure (s := {η'})).mpr isIrreducible_singleton)
    refine ⟨C', hC', fun hC'Y => ?_, hsub (hη'x.mem_closure)⟩
    have hη'mem : η' ∈ ((Y.comap h).support : Set X') := hC'Y (hsub (subset_closure rfl))
    rw [IdealSheafData.support_comap] at hη'mem
    change h η' ∈ (Y.support : Set X) at hη'mem
    rw [hη'] at hη'mem
    exact genericPoint_notMem_of_not_subset hC Y.support.isClosed hCY hη'mem

/-- The exchange with a smooth morphism, cores: `core (h^* Y) = h^* (core Y)` for smooth `h` — the
component exchange, `support_comap`, and `comap_vanishingIdeal_of_smooth`. -/
theorem coreIdeal_comap [Smooth h] (Y : X.IdealSheafData) :
    coreIdeal (Y.comap h) = (coreIdeal Y).comap h := by
  unfold coreIdeal
  rw [Hironaka.Smooth.comap_vanishingIdeal_of_smooth h]
  congr 1
  refine Closeds.ext ?_
  rw [Closeds.coe_inf, IdealSheafData.support_comap, componentsOutside_comap h Y]
  rfl

end Exchange

section SmoothLocusLocal

variable {X W T : Scheme.{u}} (Z : X.IdealSheafData) (ι : W ⟶ X) [IsOpenImmersion ι]

/-- The second leg `V(ι^* Z) → V(Z)` of Mathlib's pull-back square of `Z.subschemeι` along `ι`
(`comapIso`); an open immersion when `ι` is. -/
noncomputable def subschemeRestrict : (Z.comap ι).subscheme ⟶ Z.subscheme :=
  (Z.comapIso ι).hom ≫ pullback.snd ι Z.subschemeι

instance isOpenImmersion_subschemeRestrict : IsOpenImmersion (subschemeRestrict Z ι) := by
  unfold subschemeRestrict
  infer_instance

omit [IsOpenImmersion ι] in
/-- The restriction square commutes: `V(ι^* Z) → V(Z) → X` is `V(ι^* Z) → W → X`. -/
theorem subschemeRestrict_subschemeι :
    subschemeRestrict Z ι ≫ Z.subschemeι = (Z.comap ι).subschemeι ≫ ι := by
  rw [subschemeRestrict, Category.assoc, ← pullback.condition, ← Category.assoc,
    IdealSheafData.comapIso_hom_fst]

omit [IsOpenImmersion ι] in
/-- The image of the restriction is the part of `V(Z)` over `W` (the square is a pull-back). -/
theorem range_subschemeRestrict :
    Set.range (subschemeRestrict Z ι) = Z.subschemeι ⁻¹' Set.range ι := by
  have hp : IsPullback (pullback.snd ι Z.subschemeι) (pullback.fst ι Z.subschemeι) Z.subschemeι ι :=
    (IsPullback.of_hasPullback ι Z.subschemeι).flip
  rw [← range_fst_of_isPullback hp]
  ext y
  constructor
  · rintro ⟨w', rfl⟩
    exact ⟨(Z.comapIso ι).hom w', (Scheme.Hom.comp_apply _ _ w').symm⟩
  · rintro ⟨p, rfl⟩
    refine ⟨(Z.comapIso ι).inv p, ?_⟩
    change ((Z.comapIso ι).hom ≫ pullback.snd ι Z.subschemeι) ((Z.comapIso ι).inv p) = _
    rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (Z.comapIso ι).inv (Z.comapIso ι).hom p,
      Iso.inv_hom_id]
    rfl

/-- The smooth locus of two equal morphisms is the same. -/
theorem smoothLocus_congr {A B : Scheme.{u}} {f g : A ⟶ B} [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation g] (e : f = g) : f.smoothLocus = g.smoothLocus := by
  subst e
  rfl

variable (g : X ⟶ T) [LocallyOfFinitePresentation (Z.subschemeι ≫ g)]
  [LocallyOfFinitePresentation ((Z.comap ι).subschemeι ≫ ι ≫ g)]

/-- Smooth-locus locality along an open immersion: a point of `V(Z)` over `W` is smooth over `T` iff
its preimage in `V(Z) ∩ W` is smooth for the restricted composite (`preimage_smoothLocus_eq`). -/
theorem mem_smoothLocus_subschemeRestrict_iff (w' : (Z.comap ι).subscheme) :
    subschemeRestrict Z ι w' ∈ (Z.subschemeι ≫ g).smoothLocus ↔
      w' ∈ ((Z.comap ι).subschemeι ≫ ι ≫ g).smoothLocus := by
  have h := Scheme.Hom.preimage_smoothLocus_eq (subschemeRestrict Z ι) (Z.subschemeι ≫ g)
  have e : subschemeRestrict Z ι ≫ Z.subschemeι ≫ g = (Z.comap ι).subschemeι ≫ ι ≫ g := by
    rw [← Category.assoc, subschemeRestrict_subschemeι, Category.assoc]
  rw [smoothLocus_congr e] at h
  rw [← h]
  rfl

/-- Smooth points of `V(Z)` over `W`, read on `V(Z) ∩ W`: a point `ι w` lies in the image of the
smooth locus of `V(Z) → T` iff it is the image of a point of `V(Z) ∩ W` smooth for the restricted
composite. -/
theorem mem_image_smoothLocus_iff_of_isOpenImmersion (w : W) :
    ι w ∈ Z.subschemeι '' ((Z.subschemeι ≫ g).smoothLocus : Set Z.subscheme) ↔
      ∃ w' : (Z.comap ι).subscheme,
        w' ∈ ((Z.comap ι).subschemeι ≫ ι ≫ g).smoothLocus ∧ (Z.comap ι).subschemeι w' = w := by
  constructor
  · rintro ⟨z, hz, hzw⟩
    have hr : z ∈ Set.range (subschemeRestrict Z ι) := by
      rw [range_subschemeRestrict]
      exact ⟨w, hzw.symm⟩
    obtain ⟨w', rfl⟩ := hr
    have hsq : Z.subschemeι (subschemeRestrict Z ι w') = ι ((Z.comap ι).subschemeι w') := by
      rw [← Scheme.Hom.comp_apply, subschemeRestrict_subschemeι, Scheme.Hom.comp_apply]
    refine ⟨w', (mem_smoothLocus_subschemeRestrict_iff Z ι g w').mp hz, ?_⟩
    exact ι.isOpenEmbedding.injective (hsq.symm.trans hzw)
  · rintro ⟨w', hw', rfl⟩
    refine ⟨subschemeRestrict Z ι w', (mem_smoothLocus_subschemeRestrict_iff Z ι g w').mpr hw',
      ?_⟩
    rw [← Scheme.Hom.comp_apply, subschemeRestrict_subschemeι, Scheme.Hom.comp_apply]

end SmoothLocusLocal

section Clopen

variable {k : Type u} [Field k] {B : Scheme.{u}}

-- `IsZariskiLocalAtSource.sigmaDesc` needs the instance `IsZariskiLocalAtSource @Smooth`, which the
-- transparency-respecting unifier does not find; the older behaviour is restored for this
-- declaration.
set_option backward.isDefEq.respectTransparency.types false in
/-- Clause (c1): a closed subscheme smooth over `k` on each of two complementary clopens
is smooth over `k` — smoothness is Zariski-local on the source (`IsZariskiLocalAtSource`, found
under the transparency setting Mathlib's `smoothLocus_eq_top_iff` uses), and the two restrictions
`subschemeRestrict Z U.ι`, `subschemeRestrict Z U'.ι` form an open cover of `V(Z)`
(`range_subschemeRestrict`). -/
theorem smooth_subschemeι_comp_of_isClopen (Z : B.IdealSheafData) (g : B ⟶ Spec (CommRingCat.of k))
    (U : B.Opens) (hU : IsClosed (U : Set B))
    (h₁ : Smooth ((Z.comap U.ι).subschemeι ≫ U.ι ≫ g))
    (h₀ : Smooth ((Z.comap
        (Scheme.Opens.ι (⟨(U : Set B)ᶜ, hU.isOpen_compl⟩ : B.Opens))).subschemeι ≫
      Scheme.Opens.ι (⟨(U : Set B)ᶜ, hU.isOpen_compl⟩ : B.Opens) ≫ g)) :
    Smooth (Z.subschemeι ≫ g) := by
  set U' : B.Opens := ⟨(U : Set B)ᶜ, hU.isOpen_compl⟩ with hU'
  let V : Bool → B.Opens := fun b => if b then U else U'
  have hcov : ∀ z : Z.subscheme, ∃ b y, subschemeRestrict Z (V b).ι y = z := by
    intro z
    by_cases hz : Z.subschemeι z ∈ (U : Set B)
    · have hr : z ∈ Set.range (subschemeRestrict Z (V true).ι) := by
        rw [range_subschemeRestrict, Scheme.Opens.range_ι]
        exact hz
      obtain ⟨y, hy⟩ := hr
      exact ⟨true, y, hy⟩
    · have hr : z ∈ Set.range (subschemeRestrict Z (V false).ι) := by
        rw [range_subschemeRestrict, Scheme.Opens.range_ι]
        exact hz
      obtain ⟨y, hy⟩ := hr
      exact ⟨false, y, hy⟩
  let 𝒰 : Z.subscheme.OpenCover :=
    Scheme.Cover.mkOfCovers Bool (fun b => (Z.comap (V b).ι).subscheme)
      (fun b => subschemeRestrict Z (V b).ι) hcov
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth.{u}) (f := Z.subschemeι ≫ g) 𝒰]
  intro b
  change Smooth (subschemeRestrict Z (V b).ι ≫ Z.subschemeι ≫ g)
  rw [← Category.assoc, subschemeRestrict_subschemeι, Category.assoc]
  cases b
  · exact h₀
  · exact h₁

end Clopen

section RegAgree

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]
  [NoetherianSpace X] (Y : X.IdealSheafData)

/-- Over `X₁` the smooth points of `Y` and of its core coincide: `x = ι w` for the open immersion
`ι : X₁ ↪ X`, both images are read on the restrictions to `X₁`
(`mem_image_smoothLocus_iff_of_isOpenImmersion`), and the two restricted ideals agree
(`stalkIdeal_coreIdeal_of_mem_componentsOutside`, stalkwise). -/
theorem mem_image_smoothLocus_coreIdeal_iff [IsReduced Y.subscheme] {x : X}
    (hx : x ∈ componentsOutside Y) :
    x ∈ (coreIdeal Y).subschemeι ''
        (((coreIdeal Y).subschemeι ≫ f).smoothLocus : Set (coreIdeal Y).subscheme) ↔
      x ∈ Y.subschemeι '' ((Y.subschemeι ≫ f).smoothLocus : Set Y.subscheme) := by
  set U : X.Opens := ⟨(componentsOutside Y : Set X), isOpen_componentsOutside f Y⟩ with hUdef
  have hc : (coreIdeal Y).comap U.ι = Y.comap U.ι := by
    refine IdealSheafData.ext_stalkIdeal fun w => ?_
    have h : (coreIdeal Y).stalkIdeal (U.ι w) = Y.stalkIdeal (U.ι w) :=
      stalkIdeal_coreIdeal_of_mem_componentsOutside f Y w.2
    rw [IdealSheafData.stalkIdeal_comap, IdealSheafData.stalkIdeal_comap, h]
  have hr : x ∈ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact hx
  obtain ⟨w, rfl⟩ := hr
  rw [mem_image_smoothLocus_iff_of_isOpenImmersion (coreIdeal Y) U.ι f,
    mem_image_smoothLocus_iff_of_isOpenImmersion Y U.ι f, hc]

end RegAgree

section Glue2

variable {B T : Scheme.{u}}

/-- A closed subscheme with zero ideal is the whole scheme: smooth over `T` when the scheme is. -/
theorem smooth_subschemeι_comp_of_eq_bot (Z : B.IdealSheafData) (hZ : Z = ⊥) (g : B ⟶ T)
    [Smooth g] : Smooth (Z.subschemeι ≫ g) := by
  subst hZ
  infer_instance

/-- Clause (c2): `Z` has snc with `E` when at every point its stalk is that of a `Z'` having snc
with `E`, or is zero at a point on no member of `E` (there a regular system of parameters of the
regular stalk of the smooth scheme, with no coordinate used, is an snc system). -/
theorem hasSncWith_of_forall_stalkIdeal {k : Type u} [Field k] (f : B ⟶ Spec (CommRingCat.of k))
    [Smooth f] (E : DivisorFamily B) {Z Z' : B.IdealSheafData} (hZ' : E.HasSncWith Z')
    (h : ∀ x : B, Z.stalkIdeal x = Z'.stalkIdeal x ∨
      (Z.stalkIdeal x = ⊥ ∧ ∀ j, x ∉ (E.component j).support)) :
    E.HasSncWith Z := by
  intro x hx
  rcases h x with hx' | ⟨hbot, hE⟩
  · have hx'' : x ∈ Z'.support := by
      rw [IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal, ← hx']
      exact (IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal Z x).mp hx
    obtain ⟨n, z, hz, s, hs⟩ := hZ' x hx''
    exact ⟨n, z, hz, s, hx'.trans hs⟩
  · have := isRegularLocalRing_stalk f x
    obtain ⟨d, z, hz₁, hz₂⟩ := exists_regularSystem (B.presheaf.stalk x)
    refine ⟨d, z, isSncAt_of_forall_notMem_support E x hE z ⟨hz₁.symm, hz₂⟩, ∅, ?_⟩
    rw [hbot, Finset.coe_empty, Set.image_empty, Ideal.span_empty]

end Glue2

section RunGlue

variable {k : Type u} [Field k] [CharZero k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k))] [Smooth (X ↘ Spec (CommRingCat.of k))]
  [NoetherianSpace X] (Y : X.IdealSheafData)

/-- Over any scheme mapping into a stage over `X₀` the strict transform of `Y` pulls back to zero
(stalkwise). -/
theorem comap_strictTransformSeq_eq_bot_of_forall_notMem_componentsOutside [IsReduced Y.subscheme]
    (i : Fin (((EDFunctor k).seq X Y).length + 1)) {W : Scheme.{u}}
    (ι : W ⟶ ((EDFunctor k).seq X Y).stage i)
    (hι : ∀ w, ((EDFunctor k).seq X Y).stageMap i (ι w) ∉ componentsOutside Y) :
    (((EDFunctor k).seq X Y).strictTransformSeq Y i).comap ι = ⊥ := by
  refine IdealSheafData.ext_stalkIdeal fun w => ?_
  rw [IdealSheafData.stalkIdeal_comap, IdealSheafData.stalkIdeal_bot,
    stalkIdeal_strictTransformSeq_eq_bot_of_stageMap_notMem_componentsOutside X Y i (ι w) (hι w),
    Ideal.map_bot]

/-- Over any scheme mapping into a stage over `X₁` the strict transforms of the core and of `Y` pull
back to the same ideal sheaf (stalkwise). -/
theorem comap_strictTransformSeq_coreIdeal_of_forall_mem_componentsOutside [IsReduced Y.subscheme]
    (i : Fin (((EDFunctor k).seq X Y).length + 1)) {W : Scheme.{u}}
    (ι : W ⟶ ((EDFunctor k).seq X Y).stage i)
    (hι : ∀ w, ((EDFunctor k).seq X Y).stageMap i (ι w) ∈ componentsOutside Y) :
    (((EDFunctor k).seq X Y).strictTransformSeq (coreIdeal Y) i).comap ι =
      (((EDFunctor k).seq X Y).strictTransformSeq Y i).comap ι := by
  refine IdealSheafData.ext_stalkIdeal fun w => ?_
  rw [IdealSheafData.stalkIdeal_comap, IdealSheafData.stalkIdeal_comap,
    stalkIdeal_strictTransformSeq_coreIdeal_of_stageMap_mem_componentsOutside X Y i (ι w) (hι w)]

/-- Over `X₁` the supports of the strict transforms of the core and of `Y` agree. -/
theorem mem_support_strictTransformSeq_coreIdeal_iff [IsReduced Y.subscheme]
    (i : Fin (((EDFunctor k).seq X Y).length + 1)) (x : ((EDFunctor k).seq X Y).stage i)
    (hx : ((EDFunctor k).seq X Y).stageMap i x ∈ componentsOutside Y) :
    x ∈ (((EDFunctor k).seq X Y).strictTransformSeq (coreIdeal Y) i).support ↔
      x ∈ (((EDFunctor k).seq X Y).strictTransformSeq Y i).support := by
  rw [IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal,
      IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal,
    stalkIdeal_strictTransformSeq_coreIdeal_of_stageMap_mem_componentsOutside X Y i x hx]

/-- Clause (e): the fine factorisation of the core's total pull-back gives that of `Y` with the same
snc divisor, stalkwise — over `X₁` the ideals agree, over `X₀` both sides are zero. -/
theorem comap_composite_eq_strictTransform_mul_of_coreIdeal [IsReduced Y.subscheme]
    (J : (((EDFunctor k).seq X Y).stage (Fin.last ((EDFunctor k).seq X Y).length)).IdealSheafData)
    (hJ : (coreIdeal Y).comap ((EDFunctor k).seq X Y).composite =
      ((EDFunctor k).seq X Y).strictTransformSeq (coreIdeal Y)
        (Fin.last ((EDFunctor k).seq X Y).length) * J) :
    Y.comap ((EDFunctor k).seq X Y).composite =
      ((EDFunctor k).seq X Y).strictTransformSeq Y
        (Fin.last ((EDFunctor k).seq X Y).length) * J := by
  have hJ' : (coreIdeal Y).comap (((EDFunctor k).seq X Y).stageMap
        (Fin.last ((EDFunctor k).seq X Y).length)) =
      ((EDFunctor k).seq X Y).strictTransformSeq (coreIdeal Y)
        (Fin.last ((EDFunctor k).seq X Y).length) * J := hJ
  have key : Y.comap (((EDFunctor k).seq X Y).stageMap (Fin.last ((EDFunctor k).seq X Y).length)) =
      ((EDFunctor k).seq X Y).strictTransformSeq Y
        (Fin.last ((EDFunctor k).seq X Y).length) * J := by
    refine IdealSheafData.ext_stalkIdeal fun x => ?_
    have hJx := congrArg (fun I => Scheme.IdealSheafData.stalkIdeal I x) hJ'
    rw [IdealSheafData.stalkIdeal_comap, IdealSheafData.stalkIdeal_mul] at hJx
    rw [IdealSheafData.stalkIdeal_comap, IdealSheafData.stalkIdeal_mul]
    by_cases hx : ((EDFunctor k).seq X Y).stageMap (Fin.last ((EDFunctor k).seq X Y).length) x ∈
        componentsOutside Y
    · rw [← stalkIdeal_coreIdeal_of_mem_componentsOutside (X ↘ Spec (CommRingCat.of k)) Y hx,
        ← stalkIdeal_strictTransformSeq_coreIdeal_of_stageMap_mem_componentsOutside X Y _ x hx]
      exact hJx
    · rw [stalkIdeal_eq_bot_of_notMem_componentsOutside (X ↘ Spec (CommRingCat.of k)) Y hx,
        Ideal.map_bot,
        stalkIdeal_strictTransformSeq_eq_bot_of_stageMap_notMem_componentsOutside X Y _ x hx,
        Ideal.bot_mul]
  exact key

/-- Clause (c1): the last strict transform of `Y` is smooth over `k` when that of the core is — over
the clopen part of the last stage over `X₁` they agree, over the part over `X₀` the strict transform
of `Y` is zero and the stage is smooth (`smooth_subschemeι_comp_of_isClopen`). -/
theorem smooth_strictTransformSeq_last_of_coreIdeal [IsReduced Y.subscheme]
    [Smooth (((EDFunctor k).seq X Y).stageMap (Fin.last ((EDFunctor k).seq X Y).length) ≫
      (X ↘ Spec (CommRingCat.of k)))]
    (hsm : Smooth ((((EDFunctor k).seq X Y).strictTransformSeq (coreIdeal Y)
        (Fin.last ((EDFunctor k).seq X Y).length)).subschemeι ≫
      ((EDFunctor k).seq X Y).stageMap (Fin.last ((EDFunctor k).seq X Y).length) ≫
        (X ↘ Spec (CommRingCat.of k)))) :
    Smooth ((((EDFunctor k).seq X Y).strictTransformSeq Y
        (Fin.last ((EDFunctor k).seq X Y).length)).subschemeι ≫
      ((EDFunctor k).seq X Y).composite ≫ (X ↘ Spec (CommRingCat.of k))) := by
  change Smooth ((((EDFunctor k).seq X Y).strictTransformSeq Y
        (Fin.last ((EDFunctor k).seq X Y).length)).subschemeι ≫
      ((EDFunctor k).seq X Y).stageMap (Fin.last ((EDFunctor k).seq X Y).length) ≫
        (X ↘ Spec (CommRingCat.of k)))
  let U : (((EDFunctor k).seq X Y).stage (Fin.last ((EDFunctor k).seq X Y).length)).Opens :=
    ((EDFunctor k).seq X Y).stageMap (Fin.last ((EDFunctor k).seq X Y).length) ⁻¹ᵁ
      outsideOpens k X Y
  have hUc : IsClosed (U : Set (((EDFunctor k).seq X Y).stage
      (Fin.last ((EDFunctor k).seq X Y).length))) :=
    (componentsOutside Y).isClosed.preimage
      (((EDFunctor k).seq X Y).stageMap (Fin.last ((EDFunctor k).seq X Y).length)).continuous
  refine smooth_subschemeι_comp_of_isClopen _ _ U hUc ?_ ?_
  · rw [← comap_strictTransformSeq_coreIdeal_of_forall_mem_componentsOutside X Y _ U.ι
      (fun w => w.2)]
    have := hsm
    exact smooth_comap_subschemeι_comp _ U.ι _
  · let U' : (((EDFunctor k).seq X Y).stage (Fin.last ((EDFunctor k).seq X Y).length)).Opens :=
      ⟨(U : Set _)ᶜ, hUc.isOpen_compl⟩
    change Smooth (((((EDFunctor k).seq X Y).strictTransformSeq Y
        (Fin.last ((EDFunctor k).seq X Y).length)).comap U'.ι).subschemeι ≫ U'.ι ≫
      ((EDFunctor k).seq X Y).stageMap (Fin.last ((EDFunctor k).seq X Y).length) ≫
        (X ↘ Spec (CommRingCat.of k)))
    rw [comap_strictTransformSeq_eq_bot_of_forall_notMem_componentsOutside X Y _ U'.ι
      (fun w => w.2)]
    exact smooth_subschemeι_comp_of_eq_bot _ rfl _

/-- Clause (c2): the last strict transform of `Y` has snc with the exceptional family when that of
the core does (`hasSncWith_of_forall_stalkIdeal`: over `X₁` the stalks agree, over `X₀` the stalk is
zero at a point on no exceptional member). -/
theorem hasSncWith_strictTransformSeq_last_of_coreIdeal [IsReduced Y.subscheme]
    [Smooth (((EDFunctor k).seq X Y).stageMap (Fin.last ((EDFunctor k).seq X Y).length) ≫
      (X ↘ Spec (CommRingCat.of k)))]
    (h : (((EDFunctor k).seq X Y).totalTransformSeq (DivisorFamily.empty X)
        (Fin.last ((EDFunctor k).seq X Y).length)).HasSncWith
      (((EDFunctor k).seq X Y).strictTransformSeq (coreIdeal Y)
        (Fin.last ((EDFunctor k).seq X Y).length))) :
    (((EDFunctor k).seq X Y).totalTransformSeq (DivisorFamily.empty X)
        (Fin.last ((EDFunctor k).seq X Y).length)).HasSncWith
      (((EDFunctor k).seq X Y).strictTransformSeq Y
        (Fin.last ((EDFunctor k).seq X Y).length)) := by
  refine hasSncWith_of_forall_stalkIdeal
    (((EDFunctor k).seq X Y).stageMap (Fin.last ((EDFunctor k).seq X Y).length) ≫
      (X ↘ Spec (CommRingCat.of k))) _ h fun x => ?_
  by_cases hx : ((EDFunctor k).seq X Y).stageMap (Fin.last _) x ∈ componentsOutside Y
  · exact Or.inl
      (stalkIdeal_strictTransformSeq_coreIdeal_of_stageMap_mem_componentsOutside X Y _ x hx).symm
  · exact Or.inr
      ⟨stalkIdeal_strictTransformSeq_eq_bot_of_stageMap_notMem_componentsOutside X Y _ x hx,
        fun j =>
          notMem_totalTransformSeq_component_support_of_stageMap_notMem_componentsOutside X Y _ j
            x hx⟩

/-- Clause (b): the Reg-window clause for `Y` from that of the core — a point of a centre lies over
`X₁`, where the strict transforms and the smooth points of `Y` and its core agree. -/
theorem stageMap_notMem_image_smoothLocus_of_coreIdeal [IsReduced Y.subscheme]
    (hcore : ∀ (i : Fin ((EDFunctor k).seq X Y).length)
      (x : ((EDFunctor k).seq X Y).stage i.castSucc),
      x ∈ (((EDFunctor k).seq X Y).center i).support →
        x ∈ (((EDFunctor k).seq X Y).strictTransformSeq (coreIdeal Y) i.castSucc).support →
          ((EDFunctor k).seq X Y).stageMap i.castSucc x ∉
            (coreIdeal Y).subschemeι ''
              (((coreIdeal Y).subschemeι ≫ (X ↘ Spec (CommRingCat.of k))).smoothLocus : Set _))
    (i : Fin ((EDFunctor k).seq X Y).length) (x : ((EDFunctor k).seq X Y).stage i.castSucc)
    (hx : x ∈ (((EDFunctor k).seq X Y).center i).support)
    (hxY : x ∈ (((EDFunctor k).seq X Y).strictTransformSeq Y i.castSucc).support) :
    ((EDFunctor k).seq X Y).stageMap i.castSucc x ∉
      Y.subschemeι '' ((Y.subschemeι ≫ (X ↘ Spec (CommRingCat.of k))).smoothLocus : Set _) := by
  intro hreg
  have hmem : ((EDFunctor k).seq X Y).stageMap i.castSucc x ∈ componentsOutside Y := by
    by_contra hn
    exact notMem_center_support_of_stageMap_notMem_componentsOutside X Y i x hn hx
  exact hcore i x hx ((mem_support_strictTransformSeq_coreIdeal_iff X Y i.castSucc x hmem).mpr hxY)
    ((mem_image_smoothLocus_coreIdeal_iff (X ↘ Spec (CommRingCat.of k)) Y hmem).mpr hreg)

end RunGlue

end Hironaka.Resolution
