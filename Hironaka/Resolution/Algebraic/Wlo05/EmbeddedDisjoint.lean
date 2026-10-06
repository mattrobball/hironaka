/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenter
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedAbsorbed
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Resolution.Algebraic.Wlo05.FirstCenterLocalIso
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.FlatColon
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The absorbed strict transform meets no other member, under Włodarczyk's Claim

Włodarczyk's [Wlo05, Theorem 4.7.1] asserts that the strict transforms `Ỹᵢ` of the components are
"smooth and disjoint". With Włodarczyk's Claim (the proposition `ClaimKC` of
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses`, false for the order of the steps of
`BMO_1` used here), the disjointness would follow: the nonmonomial part `N(I_n)` agrees with the
absorbed strict transform `c̃` at the points of `c̃`; another member's strict transform `c̃'` lies
in the support of `N(I_n)` (its generic point carries the proper stalk of the marked ideal and lies
off the boundary, where `M(I_n)` is trivial), so at a common point `p`, `c̃_p = N(I_n)_p ≤ c̃'_p`;
generizing to the generic point of `c̃'` puts it on `c̃`, hence the generic points of the two
members are related by specialization on `X` — and two generic points of `supp I` so related
coincide. This gives at once the disjointness of the strict transforms absorbed at the same stage
and the fact that a remaining member misses the absorbed ones. This module proves the statement
CONDITIONALLY on `ClaimKC`; the unconditional disjointness is part of the statement CP1
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Absorbed`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP2Entry`). The unconditional first lemma,
`stalkIdeal_monomialPart_eq_top_of_forall_notMem` (the monomial part of [Kol07, Definition–Lemma
110] is trivial off the boundary), is used elsewhere.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka BlowUpSequence
  Scheme.IdealSheafData Hironaka.BMO

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-- Off the boundary the fine monomial part has the unit stalk: every factor is the reduced ideal of
a component of a member, whose stalk at a point off that member is the unit ideal. -/
theorem stalkIdeal_monomialPart_eq_top_of_forall_notMem {X : Scheme.{u}} [NoetherianSpace X]
    (I : X.IdealSheafData) (E : DivisorFamily X) {x : X}
    (hx : ∀ i, x ∉ (E.component i).support) : (monomialPart I E).stalkIdeal x = ⊤ := by
  unfold monomialPart DivisorFamily.monomial
  rw [IdealSheafData.stalkIdeal_finset_prod, ← Ideal.one_eq_top]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Hironaka.BMO.stalkIdeal_finprod_mem (Closeds.genericPoints_finite _),
    finprod_mem_eq_finite_toFinset_prod _ (Closeds.genericPoints_finite _)]
  refine Finset.prod_eq_one fun ζ hζ => ?_
  rw [Set.Finite.mem_toFinset] at hζ
  rw [IdealSheafData.stalkIdeal_pow,
      Hironaka.BMO.stalkIdeal_vanishingIdeal_closure_eq_top_of_not_specializes,
    Ideal.top_pow, Ideal.one_eq_top]
  intro hsp
  exact hx i ((E.component i).support.isClosed.closure_subset_iff.mpr
    (Set.singleton_subset_iff.mpr hζ.1) (specializes_iff_mem_closure.mp hsp))

section Disjoint

variable (T : MarkedTriple k) (hm : T.m = 1) {η η' : T.X.left}
  (hη : η ∈ T.I.support.genericPoints) (hηE : ∀ i, η ∉ (T.E.component i).support)
  (hIc : T.I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η)
  (hη' : η' ∈ T.I.support.genericPoints) (hηE' : ∀ i, η' ∉ (T.E.component i).support)
  (hIc' : T.I.stalkIdeal η' = (IdealSheafData.vanishingIdeal (Closeds.closure {η'})).stalkIdeal η')
  (n : Fin (bmoOneRun T hm).length)
  (habs : CenterContains (bmoOneRun T hm) (IdealSheafData.vanishingIdeal (Closeds.closure {η})) n)
  (hfirst : ∀ m < n.val, ¬ CenterContains (bmoOneRun T hm) (IdealSheafData.vanishingIdeal
      (Closeds.closure {η})) m)
  (hfirst' : ∀ m < n.val,
    ¬ CenterContains (bmoOneRun T hm) (IdealSheafData.vanishingIdeal (Closeds.closure {η'})) m)

include hη hηE hIc hη' hηE' hIc' habs hfirst hfirst' in
/-- Under the hypothesis `ClaimKC` (Włodarczyk's Claim; false for the transcribed order): a member
absorbed at stage `n` and any member not absorbed before `n` have strict transforms meeting at a
point only if they are the same member — their generic points coincide
([Wlo05, Theorem 4.7.1]: the strict transforms are disjoint). -/
theorem eq_of_mem_strictTransformSeq_support_of_absorbed (hKC : ClaimKC k)
    {p : (bmoOneRun T hm).stage n.castSucc}
    (hp : p ∈ ((bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
        {η}))
      n.castSucc).support)
    (hp' : p ∈ ((bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
        {η'}))
      n.castSucc).support) : η = η' := by
  have hrun := isOrderGeSeq_bmoOneRun T hm
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hlN : IsLocallyNoetherian ((bmoOneRun T hm).stage n.castSucc) :=
    ((T.induced (bmoOneRun T hm) hrun n.castSucc).X.left ↘ Spec
      (.of k)).isLocallyNoetherian_of_field
  have hNoeth : NoetherianSpace ((bmoOneRun T hm).stage n.castSucc) :=
    Hironaka.BD.noetherianSpace_triple (T.induced (bmoOneRun T hm) hrun n.castSucc).toTriple
  have hint' := isIntegral_subscheme_vanishingIdeal_closure η'
  -- the generic points of the two strict transforms
  obtain ⟨ξ, hgen, hmap, -, -, -, -⟩ :=
    exists_genericPoint_strictTransformSeq_of_absorbed T hm hηE n hfirst
  obtain ⟨ξ', hgen', hmap', huniq', havoid', -, hξE'⟩ :=
    exists_genericPoint_strictTransformSeq_of_absorbed T hm hηE' n hfirst'
  -- the strict transform of `c'` lies in the support of `N(I_n)`
  have hξ'N : ξ' ∈ (nonmonomialPart ((bmoOneRun T hm).markedTransformSeq T.I 1 n.castSucc)
      ((bmoOneRun T hm).totalTransformSeq T.E n.castSucc)).support := by
    have hmem := (mem_genericPoints_markedTransformSeq_support_of_forall_notMem (bmoOneRun T hm)
      T.I _ 1 (Hironaka.BMO.isGenericPoint_support_vanishingIdeal_closure η') hη' hIc' n.castSucc
      hmap' huniq' havoid').1
    rw [IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal] at hmem ⊢
    rw [nonmonomialPart_eq_colon, IdealSheafData.stalkIdeal_colon_of_isLocallyNoetherian,
      stalkIdeal_monomialPart_eq_top_of_forall_notMem _ _ hξE', Submodule.top_coe,
      Submodule.colon_univ]
    exact hmem
  have hNle : nonmonomialPart ((bmoOneRun T hm).markedTransformSeq T.I 1 n.castSucc)
      ((bmoOneRun T hm).totalTransformSeq T.E n.castSucc) ≤
      (bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
          {η'})) n.castSucc := by
    have hred : IsReduced ((bmoOneRun T hm).strictTransformSeq
        (IdealSheafData.vanishingIdeal (Closeds.closure {η'})) n.castSucc).subscheme :=
      have := isIntegral_strictTransformSeq_of_le_firstCenterIndex (bmoOneRun T hm) _ n.castSucc
        (val_le_firstCenterIndex_of_absorbed T hm n hfirst')
      inferInstance
    have hV : IdealSheafData.vanishingIdeal ((bmoOneRun T hm).strictTransformSeq
        (IdealSheafData.vanishingIdeal (Closeds.closure {η'})) n.castSucc).support =
        (bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
            {η'})) n.castSucc := by
      rw [IdealSheafData.vanishingIdeal_support, radical_eq_self_of_isReduced_subscheme]
    rw [← hV]
    refine IdealSheafData.le_support_iff_le_vanishingIdeal.mp ?_
    intro q hq
    have hq' : q ∈ closure {ξ'} := by rw [hgen'.def]; exact hq
    exact (nonmonomialPart _ _).support.isClosed.closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hξ'N) hq'
  -- at `p`: `c̃_p = N_p ≤ c̃'_p`, then generize to `ξ'`
  have hKCp := hKC T hm η hη hηE hIc n habs hfirst p hp
  have hle : ((bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
      {η}))
      n.castSucc).stalkIdeal p ≤
      ((bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η'}))
        n.castSucc).stalkIdeal p := by
    rw [← hKCp]
    exact IdealSheafData.stalkIdeal_mono hNle p
  have hsp' : ξ' ⤳ p := by
    rw [specializes_iff_mem_closure, hgen'.def]
    exact hp'
  have hle' : ((bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
      {η}))
      n.castSucc).stalkIdeal ξ' ≤
      ((bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η'}))
        n.castSucc).stalkIdeal ξ' := by
    rw [IdealSheafData.stalkIdeal_specializes _ hsp', IdealSheafData.stalkIdeal_specializes _ hsp']
    exact Ideal.map_mono hle
  have hξ'c : ξ' ∈ ((bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal
      (Closeds.closure {η}))
      n.castSucc).support := by
    rw [IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal]
    exact hle'.trans ((IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal _ ξ').mp hgen'.mem)
  have hspec : ξ ⤳ ξ' := by
    rw [specializes_iff_mem_closure, hgen.def]
    exact hξ'c
  have hspecX : η ⤳ η' := by
    rw [← hmap, ← hmap']
    exact hspec.map ((bmoOneRun T hm).stageMap n.castSucc).continuous
  exact hη'.2 hη.1 hspecX

end Disjoint

end Hironaka.Resolution
