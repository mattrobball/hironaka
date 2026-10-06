/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses
import Hironaka.Algebra.Local.Regular
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitMain
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Resolution.Algebraic.Wlo05.FirstCenterLocalIso
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Snc.DictionaryOrder
import Hironaka.Scheme.Snc.HasSncWith
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# At the absorbing stage: the centre is the strict transform, under Włodarczyk's Claim

In the proof of [Wlo05, Theorem 4.7.1], at the moment the strict transform `Ỹ₁` of a component is
the centre, the controlled transform of `I` has order `1` along `Ỹ₁` and is its ideal near `Ỹ₁` —
Włodarczyk's Claim. In Kollár's setting it is the proposition `ClaimKC`
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses`): at the first stage `n` whose centre `D`
contains the strict transform `c̃` of a member `c`, the nonmonomial part `N(I_n)` of the marked
ideal agrees with `c̃` at every point of `c̃`. **`ClaimKC` fails for the order of the steps of
`BMO_1` used here** (see that module); this module draws, CONDITIONALLY on it, the consequences the
loop would need. The unconditional replacements are proved from the local form of the ideal
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP2Entry`: the strict transform of an absorbed member
is smooth, integral, with simple normal crossings with the boundary, and disjoint from the other
members).

* `stalkIdeal_center_eq_of_absorbed` — at every point `p` of `c̃`, `D_p = c̃_p`: `D ≤ c̃` by the
  stop rule; conversely `I_n ≤ D` (the centre lies in the cosupport, [Kol07, Definition 66 (4′)]),
  `I_n = M(I_n) · N(I_n)` (the splitting of [Kol07, Definition–Lemma 110]) and `N(I_n)_p = c̃_p`
  (Włodarczyk's Claim), so `M(I_n)_p · c̃_p ≤ D_p` with `D_p` PRIME (the centre is smooth,
  `𝒪_p / D_p` a regular local ring, a domain); `M(I_n)_p ⊄ D_p` since a piece of the boundary
  containing `D` near `p` would contain the generic point of `c̃`, which lies on no member of the
  boundary.
* `hasSncWith_strictTransformSeq_of_absorbed`, `smooth_strictTransformSeq_of_absorbed` — `c̃` has
  simple normal crossings with the boundary at stage `n` and is smooth: [Kol07, Definition 24 (4)]
  is read at the points of `c̃`, where `c̃` has the stalks of the centre, which has snc with the
  boundary ([Kol07, Definition 66 (3′)]); smoothness by `HasSncWith.smooth`.
* `stalkIdeal_markedTransformSeq_eq_mul_of_absorbed` — `I_n = M(I_n) · I_c̃` at the points of `c̃`
  (Włodarczyk's `σ^c(I) = I_Ỹ₁` with the monomial part).

All statements are at the run's stage `n.castSucc` (the index form). The unconditional lemmas of
the first section (`val_le_firstCenterIndex_of_absorbed`,
`exists_genericPoint_strictTransformSeq_of_absorbed`, `markedTransformSeq_le_center_of_absorbed`)
are stated without the hypothesis `ClaimKC` and are used elsewhere.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.BMO

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

section Absorbed

/-! The data of an absorbed member: `T` a marked triple of mark `1`, `η` the generic point of a
component of `V(T.I)` lying on no member of the boundary at which `T.I` agrees with the component's
reduced ideal `c`, and `n` the FIRST centre index of the run whose centre contains the strict
transform of `c`. -/

variable (T : MarkedTriple k) (hm : T.m = 1) {η : T.X.left}
  (hη : η ∈ T.I.support.genericPoints) (hηE : ∀ i, η ∉ (T.E.component i).support)
  (hIc : T.I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η)
  (n : Fin (bmoOneRun T hm).length)
  (habs : CenterContains (bmoOneRun T hm) (IdealSheafData.vanishingIdeal (Closeds.closure {η})) n)
  (hfirst : ∀ m < n.val, ¬ CenterContains (bmoOneRun T hm) (IdealSheafData.vanishingIdeal
      (Closeds.closure {η})) m)

include hfirst in
/-- The stage `n` is at most the first containing index of the member. -/
theorem val_le_firstCenterIndex_of_absorbed :
    n.val ≤ firstCenterIndex (bmoOneRun T hm) (IdealSheafData.vanishingIdeal (Closeds.closure
        {η})) :=
  le_firstCenterIndex_of_forall_lt_not _ _ n.2.le hfirst

include hηE hfirst in
/-- The proof of [Kol07, Corollary 22] for the absorbed member: the strict transform `c̃` at stage
`n` has a generic point `η'`, the unique point over `η`, transported by isomorphisms of stalks and
lying on no member of the boundary at stage `n`. -/
theorem exists_genericPoint_strictTransformSeq_of_absorbed :
    ∃ η' : (bmoOneRun T hm).stage n.castSucc,
      IsGenericPoint η' (((bmoOneRun T hm).strictTransformSeq
        (IdealSheafData.vanishingIdeal (Closeds.closure {η})) n.castSucc).support : Set _) ∧
      (bmoOneRun T hm).stageMap n.castSucc η' = η ∧
      (∀ y, (bmoOneRun T hm).stageMap n.castSucc y = η → y = η') ∧
      (∀ (m : Fin (bmoOneRun T hm).length) (hmi : m.val < n.castSucc.val),
        (bmoOneRun T hm).stageMapBetween n.castSucc m.castSucc (Nat.le_of_lt hmi) η' ∉
          ((bmoOneRun T hm).center m).support) ∧
      IsIso (((bmoOneRun T hm).stageMap n.castSucc).stalkMap η') ∧
      ∀ i, η' ∉ (((bmoOneRun T hm).totalTransformSeq T.E n.castSucc).component i).support := by
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hint := isIntegral_subscheme_vanishingIdeal_closure η
  obtain ⟨η', hgen, hmap, huniq, havoid, hiso⟩ :=
    exists_isGenericPoint_strictTransformSeq_and_isIso_of_le_firstCenterIndex (bmoOneRun T hm)
      (IdealSheafData.vanishingIdeal (Closeds.closure {η}))
      (Hironaka.BMO.isGenericPoint_support_vanishingIdeal_closure η) n.castSucc
      (val_le_firstCenterIndex_of_absorbed T hm n hfirst)
  refine ⟨η', hgen, hmap, huniq, havoid, hiso, fun i => ?_⟩
  refine notMem_component_support_of_notMem_support _ ?_ i
  refine notMem_support_totalTransformSeq_of_forall_notMem (bmoOneRun T hm) T.E n.castSucc η'
    havoid ?_
  rw [hmap]
  intro hηs
  rw [← SetLike.mem_coe, DivisorFamily.coe_support_eq_iUnion] at hηs
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hηs
  exact hηE j hj


/-! ### The centre agrees with the strict transform at its points (K2a) -/

include hηE hfirst in
/-- The fine monomial part of the marked ideal at the absorbing stage is not contained in the
centre's stalk at a point of the absorbed strict transform: a piece of the boundary containing the
centre near `p` would, by generization to the generic point `η'` of the strict transform, contain
`η'` — which lies on no member of the boundary. -/
theorem not_monomialPart_stalkIdeal_le_center_of_absorbed
    {p : (bmoOneRun T hm).stage n.castSucc}
    (hp : p ∈ ((bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
        {η}))
      n.castSucc).support)
    (hprime : (((bmoOneRun T hm).center n).stalkIdeal p).IsPrime)
    (hDle : (bmoOneRun T hm).center n ≤
      (bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
          {η})) n.castSucc) :
    ¬ (monomialPart ((bmoOneRun T hm).markedTransformSeq T.I 1 n.castSucc)
        ((bmoOneRun T hm).totalTransformSeq T.E n.castSucc)).stalkIdeal p ≤
      ((bmoOneRun T hm).center n).stalkIdeal p := by
  intro hM
  have hrun := isOrderGeSeq_bmoOneRun T hm
  obtain ⟨η', hgen, -, -, -, -, hηE'⟩ :=
    exists_genericPoint_strictTransformSeq_of_absorbed T hm hηE n hfirst
  have hsp : η' ⤳ p := by
    rw [specializes_iff_mem_closure, hgen.def]
    exact hp
  have hNoeth : NoetherianSpace ((bmoOneRun T hm).stage n.castSucc) :=
    Hironaka.BD.noetherianSpace_triple (T.induced (bmoOneRun T hm) hrun n.castSucc).toTriple
  unfold monomialPart DivisorFamily.monomial at hM
  rw [IdealSheafData.stalkIdeal_finset_prod] at hM
  obtain ⟨i, -, hi⟩ := hprime.prod_le.mp hM
  rw [Hironaka.BMO.stalkIdeal_finprod_mem (Closeds.genericPoints_finite _),
    finprod_mem_eq_finite_toFinset_prod _ (Closeds.genericPoints_finite _)] at hi
  obtain ⟨ζ, hζ, hζle⟩ := hprime.prod_le.mp hi
  rw [Set.Finite.mem_toFinset] at hζ
  rw [IdealSheafData.stalkIdeal_pow] at hζle
  dsimp only at hζle
  have hDp : ((bmoOneRun T hm).center n).stalkIdeal p ≠ ⊤ := hprime.ne_top
  have hpos : (((bmoOneRun T hm).markedTransformSeq T.I 1 n.castSucc).ord ζ).toNat ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Ideal.one_eq_top] at hζle
    exact hDp (top_le_iff.mp hζle)
  have := hprime
  have hζle' : (IdealSheafData.vanishingIdeal (Closeds.closure {ζ})).stalkIdeal p ≤
      ((bmoOneRun T hm).center n).stalkIdeal p :=
    Ideal.IsPrime.le_of_pow_le hζle
  have hη'le : (IdealSheafData.vanishingIdeal (Closeds.closure {ζ})).stalkIdeal η' ≤
      ((bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η}))
        n.castSucc).stalkIdeal η' := by
    rw [IdealSheafData.stalkIdeal_specializes _ hsp, IdealSheafData.stalkIdeal_specializes _ hsp]
    exact Ideal.map_mono (hζle'.trans (IdealSheafData.stalkIdeal_mono hDle p))
  have hne : (IdealSheafData.vanishingIdeal (Closeds.closure {ζ})).stalkIdeal η' ≠ ⊤ := by
    intro htop
    have hc := (IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal _ η').mp hgen.mem
    rw [htop] at hη'le
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (hη'le.trans hc))
  have hmem : η' ∈ (IdealSheafData.vanishingIdeal (Closeds.closure {ζ})).support := by
    by_contra hnot
    exact hne (IdealSheafData.stalkIdeal_eq_top_of_notMem_support _ hnot)
  rw [support_vanishingIdeal_eq, ← SetLike.mem_coe, Closeds.coe_closure] at hmem
  exact hηE' i
    (((((bmoOneRun T hm).totalTransformSeq T.E n.castSucc).component i).support.isClosed
      |>.closure_subset_iff).mpr (Set.singleton_subset_iff.mpr hζ.1) hmem)

/-- [Kol07, Definition 66 (4′)]: the marked ideal at the absorbing stage is contained in the
centre's ideal — the centre lies in the cosupport (order `≥ 1` at its generic points), and the
centre is reduced (smooth). -/
theorem markedTransformSeq_le_center_of_absorbed :
    (bmoOneRun T hm).markedTransformSeq T.I 1 n.castSucc ≤ (bmoOneRun T hm).center n := by
  have hrun := isOrderGeSeq_bmoOneRun T hm
  obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
  have hsm : Smooth ((bmoOneRun T hm).stageMap n.castSucc ≫ (T.X.left ↘ Spec (.of k))) :=
    IsSmooth.smooth_stageMap (n := d) hrun.1 n.castSucc
  have hsnc := (hrun.2 n).1
  have hsupp : ((bmoOneRun T hm).center n).support ≤
      ((bmoOneRun T hm).markedTransformSeq T.I 1 n.castSucc).support := by
    intro x hx
    obtain ⟨ζ, hζ, hζx⟩ := Closeds.exists_mem_genericPoints_specializes _ hx
    have hord := (hrun.2 n).2 ζ hζ
    rw [hm, Nat.cast_one] at hord
    have hζI : ζ ∈ ((bmoOneRun T hm).markedTransformSeq T.I 1 n.castSucc).support :=
      (IdealSheafData.one_le_ord_iff _ ζ).mp hord
    exact ((((bmoOneRun T hm).markedTransformSeq T.I 1 n.castSucc).support.isClosed
      |>.closure_subset_iff).mpr (Set.singleton_subset_iff.mpr hζI))
        (specializes_iff_mem_closure.mp hζx)
  have hred : IsReduced ((bmoOneRun T hm).center n).subscheme :=
    isReduced_of_isRegular (HasSncWith.isRegular
      ((bmoOneRun T hm).stageMap n.castSucc ≫ (T.X.left ↘ Spec (.of k))) hsnc)
  have hD' : IdealSheafData.vanishingIdeal ((bmoOneRun T hm).center n).support =
      (bmoOneRun T hm).center n := by
    rw [IdealSheafData.vanishingIdeal_support, radical_eq_self_of_isReduced_subscheme]
  rw [← hD']
  exact IdealSheafData.le_support_iff_le_vanishingIdeal.mp hsupp

include hη hηE hIc habs hfirst in
/-- Under the hypothesis `ClaimKC` (Włodarczyk's Claim; false for the transcribed order): at every
point `p` of the absorbed strict transform `c̃`, the centre's stalk is `c̃`'s — `D ≤ c̃` by the
stop rule; conversely `I_n ≤ D`, `I_n = M(I_n) · N(I_n)` and `N(I_n)_p = c̃_p`
(Włodarczyk's Claim) give `M(I_n)_p · c̃_p ≤ D_p`, `D_p` is prime, and `M(I_n)_p ⊄ D_p`. -/
theorem stalkIdeal_center_eq_of_absorbed (hKC : ClaimKC k) {p : (bmoOneRun T hm).stage n.castSucc}
    (hp : p ∈ ((bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
        {η}))
      n.castSucc).support) :
    ((bmoOneRun T hm).center n).stalkIdeal p =
      ((bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η}))
        n.castSucc).stalkIdeal p := by
  have hrun := isOrderGeSeq_bmoOneRun T hm
  have hDle : (bmoOneRun T hm).center n ≤
      (bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
          {η})) n.castSucc :=
    habs.2
  refine le_antisymm (IdealSheafData.stalkIdeal_mono hDle p) ?_
  obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
  have hsm : Smooth ((bmoOneRun T hm).stageMap n.castSucc ≫ (T.X.left ↘ Spec (.of k))) :=
    IsSmooth.smooth_stageMap (n := d) hrun.1 n.castSucc
  have hpD : p ∈ ((bmoOneRun T hm).center n).support := IdealSheafData.support_antitone hDle hp
  have hsnc := (hrun.2 n).1
  have hprime : (((bmoOneRun T hm).center n).stalkIdeal p).IsPrime := by
    have hreg : IsRegularLocalRing (((bmoOneRun T hm).stage n.castSucc).presheaf.stalk p ⧸
        ((bmoOneRun T hm).center n).stalkIdeal p) :=
      HasSncWith.isRegularLocalRing_quotient_stalkIdeal
        ((bmoOneRun T hm).stageMap n.castSucc ≫ (T.X.left ↘ Spec (.of k))) hsnc hpD
    have := IsLocalRing.isDomain_of_isRegularLocalRing
      (((bmoOneRun T hm).stage n.castSucc).presheaf.stalk p ⧸
        ((bmoOneRun T hm).center n).stalkIdeal p)
    exact (Ideal.Quotient.isDomain_iff_prime _).mp this
  have hlN : IsLocallyNoetherian ((bmoOneRun T hm).stage n.castSucc) :=
    ((T.induced (bmoOneRun T hm) hrun n.castSucc).X.left ↘ Spec
      (.of k)).isLocallyNoetherian_of_field
  have hNoeth : NoetherianSpace ((bmoOneRun T hm).stage n.castSucc) :=
    Hironaka.BD.noetherianSpace_triple (T.induced (bmoOneRun T hm) hrun n.castSucc).toTriple
  have hE₀ : ((bmoOneRun T hm).totalTransformSeq T.E n.castSucc).IsSnc :=
    IsOrderGeSeq.isSnc_totalTransformSeq (T.X.left ↘ Spec (.of k)) d hrun T.isSnc n.castSucc
  have hsplit := Hironaka.BMO.Snc.monomialPart_mul_nonmonomialPart
    ((bmoOneRun T hm).stageMap n.castSucc ≫ (T.X.left ↘ Spec (.of k)))
    ((bmoOneRun T hm).totalTransformSeq T.E n.castSucc) hE₀
    ((bmoOneRun T hm).markedTransformSeq T.I 1 n.castSucc)
  have hKCp := hKC T hm η hη hηE hIc n habs hfirst p hp
  have hle : (monomialPart ((bmoOneRun T hm).markedTransformSeq T.I 1 n.castSucc)
      ((bmoOneRun T hm).totalTransformSeq T.E n.castSucc)).stalkIdeal p *
      ((bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η}))
        n.castSucc).stalkIdeal p ≤ ((bmoOneRun T hm).center n).stalkIdeal p := by
    rw [← hKCp, ← IdealSheafData.stalkIdeal_mul, hsplit]
    exact IdealSheafData.stalkIdeal_mono (markedTransformSeq_le_center_of_absorbed T hm n) p
  rcases hprime.mul_le.mp hle with hM | hc
  · exact absurd hM
      (not_monomialPart_stalkIdeal_le_center_of_absorbed T hm hηE n hfirst hp hprime hDle)
  · exact hc

/-! ### K2, K1, K3 -/

include hη hηE hIc habs hfirst in
/-- Under the hypothesis `ClaimKC`: the absorbed strict transform has simple normal crossings with
the boundary at stage `n` — [Kol07, Definition 24 (4)] read at its points, where its stalks are the
centre's (`stalkIdeal_center_eq_of_absorbed`) and the centre has snc with the boundary
([Kol07, Definition 66 (3′)]). The unconditional form is in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP2Entry`. -/
theorem hasSncWith_strictTransformSeq_of_absorbed (hKC : ClaimKC k) :
    ((bmoOneRun T hm).totalTransformSeq T.E n.castSucc).HasSncWith
      ((bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
          {η})) n.castSucc) := by
  have hrun := isOrderGeSeq_bmoOneRun T hm
  have hDle : (bmoOneRun T hm).center n ≤
      (bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
          {η})) n.castSucc :=
    habs.2
  intro p hp
  obtain ⟨m, z, hsncAt, s, hDs⟩ := (hrun.2 n).1 p (IdealSheafData.support_antitone hDle hp)
  refine ⟨m, z, hsncAt, s, ?_⟩
  rw [← stalkIdeal_center_eq_of_absorbed T hm hη hηE hIc n habs hfirst hKC hp]
  exact hDs

include hη hηE hIc habs hfirst in
/-- Under the hypothesis `ClaimKC`: the absorbed strict transform is smooth over `k`
(`HasSncWith.smooth`). The unconditional form is in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP2Entry`. -/
theorem smooth_strictTransformSeq_of_absorbed (hKC : ClaimKC k) :
    Smooth (((bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
        {η}))
      n.castSucc).subschemeι ≫ (bmoOneRun T hm).stageMap n.castSucc ≫
        (T.X.left ↘ Spec (.of k))) := by
  have hrun := isOrderGeSeq_bmoOneRun T hm
  obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
  have hsm : Smooth ((bmoOneRun T hm).stageMap n.castSucc ≫ (T.X.left ↘ Spec (.of k))) :=
    IsSmooth.smooth_stageMap (n := d) hrun.1 n.castSucc
  have : PerfectField k := PerfectField.ofCharZero
  exact HasSncWith.smooth ((bmoOneRun T hm).stageMap n.castSucc ≫ (T.X.left ↘ Spec (.of k)))
    (hasSncWith_strictTransformSeq_of_absorbed T hm hη hηE hIc n habs hfirst hKC)

include hη hηE hIc habs hfirst in
/-- Under the hypothesis `ClaimKC`: at every point of the absorbed strict transform, the marked
ideal is the monomial part times the strict transform's ideal (Włodarczyk's Claim with the monomial
part of [Kol07, Definition–Lemma 110]). -/
theorem stalkIdeal_markedTransformSeq_eq_mul_of_absorbed (hKC : ClaimKC k)
    {p : (bmoOneRun T hm).stage n.castSucc}
    (hp : p ∈ ((bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
        {η}))
      n.castSucc).support) :
    ((bmoOneRun T hm).markedTransformSeq T.I 1 n.castSucc).stalkIdeal p =
      (monomialPart ((bmoOneRun T hm).markedTransformSeq T.I 1 n.castSucc)
        ((bmoOneRun T hm).totalTransformSeq T.E n.castSucc)).stalkIdeal p *
      ((bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η}))
        n.castSucc).stalkIdeal p := by
  have hrun := isOrderGeSeq_bmoOneRun T hm
  obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
  have hlN : IsLocallyNoetherian ((bmoOneRun T hm).stage n.castSucc) :=
    ((T.induced (bmoOneRun T hm) hrun n.castSucc).X.left ↘ Spec
      (.of k)).isLocallyNoetherian_of_field
  have hNoeth : NoetherianSpace ((bmoOneRun T hm).stage n.castSucc) :=
    Hironaka.BD.noetherianSpace_triple (T.induced (bmoOneRun T hm) hrun n.castSucc).toTriple
  have hsm : Smooth ((bmoOneRun T hm).stageMap n.castSucc ≫ (T.X.left ↘ Spec (.of k))) :=
    IsSmooth.smooth_stageMap (n := d) hrun.1 n.castSucc
  have hE₀ : ((bmoOneRun T hm).totalTransformSeq T.E n.castSucc).IsSnc :=
    IsOrderGeSeq.isSnc_totalTransformSeq (T.X.left ↘ Spec (.of k)) d hrun T.isSnc n.castSucc
  have hsplit := Hironaka.BMO.Snc.monomialPart_mul_nonmonomialPart
    ((bmoOneRun T hm).stageMap n.castSucc ≫ (T.X.left ↘ Spec (.of k)))
    ((bmoOneRun T hm).totalTransformSeq T.E n.castSucc) hE₀
    ((bmoOneRun T hm).markedTransformSeq T.I 1 n.castSucc)
  rw [← hKC T hm η hη hηE hIc n habs hfirst p hp, ← IdealSheafData.stalkIdeal_mul, hsplit]

end Absorbed

end Hironaka.Resolution
