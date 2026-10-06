/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
import Hironaka.Resolution.Algebraic.Balanced.GoingUpChain
import Hironaka.Resolution.Algebraic.Kol07.Thm36.IndexTransport
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRegWindow
import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.Restrict
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Elementary tools for the descent step of CP1

The descent of the chain form along the pushforward of a run on a smooth hypersurface `H ↪ X`
(the induction step of the statement CP1 of the embedded desingularization,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainPushforward`) rests on four elementary facts, each
about closed immersions or supports and none about the chain form itself:

* along a closed immersion `g`, the reduced ideal of the closure of an image point pulls back to
  the reduced ideal of the closure of the point
  (`comap_vanishingIdeal_closure_of_isClosedImmersion`),
  and the member data of `cp1For_concat` (a generic point of `V(J)` off the boundary at which `J` is
  the component's ideal) descend to the restriction `J|_Y` when `V(J) ⊆ g(Y)`
  (`exists_level_data_comap`);
* the strict transform along the pushforward of a run pulls back, along the stage embedding, to
  the strict transform of the restriction (`strictTransformSeq_pushforward_comap`), and a centre of
  the pushforward contains the strict transform of `c ⊇ H` iff the corresponding centre contains
  that of `c|_H` (`centerContains_pushforward_iff_of_ker_le`) — the transport of
  `Hironaka.Resolution.Algebraic.Kol07.Thm36.IndexTransport` (`strictTransformSeq_pushforward`,
  `centerContains_pushforward_iff`) with `c = (c|_H)` extended by zero (`map_comap_of_ker_le`);
* the chain form ignores members missing the point: for a sub-family selecting every member
  through `p` the two chain forms agree (`chainRelativeAt_subfamily_iff`); and a divisor disjoint
  from `V(J)` keeps its strict transforms disjoint from the supports of the marked transforms of
  `(J, 1)` along any blow-up sequence, both lying over the originals
  (`disjoint_support_markedTransformSeq_strictTransformSeq`).

The pushforward of a blow-up sequence along a closed immersion is that of [Kol07, Definition 30]
(30.2–30.3); the marked transform is that of [Kol07, Definition 60].
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData
  BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.Resolution

variable {X Y : Scheme.{u}}

/-! ### S2c (ii): supports lie over the originals -/

/-- S2c (ii) in the `⟨j, hj⟩` form of the indices: along any blow-up sequence the support of the
marked transform of `(J, 1)` lies over `V(J)` (the marked transform contains the pull-back) and the
support of the strict transform of `D` lies over `V(D)` (`coe_support_strictTransform`), so
disjointness of `V(J)` and `V(D)` propagates to every stage. -/
theorem disjoint_support_markedTransformSeq_strictTransformSeq_mk (hN : IsLocallyNoetherian X)
    (S : BlowUpSequence X) (J D : X.IdealSheafData)
    (hD : Disjoint (J.support : Set X) (D.support : Set X)) (j : ℕ) (hj : j < S.length + 1) :
    Disjoint ((S.markedTransformSeq J 1 ⟨j, hj⟩).support : Set (S.stage ⟨j, hj⟩))
      ((S.strictTransformSeq D ⟨j, hj⟩).support : Set (S.stage ⟨j, hj⟩)) := by
  induction S generalizing j with
  | nil X => exact hD
  | cons X Z rest ih =>
    cases j with
    | zero => exact hD
    | succ j =>
      have hN' : IsLocallyNoetherian Z.blowUp := blowUp.isLocallyNoetherian Z
      refine ih hN' (J.markedTransform Z 1) (D.strictTransform Z) ?_ j (Nat.lt_of_succ_lt_succ hj)
      have h1 : ((J.markedTransform Z 1).support : Set Z.blowUp) ⊆
          Z.blowUpπ ⁻¹' (J.support : Set X) := fun x hx =>
        (mem_support_comap_iff_apply J Z.blowUpπ x).mp
          (support_antitone (Scheme.IdealSheafData.le_colon_self _ _) hx)
      have h2 : ((D.strictTransform Z).support : Set Z.blowUp) ⊆
          Z.blowUpπ ⁻¹' (D.support : Set X) := by
        rw [coe_support_strictTransform]
        exact (closure_mono Set.sdiff_subset).trans
          (D.support.isClosed.preimage Z.blowUpπ.continuous).closure_subset
      exact Set.disjoint_of_subset h1 h2 (hD.preimage _)

/-- A divisor disjoint from `V(J)` stays disjoint from the support of the marked transform of
`(J, 1)` along any blow-up sequence, at every stage. -/
theorem disjoint_support_markedTransformSeq_strictTransformSeq [IsLocallyNoetherian X]
    (S : BlowUpSequence X) (J D : X.IdealSheafData)
    (hD : Disjoint (J.support : Set X) (D.support : Set X)) (i : Fin (S.length + 1)) :
    Disjoint ((S.markedTransformSeq J 1 i).support : Set (S.stage i))
      ((S.strictTransformSeq D i).support : Set (S.stage i)) := by
  obtain ⟨j, hj⟩ := i
  exact disjoint_support_markedTransformSeq_strictTransformSeq_mk inferInstance S J D hD j hj

/-! ### S2b: the pushforward's strict transforms and centres -/

/-- For `c ⊇ ker g`, the strict transform of `c` along the pushforward pulls back along the stage
embedding to the strict transform of `c|_Y` (`strictTransformSeq_pushforward`). -/
theorem strictTransformSeq_pushforward_comap (L : BlowUpSequence Y) (g : Y ⟶ X)
    [IsClosedImmersion g] {c : X.IdealSheafData} (hc : g.ker ≤ c) (i : Fin (L.length + 1)) :
    ((L.pushforward g).strictTransformSeq c (L.pushforwardStageIdx g i)).comap
        (L.pushforwardStageHom g i) =
      L.strictTransformSeq (c.comap g) i := by
  have := isClosedImmersion_pushforwardStageHom L g i
  conv_lhs => rw [← map_comap_of_ker_le g c hc]
  rw [strictTransformSeq_pushforward L g (c.comap g) i,
    comap_map_of_isClosedImmersion]

/-- For `c ⊇ ker g`, a centre of the pushforward contains the strict transform of `c` iff the
corresponding centre of `L` contains the strict transform of `c|_Y`
(`centerContains_pushforward_iff`). -/
theorem centerContains_pushforward_iff_of_ker_le (L : BlowUpSequence Y) (g : Y ⟶ X)
    [IsClosedImmersion g] {c : X.IdealSheafData} (hc : g.ker ≤ c) (l : ℕ) :
    CenterContains (L.pushforward g) c l ↔ CenterContains L (c.comap g) l := by
  have h := centerContains_pushforward_iff L g (c.comap g) l
  rwa [map_comap_of_ker_le g c hc] at h

/-! ### S2a: the member data descend along a closed immersion -/

/-- Along a closed immersion `g` the reduced ideal of the closure of `g η'` pulls back to the
reduced ideal of the closure of `η'` — the pullback is reduced (its subscheme is isomorphic to
`V(closure {g η'})`, which lies in the image, `exists_iso_subscheme_comap_of_ker_le`) with support
the preimage of the closure, which is the closure of `η'` for a closed embedding. -/
theorem comap_vanishingIdeal_closure_of_isClosedImmersion (g : Y ⟶ X) [IsClosedImmersion g]
    (η' : Y) :
    (vanishingIdeal (Closeds.closure {g η'})).comap g = vanishingIdeal (Closeds.closure {η'}) := by
  have hker : g.ker ≤ vanishingIdeal (Closeds.closure {g η'}) := by
    rw [← le_support_iff_le_vanishingIdeal]
    intro x hx
    rw [← SetLike.mem_coe, Closeds.coe_closure] at hx
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker]
    exact closure_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self η')) hx
  obtain ⟨φ, -⟩ := exists_iso_subscheme_comap_of_ker_le g _ hker
  have hred : IsReduced ((vanishingIdeal (Closeds.closure {g η'})).comap g).subscheme := by
    have := isReduced_subscheme_vanishingIdeal (Closeds.closure {g η'})
    exact isReduced_of_isOpenImmersion φ.hom
  have hs : (vanishingIdeal (Closeds.closure {g η'})).support = Closeds.closure {g η'} :=
    Closeds.ext (by rw [coe_support_vanishingIdeal])
  rw [← vanishingIdeal_support_of_isReduced ((vanishingIdeal (Closeds.closure {g η'})).comap g),
    support_comap, hs]
  congr 1
  apply Closeds.ext
  rw [Closeds.coe_preimage, Closeds.coe_closure, Closeds.coe_closure,
    (Scheme.Hom.isClosedEmbedding g).toIsEmbedding.closure_eq_preimage_closure_image,
    Set.image_singleton]

/-- The member data of `cp1For_concat` — a generic point `η` of `V(J)` off every member of `E` at
which `J` is the ideal of the component — descend along a closed immersion `g` with `ker g ⊆ J`:
`η = g η'` for a generic point `η'` of `V(J|_Y)` off every member of `E|_Y`, at which `J|_Y` is the
ideal of the component. -/
theorem exists_level_data_comap (g : Y ⟶ X) [IsClosedImmersion g] {J : X.IdealSheafData}
    (hJ : g.ker ≤ J) (E : DivisorFamily X) {η : X} (hη : η ∈ J.support.genericPoints)
    (hηE : ∀ j, η ∉ (E.component j).support)
    (hIc : J.stalkIdeal η = (vanishingIdeal (Closeds.closure {η})).stalkIdeal η) :
    ∃ η' : Y, g η' = η ∧ η' ∈ (J.comap g).support.genericPoints ∧
      (∀ j, η' ∉ ((E.comap g).component j).support) ∧
      (J.comap g).stalkIdeal η' = (vanishingIdeal (Closeds.closure {η'})).stalkIdeal η' := by
  have hJ' : J = (J.comap g).map g := (map_comap_of_ker_le g J hJ).symm
  have hη' : η ∈ ((J.comap g).map g).support.genericPoints := by rwa [← hJ']
  obtain ⟨η', hη'gen, rfl⟩ := (mem_genericPoints_support_map_iff g (J.comap g) η).mp hη'
  refine ⟨η', rfl, hη'gen,
    fun j hj => hηE j ((mem_support_comap_iff_apply _ _ _).mp hj), ?_⟩
  rw [stalkIdeal_comap, hIc, ← stalkIdeal_comap, comap_vanishingIdeal_closure_of_isClosedImmersion]

/-! ### S2c (i): the chain form ignores members missing the point -/

/-- For a sub-family of `E` selecting every member through `p`, the chain form along `Γ` at `p` for
the sub-family and for `E` agree — the members through `p` correspond (the coordinates `c` are
re-indexed along the correspondence; stalks are unchanged). -/
theorem chainRelativeAt_subfamily_iff {E : DivisorFamily X} (q : E.ι → Prop)
    {I Γ : X.IdealSheafData} {p : X} (hq : ∀ j, p ∈ (E.component j).support → q j) :
    ChainRelativeAt (E.subfamily q) I Γ p ↔ ChainRelativeAt E I Γ p := by
  -- the members through `p` of the two families correspond
  let θ : {j : E.ι // p ∈ (E.component j).support} →
      {j : (E.subfamily q).ι // p ∈ ((E.subfamily q).component j).support} :=
    fun j => ⟨⟨j.1, hq j.1 j.2⟩, j.2⟩
  let θ' : {j : (E.subfamily q).ι // p ∈ ((E.subfamily q).component j).support} →
      {j : E.ι // p ∈ (E.component j).support} :=
    fun j => ⟨j.1.1, j.2⟩
  have hθθ' : ∀ j, θ (θ' j) = j := fun j => Subtype.ext (Subtype.ext rfl)
  have hθ'θ : ∀ j, θ' (θ j) = j := fun j => Subtype.ext rfl
  have hθinj : Function.Injective θ := fun j j' h => by
    rw [← hθ'θ j, ← hθ'θ j', h]
  have hθ'inj : Function.Injective θ' := fun j j' h => by
    rw [← hθθ' j, ← hθθ' j', h]
  constructor
  · rintro ⟨n, z, c, r, σ, a, b, ⟨hz, hcinj, hcmem, hσinj, hσc, ha, hΓ⟩, hb, hI⟩
    refine ⟨n, z, c ∘ θ, r, σ, a, b, ⟨hz, hcinj.comp hθinj, fun j => hcmem (θ j), hσinj,
      fun i j => hσc i (θ j), fun i k hk => ?_, hΓ⟩, fun k hk => ?_, hI⟩
    · obtain ⟨j, hj⟩ := ha i k hk
      exact ⟨θ' j, by rw [Function.comp_apply, hθθ', hj]⟩
    · obtain ⟨j, hj⟩ := hb k hk
      exact ⟨θ' j, by rw [Function.comp_apply, hθθ', hj]⟩
  · rintro ⟨n, z, c, r, σ, a, b, ⟨hz, hcinj, hcmem, hσinj, hσc, ha, hΓ⟩, hb, hI⟩
    refine ⟨n, z, c ∘ θ', r, σ, a, b, ⟨hz, hcinj.comp hθ'inj, fun j => hcmem (θ' j), hσinj,
      fun i j => hσc i (θ' j), fun i k hk => ?_, hΓ⟩, fun k hk => ?_, hI⟩
    · obtain ⟨j, hj⟩ := ha i k hk
      exact ⟨θ j, by rw [Function.comp_apply, hθ'θ, hj]⟩
    · obtain ⟨j, hj⟩ := hb k hk
      exact ⟨θ j, by rw [Function.comp_apply, hθ'θ, hj]⟩

end Hironaka.Resolution
