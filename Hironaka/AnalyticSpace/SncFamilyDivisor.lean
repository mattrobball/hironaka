/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.SncFamily
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.AnalyticSpace.HomExt
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The divisor of a simple normal crossings family: support and boundary predicate

For `ClosedSubspace.divisorOf` and `ClosedSubspace.IsSncFamily` of
`Hironaka/AnalyticSpace/SncFamily.lean`:

* `support_divisorOf`: the support of the divisor of a locally finite family is the union of the
  members' supports;
* `isSncBoundary_divisorOf`: the divisor of an snc family is an snc boundary
  (`ClosedSubspace.IsSncBoundary`), Kollár's
  `E = Σ Eᵢ` with simple normal crossings [Kol07, Definition 24] (the boundary of
  [Kol07, Theorem 45 (3)] and [Wlo09, Theorem 2.0.1 (2)]);
* `isSncBoundary_iff_exists_isSncFamily_divisorOf`: conversely every snc boundary is the divisor
  of an snc family, so `IsSncBoundary` is exactly "the divisor of an snc family";
* `isSncBoundary_top_iff_isNonsingular`: the boundary case — the empty divisor `⊤` is an snc
  boundary iff `X` is non-singular.

Used by `Hironaka/Resolution/Analytic/Kol07Thm45/ResolutionSncGlobal.lean`,
`Hironaka/AnalyticSpace/SncFamilyManifold.lean` and `Hironaka/AnalyticSpace/SncBoundaryChart.lean`.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set Manifold

universe u

namespace AnalyticSpace

namespace ClosedSubspace

variable {K : Type} [RCLike K] {X : AnalyticSpace.{u} K}

/-- The support of the divisor of a locally finite family is the union of the members' supports
(Kollár's `E = Σ Eᵢ`, [Kol07, Definition 24]): a finite product of proper ideals of a local ring is
proper, and off every member the product is the unit ideal. -/
theorem support_divisorOf {ι : Type u} (H : ι → ClosedSubspace X)
    (hH : LocallyFinite fun j => (H j).support) :
    (divisorOf H hH).support = ⋃ j, (H j).support := by
  ext x
  change (divisorOf H hH).stalkIdeal x ≠ ⊤ ↔ x ∈ ⋃ j, (H j).support
  rw [stalkIdeal_divisorOf, Set.mem_iUnion]
  constructor
  · intro hne
    by_contra hx
    refine hne ?_
    rw [Finset.prod_eq_one, Ideal.one_eq_top]
    intro j hj
    exact absurd ⟨j, (Set.Finite.mem_toFinset (hH.point_finite x)).mp hj⟩ hx
  · rintro ⟨j, hj⟩ htop
    have hle : ∏ i ∈ (hH.point_finite x).toFinset, (H i).stalkIdeal x ≤ (H j).stalkIdeal x :=
      Ideal.prod_le_inf.trans (Finset.inf_le ((Set.Finite.mem_toFinset _).mpr hj))
    rw [htop, top_le_iff] at hle
    exact hj hle

/-- The divisor of an snc family is an snc boundary ([Kol07, Definition 24]): the body of
`IsSncBoundaryWith` read off `stalkIdeal_divisorOf` with the finset `s := Finset.univ.image c` on
the finite subtype of the members through `x`. -/
theorem isSncBoundary_divisorOf {ι : Type u} {H : ι → ClosedSubspace X} (h : IsSncFamily H) :
    (divisorOf H h.1).IsSncBoundary := by
  classical
  refine ⟨ι, H, h.1, fun x => ?_⟩
  obtain ⟨n, z, hz, c, hc, hcz⟩ := h.2 x
  have hfin : Finite {j // x ∈ (H j).support} := (h.1.point_finite x).to_subtype
  let _ : Fintype {j // x ∈ (H j).support} := Fintype.ofFinite _
  refine ⟨n, z, hz, ⟨c, Finset.univ.image c, hc, ?_, hcz, ?_⟩, fun _ => ⟨∅, ?_⟩⟩
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  · rw [stalkIdeal_divisorOf, ← Ideal.prod_span_singleton,
      Finset.prod_image (fun a _ b _ hab => hc hab),
      Finset.prod_subtype (h.1.point_finite x).toFinset (fun j => Set.Finite.mem_toFinset _)]
    exact Finset.prod_congr rfl fun j _ => hcz j
  · rw [IdealSheaf.stalkIdeal_bot, Finset.coe_empty, Set.image_empty, Ideal.span_empty]
    rfl

/-- `IsSncBoundary` is exactly "the divisor of an snc family". -/
theorem isSncBoundary_iff_exists_isSncFamily_divisorOf (E : ClosedSubspace X) :
    E.IsSncBoundary ↔ ∃ (ι : Type u) (H : ι → ClosedSubspace X)
      (hH : LocallyFinite fun j => (H j).support), IsSncFamily H ∧ E = divisorOf H hH := by
  constructor
  · rintro ⟨ι, H, hlf, hx⟩
    refine ⟨ι, H, hlf, ⟨hlf, fun x => ?_⟩, IdealSheaf.ext fun x => ?_⟩
    · obtain ⟨n, z, hz, ⟨c, s, hc, -, hcz, -⟩, -⟩ := hx x
      exact ⟨n, z, hz, c, hc, hcz⟩
    · classical
      obtain ⟨n, z, -, ⟨c, s, hc, hrange, hcz, hE⟩, -⟩ := hx x
      have hfin : Finite {j // x ∈ (H j).support} := (hlf.point_finite x).to_subtype
      let _ : Fintype {j // x ∈ (H j).support} := Fintype.ofFinite _
      have hs : Finset.univ.image c = s := Finset.coe_injective (by
        rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hrange])
      rw [hE, stalkIdeal_divisorOf, ← hs, ← Ideal.prod_span_singleton,
        Finset.prod_image (fun a _ b _ hab => hc hab),
        Finset.prod_subtype (hlf.point_finite x).toFinset (fun j => Set.Finite.mem_toFinset _)]
      exact (Finset.prod_congr rfl fun j _ => hcz j).symm
  · rintro ⟨ι, H, hH, h, rfl⟩
    exact isSncBoundary_divisorOf h

/-- The boundary case: the empty divisor `⊤` (the unit ideal) is an snc boundary iff every stalk of
`X` is a regular local ring, i.e. iff `X` is non-singular — `IsSncBoundary` presupposes a regular
system of parameters at every point (Mathlib's `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`,
`IsLocalRing.exists_regularSystem`; the analytic stalks are Noetherian,
`isNoetherianRing_stalk`). -/
theorem isSncBoundary_top_iff_isNonsingular :
    IsSncBoundary (⊤ : ClosedSubspace X) ↔ X.IsNonsingular := by
  constructor
  · rintro ⟨ι, H, -, hx⟩
    refine Set.eq_univ_iff_forall.mpr fun x => ?_
    obtain ⟨n, z, ⟨hspan, hdim⟩, -, -⟩ := hx x
    have : IsNoetherianRing (X.presheaf.stalk x) := AnalyticSpace.isNoetherianRing_stalk X x
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
    rw [← hdim, ← hspan]
    have hle : (Ideal.span (Set.range z)).spanFinrank ≤ n := by
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_
      calc (Set.range z).ncard = (z '' Set.univ).ncard := by rw [Set.image_univ]
        _ ≤ (Set.univ : Set (Fin n)).ncard := Set.ncard_image_le Set.finite_univ
        _ = n := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact_mod_cast hle
  · intro hX
    refine ⟨PEmpty.{u + 1}, fun j => j.elim, locallyFinite_of_finite _, fun x => ?_⟩
    have hreg : IsRegularLocalRing (X.presheaf.stalk x) :=
      Set.eq_univ_iff_forall.mp hX x
    obtain ⟨d, z, hz, hd⟩ := IsLocalRing.exists_regularSystem (X.presheaf.stalk x)
    have : IsEmpty {j : PEmpty.{u + 1} // x ∈ ((fun j => j.elim) j : ClosedSubspace X).support} :=
      ⟨fun j => j.1.elim⟩
    refine ⟨d, z, ⟨hz.symm, hd⟩, ⟨fun j => j.1.elim, ∅, fun j => j.1.elim, ?_, fun j => j.1.elim,
      ?_⟩, fun _ => ⟨∅, ?_⟩⟩
    · rw [Set.range_eq_empty, Finset.coe_empty]
    · rw [IdealSheaf.stalkIdeal_top, Finset.prod_empty, Ideal.span_singleton_one]
      rfl
    · rw [IdealSheaf.stalkIdeal_bot, Finset.coe_empty, Set.image_empty, Ideal.span_empty]
      rfl

end ClosedSubspace

end AnalyticSpace

end
