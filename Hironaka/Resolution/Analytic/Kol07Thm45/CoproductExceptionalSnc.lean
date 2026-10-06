/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductExceptionalFamily
import Hironaka.Algebra.RegularSmooth.QuotientRegular
import Hironaka.AnalyticSpace.Quotient
import Hironaka.AnalyticSpace.SncFamilyManifold
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.Germ.StalkNoetherian
import Hironaka.Manifold.Snc.Dictionary
import Hironaka.Manifold.Snc.NonSingular
import Hironaka.Resolution.Analytic.Principalization.MonomialStalk
import Hironaka.Resolution.Analytic.Wlo09.BoundaryBridge
import Hironaka.Resolution.Analytic.Wlo09.Clauses
import Hironaka.Resolution.Analytic.Wlo09.IsoOverReg
import Hironaka.Resolution.Analytic.Wlo09.PreimageSing
import Hironaka.Resolution.Analytic.Wlo09.ProperSncOfEmbeddedDesing
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The exceptional members of the coproduct run: normal crossings and support

Two facts about the datum's exceptional members `D.sigmaMembers bed W hW hbed`
(`CoproductExceptionalFamily.lean`): they form a simple normal crossings family of closed subspaces
of the coproduct's local resolution `Sp(Y_r)` (`ClosedSubspace.IsSncFamily`), and the union of their
supports is `Π_Σ⁻¹(Y_Σ.singularLocus)` — at the coproduct triple `D.sigmaTriple` over
`D.ambImage W`, the counterparts of the per-piece facts of
`Hironaka/Resolution/Analytic/Wlo09/PreimageSing.lean` ([Wlo09, Theorem 2.0.1(2)];
[Kol07, Definition 24]). The pieces of a datum are resolved by the ONE run on their disjoint union,
so the facts are the per-piece proofs with the piece's triple replaced by an arbitrary admissible
one — no new mathematics beyond one bridge.

**The support.** `PieceEmbedding.localResolutionMap_preimage_sing_eq`
(`Hironaka/Resolution/Analytic/Wlo09/PreimageSing.lean`) is restated at an arbitrary admissible
`(T, W)` (`BEDanFamStar.localResolutionMapOn_preimage_sing_eq`); its proof is the per-piece proof
verbatim — `hbed`'s clauses at `(T, W)` and the generic succession lemmas. The support of each
traced member is the preimage of the member (`QuotientSpace.cosupport_comap`,
`support_toClosedSubspaces_apply`) and `|E_r| = ⋃ⱼ E_j` by definition.

**The simple normal crossings family.** The trace bridge
`isSncFamily_comap_toAnalyticSpaceι_toClosedSubspaces` (Kollár's definition of simple normal
crossings with a subvariety, [Kol07, Definition 24], read on the members — the argument of
`isSncDivisorSet_toAnalyticSpace_of_forall` at the level of the family): on an analytic manifold
`A`, an ideal sheaf `J` with regular quotient stalks along its support and a simple normal crossings
family `F` with a PROPER ADAPTED chart at every point of `V(J)` — an adapted chart of `V(J)` which
is a simple normal crossings chart of `F` with the components' coordinates off `V(J)`'s block, the
data `IsProperSnc` of `Hironaka/Resolution/Analytic/Wlo09/ProperSnc.lean` — trace to a simple normal
crossings family of closed subspaces of `V(J)`. At a point `y` of `V(J)` with image `a` the centred
coordinates `z_1, …, z_n` of the chart are a regular system of parameters of `𝒪_{A,a}`,
`J_a = (z_σ)` (the vanishing ideal of `V(J)`, by the local Hadamard lemma), and the stalk map of the
closed immersion `V(J) → A` at `y` is the quotient map `𝒪_{A,a} → 𝒪_{A,a}/J_a`: the images of the
complementary coordinates generate `𝔪_y`, they are `n − c` in number with `dim 𝒪_{V(J),y} = n − c`
(the parameter count of the regular quotient, [Sta, Tag 00NQ]), and the traced member `j` through
`y` is cut out by the image of its coordinate `z_{cidx j}`, complementary by properness — the three
clauses of `IsSncFamily`. The datum's run satisfies the hypotheses by `hbed`'s clauses at the last
stage (`hbed.isProperSnc`, `Hironaka/Resolution/Analytic/Wlo09/ProperSncOfEmbeddedDesing.lean`;
clause (3) non-singularity through `mem_reg_toAnalyticSpace_iff`).

Not in the sources beyond Kollár's definition; bookkeeping.
-/

public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜]

/-! ### The support identity at any admissible `(T, W)` -/
section Generic

variable {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (bed : BEDanFamStar.{u} 𝕜) (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
  (hT : DomBEDan 𝕜 T) (W : Opens M) (hW : IsCompact (closure (W : Set M)))

/-- `Π⁻¹((Sp(W)/T.I|W).singularLocus) = Ỹ ∩ |E_r|` for the functor's run on `T|W`
([Wlo09, Theorem 2.0.1(2)]) — `localResolutionMap_preimage_sing_eq` with the piece's triple replaced
by an arbitrary admissible one; its proof transfers verbatim (`hbed`'s clauses at `(T, W)`: the
centres over the non-simple points, the non-singularity of `Ỹ`; the generic succession lemmas). -/
theorem BEDanFamStar.localResolutionMapOn_preimage_sing_eq (hbed : bed.IsEmbeddedDesing) :
    (bed.localResolutionMapOn T hT W hW) ⁻¹'
        (BEDanFamStar.restrictedIdealOn T W).toAnalyticSpace.singularLocus =
      (fun y => ((bed.lastIdealOn T hT W hW).toAnalyticSpaceι y :
          (bed.seqOn T hT W hW).toSuccession.stage (Fin.last _))) ⁻¹'
        ((bed.seqOn T hT W hW).toSuccession.totalTransformSeq (Fin.last _)).support := by
  set S := (bed.seqOn T hT W hW).toSuccession with hS
  set J := BEDanFamStar.restrictedIdealOn T W with hJ
  have hZ : S.CentersOver (AnalyticManifold.IdealSheaf.regSet J)ᶜ :=
    hbed.centersOver_compl_regSet n T hT W hW
  obtain ⟨-, -, -, hns, -, -⟩ := hbed.1 n T hT W hW
  ext y
  constructor
  · intro hy
    by_contra hE
    apply hy
    rw [mem_reg_toAnalyticSpace_iff]
    have hreg := (mem_reg_toAnalyticSpace_iff _ y).mp (Set.eq_univ_iff_forall.mp hns y)
    exact (S.isRegularLocalRing_quotient_strictTransformSubspaceSeq_iff_of_notMem_support J
      (Fin.last _) hE).mp hreg
  · intro hE hy
    exact S.support_totalTransformSeq_subset_preimage_of_centersOver hZ (Fin.last _) hE
      ⟨AnalyticSpace.KLocallyRingedSpace.Hom.toFun (bed.localResolutionMapOn T hT W hW) y,
        hy, rfl⟩

end Generic

/-! ### The trace bridge: an snc family with a proper adapted snc chart at every point of the
smooth closed subspace `V(J)` traces to an snc family of closed subspaces of `V(J)` -/
section Trace

variable {n : ℕ} {A : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-- The trace bridge ([Kol07, Definition 24], read on the members): at a point `y` of `V(J)` with
image `a`, the proper adapted snc chart gives the centred
coordinates `z_1, …, z_n` as a regular system of parameters of `𝒪_{A,a}` with `J_a = (z_σ)`; the
stalk map of the closed immersion is the quotient map `𝒪_{A,a} → 𝒪_{A,a}/J_a`, so the images of the
complementary coordinates are a regular system of parameters of `𝒪_{V(J),y}` (dimension `n − c` by
the parameter count of the regular quotient), and the traced member `j` through `y` is cut out by
the image of its coordinate `z_{cidx j}`, which is complementary by properness. -/
theorem isSncFamily_comap_toAnalyticSpaceι_toClosedSubspaces (J : AnalyticManifold.IdealSheaf A)
    (hns : ∀ a ∈ J.support, IsRegularLocalRing
      ((structureSheaf 𝕜 (Fin n → 𝕜) A).presheaf.stalk a ⧸ J.stalkIdeal a))
    {F : HypersurfaceFamily A} (hF : F.IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
    (hproper : ∀ x ∈ J.support, ∃ (c : ℕ) (φ : OpenPartialHomeomorph A (Fin n → 𝕜))
      (σ : Fin c ↪ Fin n) (cidx : {j // x ∈ F.hyp j} → Fin n),
      IsAdaptedChart (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) J.support φ σ ∧
      F.IsSncChartAt (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ x cidx ∧
      ∀ j, cidx j ∉ Set.range σ) :
    AnalyticSpace.ClosedSubspace.IsSncFamily fun j =>
      (F.toClosedSubspaces hF.1 j).comap J.toAnalyticSpaceι := by
  classical
  -- the support of a traced member is the preimage of the member
  have hsupp : ∀ j, ((F.toClosedSubspaces hF.1 j).comap J.toAnalyticSpaceι).support =
        (fun y : J.toAnalyticSpace => (y.1 : A)) ⁻¹' F.hyp j := by
    intro j
    refine (AnalyticSpace.QuotientSpace.cosupport_comap J.toAnalyticSpaceι.1
      (F.toClosedSubspaces hF.1 j)).trans ?_
    exact congrArg (Set.preimage _) (HypersurfaceFamily.support_toClosedSubspaces_apply F hF.1 j)
  refine ⟨?_, fun y => ?_⟩
  · exact (hF.2.1.preimage_continuous continuous_subtype_val).subset fun j => (hsupp j).subset
  obtain ⟨c, φ, σ, cidx, hφ, hc, hprop⟩ := hproper y.1 y.2
  have h0 : ∀ i, (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (φ y.1) (σ i) = 0 :=
    (hφ.2 y.1 hc.2.1).mp y.2
  -- the local ring `𝒪_{A,a}` (the instance, at the point spelled through the subspace)
  have _inst : IsLocalRing ((structureSheaf 𝕜 (Fin n → 𝕜) A).presheaf.stalk y.1) :=
    structureSheaf.instLocalRing_stalk 𝕜 (Fin n → 𝕜) A y.1
  -- the ambient space and the stalk map of the closed immersion at `y`: the quotient map
  -- `𝒪_{A,a} → 𝒪_{A,a}/J_a`
  let X₀ : AlgebraicGeometry.LocallyRingedSpace.{u} :=
    (AnalyticSpace.toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) A).toLocallyRingedSpace
  let π : (structureSheaf 𝕜 (Fin n → 𝕜) A).presheaf.stalk y.1 →+*
      J.toAnalyticSpace.presheaf.stalk y := (J.toAnalyticSpaceι.1.stalkMap y).hom
  have hπs : Function.Surjective π := AnalyticSpace.QuotientSpace.stalkMap_surjective X₀ J y
  have hπl : IsLocalHom π := AnalyticSpace.QuotientSpace.isLocalHom_stalkMap X₀ J y
  have hker : ∀ r, π r = 0 ↔ r ∈ J.stalkIdeal y.1 := by
    intro r
    have h1 := AnalyticSpace.QuotientSpace.evalHom_stalkMap X₀ J y r
    rw [← Ideal.Quotient.eq_zero_iff_mem (I := J.stalkIdeal y.1)]
    constructor
    · intro hr
      have h2 : (AnalyticSpace.QuotientSpace.evalHom X₀ J y).hom (π r) = 0 := by
        rw [hr]
        exact map_zero _
      exact h1.symm.trans h2
    · intro hr
      apply AnalyticSpace.QuotientSpace.evalHom_injective X₀ J y
      exact (h1.trans hr).trans (map_zero _).symm
  -- the centred coordinates: a regular system of parameters of `𝒪_{A,a}`
  obtain ⟨hspan, hdim⟩ := hc.span_range_centred_eq_and_dim
  let cz : Fin n → (structureSheaf 𝕜 (Fin n → 𝕜) A).presheaf.stalk y.1 := fun i =>
    coord (Fin n → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ hc.1 hc.2.1 i -
      const 𝕜 (Fin n → 𝕜) A y.1 (eval 𝕜 (Fin n → 𝕜) A y.1
        (coord (Fin n → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ hc.1 hc.2.1 i))
  have hspan' : Ideal.span (Set.range cz) =
      IsLocalRing.maximalIdeal ((structureSheaf 𝕜 (Fin n → 𝕜) A).presheaf.stalk y.1) := hspan
  have hcz0 : ∀ i, (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (φ y.1) i = 0 →
      cz i = coord (Fin n → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ hc.1 hc.2.1 i :=
    fun _ hi => HypersurfaceFamily.centred_coord_eq_of_eq_zero hi
  -- `J_a` is generated by the adapted coordinates
  have hJa : J.stalkIdeal y.1 = Ideal.span (Set.range fun k =>
      coord (Fin n → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ hc.1 hc.2.1 (σ k)) := by
    rw [stalkIdeal_eq_vanishingStalk_cosupport_of_isRegularLocalRing_quotient
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) J hns y.1,
      ← vanishingStalk_inter_of_mem_nhds (φ.open_source.mem_nhds hc.2.1)]
    have hZ : J.support ∩ φ.source =
        φ.source ∩ {x | ∀ i, (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (φ x) (σ i) = 0} := by
      ext x
      constructor
      · rintro ⟨hxJ, hx⟩
        exact ⟨hx, (hφ.2 x hx).mp hxJ⟩
      · rintro ⟨hx, hx0⟩
        exact ⟨(hφ.2 x hx).mpr hx0, hx⟩
    rw [hZ]
    exact vanishingStalk_zeroSet_eq_span_coord (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) hc.1
      hc.2.1 σ h0
  -- the complementary coordinates, indexed by `Fin (n - c)`
  let τ : Fin (n - c) → Fin n := fun m => ((complEquiv σ).symm m).1
  have hτc : ∀ (i : Fin n) (hi : i ∉ Set.range σ), τ (complEquiv σ ⟨i, hi⟩) = i := fun i hi => by
    simp only [τ, Equiv.symm_apply_apply]
  let z : Fin (n - c) → J.toAnalyticSpace.presheaf.stalk y := fun m => π (cz (τ m))
  refine ⟨n - c, z, ⟨?_, ?_⟩, ?_⟩
  · -- `𝔪_y = π(𝔪_a) = π(span cz) = span (π ∘ cz ∘ τ)`
    have hmax : IsLocalRing.maximalIdeal (J.toAnalyticSpace.presheaf.stalk y) =
        (IsLocalRing.maximalIdeal ((structureSheaf 𝕜 (Fin n → 𝕜) A).presheaf.stalk y.1)).map π := by
      refine le_antisymm ?_ (IsLocalRing.map_maximalIdeal_le π)
      intro s hs
      obtain ⟨r, rfl⟩ := hπs s
      by_cases hr :
          r ∈ IsLocalRing.maximalIdeal ((structureSheaf 𝕜 (Fin n → 𝕜) A).presheaf.stalk y.1)
      · exact Ideal.mem_map_of_mem π hr
      · exact absurd hs (IsLocalRing.notMem_maximalIdeal.mpr
          ((IsLocalRing.notMem_maximalIdeal.mp hr).map π))
    rw [hmax, ← hspan', Ideal.map_span]
    apply le_antisymm
    · refine Ideal.span_mono ?_
      rintro _ ⟨m, rfl⟩
      exact ⟨cz (τ m), ⟨τ m, rfl⟩, rfl⟩
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      by_cases hi : i ∈ Set.range σ
      · obtain ⟨k, rfl⟩ := hi
        have hzero : π (cz (σ k)) = 0 := by
          rw [hcz0 (σ k) (h0 k), hker, hJa]
          exact Ideal.subset_span ⟨k, rfl⟩
        change π (cz (σ k)) ∈ Ideal.span (Set.range z)
        rw [hzero]
        exact zero_mem _
      · exact Ideal.subset_span ⟨complEquiv σ ⟨i, hi⟩, congrArg (fun t => π (cz t)) (hτc i hi)⟩
  · -- `dim 𝒪_{V(J),y} = n - c`: the quotient of `𝒪_{A,a}` by `c` independent parameters
    have hreg := isRegularLocalRing_stalk_of_chart (Fin n → 𝕜)
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ hc.2.1 hc.1
    have hQ := IsRegularLocalRing.quotient_span_range_of_linearIndependent
      (fun k => coord (Fin n → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ hc.1 hc.2.1 (σ k))
      (fun k => coord_mem_maximalIdeal_of_eq_zero φ hc.1 hc.2.1 (h0 k))
      (linearIndependent_toCotangent_coord φ hc.1 hc.2.1 σ h0)
    have hkerπ : RingHom.ker π = Ideal.span (Set.range fun k =>
        coord (Fin n → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ hc.1 hc.2.1 (σ k)) := by
      rw [← hJa]
      exact Ideal.ext fun r => RingHom.mem_ker.trans (hker r)
    have e : J.toAnalyticSpace.presheaf.stalk y ≃+*
        ((structureSheaf 𝕜 (Fin n → 𝕜) A).presheaf.stalk y.1 ⧸ Ideal.span (Set.range fun k =>
          coord (Fin n → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ hc.1 hc.2.1 (σ k))) :=
      (RingHom.quotientKerEquivOfSurjective hπs).symm.trans (Ideal.quotEquivOfEq hkerπ)
    have hdimQ := hQ.2
    rw [Fintype.card_fin, ← hdim] at hdimQ
    have _instQ := hQ.1
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ringKrullDim ((structureSheaf 𝕜 (Fin n → 𝕜) A).presheaf.stalk y.1 ⧸
        Ideal.span (Set.range fun k =>
          coord (Fin n → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ hc.1 hc.2.1 (σ k))) =
        (k : WithBot ℕ∞) :=
      ⟨_, IsRegularLocalRing.spanFinrank_maximalIdeal.symm⟩
    rw [hk] at hdimQ
    have hkc : k + c = n := by exact_mod_cast hdimQ
    rw [ringKrullDim_eq_of_ringEquiv e, hk]
    congr 1
    omega
  · -- the index map and the stalk clause
    have hmem : ∀ j : {j // y ∈
        ((F.toClosedSubspaces hF.1 j).comap J.toAnalyticSpaceι).support}, y.1 ∈ F.hyp j.1 :=
      fun j => (Set.ext_iff.mp (hsupp j.1) y).mp j.2
    let e : {j // y ∈ ((F.toClosedSubspaces hF.1 j).comap J.toAnalyticSpaceι).support} →
        {j // y.1 ∈ F.hyp j} := fun j => ⟨j.1, hmem j⟩
    refine ⟨fun j => complEquiv σ ⟨cidx (e j), hprop (e j)⟩, fun j₁ j₂ h => ?_, fun j => ?_⟩
    · have h1 : cidx (e j₁) = cidx (e j₂) := congrArg Subtype.val ((complEquiv σ).injective h)
      exact Subtype.ext (show (e j₁).1 = (e j₂).1 from congrArg Subtype.val (hc.2.2.2 h1))
    · beta_reduce
      have h1 : (F.toClosedSubspaces hF.1 j.1).stalkIdeal y.1 =
          Ideal.span (Set.range fun i : Fin 1 => coord (Fin n → 𝕜)
            (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ hc.1 hc.2.1 (singleEmb (cidx (e j)) i)) :=
        (hF.1 j.1).stalkIdeal_idealSheaf_eq_span (hmem j) (hc.isAdaptedChart_hyp (e j)) hc.2.1
      have h2 : (Set.range fun i : Fin 1 => coord (Fin n → 𝕜)
          (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ hc.1 hc.2.1 (singleEmb (cidx (e j)) i)) =
          {coord (Fin n → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ hc.1 hc.2.1
            (cidx (e j))} := by
        rw [Set.range_unique, singleEmb_apply]
      have h3 : z (complEquiv σ ⟨cidx (e j), hprop (e j)⟩) =
          π (coord (Fin n → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ hc.1 hc.2.1
            (cidx (e j))) := by
        change π (cz (τ (complEquiv σ ⟨cidx (e j), hprop (e j)⟩))) = _
        rw [hτc, hcz0 _ (hc.coord_eq_zero (e j))]
      refine (AnalyticSpace.QuotientSpace.stalkIdeal_comap J.toAnalyticSpaceι.1
        (F.toClosedSubspaces hF.1 j.1) y).trans ?_
      rw [h3, ← Set.image_singleton, ← Ideal.map_span, ← h2]
      exact congrArg (Ideal.map π) h1

end Trace

end Hironaka.Manifold

/-! ### The two facts on the datum's single run -/
namespace Hironaka.Manifold.LocalEmbeddingData

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {U : Set X}
  (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
  (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
  (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))

/-- **The exceptional members of the datum's single run form a simple normal crossings family of
closed subspaces of the coproduct's local resolution** ([Kol07, Definition 24]) — the trace bridge
at `hbed`'s clauses on the coproduct run: `Ỹ_Σ` non-singular (clause (3)), `E_r` with simple normal
crossings (clause (1)), a proper adapted chart at every point of `Ỹ_Σ` (`hbed.isProperSnc`). -/
theorem isSncFamily_sigmaMembers (hbed : bed.IsEmbeddedDesing) :
    AnalyticSpace.ClosedSubspace.IsSncFamily (D.sigmaMembers bed W hW hbed) := by
  obtain ⟨hsnc1, -, -, hns, -, -⟩ :=
    hbed.1 D.n D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
      (D.isCompact_closure_ambImage W hW)
  have hproper := hbed.isProperSnc D.n D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
    (D.isCompact_closure_ambImage W hW)
  exact isSncFamily_comap_toAnalyticSpaceι_toClosedSubspaces _
    (fun a ha => (mem_reg_toAnalyticSpace_iff _ ⟨a, ha⟩).mp
      (Set.eq_univ_iff_forall.mp hns ⟨a, ha⟩))
    (hsnc1 (Fin.last _)) hproper.2

/-- **The union of the supports of the exceptional members is `Π_Σ⁻¹(Y_Σ.singularLocus)`**
([Wlo09, Theorem 2.0.1(2)]) — `localResolutionMapOn_preimage_sing_eq` at the coproduct triple, and
the support of each traced member is the preimage of the member. -/
theorem iUnion_support_sigmaMembers (hbed : bed.IsEmbeddedDesing) :
    (⋃ j, (D.sigmaMembers bed W hW hbed j).support) =
      (bed.localResolutionMapOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
        (D.isCompact_closure_ambImage W hW)) ⁻¹'
        (BEDanFamStar.restrictedIdealOn D.sigmaTriple
          (D.ambImage W)).toAnalyticSpace.singularLocus := by
  rw [bed.localResolutionMapOn_preimage_sing_eq _ _ _ _ hbed]
  ext y
  refine Set.mem_iUnion.trans (Iff.trans ?_ Set.mem_preimage.symm)
  refine Iff.trans ?_ (Set.mem_iUnion (s := (D.sigmaFamily bed W hW).hyp)).symm
  refine exists_congr fun j => ?_
  refine (Set.ext_iff.mp (AnalyticSpace.QuotientSpace.cosupport_comap
    (bed.lastIdealOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
      (D.isCompact_closure_ambImage W hW)).toAnalyticSpaceι.1 _) y).trans ?_
  refine Set.mem_preimage.trans ?_
  exact Set.ext_iff.mp (Manifold.HypersurfaceFamily.support_toClosedSubspaces_apply
    (D.sigmaFamily bed W hW) (D.isClosedSubmanifold_sigmaFamily bed W hW hbed) j) _

end Hironaka.Manifold.LocalEmbeddingData

end
