/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.SingularHypersurface
public import Hironaka.Resolution.Analytic.Wlo09.IsoOverReg
public import Hironaka.Resolution.Analytic.Principalization.IsoOff
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.Restrict.RestrictBundle
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Basic
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Manifold.Submanifold.CodimUnique
import Hironaka.Resolution.Analytic.Wlo09.BoundaryBridge
import Hironaka.Resolution.Analytic.Wlo09.Clauses

/-!
# The centres of codimension at most one lie in the exceptional divisor

Włodarczyk blows up only centres of codimension at least two [Wlo09, Remark (2) after
Theorem 2.0.3], and a centre of codimension one has an isomorphism as its blow-up and becomes a
component of the exceptional divisor [Wlo09, Remark (1) after Theorem 2.0.3]. For a succession
whose centres lie over the singular locus `Sing(Y)` of a reduced subspace `Y` and have simple
normal crossings with the exceptional divisors, this module proves that every centre of
codimension at most one lies in the exceptional divisor of its stage, and has codimension exactly
one (`FiniteSuccession.center_subset_support_totalTransformSeq_of_codim_le_one`): at a point of
the centre off the exceptional divisor the composite blow-down is a local analytic isomorphism
(its germ map is bijective, `germMap_stageMap_bijective_of_notMem_support`), and transports the
centre, a smooth hypersurface or an open set, into `Sing(Y)`, which contains no such germ
(`IdealSheaf.not_subset_sing_of_isClosedSubmanifold_one`, `not_subset_sing_of_isOpen`,
`Hironaka/Resolution/Analytic/Wlo09/SingularHypersurface.lean`), read on the open complement of
the exceptional divisor. A nonempty open centre has a point off the exceptional divisor: in an
snc chart, a point with all the coordinates of the components through the centre's point nonzero
(`exists_notMem_support_of_isSncChartAt`). Hence, in the simple normal crossings chart of the
centre, a centre of codimension one is a coordinate hyperplane contained in the union of the
coordinate hyperplanes of the exceptional components, so it is one of them, as Włodarczyk's
Remark (1) says. The arguments are not in the sources.
-/

@[expose] public section

noncomputable section

open Set Filter Topology TopologicalSpace IsLocalRing
open scoped Manifold ContDiff

universe u

/-! ### Stalks along a bijective germ map -/

namespace AnalyticManifold.IdealSheaf

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M N : AnalyticManifold.{u} 𝕜 E} (J : IdealSheaf M) (g : AnalyticMap N M) {b : N}
  (hb : Function.Bijective (germMap ⇑g g.contMDiff b))

include hb in
/-- Where the germ map of `g` is bijective, `b` lies in the support of `g^*J` iff `g b` lies in
the support of `J`. -/
theorem mem_support_pullback_iff_of_bijective : b ∈ (J.pullback g g.contMDiff).support ↔
    g b ∈ J.support := by
  change (J.pullback g g.contMDiff).stalkIdeal b ≠ ⊤ ↔ J.stalkIdeal (g b) ≠ ⊤
  rw [Manifold.IdealSheaf.stalkIdeal_pullback]
  exact not_congr (Hironaka.Manifold.Ideal.map_eq_top_iff_of_bijective _ hb _)

include hb in
/-- Where the germ map of `g` is bijective, the quotient of the stalk by `g^*J` is regular iff
the quotient at the image point by `J` is. -/
theorem isRegularLocalRing_quotient_stalkIdeal_pullback_iff_of_bijective :
    IsRegularLocalRing (stalkRing N b ⧸ (J.pullback g g.contMDiff).stalkIdeal b) ↔
      IsRegularLocalRing (stalkRing M (g b) ⧸ J.stalkIdeal (g b)) := by
  have e : stalkRing M (g b) ⧸ J.stalkIdeal (g b) ≃+*
      stalkRing N b ⧸ (J.pullback g g.contMDiff).stalkIdeal b :=
    Ideal.quotientEquiv _ _ (RingEquiv.ofBijective _ hb)
      (by rw [Manifold.IdealSheaf.stalkIdeal_pullback]; rfl)
  exact ⟨fun hr => IsRegularLocalRing.of_ringEquiv e.symm,
    fun hr => IsRegularLocalRing.of_ringEquiv e⟩

include hb in
/-- Where the germ map of `g` is bijective, the stalk of `g^*J` is radical iff the stalk of `J`
at the image point is. -/
theorem isRadical_stalkIdeal_pullback_iff_of_bijective :
    ((J.pullback g g.contMDiff).stalkIdeal b).IsRadical ↔ (J.stalkIdeal (g b)).IsRadical := by
  have hker : RingHom.ker (germMap ⇑g g.contMDiff b) ≤ J.stalkIdeal (g b) := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hb.1]
    exact bot_le
  have hinj : Function.Injective (Ideal.map (germMap ⇑g g.contMDiff b)) := fun A B h => by
    rw [← Ideal.comap_map_of_bijective _ hb (I := A), h, Ideal.comap_map_of_bijective _ hb]
  rw [Manifold.IdealSheaf.stalkIdeal_pullback, ← Ideal.radical_eq_iff, ← Ideal.radical_eq_iff,
    ← Ideal.map_radical_of_surjective hb.2 hker]
  exact hinj.eq_iff

end AnalyticManifold.IdealSheaf

/-! ### A point of a chart off the components through its centre -/

namespace Manifold.HypersurfaceFamily

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] {F : HypersurfaceFamily M}

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- **An open neighbourhood of a point of an snc family contains a point off the family**: in an
snc chart at `a`, a point with every coordinate of the components through `a` moved off `0`,
inside the open set avoiding the components not through `a`. -/
theorem exists_notMem_support_of_isSncChartAt (hF : F.IsSnc ψ) {φ : OpenPartialHomeomorph M E}
    {a : M} {c : {j // a ∈ F.hyp j} → Fin n} (hc : F.IsSncChartAt ψ φ a c) {O : Set M}
    (hO : IsOpen O) (haO : a ∈ O) : ∃ a' ∈ O ∩ φ.source, a' ∉ F.support := by
  -- the components not through `a` miss a neighbourhood of `a`
  set T : Set M := ⋃ j : {j // a ∉ F.hyp j}, F.hyp j.1 with hT
  have hTclosed : IsClosed T :=
    (hF.2.1.comp_injective Subtype.val_injective).isClosed_iUnion fun j => (hF.1 j.1).isClosed
  have haT : a ∉ T := by
    rintro ⟨_, ⟨j, rfl⟩, hj⟩
    exact j.2 hj
  -- the curve `t ↦ φ.symm (φ a + t • v)`, `v` the vector with all coordinates `1`
  set v : E := ψ.symm fun _ => 1 with hv
  have hcurve : Continuous fun t : 𝕜 => φ a + t • v := by fun_prop
  have h1 : ∀ᶠ t : 𝕜 in 𝓝 0, φ a + t • v ∈ φ.target := by
    have h0 : (fun t : 𝕜 => φ a + t • v) 0 ∈ φ.target := by
      simpa using φ.map_source hc.2.1
    exact hcurve.continuousAt.preimage_mem_nhds (φ.open_target.mem_nhds h0)
  have h2 : ∀ᶠ t : 𝕜 in 𝓝 0, φ.symm (φ a + t • v) ∈ O ∩ Tᶜ := by
    have hcont : ContinuousAt (fun t : 𝕜 => φ.symm (φ a + t • v)) 0 := by
      refine (φ.continuousAt_symm ?_).comp hcurve.continuousAt
      simpa using φ.map_source hc.2.1
    have hmem : (fun t : 𝕜 => φ.symm (φ a + t • v)) 0 ∈ O ∩ Tᶜ := by
      simp only [zero_smul, add_zero, φ.left_inv hc.2.1]
      exact ⟨haO, haT⟩
    exact hcont.preimage_mem_nhds ((hO.inter hTclosed.isOpen_compl).mem_nhds hmem)
  have : (𝓝[≠] (0 : 𝕜)).NeBot := NormedField.nhdsNE_neBot 0
  obtain ⟨t, ⟨ht1, ht2⟩, ht0⟩ := (((h1.and h2).filter_mono
    (nhdsWithin_le_nhds (s := {(0 : 𝕜)}ᶜ))).and
    (self_mem_nhdsWithin (a := (0 : 𝕜)) (s := {(0 : 𝕜)}ᶜ))).exists
  refine ⟨φ.symm (φ a + t • v), ⟨ht2.1, φ.map_target ht1⟩, ?_⟩
  rintro ⟨_, ⟨j, rfl⟩, hj⟩
  by_cases hja : a ∈ F.hyp j
  · -- a component through `a`: its coordinate at the new point is `t ≠ 0`
    have := (hc.2.2.1 ⟨j, hja⟩ _ (φ.map_target ht1)).mp hj
    rw [φ.right_inv ht1] at this
    have ha0 : ψ (φ a) (c ⟨j, hja⟩) = 0 := (hc.2.2.1 ⟨j, hja⟩ a hc.2.1).mp hja
    simp only [map_add, map_smul, hv, ContinuousLinearEquiv.apply_symm_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, mul_one, ha0, zero_add] at this
    exact ht0 (Set.mem_singleton_iff.mpr this)
  · -- a component not through `a`: the new point avoids it
    exact ht2.2 ⟨_, ⟨⟨j, hja⟩, rfl⟩, hj⟩

end Manifold.HypersurfaceFamily

/-! ### The centres of codimension at most one -/

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (S : FiniteSuccession M) (I : IdealSheaf M)

/-- **A centre of codimension at most one lies in the exceptional divisor, and has codimension
one** ([Wlo09, Remarks (1) and (2) after Theorem 2.0.3]), for a succession whose centres lie over
the singular locus of a reduced `Y` and have simple normal crossings with the exceptional
divisors: off the exceptional divisor the composite blow-down has bijective germ maps and
carries the centre, a smooth hypersurface or an open set, into `Sing(Y)`, which contains neither
(`IdealSheaf.not_subset_sing_of_isClosedSubmanifold_one`, `IdealSheaf.not_subset_sing_of_isOpen`,
read on the open complement of the exceptional divisor); a nonempty open centre has a point off
the exceptional divisor (`exists_notMem_support_of_isSncChartAt`). -/
theorem center_subset_support_totalTransformSeq_of_codim_le_one (hI : I.IsReduced)
    (hc : S.CentersOver (I.support \ I.regularLocus)) (i : Fin S.length)
    (hsnc : (S.totalTransformSeq i.castSucc).IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
    (hsncw : (S.totalTransformSeq i.castSucc).HasSncWith (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (S.center i).support (S.codim i))
    (hcod : S.codim i ≤ 1) (hne : (S.center i).support.Nonempty) :
    S.codim i = 1 ∧ (S.center i).support ⊆ (S.totalTransformSeq i.castSucc).support := by
  set X := S.stage i.castSucc with hX
  set W : Opens X := ⟨(S.totalTransformSeq i.castSucc).supportᶜ,
    hsnc.isClosed_support.isOpen_compl⟩ with hW
  set J := I.pullback (S.stageMap i.castSucc) (S.stageMap i.castSucc).contMDiff with hJ
  set J' := IdealSheaf.restrict J W with hJ'
  -- the germ maps of the inclusion of `W` and of the composite blow-down are bijective on `W`
  have hbij : ∀ z : X.restrict W,
      Function.Bijective (germMap ⇑(X.inclusion W) (X.inclusion W).contMDiff z) := fun z =>
    Manifold.germMap_bijective_of_isLocalDiffeomorphAt _ _ (isLocalDiffeomorph_inclusion X W z)
  have hbij' : ∀ z : X.restrict W, Function.Bijective (germMap ⇑(S.stageMap i.castSucc)
      (S.stageMap i.castSucc).contMDiff (X.inclusion W z)) := fun z =>
    S.germMap_stageMap_bijective_of_notMem_support i.castSucc z.2
  have hJ'red : IdealSheaf.IsReduced J' := fun z =>
    (IdealSheaf.isRadical_stalkIdeal_pullback_iff_of_bijective J _ (hbij z)).mpr
      ((IdealSheaf.isRadical_stalkIdeal_pullback_iff_of_bijective I _ (hbij' z)).mpr (hI _))
  -- the trace of the centre on `W` lies in the singular locus of `J'`
  have hsing : ∀ z : X.restrict W, X.inclusion W z ∈ (S.center i).support →
      z ∈ J'.support \ IdealSheaf.regularLocus J' := by
    intro z hz
    have hY := hc i hz
    refine ⟨(IdealSheaf.mem_support_pullback_iff_of_bijective J _ (hbij z)).mpr
      ((IdealSheaf.mem_support_pullback_iff_of_bijective I _ (hbij' z)).mpr hY.1),
      fun hreg => hY.2 ?_⟩
    exact (IdealSheaf.isRegularLocalRing_quotient_stalkIdeal_pullback_iff_of_bijective I _
      (hbij' z)).mp ((IdealSheaf.isRegularLocalRing_quotient_stalkIdeal_pullback_iff_of_bijective
        J _ (hbij z)).mp hreg)
  -- the codimension is not zero: an open centre would have a point off the exceptional divisor
  have hcod0 : S.codim i ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := hne
    obtain ⟨φ, σ, cidx, hadapt, hchart⟩ := hsncw a ha
    have hopen : φ.source ⊆ (S.center i).support := fun x hx =>
      (hadapt.2 x hx).mpr fun j => Fin.elim0 (Fin.cast h0 j)
    obtain ⟨a', ⟨ha'src, -⟩, ha'E⟩ := HypersurfaceFamily.exists_notMem_support_of_isSncChartAt
      hsnc hchart φ.open_source hchart.2.1
    exact IdealSheaf.not_subset_sing_of_isOpen J' (O := ⇑(X.inclusion W) ⁻¹' φ.source)
      (φ.open_source.preimage (X.inclusion W).contMDiff.continuous)
      (fun z hz => hsing z (hopen hz)) ⟨⟨a', ha'E⟩, ha'src⟩
  have hcod1 : S.codim i = 1 := by omega
  refine ⟨hcod1, fun a ha => ?_⟩
  by_contra haE
  have hH : IsClosedSubmanifold (S.chartAt i) (⇑(X.inclusion W) ⁻¹' (S.center i).support) 1 := by
    have := (S.isClosedSubmanifold_center i).restrictOpen W
    rwa [hcod1] at this
  exact IdealSheaf.not_subset_sing_of_isClosedSubmanifold_one J' hJ'red hH
    (fun z hz => hsing z hz) ⟨⟨a, haE⟩, ha⟩

/-- **The boundary of a stage lies in the ideal sheaf of a centre of codimension at most one**,
which has codimension one: the clause `two_le_codim_or_boundarySeq_le_center` of
`IsLocallyFinitelyDesingularizedBy` for one step, in the form of
`two_le_codim_or_boundarySeq_le_center_iff`, from
`center_subset_support_totalTransformSeq_of_codim_le_one`, the identification of the boundary with
the reduced ideal sheaf of the exceptional family (`hbd`), and the stalks of the centre's ideal
sheaf, the vanishing ideals of the centre (`isIdealSheafOf_center`, Hadamard's lemma
`vanishingStalk_zeroSet_eq_span_coord`). The codimension `c` of the hypothesis is the chosen one
(`IsClosedSubmanifold.codim_eq_of_nonempty`). -/
theorem boundarySeq_le_center_of_codim_le_one (hI : I.IsReduced)
    (hc : S.CentersOver (I.support \ I.regularLocus)) (i : Fin S.length)
    (hsnc : (S.totalTransformSeq i.castSucc).IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
    (hsncw : (S.totalTransformSeq i.castSucc).HasSncWith (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (S.center i).support (S.codim i))
    (hbd : S.boundarySeq ⊤ i.castSucc = (S.totalTransformSeq i.castSucc).idealSheaf)
    (hne : (S.center i).support.Nonempty) {n' c : ℕ} (ψ' : (Fin n → 𝕜) ≃L[𝕜] (Fin n' → 𝕜))
    (hc1 : c ≤ 1) (hC : IsClosedSubmanifold ψ' (S.center i).support c) :
    c = 1 ∧ ∀ a, (S.boundarySeq ⊤ i.castSucc).stalkIdeal a ≤ (S.center i).stalkIdeal a := by
  have hcod : S.codim i = c :=
    IsClosedSubmanifold.codim_eq_of_nonempty (S.isClosedSubmanifold_center i) hC hne
  obtain ⟨h1, hsub⟩ := S.center_subset_support_totalTransformSeq_of_codim_le_one I hI hc i hsnc
    hsncw (hcod ▸ hc1) hne
  refine ⟨hcod ▸ h1, ?_⟩
  intro a
  rw [hbd, HypersurfaceFamily.IsSnc.stalkIdeal_idealSheaf hsnc]
  by_cases ha : a ∈ (S.center i).support
  · obtain ⟨φ, σ, haφ, hφ⟩ := (S.isClosedSubmanifold_center i).exists_adaptedChart a ha
    rw [(S.isIdealSheafOf_center i).2 φ σ hφ a haφ ha,
      ← Hironaka.Manifold.vanishingStalk_zeroSet_eq_span_coord (S.chartAt i) hφ.1 haφ σ
        ((hφ.2 a haφ).mp ha)]
    exact vanishingStalk_anti (fun x hx => hsub ((hφ.2 x hx.1).mpr hx.2)) a
  · have htop : (S.center i).stalkIdeal a = ⊤ := by
      by_contra h
      exact ha h
    rw [htop]
    exact le_top

end AnalyticManifold.FiniteSuccession

/-! ### The codimension of a nonempty centre -/

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- **The codimension condition on a nonempty centre, in two forms**: the centre `C_i` has
codimension at least two, or codimension one and lies in the exceptional divisor `E_i` of its stage
(read through the chosen codimension `S.codim i`, with `E_i` stalkwise in the ideal sheaf of
`C_i`), exactly when every codimension `c ≤ 1` in which `C_i` is a closed submanifold, for any
chart of the model space, is one, with `E_i` stalkwise in the ideal sheaf of `C_i`. A nonempty
closed submanifold has one codimension (`IsClosedSubmanifold.codim_eq_of_nonempty`), and
`C_i ≠ ⊤` makes the centre nonempty (`IdealSheaf.eq_top_of_support_eq_empty`). -/
theorem two_le_codim_or_boundarySeq_le_center_iff (i : Fin S.length) (hne : S.center i ≠ ⊤) :
    (2 ≤ S.codim i ∨ S.codim i = 1 ∧
        ∀ x, (S.boundarySeq ⊤ i.castSucc).stalkIdeal x ≤ (S.center i).stalkIdeal x) ↔
      ∀ {n' c : ℕ} (ψ' : E ≃L[𝕜] (Fin n' → 𝕜)), c ≤ 1 →
        IsClosedSubmanifold ψ' (S.center i).support c →
          c = 1 ∧ ∀ x, (S.boundarySeq ⊤ i.castSucc).stalkIdeal x ≤ (S.center i).stalkIdeal x := by
  have hne' : (S.center i).support.Nonempty :=
    Set.nonempty_iff_ne_empty.mpr fun h => hne (IdealSheaf.eq_top_of_support_eq_empty h)
  constructor
  · rintro h n' c ψ' hc hC
    have hcod : S.codim i = c := (S.isClosedSubmanifold_center i).codim_eq_of_nonempty hC hne'
    rcases h with h | ⟨h1, hle⟩
    · omega
    · exact ⟨by omega, hle⟩
  · intro h
    by_cases h2 : 2 ≤ S.codim i
    · exact Or.inl h2
    · obtain ⟨h1, hle⟩ := h (S.chartAt i) (by omega) (S.isClosedSubmanifold_center i)
      exact Or.inr ⟨h1, hle⟩

end AnalyticManifold.FiniteSuccession

end

end
