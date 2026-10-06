/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Basic
public import Hironaka.Resolution.Analytic.LocalIsoEquiv
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.BlowUp.Transform.StrictSubspaceCompletion
import Hironaka.Manifold.Chart.Swap
import Hironaka.Manifold.Completion
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Basic
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Resolution.Analytic.MaximalContact.CoordCriterion
import Hironaka.Resolution.Analytic.MaximalContact.PropagationLemmas
import Hironaka.Resolution.Analytic.MaximalContact.SwapRealizes
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init

/-!
# The local-isomorphism equivalence on a neighbourhood of a point

The propagation step of Kollár's proof of the uniqueness of maximal contact [Kol07, 95]: the
conditions (91.1′–4′), established at `p`, also hold in an open neighbourhood `U(p)` of `p`, by
Krull's intersection theorem [Kol07, Definition 55]. The coordinate swap of
`Hironaka/Resolution/Analytic/MaximalContact/SwapRealizes.lean` (`exists_realizing_swap`) gives, at
a point `p` of `cosupp(I, m)`, two charts `e, e'` centred at `p`, the swap `Φ = e'⁻¹ ∘ e` (a partial
analytic isomorphism fixing `p`) and its pull-back of germs `r = Φ^*` with `r(I_{H'}) = I_H`,
`r(I_p) = I_p`, `r(I_{E^j}) = I_{E^j}` and `s − r s ∈ MC(I)_p`. This module spreads these four
stalk-level identities to a neighbourhood:

* on the open submanifold `N := Φ.source`, with `ι₀ : N → M` the inclusion and `Φ₀ := Φ ∘ ι₀`, the
  stalk map of `Φ₀` at `p` is `ι₀^* ∘ r`, so `Φ₀^*J` and `ι₀^*J` have the same stalk at `p` for
  `J = I, I_H/I_{H'}, I_{E^j}`; two ideal sheaves with the same stalk at a point agree on a
  neighbourhood (`IdealSheaf.exists_opens_forall_stalkIdeal_eq` — Kollár's "(55)", Krull's
  intersection theorem [Kol07, Definition 55], through `eventually_stalkIdeal_le`), and their
  cosupports then agree there: (1′), (2′) and (3′) for the finitely many `E^j` meeting a
  neighbourhood of `p` (local finiteness of the snc family; the other components miss both `U(p)`
  and `Φ(U(p))`);
* (4′): the coordinate defects `dᵢ := e'ᵢ − e'ᵢ ∘ Φ` are sections near `p` whose germs at `p` are
  `e'ᵢ − r(e'ᵢ) ∈ MC(I)_p`, hence lie in `MC(I)` near `p` (`eventually_germ_mem_stalkIdeal`). At a
  point `q` of `V(MC(I))` all `dᵢ(q) = 0`, so `e'(Φ q) = e'(q)` and `Φ q = q`; and the two stalk
  maps `ι^*`, `Φ^*` at `q` agree on the constants and differ on the coordinate germs `e'ᵢ` by the
  germs of the `dᵢ`, hence differ by `MC(I)_q` on every germ (the coordinate criterion
  `sub_mem_of_forall_coord_sub_mem`) — `AgreeOnSubspace ι Φ (MC(ι^*I))`, the derivatives
  commuting with the restriction to the open subset (`iteratedDeriv_restrictOpens`).

`U(p)` is the intersection of these neighbourhoods; `Φ : U(p) → M` is a local analytic
isomorphism and an open embedding (`PartialDiffeomorph.isLocalDiffeomorph_comp_subtype_val`).
Włodarczyk's glueing automorphism has the same properties on a neighbourhood
[Wlo09, Lemma 5.5.3, proof, (1)]. The neighbourhoods are assembled into a covering in
`Hironaka/Resolution/Analytic/MaximalContact/Covering.lean`.
-/

public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology Set IsLocalRing
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : AnalyticManifold.{u} 𝕜 E}

/-- The propagation step of [Kol07, 95] ("(91.1′–4′) also hold in an open neighbourhood `U(p)`
by (55)"; [Wlo09, Lemma 5.5.3, proof, (1)]): at every point `p` of `cosupp(I, m)` there are an
open neighbourhood `U(p)` of `p` and a local analytic isomorphism `Φ : U(p) → M` fixing `p`, an
open embedding (onto Kollár's `V(p)`), such that for the pair `ψ :=` the inclusion `U(p) → M`,
`ψ' := Φ`: (1′) `ψ⁻¹(H) = ψ'⁻¹(H')`, (2′) `ψ^*I = ψ'^*I`, (3′) `ψ⁻¹(E^i) = ψ'⁻¹(E^i)` for every
component, and (4′) `ψ`, `ψ'` agree on `V(MC(ψ^*I))`. The map is the coordinate swap `e'⁻¹ ∘ e` of
`exists_realizing_swap` restricted to `U(p)`; the four identities spread from the stalk at `p` to
a neighbourhood as explained in the module docstring. -/
theorem locallyIsoEquivalent_on_nhd (I : AnalyticManifold.IdealSheaf M) {m : ℕ} (hm : 1 ≤ m)
    (hI : I.iteratedDeriv (m - 1) * I.deriv ≤ I) (F : HypersurfaceFamily M) (hF : F.IsSnc ψ)
    {H H' : Set M} (hH : IsClosedSubmanifold ψ H 1)
    (hH' : IsClosedSubmanifold ψ H' 1) (hHmc : hH.idealSheaf ≤ I.iteratedDeriv (m - 1))
    (hH'mc : hH'.idealSheaf ≤ I.iteratedDeriv (m - 1)) (hHF : (F.append H).IsSnc ψ)
    (hH'F : (F.append H').IsSnc ψ) (p : M) (hp : I.ord p = (m : ℕ∞)) :
    ∃ (U : Opens M) (hpU : p ∈ U) (Φ : AnalyticMap (M.restrict U) M),
      IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω Φ ∧ Topology.IsOpenEmbedding ⇑Φ ∧ Φ ⟨p, hpU⟩ = p ∧
        ⇑(M.inclusion U) ⁻¹' H = ⇑Φ ⁻¹' H' ∧
        I.pullback _ (M.inclusion U).contMDiff =
            I.pullback Φ Φ.contMDiff ∧
        (∀ j, ⇑(M.inclusion U) ⁻¹' F.hyp j = ⇑Φ ⁻¹' F.hyp j) ∧
        AgreeOnSubspace (M.inclusion U) Φ
          ((I.pullback _ (M.inclusion U).contMDiff).iteratedDeriv (m - 1)) := by
  classical
  have hpH : p ∈ H := mem_of_idealSheaf_le_iteratedDeriv ψ I hm hH hHmc hp
  have hpH' : p ∈ H' := mem_of_idealSheaf_le_iteratedDeriv ψ I hm hH' hH'mc hp
  obtain ⟨e, e', he, he', hpe, hpe', Φ, r, he0, he'0, hΦ, hr, -, hrH, hrI, hrE, hrMC, -⟩ :=
    exists_realizing_swap ψ I hm hI hF hH hH' hHmc hH'mc hHF hH'F p hp
  obtain ⟨hΦt, hrs⟩ := hr
  have hpΦ : p ∈ Φ.source := hΦ.1
  have hΦp : Φ p = p := hΦ.apply_self' hpe' he0 he'0
  -- the open submanifold `N := Φ.source`, its inclusion `ι₀` and `Φ₀ := Φ ∘ ι₀`
  let U₀ : Opens M := ⟨Φ.source, Φ.open_source⟩
  let ι₀ : AnalyticMap (M.restrict U₀) M := M.inclusion U₀
  let Φ₀ : AnalyticMap (M.restrict U₀) M :=
    ⟨fun x => Φ x.1,
      Φ.contMDiffOn_toFun.comp_contMDiff (contMDiff_subtype_val (U := U₀)) fun x => x.2⟩
  let q₀ : M.restrict U₀ := ⟨p, hpΦ⟩
  -- `r` is the stalk map of `Φ` at `p`: through `ι₀`, `Φ₀^* = ι₀^* ∘ r` on the stalk at `p`
  have hcomp : (germMap (⇑Φ₀) Φ₀.contMDiff q₀).comp (stalkCast hΦp.symm) =
      (germMap (⇑ι₀) ι₀.contMDiff q₀).comp r := by
    refine RingHom.ext fun s => ?_
    change germMap (⇑Φ₀) Φ₀.contMDiff q₀ (stalkCast hΦp.symm s) =
      germMap (⇑ι₀) ι₀.contMDiff q₀ (r s)
    obtain ⟨V, hpV, g, rfl⟩ := (structureSheaf 𝕜 E M).presheaf.exists_germ_eq s
    have hΦpV : Φ p ∈ V := by rw [hΦp]; exact hpV
    let W : Opens M := ⟨Φ.source ∩ Φ ⁻¹' V,
      Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_source V.2⟩
    have hpW : p ∈ W := ⟨hpΦ, hΦpV⟩
    have hW : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω (extendSection 𝕜 E g ∘ Φ) W :=
      (contMDiffOn_extendSection g).comp (Φ.contMDiffOn_toFun.mono inter_subset_left)
        fun _ hx => hx.2
    have hrg : r ((structureSheaf 𝕜 E M).presheaf.germ V p hpV g) =
        (structureSheaf 𝕜 E M).presheaf.germ W p hpW (sectionOfContMDiffOn _ W hW) := by
      apply stalkToGerm_injective
      rw [hrs, stalkToGerm_germ_sectionOfContMDiffOn, stalkToGerm_structureSheaf_germ]
      exact Germ.coe_compTendsto (l := 𝓝 p) (extendSection 𝕜 E g) hΦt
    rw [hrg, stalkCast_germ hΦp.symm hpV hΦpV]
    refine germMap_germ_eq_germMap_germ_of_eventuallyEq (W₁ := V) (W₂ := W) Φ₀ ι₀ q₀ hΦpV hpW g
      _ ?_
    filter_upwards [(continuous_subtype_val.tendsto q₀).eventually (W.2.eventually_mem hpW)]
      with x hx
    change extendSection 𝕜 E g (Φ x.1) = extendSection 𝕜 E (sectionOfContMDiffOn _ W hW) x.1
    rw [extendSection_of_mem 𝕜 E _ hx, sectionOfContMDiffOn_apply]
    rfl
  -- the stalks at `p` of `Φ₀^*J` and `ι₀^*J`
  have hkey : ∀ J : AnalyticManifold.IdealSheaf M,
      (J.pullback Φ₀ Φ₀.contMDiff).stalkIdeal q₀ =
        Ideal.map (germMap (⇑ι₀) ι₀.contMDiff q₀) (Ideal.map r (J.stalkIdeal p)) := by
    intro J
    have h1 : J.stalkIdeal (Φ₀ q₀) = Ideal.map (stalkCast hΦp.symm) (J.stalkIdeal p) :=
      (map_stalkCast_stalkIdeal J hΦp.symm).symm
    rw [stalkIdeal_comap_eq_map_germMap, h1, Ideal.map_map, hcomp]
    exact (Ideal.map_map r (germMap (⇑ι₀) ι₀.contMDiff q₀)).symm
  have hA : (I.pullback ι₀ ι₀.contMDiff).stalkIdeal q₀ =
      (I.pullback Φ₀ Φ₀.contMDiff).stalkIdeal q₀ := by
    rw [hkey, hrI]
    exact stalkIdeal_comap_eq_map_germMap ι₀ I q₀
  have hstH : hH.idealSheaf.stalkIdeal p = vanishingStalk (E := E) H p :=
    (hH.stalkIdeal_idealSheaf_of_mem hpH).trans (hH.ker_restrictStalk_eq_vanishingStalk hpH)
  have hstH' : hH'.idealSheaf.stalkIdeal p = vanishingStalk (E := E) H' p :=
    (hH'.stalkIdeal_idealSheaf_of_mem hpH').trans (hH'.ker_restrictStalk_eq_vanishingStalk hpH')
  have hB : (hH.idealSheaf.pullback ι₀ ι₀.contMDiff).stalkIdeal q₀ =
      (hH'.idealSheaf.pullback Φ₀ Φ₀.contMDiff).stalkIdeal q₀ := by
    rw [hkey, hstH', hrH, ← hstH]
    exact stalkIdeal_comap_eq_map_germMap ι₀ _ q₀
  have hC : ∀ j,
      ((hF.isClosedSubmanifold j).idealSheaf.pullback ι₀ ι₀.contMDiff).stalkIdeal
          q₀ =
        ((hF.isClosedSubmanifold j).idealSheaf.pullback Φ₀ Φ₀.contMDiff).stalkIdeal
            q₀ := by
    intro j
    rw [hkey]
    by_cases hpj : p ∈ F.hyp j
    · have hst : (hF.isClosedSubmanifold j).idealSheaf.stalkIdeal p =
          vanishingStalk (E := E) (F.hyp j) p :=
        ((hF.isClosedSubmanifold j).stalkIdeal_idealSheaf_of_mem hpj).trans
          ((hF.isClosedSubmanifold j).ker_restrictStalk_eq_vanishingStalk hpj)
      rw [hst, hrE j, ← hst]
      exact stalkIdeal_comap_eq_map_germMap ι₀ _ q₀
    · rw [(hF.isClosedSubmanifold j).stalkIdeal_idealSheaf_of_notMem hpj, Ideal.map_top,
        stalkIdeal_comap_eq_map_germMap,
        show (hF.isClosedSubmanifold j).idealSheaf.stalkIdeal (ι₀ q₀) = ⊤ from
          (hF.isClosedSubmanifold j).stalkIdeal_idealSheaf_of_notMem hpj]
      rfl
  -- propagate to a neighbourhood of `q₀` in `N`: (1′), (2′), (3′) and the local finiteness
  obtain ⟨t, ht, htfin⟩ := hF.locallyFinite p
  have ht₀ : ∀ᶠ y in 𝓝 p, y ∈ t := ht
  have hΦ₀t : ∀ᶠ x in 𝓝 q₀, Φ₀ x ∈ t := by
    have ht' : ∀ᶠ y in 𝓝 (Φ₀ q₀), y ∈ t := by
      rw [show Φ₀ q₀ = p from hΦp]
      exact ht₀
    exact (Φ₀.contMDiff.continuous.tendsto q₀).eventually ht'
  have hι₀t : ∀ᶠ x in 𝓝 q₀, ι₀ x ∈ t := (ι₀.contMDiff.continuous.tendsto q₀).eventually ht₀
  have hNev : ∀ᶠ x in 𝓝 q₀,
      (I.pullback ι₀ ι₀.contMDiff).stalkIdeal x =
          (I.pullback Φ₀ Φ₀.contMDiff).stalkIdeal x ∧
        (hH.idealSheaf.pullback ι₀ ι₀.contMDiff).stalkIdeal x =
          (hH'.idealSheaf.pullback Φ₀ Φ₀.contMDiff).stalkIdeal x ∧
        (∀ j ∈ {j | (F.hyp j ∩ t).Nonempty},
          ((hF.isClosedSubmanifold j).idealSheaf.pullback ι₀ ι₀.contMDiff).stalkIdeal x =
            ((hF.isClosedSubmanifold j).idealSheaf.pullback Φ₀ Φ₀.contMDiff).stalkIdeal x) ∧
        ι₀ x ∈ t ∧ Φ₀ x ∈ t := by
    filter_upwards [IdealSheaf.eventuallyEq_stalkIdeal_of_eq hA,
      IdealSheaf.eventuallyEq_stalkIdeal_of_eq hB,
      (Filter.eventually_all_finite htfin).mpr fun j _ =>
        IdealSheaf.eventuallyEq_stalkIdeal_of_eq (hC j), hι₀t, hΦ₀t] with x h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨Vall, hVsub, hVopen, hqV⟩ := mem_nhds_iff.mp hNev
  -- (4′): the coordinate defects `e'ᵢ − e'ᵢ ∘ Φ` on `W := Φ.source ∩ e'.source` lie in `MC(I)`
  let Ve' : Opens M := ⟨e'.source, e'.open_source⟩
  let W : Opens M := ⟨Φ.source ∩ e'.source, Φ.open_source.inter e'.open_source⟩
  have hWe' : W ≤ Ve' := fun _ hx => hx.2
  have hpW : p ∈ W := ⟨hpΦ, hpe'⟩
  have hcoord : ∀ i, ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω (fun y => ψ (e' y) i) e'.source := fun i =>
    ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => 𝕜) i).comp
      (ψ : E →L[𝕜] (Fin n → 𝕜))).contMDiff.comp_contMDiffOn
      (contMDiffOn_of_mem_maximalAtlas (n := ω) he')
  have hWi : ∀ i, ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω (fun x => ψ (e' (Φ x)) i) W := fun i =>
    (hcoord i).comp (Φ.contMDiffOn_toFun.mono inter_subset_left)
      fun _ hx => hΦ.apply_mem_source hx.1
  let d : Fin n → (structureSheaf 𝕜 E M).presheaf.obj (op W) := fun i =>
    (structureSheaf 𝕜 E M).presheaf.map (homOfLE hWe').op (chartSection E ψ e' he' i) -
      sectionOfContMDiffOn _ W (hWi i)
  have hd_germ : ∀ (x : M) (hx : x ∈ W) (i : Fin n),
      (structureSheaf 𝕜 E M).presheaf.germ W x hx (d i) =
        coord E ψ e' he' hx.2 i -
          (structureSheaf 𝕜 E M).presheaf.germ W x hx (sectionOfContMDiffOn _ W (hWi i)) := by
    intro x hx i
    change (structureSheaf 𝕜 E M).presheaf.germ W x hx
      ((structureSheaf 𝕜 E M).presheaf.map (homOfLE hWe').op (chartSection E ψ e' he' i) -
        sectionOfContMDiffOn _ W (hWi i)) = _
    rw [map_sub, TopCat.Presheaf.germ_res_apply]
    rfl
  have hrcoord : ∀ i, r (coord E ψ e' he' hpe' i) =
      (structureSheaf 𝕜 E M).presheaf.germ W p hpW (sectionOfContMDiffOn _ W (hWi i)) := by
    intro i
    apply stalkToGerm_injective
    rw [hrs, stalkToGerm_germ_sectionOfContMDiffOn, coord, stalkToGerm_structureSheaf_germ]
    refine (Germ.coe_compTendsto (l := 𝓝 p) (extendSection 𝕜 E (chartSection E ψ e' he' i))
      hΦt).trans (Germ.coe_eq.mpr ?_)
    filter_upwards [Φ.open_source.eventually_mem hpΦ] with x hx
    exact extendSection_of_mem 𝕜 E _ (hΦ.apply_mem_source hx)
  have hdmem : ∀ i, (structureSheaf 𝕜 E M).presheaf.germ W p hpW (d i) ∈
      (I.iteratedDeriv (m - 1)).stalkIdeal p := by
    intro i
    rw [hd_germ p hpW i, ← hrcoord i]
    exact hrMC _
  have hMev : ∀ᶠ x in 𝓝 p, x ∈ W ∧ ∀ i, ∀ hx : x ∈ W,
      (structureSheaf 𝕜 E M).presheaf.germ W x hx (d i) ∈
        (I.iteratedDeriv (m - 1)).stalkIdeal x := by
    filter_upwards [W.2.eventually_mem hpW, Filter.eventually_all.mpr fun i =>
      IdealSheaf.eventually_germ_mem_stalkIdeal _ hpW (d i) (hdmem i)] with x h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨Wd, hWdsub, hWdopen, hpWd⟩ := mem_nhds_iff.mp hMev
  -- the neighbourhood `U(p)` and the maps `Φ' := Φ|_{U(p)}`, `j : U(p) → N`
  let U : Opens M :=
    ⟨Subtype.val '' Vall ∩ Wd, (U₀.2.isOpenMap_subtype_val Vall hVopen).inter hWdopen⟩
  have hpU : p ∈ U := ⟨⟨q₀, hqV, rfl⟩, hpWd⟩
  have hUU₀ : U ≤ U₀ := by
    rintro x ⟨⟨y, -, rfl⟩, -⟩
    exact y.2
  let Φ' : AnalyticMap (M.restrict U) M :=
    ⟨fun x => Φ x.1,
      Φ.contMDiffOn_toFun.comp_contMDiff (contMDiff_subtype_val (U := U)) fun x => hUU₀ x.2⟩
  let j : AnalyticMap (M.restrict U) (M.restrict U₀) :=
    ⟨Opens.inclusion hUU₀, contMDiff_inclusion hUU₀⟩
  have hjV : ∀ x : M.restrict U, j x ∈ Vall := by
    intro x
    obtain ⟨y, hy, hyx⟩ := x.2.1
    have hxy : j x = y := Subtype.ext hyx.symm
    rw [hxy]
    exact hy
  have hloc : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω Φ' :=
    PartialDiffeomorph.isLocalDiffeomorph_comp_subtype_val Φ U hUU₀
  have hemb : Topology.IsOpenEmbedding ⇑Φ' :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap Φ'.contMDiff.continuous
      (fun x y hxy =>
        Subtype.ext (Φ.toOpenPartialHomeomorph.injOn (hUU₀ x.2) (hUU₀ y.2) hxy))
      hloc.isOpenMap
  -- membership in a closed submanifold through the stalk of its ideal sheaf
  have hcos : ∀ (f : AnalyticMap (M.restrict U₀) M) {Y : Set M} {c : ℕ}
      (hY : IsClosedSubmanifold ψ Y c) (x : M.restrict U₀),
      f x ∈ Y ↔ (hY.idealSheaf.pullback f f.contMDiff).stalkIdeal x ≠ ⊤ := by
    intro f Y c hY x
    have h1 : (hY.idealSheaf.pullback f f.contMDiff).support = ⇑f ⁻¹' Y :=
      (IdealSheaf.support_pullback (⇑f) f.contMDiff hY.idealSheaf).trans
        (by rw [hY.cosupport_idealSheaf])
    rw [← IdealSheaf.mem_support, h1]
    exact Iff.rfl
  refine ⟨U, hpU, Φ', hloc, hemb, hΦp, ?_, ?_, ?_, ?_⟩
  · -- (1′)
    ext x
    obtain ⟨-, h, -⟩ := hVsub (hjV x)
    have h' : (hH.idealSheaf.pullback ι₀ ι₀.contMDiff).stalkIdeal (j x) ≠ ⊤ ↔
        (hH'.idealSheaf.pullback Φ₀ Φ₀.contMDiff).stalkIdeal (j x) ≠ ⊤ := by
      rw [h]
    exact (hcos ι₀ hH (j x)).trans (h'.trans (hcos Φ₀ hH' (j x)).symm)
  · -- (2′)
    have h1 : I.pullback _ (M.inclusion U).contMDiff =
        (I.pullback ι₀ ι₀.contMDiff).pullback ⇑j j.contMDiff :=
      (IdealSheaf.pullback_pullback I (⇑ι₀) ι₀.contMDiff (⇑j) j.contMDiff).symm
    have h2 : I.pullback Φ' Φ'.contMDiff =
        (I.pullback Φ₀ Φ₀.contMDiff).pullback ⇑j j.contMDiff :=
      (IdealSheaf.pullback_pullback I (⇑Φ₀) Φ₀.contMDiff (⇑j) j.contMDiff).symm
    rw [h1, h2]
    refine IdealSheaf.ext fun x => ?_
    obtain ⟨hx1, -⟩ := hVsub (hjV x)
    rw [IdealSheaf.stalkIdeal_pullback (⇑j) j.contMDiff, IdealSheaf.stalkIdeal_pullback (⇑j)
      j.contMDiff, hx1]
  · -- (3′)
    intro j'
    ext x
    obtain ⟨-, -, h3, h4, h5⟩ := hVsub (hjV x)
    by_cases hj' : j' ∈ {j | (F.hyp j ∩ t).Nonempty}
    · have h := h3 j' hj'
      have h' : ((hF.isClosedSubmanifold j').idealSheaf.pullback ι₀ ι₀.contMDiff).stalkIdeal (j x)
          ≠ ⊤ ↔
          ((hF.isClosedSubmanifold j').idealSheaf.pullback Φ₀ Φ₀.contMDiff).stalkIdeal (j x) ≠ ⊤ :=
              by
        rw [h]
      exact (hcos ι₀ (hF.isClosedSubmanifold j') (j x)).trans
        (h'.trans (hcos Φ₀ (hF.isClosedSubmanifold j') (j x)).symm)
    · exact iff_of_false (fun hx => hj' ⟨_, hx, h4⟩) fun hx => hj' ⟨_, hx, h5⟩
  · -- (4′)
    have hK : (I.pullback _ (M.inclusion U).contMDiff).iteratedDeriv (m - 1) =
        (I.iteratedDeriv (m - 1)).pullback _ (M.inclusion U).contMDiff :=
      AnalyticManifold.IdealSheaf.iteratedDeriv_restrictOpens I U (m - 1)
    rw [hK]
    refine agreeOnSubspace_of_forall_sub_mem (M.inclusion U) Φ' _ fun q hq => ?_
    have hqWd : q.1 ∈ Wd := q.2.2
    obtain ⟨hqW, hqd⟩ := hWdsub hqWd
    have hqe' : q.1 ∈ e'.source := hqW.2
    have hΦqe' : Φ q.1 ∈ e'.source := hΦ.apply_mem_source hqW.1
    have hMC : (I.iteratedDeriv (m - 1)).stalkIdeal q.1 ≠ ⊤ := by
      intro htop
      apply hq
      rw [stalkIdeal_comap_eq_map_germMap,
        show (I.iteratedDeriv (m - 1)).stalkIdeal ((M.inclusion U) q) = ⊤ from htop, Ideal.map_top]
    have hΦq : Φ q.1 = q.1 := by
      refine e'.injOn hΦqe' hqe' (ψ.injective (funext fun i => ?_))
      have hmem := IsLocalRing.le_maximalIdeal hMC (hqd i hqW)
      have hval : extendSection 𝕜 E (d i) q.1 = ψ (e' q.1) i - ψ (e' (Φ q.1)) i := by
        rw [extendSection_of_mem 𝕜 E _ hqW]
        rfl
      rw [mem_maximalIdeal_iff_eval, eval_germ', hval, sub_eq_zero] at hmem
      exact hmem.symm
    have hpp' : (M.inclusion U) q = Φ' q := hΦq.symm
    have hqe'' : (M.inclusion U) q ∈ e'.source := hqe'
    refine ⟨hpp', fun s => ?_⟩
    rw [stalkIdeal_comap_eq_map_germMap]
    have : IsLocalHom ((germMap (⇑Φ') Φ'.contMDiff q).comp (stalkCast hpp')) :=
      RingHom.isLocalHom_comp _ _
    refine sub_mem_of_forall_coord_sub_mem E ψ e' hqe'' he'
      (germMap (⇑(M.inclusion U)) (M.inclusion U).contMDiff q)
      ((germMap (⇑Φ') Φ'.contMDiff q).comp (stalkCast hpp')) (fun c => germMap_const _ _ _)
      (fun c => ?_) _ (fun i => ?_) s
    · rw [RingHom.comp_apply, stalkCast_const, germMap_const]
    · rw [RingHom.comp_apply, stalkCast_coord ψ hpp' he' hqe'' hΦqe' i]
      have hgerm : germMap (⇑Φ') Φ'.contMDiff q (coord E ψ e' he' hΦqe' i) =
          germMap (⇑(M.inclusion U)) (M.inclusion U).contMDiff q
            ((structureSheaf 𝕜 E M).presheaf.germ W ((M.inclusion U) q) hqW
              (sectionOfContMDiffOn _ W (hWi i))) := by
        refine germMap_germ_eq_germMap_germ_of_eventuallyEq (W₁ := Ve') (W₂ := W) Φ'
          (M.inclusion U) q hΦqe' hqW (chartSection E ψ e' he' i) _ ?_
        filter_upwards [(continuous_subtype_val.tendsto q).eventually (W.2.eventually_mem hqW)]
          with x hx
        change extendSection 𝕜 E (chartSection E ψ e' he' i) (Φ x.1) =
          extendSection 𝕜 E (sectionOfContMDiffOn _ W (hWi i)) x.1
        rw [extendSection_of_mem 𝕜 E _ hx, sectionOfContMDiffOn_apply,
          extendSection_of_mem 𝕜 E _ (hΦ.apply_mem_source hx.1)]
        rfl
      rw [hgerm, ← map_sub]
      refine Ideal.mem_map_of_mem _ ?_
      have hq' : (structureSheaf 𝕜 E M).presheaf.germ W ((M.inclusion U) q) hqW (d i) ∈
          (I.iteratedDeriv (m - 1)).stalkIdeal ((M.inclusion U) q) := hqd i hqW
      rw [hd_germ ((M.inclusion U) q) hqW i] at hq'
      exact hq'

end Hironaka.Manifold

end
