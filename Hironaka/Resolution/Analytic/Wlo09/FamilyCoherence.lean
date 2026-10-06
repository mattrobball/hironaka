/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.ExceptionalDense
public import Hironaka.Resolution.Analytic.Principalization.IsoOff
public import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Defs
import Hironaka.Resolution.Analytic.Functor.ExtensionOf

/-!
# The coherence of the identifications in an extension-compatible family

An `ExtensionCompatibleFamily M` ([Wlo09, Theorem 2.0.3 (1) and (4)]) identifies, for every
compact `K`, the end result `U_r` of the succession `seq K` over `U_K = nhd K` with `map⁻¹(U_K)`
(`toSpace K`, an analytic isomorphism over `U_K`), and for `K₁ ⊆ K₂` asserts that the
restriction of `seq K₂` to `U_{K₁}` is an extension of `seq K₁` ([Wlo09, Definition 3.2.6]):
identifications `e k` of its stages with stages of `seq K₁`, over `U_{K₁}`. Włodarczyk's (4) says
that the restriction "determines the factorization" of the same map `prin_{I|Ũ₁}`; the structure
has no field tying `toSpace K₂`, restricted over `U_{K₁}`, to `toSpace K₁ ∘ e r`. None is needed:
the two agree, because an analytic map from the end result of a finite succession over `U_K` to
`M̃` over `U_K` is unique.

* `ExtensionCompatibleFamily.eq_of_map_comp_eq` (**uniqueness**): two analytic maps `f, g` from
  the end result `T_r` of a finite succession `T` over `U_K` to `M̃` with
  `map ∘ f = map ∘ g = σ^r_T` are equal. Over the complement of the images `Z` of the centres of
  `seq K` (`centerImages`) the composite blow-down of `seq K` is injective
  (`isAnalyticIsoOver_stageMap`, [Kol07, Theorem 35 (3)]), so `map` is injective on
  `map⁻¹(U_K ∖ Z)` through `toSpace K`, and `f = g` on `(σ^r_T)⁻¹(U_K ∖ Z)`. That set is dense in
  `T_r`: the composite of `T` is a local homeomorphism off the preimage of the images of its own
  centres, a dense set (`dense_preimage_compl_centerImages`), so the image of an open set contains
  an open set of `U_K` meeting the range of the composite of `seq K`, which the dense set
  `(σ^r)⁻¹(U_K ∖ Z)` of the end result of `seq K` meets. Continuous maps into a Hausdorff space
  agreeing on a dense set are equal (Mathlib's `Continuous.ext_on`).
* `restrictStageIncl`: the inclusion of the stages of the restriction of a succession to an open
  subset into the stages of the succession (the open inclusion `U₁ → U₂` at stage `0`, the
  inclusion of the trace at the later stages), compatible with the composite blow-downs
  (`val_composite_restrictStageIncl`).
* `ExtensionCompatibleFamily.toSpace_comp_restrictStageIncl_eq_of_composite_comp_eq` and
  `ExtensionCompatibleFamily.toSpace_comp_restrictStageIncl_eq` (**coherence**): for `K₁ ⊆ K₂`,
  `toSpace K₂` after the inclusion of the end result of the restriction of `seq K₂` to `U_{K₁}`
  equals `toSpace K₁` after any analytic map to the end result of `seq K₁` over `U_{K₁}` — in
  particular after the identification `e r` of the end results provided by any witness of
  `isExtensionOf_restrict` (its last-stage clause `blk r = r` and its over-`U_{K₁}` clause are the
  hypotheses; the stage `blk r` of `seq K₁` is carried to its last stage by the composite
  `stageMapLE`, the identity at equal indices).
-/

@[expose] public section

noncomputable section

open Set Topology Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace AnalyticManifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace FiniteSuccession

open Manifold

/-! ### The composite blow-down off the images of the centres -/

section CenterImages

variable {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- The centres of `S` lie over the images of the centres. -/
theorem centersOver_centerImages : S.CentersOver S.centerImages := fun k =>
  image_subset_iff.mp (S.image_stageMap_center_subset_centerImages k)

/-- The composite blow-down `σ^r : U_r → U_0` is an analytic isomorphism over the complement of
the images of the centres ([Kol07, Theorem 35 (3)]; `isAnalyticIsoOver_stageMap`). -/
theorem isIsoOver_composite_compl_centerImages : S.composite.IsIsoOver (S.centerImages)ᶜ :=
  isAnalyticIsoOver_stageMap S.centersOver_centerImages (Fin.last _)

end CenterImages

/-! ### The stage inclusions of a restriction -/

section RestrictIncl

variable {M : AnalyticManifold.{u} 𝕜 E} {U₂ : Opens M} (S : FiniteSuccession (M.restrict U₂))
  {U₁ : Opens M} (h : U₁ ≤ U₂)

/-- `ℕ`-indexed: the inclusion of the stage `(σ^m)⁻¹(U₁)` of the restriction of `S` to `U₁` into
the stage `U_m` of `S` — the open inclusion `U₁ → U₂` at stage `0` (`restrictOpensIncl`), the
inclusion of the trace, an open subset of `U_m`, at the later stages. -/
def restrictStageInclAux :
    ∀ (m : ℕ) (hm : m < S.length + 1),
      AnalyticMap ((S.restrict h).stage ⟨m, hm⟩) (S.stage ⟨m, hm⟩)
  | 0, _ => restrictOpensIncl h
  | m + 1, hm => (S.stage ⟨m + 1, hm⟩).inclusion (S.restrictStageOpens U₁ ⟨m + 1, hm⟩)

/-- The inclusion of the stage `i` of the restriction of `S` to `U₁ ≤ U₂` into the stage `U_i`
of `S` (the restriction's stages are the preimages of `U₁`, open subsets of the stages of `S`). -/
def restrictStageIncl (i : Fin (S.length + 1)) :
    AnalyticMap ((S.restrict h).stage i) (S.stage i) :=
  S.restrictStageInclAux h i.1 i.2

/-- `ℕ`-indexed: the composite blow-down of the restriction, read in `M`, is the composite
blow-down of `S` after the stage inclusion (`val_stageMap_restrict_aux` at the later stages). -/
theorem val_stageMap_restrictStageInclAux :
    ∀ (m : ℕ) (hm : m < S.length + 1) (p : (S.restrict h).stage ⟨m, hm⟩),
      ((S.restrict h).stageMap ⟨m, hm⟩ p).1 =
        (S.stageMap ⟨m, hm⟩ (S.restrictStageInclAux h m hm p)).1
  | 0, _, _ => rfl
  | m + 1, hm, p => val_stageMap_restrict_aux S h m hm p

/-- The composite blow-down of the restriction, read in `M`, is the composite blow-down of `S`
after the inclusion of the end results. -/
theorem val_composite_restrictStageIncl (p : (S.restrict h).last) :
    ((S.restrict h).composite p).1 = (S.composite (S.restrictStageIncl h (Fin.last _) p)).1 :=
  S.val_stageMap_restrictStageInclAux h S.length (Nat.lt_succ_self _) p

end RestrictIncl

/-- At two equal indices the composite `stageMapLE` between the stages is the transported
identity: it commutes with the composite blow-downs to `M` (`stageMapLE_self`). -/
theorem stageMap_stageMapLE_of_eq {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)
    {a b : Fin (S.length + 1)} (hab : a = b) (p : S.stage b) :
    S.stageMap a (S.stageMapLE hab.le p) = S.stageMap b p := by
  subst hab
  rw [stageMapLE_self]
  rfl

end FiniteSuccession

/-! ### The coherence of the identifications -/

namespace ExtensionCompatibleFamily

open FiniteSuccession

variable {M : AnalyticManifold.{u} 𝕜 E} (F : ExtensionCompatibleFamily M)

/-- `map ∘ toSpace K = σ^r` at a point, read in `M` (`map_toSpace`). -/
theorem map_toSpace_apply (K : Compacts M) (q : (F.seq K).last) :
    F.map (F.toSpace K q) = ((F.seq K).composite q).1 :=
  DFunLike.congr_fun (F.map_toSpace K) q

/-- `toSpace K` is onto `map⁻¹(U_K)` (the bijection clause of `toSpace_isIso`). -/
theorem exists_toSpace_eq (K : Compacts M) {q : F.space} (hq : F.map q ∈ F.nhd K) :
    ∃ a, F.toSpace K a = q :=
  let ⟨a, _, ha⟩ := (F.toSpace_isIso K).2.surjOn hq
  ⟨a, ha⟩

/-- **Uniqueness of the identification** ([Wlo09, Theorem 2.0.3 (4)]: the restriction of the
factorization of `prin_{I|Ũ₂}` "determines" that of `prin_{I|Ũ₁}`). Two analytic maps `f, g` from
the end result `T_r` of a finite succession `T` over `U_K` to `M̃` which are over `U_K`
(`map ∘ f = map ∘ g = σ^r_T`, as maps to `M`) are equal. Off the images `Z` of the centres of
`seq K` the composite blow-down of `seq K` is injective, so through the identification `toSpace K`
the map `map` is injective on `map⁻¹(U_K ∖ Z)` and `f = g` on `(σ^r_T)⁻¹(U_K ∖ Z)`; that set is
dense in `T_r`, and continuous maps into a Hausdorff space agreeing on a dense set are equal. -/
theorem eq_of_map_comp_eq (K : Compacts M) {T : FiniteSuccession (M.restrict (F.nhd K))}
    {f g : AnalyticMap T.last F.space}
    (hf : F.map.comp f = (M.inclusion (F.nhd K)).comp T.composite)
    (hg : F.map.comp g = (M.inclusion (F.nhd K)).comp T.composite) : f = g := by
  have hfp : ∀ p, F.map (f p) = (T.composite p).1 := fun p => DFunLike.congr_fun hf p
  have hgp : ∀ p, F.map (g p) = (T.composite p).1 := fun p => DFunLike.congr_fun hg p
  -- the points of the end result of `seq K` over a point of `T_r`, through `f` and through `g`
  have hlift : ∀ p, ∃ a, F.toSpace K a = f p ∧ (F.seq K).composite a = T.composite p := by
    intro p
    obtain ⟨a, ha⟩ := F.exists_toSpace_eq K (q := f p) (by rw [hfp]; exact (T.composite p).2)
    exact ⟨a, ha, Subtype.ext (by rw [← F.map_toSpace_apply, ha, hfp])⟩
  have hlift' : ∀ p, ∃ a, F.toSpace K a = g p ∧ (F.seq K).composite a = T.composite p := by
    intro p
    obtain ⟨a, ha⟩ := F.exists_toSpace_eq K (q := g p) (by rw [hgp]; exact (T.composite p).2)
    exact ⟨a, ha, Subtype.ext (by rw [← F.map_toSpace_apply, ha, hgp])⟩
  -- `f` and `g` agree over the complement of the images `Z` of the centres of `seq K`
  have hinj := (F.seq K).isIsoOver_composite_compl_centerImages.2.injOn
  have hEq : EqOn f g (T.composite ⁻¹' ((F.seq K).centerImages)ᶜ) := by
    intro p hp
    obtain ⟨a, ha, hπa⟩ := hlift p
    obtain ⟨b, hb, hπb⟩ := hlift' p
    have hab : a = b :=
      hinj (by rw [mem_preimage, hπa]; exact hp) (by rw [mem_preimage, hπb]; exact hp)
        (hπa.trans hπb.symm)
    rw [← ha, ← hb, hab]
  -- that set is dense in `T_r`
  have hdense : Dense (T.composite ⁻¹' ((F.seq K).centerImages)ᶜ) := by
    rw [dense_iff_inter_open]
    intro O hO hne
    -- a point of `O` off the images of the centres of `T`, where `σ^r_T` is a local homeomorphism
    obtain ⟨p, hpO, hpZ⟩ := T.dense_preimage_compl_centerImages.inter_open_nonempty O hO hne
    have hnhds : T.composite '' O ∈ 𝓝 (T.composite p) := by
      rw [← T.isIsoOver_composite_compl_centerImages.1.isLocalHomeomorphOn.map_nhds_eq hpZ]
      exact image_mem_map (hO.mem_nhds hpO)
    obtain ⟨V, hVO, hV, hpV⟩ := mem_nhds_iff.mp hnhds
    -- `σ^r_T p` is in the range of the composite of `seq K`, whose preimage of `U_K ∖ Z` is dense
    obtain ⟨a, -, hπa⟩ := hlift p
    obtain ⟨b, hbZ, hbV⟩ := (F.seq K).dense_preimage_compl_centerImages.exists_mem_open
      (hV.preimage (F.seq K).composite.contMDiff.continuous)
      ⟨a, show (F.seq K).composite a ∈ V by rw [hπa]; exact hpV⟩
    obtain ⟨q, hqO, hq⟩ := hVO (mem_preimage.mp hbV)
    exact ⟨q, hqO, by rw [mem_preimage, hq]; exact hbZ⟩
  exact ContMDiffMap.ext
    (congrFun (Continuous.ext_on hdense f.contMDiff.continuous g.contMDiff.continuous hEq))

/-- The identification `toSpace K₂` of the end result of the succession over `U_{K₂}`, after the
inclusion of the end result of its restriction to `U_{K₁}`, is over `U_{K₁}`. -/
theorem map_comp_toSpace_comp_restrictStageIncl {K₁ K₂ : Compacts M} (h : K₁ ≤ K₂) :
    F.map.comp ((F.toSpace K₂).comp
        ((F.seq K₂).restrictStageIncl (F.nhd_mono h) (Fin.last _))) =
      (M.inclusion (F.nhd K₁)).comp ((F.seq K₂).restrict (F.nhd_mono h)).composite :=
  ContMDiffMap.ext fun p =>
    (F.map_toSpace_apply K₂ _).trans
      ((F.seq K₂).val_composite_restrictStageIncl (F.nhd_mono h) p).symm

/-- **Coherence of the identifications, general form** ([Wlo09, Theorem 2.0.3 (4)]). For
`K₁ ⊆ K₂` and any analytic map `φ` from the end result of the restriction of `seq K₂` to `U_{K₁}`
to the end result of `seq K₁` which is over `U_{K₁}` (`σ^r_{K₁} ∘ φ` is the composite of the
restriction), `toSpace K₂` after the inclusion of the end results equals `toSpace K₁ ∘ φ`: both
are over `U_{K₁}`, and such a map is unique (`eq_of_map_comp_eq`). -/
theorem toSpace_comp_restrictStageIncl_eq_of_composite_comp_eq {K₁ K₂ : Compacts M}
    (h : K₁ ≤ K₂) (φ : AnalyticMap ((F.seq K₂).restrict (F.nhd_mono h)).last (F.seq K₁).last)
    (hφ : (F.seq K₁).composite.comp φ = ((F.seq K₂).restrict (F.nhd_mono h)).composite) :
    (F.toSpace K₂).comp ((F.seq K₂).restrictStageIncl (F.nhd_mono h) (Fin.last _)) =
      (F.toSpace K₁).comp φ :=
  F.eq_of_map_comp_eq K₁ (F.map_comp_toSpace_comp_restrictStageIncl h)
    (ContMDiffMap.ext fun p =>
      (F.map_toSpace_apply K₁ (φ p)).trans (congrArg Subtype.val (DFunLike.congr_fun hφ p)))

/-- **Coherence of the identifications** ([Wlo09, Theorem 2.0.3 (4)] with
[Wlo09, Definition 3.2.6]). For `K₁ ⊆ K₂` and a witness `(blk, e)` of `isExtensionOf_restrict`
— only its clauses `blk r = r` (`hl`) and "the `e k` are over `U_{K₁}`" (`hover`) are used — the
identification `toSpace K₂`, restricted to the end result of the restriction of `seq K₂` to
`U_{K₁}`, is `toSpace K₁` after the identification `e r` of the end results (the stage `blk r`
of `seq K₁` carried to its last stage by `stageMapLE`, the identity at equal indices): the
restriction of the factorization over `U_{K₂}` determines the factorization over `U_{K₁}`. -/
theorem toSpace_comp_restrictStageIncl_eq {K₁ K₂ : Compacts M} (h : K₁ ≤ K₂)
    (blk : Fin (((F.seq K₂).restrict (F.nhd_mono h)).length + 1) → Fin ((F.seq K₁).length + 1))
    (e : ∀ k, Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (((F.seq K₂).restrict (F.nhd_mono h)).stage k)
      ((F.seq K₁).stage (blk k)) ω)
    (hl : blk (Fin.last _) = Fin.last _)
    (hover : ∀ k p, (F.seq K₁).stageMap (blk k) (e k p) =
      ((F.seq K₂).restrict (F.nhd_mono h)).stageMap k p) :
    ⇑(F.toSpace K₂) ∘ ⇑((F.seq K₂).restrictStageIncl (F.nhd_mono h) (Fin.last _)) =
      ⇑(F.toSpace K₁) ∘ ⇑((F.seq K₁).stageMapLE hl.ge) ∘ ⇑(e (Fin.last _)) := by
  have key := F.toSpace_comp_restrictStageIncl_eq_of_composite_comp_eq h
    (((F.seq K₁).stageMapLE hl.ge).comp (e (Fin.last _)).toContMDiffMap)
    (ContMDiffMap.ext fun p =>
      ((F.seq K₁).stageMap_stageMapLE_of_eq hl.symm (e (Fin.last _) p)).trans (hover _ p))
  funext p
  exact DFunLike.congr_fun key p

end ExtensionCompatibleFamily

end AnalyticManifold

end

end
