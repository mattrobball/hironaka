/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Defs
import Hironaka.Manifold.BlowUp.Unique

/-!
# Density of the complement of the exceptional locus of a finite succession

For a finite succession `U_0 ← U_1 ← ⋯ ← U_r` of blow-ups with smooth centres `C_i ⊆ U_i`
(`FiniteSuccession`), the subset of `U_0` over which something is blown up is the union
`Z = ⋃_i σ^i(C_i)` of the images of the centres under the composite blow-downs (`centerImages`).
Off `Z` the composite `σ^r : U_r → U_0` is an analytic isomorphism ([Kol07, Theorem 35 (3)];
condition (1) of [BM88, Definition 4.1] iterated). This module proves that the preimage
`(σ^r)⁻¹(U_0 ∖ Z)` is dense in `U_r` (`dense_preimage_compl_centerImages`), so that two continuous
maps out of `U_r` which agree over `U_0 ∖ Z` are equal — the point-set input to the coherence of
the identifications of an extension-compatible family
(`Hironaka.Resolution.Analytic.Wlo09.FamilyCoherence`).

* `IsBlowUp.dense_compl_preimage_union`: for a blowing-up `π : M' → M` with centre `Y` and a set
  `A ⊆ M` with dense complement, `π⁻¹(A ∪ Y)` has dense complement in `M'`. The complement of the
  exceptional divisor `π⁻¹(Y)` is dense (`IsBlowUp.dense_preimage_compl`) and `π` is a local
  homeomorphism off it, so the image of an open set meeting `M' ∖ π⁻¹(Y)` contains a nonempty
  open set of `M`, which meets `M ∖ A`.
* `centerImagesLT j`, the images `⋃_{k<j} σ^k(C_k)` of the first `j` centres, and
  `injOn_and_dense_stageMapAux`: by induction on `j`, `σ^j` is injective over the complement of
  `centerImagesLT j` and the preimage of that complement is dense in `U_j`. At the step, a point
  of `U_j` over `σ^j(C_j)` but not over the earlier images lies in `C_j` (by the injectivity), so
  `(σ^{j+1})⁻¹(centerImagesLT (j+1))` is contained in the preimage under `σ_{j+1}` of
  `(σ^j)⁻¹(centerImagesLT j) ∪ C_j`, and the blow-up step applies.

No surjectivity of the blow-downs is used, so a centre of codimension `0` (for which `IsBlowUp`
forces `π⁻¹(Y) = ∅`, the blow-down being an isomorphism onto the complement of the centre) needs
no separate treatment.
-/

@[expose] public section

open Set Topology Filter
open scoped Manifold ContDiff Topology

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M}
  {c : ℕ} {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M}

/-- **The blow-up step.** For a blowing-up `π : M' → M` with centre `Y` and a set `A ⊆ M` whose
complement is dense, the complement of `π⁻¹(A ∪ Y)` is dense in `M'`: an open set `O ⊆ M'` meets
the dense complement of the exceptional divisor `π⁻¹(Y)` (`IsBlowUp.dense_preimage_compl`), on
which `π` is a local homeomorphism (condition (1) of [BM88, Definition 4.1]), so
`π(O ∖ π⁻¹(Y))` contains a nonempty open set of `M`, which meets the dense set `M ∖ A`. -/
theorem IsBlowUp.dense_compl_preimage_union (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) {A : Set M} (hA : Dense Aᶜ) : Dense (π ⁻¹' (A ∪ Y))ᶜ := by
  rw [dense_iff_inter_open]
  intro O hO hne
  obtain ⟨p, hpO, hpY⟩ := (h.dense_preimage_compl hY).inter_open_nonempty O hO hne
  have hO' : IsOpen (O ∩ π ⁻¹' Yᶜ) :=
    hO.inter (hY.isClosed.isOpen_compl.preimage h.contMDiff.continuous)
  -- `π` is a local homeomorphism at `p`, so `π(O ∖ π⁻¹(Y))` is a neighbourhood of `π p`
  have hnhds : π '' (O ∩ π ⁻¹' Yᶜ) ∈ 𝓝 (π p) := by
    rw [← h.isLocalDiffeomorphOn_compl.isLocalHomeomorphOn.map_nhds_eq hpY]
    exact image_mem_map (hO'.mem_nhds ⟨hpO, hpY⟩)
  obtain ⟨V, hVO, hV, hpV⟩ := mem_nhds_iff.mp hnhds
  obtain ⟨x, hxA, hxV⟩ := hA.exists_mem_open hV ⟨_, hpV⟩
  obtain ⟨q, ⟨hqO, hqY⟩, rfl⟩ := hVO hxV
  exact ⟨q, hqO, fun hq => hq.elim hxA hqY⟩

end Manifold

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-! ### The images of the centres -/

/-- The images in `U_0` of the first `j` centres under the composite blow-downs,
`⋃_{k<j} σ^k(C_k)`. -/
def centerImagesLT (j : ℕ) : Set M :=
  ⋃ k : Fin S.length, ⋃ (_ : k.1 < j), S.stageMap k.castSucc '' (S.center k).support

/-- The images in `U_0` of all the centres, `Z = ⋃_k σ^k(C_k)`: the set over which the succession
blows up (off it the composite blow-down is an analytic isomorphism, [Kol07, Theorem 35 (3)]). -/
def centerImages : Set M := S.centerImagesLT S.length

theorem centerImagesLT_zero : S.centerImagesLT 0 = ∅ := by
  simp [centerImagesLT]

/-- The images of the first `j + 1` centres: those of the first `j` and the image of `C_j`. -/
theorem centerImagesLT_succ {j : ℕ} (hj : j < S.length) :
    S.centerImagesLT (j + 1) =
      S.centerImagesLT j ∪ S.stageMap (Fin.castSucc ⟨j, hj⟩) '' (S.center ⟨j, hj⟩).support := by
  ext x
  simp only [centerImagesLT, mem_iUnion, mem_union, exists_prop, Nat.lt_succ_iff_lt_or_eq]
  constructor
  · rintro ⟨k, hk | hk, hx⟩
    · exact Or.inl ⟨k, hk, hx⟩
    · obtain rfl : k = ⟨j, hj⟩ := Fin.ext hk
      exact Or.inr hx
  · rintro (⟨k, hk, hx⟩ | hx)
    · exact ⟨k, Or.inl hk, hx⟩
    · exact ⟨⟨j, hj⟩, Or.inr rfl, hx⟩

/-- The image of every centre lies in `centerImages`. -/
theorem image_stageMap_center_subset_centerImages (k : Fin S.length) :
    S.stageMap k.castSucc '' (S.center k).support ⊆ S.centerImages :=
  fun _ hx => mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨k.2, hx⟩⟩

/-! ### Density of the preimage of the complement -/

/-- Along the partial composites `σ^j : U_j → U_0`, by induction on `j`: `σ^j` is injective over
the complement of the images `Z_{<j} = ⋃_{k<j} σ^k(C_k)` of the earlier centres, and the preimage
`(σ^j)⁻¹(U_0 ∖ Z_{<j})` is dense in `U_j`. At the step, a point of `U_j` over `σ^j(C_j)` but not
over `Z_{<j}` lies in `C_j` (by the injectivity), so `(σ^{j+1})⁻¹(Z_{<j+1})` is the preimage under
`σ_{j+1}` of `(σ^j)⁻¹(Z_{<j}) ∪ C_j`, whose complement is dense by the blow-up step
(`IsBlowUp.dense_compl_preimage_union`); the injectivity of `σ^{j+1}` off it composes that of
`σ_{j+1}` off `C_j` (condition (1) of [BM88, Definition 4.1]) with that of `σ^j` off `Z_{<j}`. -/
theorem injOn_and_dense_stageMapAux :
    ∀ (j : ℕ) (hj : j < S.length + 1),
      Set.InjOn (S.stageMapAux j hj) (S.stageMapAux j hj ⁻¹' (S.centerImagesLT j)ᶜ) ∧
        Dense (S.stageMapAux j hj ⁻¹' (S.centerImagesLT j)ᶜ)
  | 0, _ => by
    rw [centerImagesLT_zero, compl_empty, preimage_univ]
    exact ⟨fun _ _ _ _ h => h, dense_univ⟩
  | j + 1, hj => by
    obtain ⟨ihinj, ihd⟩ := injOn_and_dense_stageMapAux j (Nat.lt_of_succ_lt hj)
    have hjl : j < S.length := Nat.lt_of_succ_lt_succ hj
    have hb := S.isBlowUp_map ⟨j, hjl⟩
    have hY := S.isClosedSubmanifold_center ⟨j, hjl⟩
    have hcast : S.stageMap (Fin.castSucc ⟨j, hjl⟩) = S.stageMapAux j (Nat.lt_of_succ_lt hj) :=
      rfl
    rw [S.centerImagesLT_succ hjl, hcast]
    -- a point of `U_j` over the image of `C_j` but not over `Z_{<j}` lies in `C_j`
    have hkey : S.stageMapAux j (Nat.lt_of_succ_lt hj) ⁻¹'
          (S.centerImagesLT j ∪
            S.stageMapAux j (Nat.lt_of_succ_lt hj) '' (S.center ⟨j, hjl⟩).support) =
        S.stageMapAux j (Nat.lt_of_succ_lt hj) ⁻¹' S.centerImagesLT j ∪
          (S.center ⟨j, hjl⟩).support := by
      ext p
      constructor
      · rintro (hp | ⟨q, hq, hqp⟩)
        · exact Or.inl hp
        · by_cases hpZ : S.stageMapAux j (Nat.lt_of_succ_lt hj) p ∈ S.centerImagesLT j
          · exact Or.inl hpZ
          · have hqZ : S.stageMapAux j (Nat.lt_of_succ_lt hj) q ∉ S.centerImagesLT j := by
              rw [hqp]
              exact hpZ
            rw [← ihinj hqZ hpZ hqp]
            exact Or.inr hq
      · rintro (hp | hp)
        · exact Or.inl hp
        · exact Or.inr ⟨p, hp, rfl⟩
    refine ⟨?_, ?_⟩
    · -- injectivity: `σ^{j+1} = σ^j ∘ σ_{j+1}`, off `C_j` and off `(σ^j)⁻¹(Z_{<j})`
      intro p hp q hq hpq
      have hp' : S.map ⟨j, hjl⟩ p ∈ (S.stageMapAux j (Nat.lt_of_succ_lt hj) ⁻¹'
          S.centerImagesLT j ∪ (S.center ⟨j, hjl⟩).support)ᶜ := by
        rw [← hkey]
        exact hp
      have hq' : S.map ⟨j, hjl⟩ q ∈ (S.stageMapAux j (Nat.lt_of_succ_lt hj) ⁻¹'
          S.centerImagesLT j ∪ (S.center ⟨j, hjl⟩).support)ᶜ := by
        rw [← hkey]
        exact hq
      rw [compl_union] at hp' hq'
      exact hb.bijOn_compl.injOn hp'.2 hq'.2 (ihinj hp'.1 hq'.1 hpq)
    · -- density: the blow-up step for `σ_{j+1}` with `A = (σ^j)⁻¹(Z_{<j})`
      have hd := hb.dense_compl_preimage_union hY
        (A := S.stageMapAux j (Nat.lt_of_succ_lt hj) ⁻¹' S.centerImagesLT j)
        (by rw [← preimage_compl]; exact ihd)
      rw [← hkey] at hd
      rw [preimage_compl]
      exact hd

/-- The preimage under the composite blow-down `σ^r : U_r → U_0` of the complement of the images
of the centres is dense in `U_r`. -/
theorem dense_preimage_compl_centerImages : Dense (S.composite ⁻¹' (S.centerImages)ᶜ) :=
  (S.injOn_and_dense_stageMapAux S.length (Nat.lt_succ_self _)).2

end AnalyticManifold.FiniteSuccession

end
