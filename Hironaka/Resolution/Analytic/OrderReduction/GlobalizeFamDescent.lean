/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.GlobalizeFamCover
import Hironaka.Manifold.FiniteSuccession.Functor.Descent
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.FibreProduct
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Resolution.Analytic.Functor.FibreProductRestrict
import Hironaka.Resolution.Analytic.OrderReduction.GlobalizeCover
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Step 3 of Theorem 103 in the compatible-family form: the descent along the cover

The descent of Step 3 of the proof of [Kol07, Theorem 103] follows [Kol07, Proposition 37], as
axiomatized in [Kol07, Theorem 105]: on the fibre product `X'' := X' ×_X X'` of the cover
`g : X' → X` with itself, `τ₁^* B(X') = B(X'') = τ₂^* B(X')` (the first centres in (37.1) and
(105.4)), so `B(X')` descends to a unique
blow-up sequence `B̄(X)` with `g^* B̄(X) = B(X')`. In the compatible-family form the cover is the
finite cover `k : ⊔ᵢ ιᵢ^{-1}(Wᵢ ∩ U) → U` of a relatively compact open `U` by pieces with maximal
contact (`ShrunkMCCover`, `GlobalizeFamCover.lean`), and `B(X')` is the value of the family functor
on the open `⊔ᵢ ιᵢ^{-1}(Wᵢ ∩ U)` of the coproduct. The saturation is checked on the fibre product of
the coproduct of the whole pieces with itself: the pulled-back triple there has a global
hypersurface of maximal contact, the open `q₁^{-1}(O) ∩ q₂^{-1}(O)` is relatively compact, and the
commutation of the family functor with the two projections identifies both pull-backs of the value
with its value there (`ShrunkMCCover.exists_unique_descent`).

The same fibre-product argument, run for a triple of the local class over an arbitrary local
analytic isomorphism `e₁` against a cover `(e₂, O₂, L₂)`, is the **comparison lemma**
`CommutesWithLocalIsos.seqOn_eq_eraseEmpty_pullback_of_descent`: the family's value on `O₁` is the
pull-back of the descended sequence `L₂` along `e₁|_{O₁}`, with empty blow-ups deleted. From it
`GlobalizeFam.lean` derives the compatibility of the descended values under restriction, their
independence of the cover, the agreement with the family on the local class and the commutation of
the descended functor with local analytic isomorphisms.

* `CommutesWithLocalIsos.seqOn_eq_eraseEmpty_pullback_of_descent` — the comparison lemma;
* `ShrunkMCCover.coverList` — Kollár's `B(X')`, the value on the cover;
* `ShrunkMCCover.exists_unique_descent`, `descent`, `pullback_descent`, `descent_unique`,
  `noEmptyCenters_descent` — Kollár's `B̄(X)` over `U`, the unique sequence on `U` pulling back to
  the value on the cover.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace Function
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.AnalyticFamilyFunctor

open _root_.Manifold
open AnalyticManifold.BlowUpSequence

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

variable {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
  {B : AnalyticFamilyFunctor ψ₀ Dom}

/-- **The comparison lemma** (the argument of [Kol07, Proposition 37] in the compatible-family
form, with [Wlo09, Definition 3.2.6] for the deletion of empty blow-ups). Let `T₁` on `N₁` carry the
pull-back of `T₀` along a local analytic isomorphism `e₁`, and `T₂` on `N₂` the pull-back along a
coproduct of open embeddings `e₂`; let `O₁ ⊆ N₁`, `O₂ ⊆ N₂` be relatively compact opens with
`e₂(O₂) = V` and `e₁(O₁) ⊆ V`; and let `L₂` be a sequence on `V` which pulls back along `e₂|_{O₂}`
to the family's value on `O₂`. Then the family's value on `O₁` is the pull-back of `L₂` along
`e₁|_{O₁}` with the empty blow-ups deleted. On the fibre product of `e₁` and `e₂` over `M₀`, the
open `O := O₁ ×_V O₂` is relatively compact and maps onto `O₁`; the family's commutation with the
first projection gives the value on `O` as the pull-back of the value on `O₁`, its commutation with
the second projection and its compatibility on `N₂` give it as the pull-back of `L₂` along the
composite through `O₂`; the two composites to `V` agree, and pull-back along the surjective first
projection is injective. -/
theorem CommutesWithLocalIsos.seqOn_eq_eraseEmpty_pullback_of_descent
    (hB : B.CommutesWithLocalIsos)
    (hpull : ∀ {M N : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ M) (g : AnalyticMap N M)
      (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g), Dom T' → Dom (T'.pullback g hg))
    {M₀ N₁ N₂ : AnalyticManifold.{u} 𝕜 E} {T₀ : AnalyticTriple ψ₀ M₀}
    {T₁ : AnalyticTriple ψ₀ N₁} {e₁ : AnalyticMap N₁ M₀}
    (he₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω e₁) (hT₁ : Dom T₁) (hT₁e : T₁.IsPullbackOf T₀ e₁)
    {T₂ : AnalyticTriple ψ₀ N₂} {e₂ : AnalyticMap N₂ M₀} (he₂ : IsCoprodOfOpenEmbeddings e₂)
    (hT₂ : Dom T₂) (hT₂e : T₂.IsPullbackOf T₀ e₂)
    {O₁ : Opens N₁} (hO₁ : IsCompact (closure (O₁ : Set N₁)))
    {O₂ : Opens N₂} (hO₂ : IsCompact (closure (O₂ : Set N₂)))
    {V : Opens M₀} (himg₂ : ⇑e₂ '' (O₂ : Set N₂) = (V : Set M₀))
    (himg₁ : ⇑e₁ '' (O₁ : Set N₁) ⊆ V) (L₂ : AnalyticManifold.BlowUpSequence ψ₀ (M₀.restrict V))
    (hL₂ : L₂.pullback (AnalyticMap.restrictMap e₂ O₂ V himg₂.le)
      (AnalyticMap.isLocalDiffeomorph_restrictMap he₂.1 O₂ V himg₂.le) =
        (B.fam T₂ hT₂).seqOn O₂ hO₂) :
    (B.fam T₁ hT₁).seqOn O₁ hO₁ =
      (L₂.pullback (AnalyticMap.restrictMap e₁ O₁ V himg₁)
        (AnalyticMap.isLocalDiffeomorph_restrictMap he₁ O₁ V himg₁)).eraseEmpty := by
  obtain ⟨R, r₁, r₂, hr⟩ := exists_isFibreProduct_of_isLocalDiffeomorph e₁ e₂ he₁ he₂
  have hTR : Dom (T₁.pullback r₁ hr.1) := hpull T₁ r₁ hr.1 hT₁
  have hTR₂ : (T₁.pullback r₁ hr.1).IsPullbackOf T₂ r₂ :=
    hr.isPullbackOf_pullback_fst_snd hT₁e hT₂e
  set O : Opens R := IsFibreProduct.restrictOpens r₁ r₂ O₁ O₂ with hOdef
  have hO : IsCompact (closure (O : Set R)) :=
    hr.isCompact_closure_restrictOpens he₂ hO₁ hO₂
  have himgO₁ : ⇑r₁ '' (O : Set R) = O₁ :=
    hr.image_fst_restrictOpens_eq (himg₁.trans himg₂.symm.le)
  set ρ₁ := AnalyticMap.restrictMap r₁ O O₁ himgO₁.le with hρ₁
  have hld₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ₁ :=
    AnalyticMap.isLocalDiffeomorph_restrictMap hr.1 O O₁ himgO₁.le
  have hsurj₁ : Function.Surjective ρ₁ := AnalyticMap.surjective_restrictMap himgO₁
  have h1 := hB.seqOn_eq_of_image_eq hr.1 (T₁.isPullbackOf_pullback r₁ hr.1) hT₁ hTR hO hO₁ himgO₁
  set O₂' : Opens N₂ := AnalyticMap.imageOpens r₂ hr.2.1 O with hO₂'def
  have hO₂' : IsCompact (closure (O₂' : Set N₂)) := AnalyticMap.isCompact_closure_image r₂ hO
  have hle : O₂' ≤ O₂ := by
    rintro _ ⟨z, hz, rfl⟩
    exact hz.2
  have h2 := hB T₂ (T₁.pullback r₁ hr.1) r₂ hr.2.1 hTR₂ hT₂ hTR O hO
  have hc := (B.fam T₂ hT₂).compat O₂' O₂ hO₂' hO₂ hle
  set L₁ := (B.fam T₁ hT₁).seqOn O₁ hO₁ with hL₁
  set ρ₂ := AnalyticMap.restrictMap r₂ O O₂' Set.Subset.rfl with hρ₂
  have hld₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ₂ :=
    AnalyticMap.isLocalDiffeomorph_restrictMap hr.2.1 O O₂' Set.Subset.rfl
  set ι := N₂.restrictLE hle with hι
  have hldι : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ι := isLocalDiffeomorph_restrictLE hle
  set ε₂ := AnalyticMap.restrictMap e₂ O₂ V himg₂.le with hε₂
  have hldε₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ε₂ :=
    AnalyticMap.isLocalDiffeomorph_restrictMap he₂.1 O₂ V himg₂.le
  set ε₁ := AnalyticMap.restrictMap e₁ O₁ V himg₁ with hε₁
  have hldε₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ε₁ :=
    AnalyticMap.isLocalDiffeomorph_restrictMap he₁ O₁ V himg₁
  have hld_ε₂ι : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (ε₂.comp ι) :=
    isLocalDiffeomorph_comp hldε₂ hldι
  have hld_ε₂ιρ₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ((ε₂.comp ι).comp ρ₂) :=
    isLocalDiffeomorph_comp hld_ε₂ι hld₂
  have hld_ε₁ρ₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (ε₁.comp ρ₁) :=
    isLocalDiffeomorph_comp hldε₁ hld₁
  have hk : (ε₂.comp ι).comp ρ₂ = ε₁.comp ρ₁ := by
    refine ContMDiffMap.ext fun z => Subtype.ext ?_
    exact (hr.2.2.1 z.1).symm
  have hL₁ne : L₁.NoEmptyCenters := (B.fam T₁ hT₁).noEmptyCenters O₁ hO₁
  have step : L₁.pullback ρ₁ hld₁ = ((L₂.pullback ε₁ hldε₁).eraseEmpty).pullback ρ₁ hld₁ :=
    calc L₁.pullback ρ₁ hld₁ = (L₁.pullback ρ₁ hld₁).eraseEmpty :=
          (eraseEmpty_pullback_of_surjective L₁ hL₁ne ρ₁ hld₁ hsurj₁).symm
      _ = (B.fam (T₁.pullback r₁ hr.1) hTR).seqOn O hO := h1.symm
      _ = (((B.fam T₂ hT₂).seqOn O₂' hO₂').pullback ρ₂ hld₂).eraseEmpty := h2
      _ = (((((B.fam T₂ hT₂).seqOn O₂ hO₂).pullback ι hldι).eraseEmpty).pullback ρ₂
            hld₂).eraseEmpty := by rw [hc]
      _ = ((((B.fam T₂ hT₂).seqOn O₂ hO₂).pullback ι hldι).pullback ρ₂ hld₂).eraseEmpty :=
          eraseEmpty_pullback_eraseEmpty _ ρ₂ hld₂
      _ = (((L₂.pullback ε₂ hldε₂).pullback ι hldι).pullback ρ₂ hld₂).eraseEmpty := by rw [hL₂]
      _ = (L₂.pullback ((ε₂.comp ι).comp ρ₂) hld_ε₂ιρ₂).eraseEmpty := by
          rw [pullback_comp L₂ ε₂ hldε₂ ι hldι, pullback_comp L₂ (ε₂.comp ι) hld_ε₂ι ρ₂ hld₂]
      _ = (L₂.pullback (ε₁.comp ρ₁) hld_ε₁ρ₁).eraseEmpty := by
          rw [pullback_congr L₂ hk hld_ε₂ιρ₂ hld_ε₁ρ₁]
      _ = ((L₂.pullback ε₁ hldε₁).pullback ρ₁ hld₁).eraseEmpty := by
          rw [pullback_comp L₂ ε₁ hldε₁ ρ₁ hld₁]
      _ = (((L₂.pullback ε₁ hldε₁).eraseEmpty).pullback ρ₁ hld₁).eraseEmpty :=
          (eraseEmpty_pullback_eraseEmpty _ ρ₁ hld₁).symm
      _ = ((L₂.pullback ε₁ hldε₁).eraseEmpty).pullback ρ₁ hld₁ :=
          eraseEmpty_pullback_of_surjective _ (noEmptyCenters_eraseEmpty _) ρ₁ hld₁ hsurj₁
  exact pullback_injective_of_surjective ρ₁ hld₁ hsurj₁ _ _ step

end Hironaka.Manifold.AnalyticFamilyFunctor

namespace Manifold

open AnalyticManifold.BlowUpSequence

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace AnalyticTriple.ShrunkMCCover

open Hironaka.Manifold

variable {M : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M} {m : ℕ} {U : Opens M}
  (C : ShrunkMCCover T m U) (B : AnalyticFamilyFunctor ψ₀ (AnalyticTriple.LocalMCClass m))

/-- Kollár's `B(X')`: the family's value on the open `⊔ᵢ ιᵢ^{-1}(Wᵢ ∩ U)` of the coproduct of the
pieces. -/
def coverList (hT : BOClass m T) : AnalyticManifold.BlowUpSequence ψ₀ (C.sigma.restrict C.opens) :=
  (B.fam C.triple (C.localMCClass_triple hT)).seqOn C.opens C.isCompact_closure_opens

/-- The value on the cover has no empty centres. -/
theorem noEmptyCenters_coverList (hT : BOClass m T) : (C.coverList B hT).NoEmptyCenters :=
  (B.fam C.triple (C.localMCClass_triple hT)).noEmptyCenters _ _

/-- The descent of [Kol07, Proposition 37] and of the proof of [Kol07, Theorem 105], in the
compatible-family form: the value on the cover descends uniquely along the cover map
`k : ⊔ᵢ ιᵢ^{-1}(Wᵢ ∩ U) → U`. On the fibre product `Q` of the coproduct of the whole pieces with
itself, the pulled-back triple has a global hypersurface of maximal contact, the open
`q₁^{-1}(O) ∩ q₂^{-1}(O)` over `O = ⊔ᵢ ιᵢ^{-1}(Wᵢ ∩ U)` is relatively compact, and the family's
commutation with the two projections gives `q₁^* B(X') = q₂^* B(X')` there, the condition under
which a sequence descends uniquely along a surjective coproduct of open embeddings
(`BlowUpSequence.exists_unique_pullback_eq_of_isFibreProduct`). -/
theorem exists_unique_descent (hT : BOClass m T) (hB : B.CommutesWithLocalIsos) :
    ∃! L : AnalyticManifold.BlowUpSequence ψ₀ (M.restrict U),
      L.pullback C.coverMap C.isLocalDiffeomorph_coverMap = C.coverList B hT := by
  have := finiteDimensional_of_chartIso ψ₀
  obtain ⟨Q, q₁, q₂, hq⟩ := exists_isFibreProduct C.desc C.desc C.isCoprodOfOpenEmbeddings_desc
    C.isCoprodOfOpenEmbeddings_desc
  have hTσ := C.localMCClass_triple hT
  have hTQ : LocalMCClass m (C.triple.pullback q₁ hq.1) :=
    localMCClass_of_isPullbackOf hTσ hq.1 (C.triple.isPullbackOf_pullback q₁ hq.1)
  have hTQ₂ : (C.triple.pullback q₁ hq.1).IsPullbackOf C.triple q₂ :=
    hq.isPullbackOf_pullback_fst_snd (T.isPullbackOf_pullback C.desc C.isLocalDiffeomorph_desc)
      (T.isPullbackOf_pullback C.desc C.isLocalDiffeomorph_desc)
  set O : Opens Q := IsFibreProduct.restrictOpens q₁ q₂ C.opens C.opens with hOdef
  have hO : IsCompact (closure (O : Set Q)) :=
    hq.isCompact_closure_restrictOpens C.isCoprodOfOpenEmbeddings_desc C.isCompact_closure_opens
      C.isCompact_closure_opens
  have himg₁ : ⇑q₁ '' (O : Set Q) = C.opens := hq.image_fst_restrictOpens_eq Set.Subset.rfl
  have himg₂ : ⇑q₂ '' (O : Set Q) = C.opens := hq.image_snd_restrictOpens_eq Set.Subset.rfl
  have h₁ := hB.seqOn_eq_of_image_eq hq.1 (C.triple.isPullbackOf_pullback q₁ hq.1) hTσ hTQ hO
    C.isCompact_closure_opens himg₁
  have h₂ := hB.seqOn_eq_of_image_eq hq.2.1 hTQ₂ hTσ hTQ hO C.isCompact_closure_opens himg₂
  have hne := C.noEmptyCenters_coverList B hT
  have e1 := eraseEmpty_pullback_of_surjective (C.coverList B hT) hne _
    (AnalyticMap.isLocalDiffeomorph_restrictMap hq.1 O C.opens himg₁.le)
    (AnalyticMap.surjective_restrictMap himg₁)
  have e2 := eraseEmpty_pullback_of_surjective (C.coverList B hT) hne _
    (AnalyticMap.isLocalDiffeomorph_restrictMap hq.2.1 O C.opens himg₂.le)
    (AnalyticMap.surjective_restrictMap himg₂)
  have hsat := e1.symm.trans (h₁.symm.trans (h₂.trans e2))
  exact exists_unique_pullback_eq_of_isFibreProduct C.coverMap
    C.isCoprodOfOpenEmbeddings_coverMap C.surjective_coverMap _ _
    (hq.isFibreProduct_restrict C.opens C.opens U C.image_opens_subset C.image_opens_subset)
    (C.coverList B hT) hsat

/-- Kollár's `B̄(X)` over `U`: the sequence on `U` pulling back to the value on the cover. -/
def descent (hT : BOClass m T) (hB : B.CommutesWithLocalIsos) : AnalyticManifold.BlowUpSequence ψ₀
    (M.restrict U) :=
  (C.exists_unique_descent B hT hB).exists.choose

/-- The descended sequence pulls back along the cover map to the value on the cover. -/
theorem pullback_descent (hT : BOClass m T) (hB : B.CommutesWithLocalIsos) :
    (C.descent B hT hB).pullback C.coverMap C.isLocalDiffeomorph_coverMap = C.coverList B hT :=
  (C.exists_unique_descent B hT hB).exists.choose_spec

/-- The descended sequence is the only sequence on `U` pulling back to the value on the cover
(pull-back along the surjective cover map is injective). -/
theorem descent_unique (hT : BOClass m T) (hB : B.CommutesWithLocalIsos)
    {L : AnalyticManifold.BlowUpSequence ψ₀ (M.restrict U)}
    (hL : L.pullback C.coverMap C.isLocalDiffeomorph_coverMap = C.coverList B hT) :
    L = C.descent B hT hB :=
  pullback_injective_of_surjective C.coverMap C.isLocalDiffeomorph_coverMap C.surjective_coverMap
    _ _ (hL.trans (C.pullback_descent B hT hB).symm)

/-- The descended sequence has no empty centres: its pull-back along the surjective cover map has
none. -/
theorem noEmptyCenters_descent (hT : BOClass m T) (hB : B.CommutesWithLocalIsos) :
    (C.descent B hT hB).NoEmptyCenters :=
  noEmptyCenters_of_pullback_of_surjective _ C.coverMap C.isLocalDiffeomorph_coverMap
    C.surjective_coverMap ((C.pullback_descent B hT hB).symm ▸ C.noEmptyCenters_coverList B hT)

end AnalyticTriple.ShrunkMCCover

end Manifold

end
