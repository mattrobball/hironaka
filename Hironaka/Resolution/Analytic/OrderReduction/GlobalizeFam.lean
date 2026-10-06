/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.GlobalizeFamDescent
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Resolution.Analytic.OrderReduction.GlobalizeCover
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Step 3 of Theorem 103 in the compatible-family form: the descended family functor

Step 3 of the proof of [Kol07, Theorem 103]: the functor defined on the triples with a global
hypersurface of maximal contact descends "as in (37)" to the whole class, and Theorem 103 (2) holds
for the descended functor. In the compatible-family form the value of the descended functor on a
triple `T` of the class `BOClass m` is, on every relatively compact open `U`, the sequence
descended from the family's value on the coproduct of a finite cover of the closure of `U` by
pieces with maximal contact (`GlobalizeFamCover.lean`, `GlobalizeFamDescent.lean`), the cover
being chosen for each `U` (`chosenCover`, `globalizeSeqOn`). Every property of the descended
functor is an instance of the comparison lemma of `GlobalizeFamDescent.lean`:

* `ShrunkMCCover.descent_eq_globalizeSeqOn` — the descent along any finite cover of the closure of
  `U` by pieces with maximal contact is the chosen one (the uniqueness in [Kol07, Proposition 37]);
* `globalizeSeqOn_compat` — the values are compatible under restriction: on `U ≤ V` the value on `U`
  is the pull-back of the value on `V` along the open inclusion with empty blow-ups deleted
  ([Wlo09, Theorem 2.0.3 (4)] with [Wlo09, Definition 3.2.6]);
* `globalizeSeqOn_eq_seqOn`, `globalizeFam_fam_eq` — on a triple with a global hypersurface of
  maximal contact the descended functor agrees with the family;
* `globalizeSeqOn_commutes`, `globalizeFam_commutesWithLocalIsos` — the descended functor commutes
  with local analytic isomorphisms (Theorem 103 (2); both clauses of [Kol07, 34.1] per open).

`AnalyticFamilyFunctor.globalizeFam B hB` is the descended family functor on `BOClass m`; the
existence statement `BO_globalizeFam` and the descent of the remaining clauses of Theorem 103 are in
`GlobalizeFamClauses.lean`; `globalizeFam_seqOn_eq_pullback` restates the cover-independence for
the pull-back along a local isomorphism (a form no other declaration depends on), and the descended
functor of the local functor of Steps 1 and 2 is `localFunctorFam` there.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace Function
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open AnalyticManifold.BlowUpSequence Manifold.AnalyticTriple

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {m : ℕ}

namespace AnalyticFamilyFunctor

open _root_.Manifold

variable (B : AnalyticFamilyFunctor ψ₀ (AnalyticTriple.LocalMCClass m))
  (hB : B.CommutesWithLocalIsos)

/-- The class `LocalMCClass m` of triples with a global hypersurface of maximal contact is closed
under pull-back along local analytic isomorphisms, stated for the pull-back triple
`T'.pullback g hg` itself, the form the comparison lemma takes; it restates
`localMCClass_of_isPullbackOf` (`GlobalizeCover.lean`), which is stated for any triple carrying the
pull-back data and carries the finite-dimensionality binder, supplied here by
`finiteDimensional_of_chartIso`. -/
theorem localMCClass_pullback' {M N : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ M)
    (g : AnalyticMap N M) (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g)
    (hT' : AnalyticTriple.LocalMCClass m T') :
    AnalyticTriple.LocalMCClass m (T'.pullback g hg) := by
  have := finiteDimensional_of_chartIso ψ₀
  exact localMCClass_of_isPullbackOf hT' hg (T'.isPullbackOf_pullback g hg)

section PerOpen

variable {M : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M} (hT : AnalyticTriple.BOClass m T)
  (U : Opens M) (hU : IsCompact (closure (U : Set M)))

/-- A finite cover of the closure of `U` by pieces with maximal contact, chosen once for each
triple and each relatively compact open `U` (`exists_shrunkMCCover`). -/
def chosenCover : ShrunkMCCover T m U := Classical.choice (exists_shrunkMCCover hT hU)

/-- Kollár's `B̄(X)` on the relatively compact open `U`: the sequence descended from the family's
value on the coproduct of the chosen cover (`ShrunkMCCover.descent`). -/
@[irreducible] def globalizeSeqOn : AnalyticManifold.BlowUpSequence ψ₀ (M.restrict U) :=
  (chosenCover hT U hU).descent B hT hB

/-- The descended value on `U` has no empty centres. -/
theorem noEmptyCenters_globalizeSeqOn : (globalizeSeqOn B hB hT U hU).NoEmptyCenters := by
  unfold globalizeSeqOn
  exact (chosenCover hT U hU).noEmptyCenters_descent B hT hB

/-- The descent along any finite cover of the closure of `U` by pieces with maximal contact is the
chosen one (the uniqueness in [Kol07, Proposition 37]): by the comparison lemma the value on the
given cover is the pull-back of the chosen descent along the given cover map, with empty blow-ups
deleted; the cover map is surjective, so nothing is deleted, and the descent along the given cover
is unique. -/
theorem ShrunkMCCover.descent_eq_globalizeSeqOn (C : ShrunkMCCover T m U) :
    C.descent B hT hB = globalizeSeqOn B hB hT U hU := by
  unfold globalizeSeqOn
  set C' := chosenCover hT U hU with hC'
  have key := hB.seqOn_eq_eraseEmpty_pullback_of_descent (localMCClass_pullback' (m := m))
    C.isLocalDiffeomorph_desc (C.localMCClass_triple hT)
    (T.isPullbackOf_pullback C.desc C.isLocalDiffeomorph_desc) C'.isCoprodOfOpenEmbeddings_desc
    (C'.localMCClass_triple hT) (T.isPullbackOf_pullback C'.desc C'.isLocalDiffeomorph_desc)
    C.isCompact_closure_opens C'.isCompact_closure_opens C'.image_opens_eq C.image_opens_subset
    (C'.descent B hT hB) (C'.pullback_descent B hT hB)
  -- key : C.coverList = ((C'.descent).pullback C.coverMap _).eraseEmpty
  have hne : (C'.descent B hT hB).NoEmptyCenters := C'.noEmptyCenters_descent B hT hB
  have e := eraseEmpty_pullback_of_surjective (C'.descent B hT hB) hne C.coverMap
    C.isLocalDiffeomorph_coverMap C.surjective_coverMap
  exact (C.descent_unique B hT hB (e.symm.trans key.symm)).symm

/-- The descended values are compatible under restriction ([Wlo09, Theorem 2.0.3 (4)] with
[Wlo09, Definition 3.2.6]): on `U ≤ V` the value on `U` is the pull-back of the value on `V` along
the open inclusion with empty blow-ups deleted. This is the comparison lemma for the chosen cover
of `U` against the chosen cover of `V`, and the uniqueness of the descent along the cover of `U`. -/
theorem globalizeSeqOn_compat {V : Opens M} (hV : IsCompact (closure (V : Set M))) (hUV : U ≤ V) :
    globalizeSeqOn B hB hT U hU =
      ((globalizeSeqOn B hB hT V hV).pullback (M.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty := by
  unfold globalizeSeqOn
  set C := chosenCover hT U hU with hC
  set C' := chosenCover hT V hV with hC'
  have himg₁ : ⇑C.desc '' (C.opens : Set C.sigma) ⊆ V := C.image_opens_subset.trans hUV
  have key := hB.seqOn_eq_eraseEmpty_pullback_of_descent (localMCClass_pullback' (m := m))
    C.isLocalDiffeomorph_desc (C.localMCClass_triple hT)
    (T.isPullbackOf_pullback C.desc C.isLocalDiffeomorph_desc) C'.isCoprodOfOpenEmbeddings_desc
    (C'.localMCClass_triple hT) (T.isPullbackOf_pullback C'.desc C'.isLocalDiffeomorph_desc)
    C.isCompact_closure_opens C'.isCompact_closure_opens C'.image_opens_eq himg₁
    (C'.descent B hT hB) (C'.pullback_descent B hT hB)
  set L := C'.descent B hT hB with hL
  have hldι : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (M.restrictLE hUV) :=
    isLocalDiffeomorph_restrictLE hUV
  have hcomp :
      AnalyticMap.restrictMap C.desc C.opens V himg₁ = (M.restrictLE hUV).comp C.coverMap :=
    ContMDiffMap.ext fun z => Subtype.ext rfl
  have hldc : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ((M.restrictLE hUV).comp C.coverMap) :=
    isLocalDiffeomorph_comp hldι C.isLocalDiffeomorph_coverMap
  set Y := ((L.pullback (M.restrictLE hUV) hldι).eraseEmpty) with hY
  have step : C.coverList B hT = Y.pullback C.coverMap C.isLocalDiffeomorph_coverMap :=
    calc C.coverList B hT
        = (L.pullback (AnalyticMap.restrictMap C.desc C.opens V himg₁)
            (AnalyticMap.isLocalDiffeomorph_restrictMap C.isLocalDiffeomorph_desc C.opens V
              himg₁)).eraseEmpty := key
      _ = (L.pullback ((M.restrictLE hUV).comp C.coverMap) hldc).eraseEmpty := by
          rw [pullback_congr L hcomp _ hldc]
      _ = ((L.pullback (M.restrictLE hUV) hldι).pullback C.coverMap
            C.isLocalDiffeomorph_coverMap).eraseEmpty := by
          rw [pullback_comp L (M.restrictLE hUV) hldι C.coverMap C.isLocalDiffeomorph_coverMap]
      _ = (Y.pullback C.coverMap C.isLocalDiffeomorph_coverMap).eraseEmpty :=
          (eraseEmpty_pullback_eraseEmpty _ C.coverMap C.isLocalDiffeomorph_coverMap).symm
      _ = Y.pullback C.coverMap C.isLocalDiffeomorph_coverMap :=
          eraseEmpty_pullback_of_surjective Y (noEmptyCenters_eraseEmpty _) C.coverMap
            C.isLocalDiffeomorph_coverMap C.surjective_coverMap
  exact (C.descent_unique B hT hB step.symm).symm

end PerOpen

/-- On a triple with a global hypersurface of maximal contact the descended value is the family's
own value: the family commutes with the coproduct map of the chosen cover, which is surjective onto
`U`, and the descent is unique. -/
theorem globalizeSeqOn_eq_seqOn {M : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M}
    (hL : AnalyticTriple.LocalMCClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    globalizeSeqOn B hB hL.1 U hU = (B.fam T hL).seqOn U hU := by
  unfold globalizeSeqOn
  set C := chosenCover hL.1 U hU with hC
  have h := hB.seqOn_eq_of_image_eq C.isLocalDiffeomorph_desc
    (T.isPullbackOf_pullback C.desc C.isLocalDiffeomorph_desc) hL (C.localMCClass_triple hL.1)
    C.isCompact_closure_opens hU C.image_opens_eq
  -- h : C.coverList = (((B.fam T hL).seqOn U hU).pullback C.coverMap _).eraseEmpty
  have e := eraseEmpty_pullback_of_surjective ((B.fam T hL).seqOn U hU)
    ((B.fam T hL).noEmptyCenters U hU) C.coverMap C.isLocalDiffeomorph_coverMap
    C.surjective_coverMap
  exact (C.descent_unique B hL.1 hB (e.symm.trans h.symm)).symm

/-- The value of the descended functor on a triple `T` of the class `BOClass m`: the compatible
family of the descended sequences over the relatively compact opens. -/
def globalizeFamily {M : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M}
    (hT : AnalyticTriple.BOClass m T) : CompatibleFamily T where
  seqOn U hU := globalizeSeqOn B hB hT U hU
  noEmptyCenters U hU := noEmptyCenters_globalizeSeqOn B hB hT U hU
  compat U _ hU hV hUV := globalizeSeqOn_compat B hB hT U hU hV hUV

theorem globalizeFamily_seqOn {M : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M}
    (hT : AnalyticTriple.BOClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (globalizeFamily B hB hT).seqOn U hU = globalizeSeqOn B hB hT U hU := rfl

/-- **Step 3 of the proof of [Kol07, Theorem 103] in the compatible-family form**: the extension to
the class `BOClass m` of a family functor `B` on the class `LocalMCClass m` of triples with a global
hypersurface of maximal contact, `B` commuting with local analytic isomorphisms. On every relatively
compact open `U` the value is descended from the value of `B` on the coproduct of a finite cover of
the closure of `U` by pieces with maximal contact ("we argue as in (37)"). -/
def globalizeFam : AnalyticFamilyFunctor ψ₀ (AnalyticTriple.BOClass m) where
  fam _ hT := globalizeFamily B hB hT

theorem globalizeFam_fam {M : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M}
    (hT : AnalyticTriple.BOClass m T) :
    (globalizeFam B hB).fam T hT = globalizeFamily B hB hT := rfl

theorem globalizeFam_seqOn {M : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M}
    (hT : AnalyticTriple.BOClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    ((globalizeFam B hB).fam T hT).seqOn U hU = globalizeSeqOn B hB hT U hU := by
  rw [globalizeFam_fam, globalizeFamily_seqOn]

/-- The descended functor agrees with `B` on the class `LocalMCClass m` (the descent along the
cover of Step 3 of the proof of [Kol07, Theorem 103] restricts to the identity on the pieces). -/
theorem globalizeFam_fam_eq {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N)
    (hL : AnalyticTriple.LocalMCClass m T) : (globalizeFam B hB).fam T hL.1 = B.fam T hL := by
  ext U hU
  rw [globalizeFam_seqOn]
  exact globalizeSeqOn_eq_seqOn B hB hL U hU

/-- Theorem 103 (2) for the descended values, both clauses of [Kol07, 34.1] per open: along a
local analytic isomorphism `g` the value on `U'` is the pull-back of the value on `g(U')` with empty
blow-ups deleted. This is the comparison lemma for the chosen cover of `U'`, composed with `g`,
against the chosen cover of `g(U')`, and the uniqueness of the descent. -/
theorem globalizeSeqOn_commutes {M N : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M}
    {T' : AnalyticTriple ψ₀ N} {g : AnalyticMap N M} (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g)
    (hT'g : T'.IsPullbackOf T g) (hT : AnalyticTriple.BOClass m T)
    (hT' : AnalyticTriple.BOClass m T') (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))) :
    globalizeSeqOn B hB hT' U' hU' =
      ((globalizeSeqOn B hB hT (AnalyticMap.imageOpens g hg U')
          (AnalyticMap.isCompact_closure_image g hU')).pullback
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
          Set.Subset.rfl)).eraseEmpty := by
  unfold globalizeSeqOn
  set C' := chosenCover hT' U' hU' with hC'
  set C := chosenCover hT (AnalyticMap.imageOpens g hg U')
    (AnalyticMap.isCompact_closure_image g hU') with hC
  have he₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (g.comp C'.desc) :=
    isLocalDiffeomorph_comp hg C'.isLocalDiffeomorph_desc
  have hT₁e : C'.triple.IsPullbackOf T (g.comp C'.desc) :=
    hT'g.comp (T'.isPullbackOf_pullback C'.desc C'.isLocalDiffeomorph_desc)
  have himg₁ : ⇑(g.comp C'.desc) '' (C'.opens : Set C'.sigma) ⊆ AnalyticMap.imageOpens g hg U' := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨C'.desc z, C'.image_opens_subset ⟨z, hz, rfl⟩, rfl⟩
  have key := hB.seqOn_eq_eraseEmpty_pullback_of_descent (localMCClass_pullback' (m := m)) he₁
    (C'.localMCClass_triple hT') hT₁e C.isCoprodOfOpenEmbeddings_desc (C.localMCClass_triple hT)
    (T.isPullbackOf_pullback C.desc C.isLocalDiffeomorph_desc) C'.isCompact_closure_opens
    C.isCompact_closure_opens C.image_opens_eq himg₁ (C.descent B hT hB)
    (C.pullback_descent B hT hB)
  set L := C.descent B hT hB with hL
  set γ := AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl with hγ
  have hldγ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω γ :=
    AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl
  have hcomp : AnalyticMap.restrictMap (g.comp C'.desc) C'.opens (AnalyticMap.imageOpens g hg U')
      himg₁ = γ.comp C'.coverMap :=
    ContMDiffMap.ext fun z => Subtype.ext rfl
  have hldc : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (γ.comp C'.coverMap) :=
    isLocalDiffeomorph_comp hldγ C'.isLocalDiffeomorph_coverMap
  set Y := (L.pullback γ hldγ).eraseEmpty with hY
  have step : C'.coverList B hT' = Y.pullback C'.coverMap C'.isLocalDiffeomorph_coverMap :=
    calc C'.coverList B hT'
        = (L.pullback (AnalyticMap.restrictMap (g.comp C'.desc) C'.opens
              (AnalyticMap.imageOpens g hg U') himg₁)
            (AnalyticMap.isLocalDiffeomorph_restrictMap he₁ C'.opens
              (AnalyticMap.imageOpens g hg U') himg₁)).eraseEmpty := key
      _ = (L.pullback (γ.comp C'.coverMap) hldc).eraseEmpty := by
          rw [pullback_congr L hcomp _ hldc]
      _ = ((L.pullback γ hldγ).pullback C'.coverMap C'.isLocalDiffeomorph_coverMap).eraseEmpty := by
          rw [pullback_comp L γ hldγ C'.coverMap C'.isLocalDiffeomorph_coverMap]
      _ = (Y.pullback C'.coverMap C'.isLocalDiffeomorph_coverMap).eraseEmpty :=
          (eraseEmpty_pullback_eraseEmpty _ C'.coverMap C'.isLocalDiffeomorph_coverMap).symm
      _ = Y.pullback C'.coverMap C'.isLocalDiffeomorph_coverMap :=
          eraseEmpty_pullback_of_surjective Y (noEmptyCenters_eraseEmpty _) C'.coverMap
            C'.isLocalDiffeomorph_coverMap C'.surjective_coverMap
  exact (C'.descent_unique B hT' hB step.symm).symm

/-- The descended functor commutes with local analytic isomorphisms ([Kol07, Theorem 103 (2)]). -/
theorem globalizeFam_commutesWithLocalIsos : (globalizeFam B hB).CommutesWithLocalIsos :=
  fun _ _ _ hg hT'g hT hT' U' hU' => globalizeSeqOn_commutes B hB hg hT'g hT hT' U' hU'

/-- Cover-independence for the pull-back along a local isomorphism (a form no other declaration
of the library depends on): along a local analytic isomorphism `g : N → M` with `T₁` the pull-back
of a triple `T` of the class and `T₁` with
a global hypersurface of maximal contact, the value of `B` on a relatively compact `U₁ ⊆ N` with
`g(U₁) = U` is the pull-back of the descended value on `U` along `g|_{U₁}`; no empty blow-up is
deleted, since `g|_{U₁}` is onto `U`. -/
theorem globalizeFam_seqOn_eq_pullback {M N : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M}
    (hT : AnalyticTriple.BOClass m T) {T₁ : AnalyticTriple ψ₀ N} {g : AnalyticMap N M}
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) (hT₁g : T₁.IsPullbackOf T g)
    (hL : AnalyticTriple.LocalMCClass m T₁) {U₁ : Opens N} (hU₁ : IsCompact (closure (U₁ : Set N)))
    {U : Opens M} (hU : IsCompact (closure (U : Set M))) (himg : ⇑g '' (U₁ : Set N) = (U : Set M)) :
    (B.fam T₁ hL).seqOn U₁ hU₁ =
      (globalizeSeqOn B hB hT U hU).pullback (AnalyticMap.restrictMap g U₁ U himg.le)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U₁ U himg.le) := by
  have h := CommutesWithLocalIsos.seqOn_eq_of_image_eq (globalizeFam_commutesWithLocalIsos B hB) hg
    hT₁g hT hL.1 hU₁ hU himg
  rw [globalizeFam_seqOn, globalizeFam_seqOn, globalizeSeqOn_eq_seqOn B hB hL U₁ hU₁] at h
  rw [h]
  exact eraseEmpty_pullback_of_surjective _ (noEmptyCenters_globalizeSeqOn B hB hT U hU) _ _
    (AnalyticMap.surjective_restrictMap himg)

end AnalyticFamilyFunctor

end Hironaka.Manifold

end
