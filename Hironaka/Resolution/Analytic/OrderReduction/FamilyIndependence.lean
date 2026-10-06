/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Step22Fam
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackCover
public import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.IdealSheaf.DerivLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.IdealSheaf.TuningLemmas
import Hironaka.Resolution.Analytic.Functor.LocalIsoTools
import Hironaka.Resolution.Analytic.MaximalContact.Covering
import Hironaka.Resolution.Analytic.MaximalContact.StalkEquiv
import Hironaka.Resolution.Analytic.MaximalContact.Theorem97Star
import Hironaka.Resolution.Analytic.MaximalContactTheorem
import Hironaka.Resolution.Analytic.OrderReduction.ClassPullback
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.OrderReduction.LocalFunctorComm
import Hironaka.Resolution.Analytic.OrderReduction.Step22FamFunctoriality
import Hironaka.Resolution.Analytic.OrderReduction.Step22FamPersist
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The independence from the hypersurface of maximal contact, in the compatible-family form

Step 2.3 of the proof of Theorem 103 ([Kol07, 104]): for two hypersurfaces of maximal contact `H`,
`H'`, Theorem 92 makes `(X, I, H + E)` and `(X, I, H' + E)` étale equivalent, hence so are the two
blow-up sequences, and Theorem 97 makes them identical. A family functor has values only on
relatively compact opens, and the pair `ψ, ψ' : U ⇉ X` of local analytic isomorphisms given by the
analytic form of [Kol07, Theorem 92] lives on a countable disjoint union `U`, which is not
relatively compact; the argument is therefore run as follows
(`AnalyticFamilyFunctor.seqOn_eq_of_maximalContact`).

Theorem 92 (`maximalContact_locallyIsoEquivalent`) is applied to the triple restricted to the
reading open `O`; MC-invariance and the maximal-contact inequalities restrict along the inclusion.
On every member `V_k` of an exhaustion of `U` by relatively compact opens, the family's commutation
with the local analytic isomorphisms `incl_O ∘ ψ` and `incl_O ∘ ψ'`
(`seqOn_pullback_eq_of_image_subset`), applied to the two pulled-back triples, which coincide, shows
that the restrictions to `V_k` of the pulled-back sequences `ψ^* L` and `ψ'^* L'` agree once empty
blow-ups are deleted. The sequences `ψ^* L`, `ψ'^* L'` have no empty centres, because every centre
lies over `cosupp(𝓘, m) ⊆ ψ(U)`, and for `k` large their restrictions to `V_k` have none either, a
finite sequence of nonempty centres meeting every large member of the exhaustion
(`BlowUpSequence.exists_noEmptyCenters_pullback_of_cover`); so the deletions are identities and the
sequences agree on an increasing open cover, hence `ψ^* L = ψ'^* L'`
(`BlowUpSequence.eq_of_eraseEmpty_pullback_eq`, from `eq_of_pullback_openCover`; the functoriality
package is local, [Kol07, 34]). This is clause (3) of [Kol07, Definition 96]; the analytic form of
[Kol07, Theorem 97] (`BlowUpSequence.eq_of_locallyIsoEquivalentSequences`) then gives `L = L'`.

* `IdealSheaf.isMCInvariant_comap` — MC-invariance ([Kol07, 53]) is kept by pull-back
  along a local analytic isomorphism, the derivative ideal sheaves pulling back
  ([Kol07, Lemma 74 (4)]);
* `HypersurfaceFamily.comap_append_preimage`, `HypersurfaceFamily.comap_comp_map` — the inverse
  image of `E + H` is `h^{-1}(E) + h^{-1}(H)`, and inverse images compose;
* `BlowUpSequence.range_liftStep`, `BlowUpSequence.exists_noEmptyCenters_pullback_of_cover`,
  `BlowUpSequence.eq_of_eraseEmpty_pullback_eq` — the argument on the exhaustion;
* `CommutesWithLocalIsos.seqOn_pullback_eq_of_image_subset`, `fam_seqOn_congr_triple`,
  `AnalyticTriple.pullback_eq_of_locallyIsoEquivalentMC`,
  `CommutesWithLocalIsos.eraseEmpty_pullback_inclusion_eq` — the family's values under the pair;
* `AnalyticFamilyFunctor.seqOn_eq_of_maximalContact` — Step 2.3 per relatively compact open, for a
  family functor commuting with local analytic isomorphisms whose values are of order `≥ m`, on a
  class closed under pull-back;
* `BO.stepHClass_of_isPullbackOf`, `BO.maximalContact_persistsFam_tuned`, `BO.hfStep22FamOn_indep`,
  `hfStep2SeqFamOn_indep` — the application to Step 2.2 (`Step22Fam.lean`): the value of Step 2 on
  an open does not depend on the hypersurface of maximal contact, since Step 2.1 does not mention it
  and the value of Step 2.2 is that of Lemma 102's family at the greatest member on the tuned triple
  of Step 2.2, which is MC-invariant of order `≤ s`, with the transforms of `H` and `H'` as
  hypersurfaces of maximal contact for it.

The statements about Step 2 are given in the general form `hf…` over the data `HFData ψ₀ s` of
Step 2 (`HFamData.lean`) and as the instance for Lemma 102's data. This independence is what lets
the local functor commute with local analytic isomorphisms (`LocalFunctorFam.lean`).
-/

@[expose] public section

universe u

open Set Topology TopologicalSpace IsLocalRing
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

/-! ### MC-invariance restricts along local analytic isomorphisms -/

/-- MC-invariance ([Kol07, 53]) is kept by pull-back along a local analytic isomorphism:
`h^*(MC(J) · D(J)) = MC(h^* J) · D(h^* J) ≤ h^* J`, the derivative ideal sheaves pulling back
([Kol07, Lemma 74 (4)]). Not in the sources; needed because Theorem 92 is applied here to the
triple restricted to an open. -/
theorem _root_.Manifold.IdealSheaf.isMCInvariant_comap {J : AnalyticManifold.IdealSheaf M} {m : ℕ}
    (hJ : J.IsMCInvariant m) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) :
    (J.pullback h h.contMDiff).IsMCInvariant m := by
  have h1 := comap_iteratedDeriv h hh J (0 + 1)
  rw [IdealSheaf.iteratedDeriv_succ, IdealSheaf.iteratedDeriv_succ, IdealSheaf.iteratedDeriv_zero,
    IdealSheaf.iteratedDeriv_zero] at h1
  unfold IdealSheaf.IsMCInvariant
  rw [← comap_iteratedDeriv h hh J (m - 1), ← h1,
    ← IdealSheaf.pullback_mul (φ := ⇑h) (hφ := h.contMDiff)]
  exact IdealSheaf.pullback_mono (φ := ⇑h) (hφ := h.contMDiff) hJ

/-! ### Two equations for hypersurface families -/

omit [FiniteDimensional 𝕜 E] in
/-- The inverse image of `E + H` is `h^{-1}(E) + h^{-1}(H)` (componentwise, the ordered index set
kept). -/
theorem _root_.Manifold.HypersurfaceFamily.comap_append_preimage {M N : Type u} (h : N → M)
    (F : HypersurfaceFamily M) (H : Set M) :
    (F.append H).comap h = (F.comap h).append (h ⁻¹' H) := by
  unfold HypersurfaceFamily.comap HypersurfaceFamily.append
  congr 1
  funext j
  rcases j with k | u <;> rfl

omit [FiniteDimensional 𝕜 E] in
/-- The inverse image along a composite is the iterated inverse image. -/
theorem _root_.Manifold.HypersurfaceFamily.comap_comp_map {P : AnalyticManifold.{u} 𝕜 E}
    (h : AnalyticMap N M)
    (k : AnalyticMap P N) (F : HypersurfaceFamily M) :
    F.comap (h.comp k) = (F.comap h).comap k := rfl

/-! ### Eventually no empty centres along an increasing cover -/

omit [FiniteDimensional 𝕜 E] in
/-- The range of the lift of a map to a blowing-up is the preimage of the range of the map under the
blow-down. -/
theorem _root_.AnalyticManifold.BlowUpSequence.range_liftStep (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) :
    Set.range (AnalyticManifold.BlowUpSequence.liftStep h hh hY) = ⇑(Manifold.blowUpπ ψ₀ hY) ⁻¹'
        Set.range h := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨_, (AnalyticManifold.BlowUpSequence.blowUpπ_liftStep h hh hY q).symm⟩
  · rintro ⟨b, hb⟩
    obtain ⟨q, hq⟩ := AnalyticManifold.BlowUpSequence.exists_liftStep_eq h hh hY p hb
    exact ⟨q, hq⟩

omit [FiniteDimensional 𝕜 E] in
/-- A finite sequence of centres with no empty centres, pulled back along an increasing family of
local analytic isomorphisms whose ranges cover the manifold, has no empty centres from some index
on: each of its finitely many nonempty centres meets the range of every large member. By recursion
on the sequence, the family lifted along the first blow-up (`range_liftStep`). Not in the sources;
the finiteness of a blow-up sequence ([Kol07, Definition 29]) is what is used. -/
theorem _root_.AnalyticManifold.BlowUpSequence.exists_noEmptyCenters_pullback_of_cover :
    ∀ {M : AnalyticManifold.{u} 𝕜 E} (A : AnalyticManifold.BlowUpSequence ψ₀ M), A.NoEmptyCenters →
    ∀ {Nk : ℕ → AnalyticManifold.{u} 𝕜 E} (ι : ∀ k, AnalyticMap (Nk k) M)
      (hι : ∀ k, IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (ι k)),
      (∀ k, Set.range (ι k) ⊆ Set.range (ι (k + 1))) → (∀ x, ∃ k, x ∈ Set.range (ι k)) →
      ∃ k₀, ∀ k, k₀ ≤ k → (A.pullback (ι k) (hι k)).NoEmptyCenters
  | _, AnalyticManifold.BlowUpSequence.nil _, _, _, _, _, _, _ => ⟨0, fun _ _ =>
      AnalyticManifold.BlowUpSequence.noEmptyCenters_nil⟩
  | _, @AnalyticManifold.BlowUpSequence.cons _ _ _ _ _ _ _ _ Y c hY rest, hA, _, ι, hι, hmono,
      hcov => by
    obtain ⟨hne, hrest⟩ := (AnalyticManifold.BlowUpSequence.noEmptyCenters_cons_iff hY rest).mp hA
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨k₁, hk₁⟩ := hcov y
    have hmono' : ∀ k, Set.range (AnalyticManifold.BlowUpSequence.liftStep (ι k) (hι k) hY) ⊆
        Set.range (AnalyticManifold.BlowUpSequence.liftStep (ι (k + 1)) (hι (k + 1)) hY) := by
      intro k
      rw [AnalyticManifold.BlowUpSequence.range_liftStep,
          AnalyticManifold.BlowUpSequence.range_liftStep]
      exact Set.preimage_mono (hmono k)
    have hcov' : ∀ p, ∃ k, p ∈ Set.range (AnalyticManifold.BlowUpSequence.liftStep (ι k)
        (hι k) hY) := by
      intro p
      obtain ⟨k, hk⟩ := hcov (Manifold.blowUpπ ψ₀ hY p)
      exact ⟨k, by rw [AnalyticManifold.BlowUpSequence.range_liftStep]; exact hk⟩
    obtain ⟨k₂, hk₂⟩ := AnalyticManifold.BlowUpSequence.exists_noEmptyCenters_pullback_of_cover
        rest hrest
      (fun k => AnalyticManifold.BlowUpSequence.liftStep (ι k) (hι k) hY) (fun k =>
          AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep (ι k) (hι k) hY)
      hmono' hcov'
    refine ⟨max k₁ k₂, fun k hk => ?_⟩
    rw [AnalyticManifold.BlowUpSequence.pullback_cons,
        AnalyticManifold.BlowUpSequence.noEmptyCenters_cons_iff]
    refine ⟨?_, hk₂ k (le_of_max_le_right hk)⟩
    have hmonoK : Monotone fun k => Set.range (ι k) := monotone_nat_of_le_succ hmono
    obtain ⟨u, hu⟩ := hmonoK (le_of_max_le_left hk) hk₁
    exact Set.nonempty_iff_ne_empty.mp ⟨u, show ι k u ∈ Y by rw [hu]; exact hy⟩

omit [FiniteDimensional 𝕜 E] in
/-- Two sequences with no empty centres whose pull-backs along an increasing cover by analytic open
embeddings agree once empty blow-ups are deleted are equal: from some index on nothing is deleted
(`exists_noEmptyCenters_pullback_of_cover`), and a sequence is determined by its pull-backs along
an open cover (`eq_of_pullback_openCover`; the functoriality package is local, [Kol07, 34]). -/
theorem _root_.AnalyticManifold.BlowUpSequence.eq_of_eraseEmpty_pullback_eq
    {A A' : AnalyticManifold.BlowUpSequence ψ₀ M} (hA : A.NoEmptyCenters)
    (hA' : A'.NoEmptyCenters) {Nk : ℕ → AnalyticManifold.{u} 𝕜 E} (ι : ∀ k, AnalyticMap (Nk k) M)
    (hι : ∀ k, IsAnalyticOpenEmbedding (ι k))
    (hmono : ∀ k, Set.range (ι k) ⊆ Set.range (ι (k + 1)))
    (hcov : ∀ x, ∃ k, x ∈ Set.range (ι k))
    (h : ∀ k, (A.pullback (ι k) (hι k).1).eraseEmpty = (A'.pullback (ι k) (hι k).1).eraseEmpty) :
    A = A' := by
  obtain ⟨k₀, hk₀⟩ :=
    AnalyticManifold.BlowUpSequence.exists_noEmptyCenters_pullback_of_cover A hA ι (fun k =>
        (hι k).1) hmono hcov
  obtain ⟨k₀', hk₀'⟩ :=
    AnalyticManifold.BlowUpSequence.exists_noEmptyCenters_pullback_of_cover A' hA' ι (fun k =>
        (hι k).1) hmono hcov
  have hmonoK : Monotone fun k => Set.range (ι k) := monotone_nat_of_le_succ hmono
  have : Nonempty (ULift.{u} ℕ) := ⟨⟨0⟩⟩
  refine AnalyticManifold.BlowUpSequence.eq_of_pullback_openCover (σ := ULift.{u} ℕ) (fun k => ι
      (k.down + max k₀ k₀'))
    (fun k => hι _) ?_ fun k => ?_
  · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ?_
    obtain ⟨k, hk⟩ := hcov x
    exact ⟨⟨k⟩, hmonoK (Nat.le_add_right k _) hk⟩
  · have hk := h (k.down + max k₀ k₀')
    rwa [AnalyticManifold.BlowUpSequence.eraseEmpty_of_noEmptyCenters _ (hk₀ _
        ((le_max_left _ _).trans (Nat.le_add_left _ _))),
      AnalyticManifold.BlowUpSequence.eraseEmpty_of_noEmptyCenters _ (hk₀' _
          ((le_max_right _ _).trans (Nat.le_add_left _ _)))]
      at hk

/-! ### The family's value under a local isomorphism into a relatively compact open -/

namespace AnalyticFamilyFunctor

open _root_.Manifold

variable {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}

omit [FiniteDimensional 𝕜 E] in
/-- The commutation of a family functor with local analytic isomorphisms ([Kol07, 34.1] per open),
for a local analytic isomorphism `g` carrying a relatively compact open `V` into a relatively
compact open `O`: the value of the pulled-back triple on `V` is the pull-back of the value on `O`
along `g|_V : V → O` with the empty blow-ups deleted. The commutation gives it with the image `g(V)`
in place of `O`; the compatibility from `g(V)` to `O` and the merging of the two deletions
(`eraseEmpty_pullback_eraseEmpty`) finish. -/
theorem CommutesWithLocalIsos.seqOn_pullback_eq_of_image_subset
    {B : AnalyticFamilyFunctor ψ₀ Dom} (hB : B.CommutesWithLocalIsos) {T : AnalyticTriple ψ₀ M}
    {T' : AnalyticTriple ψ₀ N} {g : AnalyticMap N M} (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g)
    (hT'g : T'.IsPullbackOf T g)
    (hT : Dom T) (hT' : Dom T') {V : Opens N} (hV : IsCompact (closure (V : Set N))) {O : Opens M}
    (hO : IsCompact (closure (O : Set M))) (himg : ⇑g '' (V : Set N) ⊆ O) :
    (B.fam T' hT').seqOn V hV =
      (((B.fam T hT).seqOn O hO).pullback (AnalyticMap.restrictMap g V O himg)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg V O himg)).eraseEmpty := by
  rw [hB T T' g hg hT'g hT hT' V hV,
    (B.fam T hT).compat (AnalyticMap.imageOpens g hg V) O (AnalyticMap.isCompact_closure_image g hV)
      hO himg,
    AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
    AnalyticManifold.BlowUpSequence.pullback_comp]
  exact congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
    (AnalyticManifold.BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ => rfl) _ _)

omit [FiniteDimensional 𝕜 E] in
/-- The value of a family functor on an open depends on the triple only, not on the proof of
membership in the class. -/
theorem fam_seqOn_congr_triple (B : AnalyticFamilyFunctor ψ₀ Dom) {T₁ T₂ : AnalyticTriple ψ₀ M}
    (e : T₁ = T₂) (h₁ : Dom T₁) (h₂ : Dom T₂) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (B.fam T₁ h₁).seqOn U hU = (B.fam T₂ h₂).seqOn U hU := by
  subst e
  rfl

/-! ### Theorems 92 and 97 per relatively compact open -/

/-- The pair `ψ, ψ'` given by the analytic form of [Kol07, Theorem 92] for the restricted triple
pulls the two triples `(X, I, E + H)` and `(X, I, E + H')` back to the same triple on `U`: the
ideal sheaves agree by clause (2′) of the equivalence, the boundaries by clauses (1′) and (3′). -/
theorem _root_.Manifold.AnalyticTriple.pullback_eq_of_locallyIsoEquivalentMC
    {X : AnalyticManifold.{u} 𝕜 E} {TH TH' : AnalyticTriple ψ₀ X} (hI : TH.I = TH'.I)
    {F : HypersurfaceFamily X} {H H' : Set X} (hF : TH.F = F.append H) (hF' : TH'.F = F.append H')
    {m : ℕ} (O : Opens X)
    (e : LocallyIsoEquivalentMC (TH.I.pullback _ (X.inclusion O).contMDiff) m
      (F.comap (X.inclusion O)) (⇑(X.inclusion O) ⁻¹' H) (⇑(X.inclusion O) ⁻¹' H')) :
    TH.pullback _ (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
        (isLocalDiffeomorph_inclusion X O) e.isLocalDiffeomorph_ψ) =
      TH'.pullback _ (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
        (isLocalDiffeomorph_inclusion X O) e.isLocalDiffeomorph_ψ') := by
  refine AnalyticTriple.ext' ?_ ?_
  · change TH.I.pullback _ ((X.inclusion O).comp e.ψ).contMDiff =
      TH'.I.pullback _ ((X.inclusion O).comp e.ψ').contMDiff
    rw
        [← AnalyticManifold.IdealSheaf.pullback_comp,
            ← AnalyticManifold.IdealSheaf.pullback_comp, ← hI]
    exact e.h2
  · change TH.F.comap ((X.inclusion O).comp e.ψ) = TH'.F.comap ((X.inclusion O).comp e.ψ')
    rw [hF, hF', HypersurfaceFamily.comap_comp_map, HypersurfaceFamily.comap_comp_map,
      HypersurfaceFamily.comap_append_preimage (⇑(X.inclusion O)) F H,
      HypersurfaceFamily.comap_append_preimage (⇑(X.inclusion O)) F H']
    exact e.append_comap_eq

omit [FiniteDimensional 𝕜 E] in
/-- For two triples on `X` whose pull-backs along `incl_O ∘ ψ` and `incl_O ∘ ψ'` coincide, the
restrictions to a relatively compact open `V ⊆ U` of the pulled-back values `ψ^* L` and `ψ'^* L'`
agree once empty blow-ups are deleted: `seqOn_pullback_eq_of_image_subset` for both, on the equal
triples, with `(incl_O ∘ ψ)|_V = ψ ∘ incl_V`. -/
theorem CommutesWithLocalIsos.eraseEmpty_pullback_inclusion_eq {B : AnalyticFamilyFunctor ψ₀ Dom}
    (hB : B.CommutesWithLocalIsos) {X : AnalyticManifold.{u} 𝕜 E} {TH TH' : AnalyticTriple ψ₀ X}
    (hT : Dom TH) (hT' : Dom TH') (O : Opens X) (hO : IsCompact (closure (O : Set X)))
    {U : AnalyticManifold.{u} 𝕜 E} (ψ ψ' : AnalyticMap U (X.restrict O))
    (hψ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ψ) (hψ' : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ψ')
    (hTeq : TH.pullback _ (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
        (isLocalDiffeomorph_inclusion X O) hψ) =
      TH'.pullback _ (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
        (isLocalDiffeomorph_inclusion X O) hψ'))
    (hDψ : Dom (TH.pullback _ (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
        (isLocalDiffeomorph_inclusion X O) hψ)))
    (hDψ' : Dom (TH'.pullback _ (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
        (isLocalDiffeomorph_inclusion X O) hψ')))
    (V : Opens U) (hV : IsCompact (closure (V : Set U))) :
    ((((B.fam TH hT).seqOn O hO).pullback ψ hψ).pullback (U.inclusion V)
      (isLocalDiffeomorph_inclusion U V)).eraseEmpty =
    ((((B.fam TH' hT').seqOn O hO).pullback ψ' hψ').pullback (U.inclusion V)
      (isLocalDiffeomorph_inclusion U V)).eraseEmpty := by
  have hψc := AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
    (isLocalDiffeomorph_inclusion X O) hψ
  have hψc' := AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
    (isLocalDiffeomorph_inclusion X O) hψ'
  have himg : ⇑((X.inclusion O).comp ψ) '' (V : Set U) ⊆ (O : Set X) := by
    rintro _ ⟨u, _, rfl⟩
    exact (ψ u).2
  have himg' : ⇑((X.inclusion O).comp ψ') '' (V : Set U) ⊆ (O : Set X) := by
    rintro _ ⟨u, _, rfl⟩
    exact (ψ' u).2
  have h1 := hB.seqOn_pullback_eq_of_image_subset hψc (TH.isPullbackOf_pullback _ hψc) hT hDψ hV
    hO himg
  have h2 := hB.seqOn_pullback_eq_of_image_subset hψc' (TH'.isPullbackOf_pullback _ hψc') hT'
    hDψ' hV hO himg'
  have h12 := B.fam_seqOn_congr_triple hTeq hDψ hDψ' V hV
  have hmid := (h1.symm.trans h12).trans h2
  have hc : ((B.fam TH hT).seqOn O hO).pullback (AnalyticMap.restrictMap _ V O himg)
      (AnalyticMap.isLocalDiffeomorph_restrictMap hψc V O himg) =
      (((B.fam TH hT).seqOn O hO).pullback ψ hψ).pullback (U.inclusion V)
        (isLocalDiffeomorph_inclusion U V) :=
    (AnalyticManifold.BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ => Subtype.ext rfl) _
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hψ
          (isLocalDiffeomorph_inclusion U V))).trans
      (AnalyticManifold.BlowUpSequence.pullback_comp _ ψ hψ (U.inclusion V)
          (isLocalDiffeomorph_inclusion U V)).symm
  have hc' : ((B.fam TH' hT').seqOn O hO).pullback (AnalyticMap.restrictMap _ V O himg')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hψc' V O himg') =
      (((B.fam TH' hT').seqOn O hO).pullback ψ' hψ').pullback (U.inclusion V)
        (isLocalDiffeomorph_inclusion U V) :=
    (AnalyticManifold.BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ => Subtype.ext rfl) _
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hψ'
          (isLocalDiffeomorph_inclusion U V))).trans
      (AnalyticManifold.BlowUpSequence.pullback_comp _ ψ' hψ' (U.inclusion V)
          (isLocalDiffeomorph_inclusion U V)).symm
  exact (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty hc).symm.trans
    (hmid.trans (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty hc'))

/-- **Step 2.3 of the proof of Theorem 103 per relatively compact open** ([Kol07, 104], with the
analytic forms of [Kol07, Theorem 92] and [Kol07, Theorem 97]): for a family functor `B` commuting
with local analytic isomorphisms, whose values are of order `≥ m` for the restricted triples, on a
class closed under pull-back along local analytic isomorphisms, two triples `TH`, `TH'` with the
same MC-invariant ideal sheaf of order `≤ m` and boundaries `E + H`, `E + H'` with `H`, `H'`
hypersurfaces of maximal contact have the same value on every relatively compact open `O`.
Theorem 92 for the restricted triple on `O` gives the pair `ψ, ψ' : U ⇉ O`; the family commutes with
`incl_O ∘ ψ` and `incl_O ∘ ψ'` on every member of an exhaustion of `U`, the pulled-back triples
being equal; the pulled-back sequences have no empty centres, so `eq_of_eraseEmpty_pullback_eq`
gives `ψ^* L = ψ'^* L'`, and Theorem 97 (`eq_of_locallyIsoEquivalentSequences`) gives `L = L'`.
Stated with the equations `hI`, `hF`, `hF'` between the fields of the two triples. -/
theorem seqOn_eq_of_maximalContact (B : AnalyticFamilyFunctor ψ₀ Dom)
    (hB : B.CommutesWithLocalIsos) {m : ℕ}
    (hord : ∀ {N : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ N) (hT' : Dom T')
      (U : Opens N) (hU : IsCompact (closure (U : Set N))),
      ((B.fam T' hT').seqOn U hU).toSuccession.IsOfOrderGe
        (T'.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).I m
        (T'.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).F.idealSheaf)
    (hDom : ∀ {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
      (T' : AnalyticTriple ψ₀ N) (g : AnalyticMap N M),
      IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g → T'.IsPullbackOf T g → Dom T → Dom T')
    {X : AnalyticManifold.{u} 𝕜 E} {TH TH' : AnalyticTriple ψ₀ X} (hI : TH.I = TH'.I)
    {F : HypersurfaceFamily X} (hF₀ : F.IsSnc ψ₀) {H H' : Set X} (hF : TH.F = F.append H)
    (hF' : TH'.F = F.append H') (hm : 1 ≤ m) (hMC : TH.I.IsMCInvariant m)
    (hmax : ∀ y, TH.I.ord y ≤ (m : ℕ∞)) (hH : IsClosedSubmanifold ψ₀ H 1)
    (hH' : IsClosedSubmanifold ψ₀ H' 1) (hHmc : hH.idealSheaf ≤ TH.I.iteratedDeriv (m - 1))
    (hH'mc : hH'.idealSheaf ≤ TH'.I.iteratedDeriv (m - 1)) (hT : Dom TH) (hT' : Dom TH')
    (O : Opens X) (hO : IsCompact (closure (O : Set X))) :
    (B.fam TH hT).seqOn O hO = (B.fam TH' hT').seqOn O hO := by
  have _hfd := ‹FiniteDimensional 𝕜 E›
  have hι : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (X.inclusion O) := isLocalDiffeomorph_inclusion X O
  -- Theorem 92 for the restricted triple on `X.restrict O`
  have hHF : (F.append H).IsSnc ψ₀ := by rw [← hF]; exact TH.isSnc
  have hH'F : (F.append H').IsSnc ψ₀ := by rw [← hF']; exact TH'.isSnc
  obtain ⟨e⟩ :=
      maximalContact_locallyIsoEquivalent ψ₀ (Manifold.IdealSheaf.pullback _ (X.inclusion
          O).contMDiff
    TH.I) hm (IdealSheaf.isMCInvariant_comap hMC _ hι)
    (fun y => (IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _ (hι y)).trans_le (hmax _))
    (F.comap (X.inclusion O)) (HypersurfaceFamily.isSnc_comap hF₀ _ hι)
    (hH.preimage_of_isLocalDiffeomorph hι) (hH'.preimage_of_isLocalDiffeomorph hι)
    (TH.idealSheaf_preimage_le_iteratedDeriv_pullback _ hι hH hHmc)
    (by rw [hI]; exact TH'.idealSheaf_preimage_le_iteratedDeriv_pullback _ hι hH' hH'mc)
    (by
      rw [← HypersurfaceFamily.comap_append_preimage (⇑(X.inclusion O)) F H]
      exact HypersurfaceFamily.isSnc_comap hHF _ hι)
    (by
      rw [← HypersurfaceFamily.comap_append_preimage (⇑(X.inclusion O)) F H']
      exact HypersurfaceFamily.isSnc_comap hH'F _ hι)
  have hψ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ((X.inclusion O).comp e.ψ) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hι e.isLocalDiffeomorph_ψ
  have hψ' : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ((X.inclusion O).comp e.ψ') :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hι e.isLocalDiffeomorph_ψ'
  have hTeq := AnalyticTriple.pullback_eq_of_locallyIsoEquivalentMC hI hF hF' O e
  have hDψ : Dom (TH.pullback _ hψ) := hDom TH _ _ hψ (TH.isPullbackOf_pullback _ hψ) hT
  have hDψ' : Dom (TH'.pullback _ hψ') := hDom TH' _ _ hψ' (TH'.isPullbackOf_pullback _ hψ') hT'
  -- the values on `O` and their pull-backs to `e.U`
  have hgeL := hord TH hT O hO
  -- the order clause for `TH′`, with the ideal written as `TH.I`'s restriction (`hI`), so that
  -- no unification has to identify `TH′.I` with `TH.I`
  have hgeL' : ((B.fam TH' hT').seqOn O hO).toSuccession.IsOfOrderGe
      (TH.I.pullback _ (X.inclusion O).contMDiff) m
      (TH'.pullback (X.inclusion O) hι).F.idealSheaf := by
    have h := hord TH' hT' O hO
    change ((B.fam TH' hT').seqOn O hO).toSuccession.IsOfOrderGe
      (TH'.I.pullback _ (X.inclusion O).contMDiff) m
      (TH'.pullback (X.inclusion O) hι).F.idealSheaf at h
    rwa [← hI] at h
  have hA : (((B.fam TH hT).seqOn O hO).pullback e.ψ e.isLocalDiffeomorph_ψ).NoEmptyCenters :=
    AnalyticManifold.BlowUpSequence.noEmptyCenters_pullback_of_subset_range _ _ _
        ((B.fam TH hT).noEmptyCenters O hO)
      fun i hi hi' => AnalyticManifold.BlowUpSequence.centers_subset_range_pullbackLiftAux _ hgeL
          e.ψ
        e.isLocalDiffeomorph_ψ e.covers i hi hi'
  have hA' : (((B.fam TH' hT').seqOn O hO).pullback e.ψ' e.isLocalDiffeomorph_ψ').NoEmptyCenters :=
    AnalyticManifold.BlowUpSequence.noEmptyCenters_pullback_of_subset_range _ _ _
        ((B.fam TH' hT').noEmptyCenters O hO)
      fun i hi hi' => AnalyticManifold.BlowUpSequence.centers_subset_range_pullbackLiftAux _ hgeL'
          e.ψ'
        e.isLocalDiffeomorph_ψ' e.covers' i hi hi'
  -- the two lists on `e.U` agree: clause (3) of Definition 96
  have hAA' : ((B.fam TH hT).seqOn O hO).pullback e.ψ e.isLocalDiffeomorph_ψ =
      ((B.fam TH' hT').seqOn O hO).pullback e.ψ' e.isLocalDiffeomorph_ψ' :=
    AnalyticManifold.BlowUpSequence.eq_of_eraseEmpty_pullback_eq hA hA'
      (fun k => e.U.inclusion (relCompactOpen (exhaustion e.U) k))
      (fun k => isAnalyticOpenEmbedding_inclusion _ _)
      (fun k => by
        rw [Manifold.range_inclusion, Manifold.range_inclusion]
        exact SetLike.coe_subset_coe.mpr (relCompactOpen_le_succ _ k))
      (fun x => by
        have hx : x ∈ ⋃ k, (relCompactOpen (exhaustion e.U) k : Set e.U) := by
          rw [iUnion_relCompactOpen]
          exact Set.mem_univ x
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
        exact ⟨k, by rw [Manifold.range_inclusion]; exact hk⟩)
      (fun k => hB.eraseEmpty_pullback_inclusion_eq hT hT' O hO e.ψ e.ψ' e.isLocalDiffeomorph_ψ
        e.isLocalDiffeomorph_ψ' hTeq hDψ hDψ' _
        (isCompact_closure_relCompactOpen _ k))
  -- Definition 96 and Theorem 97
  let e' :
      LocallyIsoEquivalentSequences (TH.I.pullback _ (X.inclusion O).contMDiff) m
      ((B.fam TH hT).seqOn O hO) ((B.fam TH' hT').seqOn O hO) :=
    ⟨e.toLocalIsoPair, e.h2, e.h4, hAA'⟩
  have hW : (((B.fam TH hT).seqOn O hO).pullback e.ψ
      e.isLocalDiffeomorph_ψ).toSuccession.IsMarkedOne
      ((Manifold.IdealSheaf.pullback e.ψ e.ψ.contMDiff
        (TH.I.pullback _ (X.inclusion O).contMDiff)).iteratedDeriv (m - 1)) :=
    (AnalyticTriple.isOfOrderGe_pullback _ m _ hgeL e.ψ e.isLocalDiffeomorph_ψ).isMarkedOne hm
  exact AnalyticManifold.BlowUpSequence.eq_of_locallyIsoEquivalentSequences e' hW
    (fun i => AnalyticManifold.BlowUpSequence.centers_subset_range_pullbackLiftAux _ hgeL e.ψ
        e.isLocalDiffeomorph_ψ
      e.covers i.1 i.2 _)
    (fun i => AnalyticManifold.BlowUpSequence.centers_subset_range_pullbackLiftAux _ hgeL' e.ψ'
        e.isLocalDiffeomorph_ψ'
      e.covers' i.1 i.2 _)

end AnalyticFamilyFunctor

/-! ### Step 2.2 on an open does not see the hypersurface -/

namespace BO

open _root_.Manifold

variable {s : ℕ}

/-- The class of Step 2.2 (triples of `BOClass s` whose boundary has a greatest member,
`Step22Defs.lean`) is closed under pull-back along every local analytic isomorphism: the class
`BOClass s` is, and the index set is kept. -/
theorem stepHClass_of_isPullbackOf {T : AnalyticTriple ψ₀ M} (hT : stepHClass s T)
    {T' : AnalyticTriple ψ₀ N} {g : AnalyticMap N M} (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g)
    (hpb : T'.IsPullbackOf T g) : stepHClass s T' := by
  obtain rfl := hpb.eq (T.isPullbackOf_pullback g hg)
  exact ⟨AnalyticTriple.boClass_of_isPullbackOf hT.1 hg hpb, hT.2⟩

/-- The transform of a hypersurface of maximal contact along a sequence of order `≥ s` is a
hypersurface of maximal contact for the tuned triple of Step 2.2: it is one for the untuned triple
(`maximalContact_persistsFam`, `Step22FamPersist.lean`), and `MC(W_s(I)) = MC(I)`
([Kol07, Proposition 99 (4)]). -/
theorem maximalContact_persistsFam_tuned (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BOClass s T) (L : AnalyticManifold.BlowUpSequence ψ₀ M)
    (hge : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf) {H : Set M}
    (hH : IsClosedSubmanifold ψ₀ H 1) (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1)) :
    (isClosedSubmanifold_transformHOf T s L hT hge hH hle).idealSheaf ≤
      ((step22TripleOf T L hge (isSnc_step22BoundaryOf T s L hT hge hH hle)).tuned s
        hT.1).I.iteratedDeriv (tuningParam s - 1) := by
  rw [AnalyticTriple.tuned_I, IdealSheaf.iteratedDeriv_tuning _ _ _ hT.1
    (boClass_step22TripleOf T s L hT hge _).2.1 (one_le_tuningParam s)]
  exact maximalContact_persistsFam T hT L hge hH hle

/-- Step 2.3 of the proof of Theorem 103 ([Kol07, 104]) for Step 2.2 on an open, in the general form
over the data `HFData` of Step 2: the value of Step 2.2 does not depend on the hypersurface of
maximal contact. It is the value of the family at the greatest member on the tuned triple of Step
2.2, which is MC-invariant (`isMCInvariant_tuned`) of order `≤ s` (`ord_tuned_le`), with the
transforms of `H` and `H'` as hypersurfaces of maximal contact for it
(`maximalContact_persistsFam_tuned`), on the class of Step 2.2, closed under pull-back
(`stepHClass_of_isPullbackOf`); `seqOn_eq_of_maximalContact` applies. -/
theorem hfStep22FamOn_indep (T : AnalyticTriple ψ₀ M) (s : ℕ) (d : HFData ψ₀ s)
    (hT : AnalyticTriple.BOClass s T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    {H : Set M} (hH : IsClosedSubmanifold ψ₀ H 1) (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1))
    {H' : Set M} (hH' : IsClosedSubmanifold ψ₀ H' 1)
    (hle' : hH'.idealSheaf ≤ T.I.iteratedDeriv (s - 1)) :
    hfStep22FamOn T s d hT U hU hH hle = hfStep22FamOn T s d hT U hU hH' hle' := by
  have hTW := boClass_pullback_inclusion_of_boClass T (step2OpenW T s hT U hU) hT
  have hI₁ : ((hfStep22TripleFam T s d hT U hU hH hle).tuned s
      (stepHClass_hfStep22TripleFam T s d hT U hU hH hle).1.1).I =
      ((hfStep2FamChain T s d hT U hU).L.toSuccession.markedTransformSeq
        (T.pullback (M.inclusion (step2OpenW T s hT U hU))
          (isLocalDiffeomorph_inclusion M _)).I s (Fin.last _)).tuning s (tuningParam s) := rfl
  have hI₂ : ((hfStep22TripleFam T s d hT U hU hH' hle').tuned s
      (stepHClass_hfStep22TripleFam T s d hT U hU hH' hle').1.1).I =
      ((hfStep2FamChain T s d hT U hU).L.toSuccession.markedTransformSeq
        (T.pullback (M.inclusion (step2OpenW T s hT U hU))
          (isLocalDiffeomorph_inclusion M _)).I s (Fin.last _)).tuning s (tuningParam s) := rfl
  unfold hfStep22FamOn
  rw [hfStep22Functor_fam_seqOn, hfStep22Functor_fam_seqOn]
  exact AnalyticFamilyFunctor.seqOn_eq_of_maximalContact d.hf.hstepFunctor
    d.hf.hstepFunctor_commutesWithLocalIsos
    (fun T' hT' U' hU' => d.hf.isOfOrderGe T' hT'.1 (greatestIdx hT') U' hU')
    (fun _ _ _ hg hpb hT₀ => stepHClass_of_isPullbackOf hT₀ hg hpb)
    (hI₁.trans hI₂.symm) (isSnc_exceptionalOf _ s _ (hfStep2FamChain T s d hT U hU).hge)
    (F := exceptionalOf (hfStep2FamChain T s d hT U hU).L)
    (H := transformHOf (hfStep2FamChain T s d hT U hU).L
      (⇑(M.inclusion (step2OpenW T s hT U hU)) ⁻¹' H))
    (H' := transformHOf (hfStep2FamChain T s d hT U hU).L
      (⇑(M.inclusion (step2OpenW T s hT U hU)) ⁻¹' H'))
    rfl rfl (one_le_tuningParam s)
    (AnalyticTriple.isMCInvariant_tuned (stepHClass_hfStep22TripleFam T s d hT U hU hH hle).1)
    (AnalyticTriple.ord_tuned_le (stepHClass_hfStep22TripleFam T s d hT U hU hH hle).1)
    (isClosedSubmanifold_transformHOf _ s _ hTW (hfStep2FamChain T s d hT U hU).hge
      (hH.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion M _))
      (idealSheaf_preimage_le_iteratedDeriv_inclusion T s hH hle _))
    (isClosedSubmanifold_transformHOf _ s _ hTW (hfStep2FamChain T s d hT U hU).hge
      (hH'.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion M _))
      (idealSheaf_preimage_le_iteratedDeriv_inclusion T s hH' hle' _))
    (maximalContact_persistsFam_tuned _ hTW _ (hfStep2FamChain T s d hT U hU).hge
      (hH.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion M _))
      (idealSheaf_preimage_le_iteratedDeriv_inclusion T s hH hle _))
    (maximalContact_persistsFam_tuned _ hTW _ (hfStep2FamChain T s d hT U hU).hge
      (hH'.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion M _))
      (idealSheaf_preimage_le_iteratedDeriv_inclusion T s hH' hle' _))
    (stepHClass_tuned (stepHClass_hfStep22TripleFam T s d hT U hU hH hle))
    (stepHClass_tuned (stepHClass_hfStep22TripleFam T s d hT U hU hH' hle'))
    (hfStep2ReadOpen T s d hT U hU) (isCompact_closure_hfStep2ReadOpen T s d hT U hU)

end BO

/-- Step 2.3 of the proof of Theorem 103 ([Kol07, 104]) for Step 2 on an open, in the general form
over the data `HFData` of Step 2: the value of Step 2 does not depend on the choice of the
hypersurface of maximal contact, since Step 2.1 and the opens do not mention `H` and the value of
Step 2.2 does not depend on it (`hfStep22FamOn_indep`). -/
theorem hfStep2SeqFamOn_indep {s : ℕ} (d : HFData ψ₀ s)
    (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BOClass s T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) {H : Set M} (hH : IsClosedSubmanifold ψ₀ H 1)
    (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1)) {H' : Set M}
    (hH' : IsClosedSubmanifold ψ₀ H' 1) (hle' : hH'.idealSheaf ≤ T.I.iteratedDeriv (s - 1)) :
    BO.hfStep2SeqFamOn T s d hT U hU hH hle = BO.hfStep2SeqFamOn T s d hT U hU hH' hle' := by
  unfold BO.hfStep2SeqFamOn
  rw [BO.hfStep22FamOn_indep T s d hT U hU hH hle hH' hle']

end Hironaka.Manifold
