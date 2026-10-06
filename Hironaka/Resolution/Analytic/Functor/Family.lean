/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.LocalCover
public import Hironaka.Resolution.Analytic.OrderReduction.MarkedData
public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Compatible families of blow-up sequences and the family functors

Włodarczyk's resolution of an analytic space is a compatible family: a finite blow-up sequence
over every relatively compact open subset, the sequences over `U ⊆ V` compatible under restriction
up to empty blow-ups [Wlo09, Theorem 2.0.3, (1) and (4)], the notion of extension being
[Wlo09, Definition 3.2.6]; the vocabulary of the main theorems has the corresponding
`AnalyticManifold.ExtensionCompatibleFamily`. Accordingly the analytic order-reduction
functors have, beside their finite form on triples, a family form: the value on a triple is a
finite `CenterList` on every relatively compact open `U ⊆ M`, with no empty blow-ups
([Kol07, 32]), compatible under restriction up to empty blow-ups.

This file provides the general tool `AnalyticMap.restrictMap` (the restriction of an analytic map
to a pair of opens, with `restrictLE`, the open inclusion `U ⊆ V`, as its instance at the
identity) and its properties (image opens, compact closure of images, local isomorphism and
surjectivity of restrictions); `CompatibleFamily`; the family functor `AnalyticFamilyFunctor` with
its commutation ([Kol07, 34.1]) and indifference predicates; the records `BOanFam` and `BMOanFam`
of the order-reduction functors in family form; and the per-open bridge
`AnalyticBlowUpSequenceAssignment.toFamily` from a finite functor to a family functor.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The general restriction of an analytic map to a pair of opens -/

/-- The restriction of an analytic map
`g : N → M` to opens `U' ⊆ N`, `V ⊆ M` with `g '' U' ⊆ V`, as an analytic map
`N.restrict U' → M.restrict V`. Its instance at `g = id` is the open inclusion `restrictLE`, and it
is also the restriction `g|_{U'}` of a cover map and of a local isomorphism in the commutation
predicates of the family functors: one constructor for all three. -/
def AnalyticMap.restrictMap {N M : AnalyticManifold.{u} 𝕜 E} (g : AnalyticMap N M) (U' : Opens N)
    (V : Opens M) (h : ⇑g '' (U' : Set N) ⊆ V) : AnalyticMap (N.restrict U') (M.restrict V) :=
  ⟨fun p => ⟨g p.1, h (Set.mem_image_of_mem g p.2)⟩, fun p => by
    have hval : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω
        ((Subtype.val : M.restrict V → M) ∘
          fun q : N.restrict U' => (⟨g q.1, h (Set.mem_image_of_mem g q.2)⟩ : M.restrict V)) p :=
      (g.contMDiff.comp contMDiff_subtype_val).contMDiffAt
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (P := ContDiffWithinAtProp 𝓘(𝕜, E) 𝓘(𝕜, E) ω) _ univ p).mp hval⟩

@[simp] theorem AnalyticMap.restrictMap_apply {N M : AnalyticManifold.{u} 𝕜 E} (g : AnalyticMap N M)
    (U' : Opens N) (V : Opens M) (h : ⇑g '' (U' : Set N) ⊆ V) (p : N.restrict U') :
    M.inclusion V (AnalyticMap.restrictMap g U' V h p) = g (N.inclusion U' p) := rfl

/-- The open inclusion `M.restrict U → M.restrict V` for `U ≤ V`, the `id`-instance of
`restrictMap`. -/
def _root_.AnalyticManifold.restrictLE (M : AnalyticManifold.{u} 𝕜 E)
    {U V : Opens M}
    (hUV : U ≤ V) : AnalyticMap (M.restrict U) (M.restrict V) :=
  ⟨Opens.inclusion hUV, contMDiff_inclusion hUV⟩

theorem isLocalDiffeomorph_restrictLE {M : AnalyticManifold.{u} 𝕜 E} {U V : Opens M} (hUV : U ≤ V) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (M.restrictLE hUV) := by
  intro x
  refine IsLocalDiffeomorphAt.of_eqOn ((inclusionPartialDiffeomorph M U x).trans
      (inclusionPartialDiffeomorph M V (M.restrictLE hUV x)).symm)
      ⟨trivial, hUV x.2⟩ fun p hp => ?_
  have hpV : (M.inclusion U p) ∈ V := hp.2
  change M.restrictLE hUV p = inclusionInv M V (M.restrictLE hUV x) (M.inclusion U p)
  rw [inclusionInv_of_mem M V (M.restrictLE hUV x) hpV]
  exact Subtype.ext rfl

/-! ### The compatible family of finite blow-up sequences -/

/-- The value of an
order-reduction functor on a triple `T` — a finite `CenterList` on every relatively compact open
`U`, with no empty blow-ups, compatible under restriction `U ≤ V` up to empty blow-ups: the value
on `U` is the pull-back of the value on `V` along the inclusion with its empty centres deleted
(one-sided, `seqOn` having no empty centres). The analogue of the vocabulary's
`AnalyticManifold.ExtensionCompatibleFamily`. -/
@[ext]
structure CompatibleFamily {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) where
  /-- The finite blow-up sequence over each relatively compact open. -/
  seqOn : ∀ (U : Opens M), IsCompact (closure (U : Set M)) → AnalyticManifold.BlowUpSequence ψ₀
      (M.restrict U)
  /-- No empty centres ([Kol07, 32], per open). -/
  noEmptyCenters : ∀ (U : Opens M) (hU : IsCompact (closure (U : Set M))),
    (seqOn U hU).NoEmptyCenters
  /-- Compatibility under restriction, up to empty blow-ups ([Wlo09, Theorem 2.0.3, (4)]; [Wlo09,
  Definition 3.2.6]). -/
  compat : ∀ (U V : Opens M) (hU : IsCompact (closure (U : Set M)))
    (hV : IsCompact (closure (V : Set M))) (hUV : U ≤ V),
    seqOn U hU =
      ((seqOn V hV).pullback (M.restrictLE hUV) (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty

/-- The trivial family — the empty `CenterList` on every open — is a
`CompatibleFamily` for every triple (compatibility by `pullback_nil` and `eraseEmpty_nil`). The
value of the trivial family functor `nilFamilyFunctor`. -/
def CompatibleFamily.nil {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) :
    CompatibleFamily T where
  seqOn := fun U _ => AnalyticManifold.BlowUpSequence.nil (M.restrict U)
  noEmptyCenters := fun _ _ => AnalyticManifold.BlowUpSequence.noEmptyCenters_nil
  compat := fun _ _ _ _ hUV => by
    rw [AnalyticManifold.BlowUpSequence.pullback_nil,
        AnalyticManifold.BlowUpSequence.eraseEmpty_nil]

/-- On a manifold whose whole space is relatively compact (in particular a
compact `M`), a `CompatibleFamily` is determined by its value at `⊤` — every open lies below `⊤`, so
`compat` reads every `seqOn U hU` off `seqOn ⊤`. The finite and family layers agree there. -/
theorem CompatibleFamily.eq_of_seqOn_top {M : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M}
    {F₁ F₂ : CompatibleFamily T} (hTop : IsCompact (closure ((⊤ : Opens M) : Set M)))
    (h : F₁.seqOn ⊤ hTop = F₂.seqOn ⊤ hTop) : F₁ = F₂ := by
  ext U hU
  rw [F₁.compat U ⊤ hU hTop le_top, F₂.compat U ⊤ hU hTop le_top, h]

/-! ### More tools for `restrictMap`: the image open, its compact closure, local
diffeomorphism, surjectivity and range -/

/-- The image `g '' U'` of a relatively compact open under a local analytic
isomorphism `g`, as an open subset of the codomain (`g` is an open map,
`IsLocalDiffeomorph.isOpenMap`). The codomain open onto which `g|_{U'}` is surjective in
`CommutesWithLocalIsos`. -/
def AnalyticMap.imageOpens {N M : AnalyticManifold.{u} 𝕜 E} (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) (U' : Opens N) : Opens M :=
  ⟨⇑g '' (U' : Set N), hg.isOpenMap _ U'.isOpen⟩

/-- The closure of the image of a relatively compact open under `g` is compact —
`closure (g '' U') ⊆ g '' closure U'`, a compact (hence closed, the codomain is Hausdorff) set, and
a closed subset of a compact set is compact. Makes `g.imageOpens hg U'` a valid index of `seqOn`. -/
theorem AnalyticMap.isCompact_closure_image {N M : AnalyticManifold.{u} 𝕜 E} (g : AnalyticMap N M)
    {U' : Opens N} (hU' : IsCompact (closure (U' : Set N))) :
    IsCompact (closure (⇑g '' (U' : Set N))) :=
  (hU'.image g.contMDiff.continuous).of_isClosed_subset isClosed_closure
    (closure_minimal (Set.image_mono subset_closure)
      (hU'.image g.contMDiff.continuous).isClosed)

/-- `g|_{U'} : N.restrict U' → M.restrict V` is a local analytic isomorphism when
`g` is — it factors as `(M.inclusion V)⁻¹ ∘ g ∘ N.inclusion U'`, a composite of local
diffeomorphisms (`IsLocalDiffeomorphAt.comp`; `inclusionInv` is the local inverse of the open
inclusion on `V`). Needed to pull a family back along `g|_{U'}`. -/
theorem AnalyticMap.isLocalDiffeomorph_restrictMap {N M : AnalyticManifold.{u} 𝕜 E}
    {g : AnalyticMap N M} (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) (U' : Opens N) (V : Opens M)
    (h : ⇑g '' (U' : Set N) ⊆ V) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (AnalyticMap.restrictMap g U' V h) := by
  intro x
  have hxV : (g (N.inclusion U' x) : M) ∈ V := h (Set.mem_image_of_mem g x.2)
  have hfun : (fun p : N.restrict U' =>
      inclusionInv M V (AnalyticMap.restrictMap g U' V h x) (g (N.inclusion U' p)))
      = (AnalyticMap.restrictMap g U' V h : N.restrict U' → M.restrict V) := by
    funext p
    exact inclusionInv_of_mem M V (AnalyticMap.restrictMap g U' V h x)
      (h (Set.mem_image_of_mem g p.2))
  have hsymm : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      (inclusionInv M V (AnalyticMap.restrictMap g U' V h x)) (g (N.inclusion U' x)) :=
    IsLocalDiffeomorphAt.of_eqOn
      (inclusionPartialDiffeomorph M V (AnalyticMap.restrictMap g U' V h x)).symm hxV
      (Set.eqOn_refl _ _)
  rw [← hfun]
  exact IsLocalDiffeomorphAt.comp (hf := isLocalDiffeomorph_inclusion N U' x)
    (hg := IsLocalDiffeomorphAt.comp (hf := hg (N.inclusion U' x)) (hg := hsymm))

/-- `g|_{U'}` is surjective onto the image open (`g '' U' = V`). This is why the
two bullets of [Kol07, 34.1] collapse to one clause per open: `g|_{U'}` is always onto its image. -/
theorem AnalyticMap.surjective_restrictMap {N M : AnalyticManifold.{u} 𝕜 E} {g : AnalyticMap N M}
    {U' : Opens N} {V : Opens M} (h' : ⇑g '' (U' : Set N) = V) :
    Function.Surjective (AnalyticMap.restrictMap g U' V h'.le) := by
  rintro ⟨q, hq⟩
  have hq' : q ∈ ⇑g '' (U' : Set N) := by rw [h']; exact hq
  obtain ⟨p, hp, hpq⟩ := hq'
  exact ⟨⟨p, hp⟩, Subtype.ext hpq⟩

/-- The range of `g|_{U'}` in `M.restrict V` is the preimage of the image `g '' U'`
under the inclusion of `V`. -/
theorem AnalyticMap.range_restrictMap {N M : AnalyticManifold.{u} 𝕜 E} (g : AnalyticMap N M)
    (U' : Opens N) (V : Opens M) (h : ⇑g '' (U' : Set N) ⊆ V) :
    Set.range (AnalyticMap.restrictMap g U' V h) = Subtype.val ⁻¹' (⇑g '' (U' : Set N)) := by
  ext q
  refine ⟨?_, ?_⟩
  · rintro ⟨p, rfl⟩
    exact Set.mem_image_of_mem g p.2
  · rintro ⟨p, hp, hpq⟩
    exact ⟨⟨p, hp⟩, Subtype.ext hpq⟩

/-- The range of the open inclusion `restrictLE` in `M.restrict V` is the preimage
of `U` under the inclusion of `V`. -/
theorem range_restrictLE {M : AnalyticManifold.{u} 𝕜 E} {U V : Opens M} (hUV : U ≤ V) :
    Set.range (M.restrictLE hUV) = Subtype.val ⁻¹' (U : Set M) := by
  ext q
  refine ⟨?_, ?_⟩
  · rintro ⟨p, rfl⟩
    exact p.2
  · rintro hq
    exact ⟨⟨q.1, hq⟩, Subtype.ext rfl⟩

/-- The open inclusion `restrictLE` is an analytic open embedding (a local analytic
isomorphism that is injective) — the datum `CommutesWithOpenEmbeddings` reads in the bridge. -/
theorem isAnalyticOpenEmbedding_restrictLE {M : AnalyticManifold.{u} 𝕜 E} {U V : Opens M}
    (hUV : U ≤ V) : IsAnalyticOpenEmbedding (M.restrictLE hUV) := by
  refine ⟨isLocalDiffeomorph_restrictLE hUV, fun a b hab => ?_⟩
  have h2 := congrArg Subtype.val hab
  exact Subtype.ext h2

/-- If `g` is a coproduct of open
embeddings, so is `g|_{U'}` — the clopen decomposition of `N` pulls back to one of `N.restrict U'`,
`g` injective on each piece. -/
theorem AnalyticMap.isCoprodOfOpenEmbeddings_restrictMap {N M : AnalyticManifold.{u} 𝕜 E}
    {g : AnalyticMap N M} (hg : IsCoprodOfOpenEmbeddings g) (U' : Opens N) (V : Opens M)
    (h : ⇑g '' (U' : Set N) ⊆ V) :
    IsCoprodOfOpenEmbeddings (AnalyticMap.restrictMap g U' V h) := by
  obtain ⟨hgld, σ, W, hclopen, hdisj, hcov, hinj⟩ := hg
  refine ⟨AnalyticMap.isLocalDiffeomorph_restrictMap hgld U' V h, σ,
    fun i => ⇑(N.inclusion U') ⁻¹' W i, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hclopen i).preimage (N.inclusion U').contMDiff.continuous
  · intro i j hij
    exact Disjoint.preimage _ (hdisj hij)
  · change ⋃ i, ⇑(N.inclusion U') ⁻¹' W i = univ
    rw [← Set.preimage_iUnion, hcov, Set.preimage_univ]
  · intro i p hp q hq hpq
    have hval : ⇑g p.val = ⇑g q.val := congrArg Subtype.val hpq
    exact Subtype.ext (hinj i hp hq hval)

/-- The open inclusion `restrictLE` is the `g = id` instance of
`restrictMap` (`rfl`), so that the two constructors are interchangeable. -/
theorem restrictLE_eq_restrictMap_id {M : AnalyticManifold.{u} 𝕜 E} {U V : Opens M} (hUV : U ≤ V)
    (h : ⇑(ContMDiffMap.id : AnalyticMap M M) '' (U : Set M) ⊆ V) :
    M.restrictLE hUV = AnalyticMap.restrictMap (ContMDiffMap.id : AnalyticMap M M) U V h := rfl

/-! ### The family functor on a class and its per-open commutation predicates -/

variable (ψ₀) in
/-- A
**family order-reduction functor** on a class `Dom` — a compatible family of finite blow-up
sequences for every triple of the class. The single field is `fam`; commutation and indifference
are predicates on it, consumed by the records `BOanFam`/`BMOanFam` as
fields. -/
structure AnalyticFamilyFunctor
    (Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop) where
  /-- The compatible family assigned to each triple of the class. -/
  fam : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M), Dom T → CompatibleFamily T

namespace AnalyticFamilyFunctor

open _root_.Manifold

variable {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
  (B : AnalyticFamilyFunctor ψ₀ Dom)

/-- `B` **commutes with local analytic isomorphisms** — for a local analytic
isomorphism `g : N → M` with `T'` carrying the pull-back data of `T` (both in `Dom`) and every
relatively compact open `U' ⊆ N`, the value on `U'` is the pull-back along `g|_{U'} : U' → g(U')`
(always onto its image, so the two bullets of 34.1 unite) of the value on the relatively compact
open `g(U')`, with empty blow-ups erased. -/
def CommutesWithLocalIsos : Prop :=
  ∀ {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (T' : AnalyticTriple ψ₀ N)
    (g : AnalyticMap N M) (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g),
    T'.IsPullbackOf T g → ∀ (hT : Dom T) (hT' : Dom T') (U' : Opens N)
      (hU' : IsCompact (closure (U' : Set N))),
      (B.fam T' hT').seqOn U' hU' =
        (((B.fam T hT).seqOn (AnalyticMap.imageOpens g hg U')
              (AnalyticMap.isCompact_closure_image g hU')).pullback
            (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
            (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
              Set.Subset.rfl)).eraseEmpty

/-- Deleting empty
boundary members changes no `seqOn U hU`. -/
def IndifferentToEmptyMembers : Prop :=
  ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (F' : HypersurfaceFamily M)
    (hsnc' : F'.IsSnc ψ₀) (e : F'.ι ↪o T.F.ι),
    (∀ i, T.F.hyp (e i) = F'.hyp i) → (∀ b, b ∉ Set.range e → T.F.hyp b = ∅) →
    ∀ (hT : Dom T) (hT' : Dom (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple ψ₀ M))
      (U : Opens M) (hU : IsCompact (closure (U : Set M))),
      (B.fam T hT).seqOn U hU =
        (B.fam ⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ hT').seqOn U hU

end AnalyticFamilyFunctor

/-! ### The family records `BOanFam` / `BMOanFam` at the standard model -/

/-- **The family form of the order-reduction functor
`BO_{n,m}`** — a family functor on the class `BOClass m` at the standard model with four
clauses read per relatively compact open on the restricted triple
`T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)`. It lives in `Type (u+1)`.
The clauses of [Kol07, Theorem 103, (3)] and [Kol07, 108] are not fields. -/
structure BOanFam (𝕜 : Type) [RCLike 𝕜] (n m : ℕ) where
  /-- The family functor `BO_{n,m}` on the order-reduction class at the standard model `𝕜ⁿ`. -/
  functor : AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    (AnalyticTriple.BOClass m)
  /-- [Kol07, Definition 66] (2′)–(4′), per open: the value on `U` is a smooth blow-up
  sequence of order `≥ m` starting with the restricted `(M, 𝓘, m, E)`. -/
  isOfOrderGe : ∀ {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BOClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M))),
    ((functor.fam T hT).seqOn U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I m
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf
  /-- Theorem 103 (1) ("`max-ord I_r < m`"), pointwise per open: the marked transform at
  the last stage over `U` has order `< m` at every point. -/
  ord_lt : ∀ {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BOClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (x : ((functor.fam T hT).seqOn U hU).toSuccession.stage (Fin.last _)),
    (((functor.fam T hT).seqOn U hU).toSuccession.markedTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I m (Fin.last _)).ord x
      < (m : ℕ∞)
  /-- Theorem 103 (2): the functor commutes with local analytic isomorphisms. -/
  commutesWithLocalIsos : functor.CommutesWithLocalIsos
  /-- The functor is indifferent to empty boundary members. -/
  indifferentToEmptyMembers : functor.IndifferentToEmptyMembers

/-- **The family form of the marked
order-reduction functor `BMO_{n,m}`** — a family functor on the class `BMOClass m` (no order
bound) at the standard model with the four `BMOanData` clauses read per relatively compact open on
the restricted triple. `Type (u+1)` as the finite record. The clauses of [Kol07, Theorem 107, (3)]
and [Kol07, 108] are not fields. -/
structure BMOanFam (𝕜 : Type) [RCLike 𝕜] (n m : ℕ) where
  /-- The family functor `BMO_{n,m}` on the marked class at the standard model `𝕜ⁿ`. -/
  functor : AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    (AnalyticTriple.BMOClass m)
  /-- [Kol07, Definition 66] (2′)–(4′), per open: the value on `U` is a smooth blow-up
  sequence of order `≥ m` starting with the restricted `(M, 𝓘, m, E)`. -/
  isOfOrderGe : ∀ {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BMOClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M))),
    ((functor.fam T hT).seqOn U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I m
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf
  /-- Theorem 107 (1) ("`max-ord I_r < m`"), pointwise per open: the marked transform at
  the last stage over `U` has order `< m` at every point. -/
  ord_lt : ∀ {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BMOClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (x : ((functor.fam T hT).seqOn U hU).toSuccession.stage (Fin.last _)),
    (((functor.fam T hT).seqOn U hU).toSuccession.markedTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I m (Fin.last _)).ord x
      < (m : ℕ∞)
  /-- Theorem 107 (2): the functor commutes with local analytic isomorphisms. -/
  commutesWithLocalIsos : functor.CommutesWithLocalIsos
  /-- The functor is indifferent to empty boundary members. -/
  indifferentToEmptyMembers : functor.IndifferentToEmptyMembers

/-! ### The per-open bridge from the finite layer -/

/-- A finite blow-up-sequence functor `B` on a class closed under
restriction to opens (`hres`) that commutes with open embeddings (`hopen`) gives a **family
functor** `B.toFamily`, its value on `U` the finite value on the restricted triple. `compat` is
the open-embedding clause of [Kol07, 34.1] along the open inclusion `restrictLE`; `noEmptyCenters`
is `B.noEmptyCenters`. The finite functor thereby yields a family functor with no further proof. -/
def _root_.Manifold.AnalyticBlowUpSequenceAssignment.toFamily
    {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
    (B : AnalyticBlowUpSequenceAssignment ψ₀ Dom)
    (hres : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (U : Opens M),
      Dom T → Dom (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)))
    (hopen : B.CommutesWithOpenEmbeddings) : AnalyticFamilyFunctor ψ₀ Dom where
  fam := fun {M} T hT =>
    { seqOn := fun U _ =>
        B.seq (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) (hres T U hT)
      noEmptyCenters := fun _ _ => B.noEmptyCenters _ _
      compat := fun U V _ _ hUV => by
        have hmap : M.inclusion U = (M.inclusion V).comp (M.restrictLE hUV) := by ext p; rfl
        have hcoe : ⇑(M.inclusion U) = ⇑(M.inclusion V) ∘ ⇑(M.restrictLE hUV) := by funext p; rfl
        have hpb : (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).IsPullbackOf
            (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)) (M.restrictLE hUV) := by
          refine ⟨?_, ?_⟩
          · rw [(T.isPullbackOf_pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).1,
              (T.isPullbackOf_pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).1,
              AnalyticManifold.IdealSheaf.pullback_comp, hmap]
          · rw [(T.isPullbackOf_pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).2,
              (T.isPullbackOf_pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).2,
              HypersurfaceFamily.comap_comap, hcoe]
        exact hopen (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V))
          (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) (M.restrictLE hUV)
          (isAnalyticOpenEmbedding_restrictLE hUV) hpb (hres T V hT) (hres T U hT) }

/-! ### The intrinsic classes restrict to any open (the hypothesis `hres` of `toFamily`) -/

/-- A member's preimage under the open inclusion is nonempty only if the member is, so the global
finiteness of the nonempty members restricts to any open (no relative compactness needed — the
weaker hypothesis beside `boClass_pullback_inclusion`). -/
theorem finite_nonempty_pullback_inclusion {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (U : Opens M) (hfin : Finite {j // T.F.hyp j ≠ ∅}) :
    Finite {j // (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.hyp j ≠ ∅} := by
  have hfin' : {j | T.F.hyp j ≠ ∅}.Finite := Set.finite_coe_iff.mp hfin
  refine Set.finite_coe_iff.mpr (hfin'.subset ?_)
  intro j hj he
  exact hj (by change ⇑(M.inclusion U) ⁻¹' T.F.hyp j = ∅; rw [he, Set.preimage_empty])

/-- The intrinsic class `BOClass m` restricts to any open — the order bound
restricts (`IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt`) and the finiteness from
`finite_nonempty_pullback_inclusion` (weaker hypotheses than `boClass_pullback_inclusion`: no
relative compactness). -/
theorem boClass_pullback_inclusion_of_boClass {M : AnalyticManifold.{u} 𝕜 E}
    (T : AnalyticTriple ψ₀ M) {m : ℕ} (U : Opens M) (hT : AnalyticTriple.BOClass m T) :
    AnalyticTriple.BOClass m (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) := by
  refine ⟨hT.1, fun y => ?_, finite_nonempty_pullback_inclusion T U hT.2.2⟩
  change (T.I.pullback ⇑(M.inclusion U) (M.inclusion U).contMDiff).ord y ≤ (m : ℕ∞)
  rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ T.I
    (isLocalDiffeomorph_inclusion M U y)]
  exact hT.2.1 _

/-- The intrinsic class `BMOClass m` (no order bound) restricts to any open. -/
theorem bmoClass_pullback_inclusion_of_bmoClass {M : AnalyticManifold.{u} 𝕜 E}
    (T : AnalyticTriple ψ₀ M) {m : ℕ} (U : Opens M) (hT : AnalyticTriple.BMOClass m T) :
    AnalyticTriple.BMOClass m (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) :=
  ⟨hT.1, finite_nonempty_pullback_inclusion T U hT.2⟩

/-! ### Universes: the family records live in `Type (u+1)`,
exactly the universe of the finite record `BMOanData` (both quantify over
`AnalyticManifold.{u}`). -/

/-- The family record `BOanFam.{u}` lives in `Type (u+1)`. -/
example {𝕜 : Type} [RCLike 𝕜] (n m : ℕ) : Type (u + 1) := BOanFam 𝕜 n m

/-- The marked family record `BMOanFam.{u}` lives in `Type (u+1)`. -/
example {𝕜 : Type} [RCLike 𝕜] (n m : ℕ) : Type (u + 1) := BMOanFam 𝕜 n m

end Hironaka.Manifold

end
