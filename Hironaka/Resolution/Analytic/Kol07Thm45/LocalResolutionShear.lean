/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
public import Hironaka.Manifold.IdealSheaf.ReducedPullback
public import Hironaka.Resolution.Analytic.Kol07Thm45.ClosedSubspaceHom
import Hironaka.AnalyticSpace.LocalIso
import Hironaka.AnalyticSpace.Manifold.Chart
import Hironaka.Manifold.Exhaustion
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.FiniteSuccession.Restrict.StrictSubspaceSeqCompat
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Kol07Thm45.DimensionCast
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionPad
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceLemma39Hom
import Hironaka.Resolution.Analytic.OrderReduction.Step22Pullback
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The shear's isomorphism of padded local resolutions and the local independence of the embedding

Kollár's proof of Theorem 36 compares the local resolutions of one piece `Y ⊆ X|V` for two
embeddings `i₁ : Y → G₁ ⊆ 𝕜ⁿ`, `i₂ : Y → G₂ ⊆ 𝕜ᵐ` [Kol07, Theorem 36, proof] (Włodarczyk: the
canonical desingularization is independent of the choice of the ambient manifold,
[Wlo09, §4, (3)⇒(4)]) in three legs: pad both to dimension `n + m` (the padded resolution is the
resolution of the slice preimage — leg (α), `LocalResolutionPad.lean`), read the two paddings
against each other through Lemma 39's shear `g : W₁ → W₂` of the padded ambients (leg (β), this
file), and restrict to a smaller open where needed (leg (γ), `LocalResolutionRestrict.lean`).

## Leg (β): the shear

* `exists_padded_equivalence_hom_point`: Lemma 39 at the morphism level with its point clause —
  the shear `g` on opens `W₁ ∋ s₁(i₁ x)`, `W₂` of the padded ambients, bijective and a local
  analytic isomorphism, pulling the right-padded ideal back to the left-padded one, with the
  identification of the closed subspaces over `g` equal to the identity of the piece, and carrying
  `s₁(i₁ y)` to `s₂(i₂ y)`.
* `BEDanFamStar.exists_diffeomorph_last_of_commutes_injective`: the commutation of
  `IsEmbeddedDesing` with local analytic isomorphisms ([Kol07, 34.1]) along an INJECTIVE local
  analytic isomorphism `g : N → M`, at a relatively compact open `U'` of `N`: the last stages of the
  values on `U'` and on `g(U')` are diffeomorphic over `g` and the final strict transforms
  correspond — the same-model content of the dimension cast (`DimensionCast.lean`) without the
  cast.
* `PieceEmbedding.localResolutionToPiece_comp_homOfPullbackEq_of_shear`: the compatibility
  `Π₂ ∘ m₂ = Π₁ ∘ m₁` for any two last-stage diffeomorphisms over `ι₁` and `ι₂ ∘ g` carrying the
  final strict transforms — the body of the core, factored out.
* `PieceEmbedding.exists_isIso_localResolution_of_shear_core`: for a relatively compact open `U'`
  of the shear's source `W₁`, the commutation along the two injective local isomorphisms
  `ι₁ : W₁ ↪ A₁` and `ι₂ ∘ g : W₁ → A₂` at the SAME `U'` gives two last-stage diffeomorphisms from
  the value on `W₁|U'`, the induced morphisms of closed subspaces are isomorphisms `m₁ : Ỹ' ≅ Ỹ₁`,
  `m₂ : Ỹ' ≅ Ỹ₂` of the final strict transforms, `ψ := m₂ ∘ m₁⁻¹`; the compatibility over the
  piece reduces to `Π₂ ∘ m₂ = Π₁ ∘ m₁`, read after the isomorphism `E₁.emb` through the morphism
  identity of the shear on `W₁`, the quotient-map squares and the two squares of composites.
* `exists_isIso_localResolution_of_shear` and its strengthening
  `exists_isIso_localResolution_of_shear'` (with the point clause on the right): shrink `U'`
  around `s₁(i₁ x)` inside `ι₁⁻¹ V₁ ∩ (ι₂ ∘ g)⁻¹ V₂` (the shrinking lemma
  `exists_opens_isCompact_closure_mem_le`), then the core.

## The assembly of the three legs

`localResolution_independent_local`: for `x` over `W₁` and over `W₂`, the shear's isomorphism at
`V₁ := p₁⁻¹ W₁`, `V₂ := p₂⁻¹ W₂` gives `U₁`, `U₂`; the shrunken opens `W₁' := s₁⁻¹ U₁ ≤ W₁`,
`W₂' := s₂⁻¹ U₂ ≤ W₂` of the unpadded ambients and the open `N := (E₁ over W₁') ∩ (E₂ over W₂') ∋ x`
of the piece; the chain (γ)₁ · (α₁)⁻¹ · (β) · (α₂) · (γ)₂⁻¹ in the relation "isomorphic over `N`",
composed by `exists_restrictSet_isIso_trans`/`_symm`, with `exists_restrictSet_isIso_of_comp_eq`
turning each isomorphism over the piece into the relation over `N`. The global form is
`localResolution_independent_of_local` (`LocalResolutionIndependent.lean`).

The two small general tools `IdealSheaf.isReduced_pullback_of_isLocalDiffeomorph`
(`Hironaka/Manifold/IdealSheaf/ReducedPullback.lean`) and
`PieceEmbedding.domBEDan_ambientTriple_pullback_inclusion` put the restricted triple
`(G, 𝓘_Y, ∅)|_W` in the class `DomBEDan`.
-/

public section

noncomputable section

open TopologicalSpace Set AnalyticManifold CategoryTheory
open scoped Manifold ContDiff Topology

universe u

namespace Hironaka.Manifold

open _root_.Manifold

open AnalyticSpace.KLocallyRingedSpace

variable {𝕜 : Type} [RCLike 𝕜]

/-- **The shrinking lemma**: in a locally compact Hausdorff space a point of an open set `V` has
an open neighbourhood inside `V` with compact closure — the interior of a compact neighbourhood
inside `V` (`exists_compact_subset`). Internal. -/
theorem exists_opens_isCompact_closure_mem_le {M : Type*} [TopologicalSpace M]
    [LocallyCompactSpace M] [T2Space M] {x : M} (V : Opens M) (hx : x ∈ V) :
    ∃ U : Opens M, x ∈ U ∧ U ≤ V ∧ IsCompact (closure (U : Set M)) := by
  obtain ⟨K, hK, hxK, hKV⟩ := exists_compact_subset V.isOpen hx
  exact ⟨⟨interior K, isOpen_interior⟩, hxK, fun y hy => hKV (interior_subset hy),
    hK.of_isClosed_subset isClosed_closure (closure_minimal interior_subset hK.isClosed)⟩

/-- The commutation with local analytic isomorphisms ([Kol07, 34.1]) at an INJECTIVE local analytic
isomorphism — the same-model content of the dimension cast `exists_diffeomorph_last_of_cast`
without the cast, `g` injective instead of a diffeomorphism: for a family functor commuting with
local analytic isomorphisms, triples `T` on `M`, `T'` on `N` with `T'` the pull-back data of `T`
along `g`, and a relatively compact open `U'` of `N`, the last stages of the values on `U'` and on
`g(U')` are diffeomorphic over `g`, and the final strict transforms correspond. The argument: the
commutation puts the value on `U'` in the form `((value on g(U')).pullback (g|U')).eraseEmpty`,
`g|U' : U' → g(U')` is a bijective local isomorphism (`surjective_restrictMap`, injectivity of `g`),
and `BlowUpSequence.exists_diffeomorph_last_of_pullback_eraseEmpty` closes. -/
theorem BEDanFamStar.exists_diffeomorph_last_of_commutes_injective (bed : BEDanFamStar.{u} 𝕜)
    (hcomm : ∀ m : ℕ, (bed.fam m).CommutesWithLocalIsos) {n : ℕ}
    {M N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g) (hinj : Function.Injective g)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) N)
    (hTT' : T'.IsPullbackOf T g)
    (hT : DomBEDan 𝕜 T) (hT' : DomBEDan 𝕜 T') (U' : Opens N)
    (hU' : IsCompact (closure (U' : Set N))) :
    ∃ G : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜)
        ((((bed.fam n).fam T' hT').seqOn U' hU').stage (Fin.last _))
        ((((bed.fam n).fam T hT).seqOn (AnalyticMap.imageOpens g hg U')
          (AnalyticMap.isCompact_closure_image g hU')).stage (Fin.last _)) ω,
      (∀ p, M.inclusion (AnalyticMap.imageOpens g hg U')
          ((((bed.fam n).fam T hT).seqOn (AnalyticMap.imageOpens g hg U')
            (AnalyticMap.isCompact_closure_image g hU')).toSuccession.composite (G p)) =
        g (N.inclusion U' ((((bed.fam n).fam T' hT').seqOn U' hU').toSuccession.composite p))) ∧
      (((bed.fam n).fam T' hT').seqOn U' hU').toSuccession.strictTransformSubspaceSeq
          (T'.I.restrict U') (Fin.last _) =
        ((((bed.fam n).fam T hT).seqOn (AnalyticMap.imageOpens g hg U')
            (AnalyticMap.isCompact_closure_image g hU')).toSuccession.strictTransformSubspaceSeq
          (T.I.restrict (AnalyticMap.imageOpens g hg U')) (Fin.last _)).pullback ⇑G
          G.contMDiff := by
  have h4 := hcomm n T T' g hg hTT' hT hT' U' hU'
  generalize hL' : ((bed.fam n).fam T' hT').seqOn U' hU' = L' at h4 ⊢
  subst h4
  have hI' : T'.I = T.I.pullback ⇑g g.contMDiff := hTT'.1
  have hinj' : Function.Injective (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U')
      Set.Subset.rfl) := fun p q hpq => Subtype.ext (hinj (congrArg Subtype.val hpq))
  have hsurj : Function.Surjective (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U')
      Set.Subset.rfl) :=
    AnalyticMap.surjective_restrictMap (g := g) rfl
  have hJ' : T'.I.restrict U' = Manifold.IdealSheaf.pullback _ (AnalyticMap.restrictMap g U'
      (AnalyticMap.imageOpens g hg U') Set.Subset.rfl).contMDiff
      (T.I.restrict (AnalyticMap.imageOpens g hg U')) := by
    dsimp only
        [IdealSheaf.restrict]
    rw [IdealSheaf.pullback_pullback, hI', IdealSheaf.pullback_pullback]
    exact IdealSheaf.pullback_congr T.I _ _
      (funext fun p => (AnalyticMap.restrictMap_apply g U' _ Set.Subset.rfl p).symm)
  exact BlowUpSequence.exists_diffeomorph_last_of_pullback_eraseEmpty ⇑g _ _ _ ⟨hinj', hsurj⟩
    (fun p => AnalyticMap.restrictMap_apply _ _ _ _ p) _ _ hJ'


section Shear

variable {n m : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E₁ : PieceEmbedding 𝕜 n X V) (E₂ : PieceEmbedding 𝕜 m X V) (x : X.restrictSet V)

/-- **Lemma 39 at the morphism level, with its point clause** ([Kol07, Lemma 39]):
`exists_padded_equivalence_hom` (the shear `g` with the ideal identity and the morphism identity)
together with `embeddings_equivalent_under_automorphism_pad`'s point clause — `g` carries the
left-padded ambient points to the right-padded ones — for the SAME witnesses (the shear
`shearAmbient` of the two local lifts). Needed below: that the point `s₂(i₂ x)` lies in `V₂` is
read through `g` at `s₁(i₁ x)`. -/
theorem exists_padded_equivalence_hom_point :
    ∃ (W₁ : Opens (pieceAmbient.{u} 𝕜 (E₁.padLeft m).G))
      (W₂ : Opens (pieceAmbient.{u} 𝕜 (E₂.padRight n).G))
      (g : AnalyticMap ((pieceAmbient.{u} 𝕜 (E₁.padLeft m).G).restrict W₁)
        ((pieceAmbient.{u} 𝕜 (E₂.padRight n).G).restrict W₂)),
      (E₁.padLeft m).ambientPoint x ∈ W₁ ∧
      IsLocalDiffeomorph 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜) ω g ∧
      Function.Bijective g ∧
      (∃ hI : (E₁.padLeft m).restrictedIdeal W₁ =
          ((E₂.padRight n).restrictedIdeal W₂).pullback ⇑g g.contMDiff,
        (IdealSheaf.homOfPullbackEq ⇑g g.contMDiff hI ≫ (E₂.padRight n).restrictedIdealHom
            W₂) ≫ (E₂.padRight n).embInv =
          (E₁.padLeft m).restrictedIdealHom W₁ ≫ (E₁.padLeft m).embInv) ∧
      ∀ (y : X.restrictSet V) (hy : (E₁.padLeft m).ambientPoint y ∈ W₁),
        (g ⟨(E₁.padLeft m).ambientPoint y, hy⟩).1 = (E₂.padRight n).ambientPoint y := by
  obtain ⟨O₁, hx₁, j₂, hj₂, H₂⟩ := E₁.exists_modelLift E₂ x
  obtain ⟨O₂, hx₂, j₁, hj₁, H₁⟩ := E₂.exists_modelLift E₁ x
  have v₂ : ∀ y, E₁.modelPoint y ∈ O₁ → j₂ (E₁.modelPoint y) = E₂.modelPoint y := fun y hy =>
    funext fun k => (E₁.modelPoint_eq_of_coord_eq E₂ y _ hy k (H₂ y hy k)).symm
  have v₁ : ∀ y, E₂.modelPoint y ∈ O₂ → j₁ (E₂.modelPoint y) = E₁.modelPoint y := fun y hy =>
    funext fun k => (E₂.modelPoint_eq_of_coord_eq E₁ y _ hy k (H₁ y hy k)).symm
  set Ψₐ := shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ with hΨₐ
  have hI := pullback_padIdeal_inclusion_eq_of_shear E₁ E₂ Ψₐ (partialDiffeomorphToDiffeomorph Ψₐ)
    (partialDiffeomorphToDiffeomorph_apply_coe Ψₐ)
    (stalkIdeal_shear E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ v₂ v₁ H₂ H₁)
  refine ⟨⟨Ψₐ.source, Ψₐ.open_source⟩, ⟨Ψₐ.target, Ψₐ.open_target⟩,
    (partialDiffeomorphToDiffeomorph Ψₐ).toContMDiffMap, ?_,
    (partialDiffeomorphToDiffeomorph Ψₐ).isLocalDiffeomorph,
    (partialDiffeomorphToDiffeomorph Ψₐ).toEquiv.bijective, ⟨hI, ?_⟩, ?_⟩
  · exact (congrArg (fun p : pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G) =>
      p ∈ Ψₐ.source) (ambientPoint_padLeft E₁ x)).mpr
      (padExt_mem_shearAmbient_source E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ x hx₁ hx₂ (v₂ x hx₁) (v₁ x hx₂))
  · exact padded_equivalence_hom_of_shear E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ v₂ v₁ H₂ H₁ hI
  · intro y hy
    have hy' : padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y) ∈ Ψₐ.source :=
      (congrArg (fun p : pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G) => p ∈ Ψₐ.source)
        (ambientPoint_padLeft E₁ y)).mp hy
    obtain ⟨hy₁, hj⟩ := modelPoint_mem_of_padExt_mem_source E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ y hy'
    have h₂ := v₂ y hy₁
    have e : (⟨(E₁.padLeft m).ambientPoint y, hy⟩ : Ψₐ.source) =
        ⟨padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y), hy'⟩ :=
      Subtype.ext (ambientPoint_padLeft E₁ y)
    exact ((congrArg (fun q : Ψₐ.source => ((partialDiffeomorphToDiffeomorph Ψₐ) q).1) e).trans
      ((partialDiffeomorphToDiffeomorph_apply_coe Ψₐ _).trans
        (shearAmbient_padExt E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ y h₂ (v₁ y (h₂ ▸ hj))))).trans
      (ambientPoint_padRight E₂ y).symm

end Shear

/-- The restricted triple `(G, 𝓘_Y, ∅)|_W` lies in the class `DomBEDan`: empty divisor, and the
restricted ideal is reduced (`isReduced_pullback_of_isLocalDiffeomorph` at the open inclusion). -/
theorem PieceEmbedding.domBEDan_ambientTriple_pullback_inclusion {n : ℕ}
    {X : AnalyticSpace.{u} 𝕜} {V : Set X} (E : PieceEmbedding 𝕜 n X V)
    (W : Opens (pieceAmbient.{u} 𝕜 E.G)) :
    DomBEDan 𝕜 (E.ambientTriple.pullback (AnalyticManifold.inclusion _ W)
      (isLocalDiffeomorph_inclusion _ W)) :=
  ⟨⟨fun i => PEmpty.elim i⟩,
    IdealSheaf.isReduced_pullback_of_isLocalDiffeomorph _ (isLocalDiffeomorph_inclusion _ W)
      E.isReduced⟩

section ShearCore

variable {n m : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E₁ : PieceEmbedding 𝕜 n X V) (E₂ : PieceEmbedding 𝕜 m X V)
  (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
  (W₁ : Opens (pieceAmbient.{u} 𝕜 (E₁.padLeft m).G))
  (W₂ : Opens (pieceAmbient.{u} 𝕜 (E₂.padRight n).G))
  (g : AnalyticMap ((pieceAmbient.{u} 𝕜 (E₁.padLeft m).G).restrict W₁)
    ((pieceAmbient.{u} 𝕜 (E₂.padRight n).G).restrict W₂))
  (hloc : IsLocalDiffeomorph 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜) ω g)
  (hbij : Function.Bijective g)
  (hI : (E₁.padLeft m).restrictedIdeal W₁ =
    ((E₂.padRight n).restrictedIdeal W₂).pullback ⇑g g.contMDiff)
  (hmor : ((IdealSheaf.homOfPullbackEq ⇑g g.contMDiff hI) ≫ ((E₂.padRight n).restrictedIdealHom W₂))
      ≫ (E₂.padRight n).embInv =
    (E₁.padLeft m).restrictedIdealHom W₁ ≫ (E₁.padLeft m).embInv)
  (U' : Opens ((pieceAmbient.{u} 𝕜 (E₁.padLeft m).G).restrict W₁))
  (hU' : IsCompact (closure (U' : Set ((pieceAmbient.{u} 𝕜 (E₁.padLeft m).G).restrict W₁))))

local notation:80 g:81 " ⊚ " f:80 => CategoryTheory.CategoryStruct.comp (obj := AnalyticSpace _) f g
local macro "𝔸₁" : term => `(pieceAmbient 𝕜 (PieceEmbedding.G (PieceEmbedding.padLeft E₁ m)))
local macro "𝔸₂" : term => `(pieceAmbient 𝕜 (PieceEmbedding.G (PieceEmbedding.padRight E₂ n)))
local macro "𝕊₁" : term => `(AnalyticSpace.toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin (n + m) → 𝕜)))
local macro "ι₁" : term => `(AnalyticManifold.inclusion 𝔸₁ W₁)
local macro "ι₂" : term => `(AnalyticManifold.inclusion 𝔸₂ W₂)
local macro "hι₁" : term => `(isLocalDiffeomorph_inclusion 𝔸₁ W₁)
local macro "hι₂" : term => `(isLocalDiffeomorph_inclusion 𝔸₂ W₂)
local macro "𝐤" : term => `(ContMDiffMap.comp ι₂ g)
local macro "h𝐤" : term => `(BlowUpSequence.isLocalDiffeomorph_comp hι₂ hloc)
local macro "𝐔₁" : term => `(AnalyticMap.imageOpens ι₁ hι₁ U')
local macro "𝐔₂" : term => `(AnalyticMap.imageOpens 𝐤 h𝐤 U')
local macro "h𝐔₁" : term => `(AnalyticMap.isCompact_closure_image ι₁ hU')
local macro "h𝐔₂" : term => `(AnalyticMap.isCompact_closure_image 𝐤 hU')
local macro "𝐓₁" : term => `(PieceEmbedding.ambientTriple (PieceEmbedding.padLeft E₁ m))
local macro "𝐓₂" : term => `(PieceEmbedding.ambientTriple (PieceEmbedding.padRight E₂ n))
local macro "𝐓₁'" : term => `(AnalyticTriple.pullback 𝐓₁ ι₁ hι₁)
local macro "h𝐓₁'" : term => `(PieceEmbedding.domBEDan_ambientTriple_pullback_inclusion
  (PieceEmbedding.padLeft E₁ m) W₁)
local macro "𝐋'" : term => `(CompatibleFamily.seqOn
  (AnalyticFamilyFunctor.fam (BEDanFamStar.fam bed (n + m)) 𝐓₁' h𝐓₁') U' hU')
local macro "𝐋₁" : term => `(PieceEmbedding.localResolutionSeq (PieceEmbedding.padLeft E₁ m) bed 𝐔₁
  h𝐔₁)
local macro "𝐋₂" : term => `(PieceEmbedding.localResolutionSeq (PieceEmbedding.padRight E₂ n) bed 𝐔₂
  h𝐔₂)
local macro "𝐉'" : term => `(IdealSheaf.restrict (AnalyticTriple.I 𝐓₁') U')
local macro "𝐘'" : term => `(FiniteSuccession.strictTransformSubspaceSeq
  (BlowUpSequence.toSuccession 𝐋') 𝐉'
  (Fin.last _))
local macro "𝐘₁" : term =>
  `(FiniteSuccession.strictTransformSubspaceSeq (BlowUpSequence.toSuccession 𝐋₁)
  (PieceEmbedding.restrictedIdeal (PieceEmbedding.padLeft E₁ m) 𝐔₁) (Fin.last _))
local macro "𝐘₂" : term =>
  `(FiniteSuccession.strictTransformSubspaceSeq (BlowUpSequence.toSuccession 𝐋₂)
  (PieceEmbedding.restrictedIdeal (PieceEmbedding.padRight E₂ n) 𝐔₂) (Fin.last _))
local macro "incl'" : term => `(AnalyticManifold.inclusion
  (AnalyticManifold.restrict 𝔸₁ W₁) U')
local macro "𝐌'" : term => `(FiniteSuccession.stage (BlowUpSequence.toSuccession 𝐋') (Fin.last _))
local macro "𝐌₁" : term => `(FiniteSuccession.stage (BlowUpSequence.toSuccession 𝐋₁) (Fin.last _))
local macro "𝐌₂" : term => `(FiniteSuccession.stage (BlowUpSequence.toSuccession 𝐋₂) (Fin.last _))

include hmor in
/-- **The compatibility `Π₂ ∘ m₂ = Π₁ ∘ m₁` over the piece** (factored out of
`exists_isIso_localResolution_of_shear_core`), for ANY two last-stage diffeomorphisms
`G₁ : M' ≃ M₁`, `G₂ : M' ≃ M₂` from the value on `W₁|U'` lying over `ι₁` and over `ι₂ ∘ g` (the
squares `hG₁sq`, `hG₂sq`) and carrying the final strict transform (`hG₁id`, `hG₂id`) — the
isomorphisms `m₁ := homOfPullbackEq G₁`, `m₂ := homOfPullbackEq G₂`. The identity is
read after the isomorphism `E₁.emb` through the shear's morphism identity on `W₁`, the quotient-map
squares (`toAnalyticSpaceι_comp_restrictedIdealHom`, `localResolutionMap_comp_ι`,
`homOfPullbackEq_comp_toAnalyticSpaceι`) and the two squares of composites
(`Hom.ext_of_comp_quotientι`, `ofManifoldHom_comp`/`_congr`). The core obtains `G₁`, `G₂` from
`exists_diffeomorph_last_of_commutes_injective`. -/
theorem PieceEmbedding.localResolutionToPiece_comp_homOfPullbackEq_of_shear
    (G₁ : Diffeomorph 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜) 𝐌' 𝐌₁ ω)
    (hG₁sq : ∀ p, AnalyticManifold.inclusion 𝔸₁ 𝐔₁
        ((BlowUpSequence.toSuccession 𝐋₁).composite (G₁ p)) =
      ι₁ (incl' ((BlowUpSequence.toSuccession 𝐋').composite p)))
    (hG₁id : 𝐘' = (𝐘₁).pullback ⇑G₁ G₁.contMDiff)
    (G₂ : Diffeomorph 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜) 𝐌' 𝐌₂ ω)
    (hG₂sq : ∀ p, AnalyticManifold.inclusion 𝔸₂ 𝐔₂
        ((BlowUpSequence.toSuccession 𝐋₂).composite (G₂ p)) =
      𝐤 (incl' ((BlowUpSequence.toSuccession 𝐋').composite p)))
    (hG₂id : 𝐘' = (𝐘₂).pullback ⇑G₂ G₂.contMDiff) :
    IdealSheaf.homOfPullbackEq ⇑G₂ G₂.contMDiff hG₂id ≫
        (E₂.padRight n).localResolutionToPiece bed 𝐔₂ h𝐔₂ =
      IdealSheaf.homOfPullbackEq ⇑G₁ G₁.contMDiff hG₁id ≫
          (E₁.padLeft m).localResolutionToPiece bed 𝐔₁ h𝐔₁ := by
  -- the quotient-map squares, on the raw terms
  have q1 := (E₁.padLeft m).toAnalyticSpaceι_comp_restrictedIdealHom 𝐔₁
  have q1' := (E₂.padRight n).toAnalyticSpaceι_comp_restrictedIdealHom 𝐔₂
  have q2 := (E₁.padLeft m).localResolutionMap_comp_ι bed 𝐔₁ h𝐔₁
  have q2' := (E₂.padRight n).localResolutionMap_comp_ι bed 𝐔₂ h𝐔₂
  have q3 := homOfPullbackEq_comp_toAnalyticSpaceι ⇑G₁ G₁.contMDiff hG₁id
  have q3' := homOfPullbackEq_comp_toAnalyticSpaceι ⇑G₂ G₂.contMDiff hG₂id
  have q4 := quotientMap_comp_quotientι
    (AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin (n + m) → 𝕜))
      (BlowUpSequence.toSuccession 𝐋').composite) 𝐘' 𝐉'
    ((BlowUpSequence.toSuccession 𝐋').compat_composite_strictTransformSubspaceSeq
      (ContinuousLinearEquiv.refl 𝕜 (Fin (n + m) → 𝕜)) 𝐉')
  have q5 := homOfPullbackEq_comp_toAnalyticSpaceι (J' := 𝐉')
    (J := (E₁.padLeft m).restrictedIdeal W₁) incl' (incl').contMDiff rfl
  have q6 := (E₁.padLeft m).toAnalyticSpaceι_comp_restrictedIdealHom W₁
  have q6' := (E₂.padRight n).toAnalyticSpaceι_comp_restrictedIdealHom W₂
  have q7 := homOfPullbackEq_comp_toAnalyticSpaceι ⇑g g.contMDiff hI
  -- the `Sp`-level squares of the composites, from the pointwise squares `hG₁sq`, `hG₂sq`
  have hfun₁ : ⇑(AnalyticManifold.inclusion 𝔸₁ 𝐔₁) ∘
        (⇑(BlowUpSequence.toSuccession 𝐋₁).composite ∘ ⇑G₁) =
      ⇑ι₁ ∘ (⇑incl' ∘ ⇑(BlowUpSequence.toSuccession 𝐋').composite) :=
    funext fun p => hG₁sq p
  have hfun₂ : ⇑(AnalyticManifold.inclusion 𝔸₂ 𝐔₂) ∘
        (⇑(BlowUpSequence.toSuccession 𝐋₂).composite ∘ ⇑G₂) =
      ⇑ι₂ ∘ (⇑g ∘ (⇑incl' ∘ ⇑(BlowUpSequence.toSuccession 𝐋').composite)) :=
    funext fun p => hG₂sq p
  -- ---- the abbreviations: typed `let`s, ONE spelling per object (the two `localResolution`s, the
  -- `IdealSheaf.toAnalyticSpace` of `𝐘'` and `𝐉'`), the identities re-read on them
  let ιI₁ : (E₁.padLeft m).ideal.toAnalyticSpace ⟶ 𝕊₁ 𝔸₁ :=
    (E₁.padLeft m).ideal.toAnalyticSpaceι
  let ιI₂ :
      (E₂.padRight n).ideal.toAnalyticSpace ⟶ 𝕊₁ 𝔸₂ :=
    (E₂.padRight n).ideal.toAnalyticSpaceι
  let ιU₁ :
      ((E₁.padLeft m).restrictedIdeal 𝐔₁).toAnalyticSpace ⟶ 𝕊₁ ((𝔸₁).restrict 𝐔₁) :=
    ((E₁.padLeft m).restrictedIdeal 𝐔₁).toAnalyticSpaceι
  let ιU₂ :
      ((E₂.padRight n).restrictedIdeal 𝐔₂).toAnalyticSpace ⟶ 𝕊₁ ((𝔸₂).restrict 𝐔₂) :=
    ((E₂.padRight n).restrictedIdeal 𝐔₂).toAnalyticSpaceι
  let ιW₁ :
      ((E₁.padLeft m).restrictedIdeal W₁).toAnalyticSpace ⟶ 𝕊₁ ((𝔸₁).restrict W₁) :=
    ((E₁.padLeft m).restrictedIdeal W₁).toAnalyticSpaceι
  let ιW₂ :
      ((E₂.padRight n).restrictedIdeal W₂).toAnalyticSpace ⟶ 𝕊₁ ((𝔸₂).restrict W₂) :=
    ((E₂.padRight n).restrictedIdeal W₂).toAnalyticSpaceι
  let ιU' :
      IdealSheaf.toAnalyticSpace 𝐉' ⟶ 𝕊₁ (((𝔸₁).restrict W₁).restrict U') :=
    IdealSheaf.toAnalyticSpaceι 𝐉'
  let ιY₁ :
      (E₁.padLeft m).localResolution bed 𝐔₁ h𝐔₁ ⟶ 𝕊₁ 𝐌₁ :=
    (𝐘₁).toAnalyticSpaceι
  let ιY₂ :
      (E₂.padRight n).localResolution bed 𝐔₂ h𝐔₂ ⟶ 𝕊₁ 𝐌₂ :=
    (𝐘₂).toAnalyticSpaceι
  let ιY' : IdealSheaf.toAnalyticSpace 𝐘' ⟶ 𝕊₁ 𝐌' :=
      (𝐘').toAnalyticSpaceι
  let l₁ : (E₁.padLeft m).localResolution bed 𝐔₁ h𝐔₁ ⟶
      ((E₁.padLeft m).restrictedIdeal 𝐔₁).toAnalyticSpace :=
    (E₁.padLeft m).localResolutionMap bed 𝐔₁ h𝐔₁
  let l₂ : (E₂.padRight n).localResolution bed 𝐔₂ h𝐔₂ ⟶
      ((E₂.padRight n).restrictedIdeal 𝐔₂).toAnalyticSpace :=
    (E₂.padRight n).localResolutionMap bed 𝐔₂ h𝐔₂
  let l' : IdealSheaf.toAnalyticSpace 𝐘' ⟶ IdealSheaf.toAnalyticSpace 𝐉' :=
    quotientMap
      (AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin (n + m) → 𝕜))
        (BlowUpSequence.toSuccession 𝐋').composite) _ _
      ((BlowUpSequence.toSuccession 𝐋').compat_composite_strictTransformSubspaceSeq
        (ContinuousLinearEquiv.refl 𝕜 (Fin (n + m) → 𝕜)) 𝐉')
  let ρ₁ :
      ((E₁.padLeft m).restrictedIdeal 𝐔₁).toAnalyticSpace ⟶
          (E₁.padLeft m).ideal.toAnalyticSpace :=
    (E₁.padLeft m).restrictedIdealHom 𝐔₁
  let ρ₂ :
      ((E₂.padRight n).restrictedIdeal 𝐔₂).toAnalyticSpace ⟶
          (E₂.padRight n).ideal.toAnalyticSpace :=
    (E₂.padRight n).restrictedIdealHom 𝐔₂
  let ρW₁ :
      ((E₁.padLeft m).restrictedIdeal W₁).toAnalyticSpace ⟶
          (E₁.padLeft m).ideal.toAnalyticSpace :=
    (E₁.padLeft m).restrictedIdealHom W₁
  let ρW₂ :
      ((E₂.padRight n).restrictedIdeal W₂).toAnalyticSpace ⟶
          (E₂.padRight n).ideal.toAnalyticSpace :=
    (E₂.padRight n).restrictedIdealHom W₂
  let ρ' : IdealSheaf.toAnalyticSpace 𝐉' ⟶ ((E₁.padLeft m).restrictedIdeal W₁).toAnalyticSpace :=
    IdealSheaf.homOfPullbackEq (J' := 𝐉') (J := (E₁.padLeft m).restrictedIdeal W₁) incl'
      (incl').contMDiff rfl
  let mg :
      ((E₁.padLeft m).restrictedIdeal W₁).toAnalyticSpace ⟶
          ((E₂.padRight n).restrictedIdeal W₂).toAnalyticSpace :=
    IdealSheaf.homOfPullbackEq ⇑g g.contMDiff hI
  let m₁ : IdealSheaf.toAnalyticSpace 𝐘' ⟶ (E₁.padLeft m).localResolution bed 𝐔₁ h𝐔₁ :=
    IdealSheaf.homOfPullbackEq ⇑G₁ G₁.contMDiff hG₁id
  let m₂ : IdealSheaf.toAnalyticSpace 𝐘' ⟶ (E₂.padRight n).localResolution bed 𝐔₂ h𝐔₂ :=
    IdealSheaf.homOfPullbackEq ⇑G₂ G₂.contMDiff hG₂id
  let SpU₁ : 𝕊₁ ((𝔸₁).restrict 𝐔₁) ⟶ 𝕊₁ 𝔸₁ :=
    ofManifoldHom (AnalyticManifold.inclusion 𝔸₁ 𝐔₁)
      (AnalyticManifold.inclusion 𝔸₁ 𝐔₁).contMDiff
  let SpU₂ : 𝕊₁ ((𝔸₂).restrict 𝐔₂) ⟶ 𝕊₁ 𝔸₂ :=
    ofManifoldHom (AnalyticManifold.inclusion 𝔸₂ 𝐔₂)
      (AnalyticManifold.inclusion 𝔸₂ 𝐔₂).contMDiff
  let Spσ₁ : 𝕊₁ 𝐌₁ ⟶ 𝕊₁ ((𝔸₁).restrict 𝐔₁) :=
    AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin (n + m) → 𝕜))
      (BlowUpSequence.toSuccession 𝐋₁).composite
  let Spσ₂ : 𝕊₁ 𝐌₂ ⟶ 𝕊₁ ((𝔸₂).restrict 𝐔₂) :=
    AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin (n + m) → 𝕜))
      (BlowUpSequence.toSuccession 𝐋₂).composite
  let Spσ' : 𝕊₁ 𝐌' ⟶ 𝕊₁ (((𝔸₁).restrict W₁).restrict U') :=
    AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin (n + m) → 𝕜))
      (BlowUpSequence.toSuccession 𝐋').composite
  let SpG₁ : 𝕊₁ 𝐌' ⟶ 𝕊₁ 𝐌₁ :=
      ofManifoldHom ⇑G₁ G₁.contMDiff
  let SpG₂ : 𝕊₁ 𝐌' ⟶ 𝕊₁ 𝐌₂ :=
      ofManifoldHom ⇑G₂ G₂.contMDiff
  let Spι₁ : 𝕊₁ ((𝔸₁).restrict W₁) ⟶ 𝕊₁ 𝔸₁ :=
      ofManifoldHom ι₁
      (ι₁).contMDiff
  let Spι₂ : 𝕊₁ ((𝔸₂).restrict W₂) ⟶ 𝕊₁ 𝔸₂ :=
      ofManifoldHom ι₂
      (ι₂).contMDiff
  let Spg :
      𝕊₁ ((𝔸₁).restrict W₁) ⟶ 𝕊₁ ((𝔸₂).restrict W₂) :=
    ofManifoldHom ⇑g g.contMDiff
  let Spi' : 𝕊₁ (((𝔸₁).restrict W₁).restrict U') ⟶ 𝕊₁ ((𝔸₁).restrict W₁) :=
    ofManifoldHom incl' (incl').contMDiff
  have q1r : ιI₁ ⊚ ρ₁ = SpU₁ ⊚ ιU₁ := q1
  have q1r' : ιI₂ ⊚ ρ₂ = SpU₂ ⊚ ιU₂ := q1'
  have q2r : ιU₁ ⊚ l₁ = Spσ₁ ⊚ ιY₁ := q2
  have q2r' : ιU₂ ⊚ l₂ = Spσ₂ ⊚ ιY₂ := q2'
  have q3r : ιY₁ ⊚ m₁ = SpG₁ ⊚ ιY' := q3
  have q3r' : ιY₂ ⊚ m₂ = SpG₂ ⊚ ιY' := q3'
  have q4r : ιU' ⊚ l' = Spσ' ⊚ ιY' := q4
  have q5r : ιW₁ ⊚ ρ' = Spi' ⊚ ιU' := q5
  have q6r : ιI₁ ⊚ ρW₁ = Spι₁ ⊚ ιW₁ := q6
  have q6r' : ιI₂ ⊚ ρW₂ = Spι₂ ⊚ ιW₂ := q6'
  have q7r : ιW₂ ⊚ mg = Spg ⊚ ιW₁ := q7
  have hmorr : (E₂.padRight n).embInv ⊚ (ρW₂ ⊚ mg) = (E₁.padLeft m).embInv ⊚ ρW₁ := hmor
  have e9₁ : (E₁.padLeft m).emb ⊚ (E₁.padLeft m).embInv = 𝟙 _ :=
    (E₁.padLeft m).emb_comp_embInv
  have assoc' : ∀ {A B C D : AnalyticSpace.{u} 𝕜} (a : C ⟶ D) (b : B ⟶ C) (c : A ⟶ B),
      a ⊚ (b ⊚ c) = (a ⊚ b) ⊚ c :=
    fun _ _ _ => Category.assoc _ _ _
  have comp_id' : ∀ {A B : AnalyticSpace.{u} 𝕜} (f : A ⟶ B), 𝟙 B ⊚ f = f :=
    fun _ => Category.comp_id _
  -- the `Sp`-level squares of the composites
  have s1 : SpU₁ ⊚ (Spσ₁ ⊚ SpG₁) = Spι₁ ⊚ (Spi' ⊚ Spσ') :=
    calc SpU₁ ⊚ (Spσ₁ ⊚ SpG₁)
        = SpU₁ ⊚ (show 𝕊₁ 𝐌' ⟶ 𝕊₁ ((𝔸₁).restrict 𝐔₁) from
            ofManifoldHom (⇑(BlowUpSequence.toSuccession 𝐋₁).composite ∘ ⇑G₁)
              ((BlowUpSequence.toSuccession 𝐋₁).composite.contMDiff.comp G₁.contMDiff)) :=
          congrArg (fun k => SpU₁ ⊚ k) (ofManifoldHom_comp ⇑G₁ G₁.contMDiff
            ⇑(BlowUpSequence.toSuccession 𝐋₁).composite
            (BlowUpSequence.toSuccession 𝐋₁).composite.contMDiff).symm
      _ = (show 𝕊₁ 𝐌' ⟶ 𝕊₁ 𝔸₁ from
            ofManifoldHom (⇑(AnalyticManifold.inclusion 𝔸₁ 𝐔₁) ∘
                (⇑(BlowUpSequence.toSuccession 𝐋₁).composite ∘ ⇑G₁))
              ((AnalyticManifold.inclusion 𝔸₁ 𝐔₁).contMDiff.comp
                ((BlowUpSequence.toSuccession 𝐋₁).composite.contMDiff.comp G₁.contMDiff))) :=
          (ofManifoldHom_comp _ _ _ _).symm
      _ = (show 𝕊₁ 𝐌' ⟶ 𝕊₁ 𝔸₁ from
            ofManifoldHom (⇑ι₁ ∘ (⇑incl' ∘ ⇑(BlowUpSequence.toSuccession 𝐋').composite))
              ((ι₁).contMDiff.comp
                ((incl').contMDiff.comp (BlowUpSequence.toSuccession 𝐋').composite.contMDiff))) :=
          ofManifoldHom_congr hfun₁ _
      _ = Spι₁ ⊚ (show 𝕊₁ 𝐌' ⟶ 𝕊₁ ((𝔸₁).restrict W₁) from
            ofManifoldHom (⇑incl' ∘ ⇑(BlowUpSequence.toSuccession 𝐋').composite)
              ((incl').contMDiff.comp (BlowUpSequence.toSuccession 𝐋').composite.contMDiff)) :=
          ofManifoldHom_comp _ _ _ _
      _ = Spι₁ ⊚ (Spi' ⊚ Spσ') := congrArg (fun k => Spι₁ ⊚ k) (ofManifoldHom_comp _ _ _ _)
  have s2 : SpU₂ ⊚ (Spσ₂ ⊚ SpG₂) = Spι₂ ⊚ (Spg ⊚ (Spi' ⊚ Spσ')) :=
    calc SpU₂ ⊚ (Spσ₂ ⊚ SpG₂)
        = SpU₂ ⊚ (show 𝕊₁ 𝐌' ⟶ 𝕊₁ ((𝔸₂).restrict 𝐔₂) from
            ofManifoldHom (⇑(BlowUpSequence.toSuccession 𝐋₂).composite ∘ ⇑G₂)
              ((BlowUpSequence.toSuccession 𝐋₂).composite.contMDiff.comp G₂.contMDiff)) :=
          congrArg (fun k => SpU₂ ⊚ k) (ofManifoldHom_comp ⇑G₂ G₂.contMDiff
            ⇑(BlowUpSequence.toSuccession 𝐋₂).composite
            (BlowUpSequence.toSuccession 𝐋₂).composite.contMDiff).symm
      _ = (show 𝕊₁ 𝐌' ⟶ 𝕊₁ 𝔸₂ from
            ofManifoldHom (⇑(AnalyticManifold.inclusion 𝔸₂ 𝐔₂) ∘
                (⇑(BlowUpSequence.toSuccession 𝐋₂).composite ∘ ⇑G₂))
              ((AnalyticManifold.inclusion 𝔸₂ 𝐔₂).contMDiff.comp
                ((BlowUpSequence.toSuccession 𝐋₂).composite.contMDiff.comp G₂.contMDiff))) :=
          (ofManifoldHom_comp _ _ _ _).symm
      _ = (show 𝕊₁ 𝐌' ⟶ 𝕊₁ 𝔸₂ from
            ofManifoldHom (⇑ι₂ ∘ (⇑g ∘ (⇑incl' ∘ ⇑(BlowUpSequence.toSuccession 𝐋').composite)))
              ((ι₂).contMDiff.comp (g.contMDiff.comp
                ((incl').contMDiff.comp (BlowUpSequence.toSuccession 𝐋').composite.contMDiff)))) :=
          ofManifoldHom_congr hfun₂ _
      _ = Spι₂ ⊚ (show 𝕊₁ 𝐌' ⟶ 𝕊₁ ((𝔸₂).restrict W₂) from
            ofManifoldHom (⇑g ∘ (⇑incl' ∘ ⇑(BlowUpSequence.toSuccession 𝐋').composite))
              (g.contMDiff.comp
                ((incl').contMDiff.comp (BlowUpSequence.toSuccession 𝐋').composite.contMDiff))) :=
          ofManifoldHom_comp _ _ _ _
      _ =
          Spι₂ ⊚
              (Spg ⊚
                  (show 𝕊₁ 𝐌' ⟶ 𝕊₁ ((𝔸₁).restrict W₁) from
            ofManifoldHom (⇑incl' ∘ ⇑(BlowUpSequence.toSuccession 𝐋').composite)
              ((incl').contMDiff.comp (BlowUpSequence.toSuccession 𝐋').composite.contMDiff))) :=
          congrArg (fun k => Spι₂ ⊚ k) (ofManifoldHom_comp _ _ _ _)
      _ = Spι₂ ⊚ (Spg ⊚ (Spi' ⊚ Spσ')) :=
          congrArg (fun k => Spι₂ ⊚ (Spg ⊚ k)) (ofManifoldHom_comp _ _ _ _)
  -- (ii) the `A₁`-side composite factors through the shear's source `W₁`
  have key₁ : ρ₁ ⊚ (l₁ ⊚ m₁) = ρW₁ ⊚ (ρ' ⊚ l') :=
    Hom.ext_of_comp_quotientι (X := ofManifold 𝕜 (Fin (n + m) → 𝕜) 𝔸₁) (E₁.padLeft m).ideal
      (calc ιI₁ ⊚ (ρ₁ ⊚ (l₁ ⊚ m₁))
          = (ιI₁ ⊚ ρ₁) ⊚ (l₁ ⊚ m₁) := assoc' _ _ _
        _ = (SpU₁ ⊚ ιU₁) ⊚ (l₁ ⊚ m₁) := congrArg (fun k => k ⊚ (l₁ ⊚ m₁)) q1r
        _ = SpU₁ ⊚ (ιU₁ ⊚ (l₁ ⊚ m₁)) := (assoc' _ _ _).symm
        _ = SpU₁ ⊚ ((ιU₁ ⊚ l₁) ⊚ m₁) := congrArg (fun k => SpU₁ ⊚ k) (assoc' _ _ _)
        _ = SpU₁ ⊚ ((Spσ₁ ⊚ ιY₁) ⊚ m₁) := congrArg (fun k => SpU₁ ⊚ (k ⊚ m₁)) q2r
        _ = SpU₁ ⊚ (Spσ₁ ⊚ (ιY₁ ⊚ m₁)) := congrArg (fun k => SpU₁ ⊚ k) (assoc' _ _ _).symm
        _ = SpU₁ ⊚ (Spσ₁ ⊚ (SpG₁ ⊚ ιY')) := congrArg (fun k => SpU₁ ⊚ (Spσ₁ ⊚ k)) q3r
        _ = SpU₁ ⊚ ((Spσ₁ ⊚ SpG₁) ⊚ ιY') := congrArg (fun k => SpU₁ ⊚ k) (assoc' _ _ _)
        _ = (SpU₁ ⊚ (Spσ₁ ⊚ SpG₁)) ⊚ ιY' := assoc' _ _ _
        _ = (Spι₁ ⊚ (Spi' ⊚ Spσ')) ⊚ ιY' := congrArg (fun k => k ⊚ ιY') s1
        _ = Spι₁ ⊚ ((Spi' ⊚ Spσ') ⊚ ιY') := (assoc' _ _ _).symm
        _ = Spι₁ ⊚ (Spi' ⊚ (Spσ' ⊚ ιY')) := congrArg (fun k => Spι₁ ⊚ k) (assoc' _ _ _).symm
        _ = Spι₁ ⊚ (Spi' ⊚ (ιU' ⊚ l')) := congrArg (fun k => Spι₁ ⊚ (Spi' ⊚ k)) q4r.symm
        _ = Spι₁ ⊚ ((Spi' ⊚ ιU') ⊚ l') := congrArg (fun k => Spι₁ ⊚ k) (assoc' _ _ _)
        _ = Spι₁ ⊚ ((ιW₁ ⊚ ρ') ⊚ l') := congrArg (fun k => Spι₁ ⊚ (k ⊚ l')) q5r.symm
        _ = Spι₁ ⊚ (ιW₁ ⊚ (ρ' ⊚ l')) := congrArg (fun k => Spι₁ ⊚ k) (assoc' _ _ _).symm
        _ = (Spι₁ ⊚ ιW₁) ⊚ (ρ' ⊚ l') := assoc' _ _ _
        _ = (ιI₁ ⊚ ρW₁) ⊚ (ρ' ⊚ l') := congrArg (fun k => k ⊚ (ρ' ⊚ l')) q6r.symm
        _ = ιI₁ ⊚ (ρW₁ ⊚ (ρ' ⊚ l')) := (assoc' _ _ _).symm)
  -- (i) the `A₂`-side composite factors through the shear
  have key₂ : ρ₂ ⊚ (l₂ ⊚ m₂) = ρW₂ ⊚ (mg ⊚ (ρ' ⊚ l')) :=
    Hom.ext_of_comp_quotientι (X := ofManifold 𝕜 (Fin (n + m) → 𝕜) 𝔸₂) (E₂.padRight n).ideal
      (calc ιI₂ ⊚ (ρ₂ ⊚ (l₂ ⊚ m₂))
          = (ιI₂ ⊚ ρ₂) ⊚ (l₂ ⊚ m₂) := assoc' _ _ _
        _ = (SpU₂ ⊚ ιU₂) ⊚ (l₂ ⊚ m₂) := congrArg (fun k => k ⊚ (l₂ ⊚ m₂)) q1r'
        _ = SpU₂ ⊚ (ιU₂ ⊚ (l₂ ⊚ m₂)) := (assoc' _ _ _).symm
        _ = SpU₂ ⊚ ((ιU₂ ⊚ l₂) ⊚ m₂) := congrArg (fun k => SpU₂ ⊚ k) (assoc' _ _ _)
        _ = SpU₂ ⊚ ((Spσ₂ ⊚ ιY₂) ⊚ m₂) := congrArg (fun k => SpU₂ ⊚ (k ⊚ m₂)) q2r'
        _ = SpU₂ ⊚ (Spσ₂ ⊚ (ιY₂ ⊚ m₂)) := congrArg (fun k => SpU₂ ⊚ k) (assoc' _ _ _).symm
        _ = SpU₂ ⊚ (Spσ₂ ⊚ (SpG₂ ⊚ ιY')) := congrArg (fun k => SpU₂ ⊚ (Spσ₂ ⊚ k)) q3r'
        _ = SpU₂ ⊚ ((Spσ₂ ⊚ SpG₂) ⊚ ιY') := congrArg (fun k => SpU₂ ⊚ k) (assoc' _ _ _)
        _ = (SpU₂ ⊚ (Spσ₂ ⊚ SpG₂)) ⊚ ιY' := assoc' _ _ _
        _ = (Spι₂ ⊚ (Spg ⊚ (Spi' ⊚ Spσ'))) ⊚ ιY' := congrArg (fun k => k ⊚ ιY') s2
        _ = Spι₂ ⊚ ((Spg ⊚ (Spi' ⊚ Spσ')) ⊚ ιY') := (assoc' _ _ _).symm
        _ = Spι₂ ⊚ (Spg ⊚ ((Spi' ⊚ Spσ') ⊚ ιY')) :=
            congrArg (fun k => Spι₂ ⊚ k) (assoc' _ _ _).symm
        _ = Spι₂ ⊚ (Spg ⊚ (Spi' ⊚ (Spσ' ⊚ ιY'))) :=
            congrArg (fun k => Spι₂ ⊚ (Spg ⊚ k)) (assoc' _ _ _).symm
        _ = Spι₂ ⊚ (Spg ⊚ (Spi' ⊚ (ιU' ⊚ l'))) :=
            congrArg (fun k => Spι₂ ⊚ (Spg ⊚ (Spi' ⊚ k))) q4r.symm
        _ = Spι₂ ⊚ (Spg ⊚ ((Spi' ⊚ ιU') ⊚ l')) :=
            congrArg (fun k => Spι₂ ⊚ (Spg ⊚ k)) (assoc' _ _ _)
        _ = Spι₂ ⊚ (Spg ⊚ ((ιW₁ ⊚ ρ') ⊚ l')) :=
            congrArg (fun k => Spι₂ ⊚ (Spg ⊚ (k ⊚ l'))) q5r.symm
        _ = Spι₂ ⊚ (Spg ⊚ (ιW₁ ⊚ (ρ' ⊚ l'))) :=
            congrArg (fun k => Spι₂ ⊚ (Spg ⊚ k)) (assoc' _ _ _).symm
        _ = Spι₂ ⊚ ((Spg ⊚ ιW₁) ⊚ (ρ' ⊚ l')) := congrArg (fun k => Spι₂ ⊚ k) (assoc' _ _ _)
        _ = Spι₂ ⊚ ((ιW₂ ⊚ mg) ⊚ (ρ' ⊚ l')) :=
            congrArg (fun k => Spι₂ ⊚ (k ⊚ (ρ' ⊚ l'))) q7r.symm
        _ = Spι₂ ⊚ (ιW₂ ⊚ (mg ⊚ (ρ' ⊚ l'))) := congrArg (fun k => Spι₂ ⊚ k) (assoc' _ _ _).symm
        _ = (Spι₂ ⊚ ιW₂) ⊚ (mg ⊚ (ρ' ⊚ l')) := assoc' _ _ _
        _ = (ιI₂ ⊚ ρW₂) ⊚ (mg ⊚ (ρ' ⊚ l')) := congrArg (fun k => k ⊚ (mg ⊚ (ρ' ⊚ l'))) q6r'.symm
        _ = ιI₂ ⊚ (ρW₂ ⊚ (mg ⊚ (ρ' ⊚ l'))) := (assoc' _ _ _).symm)
  -- the two maps to the piece agree on `Ỹ'`, after the isomorphism `E₁.emb`
  have key : ((E₂.padRight n).embInv ⊚ (ρ₂ ⊚ l₂)) ⊚ m₂ =
      ((E₁.padLeft m).embInv ⊚ (ρ₁ ⊚ l₁)) ⊚ m₁ := by
    have hemb : @IsIso (AnalyticSpace.{u} 𝕜) _ _ _ (E₁.padLeft m).emb :=
      (E₁.padLeft m).emb_isIso
    refine (@Iso.cancel_iso_hom_right (AnalyticSpace.{u} 𝕜) _ _ _ _ _ _
      (@asIso (AnalyticSpace.{u} 𝕜) _ _ _ (E₁.padLeft m).emb hemb)).mp ?_
    calc (E₁.padLeft m).emb ⊚ (((E₂.padRight n).embInv ⊚ (ρ₂ ⊚ l₂)) ⊚ m₂)
        = (E₁.padLeft m).emb ⊚ ((E₂.padRight n).embInv ⊚ ((ρ₂ ⊚ l₂) ⊚ m₂)) :=
          congrArg (fun k => (E₁.padLeft m).emb ⊚ k) (assoc' _ _ _).symm
      _ = (E₁.padLeft m).emb ⊚ ((E₂.padRight n).embInv ⊚ (ρ₂ ⊚ (l₂ ⊚ m₂))) :=
          congrArg (fun k => (E₁.padLeft m).emb ⊚ ((E₂.padRight n).embInv ⊚ k))
            (assoc' _ _ _).symm
      _ = (E₁.padLeft m).emb ⊚ ((E₂.padRight n).embInv ⊚ (ρW₂ ⊚ (mg ⊚ (ρ' ⊚ l')))) :=
          congrArg (fun k => (E₁.padLeft m).emb ⊚ ((E₂.padRight n).embInv ⊚ k)) key₂
      _ = (E₁.padLeft m).emb ⊚ ((E₂.padRight n).embInv ⊚ ((ρW₂ ⊚ mg) ⊚ (ρ' ⊚ l'))) :=
          congrArg (fun k => (E₁.padLeft m).emb ⊚ ((E₂.padRight n).embInv ⊚ k)) (assoc' _ _ _)
      _ = (E₁.padLeft m).emb ⊚ (((E₂.padRight n).embInv ⊚ (ρW₂ ⊚ mg)) ⊚ (ρ' ⊚ l')) :=
          congrArg (fun k => (E₁.padLeft m).emb ⊚ k) (assoc' _ _ _)
      _ = (E₁.padLeft m).emb ⊚ (((E₁.padLeft m).embInv ⊚ ρW₁) ⊚ (ρ' ⊚ l')) :=
          congrArg (fun k => (E₁.padLeft m).emb ⊚ (k ⊚ (ρ' ⊚ l'))) hmorr
      _ = (E₁.padLeft m).emb ⊚ ((E₁.padLeft m).embInv ⊚ (ρW₁ ⊚ (ρ' ⊚ l'))) :=
          congrArg (fun k => (E₁.padLeft m).emb ⊚ k) (assoc' _ _ _).symm
      _ = ((E₁.padLeft m).emb ⊚ (E₁.padLeft m).embInv) ⊚ (ρW₁ ⊚ (ρ' ⊚ l')) := assoc' _ _ _
      _ = 𝟙 _ ⊚ (ρW₁ ⊚ (ρ' ⊚ l')) :=
          congrArg (fun k => k ⊚ (ρW₁ ⊚ (ρ' ⊚ l'))) e9₁
      _ = ρW₁ ⊚ (ρ' ⊚ l') := comp_id' _
      _ = ρ₁ ⊚ (l₁ ⊚ m₁) := key₁.symm
      _ = 𝟙 _ ⊚ (ρ₁ ⊚ (l₁ ⊚ m₁)) := (comp_id' _).symm
      _ = ((E₁.padLeft m).emb ⊚ (E₁.padLeft m).embInv) ⊚ (ρ₁ ⊚ (l₁ ⊚ m₁)) :=
          congrArg (fun k => k ⊚ (ρ₁ ⊚ (l₁ ⊚ m₁))) e9₁.symm
      _ = (E₁.padLeft m).emb ⊚ ((E₁.padLeft m).embInv ⊚ (ρ₁ ⊚ (l₁ ⊚ m₁))) :=
          (assoc' _ _ _).symm
      _ = (E₁.padLeft m).emb ⊚ ((E₁.padLeft m).embInv ⊚ ((ρ₁ ⊚ l₁) ⊚ m₁)) :=
          congrArg (fun k => (E₁.padLeft m).emb ⊚ ((E₁.padLeft m).embInv ⊚ k)) (assoc' _ _ _)
      _ = (E₁.padLeft m).emb ⊚ (((E₁.padLeft m).embInv ⊚ (ρ₁ ⊚ l₁)) ⊚ m₁) :=
          congrArg (fun k => (E₁.padLeft m).emb ⊚ k) (assoc' _ _ _)
  exact key

include hbed hbij hmor in
/-- **The shear's isomorphism of the padded local resolutions over `U₁ := ι₁(U')` and
`U₂ := (ι₂ ∘ g)(U')`** ([Kol07, Theorem 36, proof]: Lemma 39 with the commutation with smooth
morphisms), for a relatively compact open `U'` of the shear's source `W₁`: the commutation of
`IsEmbeddedDesing` with local isomorphisms along the two injective local isomorphisms
`ι₁ : W₁ ↪ A₁` and `ι₂ ∘ g : W₁ → A₂` at the SAME `U'`
(`exists_diffeomorph_last_of_commutes_injective`, twice) gives the two last-stage diffeomorphisms
`G₁`, `G₂` from the value on `W₁|U'`;
`homOfPullbackEq` makes them isomorphisms `m₁ : Ỹ' ≅ Ỹ₁`, `m₂ : Ỹ' ≅ Ỹ₂` of the final strict
transforms and `ψ := m₂ ∘ m₁⁻¹`; the compatibility over the piece reduces to `Π₂ ∘ m₂ = Π₁ ∘ m₁`
(`localResolutionToPiece_comp_homOfPullbackEq_of_shear`). -/
theorem PieceEmbedding.exists_isIso_localResolution_of_shear_core :
    ∃ ψ : (E₁.padLeft m).localResolution bed 𝐔₁ h𝐔₁ ⟶ (E₂.padRight n).localResolution bed 𝐔₂ h𝐔₂,
      IsIso ψ ∧
      ψ ≫ (E₂.padRight n).localResolutionToPiece bed 𝐔₂ h𝐔₂ =
        (E₁.padLeft m).localResolutionToPiece bed 𝐔₁ h𝐔₁ := by
  have hkinj : Function.Injective 𝐤 := fun p q h => hbij.1 (Subtype.ext h)
  have hTT₂ : (𝐓₁').IsPullbackOf 𝐓₂ 𝐤 := by
    refine AnalyticTriple.IsPullbackOf.comp ((𝐓₂).isPullbackOf_pullback _ hι₂) ⟨hI, ?_⟩
    change (HypersurfaceFamily.empty _).comap _ = ((HypersurfaceFamily.empty _).comap _).comap _
    rw [HypersurfaceFamily.empty_comap, HypersurfaceFamily.empty_comap,
      HypersurfaceFamily.empty_comap]
  -- the commutation with local isomorphisms along `ι₁` and along `k`, at the same `U'`
  obtain ⟨G₁, hG₁sq, hG₁id⟩ := bed.exists_diffeomorph_last_of_commutes_injective hbed.2 ι₁ hι₁
    Subtype.val_injective 𝐓₁ 𝐓₁' ((𝐓₁).isPullbackOf_pullback _ hι₁)
    (E₁.padLeft m).domBEDan_ambientTriple h𝐓₁' U' hU'
  obtain ⟨G₂, hG₂sq, hG₂id⟩ := bed.exists_diffeomorph_last_of_commutes_injective hbed.2 𝐤 h𝐤
    hkinj 𝐓₂ 𝐓₁' hTT₂ (E₂.padRight n).domBEDan_ambientTriple h𝐓₁' U' hU'
  -- the induced morphisms of closed subspaces, twice
  have hm₁ : @IsIso (AnalyticSpace.{u} 𝕜) _ _ _
      (IdealSheaf.homOfPullbackEq ⇑G₁ G₁.contMDiff hG₁id) :=
    isIso_homOfPullbackEq_of_diffeomorph G₁ hG₁id
  have hm₂ : @IsIso (AnalyticSpace.{u} 𝕜) _ _ _
      (IdealSheaf.homOfPullbackEq ⇑G₂ G₂.contMDiff hG₂id) :=
    isIso_homOfPullbackEq_of_diffeomorph G₂ hG₂id
  -- the compatibility `Π₂ ∘ m₂ = Π₁ ∘ m₁`
  have key := PieceEmbedding.localResolutionToPiece_comp_homOfPullbackEq_of_shear E₁ E₂ bed W₁ W₂
    g hloc hI hmor U' hU' G₁ hG₁sq hG₁id G₂ hG₂sq hG₂id
  let m₁ : IdealSheaf.toAnalyticSpace 𝐘' ⟶ (E₁.padLeft m).localResolution bed 𝐔₁ h𝐔₁ :=
    IdealSheaf.homOfPullbackEq ⇑G₁ G₁.contMDiff hG₁id
  let m₂ : IdealSheaf.toAnalyticSpace 𝐘' ⟶ (E₂.padRight n).localResolution bed 𝐔₂ h𝐔₂ :=
    IdealSheaf.homOfPullbackEq ⇑G₂ G₂.contMDiff hG₂id
  -- the isomorphism `ψ := m₂ ∘ m₁⁻¹` and its compatibility
  refine ⟨m₂ ⊚ @inv (AnalyticSpace.{u} 𝕜) _ _ _ m₁ hm₁,
    @IsIso.comp_isIso (AnalyticSpace.{u} 𝕜) _ _ _ _
      (@inv (AnalyticSpace.{u} 𝕜) _ _ _ m₁ hm₁) m₂
      (@IsIso.inv_isIso (AnalyticSpace.{u} 𝕜) _ _ _ m₁ hm₁) hm₂, ?_⟩
  exact (Category.assoc _ _ _).trans
    ((@IsIso.inv_comp_eq (AnalyticSpace.{u} 𝕜) _ _ _ _ m₁ hm₁ _ _).mpr key)

end ShearCore

section Shear2

variable {n m : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E₁ : PieceEmbedding 𝕜 n X V) (E₂ : PieceEmbedding 𝕜 m X V)
  (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing) (x : X.restrictSet V)

include hbed in
/-- **The shear's isomorphism with the point clause on the right**: the shrunken open `U₂` of the
right-padded ambient also contains `s₂(i₂ x)` — the point clause of
`exists_padded_equivalence_hom_point` read at `U₂ := (ι₂ ∘ g)(U')`, `U' ∋ s₁(i₁ x)`. Used by
`localResolution_independent_local`, whose open `N` of the piece must lie over BOTH shrunken opens.
The argument: `exists_padded_equivalence_hom_point`, the shrinking lemma inside
`ι₁⁻¹ V₁ ∩ (ι₂ ∘ g)⁻¹ V₂` around `s₁(i₁ x)`, the core. -/
theorem PieceEmbedding.exists_isIso_localResolution_of_shear'
    (V₁ : Opens (pieceAmbient.{u} 𝕜 (E₁.padLeft m).G)) (hx₁ : (E₁.padLeft m).ambientPoint x ∈ V₁)
    (V₂ : Opens (pieceAmbient.{u} 𝕜 (E₂.padRight n).G))
    (hx₂ : (E₂.padRight n).ambientPoint x ∈ V₂) :
    ∃ (U₁ : Opens (pieceAmbient.{u} 𝕜 (E₁.padLeft m).G))
      (hU₁ : IsCompact (closure (U₁ : Set (pieceAmbient 𝕜 (E₁.padLeft m).G))))
      (U₂ : Opens (pieceAmbient.{u} 𝕜 (E₂.padRight n).G))
      (hU₂ : IsCompact (closure (U₂ : Set (pieceAmbient 𝕜 (E₂.padRight n).G)))),
      (E₁.padLeft m).ambientPoint x ∈ U₁ ∧ (E₂.padRight n).ambientPoint x ∈ U₂ ∧
      U₁ ≤ V₁ ∧ U₂ ≤ V₂ ∧
      ∃ ψ : (E₁.padLeft m).localResolution bed U₁ hU₁ ⟶ (E₂.padRight n).localResolution bed U₂ hU₂,
        IsIso ψ ∧
        ψ ≫ (E₂.padRight n).localResolutionToPiece bed U₂ hU₂ =
          (E₁.padLeft m).localResolutionToPiece bed U₁ hU₁ := by
  obtain ⟨W₁, W₂, g, hxW₁, hloc, hbij, ⟨hI, hmor⟩, hpt⟩ :=
    exists_padded_equivalence_hom_point E₁ E₂ x
  have hι₂ := isLocalDiffeomorph_inclusion (pieceAmbient.{u} 𝕜 (E₂.padRight n).G) W₂
  have hk : IsLocalDiffeomorph 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜) ω
      (((pieceAmbient.{u} 𝕜 (E₂.padRight n).G).inclusion W₂).comp g) :=
    BlowUpSequence.isLocalDiffeomorph_comp hι₂ hloc
  -- the point and a relatively compact open around it inside `ι₁⁻¹ V₁ ∩ (ι₂ ∘ g)⁻¹ V₂`
  let p₀ : (pieceAmbient.{u} 𝕜 (E₁.padLeft m).G).restrict W₁ :=
    ⟨(E₁.padLeft m).ambientPoint x, hxW₁⟩
  have hp₀ : p₀ ∈ preimageOpens ((pieceAmbient.{u} 𝕜 (E₁.padLeft m).G).inclusion W₁)
      ((pieceAmbient.{u} 𝕜 (E₁.padLeft m).G).inclusion W₁).contMDiff V₁ ⊓
      preimageOpens (((pieceAmbient.{u} 𝕜 (E₂.padRight n).G).inclusion W₂).comp g)
        (((pieceAmbient.{u} 𝕜 (E₂.padRight n).G).inclusion W₂).comp g).contMDiff V₂ := by
    refine Opens.mem_inf.mpr ⟨hx₁, ?_⟩
    change (g p₀).1 ∈ V₂
    rw [hpt x hxW₁]
    exact hx₂
  have : LocallyCompactSpace ((pieceAmbient.{u} 𝕜 (E₁.padLeft m).G).restrict W₁) :=
    locallyCompactSpace_of_finiteDimensional 𝕜 (Fin (n + m) → 𝕜)
      ((pieceAmbient.{u} 𝕜 (E₁.padLeft m).G).restrict W₁)
  obtain ⟨U', hp₀U', hU'le, hU'⟩ := exists_opens_isCompact_closure_mem_le _ hp₀
  obtain ⟨ψ, hψ, hcomp⟩ := PieceEmbedding.exists_isIso_localResolution_of_shear_core E₁ E₂ bed hbed
    W₁ W₂ g hloc hbij hI hmor U' hU'
  refine ⟨_, _, _, _, ?_, ?_, ?_, ?_, ψ, hψ, hcomp⟩
  · exact ⟨p₀, hp₀U', rfl⟩
  · exact ⟨p₀, hp₀U', hpt x hxW₁⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact (Opens.mem_inf.mp (hU'le hq)).1
  · rintro _ ⟨q, hq, rfl⟩
    exact (Opens.mem_inf.mp (hU'le hq)).2

include hbed in
/-- **The shear's isomorphism of padded resolutions on shrunken opens** ([Kol07, Theorem 36,
proof]): near `x`, relatively compact opens `U₁ ∋ s₁(i₁ x)` and `U₂` of the padded ambients,
inside any prescribed neighbourhoods `V₁`, `V₂`, whose local resolutions are isomorphic over the
piece — `exists_isIso_localResolution_of_shear'` without its right point clause. -/
theorem exists_isIso_localResolution_of_shear
    (V₁ : Opens (pieceAmbient.{u} 𝕜 (E₁.padLeft m).G)) (hx₁ : (E₁.padLeft m).ambientPoint x ∈ V₁)
    (V₂ : Opens (pieceAmbient.{u} 𝕜 (E₂.padRight n).G))
    (hx₂ : (E₂.padRight n).ambientPoint x ∈ V₂) :
    ∃ (U₁ : Opens (pieceAmbient.{u} 𝕜 (E₁.padLeft m).G))
      (hU₁ : IsCompact (closure (U₁ : Set (pieceAmbient 𝕜 (E₁.padLeft m).G))))
      (U₂ : Opens (pieceAmbient.{u} 𝕜 (E₂.padRight n).G))
      (hU₂ : IsCompact (closure (U₂ : Set (pieceAmbient 𝕜 (E₂.padRight n).G)))),
      (E₁.padLeft m).ambientPoint x ∈ U₁ ∧ U₁ ≤ V₁ ∧ U₂ ≤ V₂ ∧
      ∃ ψ : (E₁.padLeft m).localResolution bed U₁ hU₁ ⟶ (E₂.padRight n).localResolution bed U₂ hU₂,
        IsIso ψ ∧
        ψ ≫ (E₂.padRight n).localResolutionToPiece bed U₂ hU₂ =
          (E₁.padLeft m).localResolutionToPiece bed U₁ hU₁ := by
  obtain ⟨U₁, hU₁, U₂, hU₂, hxU₁, -, hle₁, hle₂, ψ, hψ, hcomp⟩ :=
    E₁.exists_isIso_localResolution_of_shear' E₂ bed hbed x V₁ hx₁ V₂ hx₂
  exact ⟨U₁, hU₁, U₂, hU₂, hxU₁, hle₁, hle₂, ψ, hψ, hcomp⟩

end Shear2

section

variable (𝕜)

/-- **The local independence of the embedding** ([Kol07, Theorem 36, proof]; [Wlo09, §4,
(3)⇒(4)]): near every point `x` of the piece over `W₁` and over `W₂`, an open `N ∋ x` of the piece
over both, over which the local resolutions of the two embeddings are isomorphic compatibly with
the maps to the piece. The three legs of Kollár's proof in the relation "isomorphic over `N`",
composed by `exists_restrictSet_isIso_trans`/`_symm`: (γ) from `W₁` down to `W₁' := s₁⁻¹ U₁`
(`exists_restrictSet_isIso_localResolution_of_le`), (α) at the left padding
(`exists_isIso_localResolution_padAlong`, through `exists_restrictSet_isIso_of_comp_eq`), (β) the
shear between the two paddings on the shrunken opens `U₁ ∋ s₁(i₁ x)`, `U₂ ∋ s₂(i₂ x)` inside
`p₁⁻¹ W₁`, `p₂⁻¹ W₂` (`exists_isIso_localResolution_of_shear'`), (α) at the right padding, (γ)
back up from `W₂' := s₂⁻¹ U₂` to `W₂`; `N := (E₁ over W₁') ∩ (E₂ over W₂')`. The global form is
`localResolution_independent_of_local` (`LocalResolutionIndependent.lean`). -/
theorem localResolution_independent_local {X : AnalyticSpace.{u} 𝕜} {V : Set X}
    {n m : ℕ} (E₁ : PieceEmbedding 𝕜 n X V) (E₂ : PieceEmbedding 𝕜 m X V)
    (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
    (W₁ : Opens (pieceAmbient.{u} 𝕜 E₁.G))
    (hW₁ : IsCompact (closure (W₁ : Set (pieceAmbient 𝕜 E₁.G))))
    (W₂ : Opens (pieceAmbient.{u} 𝕜 E₂.G))
    (hW₂ : IsCompact (closure (W₂ : Set (pieceAmbient 𝕜 E₂.G))))
    (x : X.restrictSet V) (hx₁ : x ∈ E₁.embPreimage W₁) (hx₂ : x ∈ E₂.embPreimage W₂) :
    ∃ N : Set (X.restrictSet V), IsOpen N ∧ x ∈ N ∧ N ⊆ E₁.embPreimage W₁ ∩ E₂.embPreimage W₂ ∧
      ∃ ψ : (E₁.localResolution bed W₁ hW₁).restrictSet (E₁.localResolutionToPiece bed W₁ hW₁ ⁻¹'
          N) ⟶ (E₂.localResolution bed W₂ hW₂).restrictSet
          (E₂.localResolutionToPiece bed W₂ hW₂ ⁻¹' N),
        IsIso ψ ∧
        ψ ≫ (E₂.localResolutionToPiece bed W₂ hW₂).restrictSet N =
          (E₁.localResolutionToPiece bed W₁ hW₁).restrictSet N := by
  -- the padded neighbourhoods `p₁⁻¹ W₁ ∋ s₁(i₁ x)`, `p₂⁻¹ W₂ ∋ s₂(i₂ x)`
  have hxV₁ : (E₁.padLeft m).ambientPoint x ∈ preimageOpens (padCoordProj (Fin.castAddEmb m) E₁.G)
      (contMDiff_padCoordProj (Fin.castAddEmb m) E₁.G) W₁ := by
    change padCoordProj (Fin.castAddEmb m) E₁.G ((E₁.padLeft m).ambientPoint x) ∈ W₁
    rw [ambientPoint_padLeft E₁ x, padCoordProj_padExt]
    exact hx₁
  have hxV₂ : (E₂.padRight n).ambientPoint x ∈ preimageOpens (padCoordProj (Fin.natAddEmb n) E₂.G)
      (contMDiff_padCoordProj (Fin.natAddEmb n) E₂.G) W₂ := by
    change padCoordProj (Fin.natAddEmb n) E₂.G ((E₂.padRight n).ambientPoint x) ∈ W₂
    rw [ambientPoint_padRight E₂ x, padCoordProj_padExt]
    exact hx₂
  -- (β): the shear's isomorphism on shrunken opens `U₁ ≤ p₁⁻¹ W₁`, `U₂ ≤ p₂⁻¹ W₂`
  obtain ⟨U₁, hU₁, U₂, hU₂, hxU₁, hxU₂, hle₁, hle₂, ψβ, hψβ, hβ⟩ :=
    E₁.exists_isIso_localResolution_of_shear' E₂ bed hbed x _ hxV₁ _ hxV₂
  -- the shrunken opens of the unpadded ambients `W₁' := s₁⁻¹ U₁ ≤ W₁`, `W₂' := s₂⁻¹ U₂ ≤ W₂`
  have hle₁' : preimageOpens (padExt (Fin.castAddEmb m) E₁.G) (contMDiff_padExt _ _) U₁ ≤ W₁ := by
    intro w hw
    have h := hle₁ hw
    change padCoordProj (Fin.castAddEmb m) E₁.G (padExt (Fin.castAddEmb m) E₁.G w) ∈ W₁ at h
    rwa [padCoordProj_padExt] at h
  have hle₂' : preimageOpens (padExt (Fin.natAddEmb n) E₂.G) (contMDiff_padExt _ _) U₂ ≤ W₂ := by
    intro w hw
    have h := hle₂ hw
    change padCoordProj (Fin.natAddEmb n) E₂.G (padExt (Fin.natAddEmb n) E₂.G w) ∈ W₂ at h
    rwa [padCoordProj_padExt] at h
  -- (α) at both paddings
  obtain ⟨ψα₁, hψα₁, hα₁⟩ :=
    E₁.exists_isIso_localResolution_padAlong (Fin.castAddEmb m) bed hbed U₁ hU₁
  obtain ⟨ψα₂, hψα₂, hα₂⟩ :=
    E₂.exists_isIso_localResolution_padAlong (Fin.natAddEmb n) bed hbed U₂ hU₂
  -- the open `N` of the piece over both shrunken opens
  refine ⟨E₁.embPreimage (preimageOpens (padExt (Fin.castAddEmb m) E₁.G) (contMDiff_padExt _ _)
      U₁) ∩
      E₂.embPreimage (preimageOpens (padExt (Fin.natAddEmb n) E₂.G) (contMDiff_padExt _ _) U₂),
    (E₁.isOpen_embPreimage _).inter (E₂.isOpen_embPreimage _), ⟨?_, ?_⟩,
    Set.inter_subset_inter (fun _ hy => hle₁' hy) (fun _ hy => hle₂' hy), ?_⟩
  · change padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint x) ∈ U₁
    rw [← ambientPoint_padLeft E₁ x]
    exact hxU₁
  · change padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint x) ∈ U₂
    rw [← ambientPoint_padRight E₂ x]
    exact hxU₂
  -- the chain (γ)₁ · (α₁)⁻¹ · (β) · (α₂) · (γ)₂⁻¹, each isomorphism read as the relation over `N`
  exact AnalyticSpace.exists_restrictSet_isIso_trans _ _ _ _
    (AnalyticSpace.exists_restrictSet_isIso_trans _ _ _ _
      (AnalyticSpace.exists_restrictSet_isIso_trans _ _ _ _
        (AnalyticSpace.exists_restrictSet_isIso_trans _ _ _ _
          (E₁.exists_restrictSet_isIso_localResolution_of_le bed W₁ hW₁
            (preimageOpens (padExt (Fin.castAddEmb m) E₁.G) (contMDiff_padExt _ _) U₁)
            (isCompact_closure_preimage_padExt _ _ U₁ hU₁) hle₁' _
            ((E₁.isOpen_embPreimage _).inter (E₂.isOpen_embPreimage _)) Set.inter_subset_left)
          (AnalyticSpace.exists_restrictSet_isIso_symm _ _ _
            (AnalyticSpace.exists_restrictSet_isIso_of_comp_eq ψα₁ hψα₁ _ _ hα₁ _)))
        (AnalyticSpace.exists_restrictSet_isIso_of_comp_eq ψβ hψβ _ _ hβ _))
      (AnalyticSpace.exists_restrictSet_isIso_of_comp_eq ψα₂ hψα₂ _ _ hα₂ _))
    (AnalyticSpace.exists_restrictSet_isIso_symm _ _ _
      (E₂.exists_restrictSet_isIso_localResolution_of_le bed W₂ hW₂
        (preimageOpens (padExt (Fin.natAddEmb n) E₂.G) (contMDiff_padExt _ _) U₂)
        (isCompact_closure_preimage_padExt _ _ U₂ hU₂) hle₂' _
        ((E₁.isOpen_embPreimage _).inter (E₂.isOpen_embPreimage _)) Set.inter_subset_right))

end

end Hironaka.Manifold

end
