/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceEmbedding
public import Hironaka.AnalyticSpace.Manifold.Chart
public import Mathlib.Analysis.InnerProductSpace.Basic
import Hironaka.AnalyticSpace.ClosedSubspaceLemmas
import Hironaka.AnalyticSpace.Manifold.Sigma
import Hironaka.AnalyticSpace.RegDensityLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.SigmaDesc
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init

/-!
# Pieces from local models: the existence of local embedding data

Every point of an analytic `K`-space has a neighbourhood `K`-isomorphic to a local analytic
`K`-space `(S(𝓘), 𝒜_G/𝓘)`, `G ⊆ Kⁿ` open [Hir64, Ch. 0, §1, pp. 119–120]
(`exists_kIso_localModel`); for a relatively compact open `U` finitely many such models cover the
compact `closure U`. This module turns those models into the `LocalEmbeddingData` of
`PieceEmbedding.lean`:

* the **bridge** `modelBridge G' : (G', 𝒜_{G'}) ≅ Sp(pieceAmbient 𝕜 (downOpens G'))` — the model
  open `G' ⊆ Kn 𝕜 n` (the universe-lifted `Kⁿ`) read as an open of `Fin n → 𝕜`, and the one-piece
  `Σ`-ambient identified with it by two inverse analytic maps (`ofManifoldIso`,
  `ofManifold_restrictOpen_iso`; `ContMDiff.sigmaDesc`, `contMDiff_sigmaMk_comp_iff`);
* the **transport** of the model's ideal `𝓘 = (f₁, …, f_k)` along the bridge (`transportIdeal`,
  `quotient_kIso`): `modelPieceIdeal G' f` with `Sp(A)/𝓘 ≅ (S(𝓘), 𝒜/𝓘)`, hence the piece's model
  isomorphism `X|_V ≅ Sp(A)/𝓘` (`modelPieceEmbIso`), and its reducedness on a reduced `X` (the
  closed subspace is `X|_V`, whose stalks are reduced; `ClosedSubspace.isReduced_iff`);
* the **shrinking** of a finite cover of `closure U` to inner opens with compact closures
  (`exists_inner_opens_of_isCompact_closure`; the space is locally compact Hausdorff);
* the **padding** to one common dimension `n' := max n_V + 1` (Włodarczyk's common ambient
  dimension [Wlo09, §7.1]; Kollár's freedom to enlarge the affine space of an embedding
  [Kol07, Theorem 36, proof]), through the interface `PadTools`, whose fields are the padding
  constructions of `PadIdeal.lean` (instantiated in `PieceModelPad.lean`); the padding is what
  makes the ideal of a model with `k = 0` equations nonzero at every stalk, as
  `PieceEmbedding.isNonzeroEverywhere` requires;
* the **assembly** `exists_localEmbeddingData_of_padTools`: the pointwise models at the points of
  the compact `closure U`, a finite subcover, the shrinking, the padded pieces.

No new mathematics: Hironaka's definition of an analytic space, the local models, and
Włodarczyk's padding. Kollár's requirement `dim 𝔸 ≥ dim X + 2` on the embedding
[Kol07, Corollary 22, proof] is not needed: the argument follows Włodarczyk, whose local models
are minimal embeddings into open subsets of `ℂⁿ` [Wlo09, §4, (3)⇒(4)], with the freedom to use any
closed embedding coming from the commutation of the resolution with embeddings of ambient
manifolds [Wlo09, §7.1].
-/

@[expose] public section

open TopologicalSpace AnalyticSpace KLocallyRingedSpace
open CategoryTheory
open scoped Manifold ContDiff

universe u

noncomputable section

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

/-- Mathlib's `ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff` for `ContMDiff`, with the two
manifolds in independent universes (`contMDiff_subtypeVal_comp_iff'` fixes one universe for both;
here the opens of `Fin n → 𝕜` live in `Type` and those of `Kn 𝕜 n` in `Type u`). -/
theorem contMDiff_subtypeVal_comp_iff_of_opens {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] {N : Type*} [TopologicalSpace N] [ChartedSpace E' N]
    {m : WithTop ℕ∞} {U : Opens N} (g : M → U) :
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') m (Subtype.val ∘ g) ↔ ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') m g :=
  forall_congr' fun x => ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff g Set.univ x

/-- An open `G' ⊆ Kn 𝕜 n` of the universe-lifted model of `Kⁿ`, read as an open of
`Fin n → 𝕜`. -/
def downOpens (G' : Opens (Kn.{u} 𝕜 n)) : Opens (Fin n → 𝕜) :=
  ⟨ULift.up ⁻¹' (G' : Set (Kn.{u} 𝕜 n)), G'.isOpen.preimage continuous_uliftUp⟩

/-- The points of the one-piece ambient of `downOpens G'` mapped onto `G'`. -/
def toLiftOpens (G' : Opens (Kn.{u} 𝕜 n)) :
    (pieceAmbient 𝕜 (downOpens G') : Type u) → G' :=
  fun p => ⟨ULift.up p.2.1, p.2.2⟩

/-- The inverse of `toLiftOpens`. -/
def ofLiftOpens (G' : Opens (Kn.{u} 𝕜 n)) :
    G' → (pieceAmbient 𝕜 (downOpens G') : Type u) :=
  fun y => ⟨PUnit.unit, ⟨y.1.down, y.2⟩⟩

/-- `toLiftOpens` is analytic (`ContMDiff.sigmaDesc` on the one-point `Σ`, and the lifted
coordinates). -/
theorem contMDiff_toLiftOpens (G' : Opens (Kn.{u} 𝕜 n)) :
    ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Kn.{u} 𝕜 n) ω (toLiftOpens G') := by
  have h0 : ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Kn.{u} 𝕜 n) ω
      (fun x : downOpens G' => (⟨ULift.up x.1, x.2⟩ : G')) := by
    refine (contMDiff_subtypeVal_comp_iff_of_opens (𝕜 := 𝕜) (E := Fin n → 𝕜) (E' := Kn.{u} 𝕜 n)
      (fun x : downOpens G' => (⟨ULift.up x.1, x.2⟩ : G'))).mp ?_
    exact (contMDiff_ulift_coord (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))).comp
      contMDiff_subtype_val
  exact ContMDiff.sigmaDesc (M := fun _ : PUnit.{u + 1} => (downOpens G' : Type)) fun _ => h0

/-- `ofLiftOpens` is analytic (`contMDiff_sigmaMk_comp_iff`). -/
theorem contMDiff_ofLiftOpens (G' : Opens (Kn.{u} 𝕜 n)) :
    ContMDiff 𝓘(𝕜, Kn.{u} 𝕜 n) 𝓘(𝕜, Fin n → 𝕜) ω (ofLiftOpens G') := by
  have h0 : ContMDiff 𝓘(𝕜, Kn.{u} 𝕜 n) 𝓘(𝕜, Fin n → 𝕜) ω
      (fun y : G' => (⟨y.1.down, y.2⟩ : downOpens G')) := by
    refine (contMDiff_subtypeVal_comp_iff_of_opens (𝕜 := 𝕜) (E := Kn.{u} 𝕜 n) (E' := Fin n → 𝕜)
      (fun y : G' => (⟨y.1.down, y.2⟩ : downOpens G'))).mp ?_
    exact (contMDiff_coord_down (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))).comp
      contMDiff_subtype_val
  exact (contMDiff_sigmaMk_comp_iff (I := 𝓘(𝕜, Fin n → 𝕜)) (J := 𝓘(𝕜, Kn.{u} 𝕜 n)) (n := ω)
    (M := fun _ : PUnit.{u + 1} => (downOpens G' : Type)) (P := G') (i := PUnit.unit)
    (h := fun y : G' => (⟨y.1.down, y.2⟩ : downOpens G'))).mpr h0

/-- `Sp(pieceAmbient (downOpens G')) ≅ Sp(G')`: the one-piece ambient is the open itself, as
`𝕜`-local-ringed spaces. -/
def pieceAmbientLiftIso (G' : Opens (Kn.{u} 𝕜 n)) :
    KIso (ofManifold 𝕜 (Fin n → 𝕜) (pieceAmbient 𝕜 (downOpens G') : Type u))
      (ofManifold 𝕜 (Kn.{u} 𝕜 n) G') :=
  ofManifoldIso (toLiftOpens G') (ofLiftOpens G') (contMDiff_toLiftOpens G')
    (contMDiff_ofLiftOpens G') (fun p => by rcases p with ⟨⟨⟩, x⟩; rfl) (fun y => rfl)

/-- The bridge from the model open `(G', 𝒜_{G'})` of Hironaka's local analytic spaces
[Hir64, Ch. 0, §1, p. 119] to the space of the one-piece ambient manifold of `downOpens G'`
(`ofManifold_restrictOpen_iso`). -/
def modelBridge (G' : Opens (Kn.{u} 𝕜 n)) :
    KIso (analyticSpaceOfOpen 𝕜 n G')
      (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (pieceAmbient 𝕜 (downOpens G'))).toKLocallyRingedSpace :=
  (ofManifold_restrictOpen_iso (K := 𝕜) (E := Kn.{u} 𝕜 n) (M := Kn.{u} 𝕜 n) G').trans
    (pieceAmbientLiftIso G').symm

/-! ### The model ideal transported to the one-piece ambient -/

/-- The ideal `𝓘 = (f₁, …, f_k)` of a local model `(S(𝓘), 𝒜_{G'}/𝓘)` [Hir64, Ch. 0, §1,
p. 119], transported along the bridge to an ideal sheaf on the one-piece ambient manifold
(`transportIdeal`). -/
def modelPieceIdeal (G' : Opens (Kn.{u} 𝕜 n)) {k : ℕ} (f : Fin k → AnalyticFun 𝕜 n G') :
    AnalyticManifold.IdealSheaf (pieceAmbient 𝕜 (downOpens G')) :=
  transportIdeal (modelBridge G').symm (modelIdeal 𝕜 n G' f)

/-- `Sp(A)/𝓘 ≅ (S(𝓘), 𝒜_{G'}/𝓘)` (`quotient_kIso`): the closed subspace of the one-piece ambient
cut out by the transported ideal is the local model. -/
def modelPieceIdealIso (G' : Opens (Kn.{u} 𝕜 n)) {k : ℕ} (f : Fin k → AnalyticFun 𝕜 n G') :
    KIso (modelPieceIdeal G' f).toAnalyticSpace.toKLocallyRingedSpace (localModel 𝕜 n G' f) :=
  quotient_kIso (modelBridge G').symm (modelIdeal 𝕜 n G' f)

variable {X : AnalyticSpace.{u} 𝕜}

/-- A `K`-isomorphism of the underlying `K`-local-ringed spaces, as an isomorphism of analytic
`K`-spaces (the category's morphisms are those `K`-morphisms). -/
def analyticIsoOfKIso {A B : AnalyticSpace.{u} 𝕜}
    (e : KIso A.toKLocallyRingedSpace B.toKLocallyRingedSpace) : A ≅ B where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-- The model isomorphism `X|_V ≅ Sp(A)/𝓘` of a piece, from the local model isomorphism
`X|_V ≅ (S(𝓘), 𝒜/𝓘)` of `exists_kIso_localModel` [Hir64, Ch. 0, §1, pp. 119–120], as an
isomorphism of analytic spaces. -/
def modelPieceEmbIso {V : Opens X} (G' : Opens (Kn.{u} 𝕜 n)) {k : ℕ}
    (f : Fin k → AnalyticFun 𝕜 n G')
    (e : KIso (X.toKLocallyRingedSpace.restrictOpen V) (localModel 𝕜 n G' f)) :
    @CategoryTheory.Iso (AnalyticSpace.{u} 𝕜) _
      (restrictSet X (V : Set X))
          (modelPieceIdeal G' f).toAnalyticSpace :=
  eqToIso (congrArg X.restrictOpen (openOf_of_isOpen X V.isOpen)) ≪≫
    analyticIsoOfKIso (A := X.restrictOpen V) (e.trans (modelPieceIdealIso G' f).symm)

/-- The model isomorphism as the `emb` field of a `PieceEmbedding`. -/
def modelPieceEmb {V : Opens X} (G' : Opens (Kn.{u} 𝕜 n)) {k : ℕ} (f : Fin k → AnalyticFun 𝕜 n G')
    (e : KIso (X.toKLocallyRingedSpace.restrictOpen V) (localModel 𝕜 n G' f)) :
    restrictSet X (V : Set X) ⟶ (modelPieceIdeal G' f).toAnalyticSpace :=
  (modelPieceEmbIso G' f e).hom

/-- The `emb_isIso` field of the `PieceEmbedding` built from a local model. -/
theorem modelPieceEmb_isIso {V : Opens X} (G' : Opens (Kn.{u} 𝕜 n)) {k : ℕ}
    (f : Fin k → AnalyticFun 𝕜 n G')
    (e : KIso (X.toKLocallyRingedSpace.restrictOpen V) (localModel 𝕜 n G' f)) :
    IsIso (modelPieceEmb G' f e) := by
  unfold modelPieceEmb
  exact ⟨⟨(modelPieceEmbIso G' f e).inv, (modelPieceEmbIso G' f e).hom_inv_id,
    (modelPieceEmbIso G' f e).inv_hom_id⟩⟩

/-- On a reduced space the transported model ideal is reduced: its closed subspace is `X|_V`,
whose stalks are reduced (`ClosedSubspace.isReduced_iff`, `isReduced_stalk_of_kIso`,
`isReduced_stalk_restrictOpen_iff`; a space is reduced when its local rings have no nilpotent
elements, [Hir64, Introduction]). -/
theorem isReduced_modelPieceIdeal (hX : AnalyticSpace.IsReduced X)
    {V : Opens X}
    (G' : Opens (Kn.{u} 𝕜 n)) {k : ℕ} (f : Fin k → AnalyticFun 𝕜 n G')
    (e : KIso (X.toKLocallyRingedSpace.restrictOpen V) (localModel 𝕜 n G' f)) :
    (modelPieceIdeal G' f).IsReduced := by
  refine (ClosedSubspace.isReduced_iff (X := toSpace
    (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (pieceAmbient 𝕜 (downOpens G')))
    (modelPieceIdeal G' f)).mp ?_
  intro y
  let i : KIso (modelPieceIdeal G' f).toAnalyticSpace.toKLocallyRingedSpace
      (X.toKLocallyRingedSpace.restrictOpen V) := (modelPieceIdealIso G' f).trans e.symm
  have h1 : _root_.IsReduced ((X.toKLocallyRingedSpace.restrictOpen
      V).toLocallyRingedSpace.presheaf.stalk
      (i.hom.1.base y)) :=
    (isReduced_stalk_restrictOpen_iff X.toKLocallyRingedSpace V _).mpr (hX _)
  have h2 := isReduced_stalk_of_kIso i.symm (i.hom.1.base y) h1
  have h3 : i.symm.hom.1.base (i.hom.1.base y) = y := by
    change (i.hom ≫ i.inv).1.base y = y
    rw [i.hom_inv_id]
    rfl
  rw [h3] at h2
  exact h2


/-! ### The shrinking of a finite cover -/

/-- Shrinking a finite open cover of a relatively compact set to inner opens with compact
closures inside the cover's members, still covering the set (Mathlib's
`IsCompact.finite_compact_cover` followed by `exists_open_between_and_isCompact_closure`; the
space is locally compact Hausdorff). These are the inner opens `V_i ⊆ W_i ⊆ U_i` with compact
closures of [Wlo09, §4, (3)⇒(4)]. -/
theorem exists_inner_opens_of_isCompact_closure {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] {U : Set X} (hU : IsCompact (closure U)) {ι : Type*}
    [Finite ι] (V : ι → Set X) (hV : ∀ i, IsOpen (V i)) (hcov : closure U ⊆ ⋃ i, V i) :
    ∃ W : ι → Set X, (∀ i, IsOpen (W i)) ∧ (∀ i, IsCompact (closure (W i))) ∧
      (∀ i, closure (W i) ⊆ V i) ∧ U ⊆ ⋃ i, W i := by
  cases nonempty_fintype ι
  have hcov' : closure U ⊆ ⋃ i ∈ (Finset.univ : Finset ι), V i := by
    simpa using hcov
  obtain ⟨K, hKc, hKV, hsK⟩ :=
    hU.finite_compact_cover (Finset.univ : Finset ι) V (fun i _ => hV i) hcov'
  choose W hWo hKW hWV hWc using fun i =>
    exists_open_between_and_isCompact_closure (hKc i) (hV i) (hKV i)
  refine ⟨W, hWo, hWc, hWV, ?_⟩
  refine subset_closure.trans ?_
  rw [hsK]
  simp only [Finset.mem_univ, Set.iUnion_true]
  exact Set.iUnion_mono fun i => hKW i

/-! ### The assembly: local embedding data from the local models, padded -/

/-- The padding tools the existence proof uses, as an interface: for `m ≤ n'` the padded
ambient `G × 𝕜^{n'-m}` and the padded ideal `𝓘 + (z_{m+1}, …, z_{n'})`, the transport of
reducedness, the nonvanishing at every stalk for `m < n'`, and the slice isomorphism of closed
subspaces `Sp/𝓘_pad ≅ Sp/𝓘` (Włodarczyk's passage to a common ambient dimension [Wlo09, §7.1]).
The fields are the constructions of `PadIdeal.lean`, instantiated in `PieceModelPad.lean`. -/
structure PadTools (𝕜 : Type) [RCLike 𝕜] where
  padOpens : ∀ {m n' : ℕ}, m ≤ n' → Opens (Fin m → 𝕜) → Opens (Fin n' → 𝕜)
  padIdeal : ∀ {m n' : ℕ} (h : m ≤ n') {G : Opens (Fin m → 𝕜)},
    AnalyticManifold.IdealSheaf (pieceAmbient.{u} 𝕜 G) →
      AnalyticManifold.IdealSheaf (pieceAmbient.{u} 𝕜 (padOpens h G))
  isReduced : ∀ {m n' : ℕ} (h : m ≤ n') {G : Opens (Fin m → 𝕜)}
    (J : AnalyticManifold.IdealSheaf (pieceAmbient.{u} 𝕜 G)), J.IsReduced →
        (padIdeal h J).IsReduced
  isNonzeroEverywhere : ∀ {m n' : ℕ} (h : m ≤ n'), m < n' → ∀ {G : Opens (Fin m → 𝕜)}
    (J : AnalyticManifold.IdealSheaf (pieceAmbient.{u} 𝕜 G)), (padIdeal h J).IsNonzeroEverywhere
  iso : ∀ {m n' : ℕ} (h : m ≤ n') {G : Opens (Fin m → 𝕜)}
    (J : AnalyticManifold.IdealSheaf (pieceAmbient.{u} 𝕜 G)),
    @CategoryTheory.Iso (AnalyticSpace.{u} 𝕜) _ (padIdeal h J).toAnalyticSpace
      J.toAnalyticSpace

/-- The `PieceEmbedding` of a local model of `X|_V` in `K^m`, padded to the common dimension
`n' > m` by `z ↦ (z, 0)` with the equations `z_{m+1}, …, z_{n'}` added [Wlo09, §7.1]; the padding
supplies the nonvanishing of the ideal at every stalk. -/
def pieceOfModel (T : PadTools.{u} 𝕜) {V : Opens X} {m : ℕ} (G' : Opens (Kn.{u} 𝕜 m)) {k : ℕ}
    (f : Fin k → AnalyticFun 𝕜 m G')
    (e : KIso (X.toKLocallyRingedSpace.restrictOpen V) (localModel 𝕜 m G' f))
    (hX : AnalyticSpace.IsReduced X) {n' : ℕ} (h : m < n') :
    PieceEmbedding 𝕜 n' X (V : Set X) where
  G := T.padOpens h.le (downOpens G')
  ideal := T.padIdeal h.le (modelPieceIdeal G' f)
  isNonzeroEverywhere := T.isNonzeroEverywhere h.le h _
  isReduced := T.isReduced h.le _ (isReduced_modelPieceIdeal hX G' f e)
  emb := (modelPieceEmbIso G' f e ≪≫ (T.iso h.le (modelPieceIdeal G' f)).symm).hom
  emb_isIso := by
    exact ⟨⟨(modelPieceEmbIso G' f e ≪≫ (T.iso h.le (modelPieceIdeal G' f)).symm).inv,
      (modelPieceEmbIso G' f e ≪≫ (T.iso h.le (modelPieceIdeal G' f)).symm).hom_inv_id,
      (modelPieceEmbIso G' f e ≪≫ (T.iso h.le (modelPieceIdeal G' f)).symm).inv_hom_id⟩⟩

/-- Given the padding tools, every relatively compact open `U` of a reduced analytic space has
local embedding data: finitely many pieces (the local models [Hir64, Ch. 0, §1, pp. 119–120] at
the points of the compact `closure U`), inner opens with compact closures covering `U`, and one
common dimension `n' := max n_V + 1` (the local embeddings of [Wlo09, §4, (3)⇒(4)] and
[Kol07, Corollary 22, proof], padded as in [Wlo09, §7.1]). -/
theorem exists_localEmbeddingData_of_padTools (T : PadTools.{u} 𝕜)
    (hX : AnalyticSpace.IsReduced X) (U : Set X)
        (hUc : IsCompact (closure U)) :
    Nonempty (LocalEmbeddingData 𝕜 X U) := by
  classical
  choose Vx hxV nx kx Gx fx ex using
    fun x : closure U => exists_kIso_localModel X x.1
  obtain ⟨t, ht⟩ := hUc.elim_finite_subcover (fun x : closure U => (Vx x : Set X))
    (fun x => (Vx x).isOpen) (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩)
  have hcov : closure U ⊆ ⋃ i : t, (Vx i.1 : Set X) := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (ht hy)
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hyi⟩
  obtain ⟨W, hWo, hWc, hWV, hUW⟩ := exists_inner_opens_of_isCompact_closure hUc
    (fun i : t => (Vx i.1 : Set X)) (fun i => (Vx i.1).isOpen) hcov
  have hlt : ∀ i : t, nx i.1 < t.sup (fun x => nx x) + 1 :=
    fun i => Nat.lt_succ_of_le (Finset.le_sup (f := fun x => nx x) i.2)
  exact ⟨{ n := t.sup (fun x => nx x) + 1
           ι := t
           piece := fun i => (Vx i.1 : Set X)
           isOpen_piece := fun i => (Vx i.1).isOpen
           inner := W
           isOpen_inner := hWo
           isCompact_closure_inner := hWc
           closure_inner_subset := hWV
           subset_iUnion_inner := hUW
           embedding := fun i =>
             pieceOfModel T (Gx i.1) (fx i.1) (Classical.choice (ex i.1)) hX (hlt i) }⟩

end Hironaka.Manifold

end
