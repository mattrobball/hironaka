/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.ShrunkEmbeddingCover
import Hironaka.Manifold.Exhaustion
import Hironaka.Manifold.FiniteSuccession.Functor.LocalTriples
import Hironaka.Resolution.Analytic.OrderReduction.LocalMaximalContact
import Hironaka.Resolution.Analytic.OrderReduction.SigmaContact
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Step 3 of Theorem 103 in the compatible-family form: the finite cover of a compact closure

Step 3 of the proof of [Kol07, Theorem 103] covers `X` by open subsets `X^{(j)}` on each of which
"there is a smooth hypersurface of maximal contact". In the compatible-family
form the value of a functor is read on a relatively compact open `U`, so only the compact closure
of `U` has to be covered: finitely many of the neighbourhoods with maximal contact of
[Kol07, Theorem 80 (2)] (`exists_isPullbackOf_localMCClass`, `LocalMaximalContact.lean`), embedded
by `ιᵢ : Nᵢ → M`, suffice, and each is shrunk to an open `Wᵢ` with compact closure inside the range
of `ιᵢ` (the manifold is locally compact), so that the pieces `ιᵢ^{-1}(Wᵢ ∩ U)` are relatively
compact in the charts. The data are bundled as `ShrunkMCCover T m U`, a shrunk embedding cover
(`ShrunkMCCover.toCover : ShrunkEmbeddingCover M U`, `ShrunkEmbeddingCover.lean`) with maximal
contact on the pieces. The coproduct `⊔ᵢ Nᵢ` carries the pull-back triple of `T`, which has a global
hypersurface of maximal contact (`localMCClass_pullback_sigmaDescMap`, `SigmaContact.lean`); the
open `⊔ᵢ ιᵢ^{-1}(Wᵢ ∩ U)` has compact closure, and the restriction of the coproduct map to it is
Kollár's `g : X^* → X` over `U`, surjective onto `U` and a coproduct of open embeddings (the lemmas
of `ShrunkEmbeddingCover`, restated on `ShrunkMCCover`).

* `AnalyticTriple.exists_finite_shrunk_mcCover` — the existence of the cover;
* `ShrunkMCCover`, `exists_shrunkMCCover` — the data and their existence;
* `ShrunkMCCover.sigma`, `desc`, `triple`, `localMCClass_triple` — the coproduct, the coproduct
  map and the pulled-back triple, in the class `LocalMCClass m`;
* `ShrunkMCCover.opens`, `isCompact_closure_opens`, `image_opens_eq` — the open
  `⊔ᵢ ιᵢ^{-1}(Wᵢ ∩ U)`, relatively compact, mapping onto `U`;
* `ShrunkMCCover.coverMap`, `surjective_coverMap`, `isCoprodOfOpenEmbeddings_coverMap` — the
  cover map `⊔ᵢ ιᵢ^{-1}(Wᵢ ∩ U) → U`;
* `AnalyticFamilyFunctor.CommutesWithLocalIsos.seqOn_eq_of_image_eq` — the commutation of a family
  functor with a local isomorphism, for a named image open.

The descent of a family functor's value along this cover is in `GlobalizeFamDescent.lean`.
-/

@[expose] public section
noncomputable section

open Set Topology TopologicalSpace Function
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

namespace AnalyticTriple

/-- A compact set of a triple of the class `BOClass m` is covered by finitely many opens `Wᵢ` with
compact closures, each inside the range of an open embedding `ιᵢ : Nᵢ → M` whose pulled-back
triple has a hypersurface of maximal contact (Step 3 of the proof of [Kol07, Theorem 103] with
[Kol07, Theorem 80 (2)], on a compact set). Each point has such a neighbourhood
(`exists_isPullbackOf_localMCClass`), which contains a compact neighbourhood of the point by local
compactness; finitely many of their interiors cover the compact set. -/
theorem exists_finite_shrunk_mcCover {m : ℕ} {T : AnalyticTriple ψ₀ M} (hT : BOClass m T)
    {K : Set M} (hK : IsCompact K) :
    ∃ (t : Finset M) (N : t → AnalyticManifold.{u} 𝕜 E) (ι : ∀ i, AnalyticMap (N i) M)
      (hι : ∀ i, IsAnalyticOpenEmbedding (ι i)) (W : t → Opens M),
      (∀ i, HasMaximalContact m (T.pullback (ι i) (hι i).1)) ∧
        (∀ i, IsCompact (closure (W i : Set M))) ∧ (∀ i, closure (W i : Set M) ⊆ range (ι i)) ∧
          K ⊆ ⋃ i, (W i : Set M) := by
  have := finiteDimensional_of_chartIso ψ₀
  have : LocallyCompactSpace M := locallyCompactSpace_of_finiteDimensional 𝕜 E M
  choose N T' g hg hx hT' hL using exists_isPullbackOf_localMCClass hT
  have hcpt : ∀ x : M, ∃ Kx : Set M, IsCompact Kx ∧ x ∈ interior Kx ∧ Kx ⊆ range (g x) :=
    fun x => exists_compact_subset (hg x).isOpen_range (hx x)
  choose Kx hKx hxK hKsub using hcpt
  obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover (fun x => interior (Kx x))
    fun x _ => isOpen_interior.mem_nhds (hxK x)
  refine ⟨t, fun i => N i.1, fun i => g i.1, fun i => hg i.1,
    fun i => ⟨interior (Kx i.1), isOpen_interior⟩, fun i => ?_, fun i => ?_, fun i => ?_, ?_⟩
  · have e : T' i.1 = T.pullback (g i.1) (hg i.1).1 :=
      IsPullbackOf.eq (hT' i.1) (T.isPullbackOf_pullback _ _)
    rw [← e]
    exact (hL i.1).2
  · exact (hKx i.1).of_isClosed_subset isClosed_closure
      (closure_minimal interior_subset (hKx i.1).isClosed)
  · exact (closure_minimal interior_subset (hKx i.1).isClosed).trans (hKsub i.1)
  · intro y hy
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (hcov hy)
    exact mem_iUnion.mpr ⟨⟨x, hxt⟩, hyx⟩

/-- The data of a finite cover of the closure of a relatively compact open `U` by open sets `Wᵢ`
with compact closures, each inside the range of an open embedding `ιᵢ : Nᵢ → M` whose pulled-back
triple has a hypersurface of maximal contact (Step 3 of the proof of [Kol07, Theorem 103] on the
compact closure of `U`). -/
structure ShrunkMCCover (T : AnalyticTriple ψ₀ M) (m : ℕ) (U : Opens M) where
  /-- The finite index set (a finite set of points of `M`). -/
  t : Finset M
  /-- The manifolds of the pieces. -/
  N : t → AnalyticManifold.{u} 𝕜 E
  /-- The open embeddings of the pieces. -/
  ι : ∀ i, AnalyticMap (N i) M
  /-- The maps `ιᵢ` are analytic open embeddings. -/
  hι : ∀ i, IsAnalyticOpenEmbedding (ι i)
  /-- The opens `Wᵢ` of `M`. -/
  W : t → Opens M
  /-- Each pulled-back triple has a global hypersurface of maximal contact. -/
  hmc : ∀ i, HasMaximalContact m (T.pullback (ι i) (hι i).1)
  /-- Each `Wᵢ` has compact closure. -/
  hWc : ∀ i, IsCompact (closure (W i : Set M))
  /-- The closure of `Wᵢ` lies in the range of `ιᵢ`. -/
  hWr : ∀ i, closure (W i : Set M) ⊆ range (ι i)
  /-- The `Wᵢ` cover the closure of `U`. -/
  hcov : closure (U : Set M) ⊆ ⋃ i, (W i : Set M)

/-- A finite shrunk cover with maximal contact exists for every triple of the class `BOClass m`
and every relatively compact open `U` (`exists_finite_shrunk_mcCover` for the closure of `U`). -/
theorem exists_shrunkMCCover {m : ℕ} {T : AnalyticTriple ψ₀ M} (hT : BOClass m T) {U : Opens M}
    (hU : IsCompact (closure (U : Set M))) : Nonempty (ShrunkMCCover T m U) := by
  obtain ⟨t, N, ι, hι, W, hmc, hWc, hWr, hcov⟩ := exists_finite_shrunk_mcCover hT hU
  exact ⟨⟨t, N, ι, hι, W, hmc, hWc, hWr, hcov⟩⟩

namespace ShrunkMCCover

open Hironaka.Manifold

variable {T : AnalyticTriple ψ₀ M} {m : ℕ} {U : Opens M} (C : ShrunkMCCover T m U)

/-- The cover as a shrunk embedding cover (`ShrunkEmbeddingCover`), forgetting the maximal
contact. The coproduct, the open `⊔ᵢ ιᵢ^{-1}(Wᵢ ∩ U)` and the cover map below are those of this
cover. -/
abbrev toCover : ShrunkEmbeddingCover M U :=
  ⟨C.t, C.N, C.ι, C.hι, C.W, C.hWc, C.hWr, C.hcov⟩

/-- The coproduct `⊔ᵢ Nᵢ` of the pieces (Kollár's `X^*`). -/
abbrev sigma : AnalyticManifold.{u} 𝕜 E := C.toCover.sigma

/-- The coproduct `⊔ᵢ ιᵢ : ⊔ᵢ Nᵢ → M` of the embeddings (Kollár's `g : X^* → X`). -/
abbrev desc : AnalyticMap C.sigma M := C.toCover.desc

/-- The coproduct map is a local analytic isomorphism. -/
theorem isLocalDiffeomorph_desc : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω C.desc :=
  C.toCover.isLocalDiffeomorph_desc

/-- The coproduct map is a coproduct of open embeddings. -/
theorem isCoprodOfOpenEmbeddings_desc : IsCoprodOfOpenEmbeddings C.desc :=
  C.toCover.isCoprodOfOpenEmbeddings_desc

/-- The pull-back of `T` to the coproduct (Kollár's `(X^*, g^* I, g^{-1} E)`). -/
abbrev triple : AnalyticTriple ψ₀ C.sigma := T.pullback C.desc C.isLocalDiffeomorph_desc

/-- The pulled-back triple on the coproduct is in the class `LocalMCClass m`: it has a global
hypersurface of maximal contact, the union of those of the pieces (Step 3 of the proof of
[Kol07, Theorem 103]; `localMCClass_pullback_sigmaDescMap`). -/
theorem localMCClass_triple (hT : BOClass m T) : LocalMCClass m C.triple := by
  have := finiteDimensional_of_chartIso ψ₀
  exact localMCClass_pullback_sigmaDescMap hT C.ι C.hι C.hmc

/-- The open `⊔ᵢ ιᵢ^{-1}(Wᵢ ∩ U)` of the coproduct. -/
abbrev opens : Opens C.sigma := C.toCover.opens

theorem mem_opens (p : C.sigma) :
    p ∈ (C.opens : Set C.sigma) ↔ C.ι p.1 p.2 ∈ (C.W p.1 : Set M) ∩ (U : Set M) := Iff.rfl

/-- The closed set `⊔ᵢ ιᵢ^{-1}(closure Wᵢ)` of the coproduct, which contains the closure of
`opens`. -/
abbrev closedHull : Set C.sigma := C.toCover.closedHull

theorem isClosed_closedHull : IsClosed C.closedHull := C.toCover.isClosed_closedHull

theorem closedHull_eq_iUnion :
    C.closedHull = ⋃ i, (sigmaMk (fun j => C.N j) i) '' ((C.ι i) ⁻¹' closure (C.W i : Set M)) :=
  C.toCover.closedHull_eq_iUnion

/-- `⊔ᵢ ιᵢ^{-1}(closure Wᵢ)` is compact: finitely many pieces, each the preimage under an open
embedding of a compact set inside its range. -/
theorem isCompact_closedHull : IsCompact C.closedHull := C.toCover.isCompact_closedHull

theorem closure_opens_subset : closure (C.opens : Set C.sigma) ⊆ C.closedHull :=
  C.toCover.closure_opens_subset

/-- The open `⊔ᵢ ιᵢ^{-1}(Wᵢ ∩ U)` has compact closure. -/
theorem isCompact_closure_opens : IsCompact (closure (C.opens : Set C.sigma)) :=
  C.toCover.isCompact_closure_opens

/-- The coproduct map sends `⊔ᵢ ιᵢ^{-1}(Wᵢ ∩ U)` into `U`. -/
theorem image_opens_subset : ⇑C.desc '' (C.opens : Set C.sigma) ⊆ (U : Set M) :=
  C.toCover.image_opens_subset

/-- The coproduct map sends `⊔ᵢ ιᵢ^{-1}(Wᵢ ∩ U)` onto `U`: the `Wᵢ` cover the closure of `U` and
each lies in the range of `ιᵢ`. -/
theorem image_opens_eq : ⇑C.desc '' (C.opens : Set C.sigma) = (U : Set M) :=
  C.toCover.image_opens_eq

/-- The cover map `⊔ᵢ ιᵢ^{-1}(Wᵢ ∩ U) → U`, the restriction of the coproduct map. -/
abbrev coverMap : AnalyticMap (C.sigma.restrict C.opens) (M.restrict U) := C.toCover.coverMap

/-- The cover map is a local analytic isomorphism. -/
theorem isLocalDiffeomorph_coverMap : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω C.coverMap :=
  C.toCover.isLocalDiffeomorph_coverMap

/-- The cover map is surjective onto `U`. -/
theorem surjective_coverMap : Function.Surjective C.coverMap := C.toCover.surjective_coverMap

/-- The cover map is a coproduct of open embeddings. -/
theorem isCoprodOfOpenEmbeddings_coverMap : IsCoprodOfOpenEmbeddings C.coverMap :=
  C.toCover.isCoprodOfOpenEmbeddings_coverMap

end ShrunkMCCover

end AnalyticTriple

end Manifold

namespace Hironaka.Manifold.AnalyticFamilyFunctor

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

variable {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
  {B : AnalyticFamilyFunctor ψ₀ Dom}

/-- The commutation of a family functor with a local analytic isomorphism `g`, with the image open
named: when `g(U') = V`, the value of the pulled-back triple on `U'` is the value on `V` pulled
back along `g|_{U'} : U' → V`, with its empty blow-ups deleted. -/
theorem CommutesWithLocalIsos.seqOn_eq_of_image_eq (hB : B.CommutesWithLocalIsos)
    {N : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M} {T' : AnalyticTriple ψ₀ N}
    {g : AnalyticMap N M} (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) (hT'g : T'.IsPullbackOf T g)
    (hT : Dom T) (hT' : Dom T') {U' : Opens N} (hU' : IsCompact (closure (U' : Set N)))
    {V : Opens M} (hV : IsCompact (closure (V : Set M))) (himg : ⇑g '' (U' : Set N) = (V : Set M)) :
    (B.fam T' hT').seqOn U' hU' =
      (((B.fam T hT).seqOn V hV).pullback (AnalyticMap.restrictMap g U' V himg.le)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' V himg.le)).eraseEmpty := by
  have hV' : AnalyticMap.imageOpens g hg U' = V := Opens.ext himg
  subst hV'
  exact hB T T' g hg hT'g hT hT' U' hU'

end Hironaka.Manifold.AnalyticFamilyFunctor

end
