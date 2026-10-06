/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Defs
public import Hironaka.Manifold.FiniteSuccession.Defs
public import Hironaka.Manifold.Snc.Defs
public import Hironaka.Manifold.FiniteSuccession.Functor.Pullback
public import Hironaka.Manifold.IdealSheaf.ReducedPullback
public import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# The clauses of the analytic main theorems on a finite succession of monoidal transformations

The clauses of Hironaka's Main Theorem II′(N) [Hir64, p. 156] on a finite succession of monoidal
transformations `U_0 ← U_1 ← ⋯ ← U_r` of an analytic manifold (`FiniteSuccession`), in which the
analytic principalization theorems state their conclusions over each compact set. They carry the
names of the clauses of the algebraic Main Theorems II and II(N) and Corollary 1 on blow-up
sequences of schemes, whose bodies they repeat with the manifold leaf predicates. One leaf
predicate says more than its scheme namesake: the manifold `IdealSheaf.IsSncBoundaryWith B D`
asserts simple normal crossings of `B` at every point and with `D` at the points of `D`, while
the scheme `IsSncBoundaryWith` asserts the condition at the points of `D` only. So the first field
of `HasSncBoundaries` here also asserts simple normal crossings of every intermediate boundary.

* `FiniteSuccession.HasSncBoundaries S B`: the boundaries `E_i` (`S.boundarySeq B`), started at
  `E_0 = B` and continued by `E_{i+1} = red(σ_{i+1}⁻¹(E_i) ∪ σ_{i+1}⁻¹(D_i))`, have simple normal
  crossings with the centres, and the last one has simple normal crossings
  ([Hir64, Main Theorem II′(N) (iii) and the first half of (iv)]; [Wlo09, Theorem 2.0.3 (2)]).
* `FiniteSuccession.HasConstantPositiveOrderAlongCenters S J`: the order of the weak transform of
  `J` is a positive constant along every centre ([Hir64, Main Theorem II′(N) (ii)]).

The clauses of Włodarczyk's locally finite embedded desingularization [Wlo09, Theorem 2.0.2] on the
succession over each compact set are collected in one structure, named after the structure
`EmbeddedPair.IsDesingularizedBy` of the algebraic embedded desingularization on blow-up sequences
of schemes (the fields are named after the analytic notions they state):

* `IdealSheaf.IsDesingularizedBy I S`: the closed subspace with ideal sheaf `I` is desingularized
  by `S` ([Wlo09, Theorem 2.0.2 (1)–(3), (6)]);
* `IdealSheaf.IsLocallyFinitelyDesingularizedBy I F`: the family `F` is a locally finite embedded
  desingularization of the closed subspace with ideal sheaf `I` ([Wlo09, Theorem 2.0.2]: the
  map `res_{Y,M}` proper and an isomorphism off the singular locus, the succession over every
  compact desingularizing the subspace with no empty centre and every centre of codimension at
  least two or in the exceptional divisor, and an exceptional divisor and a strict transform on
  the whole space).

The clauses of Włodarczyk's locally finite principalization [Wlo09, Theorem 2.0.3], whose value is
a compatible family of finite successions over the compact sets (`ExtensionCompatibleFamily`), are
collected in a structure on the family, named after Włodarczyk's term:

* `IdealSheaf.IsLocallyFinitelyPrincipalizedBy I F`: the family `F` is a locally finite
  principalization of the ideal sheaf `I` ([Wlo09, Theorem 2.0.3 (1)–(3)], with the properness of
  `prin_I`).

The functorial theorems assert the existence of an *assignment* of a compatible family to every
input, with a property of each value and a functoriality package, as the algebraic functorial
theorems assert a blow-up sequence functor (`BlowUpSequenceFunctor`); they differ in the inputs.

* `IdealSheafPair 𝕜`: the pairs `(M, I)` of an analytic manifold `M` over `𝕜` on a
  finite-dimensional model space and an ideal sheaf `I` with nonzero stalks, the inputs of the
  principalization (Kollár's triples with an empty boundary); `IdealSheafPair.pullback` is the
  pair `(N, g^*I)` over a local analytic isomorphism `g : N → M`.
* `HasUnderlyingManifold C 𝕜`: a type `C` of inputs each with an underlying manifold on a
  finite-dimensional model space; `CompatibleFamilyAssignment C`: a compatible family for every
  input.
* `IdealSheaf.IsPushforwardAlong I J τ`: the ideal sheaf `I` on `M` is the push-forward of the
  ideal sheaf `J` on `N` along the closed embedding of analytic manifolds `τ : N → M` (an
  analytic embedding, Mathlib's `IsSmoothEmbedding` at `ω`, with closed image): `I` contains the
  ideal of `τ(N)` and `J = τ^*I` (Kollár's `𝒪_X/I_X = j_*(𝒪_Y/I_Y)` [Kol07, 34.3]).
* `IdealSheafPair.CommutesWithLocalAnalyticIsomorphisms P`: the last sentence of
  [Wlo09, Theorem 2.0.3] for local analytic isomorphisms, in its two forms — over every pair of
  compact sets, as the relation between two successions of [Wlo09, Theorem 3.5.1 (2)], and
  globally, as the lift of `g : N → M` to a unique map `g̃ : Ñ → M̃` over `g`, a local analytic
  isomorphism identifying `Ñ` with the fibre product `N ×_M M̃` (the "natural lifting" of
  [Wlo09, Theorem 2.0.1 (3)]).
* `IdealSheafPair.CommutesWithClosedEmbeddings P`: the rest of that sentence, "embeddings of
  ambient varieties", read as [Kol07, Theorem 35 (5)] and [Kol07, 34.3], over every pair of
  compact sets.
* `EmbeddedPair 𝕜`: the pairs `(M, Y)` of an analytic manifold on a finite-dimensional model
  space and a reduced closed analytic subspace, the inputs of the embedded desingularization
  (the analogue of the algebraic `EmbeddedPair`); `EmbeddedPair.pullback` is the pair
  `(N, g^{-1}(Y))` over a local analytic isomorphism `g : N → M`.
* `EmbeddedPair.CommutesWithLocalAnalyticIsomorphisms R` and
  `EmbeddedPair.CommutesWithClosedEmbeddings R`: the two halves of [Wlo09, Theorem 2.0.2 (4)],
  over every pair of compact sets, the second with Kollár's hypothesis that no component of the
  submanifold lies in the subspace.
-/

@[expose] public section

universe u v w

open TopologicalSpace
open scoped Manifold ContDiff

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E}

/-- The boundaries `E_i` of the succession `S` started at `B` (`S.boundarySeq B`: `E_0 = B` and
`E_{i+1} = red(σ_{i+1}⁻¹(E_i) ∪ σ_{i+1}⁻¹(D_i))`) have simple normal crossings with the centres,
and the last one has simple normal crossings ([Hir64, Main Theorem II′(N) (iii) and the first half
of (iv), p. 156]; [Wlo09, Theorem 2.0.3 (2)]). -/
@[mk_iff]
structure HasSncBoundaries (S : FiniteSuccession M) (B : IdealSheaf M) : Prop where
  /-- The boundary `E_i` at the stage of the `i`-th centre has simple normal crossings with it. -/
  isSncBoundaryWith_center : ∀ i : Fin S.length,
    (S.boundarySeq B i.castSucc).IsSncBoundaryWith (S.center i)
  /-- The last boundary `E_r` has simple normal crossings. -/
  isSncBoundary_last : (S.boundarySeq B (Fin.last S.length)).IsSncBoundary

/-- The order of the weak transform `J_i` of `J` (`S.weakTransformSeq J i`) is a positive constant
along the centre `D_i`, for every `i` ([Hir64, Main Theorem II′(N) (ii), p. 156]). -/
def HasConstantPositiveOrderAlongCenters (S : FiniteSuccession M) (J : IdealSheaf M) : Prop :=
  ∀ i : Fin S.length, ∃ c : ℕ, 0 < c ∧ ∀ y ∈ (S.center i).support,
    (S.weakTransformSeq J i.castSucc).ord y = c

end AnalyticManifold.FiniteSuccession

namespace AnalyticManifold.IdealSheaf

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E}

/-- The closed subspace `Y` of `M` with ideal sheaf `I` is **desingularized** by the finite
succession `S : M = U_0 ← U_1 ← ⋯ ← U_r` with composite `σ : U_r → M`
[Wlo09, Theorem 2.0.2 (1)–(3), (6)]. With exceptional divisors `E_i` (the boundaries
`S.boundarySeq ⊤ i` started at the empty boundary `⊤`) and strict transforms `Y_i` of `Y`
(`S.strictTransformSubspaceSeq I i`), `Ỹ = Y_r`: the centres `C_i` are smooth; every `E_i` has
simple normal crossings with `C_i` and `E_r` has simple normal crossings; no point of a centre
lies over a point of `Reg(Y)` (`regularLocus`); the support of `E_r` is the preimage of
`Sing(Y) = Y ∖ Reg(Y)`; `Ỹ` is smooth and has simple normal crossings with `E_r`; and
`σ^*(I_Y) = I_Ỹ · I_Ẽ` with `Ẽ` a combination of the components of `E_r`. The analogue on
manifolds of `EmbeddedPair.IsDesingularizedBy` on schemes. -/
@[mk_iff]
structure IsDesingularizedBy (I : IdealSheaf M) (S : FiniteSuccession M) : Prop where
  /-- The centres `C_i` are smooth (Włodarczyk's "smooth closed centers"; automatic for every
  finite succession, `FiniteSuccession.center_isNonsingular`). -/
  isNonsingular_center : ∀ i, (S.center i).IsNonsingular
  /-- (1) Every exceptional divisor `E_i` has simple normal crossings with the centre `C_i`, and
  `E_r` has simple normal crossings. -/
  hasSncBoundaries : S.HasSncBoundaries ⊤
  /-- (2) The centres are disjoint from `Reg(Y)`: no point of a centre `C_i` lies over a point
  where `Y` (not `Y_i`) is smooth. -/
  stageMap_notMem_regularLocus : ∀ i : Fin S.length, ∀ x ∈ (S.center i).support,
    S.stageMap i.castSucc x ∉ I.regularLocus
  /-- The support of the exceptional divisor `E_r` is the exceptional locus, read as the preimage
  `σ⁻¹(Sing Y)` of the singular locus `Sing Y = Y ∖ Reg(Y)` (the preamble of Theorem 2.0.2). -/
  support_boundarySeq_last : (S.boundarySeq ⊤ (Fin.last S.length)).support =
    S.composite ⁻¹' (I.support \ I.regularLocus)
  /-- (3) The strict transform `Ỹ = Y_r` is smooth. -/
  isNonsingular_strictTransform :
    (S.strictTransformSubspaceSeq I (Fin.last S.length)).IsNonsingular
  /-- (3) `Ỹ` has simple normal crossings with `E_r`, transversally. -/
  isSncBoundaryTransversalTo_strictTransform :
    (S.boundarySeq ⊤ (Fin.last S.length)).IsSncBoundaryTransversalTo
      (S.strictTransformSubspaceSeq I (Fin.last S.length))
  /-- (6) `σ^*(I_Y) = I_Ỹ · I_Ẽ`, `Ẽ` a combination of the components of `E_r` near every
  point. -/
  isMulBoundaryMonomial_pullback :
    IsMulBoundaryMonomial (I.pullback S.composite S.composite.contMDiff)
      (S.strictTransformSubspaceSeq I (Fin.last S.length)) (S.boundarySeq ⊤ (Fin.last S.length))

/-- The compatible family `F` is a **locally finite principalization** of the ideal sheaf `I` on
`M` [Wlo09, Theorem 2.0.3 (1)–(3)]: with `prin_I = F.map : M̃ → M`, and over the neighbourhood
`U_K` of a compact `K ⊆ M` the succession `F.seq K : U_K = U_0 ← U_1 ← ⋯ ← U_r` with composite
`σ_K : U_r → U_K` and exceptional divisors `E_i` (the boundaries `(F.seq K).boundarySeq ⊤ i`
started at the empty boundary `⊤`): `prin_I` is proper; every `U_K` has compact closure; the
centres `C_i` are smooth; every `E_i` has simple normal crossings with `C_i` and `E_r` has simple
normal crossings; the total transform `σ_K^*(I|_{U_K})` is, near every point, the ideal of an
effective combination of the components of `E_r` through it; the total transform `prin_I^*(I)` on
`M̃` is a normal-crossings divisor; and `prin_I` is an isomorphism over the complement of the
support of `I`. The compatibility of the successions over two compacts is a field of
`ExtensionCompatibleFamily`. The analogue on manifolds of `Triple.IsPrincipalizedBy` on schemes,
whose fields are Kollár's clauses (1)–(3) for a single blow-up sequence.

Relation to the source.
* **Translation.** `I.IsLocallyFinitelyPrincipalizedBy F` says that `F` is a locally finite
  principalization of $I$ in the sense of [Wlo09, Theorem 2.0.3]: `F.map` is
  $\mathrm{prin}_I \colon \tilde M \to M$; for a compact set $K$, `F.nhd K` is the open
  neighbourhood $U \supset K$ of Włodarczyk's clause (1) and `F.seq K` the factorization $(\ast)$
  of $\mathrm{prin}_I$ over $U$, whose exceptional divisors $E_{U_i}$ are the boundaries
  `(F.seq K).boundarySeq ⊤ i` started at the empty boundary `⊤`; his clause (4) is the
  compatibility of the family (`ExtensionCompatibleFamily`).
* **Translation.** The fields are the clauses of [Wlo09, Theorem 2.0.3]: `isProperMap` the
  properness of $\mathrm{prin}_I$, `isNonsingular_center` the smooth centres of (1),
  `hasSncBoundaries` clause (2), and `isMulBoundaryMonomial_pullback` clause (3) over $U$, in which
  `IsMulBoundaryMonomial J ⊤ B`, with the unit ideal `⊤` as its first factor, says that $J$ is near
  every point the ideal of an effective combination of the hypersurfaces of the simple normal
  crossings family whose reduced ideal sheaf is $B$, here $E_{U_r}$;
  `isNormalCrossingsDivisor_pullback` is clause (3) for the total transform $\mathrm{prin}_I^*(I)$
  on $\tilde M$.
* **Strengthening.** The fields `isCompact_closure_nhd` and `isIsoOver_compl_support` have no
  counterpart among Włodarczyk's clauses. -/
@[mk_iff]
structure IsLocallyFinitelyPrincipalizedBy (I : IdealSheaf M) (F : ExtensionCompatibleFamily M) :
    Prop where
  /-- `prin_I : M̃ → M` is proper (the preamble of Theorem 2.0.3). -/
  isProperMap : IsProperMap F.map
  /-- Every neighbourhood `U_K` has compact closure. Then `g(U_K)` lies in a compact for every
  analytic map `g` out of `M`, so that the commutation with local analytic isomorphisms
  (`IdealSheafPair.CommutesWithLocalAnalyticIsomorphisms`) applies to every compact of `M`. -/
  isCompact_closure_nhd : ∀ K : Compacts M, IsCompact (closure (F.nhd K : Set M))
  /-- (1) The centres `C_i` are smooth (automatic for every finite succession,
  `FiniteSuccession.center_isNonsingular`). -/
  isNonsingular_center : ∀ (K : Compacts M) (i : Fin (F.seq K).length),
    ((F.seq K).center i).IsNonsingular
  /-- (2) Every exceptional divisor `E_i` has simple normal crossings with the centre `C_i`, and
  `E_r` has simple normal crossings. -/
  hasSncBoundaries : ∀ K : Compacts M, (F.seq K).HasSncBoundaries ⊤
  /-- (3) The total transform `σ_K^*(I|_{U_K})` is the ideal of a divisor `Ẽ_U` which near every
  point is an effective combination of the components of `E_r` (`IsMulBoundaryMonomial` with the
  unit ideal `⊤` as its first factor). -/
  isMulBoundaryMonomial_pullback : ∀ K : Compacts M,
    IsMulBoundaryMonomial
      ((I.restrict (F.nhd K)).pullback (F.seq K).composite (F.seq K).composite.contMDiff) ⊤
      ((F.seq K).boundarySeq ⊤ (Fin.last (F.seq K).length))
  /-- (3) on `M̃`: the total transform `prin_I^*(I)` is a normal-crossings divisor. -/
  isNormalCrossingsDivisor_pullback : IsNormalCrossingsDivisor (I.pullback F.map F.map.contMDiff)
  /-- `prin_I` is an isomorphism over the complement of the support of `I` ([Wlo09, Lemma 4.0.3];
  [Kol07, Theorem 35 (3)]). -/
  isIsoOver_compl_support : F.map.IsIsoOver I.supportᶜ

/-- The compatible family `F` is a **locally finite embedded desingularization** of the closed
subspace `Y` of `M` with ideal sheaf `I` [Wlo09, Theorem 2.0.2]: with `res_{Y,M} = F.map : M̃ → M`,
and over the neighbourhood `U_K` of a compact `K ⊆ M` the succession `F.seq K`, `res_{Y,M}` is
proper, it is an isomorphism over the complement of the singular locus `Sing(Y) = Y ∖ Reg(Y)`,
every `F.seq K` desingularizes `Y ∩ U_K` (`IsDesingularizedBy`, clauses (1)–(3) and (6)), has
no empty centre and has every centre of codimension at least two or of codimension one inside the
exceptional divisor of its stage, and there are on `M̃` an exceptional divisor `E` and a strict
transform `Ỹ` gluing the last exceptional divisors and the last strict transforms of the
successions: over every compact `K`, read on the last stage `U_r` of `F.seq K` through its
identification `toSpace K` with `res_{Y,M}⁻¹(U_K)`, `E` is `E_r` and `Ỹ` is the strict transform
`Y_r` of `Y ∩ U_K`. Then `E` is the reduced ideal sheaf of a simple normal crossings family of
hypersurfaces of `M̃` with which `Ỹ` has simple normal crossings, transversally, and
`res_{Y,M}^*(I_Y) = I_Ỹ · I_Ẽ` with `Ẽ` near every point an effective combination of the
components of `E`.
His clause (5), the compatibility of the successions over two compacts, is a field of
`ExtensionCompatibleFamily`.

Relation to the source.
* **Translation.** `I.IsLocallyFinitelyDesingularizedBy F` says that `F` is the embedded
  desingularization of $Y$ in the sense of [Wlo09, Theorem 2.0.2]: `F.map` is
  $\mathrm{res}_{Y,M} \colon \tilde M \to M$, "proper bimeromorphic"; for a compact set $K$,
  `F.nhd K` is the open subset $U$ and `F.seq K` the factorization $(\ast)$ of
  $\mathrm{res}_{Y,M}$ over $U$, whose clauses (1)–(3) and (6) are `IsDesingularizedBy`; his
  clause (5) is the compatibility of the family (`ExtensionCompatibleFamily`).
* **Strengthening.** `isIsoOver_compl_sing`, that $\mathrm{res}_{Y,M}$ is an isomorphism over
  $M \setminus \operatorname{Sing}(Y)$, says more than Włodarczyk's "bimeromorphic". Over
  $\operatorname{Reg}(Y)$ it follows from his clause (2); over $M \setminus Y$ it is not in
  [Wlo09, Theorem 2.0.2] but holds for his construction, an initial segment of the
  principalization of $I_Y$, which is an isomorphism over $M \setminus V(I_Y)$
  [Wlo09, Lemma 4.0.3].
* **Translation.** Włodarczyk's "divisor $E$" and "strict transform $\tilde Y$" on $\tilde M$ are
  the `E` and `Y` of `exists_divisor_strictTransform`. Its first clause identifies them over every
  compact with the $E_{U_r}$ and $\tilde Y \cap U_r$ of the factorization $(\ast)$: his
  "$\tilde Y$" and "$E$" name the global objects and their restrictions alike. Its other clauses
  are his clause (1) for $E$ and his clause (3) for the simple normal crossings of $\tilde Y$ with
  $E$, and his clause (6), $\sigma^*(I_Y) = I_{\tilde Y} I_{\tilde E}$ for
  $\sigma = \mathrm{res}_{Y,M}$, on $\tilde M$.
* **Restatement.** The support of $E$, "the exceptional locus of $\mathrm{res}_{Y,M}$", and the
  smoothness of $\tilde Y$ in his clause (3) are read over every compact: through the first clause
  of `exists_divisor_strictTransform` they are the identity
  $|E_r| = \sigma_K^{-1}(\operatorname{Sing} Y)$ and the smoothness of $Y_r$ of
  `IsDesingularizedBy`, from which $|E| = \mathrm{res}_{Y,M}^{-1}(\operatorname{Sing} Y)$ and the
  smoothness of $\tilde Y$ follow (`IsGloballyDesingularizedBy.support_eq`,
  `IsGloballyDesingularizedBy.isNonsingular`).
* **Translation.** `center_ne_top` reads the first half of Włodarczyk's Remark (2) after
  Theorem 2.0.3, that his centres are nonempty (the empty blow-up convention of [Kol07, 32]), and
  `two_le_codim_or_boundarySeq_le_center` reads its second half, that his centres have
  codimension at least two, together with his Remark (1): a centre of codimension one lies in the
  exceptional divisor, its blow-up is an isomorphism, and it stays a component of the exceptional
  divisor; the centres of codimension one are not removed from the successions. -/
@[mk_iff]
structure IsLocallyFinitelyDesingularizedBy (I : IdealSheaf M) (F : ExtensionCompatibleFamily M) :
    Prop where
  /-- `res_{Y,M} : M̃ → M` is proper (the preamble of Theorem 2.0.2). -/
  isProperMap : IsProperMap F.map
  /-- `res_{Y,M}` is an isomorphism over the complement of `Sing(Y) = Y ∖ Reg(Y)`, more than
  Włodarczyk's "bimeromorphic": over `Reg(Y)` by his clause (2), over `M ∖ Y` by
  [Wlo09, Lemma 4.0.3]. -/
  isIsoOver_compl_sing : F.map.IsIsoOver (I.support \ I.regularLocus)ᶜ
  /-- Over the neighbourhood `U_K` of every compact, the succession desingularizes `Y ∩ U_K`:
  [Wlo09, Theorem 2.0.2 (1)–(3), (6)]. -/
  isDesingularizedBy_seq : ∀ K : Compacts M, (I.restrict (F.nhd K)).IsDesingularizedBy (F.seq K)
  /-- No centre of any succession is empty: the ideal sheaf of no centre is the unit ideal (the
  empty blow-up convention [Kol07, 32]; Włodarczyk's centres are nonempty,
  [Wlo09, Remark (2) after Theorem 2.0.3]). -/
  center_ne_top : ∀ (K : Compacts M) (i : Fin (F.seq K).length), (F.seq K).center i ≠ ⊤
  /-- Every centre `C_i` has codimension at least two, or has codimension one and lies in the
  exceptional divisor `E_i` of its stage, the reduced ideal sheaf of `E_i` lying in its ideal sheaf:
  then its blow-up is an isomorphism and it becomes a component of the exceptional divisor
  [Wlo09, Remarks (1) and (2) after Theorem 2.0.3]. -/
  two_le_codim_or_boundarySeq_le_center : ∀ (K : Compacts M) (i : Fin (F.seq K).length),
    2 ≤ (F.seq K).codim i ∨ (F.seq K).codim i = 1 ∧
      ∀ x, ((F.seq K).boundarySeq ⊤ i.castSucc).stalkIdeal x ≤ ((F.seq K).center i).stalkIdeal x
  /-- Włodarczyk's divisor `E` and strict transform `Ỹ` (here `Y`) on `M̃`: they glue the last
  exceptional divisors and strict transforms of the successions over the compacts, `E` is a simple
  normal crossings divisor with which `Ỹ` is transversal ((1), (3)), and `res^*(I_Y) = I_Ỹ · I_Ẽ`
  ((6)). -/
  exists_divisor_strictTransform : ∃ E Y : IdealSheaf F.space,
    -- over every compact, `E` and `Ỹ` are the last exceptional divisor and strict transform
    (∀ K : Compacts M,
      E.pullback (F.toSpace K) (F.toSpace K).contMDiff =
          (F.seq K).boundarySeq ⊤ (Fin.last (F.seq K).length) ∧
        Y.pullback (F.toSpace K) (F.toSpace K).contMDiff =
          (F.seq K).strictTransformSubspaceSeq (I.restrict (F.nhd K))
            (Fin.last (F.seq K).length)) ∧
    -- (1), (3) on `M̃`
    E.IsSncBoundaryTransversalTo Y ∧
    -- (6) on `M̃`
    IsMulBoundaryMonomial (I.pullback F.map F.map.contMDiff) Y E

end AnalyticManifold.IdealSheaf

namespace AnalyticManifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-! ### The inputs of the functorial theorems -/

-- The universes `u` of the manifold and `v` of its model space are independent (the standard
-- models `𝕜ⁿ` live in `Type`, the manifolds in `Type u`), so both occur only in the `max`.
set_option linter.checkUnivs false in
/-- A *pair* `(M, I)`, the input of Włodarczyk's functorial principalization
[Wlo09, Theorem 2.0.3]: an analytic manifold `M` over `𝕜`, modelled on a finite-dimensional space
`E`, with an ideal sheaf `I` on `M` with nonzero stalks (so on every connected component). Kollár's
triple `(X, I, ∅)` [Kol07, Notation 64] with an empty boundary, on an analytic manifold; the model
space is part of the input, so that one assignment covers the manifolds of every dimension. -/
structure IdealSheafPair (𝕜 : Type) [RCLike 𝕜] : Type (max (u + 1) (v + 1)) where
  /-- The model space. -/
  E : Type v
  [normedAddCommGroup : NormedAddCommGroup E]
  [normedSpace : NormedSpace 𝕜 E]
  [finiteDimensional : FiniteDimensional 𝕜 E]
  /-- The manifold. -/
  M : AnalyticManifold.{u} 𝕜 E
  /-- The ideal sheaf. -/
  I : IdealSheaf M
  /-- `I` has nonzero stalks. -/
  isNonzeroEverywhere : I.IsNonzeroEverywhere

attribute [instance] IdealSheafPair.normedAddCommGroup IdealSheafPair.normedSpace
  IdealSheafPair.finiteDimensional

-- The universes `u` and `v` are independent, as for `IdealSheafPair`.
set_option linter.checkUnivs false in
/-- A type `C` of inputs each with an underlying analytic manifold over `𝕜`, modelled on a
finite-dimensional space (the analogue of `HasUnderlyingScheme` for the algebraic inputs). -/
class HasUnderlyingManifold (C : Type w) (𝕜 : outParam Type) [RCLike 𝕜] :
    Type (max w (u + 1) (v + 1)) where
  /-- The model space of the underlying manifold of an input. -/
  model : C → Type v
  [normedAddCommGroup : ∀ T, NormedAddCommGroup (model T)]
  [normedSpace : ∀ T, NormedSpace 𝕜 (model T)]
  [finiteDimensional : ∀ T, FiniteDimensional 𝕜 (model T)]
  /-- The underlying manifold of an input. -/
  manifold : ∀ T, AnalyticManifold.{u} 𝕜 (model T)

attribute [instance_reducible] HasUnderlyingManifold.normedAddCommGroup
  HasUnderlyingManifold.normedSpace
attribute [instance] HasUnderlyingManifold.normedAddCommGroup HasUnderlyingManifold.normedSpace
  HasUnderlyingManifold.finiteDimensional

instance IdealSheafPair.hasUnderlyingManifold :
    HasUnderlyingManifold (IdealSheafPair.{u, v} 𝕜) 𝕜 where
  model T := T.E
  manifold T := T.M

/-- A *compatible family assignment* on the inputs `C`: a compatible family of finite successions
of blow-ups (`ExtensionCompatibleFamily`) of the underlying manifold of every input — Włodarczyk's
`prin` and `res` as rules on all pairs, the counterpart on manifolds of a blow-up sequence functor
(`BlowUpSequenceFunctor`, [Kol07, Definition 31]). Its properties are the clauses of the
functorial theorems. -/
abbrev CompatibleFamilyAssignment (C : Type w) [HasUnderlyingManifold.{u, v} C 𝕜] : Type _ :=
  ∀ T : C, ExtensionCompatibleFamily (HasUnderlyingManifold.manifold T)

/-- The pull-back `(N, g^*I)` of the pair `(M, I)` along a local analytic isomorphism `g : N → M`
of manifolds modelled on `E`: the source of the morphism of pairs over `g` [Wlo09, Theorem 3.5.1].
The pulled-back ideal sheaf has nonzero stalks (`IdealSheaf.isNonzeroEverywhere_comap`). -/
noncomputable abbrev IdealSheafPair.pullback (T : IdealSheafPair.{u, v} 𝕜)
    {N : AnalyticManifold.{u} 𝕜 T.E}
    (g : AnalyticMap N T.M) (hg : IsLocalDiffeomorph 𝓘(𝕜, T.E) 𝓘(𝕜, T.E) ω g) :
    IdealSheafPair.{u, v} 𝕜 :=
  ⟨T.E, N, T.I.pullback g g.contMDiff,
    Manifold.IdealSheaf.isNonzeroEverywhere_comap T.isNonzeroEverywhere g hg⟩

/-- The ideal sheaf `I` on `M` is the **push-forward** of the ideal sheaf `J` on `N` along the
closed embedding of analytic manifolds `τ : N → M`: `τ` is an analytic embedding (Mathlib's
`IsSmoothEmbedding` at `ω`: an analytic immersion, of the form `u ↦ (u, 0)` in suitable charts near
every point, which is a homeomorphism onto its image) with closed image, `I` contains the ideal of
the closed submanifold `τ(N)` (the vanishing ideal `vanishingStalk`, stalk by stalk), and
`J = τ^*I`. So the closed subspace of `I` lies in `τ(N)` and is the image of the closed subspace of
`J`. The image `τ(N)` is a closed submanifold of `M`
(`IsClosedAnalyticEmbedding.exists_isClosedSubmanifold`, for a finite-dimensional model) and `N`
carries the analytic structure induced on it: every analytic map into `M` with values in `τ(N)`
factors analytically through `τ` (`IsClosedAnalyticEmbedding.exists_comp_eq`).

Relation to the source.
* **Translation.** The embedding `τ` is Kollár's "closed embedding of smooth schemes"
  [Kol07, 34.3] for analytic manifolds, the embedding of Włodarczyk's "embeddings of ambient
  varieties" [Wlo09, Theorem 2.0.3]: $\tau$ identifies $N$ with the closed submanifold $\tau(N)$ of
  $M$, with its induced analytic structure.
* **Translation.** `I.IsPushforwardAlong J τ` is Kollár's hypothesis on the ideal sheaves in his
  commutation with closed embeddings [Kol07, 34.3]: "$j \colon Y \hookrightarrow X$ is a closed
  embedding of smooth schemes, $0 \neq I_Y \subset \mathcal{O}_Y$ and
  $0 \neq I_X \subset \mathcal{O}_X$ are ideal sheaves with
  $\mathcal{O}_X/I_X = j_*(\mathcal{O}_Y/I_Y)$", for an empty boundary — the quotient condition
  being the containment of the ideal sheaf of $\tau(N)$ in $I$ with $J = \tau^* I$; the nonzero
  stalks are conditions on the pairs. The containment is stated stalk by stalk, the stalks of the
  ideal sheaf of the submanifold $\tau(N)$ being the ideals of the germs vanishing on it.
* **Translation.** In Włodarczyk's notation, `I.IsPushforwardAlong J τ` says
  $I = \tau_*(J) \cdot \mathcal{O}_M$, the preimage of $\tau_*(J)$ under the surjection
  $\mathcal{O}_M \to \tau_*(\mathcal{O}_N)$ [Wlo09, Remark (3) after Theorem 2.0.3], the ideal
  for which the canonical resolution of $J$ with centres $C_i$ defines that of $I$, with the
  centres $\tau(C_i)$ [Wlo09, Theorem 3.5.1 (3)]. -/
structure IdealSheaf.IsPushforwardAlong {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {M : AnalyticManifold.{u} 𝕜 E} {N : AnalyticManifold.{u} 𝕜 E'} (I : IdealSheaf M)
    (J : IdealSheaf N) (τ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, E), M⟯) : Prop where
  /-- `τ` is an analytic embedding: an analytic immersion which is a homeomorphism onto its
  image. -/
  isSmoothEmbedding : Manifold.IsSmoothEmbedding 𝓘(𝕜, E') 𝓘(𝕜, E) ω τ
  /-- The image of `τ` is closed in `M`. -/
  isClosed_range : IsClosed (Set.range τ)
  /-- The ideal of the image of `τ` lies in `I`: at every point the germs vanishing on `τ(N)` lie
  in the stalk of `I`. -/
  vanishingStalk_le : ∀ x,
    Manifold.vanishingStalk (𝕜 := 𝕜) (E := E) (Set.range τ) x ≤ I.stalkIdeal x
  /-- `J = τ^*I`. -/
  pullback_eq : J = I.pullback τ τ.contMDiff

/-! ### The functoriality of an assignment on pairs -/

namespace IdealSheafPair

variable (P : CompatibleFamilyAssignment (IdealSheafPair.{u, v} 𝕜))

/-- A compatible family assignment `P` on the pairs `(M, I)` **commutes with local analytic
isomorphisms**, in two forms. Over every pair of compact sets: for a local analytic isomorphism
`g : N → M` of manifolds modelled on one space, the family `P(N, g^*I)` is the pull-back of
`P(M, I)` along `g` (`ExtensionCompatibleFamily.IsPullbackAlong`): for compacts `K' ⊆ N`, `K ⊆ M`
with `g(U_{K'}) ⊆ U_K`, the succession of `P(N, g^*I)` over `U_{K'}` is the pull-back along `g` of
the succession of `P(M, I)` over `U_K`, up to blow-ups with empty centre. Globally: writing
`prin_I : M̃ → M` and `prin_J : Ñ → N` for the maps of `P(M, I)` and `P(N, J)`, `J = g^*I`, there is
an analytic map `g̃ : Ñ → M̃` over `g` (`prin_I ∘ g̃ = g ∘ prin_J`) which is a local analytic
isomorphism, maps the fibre of `prin_J` over every `y ∈ N` bijectively onto the fibre of `prin_I`
over `g y`, and is the only continuous map `Ñ → M̃` over `g`; the fibre bijection with the local
isomorphism is the identification of `Ñ` with the fibre product `N ×_M M̃`, stated without forming
it.

Relation to the source.
* **Translation.** The structure is the last sentence of [Wlo09, Theorem 2.0.3], "the morphism
  $\mathrm{prin} \colon (\tilde M, \tilde I) \to (M, I)$ commutes with local analytic
  isomorphisms". `isPullbackAlong` is its form of [Wlo09, Theorem 3.5.1 (2)]: for a
  local analytic isomorphism $\varphi$, the sequence induced by $\varphi$ from the sequence of $I$
  is an extension of the sequence of $\varphi^*(I)$. `exists_lift` is its global form, the
  "natural lifting" $\tilde\varphi$, "a local analytic isomorphism", of
  [Wlo09, Theorem 2.0.1 (3)]; the uniqueness makes the lift of a composite the composite of the
  lifts.
* **Restatement.** The identification of $\tilde N$ with $N \times_M \tilde M$ of
  [Wlo09, Proposition 3.4.1] is stated pointwise, as the bijection of $\tilde g$ between the fibres
  over corresponding points; over an open set on which $g$ is injective the lift is then an
  analytic isomorphism between the preimages.
* **Interpretation.** The exact equality of [Wlo09, Theorem 3.5.1 (1)] for a surjective local
  analytic isomorphism has no counterpart per pair of compact sets: for $g$ the identity and
  compacts $K' \subsetneq K$ with a centre of the succession over $U_K$ lying over
  $U_K \setminus U_{K'}$, the induced succession over $U_{K'}$ has an empty centre that the
  succession over $U_{K'}$ omits. Its global content is read as: for surjective $g$ the lift
  $\tilde g$ is a surjective local analytic isomorphism identifying $\tilde N$ with
  $N \times_M \tilde M$. -/
structure CommutesWithLocalAnalyticIsomorphisms : Prop where
  /-- The family `P(N, g^*I)` is the pull-back of `P(M, I)` along `g`, over every pair of
  compacts. -/
  isPullbackAlong : ∀ (T : IdealSheafPair.{u, v} 𝕜) {N : AnalyticManifold.{u} 𝕜 T.E}
    (g : AnalyticMap N T.M) (hg : IsLocalDiffeomorph 𝓘(𝕜, T.E) 𝓘(𝕜, T.E) ω g),
    (P (T.pullback g hg)).IsPullbackAlong (P T) g
  /-- There is an analytic map `g̃ : Ñ → M̃` over `g`, a local analytic isomorphism bijective
  between the fibres over `y` and over `g y`, and the only continuous map over `g`. -/
  exists_lift : ∀ (T : IdealSheafPair.{u, v} 𝕜) {N : AnalyticManifold.{u} 𝕜 T.E}
    (g : AnalyticMap N T.M) (hg : IsLocalDiffeomorph 𝓘(𝕜, T.E) 𝓘(𝕜, T.E) ω g),
    ∃ g' : AnalyticMap (P (T.pullback g hg)).space (P T).space,
      (∀ q, (P T).map (g' q) = g ((P (T.pullback g hg)).map q)) ∧
      IsLocalDiffeomorph 𝓘(𝕜, T.E) 𝓘(𝕜, T.E) ω g' ∧
      (∀ y : N, Set.BijOn g' ((P (T.pullback g hg)).map ⁻¹' {y}) ((P T).map ⁻¹' {g y})) ∧
      ∀ φ : (P (T.pullback g hg)).space → (P T).space, Continuous φ →
        (∀ q, (P T).map (φ q) = g ((P (T.pullback g hg)).map q)) → φ = g'

/-- A compatible family assignment `P` on the pairs `(M, I)` **commutes with closed embeddings**:
for pairs `(M, I)` and `(N, J)` and a closed embedding of analytic manifolds `τ : N → M` along
which `I` is the push-forward of `J` (`IdealSheaf.IsPushforwardAlong`: `τ(N)` a closed
submanifold, `I ⊇ 𝓘_{τ(N)}`, `J = τ^*I`), the family `P(M, I)` is the push-forward of `P(N, J)`
along `τ` (`ExtensionCompatibleFamily.IsPushforwardAlong`): for compacts `K' ⊆ N`, `K ⊆ M` with
`τ(U_{K'}) ⊆ U_K`, the succession of `P(M, I)` over `U_K` is the push-forward along `τ` of the
succession of `P(N, J)` over `U_{K'}`, up to blow-ups whose centres lie outside the part over
`τ(U_{K'})`.

Relation to the source.
* **Translation.** `CommutesWithClosedEmbeddings P` is the rest of the last sentence of
  [Wlo09, Theorem 2.0.3], "the morphism $\mathrm{prin}$ commutes with … embeddings of ambient
  varieties", read as Kollár's commutation with closed embeddings [Kol07, Theorem 35 (5)] in the
  form of [Kol07, 34.3], $B(X, I_X, E) = j_* B(Y, I_Y, E|_Y)$ for an empty $E$.
* **Restatement.** Kollár's equation of blow-up sequences is stated over every pair of compact
  sets, up to blow-ups whose centres lie outside the part over $\tau(U_{K'})$, as the commutation
  with local analytic isomorphisms is: the succession over $U_K$ also blows up centres over
  $U_K \setminus \tau(U_{K'})$, which the succession over $U_{K'}$ does not see. -/
def CommutesWithClosedEmbeddings : Prop :=
  ∀ (T T' : IdealSheafPair.{u, v} 𝕜) (τ : C^ω⟮𝓘(𝕜, T'.E), T'.M; 𝓘(𝕜, T.E), T.M⟯),
    T.I.IsPushforwardAlong T'.I τ → (P T).IsPushforwardAlong (P T') τ

end IdealSheafPair

/-! ### Embedded pairs -/

-- The universes `u` and `v` are independent, as for `IdealSheafPair`.
set_option linter.checkUnivs false in
/-- An *embedded pair* `(M, Y)`, the input of Włodarczyk's locally finite embedded
desingularization [Wlo09, Theorem 2.0.2]: an analytic manifold `M` over `𝕜`, modelled on a
finite-dimensional space `E`, with a reduced closed analytic subspace `Y ⊆ M`, given by its ideal
sheaf (every stalk radical). The analogue on manifolds of the algebraic
`AlgebraicGeometry.EmbeddedPair` of Włodarczyk's embedded desingularization with smooth centres;
the model space is part of the input, as for `IdealSheafPair`. -/
structure EmbeddedPair (𝕜 : Type) [RCLike 𝕜] : Type (max (u + 1) (v + 1)) where
  /-- The model space. -/
  E : Type v
  [normedAddCommGroup : NormedAddCommGroup E]
  [normedSpace : NormedSpace 𝕜 E]
  [finiteDimensional : FiniteDimensional 𝕜 E]
  /-- The ambient manifold. -/
  M : AnalyticManifold.{u} 𝕜 E
  /-- The ideal sheaf of the embedded subspace. -/
  Y : IdealSheaf M
  /-- The embedded subspace is reduced: every stalk of its ideal sheaf is radical. -/
  isReduced : Y.IsReduced

attribute [instance] EmbeddedPair.normedAddCommGroup EmbeddedPair.normedSpace
  EmbeddedPair.finiteDimensional

instance EmbeddedPair.hasUnderlyingManifold :
    HasUnderlyingManifold (EmbeddedPair.{u, v} 𝕜) 𝕜 where
  model T := T.E
  manifold T := T.M

/-- The pull-back `(N, g^{-1}(Y))` of the embedded pair `(M, Y)` along a local analytic isomorphism
`g : N → M` of manifolds modelled on `E`: the source of the morphism of embedded pairs over `g`
[Wlo09, Theorem 3.5.1]. The pulled-back ideal sheaf is reduced
(`IdealSheaf.isReduced_pullback_of_isLocalDiffeomorph`). -/
noncomputable abbrev EmbeddedPair.pullback (T : EmbeddedPair.{u, v} 𝕜)
    {N : AnalyticManifold.{u} 𝕜 T.E} (g : AnalyticMap N T.M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, T.E) 𝓘(𝕜, T.E) ω g) : EmbeddedPair.{u, v} 𝕜 :=
  ⟨T.E, N, T.Y.pullback g g.contMDiff,
    Manifold.IdealSheaf.isReduced_pullback_of_isLocalDiffeomorph g hg T.isReduced⟩

/-! ### The functoriality of an assignment on embedded pairs -/

namespace EmbeddedPair

variable (R : CompatibleFamilyAssignment (EmbeddedPair.{u, v} 𝕜))

/-- A compatible family assignment `R` on the embedded pairs `(M, Y)` **commutes with local
analytic isomorphisms**: for a local analytic isomorphism `g : N → M` of manifolds modelled on
one space and the embedded pair `(N, g^{-1}(Y))`, the family `R(N, g^{-1}(Y))` is the pull-back of
`R(M, Y)` along `g` (`ExtensionCompatibleFamily.IsPullbackAlong`): for compacts `K' ⊆ N`,
`K ⊆ M` with `g(U_{K'}) ⊆ U_K`, the succession of `R(N, g^{-1}(Y))` over `U_{K'}` is the pull-back
along `g` of the succession of `R(M, Y)` over `U_K`, up to blow-ups with empty centre.

Relation to the source.
* **Translation.** `EmbeddedPair.CommutesWithLocalAnalyticIsomorphisms R` is the first half of
  [Wlo09, Theorem 2.0.2 (4)], "the morphism $\mathrm{res}_{Y,M}$ … commutes with local analytic
  isomorphisms", in the form of [Wlo09, Theorem 3.5.1 (2)]: for a local analytic isomorphism
  $\varphi$, the sequence induced by $\varphi$ from the sequence of $Y$ is an extension of the
  sequence of $\varphi^{-1}(Y)$.
* **Gap.** The lift of a local analytic isomorphism $g \colon N \to M$ to a map
  $\tilde N \to \tilde M$ identifying $\tilde N$ with the fibre product $N \times_M \tilde M$, which
  `IdealSheafPair.CommutesWithLocalAnalyticIsomorphisms` states for the principalization, is not
  stated for the embedded desingularization, and with it the global content of the exact equality
  for a surjective local analytic isomorphism [Wlo09, Theorem 3.5.1 (1)], which has no
  counterpart per pair of compact sets. -/
def CommutesWithLocalAnalyticIsomorphisms : Prop :=
  ∀ (T : EmbeddedPair.{u, v} 𝕜) {N : AnalyticManifold.{u} 𝕜 T.E} (g : AnalyticMap N T.M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, T.E) 𝓘(𝕜, T.E) ω g),
    (R (T.pullback g hg)).IsPullbackAlong (R T) g

/-- A compatible family assignment `R` on the embedded pairs **commutes with closed embeddings
of ambient manifolds**: for embedded pairs `(M, Y)` and `(N, Y')` and a closed embedding of
analytic manifolds `τ : N → M` along which the ideal sheaf of `Y` is the push-forward of that of
`Y'` (`IdealSheaf.IsPushforwardAlong`: `τ(N)` a closed submanifold containing `Y`, and
`Y' = τ^{-1}(Y)`), such that no connected component of `N` lies in `Y'` (the ideal sheaf of `Y'`
has nonzero stalks), the family `R(M, Y)` is the push-forward of `R(N, Y')` along `τ`
(`ExtensionCompatibleFamily.IsPushforwardAlong`): for compacts `K' ⊆ N`, `K ⊆ M` with
`τ(U_{K'}) ⊆ U_K`, the succession of `R(M, Y)` over `U_K` is the push-forward along `τ` of the
succession of `R(N, Y')` over `U_{K'}`, up to blow-ups whose centres lie outside the part over
`τ(U_{K'})`.

Relation to the source.
* **Translation.** `EmbeddedPair.CommutesWithClosedEmbeddings R` is the second half of
  [Wlo09, Theorem 2.0.2 (4)], "the morphism $\mathrm{res}_{Y,M}$ … commutes with … embeddings of
  ambient varieties", read as Kollár's commutation with closed embeddings [Kol07, 34.3] over every
  pair of compact sets, as `IdealSheafPair.CommutesWithClosedEmbeddings` reads the last sentence
  of [Wlo09, Theorem 2.0.3]: for a closed embedding $\tau \colon N \hookrightarrow M$ and a reduced
  $Y \subseteq N$, the embedded desingularization of $Y \subseteq M$ is the push-forward of that
  of $Y \subseteq N$, the stages of the succession over $N$ embedding over $\tau$ into those of
  the succession over $M$.
* **Restatement.** The clause is asserted when no connected component of $N$ lies in $Y$,
  Kollár's "$0 \neq I_Y$" (`T'.Y.IsNonzeroEverywhere`): on such a component the embedded
  desingularization of $Y \subseteq N$ is trivial, while that of $Y \subseteq M$ may blow up centres
  on it, where other components of $Y$ meet it. -/
def CommutesWithClosedEmbeddings : Prop :=
  ∀ (T T' : EmbeddedPair.{u, v} 𝕜) (τ : C^ω⟮𝓘(𝕜, T'.E), T'.M; 𝓘(𝕜, T.E), T.M⟯),
    T.Y.IsPushforwardAlong T'.Y τ → T'.Y.IsNonzeroEverywhere → (R T).IsPushforwardAlong (R T') τ

end EmbeddedPair

end AnalyticManifold
