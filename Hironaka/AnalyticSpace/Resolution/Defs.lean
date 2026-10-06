/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Restrict.Defs
public import Hironaka.AnalyticSpace.Manifold.Defs
public import Hironaka.Manifold.FiniteSuccession.Defs
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Resolutions of analytic spaces

The terms in which the resolution of `K`-analytic spaces is stated (the form of
[Kol07, Theorem 45] in `AnalyticSpace.exists_functorial_resolution`, and its specialization to
`K = ℂ` in `AnalyticSpace.exists_surjective_resolution_of_isReduced`), as opposed to the machinery
that constructs them.

* `f.AmbientBlowUpFactorization U` and `f.IsLocallyFiniteAmbientBlowUpComposite`: over every
  relatively compact open `U ⊆ X`, `f` is the composite of finitely many blow-ups of an ambient
  manifold with smooth centres, restricted to strict transforms — the form taken here by
  clause (4) of [Kol07, Theorem 45], "projective over any compact subset", following
  [Kol07, Warning 23] and the local factorization (∗) of [Wlo09, Theorem 2.0.2]. The ambient is
  the disjoint union `AnalyticManifold.sigmaOpens G` of finitely many opens of `Kⁿ`; its closed
  subspaces are analytic spaces through `IdealSheaf.toAnalyticSpace`, and `IdealSheaf.overPiece` is
  the part of such a subspace lying over one summand.
* `Hom.IsResolution π` [Kol07, (2)] and `Hom.IsStrongResolution π` [Kol07, (3); Theorem 45
  (1)–(3)]: the properties of a value `π : R → X` of the resolution, the analytic counterparts of
  `Scheme.BlowUpSequence.IsResolution` and `Scheme.BlowUpSequence.IsStrongResolution`.
* `HasUnderlyingSpace C K`: a type `C` of inputs each with an underlying `K`-analytic space —
  the spaces themselves, and the full subcategories of a class of spaces.
  `ResolutionAssignment C`: an assignment `R` of a space `R(X)` and a morphism `Π_X : R(X) → X`
  to every input `X`, Kollár's "resolution functor `R : X ↦ (Π_X : R(X) → X)`" of
  [Kol07, Theorem 45] stripped of its properties.
* `Hom.IsStrongResolutionOntoClosureRegularLocus π`: a strong resolution whose image is the
  closure of the simple locus, clauses (1)–(3) of Theorem 45 with the image clause.
* `Hom.IsLocalIso φ`: `φ : X' → X` is a local analytic isomorphism, locally an isomorphism onto an
  open subspace of `X` (the local analytic isomorphisms of [Wlo09, Theorem 2.0.1 (3)]); and
  `ResolutionAssignment.LiftsLocalIsomorphisms R`: every isomorphism between open subspaces of two
  inputs lifts to exactly one morphism of the resolutions over it, an isomorphism, and every local
  analytic isomorphism between inputs lifts to exactly one morphism of the resolutions over it, a
  local analytic isomorphism — clause (5) of Theorem 45 for étale morphisms, and Włodarczyk's
  clause (3).
* `ReducedSpace K`: the inputs of the resolution theorem, the reduced `K`-analytic spaces as a full
  subcategory of the `K`-analytic spaces.
-/

@[expose] public section

universe u w

open scoped CategoryTheory
open CategoryTheory (IsIso)

/-! ### The ambient blow-up factorization -/

namespace AnalyticManifold.IdealSheaf

variable {K : Type} [RCLike K] {n : ℕ}

/-- The part of the closed subspace `Sp(A)/J` of `A = ⊔ᵢ Gᵢ` lying over the summand `Gᵢ`: the
points whose image in `A` has index `i`. -/
def overPiece {ι : Type u} [Countable ι] {G : ι → TopologicalSpace.Opens (Fin n → K)}
    (J : IdealSheaf (AnalyticManifold.sigmaOpens G)) (i : ι) : Set J.toAnalyticSpace :=
  {y | (J.toAnalyticSpaceι y : Σ i, ↥(G i)).1 = i}

end AnalyticManifold.IdealSheaf

namespace AnalyticSpace.Hom

open AnalyticManifold

variable {K : Type} [RCLike K]

/-- **An ambient blow-up factorization of `f : Y → X` over the open `U ⊆ X`** (after
[Kol07, Warning 23] and the local factorization (∗) of [Wlo09, Theorem 2.0.2], with the
disjoint-union ambient of the proof of [Kol07, Proposition 37]): finitely many open subspaces `Uᵢ`
covering `U`; closed embeddings `X|Uᵢ ↪ Gᵢ ⊆ Kⁿ` (one `n` for all `i`, by padding), given as the
ideal sheaf `J₀` on the ambient `A := ⊔ᵢ Gᵢ` (`sigmaOpens`) of the closed subspace `Y₀ = ⊔ᵢ X|Uᵢ`
together with isomorphisms of `X|Uᵢ` with the part of `Sp(A)/J₀` over `Gᵢ`; a finite sequence
`π₀, …, π_{r-1}` of blow-ups of `A` with smooth centres (a `FiniteSuccession`); the strict
transforms `Y₀, …, Y_r`, `Y_{k+1}` the strict transform of `Y_k` under `π_k`, of finite type (the
saturation of the pulled-back ideal along the exceptional divisor has local generators), with
`Y_r` a closed submanifold of `A_r`; and, for each `i`, an isomorphism over `Uᵢ` of
`f⁻¹(Uᵢ) → Uᵢ` with `Π_r|_{Y_r} : Y_r → Y₀ = X|Uᵢ`, `Π_r = π₀ ∘ ⋯ ∘ π_{r-1}` (the morphism of
closed subspaces over `Π_r`, unique since the canonical morphism of a closed subspace is a
monomorphism), over the piece `Gᵢ`. -/
structure AmbientBlowUpFactorization {X Y : AnalyticSpace.{u} K} (f : Y ⟶ X) (U : Set X) where
  /-- The common dimension `n` of the ambient pieces `Gᵢ ⊆ Kⁿ`. -/
  n : ℕ
  /-- The finite index set of the pieces. -/
  ι : Type u
  [finite : Finite ι]
  /-- The open subspaces `Uᵢ ⊆ X` … -/
  piece : ι → Set X
  isOpen_piece : ∀ i, IsOpen (piece i)
  /-- … covering `U`. -/
  subset_iUnion_piece : U ⊆ ⋃ i, piece i
  /-- The open subsets `Gᵢ ⊆ Kⁿ`. -/
  G : ι → TopologicalSpace.Opens (Fin n → K)
  /-- The ideal sheaf `J₀` on `A = ⊔ᵢ Gᵢ` of the closed subspace `Y₀ = ⊔ᵢ X|Uᵢ` (locally finitely
  generated). -/
  ideal : IdealSheaf (AnalyticManifold.sigmaOpens G)
  /-- The closed embeddings: `X|Uᵢ` is isomorphic to the part of `Y₀ = Sp(A)/J₀` over `Gᵢ` … -/
  emb : ∀ i, X.restrictSet (piece i) ⟶ ideal.toAnalyticSpace.restrictSet (ideal.overPiece i)
  /-- … as analytic `K`-spaces. -/
  emb_isIso : ∀ i, IsIso (emb i)
  /-- The finite sequence of blow-ups `π₀, …, π_{r-1}` of `A` with smooth centres. -/
  seq : FiniteSuccession (AnalyticManifold.sigmaOpens G)
  /-- The closed subspaces `Y_k ⊆ A_k` of the stages, … -/
  transform : ∀ k : Fin (seq.length + 1), IdealSheaf (seq.stage k)
  /-- … starting with `Y₀`, … -/
  transform_zero : transform 0 = ideal
  /-- … `Y_{k+1}` the strict transform of `Y_k` under `π_k` (`strictTransformSubspace` at the
  witnesses of the `k`-th blow-up), … -/
  transform_succ : ∀ k : Fin seq.length,
    transform k.succ = Manifold.strictTransformSubspace
      (seq.isClosedSubmanifold_center k) (seq.isBlowUp_map k) (transform k.castSucc)
  /-- … of finite type: the saturation `⋃_m (π_k⁻¹(I_{Y_k}) : I_{F}^m)` has local generators, so
  `Y_{k+1}` is the saturation and not the unit-ideal fallback of `strictTransformSubspace`. -/
  hasLocalGenerators_saturation : ∀ k : Fin seq.length,
    Manifold.IdealSheaf.HasLocalGenerators
      (𝒪 := Manifold.structureSheaf K (Fin n → K) (seq.stage k.succ))
      (Manifold.saturationStalk (seq.isClosedSubmanifold_center k) (seq.isBlowUp_map k)
        (transform k.castSucc))
  /-- `Y_r` is a closed submanifold of `A_r`: every point of `Y_r` is simple. -/
  isNonsingular_last : (transform (Fin.last seq.length)).IsNonsingular
  /-- `Π_r|_{Y_r} : Y_r → Y₀`, the morphism of closed subspaces … -/
  map : (transform (Fin.last seq.length)).toAnalyticSpace ⟶ ideal.toAnalyticSpace
  /-- … lying over `Π_r = π₀ ∘ ⋯ ∘ π_{r-1}` (the `composite` of the succession). -/
  map_comp : map ≫ ideal.toAnalyticSpaceι =
    (transform (Fin.last seq.length)).toAnalyticSpaceι ≫
      AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl K (Fin n → K)) seq.composite
  /-- The isomorphism over `Uᵢ` of `f⁻¹(Uᵢ) → Uᵢ` with `Π_r|_{Y_r}` over the piece `Gᵢ`: `f⁻¹(Uᵢ)`
  is isomorphic to the part of `Y_r` over `Gᵢ` … -/
  lift : ∀ i, Y.restrictSet (f ⁻¹' piece i) ⟶
    (transform (Fin.last seq.length)).toAnalyticSpace.restrictSet (map ⁻¹' ideal.overPiece i)
  lift_isIso : ∀ i, IsIso (lift i)
  /-- … compatibly with `f` and `Π_r|_{Y_r}`. -/
  map_lift : ∀ i, lift i ≫ map.restrictSet (ideal.overPiece i) = f.restrictSet (piece i) ≫ emb i

/-- Clause (4) of [Kol07, Theorem 45], "`Π_X` is projective over any compact subset of `X`", in
the form of [Kol07, Warning 23] and of the local factorization (∗) of [Wlo09, Theorem 2.0.2]: over
every relatively compact open `U ⊆ X`, `f` restricted to `f⁻¹(U)` is the composite of a finite
sequence of blow-ups of smooth centres of an ambient manifold, restricted to strict transforms — an
`f.AmbientBlowUpFactorization U`. The clause plays the role of Hironaka's local finiteness of a
succession [Hir64, Ch. 0, §7, p. 155]: every point has a relatively compact open neighbourhood over
which `f` is one finite composite (no compatibility between the factorizations over different
opens is asserted). -/
def IsLocallyFiniteAmbientBlowUpComposite {X Y : AnalyticSpace.{u} K} (f : Y ⟶ X) : Prop :=
  ∀ U : Set X, IsOpen U → IsCompact (closure U) → Nonempty (f.AmbientBlowUpFactorization U)

/-! ### Resolutions -/

/-- A morphism `π : R → X` of `K`-analytic spaces is a *resolution* of `X`: `R` is non-singular,
`π` is proper, and `π` is bimeromorphic (Kollár: birational [Kol07, (2)]; [Wlo09, Theorem 2.0.1]),
read onto its image: an isomorphism over an open subset `U ⊆ X` whose preimage is dense in `R`.
Kollár asks for `π` projective; only the properness that projectivity implies is recorded. The
density is asked of the preimage and not of `U`: over `ℝ` the simple locus of a reduced space need
not be dense ([Hir64, Introduction]), and then no resolution is an isomorphism over a dense open
subset of `X`. -/
@[mk_iff]
structure IsResolution {X R : AnalyticSpace.{u} K} (π : R ⟶ X) : Prop where
  /-- `R` is non-singular. -/
  isNonsingular : R.IsNonsingular
  /-- `π` is proper [Kol07, (2)] (Kollár: projective). -/
  isProperMap : IsProperMap π
  /-- `π` is an isomorphism over an open subset of `X` whose preimage is dense in `R`. -/
  exists_isIsoOver_dense_preimage : ∃ U : Set X, IsOpen U ∧ π.IsIsoOver U ∧ Dense (π ⁻¹' U)

/-- A morphism `π : R → X` of `K`-analytic spaces is a *strong resolution* of `X` [Kol07, (3)],
clauses (1)–(3) of [Kol07, Theorem 45]: a resolution (non-singular, proper, bimeromorphic onto its
image) that is an isomorphism over the simple locus `X.regularLocus` (Kollár's smooth locus
`X^{ns}`), and such that `π⁻¹(X.singularLocus)` is the support of a simple normal crossing divisor
of `R`: a closed subspace which is the reduced divisor of a locally finite family of closed smooth
hypersurfaces with simple normal crossings (`ClosedSubspace.IsSncBoundary`;
[Kol07, Definition 24]). -/
@[mk_iff]
structure IsStrongResolution {X R : AnalyticSpace.{u} K} (π : R ⟶ X) : Prop
    extends π.IsResolution where
  /-- `π` is an isomorphism over the simple locus `X^{ns}`. -/
  isIsoOver_regularLocus : π.IsIsoOver X.regularLocus
  /-- `π⁻¹(Sing X)` is the support of a simple normal crossing divisor. -/
  exists_isSncBoundary_preimage :
    ∃ E : R.ClosedSubspace, E.IsSncBoundary ∧ E.support = π ⁻¹' X.singularLocus

end AnalyticSpace.Hom

/-! ### Resolution assignments -/

namespace AnalyticSpace

variable {K : Type} [RCLike K]

-- The universes `w` of the inputs and `u` of the spaces are independent, so both occur only in the
-- `max`.
set_option linter.checkUnivs false in
/-- A type `C` of inputs each with an underlying `K`-analytic space (the analogue of
`HasUnderlyingScheme` for the algebraic inputs): the `K`-analytic spaces themselves, and the full
subcategories of the spaces of a class. -/
class HasUnderlyingSpace (C : Type w) (K : outParam Type) [RCLike K] : Type (max w (u + 1)) where
  /-- The underlying analytic space of an input. -/
  toAnalyticSpace : C → AnalyticSpace.{u} K

export HasUnderlyingSpace (toAnalyticSpace)

/-- Every `K`-analytic space is an input. -/
instance hasUnderlyingSpaceSelf : HasUnderlyingSpace (AnalyticSpace.{u} K) K where
  toAnalyticSpace X := X

/-- The objects of a full subcategory of inputs are inputs. -/
instance FullSubcategory.hasUnderlyingSpace {C : Type w} [CategoryTheory.Category C]
    [HasUnderlyingSpace.{u, w} C K] (P : CategoryTheory.ObjectProperty C) :
    HasUnderlyingSpace (CategoryTheory.ObjectProperty.FullSubcategory P) K where
  toAnalyticSpace X := toAnalyticSpace X.obj

set_option linter.checkUnivs false in
/-- A *resolution assignment* on the inputs `C`: a `K`-analytic space `R(X)` and a morphism
`Π_X : R(X) → X` to the underlying space of every input `X` — Kollár's "resolution functor
`R : X ↦ (Π_X : R(X) → X)`" [Kol07, Theorem 45] stripped of its properties, which are the clauses
of `exists_functorial_resolution`. The theorem's inputs are the reduced spaces (`ReducedSpace`);
the constructions behind it produce assignments on all spaces
(`ResolutionAssignment (AnalyticSpace K)`). -/
structure ResolutionAssignment (C : Type w) [HasUnderlyingSpace.{u, w} C K] :
    Type (max w (u + 1)) where
  /-- The resolving space `R(X)`. -/
  space : C → AnalyticSpace.{u} K
  /-- The resolution morphism `Π_X : R(X) → X`. -/
  map : ∀ X : C, space X ⟶ toAnalyticSpace X

/-! ### Strong resolutions onto the closure of the simple locus -/

/-- A morphism `π : R → X` of `K`-analytic spaces is a *strong resolution onto the closure of the
simple locus* of `X`: a strong resolution (`Hom.IsStrongResolution`: non-singular, proper,
bimeromorphic onto its image, an isomorphism over the simple locus `X.regularLocus`, and
`π⁻¹(Sing X)` the support of a simple normal crossing divisor — clauses (1)–(3) of
[Kol07, Theorem 45]) whose image is the closure of the simple locus. Over `ℂ` the simple locus of a
reduced space is dense and the clause says that `π` is surjective; over `ℝ` it need not be dense
([Hir64, Introduction]: the subspace `x² + y² = 0` of `ℝ²` is reduced with support the origin and no
simple point), and then `π` misses the part of `X` away from the closure of the simple points.

Relation to the source.
* **Strengthening.** The image clause is printed in neither source. It is what a resolution built
  over the simple locus gives, and over $\mathbb{C}$ it is the surjectivity of
  $\Pi_X$. -/
@[mk_iff]
structure Hom.IsStrongResolutionOntoClosureRegularLocus {X R : AnalyticSpace.{u} K} (π : R ⟶ X) :
    Prop extends π.IsStrongResolution where
  /-- The image of `π` is the closure of the simple locus of `X`. -/
  range_eq : Set.range π = closure X.regularLocus

/-! ### Local analytic isomorphisms -/

/-- A morphism `φ : X' ⟶ X` of `K`-analytic spaces is a *local analytic isomorphism* when every
point of `X'` has an open neighbourhood `U'` which `φ` maps isomorphically onto an open subspace
`X|_V` of `X`: an isomorphism `χ : X'|_{U'} ≅ X|_V` with `χ ≫ (X|_V → X) = (X'|_{U'} → X') ≫ φ`.
These are the local analytic isomorphisms of [Wlo09, Theorem 2.0.1 (3)] (Kollár's étale
morphisms, the smooth morphisms of relative dimension zero [Kol07, Theorem 45 (5)]): open
immersions, isomorphisms, covering maps and the morphism `∐ Uᵢ → X` from the disjoint union of an
open cover, injective or not. -/
def Hom.IsLocalIso {X' X : AnalyticSpace.{u} K} (φ : X' ⟶ X) : Prop :=
  ∀ x' : X', ∃ (U' : Set X') (V : Set X), IsOpen U' ∧ IsOpen V ∧ x' ∈ U' ∧
    ∃ χ : X'.restrictSet U' ⟶ X.restrictSet V, IsIso χ ∧
      χ ≫ KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X V) =
        KLocallyRingedSpace.ofRestrict X'.toKLocallyRingedSpace (openOf X' U') ≫ φ

namespace ResolutionAssignment

variable {C : Type w} [HasUnderlyingSpace.{u, w} C K] (R : ResolutionAssignment C)

/-- A resolution assignment `R` on the inputs `C` **lifts local analytic isomorphisms**, in two
forms. Every isomorphism `φ : X|_U → Y|_V` between open subspaces of two inputs lifts to exactly
one morphism `ψ : R(X)|_{Π_X⁻¹ U} → R(Y)|_{Π_Y⁻¹ V}` over `φ`, `ψ ≫ Π_Y|_V = Π_X|_U ≫ φ`, where
`Π_X|_U : R(X)|_{Π_X⁻¹ U} → X|_U` is the restriction of `Π_X` (composition in diagrammatic order),
and `ψ` is an isomorphism. And every local analytic isomorphism `φ : X' → X` between inputs
(`Hom.IsLocalIso`) lifts to exactly one morphism `ψ : R(X') → R(X)` over `φ`,
`ψ ≫ Π_X = Π_{X'} ≫ φ`, and `ψ` is a local analytic isomorphism. Over every open `U' ⊆ X'` which
`φ` maps isomorphically onto an open subspace `X|_V`, the lift of `φ` restricts to the lift of that
isomorphism, by the uniqueness of the latter (`LiftsLocalIsomorphisms.lift_restrict`). By the
uniqueness the lifts respect identities and composition, so `R` is a functor on the groupoid of
isomorphisms between open subspaces of inputs and on the local analytic isomorphisms between
inputs.

Relation to the source.
* **Translation.** The first form stands for clause (5) of [Kol07, Theorem 45], "$R$ commutes with
  smooth $K$-morphisms", for the smooth morphisms of relative dimension zero that are injective;
  the second is clause (3) of [Wlo09, Theorem 2.0.1], "for any local analytic isomorphism
  $\varphi \colon Y' \to Y$ there is a natural lifting $\tilde\varphi \colon \tilde Y' \to \tilde Y$
  which is a local analytic isomorphism", and the case of étale morphisms of Kollár's (5); the two
  are bundled as the two conditions of Kollár's 34.1 are in the algebraic
  `CommutesWithSmoothMorphisms`. Composition `≫` is in diagrammatic order:
  `ψ ≫ (R.map Y).restrictSet V = (R.map X).restrictSet U ≫ φ` is
  $\Pi_Y|_V \circ \psi = \varphi \circ \Pi_X|_U$, and `ψ ≫ R.map X = R.map X' ≫ φ` is
  $\Pi_X \circ \psi = \varphi \circ \Pi_{X'}$.
* **Gap.** Smooth morphisms of positive relative dimension are not lifted, and the isomorphism
  $R(Y) \cong Y \times_X R(X)$ of Kollár's (5) is not stated. -/
structure LiftsLocalIsomorphisms : Prop where
  /-- Every isomorphism between open subspaces of two inputs lifts to exactly one morphism of the
  resolutions over it, an isomorphism. -/
  exists_lift_of_isIso : ∀ (X Y : C) (U : Set (toAnalyticSpace X)) (V : Set (toAnalyticSpace Y)),
    IsOpen U → IsOpen V →
    ∀ φ : (toAnalyticSpace X).restrictSet U ⟶ (toAnalyticSpace Y).restrictSet V, IsIso φ →
      ∃ ψ : (R.space X).restrictSet (R.map X ⁻¹' U) ⟶ (R.space Y).restrictSet (R.map Y ⁻¹' V),
        IsIso ψ ∧ ∀ ψ', ψ' ≫ (R.map Y).restrictSet V = (R.map X).restrictSet U ≫ φ ↔ ψ' = ψ
  /-- Every local analytic isomorphism between inputs lifts to exactly one morphism of the
  resolutions over it, a local analytic isomorphism. -/
  exists_lift_of_isLocalIso : ∀ (X' X : C) (φ : toAnalyticSpace X' ⟶ toAnalyticSpace X),
    φ.IsLocalIso →
      ∃ ψ : R.space X' ⟶ R.space X, ψ.IsLocalIso ∧ ∀ ψ', ψ' ≫ R.map X = R.map X' ≫ φ ↔ ψ' = ψ

end ResolutionAssignment

/-! ### The inputs: reduced spaces -/

/-- The inputs of the resolution theorem: the reduced `K`-analytic spaces, as a full subcategory of
the `K`-analytic spaces. An object `X` has `X.obj : AnalyticSpace K`, its underlying space
(`toAnalyticSpace X`). -/
abbrev ReducedSpace (K : Type) [RCLike K] : Type (u + 1) :=
  CategoryTheory.ObjectProperty.FullSubcategory fun X : AnalyticSpace.{u} K => X.IsReduced

end AnalyticSpace
