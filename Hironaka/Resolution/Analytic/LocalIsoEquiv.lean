/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Triple
public import Hironaka.Manifold.IdealSheaf.Deriv
public import Hironaka.Manifold.FiniteSuccession.CenterList
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Hironaka.Manifold.FiniteSuccession.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Formal and local-isomorphism equivalence of hypersurfaces of maximal contact

Kollár's formal and étale equivalence of hypersurfaces of maximal contact [Kol07, Definition 91]
and étale equivalence of blow-up sequences [Kol07, Definition 96], on analytic manifolds, with
local analytic isomorphisms in place of étale maps. The algebraic counterparts are
`FormallyEquivalentAt`, `AgreeOn`, `EtaleEquiv` and `EtaleEquivSeq` of
`Hironaka/Resolution/Algebraic/MaximalContact/`.

* `completeIdeal J`: the image `J · Ô` of an ideal `J` of a local ring in its `𝔪`-adic completion
  (for the analytic stalk `𝒪_{M,p}` and its completion `Ô_{M,p} ≅ 𝕜⟦x₁, …, xₙ⟧`).
* `FormallyEquivalentMC I m F H H' p` (the first half of [Kol07, Definition 91]): an automorphism
  `φ` of `Ô_{M,p}` over `𝕜` with (1) `φ(Ĥ') = Ĥ` (Kollár's `φ(Ĥ) = Ĥ'` for `φ⁻¹`; equivalent,
  since (2)–(4) are symmetric in `φ` and `φ⁻¹`), (2) `φ^*(Î) = Î`, (3) `φ(Ê^i) = Ê^i` for every
  component, (4) `h − φ^*(h) ∈ MC(Î)` for every `h ∈ Ô_{M,p}`; the ideals of the hypersurfaces are
  the vanishing ideals of the sets at `p` (`vanishingStalk`) and `MC(I) = D^{m−1}(I)` is
  `iteratedDeriv (m − 1)`.
* `AgreeOnSubspace ψ ψ' J` (the analytic form of `AgreeOn`): `ψ` and `ψ'` agree on the closed
  analytic subspace `V(J)`: for every local section `h` of `𝒪_M` defined near `ψ u` and `ψ' u`,
  `ψ^*(h) − ψ'^*(h) ∈ J_u`. (Where `ψ u ≠ ψ' u` a section separating the two points forces
  `J_u = 𝒪_{U,u}`, so the maps agree on `V(J)` as a set and to the order of `J` on germs.)
* `LocalIsoPair M S`: two local analytic isomorphisms `ψ, ψ' : U ⇉ M` whose images contain `S`.
  Kollár's étale surjections are taken in this image form: surjectivity is required only onto the
  set `S` that matters, the locus `cosupp(I, m)` of order `≥ m`, so that a pair may be assembled
  from charts covering that locus alone.
* `LocallyIsoEquivalentMC I m F H H'` (the second half of [Kol07, Definition 91], in the image
  form with `S = cosupp(I, m)`): a `LocalIsoPair` with (1′) `ψ⁻¹(H) = ψ'⁻¹(H')`, (2′)
  `ψ^*I = ψ'^*I`, (3′) `ψ⁻¹(E^i) = ψ'⁻¹(E^i)` for every component, (4′) `ψ`, `ψ'` agree on
  `V(MC(ψ^*I))`.
* `LocallyIsoEquivalentSequences I m L L'` ([Kol07, Definition 96] in the image form, on lists of
  centres `CenterList`): a `LocalIsoPair` with (1) `ψ^*I = ψ'^*I`, (2) agreement on
  `V(MC(ψ^*I))`, (3) `ψ^*L = ψ'^*L'`, the canonical list-level pull-back along local analytic
  isomorphisms (`BlowUpSequence.pullback`), an equality of lists of centres of `U`.
* `FiniteSuccession.IsMarkedOne C J`: the centre of every blow-up of `C` lies in the cosupport of
  the marked transform `(Π_i)^{-1}_*(J, 1)`, the containment `Z_i^U ⊆ W_i` in the proof of
  [Kol07, Theorem 97].
* `HypersurfaceFamily.append F H`: the family `E + H`, with `H` appended last (Kollár's `H + E`;
  the counterpart of the algebraic `DivisorFamily.append`), and
  `LocallyIsoEquivalentMC.append_comap_eq`: the pulled-back families `ψ⁻¹(E + H)` and
  `ψ'⁻¹(E + H')` of an equivalent pair coincide.

These notions are the hypotheses of the uniqueness theorem for blow-up sequences of order `m` of
an `MC`-invariant ideal (the analytic form of [Kol07, Theorem 97]) and the vocabulary in which the
independence of order reduction from the choice of a hypersurface of maximal contact is proved.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory IsLocalRing AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

/-! ### The completed ideals of a local ring -/

/-- The image `J · R̂` of an ideal `J` of the local ring `R` in the `𝔪`-adic completion `R̂` (the
analytic counterpart of `completionIdeal`, for an ideal of a stalk). -/
def completeIdeal {R : Type*} [CommRing R] [IsLocalRing R] (J : Ideal R) :
    Ideal (AdicCompletion (maximalIdeal R) R) :=
  J.map (algebraMap R (AdicCompletion (maximalIdeal R) R))

theorem completeIdeal_eq {R : Type*} [CommRing R] [IsLocalRing R] (J : Ideal R) :
    completeIdeal J = J.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  rfl

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-! ### Formal equivalence -/

/-- The hypersurfaces `H` and `H'` are **formally equivalent at `p` with respect to `(M, I, E)`**
(the first half of [Kol07, Definition 91], on the completion `Ô_{M,p} ≅ 𝕜⟦x₁, …, xₙ⟧`) when an
automorphism `φ` of `Ô_{M,p}` over `𝕜` moves `(M, I, H + E)` into `(M, I, H' + E)` and is close to
the identity: (1) `φ(Ĥ') = Ĥ` (Kollár's `φ(Ĥ) = Ĥ'` for `φ⁻¹`; equivalent, since (2)–(4) are
symmetric in `φ` and `φ⁻¹` and `φ` ranges over all automorphisms), (2) `φ^*(Î) = Î`, (3)
`φ(Ê^i) = Ê^i` for every component `E^i` of `E`, (4) `h − φ^*(h) ∈ MC(Î)` for every
`h ∈ Ô_{M,p}`. The ideals of `H`, `H'`, `E^i` at `p` are
the vanishing ideals of the sets (`vanishingStalk`), `MC(I) = D^{m−1}(I)` is
`I.iteratedDeriv (m − 1)`, and `φ` acts on the ideals by `Ideal.map`, as in the algebraic
`FormallyEquivalentAt`. -/
def FormallyEquivalentMC {M : AnalyticManifold.{u} 𝕜 E} (I : AnalyticManifold.IdealSheaf M)
    (m : ℕ)
    (F : HypersurfaceFamily M) (H H' : Set M) (p : M) : Prop :=
  ∃ φ : AdicCompletion (maximalIdeal (IdealSheaf.stalkRing M p))
        (IdealSheaf.stalkRing M p) ≃ₐ[𝕜]
      AdicCompletion (maximalIdeal (IdealSheaf.stalkRing M p))
        (IdealSheaf.stalkRing M p),
    (completeIdeal (vanishingStalk (E := E) H' p)).map φ =
        completeIdeal (vanishingStalk (E := E) H p) ∧
      (completeIdeal (I.stalkIdeal p)).map φ = completeIdeal (I.stalkIdeal p) ∧
      (∀ j, (completeIdeal (vanishingStalk (E := E) (F.hyp j) p)).map φ =
        completeIdeal (vanishingStalk (E := E) (F.hyp j) p)) ∧
      ∀ h, h - φ h ∈ completeIdeal ((I.iteratedDeriv (m - 1)).stalkIdeal p)

/-! ### Agreement on a closed analytic subspace -/

/-- `ψ` and `ψ'` **agree on the closed analytic subspace `V(J)`**: for every point `u`, every open
`W ∋ ψ u, ψ' u` and every section `h` of `𝒪_M` over `W`, the germs at `u` of `h ∘ ψ` and `h ∘ ψ'`
(`germMap`) differ by an element of `J_u`. With `J = MC(ψ^*I)` this is the clause
"`ψ^*(h) − ψ'^*(h) ∈ MC(ψ^*I)` for every `h ∈ 𝒪_X`" of [Kol07, Definition 91 (4′)]; it is the
analytic form of the algebraic `AgreeOn`. -/
def AgreeOnSubspace {U M : AnalyticManifold.{u} 𝕜 E} (ψ ψ' : AnalyticMap U M)
    (J : AnalyticManifold.IdealSheaf U) : Prop :=
  ∀ (u : U) (W : Opens M) (hu : ψ u ∈ W) (hu' : ψ' u ∈ W)
    (h : (structureSheaf 𝕜 E M).presheaf.obj (op W)),
    germMap ψ ψ.contMDiff u ((structureSheaf 𝕜 E M).presheaf.germ W (ψ u) hu h) -
        germMap ψ' ψ'.contMDiff u ((structureSheaf 𝕜 E M).presheaf.germ W (ψ' u) hu' h) ∈
      J.stalkIdeal u

/-! ### Pairs of local analytic isomorphisms covering a set -/

/-- Kollár's "étale surjections `ψ, ψ' : U ⇉ X`" [Kol07, Definition 91] in the image form, for
analytic manifolds: two local analytic isomorphisms `ψ, ψ' : U ⇉ M`
(`IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω`) whose images each contain `S`. Requiring the images to
cover only the relevant set `S` rather than all of `M` lets a pair be assembled from charts
covering that set alone. -/
structure LocalIsoPair (M : AnalyticManifold.{u} 𝕜 E) (S : Set M) where
  /-- The manifold `U` (possibly disconnected: a countable disjoint union of charts). -/
  U : AnalyticManifold.{u} 𝕜 E
  /-- The first local analytic isomorphism. -/
  ψ : AnalyticMap U M
  /-- The second local analytic isomorphism. -/
  ψ' : AnalyticMap U M
  /-- `ψ` is a local analytic isomorphism. -/
  isLocalDiffeomorph_ψ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ψ
  /-- `ψ'` is a local analytic isomorphism. -/
  isLocalDiffeomorph_ψ' : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ψ'
  /-- The image of `ψ` contains `S` (the replacement for surjectivity). -/
  covers : S ⊆ Set.range ψ
  /-- The image of `ψ'` contains `S`. -/
  covers' : S ⊆ Set.range ψ'

/-! ### Local-isomorphism equivalence -/

/-- `H` and `H'` are **local-isomorphism equivalent** with respect to `(M, I, E)` for the mark `m`
(Kollár's étale equivalence, the second half of [Kol07, Definition 91], with local analytic
isomorphisms in the image form) through local analytic isomorphisms `ψ, ψ' : U ⇉ M` whose images
each contain `cosupp(I, m) = {x | ord_x I ≥ m}`, when (1′) `ψ⁻¹(H) = ψ'⁻¹(H')`, (2′)
`ψ^*I = ψ'^*I`, (3′) `ψ⁻¹(E^i) = ψ'⁻¹(E^i)` for every component of `E`, and (4′) `ψ` and `ψ'`
agree on the closed analytic subspace `V(MC(ψ^*I))`. -/
structure LocallyIsoEquivalentMC {M : AnalyticManifold.{u} 𝕜 E}
    (I : AnalyticManifold.IdealSheaf M)
    (m : ℕ) (F : HypersurfaceFamily M) (H H' : Set M)
    extends LocalIsoPair M {x | (m : ℕ∞) ≤ I.ord x} where
  /-- (1′) `ψ⁻¹(H) = ψ'⁻¹(H')`. -/
  h1 : ⇑ψ ⁻¹' H = ⇑ψ' ⁻¹' H'
  /-- (2′) `ψ^*(I) = ψ'^*(I)`. -/
  h2 : I.pullback ψ ψ.contMDiff = I.pullback ψ' ψ'.contMDiff
  /-- (3′) `ψ⁻¹(E^i) = ψ'⁻¹(E^i)` for every component. -/
  h3 : ∀ j, ⇑ψ ⁻¹' F.hyp j = ⇑ψ' ⁻¹' F.hyp j
  /-- (4′) `ψ` and `ψ'` agree on the closed analytic subspace `V(MC(ψ^*I))`. -/
  h4 : AgreeOnSubspace ψ ψ' ((I.pullback ψ ψ.contMDiff).iteratedDeriv (m - 1))

/-! ### Local-isomorphism equivalent blow-up sequences -/

/-- The blow-up sequences `L` and `L'` of `M`, given as lists of centres (`CenterList`), are
**local-isomorphism equivalent** for `(I, m)` (Kollár's étale equivalence of blow-up sequences
[Kol07, Definition 96], in the image form) through local analytic isomorphisms `ψ, ψ' : U ⇉ M`
whose images each contain `cosupp(I, m)`, when (1) `ψ^*I = ψ'^*I`, (2) `ψ` and `ψ'` agree on
`V(MC(ψ^*I))`, and (3) `ψ^*L = ψ'^*L'`: the canonical list-level pull-backs along `ψ` and `ψ'`
(`BlowUpSequence.pullback`) are equal as lists of centres of `U`.
-/
structure LocallyIsoEquivalentSequences {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}
    {M : AnalyticManifold.{u} 𝕜 E} (I : AnalyticManifold.IdealSheaf M) (m : ℕ)
        (L L' : BlowUpSequence ψ₀ M)
    extends LocalIsoPair M {x | (m : ℕ∞) ≤ I.ord x} where
  /-- (1) `ψ^*(I) = ψ'^*(I)`. -/
  h1 : I.pullback ψ ψ.contMDiff = I.pullback ψ' ψ'.contMDiff
  /-- (2) `ψ` and `ψ'` agree on the closed analytic subspace `V(MC(ψ^*I))`. -/
  h2 : AgreeOnSubspace ψ ψ' ((I.pullback ψ ψ.contMDiff).iteratedDeriv (m - 1))
  /-- (3) `ψ^* L = ψ'^* L'` as lists of centres. -/
  h3 : L.pullback ψ isLocalDiffeomorph_ψ = L'.pullback ψ' isLocalDiffeomorph_ψ'

/-! ### Sequences of order `≥ 1` for a marked ideal `(J, 1)`, in the containment form -/

/-- The centre of every blow-up of `C` lies in the cosupport of the marked transform
`(Π_i)^{-1}_*(J, 1)` at its stage (`markedTransformSeq J 1`): the containment
`Z^U_i ⊆ W_i = cosupp((Π^U_i)^{-1}_*(MC(I^U_0), 1))` in the proof of [Kol07, Theorem 97], as a
hypothesis on the sequence; the analytic form of the algebraic `IsMarkedOneSeq`. -/
def _root_.AnalyticManifold.FiniteSuccession.IsMarkedOne {U : AnalyticManifold.{u} 𝕜 E}
    (C : FiniteSuccession U) (J : AnalyticManifold.IdealSheaf U) : Prop :=
  ∀ i : Fin C.length, (C.center i).support ⊆ (C.markedTransformSeq J 1 i.castSucc).support

/-! ### Appending a hypersurface to a family -/

/-- Kollár's divisor `H + E` ("`H + E` and `H' + E` both have simple normal crossings",
[Kol07, Theorem 92]): the family `E` with the hypersurface `H` appended last, the counterpart of
the algebraic `DivisorFamily.append`, indexed as `totalTransform` indexes an appended member. -/
def _root_.Manifold.HypersurfaceFamily.append {M : Type u} (F : HypersurfaceFamily M)
    (H : Set M) : HypersurfaceFamily M where
  ι := F.ι ⊕ₗ PUnit.{u + 1}
  countable := inferInstanceAs (Countable (F.ι ⊕ PUnit.{u + 1}))
  hyp := Sum.elim F.hyp (fun _ => H) ∘ ofLex

/-! ### The appended families of an equivalent pair coincide -/

section M20

variable {M : AnalyticManifold.{u} 𝕜 E}

/-- The pulled-back families `ψ⁻¹(E + H)` and `ψ'⁻¹(E + H')` of a local-isomorphism equivalent
pair coincide: by (1′) on the appended member, by (3′) on the members of `E`. -/
theorem LocallyIsoEquivalentMC.append_comap_eq {I : AnalyticManifold.IdealSheaf M} {m : ℕ}
    {F : HypersurfaceFamily M} {H H' : Set M} (e : LocallyIsoEquivalentMC I m F H H') :
    (F.append H).comap e.ψ = (F.append H').comap e.ψ' := by
  unfold HypersurfaceFamily.comap
  congr 1
  funext j
  rcases j with k | u
  · exact e.h3 k
  · exact e.h1

end M20

end Hironaka.Manifold

end
