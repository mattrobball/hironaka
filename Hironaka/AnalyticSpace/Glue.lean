/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.OpenSubspaceLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Carrying a local `K`-isomorphism back to the analytic space

Bookkeeping for the identification of a neighbourhood of a simple point with an open subset of
`Kⁿ` [Hir64, Ch. 0, §1, p. 121]: the `K`-isomorphism produced at a point of a local model lives
on an open of that model, and must be carried back to an open of the analytic space through the
isomorphism `X|U ≅ (local model)|W` of the local-model clause. Three formal facts do this: an
iterated open subspace `(X|V)|T` is the open subspace `X|ι(T)` (`restrictOpen_restrictOpen_iso`
on `imageOpens`, `Hironaka/AnalyticSpace/OpenSubspaceLemmas.lean`, by `isoOfRangeEq` — open
immersions into the same space with the same range are isomorphic); a `K`-isomorphism `A ≅ B`
restricts to `A|e⁻¹(T) ≅ B|T` (`restrictOpenIso`); and the image of the trace `V ∩ T`, `T ≤ V`,
is `T` again (`imageOpens_map_eq`, here, by `ext` from the membership lemma `mem_imageOpens`).
Also the
transport of regularity of stalks in the forward direction of a `K`-isomorphism and into an open
subspace.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace AnalyticSpace

namespace KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- Membership in `imageOpens V T`: the points of `V` whose trace lies in `T`. -/
theorem mem_imageOpens {X : KLocallyRingedSpace.{u} K} {V : Opens X} {T : Opens (X.restrictOpen V)}
    {x : X} : x ∈ imageOpens V T ↔ ∃ hx : x ∈ V, (⟨x, hx⟩ : V) ∈ T := by
  change x ∈ Set.range (Hom.toFun (ofRestrict (X.restrictOpen V) T ≫ ofRestrict X V)) ↔ _
  rw [Hom.range_toFun_comp, range_toFun_ofRestrict]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hT⟩
    exact ⟨⟨x, hx⟩, hT, rfl⟩

/-- The image of the trace of `T ≤ V` on `X|V` is `T`. -/
theorem imageOpens_map_eq (X : KLocallyRingedSpace.{u} K) {V T : Opens X} (h : T ≤ V) :
    imageOpens V ((Opens.map (ofRestrict X V).1.base).obj T) = T := by
  ext x
  simp only [SetLike.mem_coe]
  rw [mem_imageOpens]
  constructor
  · rintro ⟨_, hT⟩
    exact hT
  · intro hT
    exact ⟨h hT, hT⟩

/-- Regularity of stalks transports forward along a `K`-isomorphism: the converse direction of
`isRegularLocalRing_stalk_of_kIso` (`Hironaka/AnalyticSpace/RegularStalk.lean`). -/
theorem isRegularLocalRing_stalk_of_kIso' {A B : KLocallyRingedSpace.{u} K} (e : KIso A B) (a : A)
    (h : IsRegularLocalRing (A.toLocallyRingedSpace.presheaf.stalk a)) :
    IsRegularLocalRing (B.toLocallyRingedSpace.presheaf.stalk (e.hom.1.base a)) :=
  @IsRegularLocalRing.of_ringEquiv _ _ h _ _
    (asIso (e.hom.1.stalkMap a)).commRingCatIsoToRingEquiv.symm

/-- Regularity of a stalk passes from `X` to the open subspace `X|U`. -/
theorem isRegularLocalRing_stalk_restrictOpen (X : KLocallyRingedSpace.{u} K) (U : Opens X)
    (x : X.restrictOpen U) (h : IsRegularLocalRing (X.toLocallyRingedSpace.presheaf.stalk x.1)) :
    IsRegularLocalRing ((X.restrictOpen U).toLocallyRingedSpace.presheaf.stalk x) :=
  @IsRegularLocalRing.of_ringEquiv _ _ h _ _
    (X.toLocallyRingedSpace.restrictStalkIso (Opens.isOpenEmbedding U)
      x).symm.commRingCatIsoToRingEquiv

end KLocallyRingedSpace

end AnalyticSpace
