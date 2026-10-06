/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Manifold.StratumIso
import Hironaka.AnalyticSpace.Complexification
import Hironaka.AnalyticSpace.HomLocal
import Hironaka.AnalyticSpace.Manifold.FullyFaithful
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Morphisms of non-singular analytic `K`-spaces are determined by their underlying maps

`hom_ext_toFun_of_isNonsingular`: two `K`-morphisms `f g : X ⟶ Y` of analytic `K`-spaces with `X`
and `Y` non-singular (`IsNonsingular`: every stalk a regular local ring) and the same underlying
map are equal — compare the local `Kⁿ`-coordinations of [Hir64, Ch. 0, §1, p. 120], through
which a morphism is read off its coordinate functions; the manifold case is `hom_ext_baseFun`
(`Hironaka/AnalyticSpace/Manifold/FullyFaithful.lean`). Used for the uniqueness of the local
resolution over a piece (`Hironaka/Resolution/Analytic/Kol07Thm45/LocalResolutionIndependent.lean`;
the uniqueness in the proof of [Kol07, Theorem 36] and in [Wlo09, Theorem 6.0.6 (1)]): two
morphisms of local resolutions over the piece agree on a dense open, hence on points, hence as
morphisms.

**Why non-singular, not reduced.** Over `ℝ` the reduced singular space `Y = V(x(x² + y²)) ⊂ ℝ²` has
real points the line `{x = 0}`, and the section `x` vanishes on the dense open `Y ∖ {0}` yet is
nonzero in `𝒪_{Y,0}`; "agreeing on a dense open" does not determine a morphism out of such a
source. On a non-singular space the sections are analytic functions on charts, determined by their
values, over `ℝ` as over `ℂ`.

**Proof.** Equality of `K`-morphisms is local on the source (`hom_ext_of_cover`). `X` is covered by
its dimension strata `X_d = dimOpens X hX d` (`iUnion_dimSet_eq_univ`,
`Hironaka/AnalyticSpace/Manifold/Stratum.lean`), each the space of an analytic manifold through the
comparison isomorphism `stratumKIso : Sp(X_d) ≅ X | X_d`
(`Hironaka/AnalyticSpace/Manifold/StratumIso.lean`) whose base map is the identity on points.
Composing with it, `f` and `g` become two morphisms `F, G : Sp(X_d) ⟶ Y` with the same base map.
`Sp(X_d)` is covered by the preimages `P = F⁻¹(Y_{d'})` of the strata of `Y`; on `P` both `F` and
`G` factor through the open immersion `Y | Y_{d'} → Y` as their restrictions `Hom.restrictTo`
(`restrictTo_comp_ofRestrict`), and the restrictions, read between the manifold spaces
`Sp(P) ≅ Sp(X_d) | P` (`ofManifold_restrictOpen_iso`) and `Sp(Y_{d'}) ≅ Y | Y_{d'}` (`stratumKIso`),
are morphisms of manifold spaces with the same underlying map (`Hom.toFun_restrictTo`, the base
lemmas of the two isomorphisms), hence equal by `hom_ext_baseFun`; cancelling the isomorphisms
gives the equality of the restrictions, and the two open-cover arguments give `f = g`. Routine.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AnalyticSpace.KLocallyRingedSpace
open scoped Manifold ContDiff

universe u

namespace AnalyticSpace

variable {K : Type} [RCLike K]

/-- The base map of the inverse of the stratum isomorphism `Sp(X_d) ≅ X | X_d` is the identity on
points (its `hom` is `stratumHom`, whose base map is the identity, `stratumHom_base_apply`). -/
theorem stratumKIso_inv_base_apply (X : AnalyticSpace.{u} K) (hX : X.IsNonsingular) (d : ℕ)
    (q : stratumRestrict X hX d) : (stratumKIso X hX d).inv.1.base q = q := by
  have h := KIso.hom_base_inv_base (stratumKIso X hX d) q
  rwa [show (stratumKIso X hX d).hom = stratumHom X hX d from rfl, stratumHom_base_apply] at h

/-- The inverse of the stratum isomorphism is the identity on points, for the underlying map
`Hom.toFun`. -/
theorem stratumKIso_inv_toFun_apply (X : AnalyticSpace.{u} K) (hX : X.IsNonsingular) (d : ℕ)
    (q : stratumRestrict X hX d) :
    KLocallyRingedSpace.Hom.toFun (stratumKIso X hX d).inv q = q :=
  stratumKIso_inv_base_apply X hX d q

/-- The manifold-source case: two `K`-morphisms from the space `Sp(M)` of an analytic manifold into
a non-singular analytic `K`-space with the same underlying map are equal — locality on the source
over the preimages of the dimension strata of the target, `Hom.restrictTo` into a stratum, the
isomorphisms `Sp(M) | P ≅ Sp(P)` and `Sp(Y_{d'}) ≅ Y | Y_{d'}`, and `hom_ext_baseFun` between
manifold spaces. -/
theorem hom_ext_toFun_of_isNonsingular_of_manifold {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (Fin d → K) M] [IsManifold 𝓘(K, Fin d → K) ω M] {Y : AnalyticSpace.{u} K}
    (hY : Y.IsNonsingular) (F G : ofManifold K (Fin d → K) M ⟶ Y.toKLocallyRingedSpace)
    (h : ∀ y, KLocallyRingedSpace.Hom.toFun F y = KLocallyRingedSpace.Hom.toFun G y) : F = G := by
  -- equality is local on the source: the preimages of the dimension strata of `Y` cover `M`
  refine KLocallyRingedSpace.hom_ext_of_cover F G
    (fun d' : ℕ => (Opens.map F.1.base).obj (dimOpens Y hY d')) (fun y => ?_) (fun d' => ?_)
  · have hy : KLocallyRingedSpace.Hom.toFun F y ∈ ⋃ d' : ℕ, dimSet Y d' := by
      rw [iUnion_dimSet_eq_univ Y hY]
      exact Set.mem_univ _
    obtain ⟨d', hd'⟩ := Set.mem_iUnion.mp hy
    exact ⟨d', hd'⟩
  -- on `P = F⁻¹(Y_{d'})` both factor through the open immersion `Y | Y_{d'} → Y`
  have hmF : ∀ a ∈ (Opens.map F.1.base).obj (dimOpens Y hY d'),
      KLocallyRingedSpace.Hom.toFun F a ∈ dimOpens Y hY d' := fun a ha => ha
  have hmG : ∀ a ∈ (Opens.map F.1.base).obj (dimOpens Y hY d'),
      KLocallyRingedSpace.Hom.toFun G a ∈ dimOpens Y hY d' := fun a ha => by
    rw [← h a]
    exact ha
  generalize hP : (Opens.map F.1.base).obj (dimOpens Y hY d') = P at hmF hmG ⊢
  rw [← Hom.restrictTo_comp_ofRestrict F P (dimOpens Y hY d') hmF,
    ← Hom.restrictTo_comp_ofRestrict G P (dimOpens Y hY d') hmG]
  congr 1
  -- read between the manifold spaces `Sp(P)` and `Sp(Y_{d'})`: equal there by their base maps
  rw [← cancel_mono (stratumKIso Y hY d').inv,
    ← cancel_epi (ofManifold_restrictOpen_iso (K := K) (E := Fin d → K) (M := M) P).inv]
  refine hom_ext_baseFun (ContinuousLinearEquiv.refl K (Fin d → K))
    (ContinuousLinearEquiv.refl K (Fin d' → K)) _ _ (funext fun p => ?_)
  change KLocallyRingedSpace.Hom.toFun (stratumKIso Y hY d').inv
      (KLocallyRingedSpace.Hom.toFun (Hom.restrictTo F P (dimOpens Y hY d') hmF)
        (KLocallyRingedSpace.Hom.toFun
          (ofManifold_restrictOpen_iso (K := K) (E := Fin d → K) (M := M) P).inv p)) =
    KLocallyRingedSpace.Hom.toFun (stratumKIso Y hY d').inv
      (KLocallyRingedSpace.Hom.toFun (Hom.restrictTo G P (dimOpens Y hY d') hmG)
        (KLocallyRingedSpace.Hom.toFun
          (ofManifold_restrictOpen_iso (K := K) (E := Fin d → K) (M := M) P).inv p))
  rw [stratumKIso_inv_toFun_apply, stratumKIso_inv_toFun_apply]
  apply Subtype.ext
  exact (Hom.toFun_restrictTo F P (dimOpens Y hY d') hmF _).trans
    ((h _).trans (Hom.toFun_restrictTo G P (dimOpens Y hY d') hmG _).symm)

/-- **Two morphisms of non-singular analytic `K`-spaces with the same underlying map are equal**
(compare the local `Kⁿ`-coordinations of [Hir64, Ch. 0, §1, p. 120]): locality on the source
(`hom_ext_of_cover`) over the dimension strata of `X`, the comparison isomorphism
`stratumKIso : Sp(X_d) ≅ X | X_d` to a manifold space, and the manifold-source case. -/
theorem hom_ext_toFun_of_isNonsingular {X Y : AnalyticSpace.{u} K} (hX : X.IsNonsingular)
    (hY : Y.IsNonsingular) (f g : X ⟶ Y) (h : ∀ x, Hom.toFun f x = Hom.toFun g x) : f = g := by
  -- equality is local on the source: the dimension strata of `X` cover it
  refine KLocallyRingedSpace.hom_ext_of_cover
    (f : X.toKLocallyRingedSpace ⟶ Y.toKLocallyRingedSpace) g (fun d : ℕ => dimOpens X hX d)
    (fun x => ?_) (fun d => ?_)
  · have hx : x ∈ ⋃ d : ℕ, dimSet X d := by
      rw [iUnion_dimSet_eq_univ X hX]
      exact Set.mem_univ x
    obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hx
    exact ⟨d, hd⟩
  -- transport along the stratum isomorphism `Sp(X_d) ≅ X | X_d` and apply the manifold-source case
  rw [← cancel_epi (stratumKIso X hX d).hom]
  refine hom_ext_toFun_of_isNonsingular_of_manifold hY _ _ (fun y => ?_)
  exact h _

end AnalyticSpace
