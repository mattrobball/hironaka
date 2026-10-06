/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceIndependence
public import Hironaka.Resolution.Analytic.Kol07Thm45.RestrictSetIncl
import Hironaka.AnalyticSpace.HomExtNonSingular
import Hironaka.AnalyticSpace.Lemmas
import Hironaka.AnalyticSpace.RegOpenImmersion
import Hironaka.AnalyticSpace.RegPoints
import Hironaka.Manifold.FiniteSuccession.Restrict.Lift
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionRestrict
import Hironaka.Resolution.Analytic.Wlo09.Clauses
import Hironaka.Resolution.Analytic.Wlo09.IsoOverReg
import Hironaka.Resolution.Analytic.Wlo09.PreimageSing
import Hironaka.Resolution.Analytic.Wlo09.StrictTransformDensity
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Independence of the embedding: uniqueness over the piece

This module proves the UNIQUENESS half of the independence of the local resolution from the
embedding — two morphisms of the restricted local resolutions of a piece over an open `N` of the
piece, both compatible with the maps to the piece, are equal (`localResolution_hom_ext_over`) —
with its internals; then the GLUING bridge — the uniqueness packaged as the contract
`Hom.UniqueOver` of the general gluing tools of
`Hironaka/Resolution/Analytic/Kol07Thm45/RestrictSetIncl.lean`, the general-open existence
`exists_isIso_localResolution_of_forall`, its form at the common open and
`localResolution_independent_of_local` (the independence from its local form) — and the
FUNCTORIALITY leg `resolution_commutes_localIso_of_independent` (the commutation with local analytic
isomorphisms from the independence) with its two internals
(`comp_localResolutionToPiece_transportAlongIso`, `embPreimage_transportAlongIso`).

**Mathematics** (Kollár: "any two embeddings … become equivalent by an automorphism …, which
gives the required uniqueness" [Kol07, Theorem 36, proof]; Włodarczyk: the canonical
desingularization is independent of the choice of the ambient manifold [Wlo09, §4, (3)⇒(4)]). Let
`Π = σ|_Ỹ : Ỹ → Y|_W` be the local resolution map of a piece and `Π_X : Ỹ → X|V` its composite
with the identification of `Y|_W` with an open of the piece. `Π` is an isomorphism over the simple
locus `(Y|_W).regularLocus` (`localResolutionMap_isIsoOver_reg`); the points of `Ỹ` over the
singular locus are exactly those on the exceptional divisor `E_r`
(`localResolutionMap_preimage_sing_eq_inter_exceptional`); the points of `Ỹ` off `E_r` are dense,
`Ỹ` being non-singular (clause (3) of `IsEmbeddedDesing`;
`mem_closure_cosupport_strictTransformSubspaceSeq_diff_support_of_isRegular`). Hence two morphisms
`ψ₁ ψ₂ : Ỹ₁|Π₁⁻¹N → Ỹ₂|Π₂⁻¹N` over the piece coincide on the dense open `Π₁⁻¹(regularLocus)` (there
`ψᵢ = Π₂⁻¹ ∘ Π₁`), so on all points (the target is Hausdorff), and two morphisms of NON-SINGULAR
analytic spaces with the same underlying map are equal (`hom_ext_toFun_of_isNonsingular`,
`Hironaka/AnalyticSpace/HomExtNonSingular.lean`).

**The argument.** `isNonsingular_localResolution`: clause (3) of `hbed`.
`mem_reg_iff_localResolutionToPiece`: the read-down `inv E.emb ∘ restrictedIdealHom W` is an open
immersion (`isOpenImmersion_homOfPullbackEq_of_injective`; an isomorphism), and `regularLocus`
transports along open immersions (`mem_reg_iff_of_isOpenImmersion`).
`injOn_localResolutionToPiece_preimage_reg`: `localResolutionMap_isIsoOver_reg`.
`dense_preimage_reg_localResolutionToPiece`: the two density results named above. The uniqueness:
`eqOn_of_comp_eq_of_dense` on the restricted spaces, then `hom_ext_toFun_of_isNonsingular`.

**Conventions.** Every restriction here is at an open set (`N` open by hypothesis; `Π ⁻¹' N`
open); the restriction of a space to a non-open set is by convention the whole space (`openOf`).

Not in the sources beyond the two remarks; bookkeeping.
-/

public section

open TopologicalSpace Hironaka.Manifold CategoryTheory AlgebraicGeometry
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.PieceEmbedding

open _root_.Manifold

section Internals

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {V : Set X} {n : ℕ}
  (E : PieceEmbedding 𝕜 n X V) (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
  (W : Opens (pieceAmbient.{u} 𝕜 E.G)) (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G))))

include hbed in
/-- **The local resolution is non-singular**: clause (3) of `hbed` at the piece's triple over `W`
— the final strict transform `Ỹ` is smooth ([Wlo09, Theorem 2.0.2(3)]). -/
theorem isNonsingular_localResolution :
    AnalyticSpace.IsNonsingular (E.localResolution bed W hW) := by
  obtain ⟨-, -, -, hns, -, -⟩ := hbed.1 n E.ambientTriple E.domBEDan_ambientTriple W hW
  exact hns

/-- The restriction-of-a-quotient map `restrictedIdealHom W : Sp(W)/𝓘|W → Sp(G)/𝓘` is an open
immersion: `isOpenImmersion_homOfPullbackEq_of_injective` — it is the closed-subspace morphism
along the open inclusion `W ↪ G`, injective. -/
theorem isOpenImmersion_restrictedIdealHom :
    LocallyRingedSpace.IsOpenImmersion (E.restrictedIdealHom W).1 :=
  isOpenImmersion_homOfPullbackEq_of_injective (AnalyticManifold.inclusion _ W)
    (isLocalDiffeomorph_inclusion _ W) Subtype.val_injective rfl

/-- The inverse of the piece's embedding is an open immersion — an isomorphism is one (Mathlib's
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_isIso`). -/
theorem isOpenImmersion_inv_emb [IsIso E.emb] :
    LocallyRingedSpace.IsOpenImmersion (inv E.emb).1 := by
  have hinv : IsIso (inv E.emb) := ⟨⟨E.emb, IsIso.inv_hom_id E.emb, IsIso.hom_inv_id E.emb⟩⟩
  have : IsIso (inv E.emb).1 := (AnalyticSpace.isIso_iff (inv E.emb)).mp hinv
  infer_instance

/-- **A point of the local resolution lies over a simple point of `Sp(W)/𝓘|W` iff it lies over a
simple point of the piece `X|V`** (simple points in Hironaka's sense, [Hir64, Ch. 0, §1]: the
local ring is regular): the read-down `inv E.emb ∘ restrictedIdealHom W` is an open immersion, and
`regularLocus` transports along open immersions (`mem_reg_iff_of_isOpenImmersion`). -/
theorem mem_reg_iff_localResolutionToPiece (y : E.localResolution bed W hW) :
    (E.localResolutionMap bed W hW) y ∈
        (E.restrictedIdeal W).toAnalyticSpace.regularLocus ↔
      (E.localResolutionToPiece bed W hW) y ∈
        (X.restrictSet V).regularLocus := by
  have : IsIso E.emb := E.emb_isIso
  exact (AnalyticSpace.mem_reg_iff_of_isOpenImmersion (E.restrictedIdealHom W)
    (E.isOpenImmersion_restrictedIdealHom W) _).trans
    (AnalyticSpace.mem_reg_iff_of_isOpenImmersion (inv E.emb)
      E.isOpenImmersion_inv_emb _)

include hbed in
/-- **The map to the piece is injective over the simple points of the piece**:
`localResolutionMap_isIsoOver_reg` — `Π` restricted over `(Sp(W)/𝓘|W).regularLocus` is an
isomorphism, hence injective on its preimage — read down to the piece through the injective
read-down map. -/
theorem injOn_localResolutionToPiece_preimage_reg :
    Set.InjOn ⇑(E.localResolutionToPiece bed W hW)
      (⇑(E.localResolutionToPiece bed W hW) ⁻¹'
        (X.restrictSet V).regularLocus) := by
  intro y hy y' hy' hyy'
  have : IsIso E.emb := E.emb_isIso
  -- the read-down map is injective, so the images under `Π` agree
  have hm : (E.localResolutionMap bed W hW) y =
      (E.localResolutionMap bed W hW) y' :=
    AnalyticSpace.injective_toFun_of_isOpenImmersion _
      (E.isOpenImmersion_restrictedIdealHom W)
      (AnalyticSpace.injective_toFun_of_isOpenImmersion _
        E.isOpenImmersion_inv_emb hyy')
  have hyA : (E.localResolutionMap bed W hW) y ∈
      (E.restrictedIdeal W).toAnalyticSpace.regularLocus :=
    (E.mem_reg_iff_localResolutionToPiece bed W hW y).mpr hy
  have hyA' : (E.localResolutionMap bed W hW) y' ∈
      (E.restrictedIdeal W).toAnalyticSpace.regularLocus := hm ▸ hyA
  -- the points of the restriction over the regular locus
  have hopen : IsOpen (⇑(E.localResolutionMap bed W hW) ⁻¹'
      (E.restrictedIdeal W).toAnalyticSpace.regularLocus) :=
    (AnalyticSpace.isOpen_reg _).preimage
      (AnalyticSpace.KLocallyRingedSpace.Hom.continuous_toFun _)
  have hmem : ∀ z, (E.localResolutionMap bed W hW) z ∈
      (E.restrictedIdeal W).toAnalyticSpace.regularLocus →
      z ∈ AnalyticSpace.openOf (E.localResolution bed W hW)
        (⇑(E.localResolutionMap bed W hW) ⁻¹'
          (E.restrictedIdeal W).toAnalyticSpace.regularLocus) := fun z hz =>
    (congrArg (fun U : Opens (E.localResolution bed W hW) => z ∈ U)
      (AnalyticSpace.openOf_of_isOpen _ hopen)).mpr hz
  -- the restriction is an isomorphism, so its underlying map is injective
  have hinj : Function.Injective ⇑((E.localResolutionMap bed W hW).restrictSet
      (E.restrictedIdeal W).toAnalyticSpace.regularLocus) :=
    AnalyticSpace.injective_toFun_of_isIso _
      (E.localResolutionMap_isIsoOver_reg bed W hW hbed)
  have hval : ∀ z : (E.localResolution bed W hW).restrictSet
      (⇑(E.localResolutionMap bed W hW) ⁻¹'
        (E.restrictedIdeal W).toAnalyticSpace.regularLocus),
      (((E.localResolutionMap bed W hW).restrictSet
          (E.restrictedIdeal W).toAnalyticSpace.regularLocus) z).1 =
        (E.localResolutionMap bed W hW) z.1 := fun z =>
    AnalyticSpace.KLocallyRingedSpace.Hom.toFun_restrictTo (E.localResolutionMap bed W hW)
      (AnalyticSpace.openOf _ (⇑(E.localResolutionMap bed W hW)
        ⁻¹' (E.restrictedIdeal W).toAnalyticSpace.regularLocus))
      (AnalyticSpace.openOf _ (E.restrictedIdeal W).toAnalyticSpace.regularLocus)
      (AnalyticSpace.Hom.mapsTo_openOf _ _) z
  have h := @hinj ⟨y, hmem y hyA⟩ ⟨y', hmem y' hyA'⟩
    (Subtype.ext ((hval ⟨y, hmem y hyA⟩).trans (hm.trans (hval ⟨y', hmem y' hyA'⟩).symm)))
  exact congrArg Subtype.val h

include hbed in
/-- **The points of the local resolution over the simple points of the piece are dense**: by
`localResolutionMap_preimage_sing_eq_inter_exceptional` they are the points off the exceptional
divisor `E_r`, and by `mem_closure_cosupport_strictTransformSubspaceSeq_diff_support_of_isRegular`
these accumulate at every point of the non-singular `Ỹ`. -/
theorem dense_preimage_reg_localResolutionToPiece :
    Dense (⇑(E.localResolutionToPiece bed W hW) ⁻¹'
      (X.restrictSet V).regularLocus) := by
  have hset : ⇑(E.localResolutionToPiece bed W hW) ⁻¹'
      (X.restrictSet V).regularLocus =
      ⇑(E.localResolutionMap bed W hW) ⁻¹'
        (E.restrictedIdeal W).toAnalyticSpace.regularLocus :=
    Set.ext fun y => (E.mem_reg_iff_localResolutionToPiece bed W hW y).symm
  rw [hset]
  have hsing := (E.localResolutionMap_preimage_sing_eq_inter_exceptional bed W hW hbed).1
  -- the set is the complement of the points on the exceptional divisor
  have hreg : ⇑(E.localResolutionMap bed W hW) ⁻¹'
      (E.restrictedIdeal W).toAnalyticSpace.regularLocus =
      ((fun y => (((E.localResolutionSeq bed W hW).toSuccession.strictTransformSubspaceSeq
          (E.restrictedIdeal W) (Fin.last _)).toAnalyticSpaceι y :
          (E.localResolutionSeq bed W hW).toSuccession.stage (Fin.last _))) ⁻¹'
        ((E.localResolutionSeq bed W hW).toSuccession.totalTransformSeq
          (Fin.last _)).support)ᶜ := by
    ext y
    have h2 := Set.ext_iff.mp hsing y
    exact ⟨fun h hy => (h2.mpr hy) h, fun h => not_not.mp (fun hs => h (h2.mp hs))⟩
  rw [hreg]
  have hns := E.isNonsingular_localResolution bed hbed W hW
  -- read on the subtype of the cosupport: `ι` is `Subtype.val`, an embedding
  change Dense ((Subtype.val : ((E.localResolutionSeq bed W
hW).toSuccession.strictTransformSubspaceSeq
      (E.restrictedIdeal W) (Fin.last _)).support →
      (E.localResolutionSeq bed W hW).toSuccession.stage (Fin.last _)) ⁻¹'
    ((E.localResolutionSeq bed W hW).toSuccession.totalTransformSeq (Fin.last _)).supportᶜ)
  intro y
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, Set.mem_preimage,
    Set.image_preimage_eq_inter_range, Subtype.range_coe]
  have hyreg : y ∈ (E.localResolution bed W hW).regularLocus :=
    Set.eq_univ_iff_forall.mp hns y
  have hq := (mem_reg_toAnalyticSpace_iff
    ((E.localResolutionSeq bed W hW).toSuccession.strictTransformSubspaceSeq
      (E.restrictedIdeal W) (Fin.last _)) y).mp hyreg
  have hy :=
    Hironaka.Manifold.mem_closure_cosupport_strictTransformSubspaceSeq_diff_support_of_isRegular
      (E.localResolutionSeq bed W hW).toSuccession (E.restrictedIdeal W) (Fin.last _) y.1 y.2 hq
  rwa [Set.sdiff_eq, Set.inter_comm] at hy

end Internals

section Uniqueness

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {V : Set X} {n m : ℕ}
  (E₁ : PieceEmbedding 𝕜 n X V) (E₂ : PieceEmbedding 𝕜 m X V)
  (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
  (W₁ : Opens (pieceAmbient.{u} 𝕜 E₁.G))
  (hW₁ : IsCompact (closure (W₁ : Set (pieceAmbient 𝕜 E₁.G))))
  (W₂ : Opens (pieceAmbient.{u} 𝕜 E₂.G))
  (hW₂ : IsCompact (closure (W₂ : Set (pieceAmbient 𝕜 E₂.G))))

/-- The underlying map of the restriction `f.restrictSet N` on points: `(f|_{f⁻¹N} p).1 = f p.1`
(`Hom.restrictSet_eq_restrictTo`, `Hom.toFun_restrictTo`). -/
theorem toFun_restrictSet_val {A Z : AnalyticSpace.{u} 𝕜} (f : A ⟶ Z)
    (N : Set Z)
    (p : A.restrictSet (⇑f ⁻¹' N)) :
    (f.restrictSet N p).1 = f p.1 :=
  AnalyticSpace.KLocallyRingedSpace.Hom.toFun_restrictTo f
    (AnalyticSpace.openOf _ (⇑f ⁻¹' N))
    (AnalyticSpace.openOf _ N) (AnalyticSpace.Hom.mapsTo_openOf
  f N) p

include hbed in
/-- **Uniqueness over the piece** (Kollár's "the required uniqueness", [Kol07, Theorem 36, proof];
the independence of the choice of ambient manifold, [Wlo09, §4, (3)⇒(4)]): two morphisms of the
restricted local resolutions over an OPEN `N` of the piece, both compatible with the maps to the
piece, are equal — they agree on the dense open over the simple points
(`injOn_localResolutionToPiece_preimage_reg`, `dense_preimage_reg_localResolutionToPiece`,
`eqOn_of_comp_eq_of_dense`), hence on all points, hence as morphisms of non-singular spaces
(`isNonsingular_localResolution`, `isNonsingular_restrictSet`,
`hom_ext_toFun_of_isNonsingular`). -/
theorem localResolution_hom_ext_over {N : Set (X.restrictSet V)} (hN : IsOpen N)
    (ψ₁ ψ₂ : (E₁.localResolution bed W₁ hW₁).restrictSet
        (E₁.localResolutionToPiece bed W₁ hW₁ ⁻¹' N) ⟶
        (E₂.localResolution bed W₂ hW₂).restrictSet (E₂.localResolutionToPiece bed W₂ hW₂ ⁻¹' N))
    (h₁ : ψ₁ ≫ ((E₂.localResolutionToPiece bed W₂ hW₂).restrictSet N) =
      (E₁.localResolutionToPiece bed W₁ hW₁).restrictSet N)
    (h₂ : ψ₂ ≫ ((E₂.localResolutionToPiece bed W₂ hW₂).restrictSet N) =
      (E₁.localResolutionToPiece bed W₁ hW₁).restrictSet N) : ψ₁ = ψ₂ := by
  have _hN := hN
  refine AnalyticSpace.hom_ext_toFun_of_isNonsingular
    (AnalyticSpace.isNonsingular_restrictSet
      (E₁.isNonsingular_localResolution bed hbed W₁ hW₁) _)
    (AnalyticSpace.isNonsingular_restrictSet
      (E₂.isNonsingular_localResolution bed hbed W₂ hW₂) _) ψ₁ ψ₂ (fun p => ?_)
  have : T2Space ((E₂.localResolution bed W₂ hW₂).restrictSet
      (E₂.localResolutionToPiece bed W₂ hW₂ ⁻¹' N)) :=
    inferInstanceAs (T2Space ((E₂.localResolution bed W₂ hW₂).restrictSet
      (E₂.localResolutionToPiece bed W₂ hW₂ ⁻¹' N)))
  -- injectivity of `Π₂|N` over the simple points, from `injOn_localResolutionToPiece_preimage_reg`
  have hinj : Set.InjOn
      ⇑((E₂.localResolutionToPiece bed W₂ hW₂).restrictSet N)
      (⇑((E₂.localResolutionToPiece bed W₂ hW₂).restrictSet N) ⁻¹'
        (Subtype.val ⁻¹' (X.restrictSet V).singularLocus)ᶜ) := by
    intro q hq q' hq' hqq'
    have e1 := toFun_restrictSet_val (E₂.localResolutionToPiece bed W₂ hW₂) N q
    have e2 := toFun_restrictSet_val (E₂.localResolutionToPiece bed W₂ hW₂) N q'
    have hq1 : (E₂.localResolutionToPiece bed W₂ hW₂) q.1 ∈
        (X.restrictSet V).regularLocus := by
      rw [← e1]
      exact not_not.mp hq
    have hq2 : (E₂.localResolutionToPiece bed W₂ hW₂) q'.1 ∈
        (X.restrictSet V).regularLocus := by
      rw [← e2]
      exact not_not.mp hq'
    exact Subtype.ext (E₂.injOn_localResolutionToPiece_preimage_reg bed hbed W₂ hW₂ hq1 hq2
      (e1.symm.trans ((congrArg Subtype.val hqq').trans e2)))
  -- density of the points over the simple points, from `dense_preimage_reg_localResolutionToPiece`
  have hdense : Dense
      (⇑((E₁.localResolutionToPiece bed W₁ hW₁).restrictSet N) ⁻¹'
        (Subtype.val ⁻¹' (X.restrictSet V).singularLocus)ᶜ) := by
    have hset : ⇑((E₁.localResolutionToPiece bed W₁ hW₁).restrictSet N) ⁻¹'
        (Subtype.val ⁻¹' (X.restrictSet V).singularLocus)ᶜ =
        Subtype.val ⁻¹' (⇑(E₁.localResolutionToPiece bed W₁ hW₁) ⁻¹'
          (X.restrictSet V).regularLocus) := by
      ext q
      change ¬ (((E₁.localResolutionToPiece bed W₁ hW₁).restrictSet N)
          q).1 ∈
        (X.restrictSet V).singularLocus ↔ _
      rw [toFun_restrictSet_val]
      exact not_not
    rw [hset]
    exact (E₁.dense_preimage_reg_localResolutionToPiece bed hbed W₁ hW₁).preimage
      (AnalyticSpace.openOf _ _).isOpen.isOpenMap_subtype_val
  have key := eqOn_of_comp_eq_of_dense (T := Subtype.val ⁻¹' (X.restrictSet V).singularLocus)
    hinj hdense isOpen_univ
    (AnalyticSpace.KLocallyRingedSpace.Hom.continuous_toFun ψ₁).continuousOn
    (AnalyticSpace.KLocallyRingedSpace.Hom.continuous_toFun ψ₂).continuousOn
    (fun q _ => congrArg (fun φ => φ q) h₁)
    (fun q _ => congrArg (fun φ => φ q) h₂)
  exact key (Set.mem_univ p)

end Uniqueness

section Gluing

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {V : Set X} {n m : ℕ}
  (E₁ : PieceEmbedding 𝕜 n X V) (E₂ : PieceEmbedding 𝕜 m X V)
  (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
  (W₁ : Opens (pieceAmbient.{u} 𝕜 E₁.G))
  (hW₁ : IsCompact (closure (W₁ : Set (pieceAmbient 𝕜 E₁.G))))
  (W₂ : Opens (pieceAmbient.{u} 𝕜 E₂.G))
  (hW₂ : IsCompact (closure (W₂ : Set (pieceAmbient 𝕜 E₂.G))))

open AnalyticSpace in
include hbed in
/-- The uniqueness as the contract of the gluing tools: the local resolution maps to the piece
have unique morphisms over the piece (`Hom.UniqueOver`,
`Hironaka/Resolution/Analytic/Kol07Thm45/RestrictSetIncl.lean`). -/
theorem uniqueOver_localResolutionToPiece :
    Hom.UniqueOver (A := E₁.localResolution bed W₁ hW₁) (B := E₂.localResolution bed W₂ hW₂)
      (Z := X.restrictSet V) (E₁.localResolutionToPiece bed W₁ hW₁)
      (E₂.localResolutionToPiece bed W₂ hW₂) :=
  fun hN χ₁ χ₂ h₁ h₂ => E₁.localResolution_hom_ext_over E₂ bed hbed W₁ hW₁ W₂ hW₂ hN χ₁ χ₂ h₁ h₂

open AnalyticSpace in
include hbed in
/-- **Local isomorphisms over the piece around every point of an open `O` glue to an isomorphism
over `O`** ([Kol07, Theorem 36, proof]; [Wlo09, §4, (3)⇒(4)]): the general gluing
`Hom.UniqueOver.exists_isIso_restrictSetTo` of
`Hironaka/Resolution/Analytic/Kol07Thm45/RestrictSetIncl.lean` at the local resolution maps, with
the uniqueness in both directions as the contract; `IsIso` of analytic spaces is the
`K`-local-ringed one (`Hom.isIso_iff_isIso_toKLocallyRingedSpace`). -/
theorem exists_isIso_localResolution_of_forall {O : Set (X.restrictSet V)} (hO : IsOpen O)
    (hloc : ∀ x ∈ O, ∃ N : Set (X.restrictSet V), IsOpen N ∧ x ∈ N ∧ N ⊆ O ∧
      ∃ ψ : (E₁.localResolution bed W₁ hW₁).restrictSet (E₁.localResolutionToPiece bed W₁ hW₁ ⁻¹'
          N) ⟶ (E₂.localResolution bed W₂ hW₂).restrictSet
          (E₂.localResolutionToPiece bed W₂ hW₂ ⁻¹' N),
        IsIso ψ ∧ ψ ≫ (E₂.localResolutionToPiece bed W₂ hW₂).restrictSet N =
          (E₁.localResolutionToPiece bed W₁ hW₁).restrictSet N) :
    ∃ ψ : (E₁.localResolution bed W₁ hW₁).restrictSet (E₁.localResolutionToPiece bed W₁ hW₁ ⁻¹'
        O) ⟶ (E₂.localResolution bed W₂ hW₂).restrictSet
        (E₂.localResolutionToPiece bed W₂ hW₂ ⁻¹' O),
      IsIso ψ ∧ ψ ≫ (E₂.localResolutionToPiece bed W₂ hW₂).restrictSet O =
        (E₁.localResolutionToPiece bed W₁ hW₁).restrictSet O := by
  have hU₁ : Hom.UniqueOver (A := E₁.localResolution bed W₁ hW₁)
      (B := E₂.localResolution bed W₂ hW₂) (Z := X.restrictSet V)
      (E₁.localResolutionToPiece bed W₁ hW₁) (E₂.localResolutionToPiece bed W₂ hW₂) :=
    E₁.uniqueOver_localResolutionToPiece E₂ bed hbed W₁ hW₁ W₂ hW₂
  have hU₂ : Hom.UniqueOver (A := E₂.localResolution bed W₂ hW₂)
      (B := E₁.localResolution bed W₁ hW₁) (Z := X.restrictSet V)
      (E₂.localResolutionToPiece bed W₂ hW₂) (E₁.localResolutionToPiece bed W₁ hW₁) :=
    E₂.uniqueOver_localResolutionToPiece E₁ bed hbed W₂ hW₂ W₁ hW₁
  obtain ⟨ψ, hi, hc⟩ := Hom.UniqueOver.exists_isIso_restrictSetTo hU₁ hU₂ hO
    (fun x hx => by
      obtain ⟨N, hN, hxN, hNO, ψ, hi, hc⟩ := hloc x hx
      exact ⟨N, hN, hxN, hNO, ψ, (Hom.isIso_iff_isIso_toKLocallyRingedSpace
        (X := (E₁.localResolution bed W₁ hW₁).restrictSet (E₁.localResolutionToPiece bed W₁ hW₁ ⁻¹'
            N))
        (Y := (E₂.localResolution bed W₂ hW₂).restrictSet (E₂.localResolutionToPiece bed W₂ hW₂ ⁻¹'
            N))
        ψ).mp hi, hc⟩)
  exact ⟨ψ, (Hom.isIso_iff_isIso_toKLocallyRingedSpace
    (X := (E₁.localResolution bed W₁ hW₁).restrictSet (E₁.localResolutionToPiece bed W₁ hW₁ ⁻¹' O))
    (Y := (E₂.localResolution bed W₂ hW₂).restrictSet (E₂.localResolutionToPiece bed W₂ hW₂ ⁻¹' O))
    ψ).mpr hi, hc⟩

end Gluing

section

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {V : Set X} {n m : ℕ}
  (E₁ : PieceEmbedding 𝕜 n X V) (E₂ : PieceEmbedding 𝕜 m X V)
  (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
  (W₁ : Opens (pieceAmbient.{u} 𝕜 E₁.G))
  (hW₁ : IsCompact (closure (W₁ : Set (pieceAmbient 𝕜 E₁.G))))
  (W₂ : Opens (pieceAmbient.{u} 𝕜 E₂.G))
  (hW₂ : IsCompact (closure (W₂ : Set (pieceAmbient 𝕜 E₂.G))))

include hbed in
/-- **The EXISTENCE half of the independence from its local form**: the local isomorphisms over
the piece glue to an isomorphism over the common open `embPreimage W₁ ∩ embPreimage W₂`
(`exists_isIso_localResolution_of_forall` at that open, `isOpen_embPreimage`). -/
theorem exists_isIso_localResolution_of_local
    (hloc : ∀ (x : X.restrictSet V), x ∈ E₁.embPreimage W₁ → x ∈ E₂.embPreimage W₂ →
      ∃ N : Set (X.restrictSet V), IsOpen N ∧ x ∈ N ∧ N ⊆ E₁.embPreimage W₁ ∩ E₂.embPreimage W₂ ∧
        ∃ ψ : (E₁.localResolution bed W₁ hW₁).restrictSet (E₁.localResolutionToPiece bed W₁ hW₁ ⁻¹'
            N) ⟶ (E₂.localResolution bed W₂ hW₂).restrictSet
            (E₂.localResolutionToPiece bed W₂ hW₂ ⁻¹' N),
          IsIso ψ ∧
          ψ ≫ (E₂.localResolutionToPiece bed W₂ hW₂).restrictSet N =
            (E₁.localResolutionToPiece bed W₁ hW₁).restrictSet N) :
    ∃ ψ : (E₁.localResolution bed W₁ hW₁).restrictSet (E₁.localResolutionToPiece bed W₁ hW₁ ⁻¹'
        (E₁.embPreimage W₁ ∩ E₂.embPreimage
        W₂)) ⟶ (E₂.localResolution bed W₂ hW₂).restrictSet
        (E₂.localResolutionToPiece bed W₂ hW₂ ⁻¹' (E₁.embPreimage W₁ ∩ E₂.embPreimage W₂)),
      IsIso ψ ∧
      ψ ≫ (E₂.localResolutionToPiece bed W₂ hW₂).restrictSet (E₁.embPreimage W₁ ∩ E₂.embPreimage
          W₂) =
        (E₁.localResolutionToPiece bed W₁ hW₁).restrictSet (E₁.embPreimage W₁ ∩ E₂.embPreimage
            W₂) :=
  E₁.exists_isIso_localResolution_of_forall E₂ bed hbed W₁ hW₁ W₂ hW₂
    ((E₁.isOpen_embPreimage W₁).inter (E₂.isOpen_embPreimage W₂)) fun x hx => hloc x hx.1 hx.2

include hbed in
/-- **The independence from its local form** ([Kol07, Theorem 36, proof]; [Wlo09, §4, (3)⇒(4)]):
the unique isomorphism over the common open `E₁.embPreimage W₁ ∩ E₂.embPreimage W₂` from the
conclusion of `localResolution_independent_local` (`LocalResolutionShear.lean`) as the hypothesis
`hloc` — existence by the gluing (`exists_isIso_localResolution_of_local`), uniqueness by
`localResolution_hom_ext_over` at the common open. -/
theorem localResolution_independent_of_local
    (hloc : ∀ (x : X.restrictSet V), x ∈ E₁.embPreimage W₁ → x ∈ E₂.embPreimage W₂ →
      ∃ N : Set (X.restrictSet V), IsOpen N ∧ x ∈ N ∧ N ⊆ E₁.embPreimage W₁ ∩ E₂.embPreimage W₂ ∧
        ∃ ψ : (E₁.localResolution bed W₁ hW₁).restrictSet (E₁.localResolutionToPiece bed W₁ hW₁ ⁻¹'
            N) ⟶ (E₂.localResolution bed W₂ hW₂).restrictSet
            (E₂.localResolutionToPiece bed W₂ hW₂ ⁻¹' N),
          IsIso ψ ∧
          ψ ≫ (E₂.localResolutionToPiece bed W₂ hW₂).restrictSet N =
            (E₁.localResolutionToPiece bed W₁ hW₁).restrictSet N) :
    ∃! ψ : (E₁.localResolution bed W₁ hW₁).restrictSet (E₁.localResolutionToPiece bed W₁ hW₁ ⁻¹'
        (E₁.embPreimage W₁ ∩ E₂.embPreimage
        W₂)) ⟶ (E₂.localResolution bed W₂ hW₂).restrictSet
        (E₂.localResolutionToPiece bed W₂ hW₂ ⁻¹' (E₁.embPreimage W₁ ∩ E₂.embPreimage W₂)),
      IsIso ψ ∧
      ψ ≫ (E₂.localResolutionToPiece bed W₂ hW₂).restrictSet (E₁.embPreimage W₁ ∩ E₂.embPreimage
          W₂) =
        (E₁.localResolutionToPiece bed W₁ hW₁).restrictSet (E₁.embPreimage W₁ ∩ E₂.embPreimage
            W₂) := by
  obtain ⟨ψ, hi, hc⟩ :=
    E₁.exists_isIso_localResolution_of_local E₂ bed hbed W₁ hW₁ W₂ hW₂ hloc
  refine ⟨ψ, ⟨hi, hc⟩, fun ψ' h' => ?_⟩
  exact E₁.localResolution_hom_ext_over E₂ bed hbed W₁ hW₁ W₂ hW₂
    ((E₁.isOpen_embPreimage W₁).inter (E₂.isOpen_embPreimage W₂)) ψ' ψ h'.2 hc

end

section Functoriality

variable {𝕜 : Type} [RCLike 𝕜] {X Y : AnalyticSpace.{u} 𝕜} {V : Set X} {U : Set Y}
    {n m : ℕ}
  (φ : X.restrictSet V ⟶ Y.restrictSet U) (hφ : IsIso φ)
  (E : PieceEmbedding 𝕜 n X V) (F : PieceEmbedding 𝕜 m Y U)
  (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
  (W : Opens (pieceAmbient.{u} 𝕜 E.G)) (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G))))
  (W' : Opens (pieceAmbient.{u} 𝕜 F.G))
  (hW' : IsCompact (closure (W' : Set (pieceAmbient 𝕜 F.G))))

include hφ in
/-- The map to the piece of the transported embedding `F.transportAlongIso φ hφ` (the transport
of an embedding along an isomorphism of pieces; compare the lifting of a smooth morphism to the
ambient spaces in [Kol07, Lemma 41]) lies over `φ`: `φ ∘ Π_{F'} = Π_F` — the transport keeps the
ambient, the ideal and the local resolution, and its embedding is `F.emb ∘ φ`, so
`inv (φ ≫ F.emb) ≫ φ = inv F.emb`. -/
theorem comp_localResolutionToPiece_transportAlongIso :
    (F.transportAlongIso φ hφ).localResolutionToPiece bed W' hW' ≫ φ =
      F.localResolutionToPiece bed W' hW' := by
  have hF : IsIso F.emb := F.emb_isIso
  have hφ' : IsIso φ := hφ
  have hFφ : IsIso (CategoryStruct.comp φ F.emb) := (F.transportAlongIso φ hφ).emb_isIso
  -- `inv (φ ≫ F.emb) ≫ φ = inv F.emb` (term-level: the objects are definitional aliases)
  have key : CategoryStruct.comp (inv (CategoryStruct.comp φ F.emb)) φ = inv F.emb :=
    (IsIso.inv_comp_eq _).mpr
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => CategoryStruct.comp φ k) (IsIso.hom_inv_id F.emb)).trans
          (Category.comp_id φ))).symm
  change CategoryStruct.comp (CategoryStruct.comp
      (CategoryStruct.comp (F.localResolutionMap bed W' hW') (F.restrictedIdealHom W'))
      (inv (CategoryStruct.comp φ F.emb))) φ =
    CategoryStruct.comp (CategoryStruct.comp (F.localResolutionMap bed W' hW')
      (F.restrictedIdealHom W')) (inv F.emb)
  exact (Category.assoc _ _ _).trans (congrArg (fun k => CategoryStruct.comp
    (CategoryStruct.comp (F.localResolutionMap bed W' hW') (F.restrictedIdealHom W')) k) key)

/-- The points of the piece `X|V` over `W'` for the transported embedding are the preimage under
`φ` of the points of `Y|U` over `W'` (`(F.transportAlongIso φ hφ).ambientPoint x = F.ambientPoint
(φ x)` by definition of the transport). -/
theorem embPreimage_transportAlongIso :
    (F.transportAlongIso φ hφ).embPreimage W' = φ ⁻¹' F.embPreimage W' :=
  Set.ext fun _ => Iff.rfl

open AnalyticSpace in
include hφ in
/-- **The commutation with local isomorphisms from the independence** (Kollár's reduction of the
functoriality for smooth morphisms to the embedded case, [Kol07, Theorem 36, proof];
[Wlo09, Theorem 6.0.6(2)]): the unique isomorphism over `φ` of the restricted local resolutions
from the independence over `X|V` at the fixed `bed` as the hypothesis `hind` — the independence
at `E` and the transported embedding `F.transportAlongIso φ hφ` (same ambient, same ideal, the
embedding `F.emb ∘ φ`), the two opens identified through `φ` (an isomorphism, hence injective:
`E.embPreimage W ∩ F'.embPreimage W' = φ⁻¹(φ(E.embPreimage W) ∩ F.embPreimage W')`), and the
general transport `Hom.existsUnique_isIso_restrictSetTo_transport` of
`Hironaka/Resolution/Analytic/Kol07Thm45/RestrictSetIncl.lean`. The hypothesis `IsEmbeddedDesing`
enters only through `hind`. -/
theorem resolution_commutes_localIso_of_independent
    (hind : ∀ {n' m' : ℕ} (E₁ : PieceEmbedding 𝕜 n' X V) (E₂ : PieceEmbedding 𝕜 m' X V)
      (W₁ : Opens (pieceAmbient.{u} 𝕜 E₁.G))
      (hW₁ : IsCompact (closure (W₁ : Set (pieceAmbient 𝕜 E₁.G))))
      (W₂ : Opens (pieceAmbient.{u} 𝕜 E₂.G))
      (hW₂ : IsCompact (closure (W₂ : Set (pieceAmbient 𝕜 E₂.G)))),
      ∃! ψ : (E₁.localResolution bed W₁ hW₁).restrictSet (E₁.localResolutionToPiece bed W₁ hW₁ ⁻¹'
          (E₁.embPreimage W₁ ∩ E₂.embPreimage
          W₂)) ⟶ (E₂.localResolution bed W₂ hW₂).restrictSet
          (E₂.localResolutionToPiece bed W₂ hW₂ ⁻¹' (E₁.embPreimage W₁ ∩ E₂.embPreimage W₂)),
        IsIso ψ ∧
        ψ ≫ (E₂.localResolutionToPiece bed W₂ hW₂).restrictSet (E₁.embPreimage W₁ ∩ E₂.embPreimage
            W₂) =
          (E₁.localResolutionToPiece bed W₁ hW₁).restrictSet (E₁.embPreimage W₁ ∩ E₂.embPreimage
              W₂)) :
    ∃! ψ : (E.localResolution bed W hW).restrictSet (E.localResolutionToPiece bed W hW ⁻¹'
        (φ ⁻¹' (φ '' E.embPreimage W ∩ F.embPreimage
        W'))) ⟶ (F.localResolution bed W' hW').restrictSet
        (F.localResolutionToPiece bed W' hW' ⁻¹' (φ '' E.embPreimage W ∩ F.embPreimage W')),
      IsIso ψ ∧
      ψ ≫ (F.localResolutionToPiece bed W' hW').restrictSet (φ '' E.embPreimage W ∩ F.embPreimage
          W') =
        (E.localResolutionToPiece bed W hW).restrictSet (φ ⁻¹'
            (φ '' E.embPreimage W ∩ F.embPreimage
            W')) ≫ φ.restrictSet (φ '' E.embPreimage W ∩ F.embPreimage W') := by
  have hφK : @CategoryTheory.IsIso (KLocallyRingedSpace.{u} 𝕜) _ _ _ φ :=
    (Hom.isIso_iff_isIso_toKLocallyRingedSpace φ).mp hφ
  have hinj : Function.Injective ⇑φ :=
      injective_toFun_of_isIso φ hφ
  have hO' : E.embPreimage W ∩ (F.transportAlongIso φ hφ).embPreimage W' =
      φ ⁻¹' (φ '' E.embPreimage W ∩ F.embPreimage W') := by
    rw [embPreimage_transportAlongIso, Set.preimage_inter, Set.preimage_image_eq _ hinj]
  have h := (existsUnique_congr fun ψ =>
    and_congr_left' (Hom.isIso_iff_isIso_toKLocallyRingedSpace ψ)).mp
    (hind E (F.transportAlongIso φ hφ) W hW W' hW')
  have key := Hom.existsUnique_isIso_restrictSetTo_transport (A := E.localResolution bed W hW)
    (B := F.localResolution bed W' hW') (Z := X.restrictSet V) (Z' := Y.restrictSet U)
    (E.localResolutionToPiece bed W hW) (F.localResolutionToPiece bed W' hW') φ hO'
    (comp_localResolutionToPiece_transportAlongIso φ hφ F bed W' hW') h
  exact (existsUnique_congr fun ψ =>
    and_congr_left' (Hom.isIso_iff_isIso_toKLocallyRingedSpace ψ)).mpr key

end Functoriality

end Hironaka.Manifold.PieceEmbedding
