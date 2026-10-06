/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Defs
import Hironaka.AnalyticSpace.Glue
import Hironaka.AnalyticSpace.Jacobian
import Hironaka.AnalyticSpace.ModelIso
import Hironaka.AnalyticSpace.RegularStalk
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Simple points are manifold points; the simple points form an open set

Hironaka [Hir64, Ch. 0, §1, p. 121]: a point `x` of an analytic `K`-space `X` is simple (`𝒪_{X,x}`
regular) iff some open neighbourhood `X|V` is `K`-isomorphic to a local analytic `K`-space
`(G', 𝒜_{G'})`, `G' ⊆ K^d` open — here with `d = dim 𝒪_{X,x}`
(`isRegular_stalk_iff_exists_manifold_nhd`). Hironaka has it "by means of jacobian criterion and
the implicit function theorem"; the argument here: the easy half is
`isRegularLocalRing_stalk_of_kIso_analyticSpaceOfOpen` (`Hironaka/AnalyticSpace/RegularStalk.lean`).
For the other, the local-model clause of `AnalyticSpace` gives `X|U ≅ (local model)|W` with
`x ↦ w`; regularity passes to the stalk of the model at `z = w`, where the Jacobian criterion
hands over `c` germs generating `𝓘_z` with independent differentials
(`exists_span_eq_of_isRegularLocalRing_stalk`, `Hironaka/AnalyticSpace/Jacobian.lean`), the implicit
function theorem gives `(model)|V₁ ≅ (G', 𝒜_{G'})` with `G' ⊆ K^{n−c}`
(`exists_kIso_analyticSpaceOfOpen_of_span_germ_eq`, `Hironaka/AnalyticSpace/ModelIso.lean`), and the
isomorphisms are carried back to an open `V' ∋ x` of `X` through `Hironaka/AnalyticSpace/Glue.lean`.
Hence `X.regularLocus` is open (`isOpen_reg`), every point of the neighbourhood `V` being simple,
and `X.singularLocus = (X.regularLocus)ᶜ` is closed (`isClosed_singularLocus`) — "the open subspace
of `X` which consists of the simple points of `X`" [Hir64, Introduction].
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AnalyticSpace.KLocallyRingedSpace

universe u


namespace AnalyticSpace

variable {K : Type} [RCLike K]

/-- **A point is simple iff it has a manifold neighbourhood** [Hir64, Ch. 0, §1, p. 121]: `x` is a
simple point of the analytic `K`-space `X` iff, for `d = dim 𝒪_{X,x}`, some open neighbourhood
`X|V` of `x` is `K`-isomorphic to a local analytic `K`-space `(G', 𝒜_{G'})` with `G' ⊆ K^d` open. -/
theorem isRegular_stalk_iff_exists_manifold_nhd (X : AnalyticSpace.{u} K) (x : X) :
    x ∈ regularLocus X ↔
      ∃ d : ℕ, ringKrullDim (X.toLocallyRingedSpace.presheaf.stalk x) = ((d : ℕ) : WithBot ℕ∞) ∧
        ∃ (V : Opens X) (_ : x ∈ V) (G' : Opens (Kn.{u} K d)),
          Nonempty (KIso (X.toKLocallyRingedSpace.restrictOpen V)
            (analyticSpaceOfOpen K d G')) := by
  constructor
  · intro hx
    obtain ⟨U, hxU, n, k, G, f, W, ⟨e₀⟩⟩ := X.locallyModel x
    -- the model point `w` and the regularity of its stalk
    have h1 := KLocallyRingedSpace.isRegularLocalRing_stalk_restrictOpen X.toKLocallyRingedSpace U
      ⟨x, hxU⟩ hx
    have h2 := KLocallyRingedSpace.isRegularLocalRing_stalk_of_kIso' e₀ ⟨x, hxU⟩ h1
    have h3 := KLocallyRingedSpace.isRegularLocalRing_stalk_of_restrictOpen _ W _ h2
    have hd1 : ringKrullDim (X.toLocallyRingedSpace.presheaf.stalk x) =
        ringKrullDim ((localModel K n G f).toLocallyRingedSpace.presheaf.stalk
          (e₀.hom.1.base ⟨x, hxU⟩).1) := by
      rw [← KLocallyRingedSpace.ringKrullDim_stalk_restrictOpen X.toKLocallyRingedSpace U ⟨x, hxU⟩,
        KLocallyRingedSpace.ringKrullDim_stalk_of_kIso e₀ ⟨x, hxU⟩,
        KLocallyRingedSpace.ringKrullDim_stalk_restrictOpen]
    -- the generators of `𝓘_z` with independent differentials, and the chart
    -- (`exists_kIso_analyticSpaceOfOpen_of_span_germ_eq`)
    obtain ⟨c, h, hgen, hind, hcount⟩ :=
      exists_span_eq_of_isRegularLocalRing_stalk G f (e₀.hom.1.base ⟨x, hxU⟩).1 h3
    obtain ⟨V₁, hzV₁, G', ⟨e₁⟩⟩ :=
      exists_kIso_analyticSpaceOfOpen_of_span_germ_eq G f (e₀.hom.1.base ⟨x, hxU⟩).1 h hgen hind
    -- gluing: the common open `T = W ⊓ V₁` of the model
    let Y := localModel K n G f
    let T : Opens Y := W ⊓ V₁
    have hzT : (e₀.hom.1.base ⟨x, hxU⟩).1 ∈ T :=
      Opens.mem_inf.mpr ⟨(e₀.hom.1.base ⟨x, hxU⟩).2, hzV₁⟩
    let T₂ : Opens (Y.restrictOpen W) := (Opens.map (ofRestrict Y W).1.base).obj T
    let T₁ : Opens (X.toKLocallyRingedSpace.restrictOpen U) := (Opens.map e₀.hom.1.base).obj T₂
    let T₃ : Opens (Y.restrictOpen V₁) := (Opens.map (ofRestrict Y V₁).1.base).obj T
    let T₄ : Opens (analyticSpaceOfOpen K (n - c) G') := (Opens.map e₁.inv.1.base).obj T₃
    have hxT₁ : (⟨x, hxU⟩ : U) ∈ T₁ := hzT
    have hT₂ : imageOpens W T₂ = T := imageOpens_map_eq Y inf_le_left
    have hT₃ : imageOpens V₁ T₃ = T := imageOpens_map_eq Y inf_le_right
    refine ⟨n - c, ?_, imageOpens U T₁, mem_imageOpens.mpr ⟨hxU, hxT₁⟩,
      imageOpens (X := affine K (n - c)) G' T₄, ⟨?_⟩⟩
    · rw [hd1]
      exact WithBot.eq_natCast_sub_of_add_natCast_eq (by rwa [add_comm] at hcount)
    · exact (restrictOpen_restrictOpen_iso U T₁).symm ≪≫ restrictOpenIso e₀ T₂ ≪≫
        restrictOpen_restrictOpen_iso W T₂ ≪≫ eqToIso (congrArg Y.restrictOpen hT₂) ≪≫
        (eqToIso (congrArg Y.restrictOpen hT₃)).symm ≪≫
        (restrictOpen_restrictOpen_iso V₁ T₃).symm ≪≫
        (restrictOpenIso e₁.symm T₃).symm ≪≫
        restrictOpen_restrictOpen_iso (X := affine K (n - c)) G' T₄
  · rintro ⟨d, -, V, hxV, G', ⟨e⟩⟩
    exact (isRegularLocalRing_stalk_of_kIso_analyticSpaceOfOpen hxV e).1

/-- The simple points form an open set ("the open subspace of `X` which consists of the simple
points" [Hir64, Introduction]). -/
theorem isOpen_reg (X : AnalyticSpace.{u} K) : IsOpen (regularLocus X) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨d, -, V, hxV, G', ⟨e⟩⟩ := (isRegular_stalk_iff_exists_manifold_nhd X x).mp hx
  exact ⟨V, fun y hy => (isRegularLocalRing_stalk_of_kIso_analyticSpaceOfOpen hy e).1, V.isOpen,
    hxV⟩

/-- The multiple points form a closed set. -/
theorem isClosed_singularLocus (X : AnalyticSpace.{u} K) : IsClosed (singularLocus X) :=
  isClosed_compl_iff.mpr (isOpen_reg X)

end AnalyticSpace

