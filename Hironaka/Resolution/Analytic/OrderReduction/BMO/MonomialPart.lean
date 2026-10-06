/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BMO.LocallyFiniteProduct
public import Hironaka.Manifold.BlowUp.Transform.Defs
public import Hironaka.Manifold.IdealSheaf.Basic
public import Hironaka.Manifold.Snc.Defs
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.Snc.Basic
import Hironaka.Manifold.Submanifold.Components
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The monomial part of an ideal sheaf with respect to a boundary family

For a triple `(X, I, E)`, Kollár writes `I = M(I) · N(I)` with `M(I) = 𝒪_X(−∑ cᵢ Eⁱ)` the *monomial
part*, a product of powers of the ideal sheaves of the members `Eⁱ` of the boundary, and `N(I)` the
*nonmonomial part*, whose cosupport contains no member [Kol07, Definition–Lemma 110]. This file
defines the monomial part on an analytic manifold, for an ideal sheaf `I` and a boundary family `F`
with simple normal crossings, in a finer form: the product runs over the **connected components**
`D` of the members `E^j`, each contributing `𝓘_D^{ord_D I}`, where `𝓘_D` is the reduced ideal sheaf
of `D` and `ord_D I` is the order of `I` along `D` (constant along the connected component; it is
read at one point). Kollár's members are not assumed irreducible, and on a manifold a member need
not be connected; reading the exponent on each component separately is what makes the monomial
part commute with restriction to open subsets and with local analytic isomorphisms, as the functor
of [Kol07, Theorem 107 (2)] requires.

The components are indexed by `ComponentIndex F = Σ j, ConnectedComponents (E^j)`. A member may have
infinitely many components, but the family of all component sets is locally finite
(`componentSet_locallyFinite`), so `M(I)` is the locally finite product of the component factors
(`IdealSheaf.locallyFiniteProduct`, `BMO/LocallyFiniteProduct.lean`) rather than a finite product.
The analytic counterpart of `Hironaka.BMO.monomialPart`.
-/

@[expose] public section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M]

/-- The index type of the factors of the monomial part: a member `j` of the boundary family
together with one of the connected components of `E^j`. These are the components `D` of
[Kol07, Definition–Lemma 110], taken one connected component at a time. -/
abbrev ComponentIndex (F : HypersurfaceFamily M) : Type u :=
  Σ j : F.ι, ConnectedComponents (F.hyp j)

variable (F : HypersurfaceFamily M)

/-- The underlying set of the component `i = ⟨j, C⟩`: the image in `M` of the connected component
`C` of the member `E^j` (the preimage of `{C}` under `ConnectedComponents.mk`). -/
def componentSet (i : ComponentIndex F) : Set M :=
  Subtype.val '' (ConnectedComponents.mk ⁻¹' {i.2} : Set (F.hyp i.1))

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- Each component `i = ⟨j, C⟩` of a boundary family with simple normal crossings is a closed
submanifold of `M` of codimension one: the member is one, and a connected component of a closed
submanifold is again a closed submanifold. -/
theorem componentSubmanifold (hF : F.IsSnc ψ) (i : ComponentIndex F) :
    IsClosedSubmanifold ψ (componentSet F i) 1 := by
  have h := (hF.isClosedSubmanifold i.1).connectedComponent' i.2.out
  have hmk : (ConnectedComponents.mk i.2.out : ConnectedComponents (F.hyp i.1)) = i.2 :=
    Quotient.out_eq' i.2
  have hset : (ConnectedComponents.mk ⁻¹' {i.2} : Set (F.hyp i.1)) =
      connectedComponent i.2.out := by
    conv_lhs => rw [← hmk]
    rw [connectedComponents_preimage_singleton]
  rwa [componentSet, hset]

/-- The reduced ideal sheaf `𝓘_D` of the component `D = i`. -/
noncomputable def componentIdeal (hF : F.IsSnc ψ) (i : ComponentIndex F) :
    IdealSheaf (structureSheaf 𝕜 E M) :=
  (componentSubmanifold F hF i).idealSheaf

/-- The exponent `ord_D I` of the component `D = i`: the order of `I` along `D`, which is constant
along the connected component and is read at the representative `i.2.out`, as a natural number.
For an ideal sheaf that is nonzero at every point (every ideal of a triple is,
[Kol07, Definition 31]) the order along `D` is finite, so passing to `ℕ` loses nothing; for a zero
stalk the value `⊤` would be read as `0`. -/
noncomputable def componentExponent (hF : F.IsSnc ψ) (I : IdealSheaf (structureSheaf 𝕜 E M))
    (i : ComponentIndex F) : ℕ :=
  (IdealSheaf.genericOrdAlong (componentIdeal F hF i) I i.2.out.val).toNat

/-- The factor `𝓘_D ^ (ord_D I)` of the monomial part at the component `D = i`. -/
noncomputable def componentFactor (hF : F.IsSnc ψ) (I : IdealSheaf (structureSheaf 𝕜 E M))
    (i : ComponentIndex F) : IdealSheaf (structureSheaf 𝕜 E M) :=
  componentIdeal F hF i ^ componentExponent F hF I i

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The component sets form a locally finite family of subsets of `M`: the members `E^j` are locally
finite, the connected components of each member are locally finite in `M`, and each component lies
in its member (`locallyFinite_sigma`). This is the finiteness that makes the monomial part an ideal
sheaf on a non-compact manifold, where a member may have infinitely many components. -/
theorem componentSet_locallyFinite (hF : F.IsSnc ψ) : LocallyFinite (componentSet F) :=
  locallyFinite_sigma hF.locallyFinite
    (fun j => (hF.isClosedSubmanifold j).locallyFinite_connectedComponents')
    (fun _ _ => Subtype.coe_image_subset _ _)

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- Off its component, the factor `𝓘_D ^ (ord_D I)` is the unit ideal, since the ideal sheaf of a
closed submanifold is the unit ideal off the submanifold. This is the controlling-set hypothesis of
the locally finite product. -/
theorem componentFactor_stalkIdeal_top_of_notMem (hF : F.IsSnc ψ)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) (i : ComponentIndex F) (x : M)
    (hx : x ∉ componentSet F i) : (componentFactor F hF I i).stalkIdeal x = ⊤ := by
  change ((componentSubmanifold F hF i).idealSheaf ^ componentExponent F hF I i).stalkIdeal x = ⊤
  rw [IdealSheaf.stalkIdeal_pow, (componentSubmanifold F hF i).stalkIdeal_idealSheaf_of_notMem hx,
    ← Ideal.one_eq_top, one_pow]

/-- The **monomial part** `M(I) = ∏_D 𝓘_D ^ (ord_D I)` of `I` with respect to the boundary family
`F` with simple normal crossings: the locally finite product of the component factors over all
components `D` of the members of `F` ([Kol07, Definition–Lemma 110], with the exponents read on the
connected components of the members; see the module docstring). The same decomposition
`I = M(I) · N(I)` appears in [BM08, (5.2)] and in [Wlo05, Proposition 3.0.8, Step 2 of the proof].
The analytic counterpart of `Hironaka.BMO.monomialPart`. -/
noncomputable def monomialPart (hF : F.IsSnc ψ) (I : IdealSheaf (structureSheaf 𝕜 E M)) :
    IdealSheaf (structureSheaf 𝕜 E M) :=
  IdealSheaf.locallyFiniteProduct (structureSheaf 𝕜 E M) (componentFactor F hF I) (componentSet F)
    (componentSet_locallyFinite F hF) (componentFactor_stalkIdeal_top_of_notMem F hF I)

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The stalk of the monomial part at `x` is the finite product of the factors of the components
passing through `x`. -/
@[simp] theorem stalkIdeal_monomialPart (hF : F.IsSnc ψ) (I : IdealSheaf (structureSheaf 𝕜 E M))
    (x : M) :
    (monomialPart F hF I).stalkIdeal x =
      ∏ i ∈ IdealSheaf.activeFinset (componentSet F) (componentSet_locallyFinite F hF) x,
        (componentFactor F hF I i).stalkIdeal x :=
  IdealSheaf.stalkIdeal_locallyFiniteProduct _ _ _ _ x

end Hironaka.Manifold.BMO
