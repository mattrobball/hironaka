/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.DirectLimit.Manifold
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Maps out of the direct limit of a chain of analytic open embeddings

The universal property of the direct limit `limitManifold` of `DirectLimit/Manifold.lean`: a
family of analytic maps `f n : X n → Y` compatible with the transition maps
(`f (n+1) ∘ ι n = f n`) induces an analytic map `limitDesc f hf : limitManifold → Y` with
`limitDesc ∘ toLimit n = f n`, Włodarczyk's glued map `prin : M̃ → M` [Wlo09, §4.1] for the
blow-downs of the end results. When moreover the transition maps are the preimages of an
increasing sequence of sets `V n` of `Y` (`range (ι n) = f (n+1) ⁻¹' V n`), the preimage of `V n`
under the induced map is exactly the `n`-th piece (`preimage_limitDesc_eq_range_toLimit`:
`σ⁻¹(M_n) = M'_n`), so the inclusion of the `n`-th piece is an analytic isomorphism onto
`limitDesc⁻¹(V n)` (`isAnalyticIsoOver_toLimitMap_limitDesc`; the identification `U_r = Ũ` of
[Wlo09, Theorem 2.0.3 (1)], the field `toSpace_isIso` of `ExtensionCompatibleFamily`).

The induced map is defined on the quotient (`Quotient.lift`), well defined because the family is
compatible with the composites (`apply_iter`); it is analytic since on the image of the `n`-th
piece it is `f n ∘ (pieceOpenEmb n).symm` (`contMDiff_limitDescFun`). For the preimage, a point
`toLimit m y` with `f m y ∈ V n` and `m > n` descends step by step: `f m y ∈ V (m-1)` by
monotonicity, so `y = ι (m-1) y'` with `f (m-1) y' = f m y`, and `toLimit m y = toLimit (m-1) y'`
(`toLimit_mem_range_of_apply_mem`); conversely `f n x ∈ V n` since `ι n x ∈ range (ι n)`
(`apply_mem_of_range_eq`; no separate hypothesis `range (f n) ⊆ V n` is needed).

* `apply_iter`, `limitDescFun`, `limitDescFun_toLimit`, `contMDiff_limitDescFun`, `limitDesc`,
  `limitDesc_toLimit`, `limitDesc_comp_toLimitMap`.
* `apply_mem_of_range_eq`, `toLimit_mem_range_of_apply_mem`,
  `preimage_limitDesc_eq_range_toLimit`, `preimage_limitDesc_eq_range_toLimitMap`,
  `isAnalyticIsoOver_toLimitMap_limitDesc`.
-/

@[expose] public noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace OpenEmbeddingChain

variable (c : OpenEmbeddingChain.{u} 𝕜 E)

/-! ### Maps out of the limit -/

/-- A family compatible with the transition maps is compatible with the composite
embeddings. -/
theorem apply_iter {Y : AnalyticManifold.{u} 𝕜 E} (f : ∀ n, AnalyticMap (c.X n) Y)
    (hf : ∀ n (x : c.X n), f (n + 1) (c.ι n x) = f n x) {n m : ℕ} (h : n ≤ m) (x : c.X n) :
    f m (c.iter h x) = f n x := by
  induction m, h using Nat.le_induction with
  | base => rw [iter_self_apply]
  | succ m hnm ih => rw [iter_succ_apply c hnm, hf, ih]

/-- The underlying function of the map out of the limit induced by a compatible family: `f n` on the
`n`-th piece (`Quotient.lift`); Włodarczyk's glued map, [Wlo09, §4.1]. -/
def limitDescFun {Y : AnalyticManifold.{u} 𝕜 E} (f : ∀ n, AnalyticMap (c.X n) Y)
    (hf : ∀ n (x : c.X n), f (n + 1) (c.ι n x) = f n x) : c.Limit → Y :=
  Quotient.lift (fun a : Σ n, (c.X n : Type u) => f a.1 a.2) fun a b hab => by
    obtain ⟨k, h₁, h₂, e⟩ := hab
    rw [← c.apply_iter f hf h₁, e, c.apply_iter f hf h₂]

/-- The induced function restricts to `f n` on the `n`-th piece. -/
theorem limitDescFun_toLimit {Y : AnalyticManifold.{u} 𝕜 E} (f : ∀ n, AnalyticMap (c.X n) Y)
    (hf : ∀ n (x : c.X n), f (n + 1) (c.ι n x) = f n x) (n : ℕ) (x : c.X n) :
    c.limitDescFun f hf (c.toLimit n x) = f n x := rfl

/-- The induced function is analytic — on the image of the `n`-th piece it is
`f n ∘ (pieceOpenEmb n).symm`. -/
theorem contMDiff_limitDescFun {Y : AnalyticManifold.{u} 𝕜 E} (f : ∀ n, AnalyticMap (c.X n) Y)
    (hf : ∀ n (x : c.X n), f (n + 1) (c.ι n x) = f n x) :
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω (c.limitDescFun f hf) := by
  intro p
  obtain ⟨n, x, rfl⟩ := c.toLimit_surjective p
  have : Nonempty (c.X n) := ⟨x⟩
  have h1 : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω (f n ∘ (c.pieceOpenEmb n).symm)
      (Set.range (c.toLimit n)) :=
    (f n).contMDiff.comp_contMDiffOn (c.contMDiffOn_pieceOpenEmb_symm n)
  refine (h1.congr fun q hq => ?_).contMDiffAt ((c.isOpen_range_toLimit n).mem_nhds ⟨x, rfl⟩)
  rw [Function.comp_apply, ← c.limitDescFun_toLimit f hf n, c.toLimit_pieceOpenEmb_symm n hq]

/-- The analytic map out of the limit induced by a family of analytic maps compatible with the
transition maps (Włodarczyk's glued map `prin : M̃ → M`, [Wlo09, §4.1]). -/
def limitDesc {Y : AnalyticManifold.{u} 𝕜 E} (f : ∀ n, AnalyticMap (c.X n) Y)
    (hf : ∀ n (x : c.X n), f (n + 1) (c.ι n x) = f n x) : AnalyticMap c.limitManifold Y :=
  ⟨c.limitDescFun f hf, c.contMDiff_limitDescFun f hf⟩

/-- The induced map restricts to `f n` on the `n`-th piece. -/
theorem limitDesc_toLimit {Y : AnalyticManifold.{u} 𝕜 E} (f : ∀ n, AnalyticMap (c.X n) Y)
    (hf : ∀ n (x : c.X n), f (n + 1) (c.ι n x) = f n x) (n : ℕ) (x : c.X n) :
    c.limitDesc f hf (c.toLimit n x) = f n x := rfl

/-- `limitDesc f hf ∘ toLimitMap n = f n` as analytic maps (the field `map_toSpace` of
`ExtensionCompatibleFamily`). -/
theorem limitDesc_comp_toLimitMap {Y : AnalyticManifold.{u} 𝕜 E} (f : ∀ n, AnalyticMap (c.X n) Y)
    (hf : ∀ n (x : c.X n), f (n + 1) (c.ι n x) = f n x) (n : ℕ) :
    (c.limitDesc f hf).comp (c.toLimitMap n) = f n := ContMDiffMap.ext fun _ => rfl

/-! ### The preimages of an increasing sequence of sets are the pieces -/

/-- When the transition maps are the preimages of the sets `V n`, `f n` maps the `n`-th piece into
`V n` (`ι n x` lies in the range of `ι n`); no separate hypothesis is needed. -/
theorem apply_mem_of_range_eq {Y : AnalyticManifold.{u} 𝕜 E} (f : ∀ n, AnalyticMap (c.X n) Y)
    (hf : ∀ n (x : c.X n), f (n + 1) (c.ι n x) = f n x) (V : ℕ → Set Y)
    (hι : ∀ n, Set.range (c.ι n) = f (n + 1) ⁻¹' V n) (n : ℕ) (x : c.X n) : f n x ∈ V n := by
  have h : c.ι n x ∈ Set.range (c.ι n) := ⟨x, rfl⟩
  rwa [hι n, mem_preimage, hf n x] at h

/-- A point of the `m`-th piece mapped into `V n` lies in the image of the `n`-th
piece — descend from `m` to `n` one transition map at a time (`V` increasing). -/
theorem toLimit_mem_range_of_apply_mem {Y : AnalyticManifold.{u} 𝕜 E}
    (f : ∀ n, AnalyticMap (c.X n) Y) (hf : ∀ n (x : c.X n), f (n + 1) (c.ι n x) = f n x)
    (V : ℕ → Set Y) (hV : ∀ n, V n ⊆ V (n + 1))
    (hι : ∀ n, Set.range (c.ι n) = f (n + 1) ⁻¹' V n) {n m : ℕ} (y : c.X m) (hy : f m y ∈ V n) :
    c.toLimit m y ∈ Set.range (c.toLimit n) := by
  induction m with
  | zero => exact c.range_toLimit_mono (Nat.zero_le n) ⟨y, rfl⟩
  | succ m ih =>
    by_cases h : m + 1 ≤ n
    · exact c.range_toLimit_mono h ⟨y, rfl⟩
    · have hmn : n ≤ m := Nat.le_of_lt_succ (Nat.lt_of_not_le h)
      have hy' : y ∈ Set.range (c.ι m) := by
        rw [hι m, mem_preimage]
        exact (monotone_nat_of_le_succ hV hmn : V n ⊆ V m) hy
      obtain ⟨y', rfl⟩ := hy'
      rw [toLimit_succ]
      exact ih y' (by rwa [← hf m y'])

/-- When the transition maps are the preimages of an increasing sequence of sets `V n`, the preimage
of `V n` under the induced map is the image of the `n`-th piece (`σ⁻¹(M_n) = M'_n` for the glued
blow-down). -/
theorem preimage_limitDesc_eq_range_toLimit {Y : AnalyticManifold.{u} 𝕜 E}
    (f : ∀ n, AnalyticMap (c.X n) Y) (hf : ∀ n (x : c.X n), f (n + 1) (c.ι n x) = f n x)
    (V : ℕ → Set Y) (hV : ∀ n, V n ⊆ V (n + 1))
    (hι : ∀ n, Set.range (c.ι n) = f (n + 1) ⁻¹' V n) (n : ℕ) :
    c.limitDesc f hf ⁻¹' V n = Set.range (c.toLimit n) := by
  ext p
  obtain ⟨m, y, rfl⟩ := c.toLimit_surjective p
  constructor
  · intro hp
    exact c.toLimit_mem_range_of_apply_mem f hf V hV hι y hp
  · rintro ⟨x, hx⟩
    have h1 : c.limitDescFun f hf (c.toLimit n x) ∈ V n := c.apply_mem_of_range_eq f hf V hι n x
    rw [hx] at h1
    exact h1

/-- `preimage_limitDesc_eq_range_toLimit` with the range of the bundled inclusion
(the form stated in the limit manifold's carrier, for rewriting). -/
theorem preimage_limitDesc_eq_range_toLimitMap {Y : AnalyticManifold.{u} 𝕜 E}
    (f : ∀ n, AnalyticMap (c.X n) Y) (hf : ∀ n (x : c.X n), f (n + 1) (c.ι n x) = f n x)
    (V : ℕ → Set Y) (hV : ∀ n, V n ⊆ V (n + 1))
    (hι : ∀ n, Set.range (c.ι n) = f (n + 1) ⁻¹' V n) (n : ℕ) :
    c.limitDesc f hf ⁻¹' V n = Set.range (c.toLimitMap n) :=
  c.preimage_limitDesc_eq_range_toLimit f hf V hV hι n

/-- The inclusion of the `n`-th piece is an analytic isomorphism onto `limitDesc⁻¹(V n)` (the
identification `U_r = Ũ` of [Wlo09, Theorem 2.0.3 (1)]; the field `toSpace_isIso` of
`ExtensionCompatibleFamily`). -/
theorem isAnalyticIsoOver_toLimitMap_limitDesc {Y : AnalyticManifold.{u} 𝕜 E}
    (f : ∀ n, AnalyticMap (c.X n) Y) (hf : ∀ n (x : c.X n), f (n + 1) (c.ι n x) = f n x)
    (V : ℕ → Set Y) (hV : ∀ n, V n ⊆ V (n + 1))
    (hι : ∀ n, Set.range (c.ι n) = f (n + 1) ⁻¹' V n) (n : ℕ) :
    (c.toLimitMap n).IsIsoOver (c.limitDesc f hf ⁻¹' V n) := by
  rw [c.preimage_limitDesc_eq_range_toLimitMap f hf V hV hι n]
  exact c.isAnalyticIsoOver_toLimitMap n

end OpenEmbeddingChain

end Manifold
