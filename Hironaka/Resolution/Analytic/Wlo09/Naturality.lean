/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.Canonicity
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Wlo09.Transport
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The resolution family commutes with local analytic isomorphisms

The value of the resolution family `resolveFam bo` (the rounds of the order-reduction functors
`bo d` at decreasing maximal order, `Hironaka/Resolution/Analytic/Wlo09/Rounds.lean`) on a
pulled-back triple is the pull-back of the value, with the empty blow-ups erased: for a local
analytic isomorphism `g : N → M`, a triple `T'` on `N` carrying the pull-back data of a triple `T`
on `M` and a relatively compact open `U' ⊆ N`, the value of `T'` on `U'` is the pull-back of the
value of `T` on the image `g(U')` along `g|_{U'} : U' → g(U')`, its empty blow-ups erased
(`resolveSeqOn_pullback`). This is the behaviour of a blow-up sequence functor under smooth
morphisms [Kol07, 34.1], and Włodarczyk's commutation of the canonical principalization with local
analytic isomorphisms [Wlo09, Theorem 3.5.1 (2)] for the locally finite principalization
[Wlo09, Theorem 2.0.3]; the compatibility of the family under restriction (`resolveSeqOn_compat`,
`Hironaka/Resolution/Analytic/Wlo09/Canonicity.lean`) is the case of an open inclusion.

The proof reads the canonical chain `c` of `g(U')` on `M` (`canonicalResolveChain`) and builds an
admissible chain `c'` for `U'` on `N` of the same length: the iterated shrinks of `closure U'`
inside `g⁻¹(c.W 0)` (`shrinkChain`), on whose outermost open the order of the pulled-back ideal is
at most the length, the order being invariant under local analytic isomorphisms
(`IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt`). The value of `T'` on `U'` is its value along
`c'` (canonicity, `resolveSeqOnAlong_chain_indep`), and the transport theorem of the rounds
(`eraseEmpty_resolveFrom_congr`, `Hironaka/Resolution/Analytic/Wlo09/Transport.lean`) along the
restriction of `g` to the outermost opens, with the reading maps the inclusions of `U'` and `g(U')`,
identifies the two erased lists.
-/

public section

noncomputable section

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)

/-- **The value of the resolution family commutes with local analytic isomorphisms**
([Kol07, 34.1]; [Wlo09, Theorem 3.5.1 (2)]): for a local analytic isomorphism `g : N → M` and a
triple `T'` on `N` carrying the pull-back data of `T`, the value of `T'` on a relatively compact
open `U'` is the pull-back of the value of `T` on `g(U')` along `g|_{U'}`, with the empty blow-ups
erased. The canonical chain of `g(U')` and the shrinks of `closure U'` inside the preimage of its
innermost open are two chains of the same length related by `g`, and the transport theorem of the
rounds identifies their values (`eraseEmpty_resolveFrom_congr`). -/
theorem resolveSeqOn_pullback {M N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) N)
    (g : AnalyticMap N M) (hg : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g)
    (hpb : T'.IsPullbackOf T g) (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))) :
    resolveSeqOn bo T' U' hU' =
      ((resolveSeqOn bo T (AnalyticMap.imageOpens g hg U')
          (AnalyticMap.isCompact_closure_image g hU')).pullback
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' _ Set.Subset.rfl)).eraseEmpty := by
  set V := AnalyticMap.imageOpens g hg U' with hVdef
  have hV : IsCompact (closure (V : Set M)) := AnalyticMap.isCompact_closure_image g hU'
  set c : ResolveChain T V := canonicalResolveChain T V hV with hc
  -- the closure of `U'` lies over the innermost open of the canonical chain of `V`
  have hK : closure (U' : Set N) ⊆ ⇑g ⁻¹' (c.W 0 : Set M) := by
    intro y hy
    have hgy : g y ∈ closure (V : Set M) :=
      image_closure_subset_closure_image g.contMDiff.continuous ⟨y, hy, rfl⟩
    exact subset_shrinkChain hV _ _ hgy
  set O : Opens N := ⟨⇑g ⁻¹' (c.W 0 : Set M), (c.W 0).isOpen.preimage g.contMDiff.continuous⟩
    with hOdef
  have hW0 : ∀ k, k ≤ c.D → c.W 0 ≤ c.W k := fun k hk => c.le_of_le (Nat.zero_le k) hk
  -- the chain on `N`: the shrinks of `closure U'` inside `g⁻¹(W 0)`, as many as the rounds of `c`
  set c' : ResolveChain T' U' :=
    { D := c.D
      W := fun k => shrinkChain (closure (U' : Set N)) O hU' hK (c.D - k)
      isCompact_closure := fun k _ => isCompact_closure_shrinkChain hU' hK _
      closure_subset := fun k hk => by
        have h : c.D - k = (c.D - (k + 1)) + 1 := by omega
        rw [h]
        exact closure_shrinkChain_succ_subset hU' hK _
      le_zero := fun _ hx => subset_shrinkChain hU' hK _ (subset_closure hx)
      ord_le := fun y hy => by
        have hyO : y ∈ O := by
          have h0 : (c.D - c.D) = 0 := Nat.sub_self _
          have hy' : y ∈ shrinkChain (closure (U' : Set N)) O hU' hK (c.D - c.D) := hy
          rw [h0] at hy'
          exact closure_shrinkChain_zero_subset hU' hK (subset_closure hy')
        rw [hpb.1, IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ T.I (hg y)]
        exact c.ord_le _ (hW0 c.D le_rfl hyO) } with hc'
  -- every open of the chain on `N` lies in `g⁻¹(W 0)`
  have hc'O : ∀ k, (c'.W k : Set N) ⊆ O := fun k =>
    (shrinkChain_antitone hU' hK (Nat.zero_le _)).trans
      (fun _ hx => closure_shrinkChain_zero_subset hU' hK (subset_closure hx))
  have hgW : ⇑g '' (c'.W c'.D : Set N) ⊆ c.W c.D := by
    rintro _ ⟨y, hy, rfl⟩
    exact hW0 c.D le_rfl (hc'O _ hy)
  set g₀ := AnalyticMap.restrictMap g (c'.W c'.D) (c.W c.D) hgW with hg₀def
  have hg₀ : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g₀ :=
    AnalyticMap.isLocalDiffeomorph_restrictMap hg _ _ hgW
  -- the triples on the outermost opens correspond along `g₀`
  have hpb₀ : c'.outerTriple.IsPullbackOf c.outerTriple g₀ := by
    have e : g.comp (N.inclusion (c'.W c'.D)) = (M.inclusion (c.W c.D)).comp g₀ :=
      ContMDiffMap.ext fun _ => rfl
    have h1 := hpb.comp (T'.isPullbackOf_pullback (N.inclusion (c'.W c'.D))
      (isLocalDiffeomorph_inclusion N _))
    have h2 := (T.isPullbackOf_pullback (M.inclusion (c.W c.D))
      (isLocalDiffeomorph_inclusion M _)).comp (c.outerTriple.isPullbackOf_pullback g₀ hg₀)
    rw [e] at h1
    have h3 := h1.eq h2
    change (T'.pullback (N.inclusion (c'.W c'.D)) _).IsPullbackOf c.outerTriple g₀
    rw [h3]
    exact c.outerTriple.isPullbackOf_pullback g₀ hg₀
  -- the two chains correspond along `g₀`
  have hΩg : ∀ k, k < c.D → ⇑g₀ '' (c'.trace k : Set _) ⊆ c.trace k := by
    rintro k hk _ ⟨p, hp, rfl⟩
    exact hW0 k hk.le (hc'O k hp)
  -- the reading maps on `U'` and `V` correspond along `g|_{U'}`
  have hcomm : (M.restrictLE c.le_outerOpen).comp
      (AnalyticMap.restrictMap g U' V Set.Subset.rfl) =
      g₀.comp (N.restrictLE c'.le_outerOpen) := ContMDiffMap.ext fun _ => rfl
  have key := eraseEmpty_resolveFrom_congr bo c.D g₀ hg₀ c.outerTriple c'.outerTriple hpb₀
    c.outerTriple_ord_le c.outerTriple_finite c'.outerTriple_ord_le c'.outerTriple_finite
    c.trace c.isCompact_closure_trace c.closure_trace_subset
    c'.trace c'.isCompact_closure_trace c'.closure_trace_subset hΩg
    (M.restrictLE c.le_outerOpen) (isLocalDiffeomorph_restrictLE _)
    c.range_restrictLE_subset_trace
    (N.restrictLE c'.le_outerOpen) (isLocalDiffeomorph_restrictLE _)
    c'.range_restrictLE_subset_trace
    (AnalyticMap.restrictMap g U' V Set.Subset.rfl)
    (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' V Set.Subset.rfl) hcomm
  refine (resolveSeqOnAlong_chain_indep bo T' U' _ c').trans ?_
  refine key.trans ?_
  exact (BlowUpSequence.eraseEmpty_pullback_eraseEmpty _ _ _).symm

end Hironaka.Manifold

end

end
