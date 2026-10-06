import Verso
import VersoManual
import VersoBlueprint
import Blueprint.ConjunctionChains
import Hironaka.Scheme.Resolution.Defs
import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Defs

open Verso.Genre
open Verso.Genre.Manual
open Informal
open CategoryTheory AlgebraicGeometry Scheme Scheme.IdealSheafData

set_option verso.blueprint.autoDeps true

#doc (Manual) "Conventions and sources" =>
%%%
tag := "ch-conventions"
file := "conventions"
%%%

This appendix collects the matters that concern every page: a dictionary from the classical
notions to their names in Mathlib and the library, the typing conventions of the statements, the
names of the declarations, and the sources cited. How to read a node, with its boxes on the relation to the source, is explained in
the introduction ({ref "intro-reading"}[How to read a node]).

# Dictionary
%%%
tag := "conv-dictionary"
%%%

The statements use the standard notions of scheme theory \[Sta\] under their names in Mathlib or
in the library. Each line gives a classical notion, its Lean name, and the node of the library's
definition where there is one.

- *Scheme; morphism; composite; identity; isomorphism*: {decl}`Scheme`, `X ⟶ Y`, `f ≫ g` (first `f`,
  then `g`), `𝟙 X`, `IsIso f`.
- *Spectrum of a ring; the point $`\operatorname{Spec} k`*: `Spec R` for `R : CommRingCat`;
  `Spec (.of k)`.
- *Open subsets; affine opens; functions on an open $`U`; stalk at $`x`*: `X.Opens`,
  `X.affineOpens`, `Γ(X, U)`, `X.presheaf.stalk x`.
- *The part of $`f \colon X \to Y` over an open $`U \subseteq Y`*: `f ∣_ U : f ⁻¹ᵁ U ⟶ U`, as in
  the weak form of Main Theorem I ({bpref "thm:mt1_weak"}[]).
- *Algebraic $`k`-scheme (separated and of finite type over $`k`)*: `X : AlgScheme k`, with
  scheme `X.left` and structure morphism `X.left ↘ Spec (.of k)` ({ref "conv-schemes"}[Algebraic k-schemes],
  {bpref "def:alg_scheme"}[], {bpref "def:finite_type"}[]).
- *Closed subscheme, given by its ideal sheaf; its support; inverse image along $`h`*:
  `I : X.IdealSheafData`, `I.support`, `I.comap h` ({ref "conv-ideals"}[below]).
- *Stalk $`I_x` and order $`\nu(I_x)` of an ideal sheaf*: `I.stalkIdeal x`, `I.ord x`
  ({bpref "def:stalk_ideal"}[], {bpref "def:order"}[]).
- *Reduced; irreducible components; integral (a variety, when of finite type over $`k`)*:
  `IsReduced X`, `irreducibleComponents X`, `IsIntegral X`.
- *Simple point (regular local ring); non-singular scheme; singular locus*: `X.IsRegularAt x`,
  `IsRegular X`, `X.singularLocus` ({bpref "def:is_regular"}[]).
- *Regular system of parameters, the local coordinates at a point*:
  {decl}`IsLocalRing.IsRegularSystemOfParameters` ({bpref "def:regular_system"}[]).
- *Smooth morphism, of relative dimension $`d`; smooth locus $`X^{ns}` of $`X` over $`k`*:
  `Smooth f`, `SmoothOfRelativeDimension d f`, `(X.left ↘ Spec (.of k)).smoothLocus`. Over a field
  of characteristic zero a scheme of finite type is smooth over $`k` exactly at its simple points
  ({bpref "def:is_regular"}[]).
- *Cartesian square, $`P = X \times_S Y`; base change along a field extension $`\sigma`*:
  {decl}`IsPullback`; a cartesian square over `Spec σ` ({bpref "def:change_of_fields"}[]).
- *Effective Cartier divisor*: the subscheme of an invertible ideal sheaf, `I.IsInvertible`
  ({bpref "def:invertible"}[]).
- *Blow-up, or monoidal transformation, with centre $`D`; exceptional divisor*: `D.blowUp`,
  `D.blowUpπ`, `D.exceptionalDivisor` ({bpref "def:blowup_construction"}[],
  {bpref "def:exceptional_divisor"}[]).
- *Quasi-coherent sheaf of modules, of finite type; projective bundle $`\mathbf{P}(\mathcal{E})`;
  projective morphism*: `E : X.Modules` with `E.IsQuasicoherent` and `SheafOfModules.IsFiniteType E`,
  `E.projectiveBundle`, `IsProjective f` ({bpref "def:projective_bundle"}[],
  {bpref "def:projective"}[]).
- *Finite succession of blow-ups*: `BlowUpSequence X` ({bpref "def:blowup_sequence"}[]).
- *Normal crossings (Hironaka); simple normal crossings divisor (Kollár)*:
  {decl}`IsSncBoundaryWith`, {decl}`IsSncBoundary` ({bpref "def:normal_crossings"}[]);
  {decl}`DivisorFamily` and {decl}`DivisorFamily.IsSnc` ({bpref "def:divisor_family"}[],
  {bpref "def:snc"}[]).
- *Analytic manifold; coherent sheaf of ideals; blow-up of a manifold; analytic space*:
  `AnalyticManifold 𝕜 E`, {decl}`Manifold.IdealSheaf`, {decl}`Manifold.IsBlowUp`, `AnalyticSpace K`
  ({bpref "def:analytic_manifold"}[], {bpref "def:ideal_sheaf_general"}[],
  {bpref "def:manifold_blowup"}[], {bpref "def:analytic_space"}[]).

# Ideal sheaves and closed subschemes
%%%
tag := "conv-ideals"
%%%

Closed subschemes, centres and boundaries are given by their ideal sheaves: Mathlib's
`X.IdealSheafData` on a scheme ({ref "ch-scheme-vocab"}[Algebraic k-schemes, singularities and
normal crossings]), a locally finitely generated ideal sheaf of the sheaf of analytic functions on a
manifold or an analytic space ({ref "ch-manifolds"}[Analytic manifolds]). Ideal sheaves are ordered
by inclusion, so a larger ideal sheaf is a smaller subscheme: the unit ideal sheaf `⊤` is the empty
subscheme, so a blow-up with centre `⊤` is an isomorphism, and the zero ideal sheaf `⊥` is the whole
space. "With nonzero stalks" reads Hironaka's "sheaf of non-zero ideals" at every stalk. The
*monoidal transformation* with centre $`D` is the blow-up along the ideal sheaf of $`D`; "blow-up"
and "monoidal transformation" are used interchangeably, as are Kollár's "cosupport" and the
library's {decl}`support` of an ideal sheaf.

# Names
%%%
tag := "conv-names"
%%%

Declarations are referred to by their full Lean names. On each page the names in rendered signatures
are shown relative to the namespaces that page opens, as its legend says; links and hovers keep the
full name. The library names its declarations after what they are, in the manner of Mathlib. The
algebraic vocabulary is in `AlgebraicGeometry`, most of it in `AlgebraicGeometry.Scheme` (the
singular locus, blow-up sequences and divisor families) and
`AlgebraicGeometry.Scheme.IdealSheafData` (ideal sheaves, the blow-up and the transforms), with the
order of an ideal of a local ring in `IsLocalRing`, and the inputs and functors of the functorial
theorems, with the properties these theorems assert of them, in `AlgebraicGeometry`. The analytic
vocabulary is in `AnalyticManifold` (manifolds, their ideal sheaves and finite successions), built
on the infrastructure in `Manifold`; analytic spaces, their vocabulary and their resolution theorems
are in `AnalyticSpace`.

# Sources
%%%
tag := "conv-sources"
%%%

The sources cited in this document. The bibliography of the library, the file `references.bib` of
the repository, lists these and the other sources that the library cites, under the same keys.

- *\[Hir64\]* H. Hironaka, Resolution of singularities of an algebraic variety over a field of
  characteristic zero. I, II, Annals of Mathematics (2) 79 (1964), 109–203 and 205–326.
  [doi:10.2307/1970486](https://doi.org/10.2307/1970486). Part II:
  [doi:10.2307/1970547](https://doi.org/10.2307/1970547).
- *\[Kol07\]* J. Kollár, Lectures on Resolution of Singularities, Annals of Mathematics Studies 166,
  Princeton University Press, 2007. [arXiv:math/0508332](https://arxiv.org/abs/math/0508332). The
  arXiv text (v3) is the resolution chapter, circulated as a Seattle lecture; item numbers follow
  it.
- *\[Wlo05\]* J. Włodarczyk, Simple Hironaka resolution in characteristic zero, Journal of the
  American Mathematical Society 18 (2005), 779–822.
  [doi:10.1090/S0894-0347-05-00493-5](https://doi.org/10.1090/S0894-0347-05-00493-5),
  [arXiv:math/0401401](https://arxiv.org/abs/math/0401401).
- *\[Wlo09\]* J. Włodarczyk, Resolution of singularities of analytic spaces, in: Proceedings of the
  15th Gökova Geometry–Topology Conference (2008), International Press, 2009, 31–63.
  [gokovagt.org](https://gokovagt.org/proceedings/2008/ggt08-wlodarczyk.pdf).
- *\[BM88\]* E. Bierstone and P. D. Milman, Semianalytic and subanalytic sets, Publications
  Mathématiques de l'IHÉS 67 (1988), 5–42.
  [doi:10.1007/BF02699126](https://doi.org/10.1007/BF02699126).
- *\[BM97\]* E. Bierstone and P. D. Milman, Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant, Inventiones Mathematicae 128 (1997), 207–302.
  [doi:10.1007/s002220050141](https://doi.org/10.1007/s002220050141),
  [arXiv:alg-geom/9508005](https://arxiv.org/abs/alg-geom/9508005). Item numbers follow the arXiv
  version.
- *\[Hau14\]* H. Hauser, Blowups and resolution, in: The Resolution of Singular Algebraic Varieties,
  Clay Mathematics Proceedings 20, American Mathematical Society, 2014, 1–80.
  [arXiv:1404.1041](https://arxiv.org/abs/1404.1041).
- *\[Sta\]* The Stacks Project Authors, The Stacks Project.
  [stacks.math.columbia.edu](https://stacks.math.columbia.edu). Cited by tag.
- *\[Ati70\]* M. F. Atiyah, Resolution of singularities and division of distributions,
  Communications on Pure and Applied Mathematics 23 (1970), 145–150.
  [doi:10.1002/cpa.3160230202](https://doi.org/10.1002/cpa.3160230202).
- *\[BG69\]* I. N. Bernshtein and S. I. Gel'fand, Meromorphic property of the functions P^λ,
  Functional Analysis and Its Applications 3 (1969), 68–69.
  [doi:10.1007/BF01078276](https://doi.org/10.1007/BF01078276).
- *\[Wat09\]* S. Watanabe, Algebraic Geometry and Statistical Learning Theory, Cambridge Monographs
  on Applied and Computational Mathematics 25, Cambridge University Press, 2009.
  [doi:10.1017/CBO9780511800474](https://doi.org/10.1017/CBO9780511800474).
