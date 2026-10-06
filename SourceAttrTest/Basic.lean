/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

import all SourceAttrTest.Decls
public meta import Lean.DocString
public meta import Lean.Elab.Command
import Lean.Exception

/-!
# Tests of the `source` attribute

Checks, from an importing module, the declarations tagged in
`SourceAttrTest.Decls`: the listing `#source_refs` (all tags, and the tags of one
key), the docstrings with their `Source:` paragraphs (after the docstring, in the order of the
attributes, linked to the address of the reference when it has one), the JSON export read by
`scripts/export_source_refs.lean`, and the registry entry of `Wlo05`, with the address of its `doi`.
-/

public meta section

set_option linter.hashCommand false

open Lean SourceAttr

/--
info: SourceAttrTest.CitedStructure: [Har77, II, Definition 7.1] (the object only)
SourceAttrTest.bracketed: [Hir64, Theorem [1]]
SourceAttrTest.citedDef: [AM69, Proposition 1.2, p. 2]
SourceAttrTest.citesTwo: [Hir64, Main Theorem I, p. 132]
SourceAttrTest.citesTwo: [Kol07, Theorem 68] (arXiv numbering)
SourceAttrTest.citesTwoSync: [Hir64, Main Theorem II, pp. 142–143]
SourceAttrTest.citesTwoSync: [BM97, Theorem 1.10]
SourceAttrTest.duplicate: [Hir64, Main Theorem I]
SourceAttrTest.taggedLater: [Sta, Tag 00TT]
SourceAttrTest.undocumented: [Wlo05, Theorem 1.0.2]
-/
#guard_msgs in
#source_refs

/--
info: SourceAttrTest.bracketed: [Hir64, Theorem [1]]
SourceAttrTest.citesTwo: [Hir64, Main Theorem I, p. 132]
SourceAttrTest.citesTwoSync: [Hir64, Main Theorem II, pp. 142–143]
SourceAttrTest.duplicate: [Hir64, Main Theorem I]
-/
#guard_msgs in
#source_refs Hir64

/-- info: No sources found. -/
#guard_msgs in
#source_refs BM88

/-- error: unknown reference key `Foo99` -/
#guard_msgs in
#source_refs Foo99

/-- Logs the docstring of the declaration `decl`. -/
def logDoc (decl : Name) : Elab.Command.CommandElabM Unit := do
  logInfo ((← findDocString? (← getEnv) decl).getD "(no docstring)")

/--
info: A theorem citing two sources.

Source: [Hir64, Main Theorem I, p. 132](https://doi.org/10.2307/1970486)

Source: [Kol07, Theorem 68](https://arxiv.org/abs/math/0508332v3) (arXiv numbering)
-/
#guard_msgs in
run_cmd logDoc ``SourceAttrTest.citesTwo

/--
info: A theorem citing two sources, elaborated synchronously.

Source: [Hir64, Main Theorem II, pp. 142–143](https://doi.org/10.2307/1970486)

Source: [BM97, Theorem 1.10](https://arxiv.org/abs/alg-geom/9508005)
-/
#guard_msgs in
run_cmd logDoc ``SourceAttrTest.citesTwoSync

/-- info: Source: [Wlo05, Theorem 1.0.2](https://doi.org/10.1090/S0894-0347-05-00493-5) -/
#guard_msgs in
run_cmd logDoc ``SourceAttrTest.undocumented

/--
info: A definition citing a source without an address.

Source: [AM69, Proposition 1.2, p. 2]
-/
#guard_msgs in
run_cmd logDoc ``SourceAttrTest.citedDef

/--
info: A structure.

Source: [Har77, II, Definition 7.1](https://doi.org/10.1007/978-1-4757-3849-0) (the object only)
-/
#guard_msgs in
run_cmd logDoc ``SourceAttrTest.CitedStructure

/--
info: A theorem tagged by the `attribute` command.

Source: [Sta, Tag 00TT](https://stacks.math.columbia.edu)
-/
#guard_msgs in
run_cmd logDoc ``SourceAttrTest.taggedLater

/--
info: A locator with brackets.

Source: [Hir64, Theorem \[1\]](https://doi.org/10.2307/1970486)
-/
#guard_msgs in
run_cmd logDoc ``SourceAttrTest.bracketed

/--
info: The first attribute applies, the second is an error.

Source: [Hir64, Main Theorem I](https://doi.org/10.2307/1970486)
-/
#guard_msgs in
run_cmd logDoc ``SourceAttrTest.duplicate

/--
info: decl: "SourceAttrTest.citesTwo"
module: "SourceAttrTest.Decls"
file: "SourceAttrTest/Decls.lean"
key: "Kol07"
locator: "Theorem 68"
page: null
comment: "arXiv numbering"
url: "https://arxiv.org/abs/math/0508332v3"
cite: "Kol07, Theorem 68"
---
info: decl: "SourceAttrTest.citedDef"
module: "SourceAttrTest.Decls"
file: "SourceAttrTest/Decls.lean"
key: "AM69"
locator: "Proposition 1.2"
page: "p. 2"
comment: null
url: null
cite: "AM69, Proposition 1.2, p. 2"
-/
#guard_msgs in
run_cmd do
  let lines := exportSourceTags (← getEnv)
  for i in [4, 2] do
    let json := (Json.parse lines[i]!).toOption.get!
    logInfo <| "\n".intercalate <| ["decl", "module", "file", "key", "locator", "page", "comment",
      "url", "cite"].map fun field => s!"{field}: {(json.getObjValD field).compress}"

/-- info: Wlo05 https://doi.org/10.1090/S0894-0347-05-00493-5 -/
#guard_msgs in
run_cmd do
  let some r := findReference? (← getEnv) "Wlo05" | throwError "`Wlo05` is not registered"
  logInfo s!"{r.key} {r.url?.getD "(no address)"}"
