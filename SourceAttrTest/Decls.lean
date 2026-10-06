/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

import SourceAttr
import Lean.Message
import HironakaReferences  -- shake: keep (used only by `example`s)
import Mathlib.Tactic.Linter.HashCommandLinter  -- shake: keep (used only by `example`s)

/-!
# Test declarations of the `source` attribute

Dummy declarations tagged with `@[source …]` (`SourceAttr`): a documented theorem
citing two sources, the same elaborated synchronously, an undocumented theorem citing
`Wlo05`, a definition citing a source without an address, a structure with a
comment, a theorem tagged afterwards by the `attribute` command, and a locator with brackets.
Their listing, docstrings and export are checked in `SourceAttrTest.Basic`, which
imports this module: the docstring of a theorem elaborated asynchronously (the default) receives
the `Source:` paragraphs in the final environment, which importers see, while `findDocString?` in
this module reads the docstring as the elaboration of the proof stored it.

This module checks the errors: an unknown key, an empty locator, a duplicate source, a local
attribute, a declaration of another module and a malformed key. It also checks `parseBib`, the
reader of BibTeX files, on well-formed and malformed entries (and the address `BibEntry.url?` that
a citation links to), and the errors of `register_bibliography`.
-/

@[expose] public section

set_option linter.hashCommand false

namespace SourceAttrTest

/-- A theorem citing two sources. -/
@[source Hir64 "Main Theorem I" "p. 132", source Kol07 "Theorem 68" (comment := "arXiv numbering")]
theorem citesTwo : True := trivial

set_option Elab.async false in
/-- A theorem citing two sources, elaborated synchronously. -/
@[source Hir64 "Main Theorem II" "pp. 142–143", source BM97 "Theorem 1.10"]
theorem citesTwoSync : True := trivial

@[source Wlo05 "Theorem 1.0.2"]
theorem undocumented : True := trivial

/-- A definition citing a source without an address. -/
@[source AM69 "Proposition 1.2" "p. 2"]
def citedDef : Nat := 0

/-- A structure. -/
@[source Har77 "II, Definition 7.1" (comment := "the object only")]
structure CitedStructure where
  /-- The field. -/
  n : Nat

/-- A theorem tagged by the `attribute` command. -/
theorem taggedLater : True := trivial

attribute [source Sta "Tag 00TT"] taggedLater

/-- A locator with brackets. -/
@[source Hir64 "Theorem [1]"]
theorem bracketed : True := trivial

/-! ### Errors -/

/-- error: unknown reference key `Foo99`: it is not in the registered bibliography -/
#guard_msgs in
@[source Foo99 "Theorem 1"]
theorem unknownKey : True := trivial

/-- error: empty string in a `source` attribute -/
#guard_msgs in
@[source Hir64 ""]
theorem emptyLocator : True := trivial

/-- The first attribute applies, the second is an error. -/
theorem duplicate : True := trivial

/--
error: duplicate source: the docstring of `duplicate` already reads
  Source: [Hir64, Main Theorem I](https://doi.org/10.2307/1970486)
-/
#guard_msgs in
attribute [source Hir64 "Main Theorem I", source Hir64 "Main Theorem I"] duplicate

/-- error: the `source` attribute must be global -/
#guard_msgs in
@[local source Hir64 "Main Theorem I"]
theorem localSource : True := trivial

/-- error: invalid doc string, declaration `Nat.add_comm` is in an imported module -/
#guard_msgs in
attribute [source Hir64 "Main Theorem I"] Nat.add_comm

open Lean in
/--
info: error: <input>:1:11: a reference key starts with a letter
---
info: error: <input>:1:12: unexpected end of input; expected string literal
---
info: parsed: source Wło05 "Theorem 1" "p. 1" (comment := "c")
-/
#guard_msgs in
run_cmd do
  for s in ["source 9Hir \"A\"", "source Hir64",
      "source Wło05 \"Theorem 1\" \"p. 1\" (comment := \"c\")"] do
    match Parser.runParserCategory (← getEnv) `attr s with
    | .ok stx => logInfo m!"parsed: {stx}"
    | .error e => logInfo m!"error: {e}"

open Lean SourceAttr in
/--
info: Wło05 article https://doi.org/10.1/x; Hir64 book https://example.org
---
info: Sta misc (no address)
---
info: error: line 1: expected a value in braces or a number
---
info: error: line 2: expected `,` or `}` after a field
---
info: error: line 1: the key `9x` starts with a digit
---
info: error: line 3: expected an entry type after `@`
---
info: error: line 1: the field `title` occurs twice
---
info: error: line 1: unexpected end of file
-/
#guard_msgs in
run_cmd do
  for s in [
      -- a doi gives the address; a url field takes precedence over it; comments are skipped
      "% the first entry\n@Article{Wło05, title = {A {B} c}, year = 2005, doi = {10.1/x}}\n\n\
        @book{Hir64,\n  doi = {10.2/y}, url = {https://example.org},\n}",
      "@Misc{Sta, title = {S}}",
      "@Book{A, title = \"quoted\"}",
      "@Book{A,\n  title = {T} year = 1}",
      "@Book{9x, title = {T}}",
      "@Book{A, title = {T}}\n% an at sign in a comment:\n@ is the start of an entry",
      "@Book{A, title = {T}, Title = {U}}",
      "@Book{A, title = {T"] do
    match parseBib s with
    | .ok es => logInfo <| "; ".intercalate <| es.toList.map fun e =>
        s!"{e.key} {e.type} {e.url?.getD "(no address)"}"
    | .error e => logInfo m!"error: {e}"

/-- error: ../references.bib: the key `Hir64` is already registered -/
#guard_msgs in
register_bibliography "../references.bib"

/-- error: the bibliography ../lean-toolchain has no entries -/
#guard_msgs in
register_bibliography "../lean-toolchain"

end SourceAttrTest
