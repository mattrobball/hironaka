/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public meta import Lean.Elab.Command
import Lean.DocString.Extension

/-!
# The `source` attribute: the published source of a declaration

A declaration that formalizes a statement of the literature records where the statement is printed:
```
@[source Hir64 "Main Theorem I" "p. 132"]
theorem exists_support_eq_singularLocus_isRegular_blowUp …
```
The attribute takes a key of the bibliography registry, a locator (the item of the source: a
theorem, a section, an equation) and optionally a page, and after these optionally a free comment
`(comment := "…")`:
```
@[source KEY "locator"]
@[source KEY "locator" "page"]
@[source KEY "locator" "page" (comment := "…")]
@[source KEY "locator" (comment := "…")]
```
A declaration may carry several `source` attributes (`@[source Hir64 "…", source Kol07 "…"]`).

The **bibliography registry** holds the sources a `source` attribute may cite. It is filled by
the command `register_bibliography "path"`, which reads a BibTeX file and registers each entry
under its key, with the address its citations link to. A project keeps its registry in one module
that runs this command on its bibliography (in this package, `HironakaReferences` reads
`references.bib`). A key is a letter followed by letters and digits, where a letter may be a Latin letter
with a diacritic: `Wło05` is a key, although it is not a Lean identifier. A key that is not
registered is an elaboration error, so modules citing a source import the registry module.

Each `source` attribute
* records a `SourceTag` (declaration, module, key, locator, page, comment) in the persistent
  environment extension `sourceTagExt`;
* appends a paragraph to the declaration's docstring, `Source: [KEY, locator, page](url)`
  followed by ` (comment)` if there is a comment, linking to the URL of the registry entry when it
  has one (plain `Source: [KEY, locator, page]` otherwise).

The command `#source_refs` lists every tagged declaration of the environment, `#source_refs KEY`
those citing `KEY`; `scripts/export_source_refs.lean` prints the tags as JSON lines
(`SourceTag.toJson`).

## Implementation notes

The design follows Mathlib's cross-reference attributes (`Mathlib.Tactic.CrossRefAttribute`:
`@[stacks TAG]`, `@[kerodon TAG]`, `@[wikidata QID]`), whose database is a closed inductive type,
with the following differences.

* **Docstrings.** Mathlib's attributes run `beforeElaboration`, before the elaborator stores the
  docstring of the declaration, which then replaces the link: a documented declaration tagged
  `@[stacks …]` has no link in its docstring. This attribute runs `afterCompilation`, after the
  docstring is stored, and appends to the docstring as the final environment of the module records
  it (`finalDocString?`). For a theorem whose proof is elaborated asynchronously (Lean's default)
  the docstring is stored by the elaboration of the proof, on its own environment branch, while the
  attribute runs on the main branch; reading the final docstring waits for that elaboration, and the
  appended docstring reaches the final environment. So the `Source:` paragraphs are in the `.olean`
  file, and hence in doc-gen4 and in every importing module, whatever the order in which the
  docstring and the attribute are processed; `attribute [source …] foo` after the declaration of
  `foo`, in its module, works as well. Within the declaring module, `findDocString?` (and the
  hover) shows the docstring of such a theorem as its proof's branch stored it, without the
  paragraphs; for definitions, structures and synchronously elaborated theorems they are visible
  at once.
* **Keys.** A reference key is parsed by the token function `refKeyFn`, which accepts the
  non-ASCII keys of `references.bib`; `parseBib` reads the keys of the file with the same
  characters.
* **State.** The tags are recorded in the extension `sourceTagExt` in the `sync` mode, which may be
  written on any environment branch; the registry `referenceExt` is written only by the
  `register_bibliography` command. Both keep the entries of the imported modules as they were
  imported (as Mathlib's `tagExt` does), so importing costs nothing.

This module imports what `Mathlib.Tactic.CrossRefAttribute` imports: `Lean.Elab.Command`, and
`Mathlib.Init` so that Mathlib's linters run on it, and adds nothing to an importer's closure
beyond these.
-/

public meta section

open Lean Elab Command Parser

namespace SourceAttr

/-! ### Reference keys -/

/-- A character of a reference key: an ASCII letter or digit, or a Latin letter with a diacritic of
Unicode's Latin-1 Supplement and Latin Extended-A and Extended-B blocks, such as the `ł` of
`Wło05` (the signs `×` and `÷` of the Latin-1 Supplement excepted). -/
def isRefKeyChar (c : Char) : Bool :=
  c.isAlphanum || (0xC0 ≤ c.val && c.val ≤ 0x24F && c.val != 0xD7 && c.val != 0xF7)

/-- The node kind of reference keys. -/
abbrev refKeyKind : SyntaxNodeKind := `SourceAttr.refKey

/-- The token function of reference keys: a letter followed by letters and digits, in the sense of
`isRefKeyChar`, such as `Hir64`, `BM97`, `Sta` or `Wło05`. Unlike an identifier, a key may contain
Latin letters with diacritics. -/
def refKeyFn : ParserFn := fun c s =>
  let i := s.pos
  let s := takeWhileFn isRefKeyChar c s
  if s.hasError then
    s
  else if s.pos == i then
    s.mkError "reference key"
  else if (c.extract i s.pos).front.isDigit then
    s.mkUnexpectedError "a reference key starts with a letter"
  else
    mkNodeToken refKeyKind i true c s

@[inherit_doc refKeyFn]
def refKeyNoAntiquot : Parser where
  fn := refKeyFn
  info := mkAtomicInfo "refKey"

@[inherit_doc refKeyFn]
def refKey : Parser :=
  withAntiquot (mkAntiquot "refKey" refKeyKind) refKeyNoAntiquot

/-- The formatter of reference keys. -/
@[combinator_formatter refKeyNoAntiquot]
def refKeyNoAntiquot.formatter : PrettyPrinter.Formatter :=
  PrettyPrinter.Formatter.visitAtom refKeyKind

/-- The parenthesizer of reference keys. -/
@[combinator_parenthesizer refKeyNoAntiquot]
def refKeyNoAntiquot.parenthesizer : PrettyPrinter.Parenthesizer :=
  PrettyPrinter.Parenthesizer.visitToken

/-- The key of a reference-key node. -/
def getRefKey (stx : TSyntax refKeyKind) : String :=
  (stx.raw.isLit? refKeyKind).getD ""

/-! ### The bibliography registry -/

/-- An entry of the bibliography registry: a source that `source` attributes may cite. -/
structure Reference where
  /-- The key of the source's entry in `references.bib`: `Hir64`, `Wlo05`. -/
  key : String
  /-- The address a rendered citation links to, if any: the `url` field of the entry, or else the
  address of its `doi` (`BibEntry.url?`). -/
  url? : Option String
  deriving Inhabited, Repr

/-- The bibliography registry, written by `register_bibliography`. The state is the array of the
entries of each imported module, as imported; the entries of the current module are the local
entries of the extension. -/
initialize referenceExt : SimplePersistentEnvExtension Reference (Array (Array Reference)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := id
    addEntryFn := fun s _ => s
  }

/-- The registered references, in the order of registration. -/
def getReferences (env : Environment) : Array Reference :=
  let (current, imported) := PersistentEnvExtension.getState referenceExt env
  imported.flatten ++ current.reverse.toArray

/-- The registered reference with key `key`, if any. -/
def findReference? (env : Environment) (key : String) : Option Reference :=
  (getReferences env).find? (·.key == key)

/-! ### Reading a BibTeX file -/

/-- An entry of a BibTeX file. -/
structure BibEntry where
  /-- The entry type, in lower case: `article`, `book`. -/
  type : String
  /-- The key: `Hir64`. -/
  key : String
  /-- The fields in order, each a name in lower case and a value: the text between the braces as
  written, or the number. -/
  fields : Array (String × String)
  /-- The line of the file at which the entry starts. -/
  line : Nat
  deriving Inhabited, Repr

/-- The value of the field `name` of an entry, if it has one. -/
def BibEntry.field? (e : BibEntry) (name : String) : Option String :=
  (e.fields.find? (·.1 == name)).map (·.2)

/-- The address rendered citations of an entry link to: its `url` field, or else the address
`https://doi.org/…` of its `doi` field; none if it has neither. -/
def BibEntry.url? (e : BibEntry) : Option String :=
  e.field? "url" <|> (e.field? "doi").map ("https://doi.org/" ++ ·)

namespace BibParser

/-- The parser state: the rest of the input and the current line. -/
abbrev M := StateT (List Char × Nat) (Except String)

/-- Fails with `msg`, prefixed by the current line. -/
def fail {α : Type} (msg : String) : M α := do
  throw s!"line {(← get).2}: {msg}"

/-- The next character, if any, without consuming it. -/
def peek? : M (Option Char) :=
  return (← get).1.head?

/-- Consumes the next character. -/
def next : M Char := do
  match ← get with
  | (c :: cs, n) =>
    set (cs, if c == '\n' then n + 1 else n)
    return c
  | ([], _) => fail "unexpected end of file"

/-- Consumes the characters satisfying `p` and returns them. -/
partial def takeWhile (p : Char → Bool) (acc : String := "") : M String := do
  match ← peek? with
  | some c => if p c then do discard next; takeWhile p (acc.push c) else return acc
  | none => return acc

/-- Consumes white space. -/
def skipWs : M Unit :=
  discard <| takeWhile Char.isWhitespace

/-- Consumes the character `c`, described as `what` in the error message if it is not next. -/
def expect (c : Char) (what : String) : M Unit := do
  if (← peek?) == some c then discard next else fail s!"expected {what}"

/-- The text up to the brace closing an opened one, braces inside balanced; consumes the closing
brace. -/
partial def braced (depth : Nat := 0) (acc : String := "") : M String := do
  match ← next with
  | '}' => if depth == 0 then return acc else braced (depth - 1) (acc.push '}')
  | '{' => braced (depth + 1) (acc.push '{')
  | c => braced depth (acc.push c)

/-- A field value: text in braces, or a number. -/
def value : M String := do
  match ← peek? with
  | some '{' => discard next; braced
  | some c =>
    if c.isDigit then takeWhile Char.isDigit
    else fail "expected a value in braces or a number"
  | none => fail "unexpected end of file"

/-- The fields of an entry up to its closing brace, which is consumed. -/
partial def fields (acc : Array (String × String)) : M (Array (String × String)) := do
  skipWs
  if (← peek?) == some '}' then discard next; return acc
  let name := (← takeWhile fun c => c.isAlphanum || c == '_' || c == '-').toLower
  if name.isEmpty then fail "expected a field name or `}`"
  skipWs; expect '=' "`=` after the field name"; skipWs
  let v ← value
  if acc.any (·.1 == name) then fail s!"the field `{name}` occurs twice"
  skipWs
  match ← peek? with
  | some ',' => discard next; fields (acc.push (name, v))
  | some '}' => discard next; return acc.push (name, v)
  | _ => fail "expected `,` or `}` after a field"

/-- An entry, `@type{key, field = {value}, …}`. -/
def entry : M BibEntry := do
  let line := (← get).2
  expect '@' "`@`"
  let type ← takeWhile Char.isAlpha
  if type.isEmpty then fail "expected an entry type after `@`"
  skipWs; expect '{' "`{` after the entry type"; skipWs
  let key ← takeWhile isRefKeyChar
  match key.toList with
  | c :: _ => if c.isDigit then fail s!"the key `{key}` starts with a digit"
  | [] => fail "expected a key: a letter followed by letters and digits"
  skipWs; expect ',' s!"`,` after the key `{key}`"
  return { type := type.toLower, key, fields := ← fields #[], line }

/-- The entries of the rest of the file. Text outside the entries (comments) is skipped: it is
everything up to the next `@`. -/
partial def entries (acc : Array BibEntry) : M (Array BibEntry) := do
  discard <| takeWhile (· != '@')
  if (← peek?).isNone then return acc
  entries (acc.push (← entry))

end BibParser

/-- The entries of a BibTeX file, or an error naming the line where it is malformed. The file is
read in a strict part of BibTeX: an entry is `@type{key, name = {value}, …}`, where the key is a
reference key (`refKeyFn`), a field name is made of ASCII letters, digits, `_` and `-`, and a value
is text in braces (braces inside balanced) or a number; text between entries is a comment, so it
must not contain `@`. Strings (`@string`), quoted values and concatenation (`#`) are errors. -/
def parseBib (s : String) : Except String (Array BibEntry) :=
  (BibParser.entries #[]).run' (s.toList, 1)

/--
`register_bibliography "path"` adds every entry of the BibTeX file at `path` (relative to the
directory of the current file) to the bibliography registry, under its key and with its address
(`BibEntry.url?`); `source` attributes then cite it. The file is read with `parseBib`. A key can be
registered once.

Lake does not see that a module reads a file: the library holding the registry module should
declare the file as a dependency (`needs` in `lakefile.toml`), so that a change to the file
rebuilds the registry and what imports it.
-/
syntax (name := registerBibliography) "register_bibliography " str : command

@[command_elab registerBibliography, inherit_doc registerBibliography]
def elabRegisterBibliography : CommandElab
  | `(register_bibliography $path) => do
    let some dir := (System.FilePath.mk (← getFileName)).parent
      | throwError "cannot compute the directory of the current file"
    let name := path.getString
    let text ← match ← (IO.FS.readFile (dir / name)).toBaseIO with
      | .ok text => pure text
      | .error e => throwErrorAt path "cannot read the bibliography {name}: {toString e}"
    let entries ← match parseBib text with
      | .ok entries => pure entries
      | .error msg => throwErrorAt path "malformed bibliography {name}, {msg}"
    if entries.isEmpty then throwErrorAt path "the bibliography {name} has no entries"
    for e in entries do
      if (findReference? (← getEnv) e.key).isSome then
        throwErrorAt path "{name}: the key `{e.key}` is already registered"
      if let some url := e.url? then
        if url.isEmpty || url.any Char.isWhitespace then
          throwErrorAt path "{name}: the address {repr url} of `{e.key}` is empty or contains \
            white space"
      modifyEnv (referenceExt.addEntry · { key := e.key, url? := e.url? })
  | _ => throwUnsupportedSyntax

/-! ### Source tags -/

/-- A citation of a source by a declaration, recorded by a `source` attribute. -/
structure SourceTag where
  /-- The declaration. -/
  declName : Name
  /-- The module of the declaration. -/
  module : Name
  /-- The key of the source in the bibliography registry. -/
  key : String
  /-- The item of the source: `Main Theorem I`, `Theorem 1.0.2`, `§3, (3.4)`. -/
  locator : String
  /-- The page, if given: `p. 132`, `pp. 142–143`. -/
  page? : Option String
  /-- A free comment, if given. -/
  comment? : Option String
  deriving Inhabited, BEq, Repr

namespace SourceTag

/-- The citation text of a tag, `KEY, locator` or `KEY, locator, page`, as the library writes
citations in docstrings (`[Hir64, Main Theorem I, p. 132]` without the brackets). -/
def cite (t : SourceTag) : String :=
  ", ".intercalate ([t.key, t.locator] ++ t.page?.toList)

/-- The comment of a tag in parentheses after a space, or the empty string. -/
def commentSuffix (t : SourceTag) : String :=
  (t.comment?.map (s!" ({·})")).getD ""

/-- The paragraph a tag appends to the docstring: `Source: [cite](url)`, or `Source: [cite]` when
the reference has no URL, followed by the comment. Brackets in the citation text are escaped. -/
def docLine (t : SourceTag) (url? : Option String) : String :=
  let text := t.cite.foldl (init := "") fun acc c =>
    if c == '[' || c == ']' then acc.push '\\' |>.push c else acc.push c
  let link := match url? with
    | some url => s!"[{text}]({url})"
    | none => s!"[{text}]"
  s!"Source: {link}{t.commentSuffix}"

/-- The path of the source file of a module relative to the root of its package:
`SourceAttr.lean` for `SourceAttr`. -/
def moduleFile (module : Name) : String :=
  "/".intercalate (module.components.map (·.toString (escape := false))) ++ ".lean"

/-- The JSON object of a tag, with the fields `decl`, `module`, `file` (the path of the module's
source file), `key`, `locator`, `page` and `comment` (`null` when absent), `url` (the URL of the
reference, or `null`) and `cite` (the citation text `KEY, locator, page`). -/
def toJson (t : SourceTag) (url? : Option String) : Json :=
  Json.mkObj [
    ("decl", t.declName.toString),
    ("module", t.module.toString),
    ("file", moduleFile t.module),
    ("key", t.key),
    ("locator", t.locator),
    ("page", Lean.toJson t.page?),
    ("comment", Lean.toJson t.comment?),
    ("url", Lean.toJson url?),
    ("cite", t.cite)]

end SourceTag

/-- The source tags, written by the `source` attribute. The state is the array of the entries of
each imported module, as imported; the entries of the current module are the local entries of the
extension. The extension is in the `sync` mode, which may be written on any environment branch;
reading it waits for the pending elaborations of the module. -/
initialize sourceTagExt : SimplePersistentEnvExtension SourceTag (Array (Array SourceTag)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := id
    addEntryFn := fun s _ => s
    asyncMode := .sync
  }

/-- Every source tag of the environment, sorted by declaration name; the tags of one declaration
in the order of its attributes. -/
def getSourceTags (env : Environment) : Array SourceTag :=
  let (current, imported) := PersistentEnvExtension.getState sourceTagExt env
  let tags := imported.flatten.toList ++ current.reverse
  (tags.mergeSort fun a b => a.declName.cmp b.declName != .gt).toArray

/-- The JSON lines of every source tag of the environment (`SourceTag.toJson`), in the order of
`getSourceTags`. -/
def exportSourceTags (env : Environment) : Array String :=
  (getSourceTags env).map fun t => (t.toJson ((findReference? env t.key).bind (·.url?))).compress

/-! ### The attribute -/

/-- The Markdown docstring of `decl`, a declaration of the current module, as the environment will
record it once every pending elaboration is over (the `sync` state of `docStringExt`). This differs
from what `findDocString?` returns on the main environment branch for a theorem whose proof is
elaborated asynchronously: its docstring is stored on the branch of the proof, and later changes
made on the main branch reach the final environment (and the `.olean` file) but not the snapshot
of the branch that `findDocString?` reads. The call waits for the pending elaborations. -/
def finalDocString? (env : Environment) (decl : Name) : Option String :=
  (docStringExt.toPersistentEnvExtension.getState (asyncMode := .sync) env).find? decl

/-- Appends the paragraph `line` to the docstring of `decl`, a declaration of the current module.
It is an error if the docstring already has this paragraph or is a Verso docstring. -/
def appendDocLine (decl : Name) (line : String) : CoreM Unit := do
  let env ← getEnv
  if let some (.inr _) ← findInternalDocString? env decl (includeBuiltin := false) then
    throwError "the `source` attribute does not support Verso docstrings"
  let old := ((finalDocString? env decl).getD "").trimAsciiEnd.copy
  if (old.splitOn "\n\n").contains line then
    throwError "duplicate source: the docstring of `{.ofConstName decl}` already \
      reads{indentD line}"
  addDocStringCore decl (if old.isEmpty then line else old ++ "\n\n" ++ line)

/-- Records the source tag of `decl` with key `key`, locator `locator`, page `page?` and comment
`comment?`, and appends its paragraph to the docstring of `decl`; the work of the `source`
attribute. -/
def addSource (decl : Name) (key : TSyntax refKeyKind) (locator : StrLit)
    (page? comment? : Option StrLit) : CoreM Unit := do
  let env ← getEnv
  let k := getRefKey key
  let some ref := findReference? env k
    | let hint := if (getReferences env).isEmpty then
          m!" (no reference is registered: import the module that runs `register_bibliography`)"
        else m!""
      throwErrorAt key "unknown reference key `{k}`: it is not in the registered bibliography{hint}"
  for s in [some locator, page?, comment?].filterMap id do
    if s.getString.isEmpty then throwErrorAt s "empty string in a `source` attribute"
  let tag : SourceTag := {
    declName := decl, module := env.mainModule, key := k, locator := locator.getString,
    page? := page?.map (·.getString), comment? := comment?.map (·.getString) }
  appendDocLine decl (tag.docLine ref.url?)
  modifyEnv (sourceTagExt.addEntry · tag)

/--
`@[source KEY "locator"]` records that the declaration formalizes the item `locator` of the source
`KEY` of the bibliography registry (`register_bibliography`), and appends
`Source: [KEY, locator](url)` to its docstring. Optional arguments, in this order: a page,
`@[source KEY "locator" "page"]`, rendered `[KEY, locator, page]`; a comment,
`(comment := "…")`, rendered in parentheses after the link. A declaration may carry several
`source` attributes. An unknown `KEY` is an error.
-/
syntax (name := source) "source " refKey ppSpace str (ppSpace str)?
  (ppSpace "(" &"comment" " := " str ")")? : attr

initialize registerBuiltinAttribute {
  name := `source
  descr := "The published source of a declaration: `@[source KEY \"locator\" \"page\"]`."
  add := fun decl stx kind => do
    unless kind == .global do throwError "the `source` attribute must be global"
    let `(attr| source $key $locator $[$page?]? $[(comment := $comment?)]?) := stx
      | throwError "expected `@[source KEY \"locator\"]`, optionally followed by a page \
          \"page\" and a comment (comment := \"…\")"
    addSource decl key locator page? comment?
  -- after the elaborator has stored the docstring (see `finalDocString?` for theorems)
  applicationTime := .afterCompilation
}

/-! ### Listing -/

/--
`#source_refs` lists every declaration of the environment that carries a `source` attribute, one
line per attribute, `decl: [KEY, locator, page] (comment)`, sorted by declaration name.
`#source_refs KEY` lists only the citations of `KEY`.
-/
elab (name := sourceRefs) "#source_refs" key?:(ppSpace colGt refKey)? : command => do
  let env ← getEnv
  let mut tags := getSourceTags env
  if let some key := key? then
    let k := getRefKey key
    if (findReference? env k).isNone then throwErrorAt key "unknown reference key `{k}`"
    tags := tags.filter (·.key == k)
  if tags.isEmpty then
    logInfo "No sources found."
  else
    logInfo <| MessageData.joinSep (tags.toList.map fun t =>
      m!"{.ofConstName t.declName (fullNames := true)}: [{t.cite}]{t.commentSuffix}") "\n"

end SourceAttr
