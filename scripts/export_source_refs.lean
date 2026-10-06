/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
import Lean
import Hironaka

/-!
# Export of the `@[source …]` tags as JSON lines

Run as `lake lean scripts/export_source_refs.lean` from the directory of `lakefile.toml`: Lake
builds the library this file imports and hands it to Lean (from its artifact cache when it is
cached). The script prints on standard output one JSON object per `source` attribute of `Hironaka`,
sorted by declaration name (the attributes of one declaration in their order), with the fields
* `decl`: the declaration, `module`: its module, `file`: the module's source file relative to the
  directory of `lakefile.toml`;
* `key`, `locator`, `page`, `comment`: the arguments of the attribute (`page` and `comment` are
  `null` when absent);
* `url`: the address of the reference in the registry (`null` if it has none);
* `cite`: the citation text `KEY, locator, page`, as rendered in the docstring.

This is the input of `scripts/check_formalization_yaml.py`, which compares it with the
`alignment.statements` table of `formalization.yaml`:
```
lake lean scripts/export_source_refs.lean |
  python3 scripts/check_formalization_yaml.py formalization.yaml
```
Nothing else is printed on standard output while the build succeeds; Lean's own messages (an
error or a warning of this file) would go there too, and the check reports them as lines that are
not JSON.
-/

open Lean Elab Command in
run_cmd do
  let lines := SourceAttr.exportSourceTags (← getEnv)
  -- written to standard output directly: a `logInfo` message would carry a position prefix
  let out ← IO.getStdout
  for line in lines do
    out.putStrLn line
  out.flush
