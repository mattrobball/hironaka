/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

import SourceAttr

/-!
# The bibliography registry

The entries of `references.bib`, the bibliography at the root of the package, registered under
their BibTeX keys for the `source` attribute (`SourceAttr`): a module that tags a
declaration with `@[source KEY "…"]` imports this module. A rendered citation links to the `url`
field of the entry, or else to the address of its `doi`: the version of the source whose item
numbers the library cites (the arXiv version for [Kol07] and [BM97]), otherwise the published
version, otherwise the author's or project's own copy.

The file is read when this module is compiled. In `lakefile.toml` this module forms a library of
its own, `HironakaReferences`, which needs the input file `references.bib`, so that Lake rebuilds
it, and the modules that import it, when the file changes.
-/

public section

register_bibliography "references.bib"
