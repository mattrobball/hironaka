#!/usr/bin/env python3
"""Compare the `alignment.statements` of a `formalization.yaml` with the `@[source …]` tags.

The tags are read as the JSON lines printed by `scripts/export_source_refs.lean` (from a file, or
from standard input when the file is `-` or omitted). A tagged declaration corresponds to one
statement

  - source: "KEY, locator, page; KEY, locator"   (the `cite` of each of its tags, joined by "; ")
    lean: "Namespace.decl"
    module: "Path/To/Module.lean"

and the check reports every tagged declaration without a statement, every statement whose `lean`
declaration has no tag (unless its `status` says it has no source item), and every `source` or
`module` that differs from the tags. A `source` may write a key as the authors' last names and the
year of its entry in `references.bib` (`label`), e.g. "Hironaka 1964, Main Theorem I, p. 132" for
the cite "Hir64, Main Theorem I, p. 132", or "Bierstone–Milman 1997" for `BM97`. Other fields of a
statement (`status`, `note`) are not checked. The statements in the files `formalization.NAME.yaml`
beside the file, which list the theorems of a namespace kept apart, are read with it. With `--emit`,
the script prints the statements of the tags instead, as YAML to paste under `alignment:`.

The check also compares the `sources` of `formalization.yaml` with `references.bib`: each source
other than an `original-proof` has the `title` of an entry (braces dropped), and the `authors` of
that entry (names as first names and last name).

Usage, from the directory of `lakefile.toml` (`lake lean` builds the library first if needed, and
Lake's progress lines go to standard error):
  lake lean scripts/export_source_refs.lean | python3 scripts/check_formalization_yaml.py formalization.yaml
  lake lean scripts/export_source_refs.lean | python3 scripts/check_formalization_yaml.py --emit
The check needs PyYAML (`uv run --with pyyaml python3 scripts/check_formalization_yaml.py …`);
`--emit` does not. A line of the input that is not a JSON object with the fields `decl`, `file`
and `cite` (for instance a message of Lean, which also writes to standard output) is printed and
makes the script exit with status 2, as does an input without any tag. Exits with status 1 on a
discrepancy.
"""

import glob
import json
import os
import sys

from check_references import BIB, BibError, authors, plain, read_bib

NO_SOURCE = ("not in the sources", "no specific source item")


class InputError(Exception):
    """The input is not the output of `scripts/export_source_refs.lean`."""


def label(entry):
    """How `formalization.yaml` may write the key of a bibliography entry: the last names of its
    authors, joined by an en dash, and its year (`Hironaka 1964`, `Bierstone–Milman 1997`)."""
    year = entry.fields.get("year")
    return "–".join(last for _, last in authors(entry)) + (f" {year}" if year else "")


def labelled(source, labels):
    """`source` with each cite's leading key replaced by its label."""
    parts = []
    for cite in source.split("; "):
        key, _, rest = cite.partition(", ")
        parts.append(f"{labels.get(key, key)}, {rest}" if rest else labels.get(key, key))
    return "; ".join(parts)


def check_sources(doc, entries):
    """The discrepancies between the `sources` of `formalization.yaml` and the bibliography."""
    by_title = {plain(e.fields.get("title", "")): e for e in entries}
    bad = []
    for source in doc.get("sources") or []:
        title = source.get("title", "")
        if source.get("type") == "original-proof":
            continue
        entry = by_title.get(title)
        if entry is None:
            bad.append(f"source {title!r}: no entry of {BIB} has this title")
            continue
        names = [" ".join(filter(None, name)) for name in authors(entry)]
        if source.get("authors") != names:
            bad.append(f"source {title!r}: the authors of `{entry.key}` in {BIB} are {names!r}")
    return bad


def read_tags(path):
    """The statements of the tags, `{decl: {"source": …, "lean": decl, "module": …}}`, in order."""
    handle = sys.stdin if path in (None, "-") else open(path, encoding="utf-8")
    statements = {}
    for line in handle:
        if not line.strip():
            continue
        try:
            tag = json.loads(line)
        except json.JSONDecodeError:
            tag = None
        if not isinstance(tag, dict) or not {"decl", "file", "cite"} <= tag.keys():
            raise InputError(f"not a JSON line of export_source_refs.lean: {line.rstrip()}")
        entry = statements.setdefault(tag["decl"], {"cites": [], "module": tag["file"]})
        entry["cites"].append(tag["cite"])
    return {
        decl: {"source": "; ".join(e["cites"]), "lean": decl, "module": e["module"]}
        for decl, e in statements.items()
    }


def emit(statements):
    print("  statements:")
    for s in statements.values():
        for i, field in enumerate(["source", "lean", "module"]):
            prefix = "    - " if i == 0 else "      "
            print(f"{prefix}{field}: {json.dumps(s[field], ensure_ascii=False)}")


def check(yaml_path, statements):
    try:
        import yaml
    except ImportError:
        print("check_formalization_yaml: needs PyYAML; run it with "
              "`uv run --with pyyaml python3 scripts/check_formalization_yaml.py …`")
        return 2
    with open(yaml_path, encoding="utf-8") as h:
        doc = yaml.safe_load(h)
    try:
        entries = read_bib()
    except BibError as e:
        print(f"check_formalization_yaml: {e}")
        return 1
    labels = {e.key: label(e) for e in entries}
    listed = list((doc.get("alignment") or {}).get("statements") or [])
    # theorems of a namespace kept apart are listed in a `formalization.NAME.yaml` beside it
    here = os.path.dirname(yaml_path) or "."
    for extra in sorted(glob.glob(os.path.join(here, "formalization.*.yaml"))):
        with open(extra, encoding="utf-8") as h:
            listed += (yaml.safe_load(h).get("alignment") or {}).get("statements") or []
    by_decl = {s["lean"]: s for s in listed if "lean" in s}
    bad = check_sources(doc, entries)
    for decl, expected in statements.items():
        actual = by_decl.get(decl)
        if actual is None:
            bad.append(f"`{decl}` is tagged but has no alignment statement")
            continue
        if actual.get("source") not in (expected["source"], labelled(expected["source"], labels)):
            bad.append(f"`{decl}`: source {actual.get('source')!r}, the tags give "
                       f"{labelled(expected['source'], labels)!r}")
        if actual.get("module") != expected["module"]:
            bad.append(f"`{decl}`: module {actual.get('module')!r}, the tags give "
                       f"{expected['module']!r}")
    for decl, s in by_decl.items():
        if decl not in statements and not any(k in str(s.get("status", "")) for k in NO_SOURCE):
            bad.append(f"`{decl}` has an alignment statement but no `@[source …]` tag")
    for b in bad:
        print(f"check_formalization_yaml: {b}")
    if bad:
        print(f"check_formalization_yaml: {len(bad)} discrepancy(ies)")
        return 1
    print(f"check_formalization_yaml: ok ({len(statements)} statements)")
    return 0


def main(argv):
    emitting = bool(argv) and argv[0] == "--emit"
    if not emitting and (not argv or argv[0].startswith("-") and argv[0] != "-"):
        print(__doc__)
        return 2
    try:
        statements = read_tags(argv[1] if len(argv) > 1 else None)
        if not statements:
            raise InputError("no tags in the input "
                             "(did `lake lean scripts/export_source_refs.lean` fail?)")
    except InputError as e:
        print(f"check_formalization_yaml: {e}")
        return 2
    if emitting:
        emit(statements)
        return 0
    return check(argv[0], statements)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
