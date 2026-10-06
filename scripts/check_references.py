#!/usr/bin/env python3
r"""The bibliography `references.bib`: its check, and the blueprint's Sources list made from it.

`references.bib`, at the root of the package, is the one list of the sources. Its BibTeX keys are
the keys by which everything cites them: the attribute `@[source KEY "locator"]` (whose registry,
`HironakaReferences`, reads the file when it is compiled), docstrings and comments
(`[Hir64, Main Theorem I]`), the blueprint (`\[Hir64, …\]`) and the Markdown files. The check:

* the file is written in the part of BibTeX that every reader of it accepts (`read_bib`, the same
  as `SourceAttr.parseBib`): no key twice, every entry with an author and a title, no
  backslash (accented letters are Unicode characters, not TeX macros);
* a source is listed exactly when the tree cites it. Every key of the file is cited by some `.lean`
  or `.md` file of the package, as `[KEY]` or `[KEY, …]` (also with escaped brackets, `\[KEY\]`,
  as in the blueprint) or by the attribute `@[source KEY …]`. Conversely, every citation of a key
  shaped like the keys of the file, capitals and letters followed by a two-digit year (`Hir64`,
  `BM97`, `Wlo05`), is of a key of the file; citations are looked for in the comments and
  docstrings of the `.lean` files, in the whole text of the blueprint's chapters and in the
  Markdown files. (A citation of an unknown key without a year, such as `[Sta]`, is not found;
  the attribute rejects an unknown key when the library is built.)
* the Sources list of the blueprint, the bulleted list of the section `conv-sources` of
  `blueprint/Blueprint/Conventions.lean`, is the list made from the file: one bullet for each entry
  that the blueprint's chapters cite, in the order of the file, with the citation, the links of its
  `doi`, `eprint` (arXiv) and `url` fields and its `note`.

Build directories (`.lake`, `_out`, `_site`) are not searched. Usage, from anywhere in the
repository:
  python3 scripts/check_references.py           # prints every discrepancy; status 1 if there is one
  python3 scripts/check_references.py --write   # also rewrites the blueprint's Sources list
`scripts/check_formalization_yaml.py` and `scripts/build_docs.py` read the file with `read_bib`.
"""

import os
import re
import sys
from dataclasses import dataclass, field
from urllib.parse import urlparse

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIB = "references.bib"
BLUEPRINT = "blueprint"
SOURCES_CHAPTER = os.path.join(BLUEPRINT, "Blueprint", "Conventions.lean")
SOURCES_TAG = 'tag := "conv-sources"'
SKIP_DIRS = {".git", ".lake", "_out", "_site"}
WIDTH = 100

# A letter of a key: an ASCII letter, or a Latin letter with a diacritic (Latin-1 Supplement and
# Latin Extended-A and -B, without the signs × and ÷), as `SourceAttr.isRefKeyChar`.
LETTER = "A-Za-z\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u024f"
KEY = f"[{LETTER}][{LETTER}0-9]*"
# A citation of a key: `[KEY]`, `[KEY, …]`, `\[KEY\]`, `source KEY`.
CITATION = re.compile(rf"(?:\\?\[|\bsource\s+)({KEY})(?=\\?\]|,|\s)")
# A citation in prose of a key shaped like the keys of the file: capitals and letters, then a year.
YEAR_KEY = re.compile(rf"\\?\[([A-Z][{LETTER}]*[0-9]{{2}})(?=\\?\]|,)")


class BibError(Exception):
    """A malformed bibliography."""


@dataclass
class Entry:
    """An entry of the bibliography: type and field names in lower case, values as written."""
    type: str
    key: str
    line: int
    fields: dict = field(default_factory=dict)


def read_bib(text=None):
    """The entries of `references.bib` (or of the BibTeX text `text`), in order.

    The grammar is that of `SourceAttr.parseBib`: an entry is `@type{key, name = {value},
    …}`, where the key is a letter followed by letters and digits (`KEY`), a field name is made of
    ASCII letters, digits, `_` and `-`, and a value is text in braces (braces inside balanced) or a
    number; text between entries is a comment, so it must not contain `@`. Raises `BibError`,
    naming the line, on anything else.
    """
    if text is None:
        text = read(BIB)
    entries, i, n = [], 0, len(text)

    def fail(msg, at):
        raise BibError(f"{BIB}, line {text.count(chr(10), 0, at) + 1}: {msg}")

    def skip_ws(j):
        while j < n and text[j].isspace():
            j += 1
        return j

    while True:
        i = text.find("@", i)
        if i < 0:
            return entries
        start = i
        m = re.compile(r"@([A-Za-z]+)\s*\{\s*").match(text, i)
        if not m:
            fail("expected an entry `@type{key, …}`", i)
        k = re.compile(KEY).match(text, m.end())
        if not k:
            fail("expected a key: a letter followed by letters and digits", m.end())
        i = skip_ws(k.end())
        if i >= n or text[i] != ",":
            fail(f"expected `,` after the key `{k.group()}`", i)
        entry = Entry(m.group(1).lower(), k.group(), text.count("\n", 0, start) + 1)
        i += 1
        while True:
            i = skip_ws(i)
            if i < n and text[i] == "}":
                i += 1
                break
            name = re.compile(r"[A-Za-z0-9_-]+").match(text, i)
            if not name:
                fail("expected a field name or `}`", i)
            i = skip_ws(name.end())
            if i >= n or text[i] != "=":
                fail("expected `=` after the field name", i)
            i = skip_ws(i + 1)
            if i < n and text[i] == "{":
                depth, j = 0, i + 1
                while j < n and (text[j] != "}" or depth):
                    depth += {"{": 1, "}": -1}.get(text[j], 0)
                    j += 1
                if j >= n:
                    fail("unexpected end of file", j)
                value, i = text[i + 1:j], j + 1
            elif i < n and text[i].isdigit():
                value = re.compile(r"[0-9]+").match(text, i).group()
                i += len(value)
            else:
                fail("expected a value in braces or a number", i)
            if name.group().lower() in entry.fields:
                fail(f"the field `{name.group().lower()}` occurs twice", i)
            entry.fields[name.group().lower()] = value
            i = skip_ws(i)
            if i < n and text[i] == ",":
                i += 1
            elif i < n and text[i] == "}":
                i += 1
                break
            else:
                fail("expected `,` or `}` after a field", i)
        entries.append(entry)


def plain(value):
    """A field value as text: braces dropped, `--` an en dash, white space collapsed."""
    text = value.replace("{", "").replace("}", "").replace("---", "—").replace("--", "–")
    return " ".join(text.split())


def split_top(value, sep):
    """`value` split at the occurrences of `sep` outside braces."""
    parts, depth, start, i = [], 0, 0, 0
    while i < len(value):
        if value[i] in "{}":
            depth += 1 if value[i] == "{" else -1
        elif depth == 0 and value.startswith(sep, i):
            parts.append(value[start:i])
            start = i = i + len(sep)
            continue
        i += 1
    return parts + [value[start:]]


def authors(entry):
    """The authors of an entry as (first names, last name); a name in braces is a last name."""
    names = []
    for name in split_top(entry.fields.get("author", ""), " and "):
        parts = split_top(name.strip(), ",")
        if len(parts) > 1:
            names.append((plain(",".join(parts[1:])), plain(parts[0])))
        else:
            words = split_top(name.strip(), " ")
            names.append((plain(" ".join(words[:-1])), plain(words[-1])))
    return names


def join_names(names):
    """`A`, `A and B`, `A, B and C`."""
    return names[0] if len(names) == 1 else ", ".join(names[:-1]) + " and " + names[-1]


def initials(first):
    """`H.` for `Heisuke`, `P. D.` for `Pierre D.`, `J.-P.` for `Jean-Pierre`."""
    return " ".join("-".join(p[0] + "." for p in w.split("-") if p) for w in first.split())


def citation(entry):
    """The citation of an entry in one line: authors, title and publication data."""
    f = {k: plain(v) for k, v in entry.fields.items()}
    who = join_names([" ".join(filter(None, [initials(a), b])) for a, b in authors(entry)])
    series = " ".join(filter(None, [f.get("series"), f.get("volume")]))
    if entry.type == "article":
        year = f"({f['year']})" if "year" in f else None
        rest = [" ".join(filter(None, [f.get("journal"), f.get("volume"), year])), f.get("pages")]
    elif entry.type in ("incollection", "inproceedings"):
        rest = ["in: " + f.get("booktitle", ""), series, f.get("publisher"), f.get("address"),
                f.get("year"), f.get("pages")]
    else:
        edition = f"{f['edition'].lower()} edition" if "edition" in f else None
        rest = [edition, series, f.get("howpublished"), f.get("publisher"), f.get("address"),
                f.get("year")]
    return ", ".join(filter(None, [who, f.get("title")] + rest))


def links(entry):
    """The links of an entry, `(text, address)`: its DOI, its arXiv identifier, and its `url`
    unless that is the address of one of these (or adds only a version to an arXiv address)."""
    f = entry.fields
    out = []
    if "doi" in f:
        out.append((f"doi:{f['doi']}", f"https://doi.org/{f['doi']}"))
    if "eprint" in f and f.get("archiveprefix", "arXiv").lower() == "arxiv":
        out.append((f"arXiv:{f['eprint']}", f"https://arxiv.org/abs/{f['eprint']}"))
    url = f.get("url")
    if url and not any(url == a or url.startswith(a + "v") for _, a in out):
        out.append((urlparse(url).netloc.removeprefix("www."), url))
    return out


def escape(text):
    """`text` with the characters that open Verso markup escaped."""
    return re.sub(r"([\\*_`\[\]{}])", r"\\\1", text)


def sentence(text):
    """`text` ending with a full stop."""
    return text if text.endswith((".", "?", "!")) else text + "."


def bullet(entry):
    """The lines of the bullet of an entry in the blueprint's Sources list, at most `WIDTH`
    columns wide where the words allow."""
    linked = links(entry)
    parts = [sentence(escape(citation(entry)))]
    if linked:
        parts.append(sentence(", ".join(f"[{t}]({a})" for t, a in linked)))
    if "note" in entry.fields:
        # The identifiers a note mentions are links too, unless the entry links them already.
        done = {t for t, _ in linked}
        note = re.sub(
            r"\b(doi|arXiv):([^\s,;()]*[^\s,;().])",
            lambda m: m.group() if m.group() in done else
            f"[{m.group()}](https://{'doi.org' if m.group(1) == 'doi' else 'arxiv.org/abs'}/"
            f"{m.group(2)})", escape(plain(entry.fields["note"])))
        parts.append(sentence(note[0].upper() + note[1:]))
    words = f"- *\\[{entry.key}\\]* {' '.join(parts)}".split(" ")
    lines = [words[0]]
    for word in words[1:]:
        if len(lines[-1]) + 1 + len(word) <= WIDTH:
            lines[-1] += " " + word
            continue
        # A continuation line must not begin like a block of its own (a list item, a heading).
        carry = [word]
        while re.match(r"[-*+>#:]|[0-9]+[.)]$", carry[0]) and " " in lines[-1].strip():
            lines[-1], _, last = lines[-1].rpartition(" ")
            carry.insert(0, last)
        lines.append("  " + " ".join(carry))
    return lines


def read(path):
    with open(os.path.join(ROOT, path), encoding="utf-8") as h:
        return h.read()


def sources_region(lines):
    """The range of the lines of the Sources list among the lines of `SOURCES_CHAPTER`."""
    try:
        start = next(i for i in range(lines.index(SOURCES_TAG), len(lines))
                     if lines[i].startswith("- *\\["))
    except (ValueError, StopIteration):
        raise BibError(f"{SOURCES_CHAPTER} has no Sources list after `{SOURCES_TAG}`")
    end = start + 1
    while end < len(lines) and lines[end].startswith(("- ", "  ")):
        end += 1
    return start, end


def lean_comments(text):
    """The comments and docstrings of a Lean file (string and character literals skipped)."""
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append(text[i:j])
            i = j
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(text[i:j])
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            i = j + 1
        elif text[i] == "'" and i + 2 < n and text[i + 2] == "'":
            i += 3
        else:
            i += 1
    return "\n".join(out)


def package_texts():
    """(path, text, prose) for every `.lean` and `.md` file of the package, where `prose` is the
    part searched for citations of unknown keys: the comments of a Lean file outside the
    blueprint, all of any other file. The Sources list of the blueprint is left out."""
    for top, dirs, files in os.walk(ROOT):
        dirs[:] = sorted(d for d in dirs if d not in SKIP_DIRS)
        for name in sorted(files):
            if not name.endswith((".lean", ".md")):
                continue
            path = os.path.relpath(os.path.join(top, name), ROOT)
            text = read(path)
            if path == SOURCES_CHAPTER:
                lines = text.split("\n")
                start, end = sources_region(lines)
                text = "\n".join(lines[:start] + lines[end:])
            in_blueprint = path.startswith(BLUEPRINT + os.sep)
            prose = text if name.endswith(".md") or in_blueprint else lean_comments(text)
            yield path, text, prose


def main(argv):
    write = argv == ["--write"]
    if argv and not write:
        print(__doc__)
        return 2
    bad = []
    try:
        entries = read_bib()
        chapter = read(SOURCES_CHAPTER).split("\n")
        start, end = sources_region(chapter)
    except BibError as e:
        print(f"check_references: {e}")
        return 1
    keys = [e.key for e in entries]
    for k in sorted({k for k in keys if keys.count(k) > 1}):
        bad.append(f"the key `{k}` occurs more than once in {BIB}")
    for e in entries:
        for f in ("author", "title"):
            if f not in e.fields:
                bad.append(f"{BIB}, line {e.line}: `{e.key}` has no {f}")
        for f, v in e.fields.items():
            if "\\" in v:
                bad.append(f"{BIB}, line {e.line}: the {f} of `{e.key}` contains a backslash")
            if f in ("url", "doi", "eprint") and (not v or any(c.isspace() for c in v)):
                bad.append(f"{BIB}, line {e.line}: the {f} of `{e.key}` is empty or has spaces")

    cited, cited_by_blueprint, unknown = set(), set(), {}
    for path, text, prose in package_texts():
        found = set(CITATION.findall(text)) & set(keys)
        cited |= found
        if path.startswith(BLUEPRINT + os.sep):
            cited_by_blueprint |= found
        for k in YEAR_KEY.findall(prose):
            if k not in keys:
                unknown.setdefault(k, path)
    for k in keys:
        if k not in cited:
            bad.append(f"`{k}` is in {BIB} but no file of the package cites it")
    for k, path in sorted(unknown.items()):
        bad.append(f"{path} cites `{k}`, which is not in {BIB}")

    listed = [line for e in entries if e.key in cited_by_blueprint for line in bullet(e)]
    if chapter[start:end] != listed:
        if write:
            chapter[start:end] = listed
            with open(os.path.join(ROOT, SOURCES_CHAPTER), "w", encoding="utf-8") as h:
                h.write("\n".join(chapter))
            print(f"check_references: wrote the Sources list of {SOURCES_CHAPTER}")
        else:
            bad.append(f"the Sources list of {SOURCES_CHAPTER} is not the one {BIB} gives; "
                       "run `python3 scripts/check_references.py --write`")

    for b in bad:
        print(f"check_references: {b}")
    if bad:
        print(f"check_references: {len(bad)} discrepancy(ies)")
        return 1
    print(f"check_references: ok ({len(keys)} references, "
          f"{len(cited_by_blueprint)} cited by the blueprint)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
