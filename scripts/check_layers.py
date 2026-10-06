#!/usr/bin/env python3
"""Layer check: no module imports against the grain of the library's layout.

Every module of `Hironaka` and `HironakaExamples` gets a layer from its folder:

  1  objects and foundations: `Hironaka/{Algebra,Analytic,Scheme,Manifold,AnalyticSpace}`
  2  machinery: `Hironaka/Resolution`
  3  examples: `HironakaExamples`

and a module may import only modules of its own layer or a lower one (Mathlib and the other
dependencies are below everything). A module in a folder the table does not name is an error, so
that a new top-level folder has to be placed deliberately. Usage: `python3 scripts/check_layers.py`
from anywhere in the repository; prints every offending import and exits with status 1 if there is
one.
"""

import os
import re
import sys

LAYERS = {
    "Hironaka.Algebra": 1,
    "Hironaka.Analytic": 1,
    "Hironaka.Scheme": 1,
    "Hironaka.Manifold": 1,
    "Hironaka.AnalyticSpace": 1,
    "Hironaka.Resolution": 2,
    "HironakaExamples": 3,
}
LIBS = ["Hironaka", "HironakaExamples"]
IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(\S+)", re.M)


def layer(module):
    for prefix, k in LAYERS.items():
        if module == prefix or module.startswith(prefix + "."):
            return k
    return None


def main():
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    os.chdir(root)
    bad = []
    count = 0
    for lib in LIBS:
        for dirpath, _, files in os.walk(lib):
            for f in sorted(files):
                if not f.endswith(".lean"):
                    continue
                path = os.path.join(dirpath, f)
                module = path[:-5].replace(os.sep, ".")
                src = layer(module)
                count += 1
                if src is None:
                    bad.append(f"{module}: not in any layer (add its folder to LAYERS)")
                    continue
                with open(path, encoding="utf-8") as h:
                    text = h.read()
                for target in IMPORT.findall(text):
                    if not target.startswith(tuple(LIBS)):
                        continue
                    dst = layer(target)
                    if dst is not None and dst > src:
                        bad.append(f"{module} (layer {src}) imports {target} (layer {dst})")
    for b in bad:
        print(f"check_layers: {b}")
    if bad:
        print(f"check_layers: {len(bad)} import(s) against the grain")
        sys.exit(1)
    print(f"check_layers: ok ({count} modules)")


if __name__ == "__main__":
    main()
