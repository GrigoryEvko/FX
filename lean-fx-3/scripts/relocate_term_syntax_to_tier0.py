#!/usr/bin/env python3
"""Relocate the pure de-Bruijn `.term` syntax files from FX1Poly.Core to FX1Poly.Tier0.Syntax.

CORE-REORG: seven files in `FX1Poly/Core/` are pure de Bruijn-syntax operations
(freeVars, occurrence renaming/substitution, the substitution pair, rename-as-subst).
They import only `Tier0.Syntax` modules (or each other), so they belong in the Tier-0
syntax substrate, not in Core.  The `git mv` is done separately; this script rewrites
every IMPORT module-path `FX1Poly.Core.<name>` -> `FX1Poly.Tier0.Syntax.<name>` for the
seven relocated modules, across every `.lean` file (consumers AND the relocated files'
own cross-imports).

Only the MODULE PATH moves; the `namespace FX1Poly.Core` inside each file is UNCHANGED
(matching the 43 existing Tier0/Syntax files that keep `namespace FX1Poly.Core`), so no
declaration reference needs rewriting -- consumers' `open FX1Poly.Core` still resolves
every name.  The token-boundary lookahead `(?![A-Za-z0-9_.])` keeps `RawTermOccurrenceSubst`
from matching inside `RawTermOccurrenceSubstLift` and keeps each module name from matching
a longer identifier.
"""

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
assert (ROOT / "lakefile.lean").exists(), f"not the repo root: {ROOT}"

RELOCATED_MODULES = [
    "RawTermFresh",
    "RawTermFreeVars",
    "RawTermOccurrenceRename",
    "RawTermOccurrenceSubst",
    "RawTermOccurrenceSubstLift",
    "RawTermSubstPair",
    "RawTermRenameAsSubst",
]

# Longest-first so a prefix module (RawTermOccurrenceSubst) cannot shadow its
# extension (RawTermOccurrenceSubstLift) even if the lookahead were dropped.
patterns = [
    (
        re.compile(r"FX1Poly\.Core\." + re.escape(name) + r"(?![A-Za-z0-9_.])"),
        f"FX1Poly.Tier0.Syntax.{name}",
    )
    for name in sorted(RELOCATED_MODULES, key=len, reverse=True)
]

rewriteCount = 0
changedFiles = 0
for libdir in ("FX1Poly", "FX1PolyAudit", "FX0Poly"):
    for leanFile in (ROOT / libdir).rglob("*.lean"):
        text = leanFile.read_text()
        if "FX1Poly.Core.RawTerm" not in text:
            continue
        newText = text
        for matcher, replacement in patterns:
            newText, count = matcher.subn(replacement, newText)
            rewriteCount += count
        if newText != text:
            leanFile.write_text(newText)
            changedFiles += 1

print(f"rewrote {rewriteCount} import path(s) across {changedFiles} file(s)")
print("DONE. seven .term modules repointed to FX1Poly.Tier0.Syntax.")
