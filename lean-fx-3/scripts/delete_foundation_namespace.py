#!/usr/bin/env python3
"""Delete the FX1Poly.Foundation namespace: fold it into FX1Poly.Tier0.Syntax.

The three ex-Foundation modules (Action, RenameDefs, ActionInstances) were
physically relocated to FX1Poly/Tier0/Syntax/ in the Phase-1 restructure but kept
`namespace FX1Poly.Foundation` (Phase 1 moved paths only, preserving namespaces).

The Foundation namespace is the cleanly-deletable case: it is NON-SHARED (only
those three relocated files ever declare it) and nothing yet occupies
FX1Poly.Tier0.Syntax (verified). So erasing it is a single token-boundary-safe
literal rename across the whole tree — namespace declarations, `open`s, qualified
references, audit pragmas, and docstrings all repoint to FX1Poly.Tier0.Syntax,
making the namespace finally match the on-disk Tier0/Syntax/ path.

Token-boundary guard: `FX1Poly.Foundation` is rewritten only when NOT followed by
an identifier character, so a hypothetical `FX1Poly.FoundationFoo` could never be
corrupted (verified absent, but the guard future-proofs the rename).
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
assert (ROOT / "lakefile.lean").exists(), f"not the repo root: {ROOT}"

OLD_NAMESPACE = "FX1Poly.Foundation"
NEW_NAMESPACE = "FX1Poly.Tier0.Syntax"
boundaryRename = re.compile(re.escape(OLD_NAMESPACE) + r"(?![A-Za-z0-9_])")

changedFiles = 0
changedOccurrences = 0
for libdir in ("FX1Poly", "FX1PolyAudit", "FX0Poly"):
    for leanFile in (ROOT / libdir).rglob("*.lean"):
        text = leanFile.read_text()
        if OLD_NAMESPACE not in text:
            continue
        rewritten, count = boundaryRename.subn(NEW_NAMESPACE, text)
        if count:
            leanFile.write_text(rewritten)
            changedFiles += 1
            changedOccurrences += count

print(f"renamed {changedOccurrences} occurrence(s) across {changedFiles} file(s)")
print("DONE. FX1Poly.Foundation -> FX1Poly.Tier0.Syntax.")
