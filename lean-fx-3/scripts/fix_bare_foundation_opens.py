#!/usr/bin/env python3
"""Follow-up to delete_foundation_namespace.py: repoint BARE `Foundation` references.

The first pass rewrote fully-qualified `FX1Poly.Foundation`, but consumers also
referenced the namespace bare (resolved via the implicit `FX1Poly` prefix):

  * `open Foundation`  /  `open FX1Poly.Core FX1Poly.Universe Foundation`
  * the qualified `Foundation.RawRenaming` projection

Those bare references survived the first pass and broke the build with
`unknown namespace 'Foundation'`.  This pass is surgical: it rewrites the bare
namespace token to `FX1Poly.Tier0.Syntax` ONLY on `open` statements (unambiguous
code) and at the one qualified `Foundation.<Ctor>` code site — leaving prose and
file-path mentions of "Foundation" untouched (those are handled cosmetically and
never break the build).
"""

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
assert (ROOT / "lakefile.lean").exists(), f"not the repo root: {ROOT}"

# Whole-word `Foundation` not part of a dotted path and not glued to an identifier.
bareToken = re.compile(r"(?<![.\w/])Foundation(?![.\w])")
# Qualified `Foundation.<Ctor>` projection in code (the lone surviving site).
qualifiedCtor = re.compile(r"(?<![.\w/])Foundation\.(RawRenaming|Action|IdAction|MockTy)\b")

openFixCount = 0
qualifiedFixCount = 0
changedFiles = 0
for libdir in ("FX1Poly", "FX1PolyAudit", "FX0Poly"):
    for leanFile in (ROOT / libdir).rglob("*.lean"):
        text = leanFile.read_text()
        if "Foundation" not in text:
            continue
        outputLines = []
        touched = False
        for line in text.split("\n"):
            # Qualified projection: rewrite anywhere it appears as code.
            newLine, qcount = qualifiedCtor.subn(r"FX1Poly.Tier0.Syntax.\1", line)
            if qcount:
                qualifiedFixCount += qcount
                touched = True
            # Bare namespace token: only on `open` statements (unambiguous code).
            if newLine.lstrip().startswith("open "):
                newLine, ocount = bareToken.subn("FX1Poly.Tier0.Syntax", newLine)
                if ocount:
                    openFixCount += ocount
                    touched = True
            outputLines.append(newLine)
        if touched:
            leanFile.write_text("\n".join(outputLines))
            changedFiles += 1

print(f"fixed {openFixCount} open-line token(s) + {qualifiedFixCount} qualified ref(s) "
      f"across {changedFiles} file(s)")
print("DONE. bare Foundation namespace references repointed.")
