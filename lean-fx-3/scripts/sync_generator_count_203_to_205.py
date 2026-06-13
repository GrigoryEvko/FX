#!/usr/bin/env python3
"""TABLE-CANON-8 doc/count sync: the Generator enum is now 205 constructors
(GeneratorCountPin.generatorCount = 205, gen_npComplete at index 204, both pin
theorems green). Many docstrings still cite the pre-last-two-generators count
of 203 (and the totalityClass partition 199-of-203). This script does TARGETED
LITERAL phrase replacement only — never a blanket '203' -> '205' substring strip,
so generator tag data (`=> 203`, `203 =>`) and any other numeric uses are left
untouched."""

import pathlib

# Roots holding kernel Lean source (NOT the .md spec files — those sync under
# the separate NATIVE-62 / MOON-DOCS tasks).
ROOTS = ["FX1Poly", "FX1PolyAudit", "FX0Poly"]

# Literal phrase replacements. Each is an unambiguous generator-count phrasing.
PHRASE_REPLACEMENTS = [
    ("203 generator", "205 generator"),     # "203 generators"
    ("203 constructor", "205 constructor"), # "203 constructors"
    ("203 ctor", "205 ctor"),               # "203 ctors"
    ("203 arm", "205 arm"),                 # "203 arms"
    ("203-generator", "205-generator"),
    ("203-arm", "205-arm"),
    ("203-ctor", "205-ctor"),
    ("203-way", "205-way"),
    ("203-constructor", "205-constructor"),
    # totalityClass partition: 4 non-total (2 partial + 2 productive) of 205 ->
    # totalClass = 201; the old "199 of the 203" predates the +2 (both total).
    ("199 of the 205 generators", "201 of the 205 generators"),
]

repo = pathlib.Path(__file__).resolve().parent.parent
changed = []
for root in ROOTS:
    for path in (repo / root).rglob("*.lean"):
        text = path.read_text()
        updated = text
        for old, new in PHRASE_REPLACEMENTS:
            updated = updated.replace(old, new)
        if updated != text:
            path.write_text(updated)
            hits = sum(text.count(old) for old, _ in PHRASE_REPLACEMENTS)
            changed.append((path.relative_to(repo), hits))

for rel, hits in sorted(changed):
    print(f"{rel}: {hits} replacement(s)")
print(f"--- {len(changed)} file(s) changed ---")
