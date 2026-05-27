#!/usr/bin/env python3
"""Audit orphan-file detector for the V2 substrate.

V2-fix-9 (2026-05-27).  Discharges Agent 3's audit-coverage
gap: detects .lean files in `LeanFX2/Foundation/PolyCell/Core/`
whose namespaced declarations have NO `#assert_no_axioms` gate
in any audit file.

## What this detector does

For each `.lean` file in the V2 substrate
(`LeanFX2/Foundation/PolyCell/Core/`):

1. Extract every top-level `def` / `theorem` / `lemma` /
   `inductive` / `structure` declaration name.
2. Compare against the `#assert_no_axioms` gate corpus in
   `LeanFX2/Tools/AuditAll/AuditPolyCell.lean`.
3. Report files whose declarations are entirely UN-gated.

## Why this matters

Each new V2 file should ship with at least one
`#assert_no_axioms` gate per public declaration -- per the
zero-axiom discipline in `lean-fx-2/CLAUDE.md`.  A file with
NO gates means the audit's structural-coverage promise has a
hole: a regression could land axiomful code in that file and
slip past the gate.

This script is a regression detector: it ensures that when
NEW V2 files are added in future sessions (e.g. V2-bridge.*,
V2-mig.*, V2-L3.*), they do not slip in without audit gates.

## Limitations (intentional)

* The detector reports FILE-level coverage, not declaration-level.
  A file with at least one gated declaration passes -- even if
  other declarations in the same file are un-gated.  Declaration-
  level coverage is a stricter audit deferred to a future
  Tool/StrictHarness/* extension.

* The detector treats `private def` / `private theorem` as
  non-public and skips them.  Same for `set_option` / `attribute`
  / `namespace` / `open` headers.

* The detector matches gate references via simple text search.
  A gate `#assert_no_axioms Mod.Foo.bar` is treated as covering
  `bar` from module `Mod.Foo`.  False positives possible if a
  file declares `bar` and another module also has `bar` gated
  -- but this is rare in practice and would be visible during
  manual review.

## Usage

```
python3 scripts/audit_orphan_v2_files.py
```

Output to stdout:

* Lines `OK: <module>` -- file has at least one gated declaration.
* Lines `ORPHAN: <module> -- N declarations, 0 gated` -- file
  has at least one public declaration but NONE are gated.
* Final summary line with orphan count.

Exit code:

* `0` if no orphans detected.
* `1` if any orphan detected (suitable for CI gating).

## Forward-compat

When V2-mig.x drops the `V2` suffix on V2 file names (renaming
`RawTermV2` -> `RawTerm`, etc.), update the path glob in this
script accordingly.
"""

import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
V2_DIR = ROOT / "LeanFX2" / "Foundation" / "PolyCell" / "Core"
AUDIT_FILE = ROOT / "LeanFX2" / "Tools" / "AuditAll" / "AuditPolyCell.lean"

# Regex captures top-level declarations.  Lean 4 declaration syntax:
#   def <name>     -- function
#   theorem <name> -- theorem
#   lemma <name>   -- alias for theorem in some styles
#   inductive <name>
#   structure <name>
#   instance [<name> :] ... -- instance declarations; the optional
#                              named instance is what we capture
#   class <name>   -- typeclass declaration
#
# We also accept the @[reducible] / @[simp] / @[ext] etc. attribute
# prefix, since attributes don't change the public identity.
#
# `private` declarations are NON-public; skip them.
DECL_REGEX = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"  # optional attribute prefix
    r"(?P<kind>def|theorem|lemma|inductive|structure|class|abbrev)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_.?'!]*)",
    flags=re.MULTILINE,
)

# Match #assert_no_axioms gates: capture the fully-qualified symbol name.
GATE_REGEX = re.compile(
    r"^#assert_no_axioms\s+(?P<symbol>[A-Za-z_][A-Za-z0-9_.?'!]*)",
    flags=re.MULTILINE,
)

# Match `private` modifier so we can detect private declarations.
PRIVATE_REGEX = re.compile(
    r"^private\s+(?:def|theorem|lemma|inductive|structure|class|abbrev)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_.?'!]*)",
    flags=re.MULTILINE,
)


def extract_declarations(file_path: Path) -> list[str]:
    """Return the list of public top-level declaration names."""
    text = file_path.read_text(encoding="utf-8")
    # Strip block comments to avoid matching declarations in docstrings.
    text_no_block_comments = re.sub(
        r"/-(?:[^-]|-(?!/))*-/", "", text, flags=re.DOTALL
    )
    # Strip line comments.
    text_clean = re.sub(r"--[^\n]*", "", text_no_block_comments)
    # Collect all declared names.
    all_decls = [m.group("name") for m in DECL_REGEX.finditer(text_clean)]
    # Subtract private ones.
    private_decls = {m.group("name") for m in PRIVATE_REGEX.finditer(text_clean)}
    return [d for d in all_decls if d not in private_decls]


def extract_gated_symbols(audit_file: Path) -> set[str]:
    """Return the set of fully-qualified symbol names referenced by
    `#assert_no_axioms` gates."""
    text = audit_file.read_text(encoding="utf-8")
    return {m.group("symbol") for m in GATE_REGEX.finditer(text)}


def check_orphan_files() -> int:
    """Scan V2 files; report orphans; return number of orphans."""
    if not V2_DIR.is_dir():
        print(f"ERROR: V2 directory not found at {V2_DIR}", file=sys.stderr)
        return -1
    if not AUDIT_FILE.is_file():
        print(f"ERROR: Audit file not found at {AUDIT_FILE}", file=sys.stderr)
        return -1

    gated_symbols = extract_gated_symbols(AUDIT_FILE)
    orphan_count = 0
    total_files = 0
    files_with_no_decls = 0

    # Only inspect files matching the V2 naming convention.  Files
    # without V2 in their name predate the V2 substrate and are
    # outside this detector's purview.
    v2_files = sorted(
        f for f in V2_DIR.iterdir()
        if f.is_file() and f.suffix == ".lean" and "V2" in f.stem
    )

    for f in v2_files:
        total_files += 1
        decls = extract_declarations(f)
        module_path_parts = f.stem  # e.g. "RawTermV2Subst"
        module_qual = (
            f"LeanFX2.Foundation.PolyCell.Core.{module_path_parts}"
        )

        if not decls:
            files_with_no_decls += 1
            print(f"NO DECLS: {f.name}")
            continue

        # A file is "gated" iff at least one of its declarations
        # appears in the gated_symbols set (matched on the unqualified
        # name as a suffix).
        any_gated = False
        for d in decls:
            # Match in two ways: the bare name OR a fully-qualified
            # match (e.g. NameSpace.decl).
            # We treat decl as gated iff some gate symbol ends with
            # ".<decl>" OR equals "<decl>" exactly.
            for sym in gated_symbols:
                # If the gate is fully qualified, it ends with .<decl>;
                # if bare, it equals <decl>.
                if sym == d or sym.endswith("." + d):
                    any_gated = True
                    break
            if any_gated:
                break

        if any_gated:
            print(f"OK: {f.name} -- {len(decls)} declarations, at least one gated")
        else:
            orphan_count += 1
            print(
                f"ORPHAN: {f.name} -- "
                f"{len(decls)} declarations, 0 gated"
            )

    print()
    print(
        f"V2 audit orphan summary: "
        f"{total_files} V2 files scanned, "
        f"{files_with_no_decls} with no public declarations, "
        f"{orphan_count} orphans"
    )
    return orphan_count


def main() -> int:
    orphan_count = check_orphan_files()
    if orphan_count < 0:
        return 2
    if orphan_count == 0:
        print()
        print("V2 audit-coverage check: GREEN")
        return 0
    print()
    print(f"V2 audit-coverage check: RED ({orphan_count} orphans)")
    return 1


if __name__ == "__main__":
    sys.exit(main())
