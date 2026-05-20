#!/usr/bin/env python3
"""Convert PURE single-recursive-def ``simp only [DEF]`` to ``dsimp only [DEF]``.

Why this exists
---------------
``simp only [RawTerm.rename]`` (and the ``Term``/``Ty`` and ``subst``/``weaken``
siblings) unfolds a 78-arm recursive engine through its *propositional* equation
lemmas, producing a giant ``Eq.mpr``/``congrArg`` certificate that the Lean
kernel re-typechecks on every build -- the dominant cold-build cost catalogued
in ``scripts/profile_lean_elab.py``.  ``dsimp only [RawTerm.rename]`` performs
the *identical* iota reduction definitionally, emitting no certificate, so the
per-file kernel recheck collapses.  The swap is axiom-safe: ``dsimp only`` is
pure definitional reduction and cannot introduce ``propext`` / ``Quot.sound``.

Safety boundary (the whole point)
---------------------------------
Only PURE single-def brackets are converted.  Two regex constraints encode the
boundary so a mechanical pass never breaks a proof:

1. **Closed bracket** ``[DEF]`` -- the bracket must contain exactly one known
   recursive engine and close immediately.  A MIXED bracket such as
   ``simp only [RawTerm.subst, RawTerm.subst_compose]`` also applies a
   *propositional* helper lemma (``subst_compose`` is an equation, not a
   definitional unfold); ``dsimp only`` physically cannot apply it, so MIXED
   brackets are left untouched (the char after the def name is ``,`` not ``]``,
   so they never match).

2. **Tactic-position anchor** -- the match must begin a line after only
   whitespace and an optional ``·`` bullet.  This skips docstring / comment
   mentions like ``Each case is `simp only [RawTerm.rename]; ...` `` whose
   ``simp`` is preceded by prose.

Residual fallout (expected, handled downstream)
-----------------------------------------------
Even a pure swap can leave a goal the *next* tactic cannot close: ``dsimp only``
hard-errors with "made no progress" where ``simp only`` silently no-op'd, or a
goal ``simp only`` closed by an internal ``rfl`` is left open.  This script does
NOT try to be clever about that -- it does the textual swap, you rebuild, and
fix the handful of fallout sites (revert that one line to ``simp only`` or drop
a redundant call).  The swaps are git-tracked, so reverting a whole file is
``git checkout`` if a file is unsalvageable.

Usage
-----
    python3 scripts/dsimp_pure_swap.py <file.lean> [<file.lean> ...]   # dry-run
    python3 scripts/dsimp_pure_swap.py --apply <file.lean> ...         # write
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

# Every name that reduces DEFINITIONALLY (by iota / delta on a `def`), so
# `dsimp only [NAME]` does the same work `simp only [NAME]` did with no
# kernel-rechecked certificate.  All entries verified to be `def` (not
# `theorem`): the 78-arm recursive engines, their PolyTerm/Ty siblings, the
# conversion functions, and the structural Option helpers.  A bracket is
# convertible iff EVERY comma-separated entry is in this set -- which auto-
# excludes (a) propositional rewrite *theorems* like
# `RawTerm.weaken_rename_commute` that dsimp physically cannot apply, and (b)
# brackets carrying a local hypothesis `h` (e.g. `simp only [Term.isWHNF, h]`,
# whose `; rfl` tail needs a different 2-tactic transform).
ALLOWED_DEFINITIONAL: frozenset[str] = frozenset({
    # recursive term engines
    "RawTerm.rename", "RawTerm.subst", "RawTerm.weaken",
    "RawTerm.partialRename?", "RawTerm.partialStrengthen?",
    "Term.rename", "Term.subst", "Term.weaken",
    # type engines
    "Ty.rename", "Ty.subst", "Ty.weaken", "Ty.substHet", "Ty.lift_level",
    # polygraph mirror engines + conversion functions
    "RawPolyTerm.rename", "RawPolyTerm.subst", "RawPolyTerm.toRawTerm",
    "RawTerm.toRawPoly",
    # confluence development function
    "RawTerm.cd", "RawTerm.cdTranspCase",
    # structural Option combinators (plain defs)
    "Option.mapTwo", "Option.mapThree",
})

# A line is eligible iff, after leading whitespace and an optional `·` bullet,
# it begins with `simp only [ ... ]`.  The bracket body is split on commas and
# every element must be in ALLOWED_DEFINITIONAL for the swap to fire.
SIMP_ONLY_LINE = re.compile(
    r'^(?P<lead>\s*(?:·\s+)?)simp only \[(?P<body>[^\]]*)\](?P<rest>.*)$'
)


def convertedLine(sourceLine: str) -> str | None:
    """Return the ``dsimp only`` rewrite of an all-definitional simp line, else ``None``.

    ``None`` means the line is not a tactic-position ``simp only`` whose bracket
    is entirely definitional, so it must be left exactly as-is (a propositional
    rewrite lemma, a local hypothesis, prose, or an unrelated tactic).
    """
    matched = SIMP_ONLY_LINE.match(sourceLine)
    if matched is None:
        return None
    bracketEntries = [entry.strip() for entry in matched.group("body").split(",")]
    if not bracketEntries or any(entry not in ALLOWED_DEFINITIONAL
                                 for entry in bracketEntries):
        return None
    return (
        f"{matched.group('lead')}dsimp only "
        f"[{matched.group('body')}]{matched.group('rest')}"
    )


def rewriteFile(targetPath: Path, shouldApply: bool) -> int:
    """Rewrite one file, returning the count of converted lines.

    A stateful pass that tracks ``/- ... -/`` block-comment nesting depth (Lean
    block comments nest) so a ``simp only [...]`` sitting in the interior of a
    multi-line docstring is never converted -- only lines whose start is outside
    any block comment are eligible.  ``--`` line comments and prose-prefixed
    mentions are already excluded by the tactic-position anchor in
    ``PURE_SIMP_ONLY_LINE``.  In dry-run mode (``shouldApply`` false) the file is
    not touched; a sample of up to three before/after pairs is printed.
    """
    originalLines = targetPath.read_text(encoding="utf-8").splitlines(keepends=True)
    convertedCount = 0
    samplePairs: list[tuple[str, str]] = []
    rewrittenLines: list[str] = []
    blockCommentDepth = 0
    for sourceLine in originalLines:
        trailingNewline = "\n" if sourceLine.endswith("\n") else ""
        bareLine = sourceLine[: -1] if trailingNewline else sourceLine
        depthAtLineStart = blockCommentDepth
        # Update depth for the NEXT line.  `/-` (incl. `/--` docstrings) opens,
        # `-/` closes; net per line gives the carried nesting depth.
        blockCommentDepth = max(0, blockCommentDepth
                                + bareLine.count("/-") - bareLine.count("-/"))
        rewritten = None if depthAtLineStart > 0 else convertedLine(bareLine)
        if rewritten is None:
            rewrittenLines.append(sourceLine)
            continue
        convertedCount += 1
        if len(samplePairs) < 3:
            samplePairs.append((bareLine, rewritten))
        rewrittenLines.append(rewritten + trailingNewline)

    if convertedCount == 0:
        return 0

    print(f"{targetPath}: {convertedCount} pure simp-only -> dsimp only")
    for beforeLine, afterLine in samplePairs:
        print(f"    - {beforeLine.strip()}")
        print(f"    + {afterLine.strip()}")
    if shouldApply:
        targetPath.write_text("".join(rewrittenLines), encoding="utf-8")
    return convertedCount


def main() -> int:
    """Parse arguments, rewrite each file, print the grand total."""
    argumentParser = argparse.ArgumentParser(description=__doc__)
    argumentParser.add_argument(
        "files", nargs="+", type=Path,
        help="`.lean` files to convert (pass explicit paths to control scope)",
    )
    argumentParser.add_argument(
        "--apply", action="store_true",
        help="write changes (default is a dry-run that prints the plan only)",
    )
    parsedArguments = argumentParser.parse_args()

    grandTotal = 0
    for targetPath in parsedArguments.files:
        if not targetPath.is_file():
            print(f"skip (not a file): {targetPath}", file=sys.stderr)
            continue
        grandTotal += rewriteFile(targetPath, parsedArguments.apply)

    verb = "converted" if parsedArguments.apply else "would convert"
    print(f"\nTOTAL: {verb} {grandTotal} pure simp-only sites"
          f"{'' if parsedArguments.apply else ' (dry-run; pass --apply to write)'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
