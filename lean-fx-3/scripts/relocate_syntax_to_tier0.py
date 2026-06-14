#!/usr/bin/env python3
"""Phase 1 of the Tier0 -> Core -> everything-else restructure.

Relocates the pure-syntax substrate (Universe level-algebra + Generator signature
+ RawTerm/cell de Bruijn algebra + the thin Foundation/) DOWN into a single
`FX1Poly/Tier0/Syntax/` directory, and rewrites every consumer's import path.

DECL NAMESPACES ARE PRESERVED (FX1Poly.Core / FX1Poly.Universe / FX1Poly.Foundation):
FX1Poly.Core is shared between moving syntax modules and staying reduction/typing
modules, so a namespace rename is NOT scriptable here — only module PATHS move.
A module at path FX1Poly.Tier0.Syntax.X may freely keep `namespace FX1Poly.Core`,
so consumers need ONLY their `import` line rewritten, not their references.

Idempotent-ish: validates every source exists before moving; aborts on any
coupled-file leak into the move set.
"""

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent          # lean-fx-3/
assert (ROOT / "lakefile.lean").exists(), f"not the repo root: {ROOT}"

# --- the maximal Foundation-eligible cut (agent-1 section 5b), base -> old module ---
UNIVERSE = [
    "LevelExpr", "LevelExprSimplify", "LevelExprSerialize",
    "LevelExprImpredicativeClosure", "LevelNormalizationTableExclusion",
    "UniverseFlag", "UniverseFlagSerialize", "UniverseFlagStrength",
    "UniversePayloadSerialize", "UniverseConfig",
]
GENERATOR = [
    "GeneratorCore", "GeneratorMetadata", "GeneratorSignatureValue",
    "GeneratorAdmission", "GeneratorChildSpecsDim0", "GeneratorCountPin",
    "GeneratorFinitePolygraph", "GeneratorPolygraphMap", "GeneratorTagRoundTrip",
    "GeneratorTotalityClass", "GenPayloadEvidence", "GeneratorRedexHead",
]
RAWTERM_AND_SUPPORT = [
    "RawTerm", "RawTermSubstDefs", "RawTermSubst", "RawTermSubst0",
    "RawTermSubst0Commute", "RawTermSubstAction", "RawTermSubstCompose",
    "RawTermSubstConsCommute", "RawTermSubstIdentity", "RawTermSubstLiftWeaken",
    "RawTermSubstPointwise", "RawTermSubstRenameCommute", "RawTermRename",
    "RawTermRenameCompose", "RawTermRenameComposeFusion", "RawTermRenamePointwise",
    "RawTermRenameSubstCommute", "RawTermWeaken", "RawTermStrengthen",
    "RawTermChildrenUnique", "RawTermFoldNonVarCommute", "RawTermDecEq",
    "Fold", "GenAlgebra", "LiftsRaw",
    "RawCell", "RawCellDecEq", "RawCellCode", "RawSize", "CellSort",
]
# Foundation: base -> old module (nested under RawSubst for two of them)
FOUNDATION = {
    "Action": "FX1Poly.Foundation.Action",
    "RenameDefs": "FX1Poly.Foundation.RawSubst.RenameDefs",
    "ActionInstances": "FX1Poly.Foundation.RawSubst.ActionInstances",
}

# Must NEVER appear in the move set (coupled to PolyProfile stack or to Step / NbE).
EXCLUDE = {
    "RawTermFresh", "RawTermFreeVars", "RawTermNF", "RawTermOccurrenceRename",
    "RawTermOccurrenceSubst", "RawTermOccurrenceSubstLift", "RawTermSubstPair",
    "RawTermRenameAsSubst", "RawTermRenameInjective",
    "GeneratorRedexHeadSoundness", "LevelExprComplexity",
}

# Build base -> old_module map.
old_module = {}
for b in UNIVERSE:
    old_module[b] = f"FX1Poly.Universe.{b}"
for b in GENERATOR + RAWTERM_AND_SUPPORT:
    old_module[b] = f"FX1Poly.Core.{b}"
old_module.update(FOUNDATION)

# --- guardrails ---
leaked = EXCLUDE & set(old_module)
if leaked:
    sys.exit(f"ABORT: coupled files leaked into the move set: {sorted(leaked)}")

def module_to_path(mod: str) -> Path:
    return ROOT / (mod.replace(".", "/") + ".lean")

old_path = {}
missing = []
for b, mod in old_module.items():
    p = module_to_path(mod)
    old_path[b] = p
    if not p.exists():
        missing.append((b, str(p.relative_to(ROOT))))
if missing:
    for b, p in missing:
        print(f"  MISSING: {b}  ->  {p}")
    sys.exit(f"ABORT: {len(missing)} source file(s) not found; fix the cut list.")

new_module = {b: f"FX1Poly.Tier0.Syntax.{b}" for b in old_module}
SYNTAX_DIR = ROOT / "FX1Poly" / "Tier0" / "Syntax"
SYNTAX_DIR.mkdir(parents=True, exist_ok=True)

# --- 1. git mv each module into Tier0/Syntax/<base>.lean ---
print(f"Moving {len(old_module)} modules into FX1Poly/Tier0/Syntax/ ...")
for b in old_module:
    src = old_path[b].relative_to(ROOT)
    dst = (SYNTAX_DIR / f"{b}.lean").relative_to(ROOT)
    r = subprocess.run(["git", "mv", str(src), str(dst)], cwd=ROOT,
                       capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"ABORT: git mv {src} -> {dst} failed:\n{r.stderr}")
print(f"  moved {len(old_module)} files.")

# --- 2. rewrite import lines across the whole tree (exact full-line match) ---
import_rename = {f"import {old_module[b]}": f"import {new_module[b]}" for b in old_module}
changed_files = 0
changed_lines = 0
for libdir in ("FX1Poly", "FX1PolyAudit", "FX0Poly"):
    for f in (ROOT / libdir).rglob("*.lean"):
        text = f.read_text()
        lines = text.split("\n")
        out = []
        touched = False
        for ln in lines:
            key = ln.rstrip()
            if key in import_rename:
                out.append(import_rename[key])
                touched = True
                changed_lines += 1
            else:
                out.append(ln)
        if touched:
            f.write_text("\n".join(out))
            changed_files += 1
print(f"  rewrote {changed_lines} import lines across {changed_files} files.")
print("DONE. Phase 1 relocation complete (namespaces preserved).")
