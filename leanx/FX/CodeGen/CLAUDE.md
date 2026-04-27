# FX.CodeGen — module-local design notes

The Phase-7-deferred code-generation scaffolding.  Three IR
layers between surface FX and target assembly:

  FX  →  FXCore  →  FXLow  →  FXAsm  →  Object

This directory was seeded in tasks H1/H2/H3 with stable op
catalogues and envelope types; **all `emit` functions are
stubs returning `[]`**.  Real lowering/selection/emit work is
Phase 7.  Root project `CLAUDE.md` covers cross-cutting
invariants; this file covers codegen-specific choices.

## "Deferred to Phase 7+" contract

Every file in `FX/CodeGen/**` marks its module-level docstring
with "Deferred to Phase 7+ per SPEC.md".  This is a contract,
not an excuse:

  * Types are fully declared (struct shapes, enum constructors,
    `deriving Repr, Inhabited`) so downstream work has a stable
    referent.
  * `emit : FXLowOp → List Instruction` functions exist with
    the right signature, returning `[]`.
  * Phase 7 populates the function bodies from §20.5 emit
    tables; no signature churn required.
  * The 120-lemma refinement proof (§20.5 final paragraph)
    discharges against each arch's formal memory model per
    Appendix G — that's the Phase 7 body.

Tests in `tests/Tests/CodeGen/*` pin the `emit _ = []` contract
and name-lookup tables.  If a future pass fills in `emit`
bodies, test expectations update — but the shape stays.

## Op-kind enum + envelope struct split

Each IR layer follows the same design:

  * `<Layer>OpKind` — the operation catalogue.  One
    constructor per op per §20.3 / §20.5 bullet.  Pure enum,
    `deriving Repr, DecidableEq, Inhabited`.
  * `<Layer>Op` / `<Layer>Instruction` — the envelope.  Carries
    the op kind plus operand refs, optional result type/width,
    per-layer metadata.

**Why split enum from envelope:** the enum is the INFORMATIVE
content (matches spec text verbatim) and stays stable across
refactors; the envelope captures lowering-specific details
that evolve with the real emit work.  Clients pattern-match
on `kind` for dispatch and access the envelope for operands —
two concerns, two types.

Per-op constructors with full arg signatures were considered
and rejected for stub files: they'd bloat each file to 1000+
lines with spec-uncertain arg shapes that'd need rewriting in
Phase 7 anyway.

## No per-size op constructors in FXLow

Spec §20.3 says FXLow has "~100 operations" — but that count
includes size variants (i8/i16/i32/i64 × add/sub/mul/div).
`FXLowOpKind` covers the ~45 op KINDS; size lives on the
envelope as `FXLowWidth`.

**Why this choice:** per-size constructors explode the enum
(5 widths × 5 int ops = 25 constructors just for integer
arith).  Carrying width as data keeps the enum informative
without combinatorial bloat.  Phase 7 may split to per-size
constructors if the real lowering benefits — but the data-
carrying shape is a fine starting point.

SIMD width/lanes ride on `FXLowWidth.vec laneCount laneWidth`;
the recursive `vec` case handles arbitrary SIMD shapes without
adding enum constructors.

## Arch-specific metadata on dedicated fields

Two per-arch `Instruction` fields carry arch-local data that
doesn't fit the generic register-operand model:

  * **rv64** `fencePred` / `fenceSucc : Option FenceSet` —
    RVWMO FENCE predecessor/successor sets (R / W / RW).
    Per RISC-V ISA Manual Table A.6 and §20.5.5.
  * **mips64** `syncHint : Option SyncHint` — SYNC hint tag
    (fullBarrier=0, wmb=4, syncWrites=13, acquire=16,
    release=17).  Per MIPS64 ISA Manual Vol.2 and §20.5.5.

Non-applicable instructions leave these fields `none`.  The
alternative — folding hints into op-kind constructors — would
mean `fenceR`, `fenceW`, `fenceRw`, `fenceR_W`, … (9
constructors just for FENCE variants).  Data-on-envelope keeps
the enum clean.

Arm64 takes the OPPOSITE choice: each LSE A/L/AL suffix variant
(LDADD, LDADDA, LDADDL, LDADDAL) is a distinct opcode
constructor because each maps to a distinct machine encoding,
the spec table lists them individually, and the pattern-match
dispatch in Phase 7 emits them uniformly.  Both choices are
informed by "what matches the spec table's granularity."

## Lake auto-discovery — no lakefile changes needed

`lakefile.lean` declares `globs := #[.andSubmodules \`FX]`
so every `.lean` file under `FX/` is automatically part of
the `FX` library.  Adding a new CodeGen file requires no
lakefile edit.

Do NOT add explicit file entries to the lakefile — breaks the
"one lakefile, stable shape" invariant and creates a merge-
conflict hotspot for concurrent work.

## Umbrella module pattern

`FX/CodeGen/FXAsm.lean` re-exports all four arch modules.
Downstream callers `import FX.CodeGen.FXAsm` and reference
`FX.CodeGen.FXAsm.<Arch>.*` without per-arch imports.

When adding a 5th arch (e.g. wasm), add the arch file under
`FX/CodeGen/FXAsm/<NewArch>.lean` and an import line to the
umbrella.  The umbrella stays a pure re-export — no shared
definitions live there.

## Name methods — spec-verbatim diagnostics

Every `<Layer>OpKind.name : _ → String` and
`<Arch>Insn.name : _ → String` method matches the spec's
bullet / ISA manual mnemonic VERBATIM:

  * FXCore: "IAdd", "AtomicCAS", "SecureZero" — §20.3 bullet
    names
  * Arm64: "LDADDAL", "DMB ISH" — ARM ARM mnemonic
  * Rv64: "AMOADD.D.AQRL", "FENCE" — RISC-V ISA manual
  * Mips64: "SYNC", "SUBU" — MIPS ISA reference
  * x86-64: "LOCK XADD", "MFENCE" — Intel SDM / AT&T syntax

Consistency matters: `fxi dump --core` and `fxi dump --fxasm`
(future) render these names, and the diagnostic output must
match what a reader sees in the spec / ISA manual.

## Trust status

`FX/CodeGen/**` is UNTRUSTED per the layered SPEC.md §3 trust
story.  Currently trivial (no logic) so trust is a non-issue;
Phase 7's real emit tables will be subject to the 120-lemma
refinement proof obligation (§20.5), which is PROVED work
(lives in `FX/Metatheory/` when it lands).
