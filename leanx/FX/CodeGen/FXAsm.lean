import FX.CodeGen.FXAsm.X86_64
import FX.CodeGen.FXAsm.Arm64
import FX.CodeGen.FXAsm.Rv64
import FX.CodeGen.FXAsm.Mips64

/-!
# FXAsm umbrella — four per-arch emit-table stubs (task H2)

Re-exports the four per-arch assembly IR modules so downstream
callers can `import FX.CodeGen.FXAsm` and reference any
`FX.CodeGen.FXAsm.<Arch>.*` without per-arch imports.

Each arch file contains:

  * `Reg`          — that arch's register set
  * `Insn`         — opcode enum (representative, matching
                     §20.5's atomic tables + core ops)
  * `Insn.name`    — mnemonic string for diagnostics
  * `Instruction`  — opcode + operands + per-arch metadata
  * `emit`         — stub `FXLowOp → List Instruction` that
                     currently returns `[]`

The real emit tables (Phase 7+) will be populated per §20.5's
per-arch tabulation, with the correctness refinement theorem
(120-lemma proof obligation, §20.5 last paragraph)
discharging against each arch's formal memory model per
Appendix G.

**Deferred to Phase 7+ per SPEC.md.**  See each arch file for
arch-specific notes (x86-64 TSO, ARM Flat, RVWMO, MIPS64 RC).
-/
