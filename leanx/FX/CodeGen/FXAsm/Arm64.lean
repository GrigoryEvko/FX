import FX.CodeGen.FXLow

/-!
# FXAsm / arm64 — Phase 7+ stub per `fx_design.md` §20.5

ARMv8.1-A with the Large System Extensions (LSE) is the
baseline target for FX's arm64 emit tables.  LSE adds
single-instruction atomic RMWs (LDADD, SWP, CAS, CASP)
encoded with A/L/AL suffixes for Acquire/Release/AcqRel
ordering — no DMB needed inside the RMW.  Pre-LSE ARMv8.0
is available only under profile `embedded_arm64` with
explicit opt-in (§20.5.1).

Memory model: ARM Flat (Pulte et al. POPL 2018).  Multi-copy
atomic; weak memory requires explicit LDAR/STLR for
Acquire/Release (RCsc) or DMB ISH for full barriers.  Per
§20.5.2, LDAR suffices for SeqCst loads — it participates in
a multi-copy-atomic ordering across cores.

## Phase-2 stub scope

  * `Reg` — x0..x30, SP, XZR plus V0..V31 (NEON), matching the
    ARMv8 GPR + vector register file.
  * `Insn` — LDR/STR + LDAR/STLR load-acquire/store-release,
    the LSE atomic RMW family, CAS variants, DMB fence
    variants, LDP/STXP/CASP for double-word atomics (§20.5.6),
    plus MOV/ADD/SUB/CMP/B/BL/RET for basic ops.
  * `Instruction` — opcode plus operand registers; the AL/A/L
    suffix encoding is carried on the opcode enum directly.
  * `emit : FXLowOp → List Instruction` — stub returning `[]`.

**Deferred to Phase 7+ per SPEC.md.**
-/

namespace FX.CodeGen.FXAsm.Arm64

/--
ARMv8 register file: 32 general-purpose (x0..x30 + XZR), SP,
32 vector registers (NEON V0..V31).  PC is not directly
addressable in ARMv8 (unlike RIP-relative on x86-64) so it is
not included here; branches use BL/RET which manipulate LR
(x30) implicitly. -/
inductive Reg : Type where
  -- General-purpose 64-bit: x0..x30
  | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7
  | x8 | x9 | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x18 | x19 | x20 | x21 | x22 | x23
  | x24 | x25 | x26 | x27 | x28 | x29 | x30
  -- Stack pointer / zero register
  | sp  | xzr
  -- NEON/SIMD vector registers V0..V31
  | v0  | v1  | v2  | v3  | v4  | v5  | v6  | v7
  | v8  | v9  | v10 | v11 | v12 | v13 | v14 | v15
  | v16 | v17 | v18 | v19 | v20 | v21 | v22 | v23
  | v24 | v25 | v26 | v27 | v28 | v29 | v30 | v31
  -- Condition flags register — not directly named in ARMv8
  -- but produced/consumed by CMP/CSEL family
  | nzcv
  deriving Repr, DecidableEq, Inhabited

/--
ARMv8.1-A opcode enum.  Acquire/Release/AcqRel-suffixed
variants of the LSE atomics (LDADDA, LDADDL, LDADDAL, etc.)
are distinct constructors since each maps to a distinct
encoding per the ISA manual. -/
inductive Insn : Type where
  -- Data movement
  | mov | mvn
  -- Load / store — plain
  | ldr | str
  -- Load-acquire / store-release (RCsc, §20.5.2)
  | ldar | stlr
  -- Load-acquire PC-ordering (ARMv8.3+, RCpc) — weaker variant
  | ldapr
  -- LSE atomic load-op family: base, A (acquire), L (release),
  -- AL (acq+rel).  §20.5.3 maps these to FXLow atomic RMW at
  -- each ordering.
  | ldadd | ldadda | ldaddl | ldaddal
  | ldclr | ldclra | ldclrl | ldclral  -- and-with-inverted
  | ldset | ldseta | ldsetl | ldsetal  -- or
  | ldeor | ldeora | ldeorl | ldeoral  -- xor
  -- Atomic swap
  | swp | swpa | swpl | swpal
  -- Compare-and-swap — §20.5.4
  | cas | casa | casl | casal
  -- Compare-and-swap pair (128-bit double-word, §20.5.6)
  | casp | caspa | caspl | caspal
  -- LL/SC fallback for pre-LSE ARMv8.0 (emit only on that profile)
  | ldxr  | ldxra | ldxp
  | stxr  | stxrl | stxp
  -- Data memory barriers — §20.5.5
  | dmbIshld  -- DMB ISHLD (load-load + load-store)
  | dmbIshst  -- DMB ISHST (store-store)
  | dmbIsh    -- DMB ISH (full, inner shareable)
  -- Integer arithmetic
  | add | sub | mul | neg | cmp
  -- Bitwise / shift
  | and_ | orr | eor | lsl | lsr | asr
  -- Control flow
  | b | bl | ret | cbz | cbnz
  -- NEON / SIMD (representative)
  | addVec | subVec | mulVec
  deriving Repr, DecidableEq, Inhabited

namespace Insn

/-- Diagnostic name matching the ARM ARM reference manual
    mnemonic in all-caps.  Suffixed variants render as a
    single token (e.g. "LDADDAL"). -/
def name : Insn → String
  | .mov      => "MOV"
  | .mvn      => "MVN"
  | .ldr      => "LDR"
  | .str      => "STR"
  | .ldar     => "LDAR"
  | .stlr     => "STLR"
  | .ldapr    => "LDAPR"
  | .ldadd    => "LDADD"
  | .ldadda   => "LDADDA"
  | .ldaddl   => "LDADDL"
  | .ldaddal  => "LDADDAL"
  | .ldclr    => "LDCLR"
  | .ldclra   => "LDCLRA"
  | .ldclrl   => "LDCLRL"
  | .ldclral  => "LDCLRAL"
  | .ldset    => "LDSET"
  | .ldseta   => "LDSETA"
  | .ldsetl   => "LDSETL"
  | .ldsetal  => "LDSETAL"
  | .ldeor    => "LDEOR"
  | .ldeora   => "LDEORA"
  | .ldeorl   => "LDEORL"
  | .ldeoral  => "LDEORAL"
  | .swp      => "SWP"
  | .swpa     => "SWPA"
  | .swpl     => "SWPL"
  | .swpal    => "SWPAL"
  | .cas      => "CAS"
  | .casa     => "CASA"
  | .casl     => "CASL"
  | .casal    => "CASAL"
  | .casp     => "CASP"
  | .caspa    => "CASPA"
  | .caspl    => "CASPL"
  | .caspal   => "CASPAL"
  | .ldxr     => "LDXR"
  | .ldxra    => "LDXRA"
  | .ldxp     => "LDXP"
  | .stxr     => "STXR"
  | .stxrl    => "STXRL"
  | .stxp     => "STXP"
  | .dmbIshld => "DMB ISHLD"
  | .dmbIshst => "DMB ISHST"
  | .dmbIsh   => "DMB ISH"
  | .add      => "ADD"
  | .sub      => "SUB"
  | .mul      => "MUL"
  | .neg      => "NEG"
  | .cmp      => "CMP"
  | .and_     => "AND"
  | .orr      => "ORR"
  | .eor      => "EOR"
  | .lsl      => "LSL"
  | .lsr      => "LSR"
  | .asr      => "ASR"
  | .b        => "B"
  | .bl       => "BL"
  | .ret      => "RET"
  | .cbz      => "CBZ"
  | .cbnz     => "CBNZ"
  | .addVec   => "ADD (vec)"
  | .subVec   => "SUB (vec)"
  | .mulVec   => "MUL (vec)"

end Insn

/--
An arm64 instruction in context. -/
structure Instruction : Type where
  opcode    : Insn
  operands  : List Reg := []
  immediate : Option Int := none
  deriving Repr, Inhabited

/--
Emit the arm64 instruction sequence for one FXLow op.
**Phase-2 stub** — returns `[]`; Phase 7 fills per §20.5.2-§20.5.6. -/
def emit (_op : FX.CodeGen.FXLowOp) : List Instruction :=
  []  -- Phase 7+

end FX.CodeGen.FXAsm.Arm64
