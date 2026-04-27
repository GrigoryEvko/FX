import FX.CodeGen.FXLow

/-!
# FXAsm / mips64 — Phase 7+ stub per `fx_design.md` §20.5

Legacy target: MIPS64r2 is available only under profile
`legacy_mips` per §20.5.1 — not a baseline target.  The
MIPS64 ISA predates the modern "atomic RMW as one instruction"
design; every atomic RMW compiles to an LL/SC loop, and fences
use SYNC with hint tags (SYNC 0 = full, SYNC 16 = acquire,
SYNC 17 = release, per §20.5.5).

Memory model: MIPS64r2 Release Consistency with typed SYNC
hints.  Documented in MIPS64 ISA Reference Manual Vol.2.
Weak by default; explicit SYNC before/after each atomic
access is the path to source-level DRF-SC.

## Phase-2 stub scope

  * `Reg` — $0..$31 (integer) + $f0..$f31 (FPU), matching the
    MIPS64r2 register file.
  * `Insn` — LD/SD, LL/SC (the LL/SC pair — no native AMO
    RMW), SYNC with hint values, plus basic ops (ADDU, SUBU,
    MOVE, JAL, JR, RET).
  * `Instruction` + `emit` — same shape as other arches; SYNC
    hint lives in a dedicated field.

**Deferred to Phase 7+ per SPEC.md.**
-/

namespace FX.CodeGen.FXAsm.Mips64

/--
MIPS64r2 register file: 32 integer ($0..$31; $0 is hard-wired
zero, $31 is the link register), 32 FPU ($f0..$f31). -/
inductive Reg : Type where
  -- Integer $0..$31
  | r0  | r1  | r2  | r3  | r4  | r5  | r6  | r7
  | r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15
  | r16 | r17 | r18 | r19 | r20 | r21 | r22 | r23
  | r24 | r25 | r26 | r27 | r28 | r29 | r30 | r31
  -- FPU $f0..$f31
  | f0  | f1  | f2  | f3  | f4  | f5  | f6  | f7
  | f8  | f9  | f10 | f11 | f12 | f13 | f14 | f15
  | f16 | f17 | f18 | f19 | f20 | f21 | f22 | f23
  | f24 | f25 | f26 | f27 | f28 | f29 | f30 | f31
  -- HI / LO — multiplication result registers
  | hi | lo
  deriving Repr, DecidableEq, Inhabited

/--
SYNC hint tags per MIPS64 ISA Reference Manual Vol.2 and
§20.5.5.  The numeric hint encodes barrier type:

  * `fullBarrier` — SYNC 0 (historical name; all access
    types ordered).  Default hint when no specifier given.
  * `wmb` — SYNC 4 (store-store only).
  * `syncWrites` — SYNC 13 (writes synchronised).
  * `acquire` — SYNC 16 (acquire barrier).
  * `release` — SYNC 17 (release barrier).
-/
inductive SyncHint : Type where
  | fullBarrier | wmb | syncWrites | acquire | release
  deriving Repr, DecidableEq, Inhabited

namespace SyncHint

/-- Numeric hint value per the ISA manual. -/
def value : SyncHint → Nat
  | .fullBarrier => 0
  | .wmb         => 4
  | .syncWrites  => 13
  | .acquire     => 16
  | .release     => 17

end SyncHint

/--
MIPS64r2 opcode enum.  No native atomic RMW — every FXLow
atomic RMW compiles to an LL/SC loop by the Phase-7 emit
table. -/
inductive Insn : Type where
  -- Load / store — plain
  | ld  | sd
  | lb  | lh  | lw   | lbu  | lhu  | lwu
  | sb  | sh  | sw
  -- LL/SC pair — §20.5.3 atomic RMW fallback base
  | ll  | lld
  | sc  | scd
  -- SYNC — memory barrier with hint tag
  | sync
  -- Integer arithmetic (unsigned variants — standard choice)
  | addu | subu | multu | divu | modu
  | addi | addiu
  | neg_
  -- Bitwise / shift
  | and_ | or_ | xor_ | nor
  | sll | srl | sra
  | sllv | srlv | srav
  -- Comparison / branches
  | beq  | bne  | blez | bgtz | bltz | bgez
  | slt  | sltu
  -- Move
  | move | mfhi | mflo
  -- Jump / call
  | j | jal | jr | jalr
  deriving Repr, DecidableEq, Inhabited

namespace Insn

/-- Mnemonic per the MIPS ISA reference. -/
def name : Insn → String
  | .ld    => "LD"
  | .sd    => "SD"
  | .lb    => "LB"
  | .lh    => "LH"
  | .lw    => "LW"
  | .lbu   => "LBU"
  | .lhu   => "LHU"
  | .lwu   => "LWU"
  | .sb    => "SB"
  | .sh    => "SH"
  | .sw    => "SW"
  | .ll    => "LL"
  | .lld   => "LLD"
  | .sc    => "SC"
  | .scd   => "SCD"
  | .sync  => "SYNC"
  | .addu  => "ADDU"
  | .subu  => "SUBU"
  | .multu => "MULTU"
  | .divu  => "DIVU"
  | .modu  => "MODU"
  | .addi  => "ADDI"
  | .addiu => "ADDIU"
  | .neg_  => "NEG"
  | .and_  => "AND"
  | .or_   => "OR"
  | .xor_  => "XOR"
  | .nor   => "NOR"
  | .sll   => "SLL"
  | .srl   => "SRL"
  | .sra   => "SRA"
  | .sllv  => "SLLV"
  | .srlv  => "SRLV"
  | .srav  => "SRAV"
  | .beq   => "BEQ"
  | .bne   => "BNE"
  | .blez  => "BLEZ"
  | .bgtz  => "BGTZ"
  | .bltz  => "BLTZ"
  | .bgez  => "BGEZ"
  | .slt   => "SLT"
  | .sltu  => "SLTU"
  | .move  => "MOVE"
  | .mfhi  => "MFHI"
  | .mflo  => "MFLO"
  | .j     => "J"
  | .jal   => "JAL"
  | .jr    => "JR"
  | .jalr  => "JALR"

end Insn

/--
A MIPS64 instruction in context.  SYNC-hint tag lives in a
dedicated field since SYNC's operand is an immediate numeric
hint, not a register. -/
structure Instruction : Type where
  opcode    : Insn
  operands  : List Reg := []
  immediate : Option Int := none
  /-- SYNC hint — only meaningful when `opcode = .sync`. -/
  syncHint  : Option SyncHint := none
  deriving Repr, Inhabited

/--
Emit the mips64 instruction sequence for one FXLow op.
**Phase-2 stub** — returns `[]`; Phase 7 fills per §20.5's
MIPS64 column of the atomic tables and MIPS64 ISA Reference
Manual Vol.2 SYNC / LL-SC semantics. -/
def emit (_op : FX.CodeGen.FXLowOp) : List Instruction :=
  []  -- Phase 7+

end FX.CodeGen.FXAsm.Mips64
