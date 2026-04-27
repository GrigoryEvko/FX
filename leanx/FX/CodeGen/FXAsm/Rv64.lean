import FX.CodeGen.FXLow

/-!
# FXAsm / rv64 — Phase 7+ stub per `fx_design.md` §20.5

RV64GC + Zaamo is the baseline target per §20.5.1.  Zaamo
(reorganization of atomic memory operations, 2023) provides
native AMO{ADD,SWAP,XOR,OR,AND} with .AQ/.RL/.AQRL suffixes
for Acquire/Release/AcqRel.  Zacas (single-instruction
compare-and-swap, 2024) is an optional extension; baseline
falls back to LR.D/SC.D loops for CAS.  Zabha (byte/half-word
atomics, 2024) is optional; baseline uses mask-CAS for 1/2
byte atomics.

Memory model: RVWMO (RISC-V Weak Memory Ordering), axiomatic
release-consistency.  FENCE with predecessor/successor sets
(R,R / R,W / R,RW / W,R / W,W / W,RW / RW,R / RW,W / RW,RW)
encodes ordering requirements per §20.5.2-§20.5.5 and RISC-V
ISA Manual Table A.6.

## Phase-2 stub scope

  * `Reg` — x0..x31 (x0 is hard-wired zero), f0..f31.
  * `Insn` — load/store at each ordering (LD, LD+FENCE,
    LR.D/SC.D, AMOADD/AMOSWAP/AMOCAS with suffix variants),
    FENCE with predecessor/successor sets, plus basic ops
    (ADD/SUB/MV/JAL/JALR/BNE).  No full ISA coverage — just
    what §20.5 refers to plus enough core ops to not be
    misleading.
  * `Instruction` + `emit` — same shape as other arches.

**Deferred to Phase 7+ per SPEC.md.**
-/

namespace FX.CodeGen.FXAsm.Rv64

/--
RV64 register file: 32 integer x0..x31 (x0 = zero), 32
floating-point f0..f31.  ABI names (ra, sp, gp, tp, t0..t6,
s0..s11, a0..a7) are typically preferred in emitted assembly
text; this stub uses the numeric form for simplicity and adds
an `abi` method later if needed. -/
inductive Reg : Type where
  -- Integer registers x0..x31 (x0 is hard-wired zero)
  | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7
  | x8 | x9 | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x18 | x19 | x20 | x21 | x22 | x23
  | x24 | x25 | x26 | x27 | x28 | x29 | x30 | x31
  -- FP registers f0..f31 (representative subset)
  | f0  | f1  | f2  | f3  | f4  | f5  | f6  | f7
  | f8  | f9  | f10 | f11 | f12 | f13 | f14 | f15
  | f16 | f17 | f18 | f19 | f20 | f21 | f22 | f23
  | f24 | f25 | f26 | f27 | f28 | f29 | f30 | f31
  deriving Repr, DecidableEq, Inhabited

/--
RVWMO fence predecessor/successor sets.  Encodes which prior
and subsequent memory accesses the FENCE synchronises against,
per RISC-V ISA Manual §A.6. -/
inductive FenceSet : Type where
  /-- R — loads only. -/
  | r
  /-- W — stores only. -/
  | w
  /-- RW — loads and stores. -/
  | rw
  deriving Repr, DecidableEq, Inhabited

/--
RV64 opcode enum.  AMO variants carry ordering as a suffix
(.AQ/.RL/.AQRL); each combination is a distinct constructor
since each maps to a distinct machine encoding. -/
inductive Insn : Type where
  -- Load / store — plain
  | ld      -- LD (64-bit load)
  | sd      -- SD (64-bit store)
  | lb | lh | lw
  | sb | sh | sw
  -- LR/SC — load-reserved / store-conditional (LL/SC pair)
  | lrD   | lrDAq     -- LR.D / LR.D.AQ
  | scD   | scDRl     -- SC.D / SC.D.RL
  -- AMO atomic ops (Zaamo) — §20.5.3
  | amoaddD  | amoaddDAq  | amoaddDRl  | amoaddDAqrl
  | amoswapD | amoswapDAq | amoswapDRl | amoswapDAqrl
  | amoandD  | amoandDAq  | amoandDRl  | amoandDAqrl
  | amoorD   | amoorDAq   | amoorDRl   | amoorDAqrl
  | amoxorD  | amoxorDAq  | amoxorDRl  | amoxorDAqrl
  -- AMOCAS (Zacas extension) — §20.5.4
  | amocasD  | amocasDAq  | amocasDRl  | amocasDAqrl
  -- Fences — §20.5.5 (predecessor/successor sets carried on
  -- the Instruction envelope's metadata in a real emit table;
  -- stub just has a single fence opcode).
  | fence
  -- Integer arithmetic / logic
  | addi | add | sub | mv | neg
  | andi | ori  | xori
  | slli | srli | srai | sll | srl | sra
  -- Comparison / branches
  | beq | bne | blt | bge | bltu | bgeu
  -- Jump / call
  | jal | jalr | ret
  deriving Repr, DecidableEq, Inhabited

namespace Insn

/-- Mnemonic matching the RISC-V ISA Manual's assembly syntax.
    Suffixed AMO variants render as e.g. "AMOADD.D.AQRL". -/
def name : Insn → String
  | .ld            => "LD"
  | .sd            => "SD"
  | .lb            => "LB"
  | .lh            => "LH"
  | .lw            => "LW"
  | .sb            => "SB"
  | .sh            => "SH"
  | .sw            => "SW"
  | .lrD           => "LR.D"
  | .lrDAq         => "LR.D.AQ"
  | .scD           => "SC.D"
  | .scDRl         => "SC.D.RL"
  | .amoaddD       => "AMOADD.D"
  | .amoaddDAq     => "AMOADD.D.AQ"
  | .amoaddDRl     => "AMOADD.D.RL"
  | .amoaddDAqrl   => "AMOADD.D.AQRL"
  | .amoswapD      => "AMOSWAP.D"
  | .amoswapDAq    => "AMOSWAP.D.AQ"
  | .amoswapDRl    => "AMOSWAP.D.RL"
  | .amoswapDAqrl  => "AMOSWAP.D.AQRL"
  | .amoandD       => "AMOAND.D"
  | .amoandDAq     => "AMOAND.D.AQ"
  | .amoandDRl     => "AMOAND.D.RL"
  | .amoandDAqrl   => "AMOAND.D.AQRL"
  | .amoorD        => "AMOOR.D"
  | .amoorDAq      => "AMOOR.D.AQ"
  | .amoorDRl      => "AMOOR.D.RL"
  | .amoorDAqrl    => "AMOOR.D.AQRL"
  | .amoxorD       => "AMOXOR.D"
  | .amoxorDAq     => "AMOXOR.D.AQ"
  | .amoxorDRl     => "AMOXOR.D.RL"
  | .amoxorDAqrl   => "AMOXOR.D.AQRL"
  | .amocasD       => "AMOCAS.D"
  | .amocasDAq     => "AMOCAS.D.AQ"
  | .amocasDRl     => "AMOCAS.D.RL"
  | .amocasDAqrl   => "AMOCAS.D.AQRL"
  | .fence         => "FENCE"
  | .addi          => "ADDI"
  | .add           => "ADD"
  | .sub           => "SUB"
  | .mv            => "MV"
  | .neg           => "NEG"
  | .andi          => "ANDI"
  | .ori           => "ORI"
  | .xori          => "XORI"
  | .slli          => "SLLI"
  | .srli          => "SRLI"
  | .srai          => "SRAI"
  | .sll           => "SLL"
  | .srl           => "SRL"
  | .sra           => "SRA"
  | .beq           => "BEQ"
  | .bne           => "BNE"
  | .blt           => "BLT"
  | .bge           => "BGE"
  | .bltu          => "BLTU"
  | .bgeu          => "BGEU"
  | .jal           => "JAL"
  | .jalr          => "JALR"
  | .ret           => "RET"

end Insn

/--
An rv64 instruction in context.  FENCE-specific
predecessor/successor sets are carried on dedicated fields
since they don't fit the generic register-operand model. -/
structure Instruction : Type where
  opcode       : Insn
  operands     : List Reg := []
  immediate    : Option Int := none
  /-- FENCE predecessor set (RW / R / W).  Only meaningful when
      `opcode = .fence`; otherwise `none`. -/
  fencePred : Option FenceSet := none
  /-- FENCE successor set (RW / R / W).  Only meaningful when
      `opcode = .fence`; otherwise `none`. -/
  fenceSucc : Option FenceSet := none
  deriving Repr, Inhabited

/--
Emit the rv64 instruction sequence for one FXLow op.
**Phase-2 stub** — returns `[]`; Phase 7 fills per §20.5.2-§20.5.5
and RISC-V ISA Manual Table A.6 mappings. -/
def emit (_op : FX.CodeGen.FXLowOp) : List Instruction :=
  []  -- Phase 7+

end FX.CodeGen.FXAsm.Rv64
