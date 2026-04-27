import FX.CodeGen.FXLow

/-!
# FXAsm / x86-64 — Phase 7+ stub per `fx_design.md` §20.5

Third binary IR in the pipeline (per §20.1): FXLow → FXAsm.
At this layer, operations become concrete x86-64 instructions
with concrete (or virtual-to-be-allocated) registers.  The
§20.5 emit tables tabulate which instruction sequence is
produced for each `(FXLow op, ordering, width)` triple on
x86-64's TSO memory model.

## Phase-2 stub scope

  * `Reg` — canonical x86-64 registers (general-purpose + XMM
    vector subset).  The Phase-7 body will either expand this
    to cover every ABI-required register or switch to a
    virtual-register abstraction with later physical-register
    allocation.
  * `Insn` — opcode enum covering the §20.5-mentioned
    instructions (MOV, XCHG, LOCK XADD, LOCK CMPXCHG,
    LOCK CMPXCHG16B, MFENCE) plus a handful of core ops
    (ADD, SUB, CMP, CALL, RET, JMP, JCC) so the stub is
    informative rather than trivial.
  * `Instruction` — one x86-64 instruction: opcode plus
    register operands and an optional immediate.
  * `emit : FXLowOp → List Instruction` — stub returning
    `[]`; the real emit table lands in Phase 7 along with
    the correctness-refinement theorem promised by the U-emit
    axiom (§20.5).

**Memory-model note.** x86-64 is TSO, so most orderings are
"free" at the instruction level: every aligned MOV is atomic,
and LOCK-prefixed RMW is a full fence (simultaneously Acquire,
Release, AcqRel, SeqCst).  The emit table exploits this by
mapping all RMW orderings to the same LOCK XADD / CMPXCHG
sequence — the @Ord tag is consumed by the auto-sync optimizer
(§21.2), not by x86-64's emit output.

**Deferred to Phase 7+ per SPEC.md.**
-/

namespace FX.CodeGen.FXAsm.X86_64

/--
x86-64 register subset covering what §20.5 and common ABI
requirements need.  Phase-2 uses this as a stable referent;
Phase 7 may extend or switch to virtual registers. -/
inductive Reg : Type where
  -- 64-bit general-purpose registers (System V AMD64 ABI order)
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15
  -- RIP (instruction pointer) — used in RIP-relative addressing
  | rip
  -- XMM vector registers (SSE; YMM/ZMM variants deferred)
  | xmm0  | xmm1  | xmm2  | xmm3  | xmm4  | xmm5  | xmm6  | xmm7
  | xmm8  | xmm9  | xmm10 | xmm11 | xmm12 | xmm13 | xmm14 | xmm15
  -- RFLAGS — not a GPR but referenced by JCC-style instructions
  | rflags
  deriving Repr, DecidableEq, Inhabited

/--
x86-64 opcode enum.  Covers §20.5 emit-table instructions plus
a representative core-ops subset.  Phase 7 will extend to
whatever the real lowering uses; new opcodes just add cases
here. -/
inductive Insn : Type where
  -- Data movement
  | mov    -- MOV (register/memory)
  | xchg   -- XCHG (atomic with memory operand; always LOCK-prefixed)
  | movzx  -- MOVZX (zero-extend)
  | movsx  -- MOVSX (sign-extend)
  -- Integer arithmetic
  | add | sub | mul | imul | div | idiv | neg | inc | dec
  -- Bitwise
  | and_ | or_ | xor_ | not_ | shl | shr | sar
  -- Comparison / branches
  | cmp | test
  | jmp | jz | jnz | jl | jle | jg | jge | je | jne
  | call | ret
  -- Stack
  | push | pop
  -- LOCK-prefixed RMW (§20.5.3)
  | lockXadd     -- LOCK XADD [m], r
  | lockCmpxchg  -- LOCK CMPXCHG [m], r  (expected in RAX)
  | lockCmpxchg16b -- LOCK CMPXCHG16B (§20.5.6 double-word)
  | lockAnd | lockOr | lockXor  -- LOCK AND/OR/XOR for fetch_{and,or,xor}
  -- Memory fence (§20.5.5)
  | mfence
  -- SIMD (SSE subset — representative)
  | vaddsd | vaddps
  deriving Repr, DecidableEq, Inhabited

namespace Insn

/-- Diagnostic name matching the Intel SDM / AT&T-syntax
    mnemonic.  LOCK-prefixed variants render as "LOCK XADD"
    etc. per §20.5 tables. -/
def name : Insn → String
  | .mov             => "MOV"
  | .xchg            => "XCHG"
  | .movzx           => "MOVZX"
  | .movsx           => "MOVSX"
  | .add             => "ADD"
  | .sub             => "SUB"
  | .mul             => "MUL"
  | .imul            => "IMUL"
  | .div             => "DIV"
  | .idiv            => "IDIV"
  | .neg             => "NEG"
  | .inc             => "INC"
  | .dec             => "DEC"
  | .and_            => "AND"
  | .or_             => "OR"
  | .xor_            => "XOR"
  | .not_            => "NOT"
  | .shl             => "SHL"
  | .shr             => "SHR"
  | .sar             => "SAR"
  | .cmp             => "CMP"
  | .test            => "TEST"
  | .jmp             => "JMP"
  | .jz              => "JZ"
  | .jnz             => "JNZ"
  | .jl              => "JL"
  | .jle             => "JLE"
  | .jg              => "JG"
  | .jge             => "JGE"
  | .je              => "JE"
  | .jne             => "JNE"
  | .call            => "CALL"
  | .ret             => "RET"
  | .push            => "PUSH"
  | .pop             => "POP"
  | .lockXadd        => "LOCK XADD"
  | .lockCmpxchg     => "LOCK CMPXCHG"
  | .lockCmpxchg16b  => "LOCK CMPXCHG16B"
  | .lockAnd         => "LOCK AND"
  | .lockOr          => "LOCK OR"
  | .lockXor         => "LOCK XOR"
  | .mfence          => "MFENCE"
  | .vaddsd          => "VADDSD"
  | .vaddps          => "VADDPS"

end Insn

/--
An x86-64 instruction in context: the opcode plus its operand
registers.  Phase-2 leaves immediates and memory operands
coarse (no per-mode breakdown) — Phase 7 refines as needed. -/
structure Instruction : Type where
  opcode   : Insn
  operands : List Reg := []
  /-- Literal immediate value, when the opcode takes one
      (e.g. `MOV rax, 42` has `immediate := some 42`). -/
  immediate : Option Int := none
  deriving Repr, Inhabited

/--
Emit the x86-64 instruction sequence for one FXLow op.
**Phase-2 stub** — returns `[]` in every case.  Phase 7 will
fill in each case per the §20.5 emit tables, with the
correctness-refinement theorem discharging against x86-TSO
per Appendix G.1. -/
def emit (_op : FX.CodeGen.FXLowOp) : List Instruction :=
  []  -- Phase 7+

end FX.CodeGen.FXAsm.X86_64
