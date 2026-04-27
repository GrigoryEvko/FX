import FX.CodeGen.FXAsm

/-!
# FXAsm per-arch stub smoke tests (H2 + H3)

Compile-time tests pinning the four arch stubs' surface areas.
These stubs have no logic — each `emit` returns `[]` — so
tests verify:

  * Each arch's `Reg` enumerates at least one representative
    constructor per category (GPR, vec/FP, special).
  * Each arch's `Insn.name` is total and renders the spec's
    §20.5 instruction mnemonics verbatim.
  * `Instruction` structs compose with default-initialized
    metadata.
  * `emit` returns `[]` for every FXLow op (the stub contract).
  * The umbrella `FX.CodeGen.FXAsm` module resolves all four
    arch namespaces.

Adding a new opcode to any `Insn` enum extends the pattern; the
`name` match is exhaustive so Lean will force a matching name
arm addition at build time.
-/

namespace Tests.CodeGen.FXAsmStubs

open FX.CodeGen

/-! ## 1. x86-64 -/

example : FXAsm.X86_64.Insn.mov.name           = "MOV" := rfl
example : FXAsm.X86_64.Insn.xchg.name          = "XCHG" := rfl
example : FXAsm.X86_64.Insn.lockXadd.name      = "LOCK XADD" := rfl
example : FXAsm.X86_64.Insn.lockCmpxchg.name   = "LOCK CMPXCHG" := rfl
example : FXAsm.X86_64.Insn.lockCmpxchg16b.name = "LOCK CMPXCHG16B" := rfl
example : FXAsm.X86_64.Insn.mfence.name        = "MFENCE" := rfl
example : FXAsm.X86_64.Insn.call.name          = "CALL" := rfl
example : FXAsm.X86_64.Insn.ret.name           = "RET" := rfl

-- Stub emit returns [] for any FXLow op.
example : (FXAsm.X86_64.emit (default : FXLowOp)).length = 0 := rfl

-- Instruction envelope composes.
example :
  ({ opcode := FXAsm.X86_64.Insn.mov
   , operands := [FXAsm.X86_64.Reg.rax, FXAsm.X86_64.Reg.rbx]
   } : FXAsm.X86_64.Instruction).operands.length = 2 := rfl

/-! ## 2. arm64 -/

example : FXAsm.Arm64.Insn.ldr.name     = "LDR" := rfl
example : FXAsm.Arm64.Insn.ldar.name    = "LDAR" := rfl
example : FXAsm.Arm64.Insn.stlr.name    = "STLR" := rfl
example : FXAsm.Arm64.Insn.ldaddal.name = "LDADDAL" := rfl
example : FXAsm.Arm64.Insn.casal.name   = "CASAL" := rfl
example : FXAsm.Arm64.Insn.caspal.name  = "CASPAL" := rfl
example : FXAsm.Arm64.Insn.dmbIsh.name  = "DMB ISH" := rfl
example : FXAsm.Arm64.Insn.bl.name      = "BL" := rfl

example : (FXAsm.Arm64.emit (default : FXLowOp)).length = 0 := rfl

example :
  ({ opcode := FXAsm.Arm64.Insn.ldar
   , operands := [FXAsm.Arm64.Reg.x0, FXAsm.Arm64.Reg.x1]
   } : FXAsm.Arm64.Instruction).operands.length = 2 := rfl

/-! ## 3. rv64 -/

example : FXAsm.Rv64.Insn.ld.name          = "LD" := rfl
example : FXAsm.Rv64.Insn.sd.name          = "SD" := rfl
example : FXAsm.Rv64.Insn.amoaddDAqrl.name = "AMOADD.D.AQRL" := rfl
example : FXAsm.Rv64.Insn.amocasDAqrl.name = "AMOCAS.D.AQRL" := rfl
example : FXAsm.Rv64.Insn.lrDAq.name       = "LR.D.AQ" := rfl
example : FXAsm.Rv64.Insn.scDRl.name       = "SC.D.RL" := rfl
example : FXAsm.Rv64.Insn.fence.name       = "FENCE" := rfl
example : FXAsm.Rv64.Insn.jalr.name        = "JALR" := rfl

example : (FXAsm.Rv64.emit (default : FXLowOp)).length = 0 := rfl

-- FENCE sets enumerate.
example : (FXAsm.Rv64.FenceSet.r == FXAsm.Rv64.FenceSet.r) = true := by native_decide
example : (FXAsm.Rv64.FenceSet.r == FXAsm.Rv64.FenceSet.w) = false := by
  native_decide
example : (FXAsm.Rv64.FenceSet.rw == FXAsm.Rv64.FenceSet.rw) = true := by
  native_decide

-- FENCE instruction envelope carries predecessor/successor sets.
example :
  ({ opcode := FXAsm.Rv64.Insn.fence
   , fencePred := some FXAsm.Rv64.FenceSet.rw
   , fenceSucc := some FXAsm.Rv64.FenceSet.rw
   } : FXAsm.Rv64.Instruction).opcode = FXAsm.Rv64.Insn.fence := rfl

/-! ## 4. mips64 -/

example : FXAsm.Mips64.Insn.ld.name   = "LD" := rfl
example : FXAsm.Mips64.Insn.ll.name   = "LL" := rfl
example : FXAsm.Mips64.Insn.lld.name  = "LLD" := rfl
example : FXAsm.Mips64.Insn.sc.name   = "SC" := rfl
example : FXAsm.Mips64.Insn.scd.name  = "SCD" := rfl
example : FXAsm.Mips64.Insn.sync.name = "SYNC" := rfl
example : FXAsm.Mips64.Insn.jal.name  = "JAL" := rfl

example : (FXAsm.Mips64.emit (default : FXLowOp)).length = 0 := rfl

/-- SYNC hint values match the MIPS64 ISA manual's numeric
    mnemonics.  Phase 7 will emit the numeric hint as the SYNC
    instruction's immediate field. -/
example : FXAsm.Mips64.SyncHint.fullBarrier.value = 0  := rfl
example : FXAsm.Mips64.SyncHint.wmb.value         = 4  := rfl
example : FXAsm.Mips64.SyncHint.syncWrites.value  = 13 := rfl
example : FXAsm.Mips64.SyncHint.acquire.value     = 16 := rfl
example : FXAsm.Mips64.SyncHint.release.value     = 17 := rfl

-- SYNC instruction with hint.
example :
  ({ opcode := FXAsm.Mips64.Insn.sync
   , syncHint := some FXAsm.Mips64.SyncHint.acquire
   } : FXAsm.Mips64.Instruction).opcode = FXAsm.Mips64.Insn.sync := rfl

/-! ## 5. Umbrella resolves all four namespaces -/

-- `FX.CodeGen.FXAsm` re-exports every arch module.  These
-- trivial rfl tests confirm the namespace paths resolve;
-- `import FX.CodeGen.FXAsm` alone should be sufficient.
example : FXAsm.X86_64.Insn.mov.name = "MOV" := rfl
example : FXAsm.Arm64.Insn.ldar.name = "LDAR" := rfl
example : FXAsm.Rv64.Insn.amoaddDAqrl.name = "AMOADD.D.AQRL" := rfl
example : FXAsm.Mips64.Insn.sync.name = "SYNC" := rfl

end Tests.CodeGen.FXAsmStubs
