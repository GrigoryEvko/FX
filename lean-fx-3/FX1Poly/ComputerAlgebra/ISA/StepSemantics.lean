import FX1Poly.ComputerAlgebra.ISA.ArchState
import FX1Poly.ComputerAlgebra.ISA.StepRefinement

/-! # StepSemantics — the golden-reference ISA: decode + execute + step (fx_design.md §18.12)

A small, total, zero-axiom instruction-set architecture over the shipped `BitVec`
floor.  Word width 32, register-selector width 5 (`2^5 = 32` registers), addresses
32-bit.  This is the §18.12 "ISA is a `Tot` function over architectural state" golden
reference:

  step = execute . decode . fetch

Totality is DEFINITIONAL: `decode` is a `Nat`-opcode dispatch with a total catch-all,
`execute` is an exhaustive match over the instruction constructors, and every leaf is a
shipped total op (`extractField`, `bitVecSignExtend`, `bitVecAdd`, functional-override
`ite` under the axiom-clean `DecidableEq (BitVec _)`).  No recursion, no `partial`, no
fuel, no `WellFounded.fix`.

This is a SPEC/PROOF substrate — memory and registers are total mathematical maps over
all `2^k` slots (the golden-reference `Tot` shape), NOT a runtime-efficient machine.
Do not `#eval` large runs; the proof-grade division corpus makes concrete evaluation
expensive.  `Init`-only, structural, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-- The concrete RV-flavoured architectural state: 32-bit words, 32-bit addresses,
5-bit register selectors (32 registers). -/
abbrev IsaState : Type := ArchState 32 32 5

/-! ## The instruction set -/

/-- The demonstrator instruction set.  The `invalid` arm makes `decode` total without a
partial function: an unrecognised opcode is given DEFINED behaviour (advance PC). -/
inductive Instruction where
  /-- `rd := rs1 + rs2` (modular add datapath). -/
  | addReg   (rd rs1 rs2 : BitVec 5)
  /-- `rd := imm` (sign-extended 13-bit immediate). -/
  | loadImm  (rd : BitVec 5) (imm : BitVec 32)
  /-- `rd := mem[rs1 + offset]`. -/
  | load     (rd rs1 : BitVec 5) (offset : BitVec 32)
  /-- `mem[rs1 + offset] := rs2`. -/
  | store    (rs2 rs1 : BitVec 5) (offset : BitVec 32)
  /-- `if rs1 = rs2 then pc += offset else pc += 1`. -/
  | branchEq (rs1 rs2 : BitVec 5) (offset : BitVec 32)
  /-- `pc += offset` (unconditional PC-relative jump). -/
  | jump     (offset : BitVec 32)
  /-- Unrecognised opcode: defined as a PC advance. -/
  | invalid  (raw : BitVec 32)

/-! ## Instruction field layout (LSB-first, 32-bit encoding) -/

/-- Opcode field: bits `[0, 4)` — room for 16 opcodes, 6 used. -/
def opcodeField : FieldSpec := ⟨0, 4⟩
/-- Destination register: bits `[4, 9)`. -/
def rdField : FieldSpec := ⟨4, 5⟩
/-- First source register: bits `[9, 14)`. -/
def rs1Field : FieldSpec := ⟨9, 5⟩
/-- Second source register: bits `[14, 19)`. -/
def rs2Field : FieldSpec := ⟨14, 5⟩
/-- Immediate / offset: bits `[19, 32)` — a 13-bit sign-extended field. -/
def immField : FieldSpec := ⟨19, 13⟩

/-! ## decode — via the register `extractField`, structurally total -/

/-- Decode a 32-bit word into an `Instruction`.  Opcode dispatch is an `if`-chain over
`Nat` equality (`Nat.decEq`, axiom-clean) rather than a numeric-literal match, so no
match-compiler propext appears.  The final `else` is the total catch-all. -/
def decode (word : BitVec 32) : Instruction :=
  let opcode : Nat      := (extractField word opcodeField).toNat
  let rd     : BitVec 5 := extractField word rdField
  let rs1    : BitVec 5 := extractField word rs1Field
  let rs2    : BitVec 5 := extractField word rs2Field
  let imm    : BitVec 32 := bitVecSignExtend (extractField word immField) 32
  if opcode = 0 then Instruction.addReg rd rs1 rs2
  else if opcode = 1 then Instruction.loadImm rd imm
  else if opcode = 2 then Instruction.load rd rs1 imm
  else if opcode = 3 then Instruction.store rs2 rs1 imm
  else if opcode = 4 then Instruction.branchEq rs1 rs2 imm
  else if opcode = 5 then Instruction.jump imm
  else Instruction.invalid word

/-! ## execute — total per-instruction semantics, each advancing PC -/

/-- Execute one decoded instruction against the architectural state.  Exhaustive match
over the seven constructors; every arm is total.  Address arithmetic, the add datapath,
and PC-relative control all reuse the modular `bitVecAdd` (`overflow(wrap)`, the correct
hardware wrap); the branch test reuses `DecidableEq (BitVec 32)`. -/
def execute : Instruction → IsaState → IsaState
  | .addReg rd rs1 rs2, state =>
      (state.writeReg rd (bitVecAdd (state.readReg rs1) (state.readReg rs2))).advancePc
  | .loadImm rd imm, state =>
      (state.writeReg rd imm).advancePc
  | .load rd rs1 offset, state =>
      (state.writeReg rd (state.readMem (bitVecAdd (state.readReg rs1) offset))).advancePc
  | .store rs2 rs1 offset, state =>
      (state.writeMem (bitVecAdd (state.readReg rs1) offset) (state.readReg rs2)).advancePc
  | .branchEq rs1 rs2 offset, state =>
      if state.readReg rs1 = state.readReg rs2 then
        state.setPc (bitVecAdd state.pc offset)
      else state.advancePc
  | .jump offset, state =>
      state.setPc (bitVecAdd state.pc offset)
  | .invalid _, state =>
      state.advancePc

/-! ## step = execute . decode . fetch -/

/-- One golden-reference machine step: fetch the word at PC, decode it, execute it. -/
def step (state : IsaState) : IsaState :=
  execute (decode state.fetch) state

/-! ## Bonus correctness theorems (each a shipped-lemma / `rfl` corollary) -/

/-- After `addReg`, the destination register holds the sum (the write survives the PC
advance, which touches only `pc`). -/
theorem execute_addReg_readReg (state : IsaState) (rd rs1 rs2 : BitVec 5) :
    (execute (.addReg rd rs1 rs2) state).readReg rd
      = bitVecAdd (state.readReg rs1) (state.readReg rs2) :=
  ArchState.readReg_writeReg_same state rd (bitVecAdd (state.readReg rs1) (state.readReg rs2))

/-- After `loadImm`, the destination register holds the immediate. -/
theorem execute_loadImm_readReg (state : IsaState) (rd : BitVec 5) (imm : BitVec 32) :
    (execute (.loadImm rd imm) state).readReg rd = imm :=
  ArchState.readReg_writeReg_same state rd imm

/-- `loadImm` does not disturb any register other than the destination. -/
theorem execute_loadImm_readReg_other (state : IsaState) (rd probe : BitVec 5)
    (imm : BitVec 32) (distinct : probe ≠ rd) :
    (execute (.loadImm rd imm) state).readReg probe = state.readReg probe :=
  ArchState.readReg_writeReg_other state rd probe imm distinct

/-- `jump` sets the PC to the PC-relative target. -/
theorem execute_jump_pc (state : IsaState) (offset : BitVec 32) :
    (execute (.jump offset) state).pc = bitVecAdd state.pc offset := rfl

/-- An unrecognised instruction advances the PC and touches nothing else observable in
the register file. -/
theorem execute_invalid_readReg (state : IsaState) (raw : BitVec 32) (idx : BitVec 5) :
    (execute (.invalid raw) state).readReg idx = state.readReg idx := rfl

/-! ## Tie-in to the refinement scaffold: the ISA is its own golden reference -/

/-- The identity forward simulation of the ISA against itself — the non-vacuous witness
that `step` inhabits the `StepRefinement` scaffold. -/
def isaSelfRefinement (init : IsaState) : StepRefinement IsaState IsaState :=
  StepRefinement.identity step init

/-- Every reachable ISA run abstracts to itself (whole-trace correspondence for the
self-refinement) — the §18.12 follow-on that ISA-level properties transport along the
trace. -/
theorem isaSelfRefinement_onAllRuns (init : IsaState) (count : Nat) :
    (isaSelfRefinement init).abstracts
      (iterateStep step count init) (iterateStep step count init) :=
  (isaSelfRefinement init).onAllRuns count

end FX1Poly.ComputerAlgebra
