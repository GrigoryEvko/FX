import FX1Poly.ComputerAlgebra.ISA.ArchState
import FX1Poly.ComputerAlgebra.ISA.StepRefinement

/-! # StepSemantics: golden-reference ISA — decode, execute, step (fx_design.md §18.12)

A small total zero-axiom instruction-set architecture over the `BitVec` floor:
32-bit words, 5-bit register selectors (`2^5 = 32` registers), 32-bit addresses.
The §18.12 golden reference `step = execute ∘ decode ∘ fetch` is total by
construction — `decode` an `if`-chain with a total catch-all, `execute` an
exhaustive constructor match, every leaf a total op under `DecidableEq (BitVec _)`;
no recursion, `partial`, fuel, or `WellFounded.fix`.  Registers and memory are total
maps over all `2^k` slots.  `Init`-only, structural, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-- The concrete ISA state, `ArchState 32 32 5`. -/
abbrev IsaState : Type := ArchState 32 32 5

/-! ## Instruction set -/

/-- The `invalid` arm makes `decode` total: an unrecognised opcode is a PC advance. -/
inductive Instruction where
  /-- `rd := rs1 + rs2`. -/
  | addReg   (rd rs1 rs2 : BitVec 5)
  /-- `rd := imm` (13-bit sign-extended immediate). -/
  | loadImm  (rd : BitVec 5) (imm : BitVec 32)
  /-- `rd := mem[rs1 + offset]`. -/
  | load     (rd rs1 : BitVec 5) (offset : BitVec 32)
  /-- `mem[rs1 + offset] := rs2`. -/
  | store    (rs2 rs1 : BitVec 5) (offset : BitVec 32)
  /-- `if rs1 = rs2 then pc += offset else pc += 1`. -/
  | branchEq (rs1 rs2 : BitVec 5) (offset : BitVec 32)
  /-- `pc += offset` (PC-relative jump). -/
  | jump     (offset : BitVec 32)
  /-- Unrecognised opcode: a PC advance. -/
  | invalid  (raw : BitVec 32)

/-! ## Field layout (LSB-first, 32-bit encoding) -/

/-- Opcode: bits `[0, 4)`. -/
def opcodeField : FieldSpec := ⟨0, 4⟩
/-- Destination register: bits `[4, 9)`. -/
def rdField : FieldSpec := ⟨4, 5⟩
/-- First source register: bits `[9, 14)`. -/
def rs1Field : FieldSpec := ⟨9, 5⟩
/-- Second source register: bits `[14, 19)`. -/
def rs2Field : FieldSpec := ⟨14, 5⟩
/-- Immediate / offset: bits `[19, 32)`, sign-extended. -/
def immField : FieldSpec := ⟨19, 13⟩

/-! ## decode -/

/-- Decode a 32-bit word: an `if`-chain over `Nat.decEq` (avoiding match-compiler
propext), with a total final `else`. -/
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

/-! ## execute -/

/-- Execute one decoded instruction: an exhaustive total match.  Arithmetic and
PC-relative control use modular `bitVecAdd` (`overflow(wrap)`); the branch test
uses `DecidableEq (BitVec 32)`. -/
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

/-! ## step = execute ∘ decode ∘ fetch -/

/-- One machine step: fetch at PC, decode, execute. -/
def step (state : IsaState) : IsaState :=
  execute (decode state.fetch) state

/-! ## Execute-level correctness corollaries -/

/-- `addReg` writes the sum `rs1 + rs2` to the destination register. -/
theorem execute_addReg_readReg (state : IsaState) (rd rs1 rs2 : BitVec 5) :
    (execute (.addReg rd rs1 rs2) state).readReg rd
      = bitVecAdd (state.readReg rs1) (state.readReg rs2) :=
  ArchState.readReg_writeReg_same state rd (bitVecAdd (state.readReg rs1) (state.readReg rs2))

/-- `loadImm` writes the immediate to the destination register. -/
theorem execute_loadImm_readReg (state : IsaState) (rd : BitVec 5) (imm : BitVec 32) :
    (execute (.loadImm rd imm) state).readReg rd = imm :=
  ArchState.readReg_writeReg_same state rd imm

/-- `loadImm` leaves registers other than the destination unchanged. -/
theorem execute_loadImm_readReg_other (state : IsaState) (rd probe : BitVec 5)
    (imm : BitVec 32) (distinct : probe ≠ rd) :
    (execute (.loadImm rd imm) state).readReg probe = state.readReg probe :=
  ArchState.readReg_writeReg_other state rd probe imm distinct

/-- `jump` sets the PC to the PC-relative target. -/
theorem execute_jump_pc (state : IsaState) (offset : BitVec 32) :
    (execute (.jump offset) state).pc = bitVecAdd state.pc offset := rfl

/-- `invalid` advances the PC, leaving the register file unchanged. -/
theorem execute_invalid_readReg (state : IsaState) (raw : BitVec 32) (idx : BitVec 5) :
    (execute (.invalid raw) state).readReg idx = state.readReg idx := rfl

/-! ## The ISA as its own golden reference (refinement tie-in) -/

/-- The identity forward simulation of the ISA against itself; `step` inhabits
`StepRefinement`. -/
def isaSelfRefinement (init : IsaState) : StepRefinement IsaState IsaState :=
  StepRefinement.identity step init

/-- Every reachable ISA run abstracts to itself: the whole-trace correspondence
(§18.12) for the self-refinement. -/
theorem isaSelfRefinement_onAllRuns (init : IsaState) (count : Nat) :
    (isaSelfRefinement init).abstracts
      (iterateStep step count init) (iterateStep step count init) :=
  (isaSelfRefinement init).onAllRuns count

end FX1Poly.ComputerAlgebra
