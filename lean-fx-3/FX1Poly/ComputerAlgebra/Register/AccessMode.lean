import FX1Poly.ComputerAlgebra.Bits.BitVec

/-! # AccessMode — the register access-mode algebra (fx_design.md §18.3)

The eight hardware register access modes as typed transitions over `BitVec width`.
A `RegisterAccessMode` records the read result (`readValue`), the post-read residual
(`readResidual`, nontrivial only for RC/RS), the write update (`writeUpdate`), and
write legality (`mayWrite`, constrained only by `RSVD`: reserved bits must be written
zero).

Six modes are definitional, each law closing by `rfl`: `RW` installs the written
value; `RO` rejects writes; `WO` reads as zero; `RC` reads then clears; `RS` reads
then sets all bits; `RSVD` reads zero, ignores writes, and admits a write exactly
when it is zero.  The read semantics of all eight modes and the `W1C`/`W1S` write
forms — `bitVecAnd old (bitVecNot write)` and `bitVecOr old write` — are pinned
definitionally too.

The per-bit residual of `W1C`/`W1S` sits above a bit-readback layer whose bridge
`value >>> index = natQuotient value (2^index)` is unavailable zero-axiom: Init's
`Nat.shiftRight` reduces through `Nat.div` and leaks `propext`.  The mode
definitions are complete without it.

`Init`-only, structural, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The all-ones constant (read-to-set residual) -/

/-- Every bit set: the ones' complement of zero. -/
def bitVecAllOnes {width : Nat} : BitVec width := bitVecNot bitVecZero

/-! ## The access-mode record -/

/-- A register access mode over `BitVec width`: read result, post-read residual,
write update, and write legality. -/
structure RegisterAccessMode (width : Nat) where
  /-- The value a read returns. -/
  readValue    : BitVec width → BitVec width
  /-- The register state left behind by a read (identity except RC/RS). -/
  readResidual : BitVec width → BitVec width
  /-- The register state after writing `written` onto `old`. -/
  writeUpdate  : BitVec width → BitVec width → BitVec width
  /-- Whether writing `written` is legal (only `RSVD` restricts). -/
  mayWrite     : BitVec width → Prop

/-! ## The eight modes -/

/-- `RW` — read-write: reads the value, writes install it. -/
def readWriteMode {width : Nat} : RegisterAccessMode width where
  readValue    := fun old => old
  readResidual := fun old => old
  writeUpdate  := fun _ written => written
  mayWrite     := fun _ => True

/-- `RO` — read-only: reads the value, writes are rejected (no-op, `mayWrite`
False). -/
def readOnlyMode {width : Nat} : RegisterAccessMode width where
  readValue    := fun old => old
  readResidual := fun old => old
  writeUpdate  := fun old _ => old
  mayWrite     := fun _ => False

/-- `WO` — write-only: writes install the value, reads are rejected (read as
zero). -/
def writeOnlyMode {width : Nat} : RegisterAccessMode width where
  readValue    := fun _ => bitVecZero
  readResidual := fun old => old
  writeUpdate  := fun _ written => written
  mayWrite     := fun _ => True

/-- `W1C` — write-1-to-clear: a `1` in the write clears the corresponding bit
(`old AND NOT written`). -/
def writeOneToClearMode {width : Nat} : RegisterAccessMode width where
  readValue    := fun old => old
  readResidual := fun old => old
  writeUpdate  := fun old written => bitVecAnd old (bitVecNot written)
  mayWrite     := fun _ => True

/-- `W1S` — write-1-to-set: a `1` in the write sets the corresponding bit
(`old OR written`). -/
def writeOneToSetMode {width : Nat} : RegisterAccessMode width where
  readValue    := fun old => old
  readResidual := fun old => old
  writeUpdate  := fun old written => bitVecOr old written
  mayWrite     := fun _ => True

/-- `RC` — read-to-clear: a read returns the value and clears the register. -/
def readToClearMode {width : Nat} : RegisterAccessMode width where
  readValue    := fun old => old
  readResidual := fun _ => bitVecZero
  writeUpdate  := fun old _ => old
  mayWrite     := fun _ => True

/-- `RS` — read-to-set: a read returns the value and sets every bit. -/
def readToSetMode {width : Nat} : RegisterAccessMode width where
  readValue    := fun old => old
  readResidual := fun _ => bitVecAllOnes
  writeUpdate  := fun old _ => old
  mayWrite     := fun _ => True

/-- `RSVD` — reserved: reads return zero, writes are no-ops, and a write is legal
only when it is zero ("reserved bits must be written zero"). -/
def reservedMode {width : Nat} : RegisterAccessMode width where
  readValue    := fun _ => bitVecZero
  readResidual := fun old => old
  writeUpdate  := fun old _ => old
  mayWrite     := fun written => written = bitVecZero

/-! ## Proven semantics (definitional) -/

theorem readWriteMode_readValue {width : Nat} (old : BitVec width) :
    readWriteMode.readValue old = old := rfl

theorem readWriteMode_writeUpdate {width : Nat} (old written : BitVec width) :
    readWriteMode.writeUpdate old written = written := rfl

theorem readOnlyMode_readValue {width : Nat} (old : BitVec width) :
    readOnlyMode.readValue old = old := rfl

theorem readOnlyMode_writeUpdate {width : Nat} (old written : BitVec width) :
    readOnlyMode.writeUpdate old written = old := rfl

theorem readOnlyMode_rejectsWrite {width : Nat} (written : BitVec width) :
    readOnlyMode.mayWrite written = False := rfl

theorem writeOnlyMode_readValue {width : Nat} (old : BitVec width) :
    writeOnlyMode.readValue old = bitVecZero := rfl

theorem writeOnlyMode_writeUpdate {width : Nat} (old written : BitVec width) :
    writeOnlyMode.writeUpdate old written = written := rfl

theorem readToClearMode_readValue {width : Nat} (old : BitVec width) :
    readToClearMode.readValue old = old := rfl

theorem readToClearMode_readResidual {width : Nat} (old : BitVec width) :
    readToClearMode.readResidual old = bitVecZero := rfl

theorem readToSetMode_readValue {width : Nat} (old : BitVec width) :
    readToSetMode.readValue old = old := rfl

theorem readToSetMode_readResidual {width : Nat} (old : BitVec width) :
    readToSetMode.readResidual old = bitVecAllOnes := rfl

theorem reservedMode_readValue {width : Nat} (old : BitVec width) :
    reservedMode.readValue old = bitVecZero := rfl

theorem reservedMode_writeUpdate {width : Nat} (old written : BitVec width) :
    reservedMode.writeUpdate old written = old := rfl

theorem reservedMode_mayWrite {width : Nat} (written : BitVec width) :
    reservedMode.mayWrite written = (written = bitVecZero) := rfl

/-- A zero write into a reserved field is always legal. -/
theorem reservedMode_zeroWriteLegal {width : Nat} :
    reservedMode.mayWrite (bitVecZero (width := width)) := rfl

/-! ## `W1C` / `W1S` write FORM (definitional; per-bit effect is the residual) -/

theorem writeOneToClearMode_readValue {width : Nat} (old : BitVec width) :
    writeOneToClearMode.readValue old = old := rfl

/-- The `W1C` write is exactly the mask-and `old AND NOT written` (the per-bit
`old_k && !written_k` reading is the deferred bit-readback residual). -/
theorem writeOneToClearMode_writeUpdate {width : Nat} (old written : BitVec width) :
    writeOneToClearMode.writeUpdate old written = bitVecAnd old (bitVecNot written) := rfl

theorem writeOneToSetMode_readValue {width : Nat} (old : BitVec width) :
    writeOneToSetMode.readValue old = old := rfl

/-- The `W1S` write is exactly the `old OR written` (the per-bit `old_k ||
written_k` reading is the deferred bit-readback residual). -/
theorem writeOneToSetMode_writeUpdate {width : Nat} (old written : BitVec width) :
    writeOneToSetMode.writeUpdate old written = bitVecOr old written := rfl

end FX1Poly.ComputerAlgebra
