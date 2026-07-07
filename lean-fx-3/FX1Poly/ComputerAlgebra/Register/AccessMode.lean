import FX1Poly.ComputerAlgebra.Bits.BitVec

/-! # AccessMode — the register access-mode algebra (fx_design.md §18.3)

The eight hardware register access modes as typed state transitions over
`BitVec width`.  Each mode is a `RegisterAccessMode`: what a read RETURNS
(`readValue`), what a read LEAVES BEHIND (`readResidual`, for the read-side-effect
modes RC/RS), how a write UPDATES the register (`writeUpdate`), and which writes
are LEGAL (`mayWrite`, only `RSVD` constrains it — "reserved bits must be written
zero").

## What is proven here

Six of the eight modes are DEFINITIONAL — every stated semantics closes by `rfl`:

* `RW` write installs the written value; `RO` write is a no-op (writes rejected via
  `mayWrite = False`); `WO` read returns zero (reads rejected, softened to "read as
  zero"); `RC` read returns the value and leaves zero; `RS` read returns the value
  and leaves all-ones; `RSVD` read returns zero, write is a no-op, and a write is
  legal exactly when it is zero.

Additionally the READ semantics of all eight modes (`readValue`) and the WRITE
FORM of `W1C`/`W1S` (`writeUpdate = bitVecAnd old (bitVecNot write)` resp.
`bitVecOr old write`) are pinned definitionally.

## Honest residual

The PER-BIT effect of `W1C`/`W1S` — "bit k of the result is `old_k && !write_k`"
resp. "`old_k || write_k`", and the closed forms `W1S old allOnes = allOnes`,
`W1C old allOnes = zero` — is NOT proven here.  It requires a bit-readback layer
(`bitAtNat (bitwiseFold …)`), whose enabling bridge `value >>> index =
natQuotient value (2^index)` is blocked zero-axiom: Init's `Nat.shiftRight`
reduces through `Nat.div`, whose reconstruction lemmas leak `propext`.  That
readback layer is a separate, larger arc; the mode DEFINITIONS ship complete here
so the layer can cap them later without disturbing this file.

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
