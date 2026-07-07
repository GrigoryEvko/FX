import FX1Poly.ComputerAlgebra.Register.FieldLayout

/-! # ArchState — the golden-reference architectural machine state (fx_design.md §18.12)

The state layer of the hardware substrate: a register file, a memory, and a
program counter over the shipped zero-axiom `BitVec` carrier.  Both stores are
modelled as TOTAL FUNCTIONS `BitVec key -> BitVec value`, updated by functional
override under the axiom-clean `DecidableEq (BitVec _)`.  This is exactly the
§18.12 "ISA is a `Tot` function over architectural state" golden-reference shape:

* every read/write is total with genuine `Eq`, no `Array` bound proofs, no
  `Nat.mod` index wrap, no `Fin.ofNat` coercion at decode sites;
* update is O(1) (prepend one `ite`); read is O(#writes) at runtime — irrelevant
  for a spec/proof state, the stated target;
* the two store laws (read-after-write same / other) close by `if_pos`/`if_neg`,
  both `match`-on-`Decidable`, so the layer inherits the substrate's zero-axiom
  status verbatim.

State EQUALITY is deliberately out of scope (proving two whole `ArchState`s equal
would need `funext`, a `Quot.sound`-derived theorem).  All reasoning here is
OBSERVATIONAL — `readReg`/`readMem`/`fetch` after a sequence of writes — and every
observational law closes with `if_pos`/`if_neg`/`rfl`, no funext.

`Init`-only (through the `BitVec` floor), structural, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The generic total store (reused for both registers and memory) -/

/-- A total store: a function from a `BitVec`-indexed key to a `BitVec` word.
`keyWidth` bits of index, `valWidth` bits of payload. -/
abbrev BitStore (keyWidth valWidth : Nat) : Type := BitVec keyWidth → BitVec valWidth

/-- Constant store — every slot holds the same word (use `bitVecZero` for a
zero-initialised machine). -/
def BitStore.const {keyWidth valWidth : Nat} (fill : BitVec valWidth) :
    BitStore keyWidth valWidth := fun _ => fill

/-- Read slot `key`. -/
def BitStore.read {keyWidth valWidth : Nat}
    (store : BitStore keyWidth valWidth) (key : BitVec keyWidth) : BitVec valWidth :=
  store key

/-- Write `value` at `key`, leaving every other slot untouched. -/
def BitStore.write {keyWidth valWidth : Nat}
    (store : BitStore keyWidth valWidth) (key : BitVec keyWidth)
    (value : BitVec valWidth) : BitStore keyWidth valWidth :=
  fun probe => if probe = key then value else store probe

/-- Read-after-write at the same slot returns exactly what was written. -/
theorem BitStore.read_write_same {keyWidth valWidth : Nat}
    (store : BitStore keyWidth valWidth) (key : BitVec keyWidth)
    (value : BitVec valWidth) :
    (store.write key value).read key = value :=
  if_pos rfl

/-- Read-after-write at a DIFFERENT slot is unchanged. -/
theorem BitStore.read_write_other {keyWidth valWidth : Nat}
    (store : BitStore keyWidth valWidth) (key probe : BitVec keyWidth)
    (value : BitVec valWidth) (distinct : probe ≠ key) :
    (store.write key value).read probe = store.read probe :=
  if_neg distinct

/-! ## The architectural state -/

/-- The architectural machine state, parametric in three widths:

* `wordWidth`   — data-word width  (RV32: 32),
* `addrWidth`   — address width    (RV32: 32),
* `regIdxWidth` — register-selector width (RV: 5, i.e. `2^5 = 32` registers). -/
structure ArchState (wordWidth addrWidth regIdxWidth : Nat) where
  /-- Register file: `BitVec regIdxWidth |-> BitVec wordWidth`. -/
  registers : BitStore regIdxWidth wordWidth
  /-- Memory: `BitVec addrWidth |-> BitVec wordWidth` (word-addressed spec store). -/
  memory    : BitStore addrWidth wordWidth
  /-- Program counter. -/
  pc        : BitVec addrWidth

/-- A zero-initialised machine: every register and memory slot holds zero, PC at
zero. -/
def ArchState.zeroed {wordWidth addrWidth regIdxWidth : Nat} :
    ArchState wordWidth addrWidth regIdxWidth :=
  { registers := BitStore.const bitVecZero
  , memory    := BitStore.const bitVecZero
  , pc        := bitVecZero }

/-! ## Register / memory / PC operations (thin field-updating wrappers) -/

/-- Read register `idx`. -/
def ArchState.readReg {wordWidth addrWidth regIdxWidth : Nat}
    (state : ArchState wordWidth addrWidth regIdxWidth) (idx : BitVec regIdxWidth) :
    BitVec wordWidth := state.registers.read idx

/-- Write register `idx := value`. -/
def ArchState.writeReg {wordWidth addrWidth regIdxWidth : Nat}
    (state : ArchState wordWidth addrWidth regIdxWidth) (idx : BitVec regIdxWidth)
    (value : BitVec wordWidth) : ArchState wordWidth addrWidth regIdxWidth :=
  { state with registers := state.registers.write idx value }

/-- Read memory at `addr`. -/
def ArchState.readMem {wordWidth addrWidth regIdxWidth : Nat}
    (state : ArchState wordWidth addrWidth regIdxWidth) (addr : BitVec addrWidth) :
    BitVec wordWidth := state.memory.read addr

/-- Write memory `addr := value`. -/
def ArchState.writeMem {wordWidth addrWidth regIdxWidth : Nat}
    (state : ArchState wordWidth addrWidth regIdxWidth) (addr : BitVec addrWidth)
    (value : BitVec wordWidth) : ArchState wordWidth addrWidth regIdxWidth :=
  { state with memory := state.memory.write addr value }

/-- Overwrite the program counter. -/
def ArchState.setPc {wordWidth addrWidth regIdxWidth : Nat}
    (state : ArchState wordWidth addrWidth regIdxWidth) (target : BitVec addrWidth) :
    ArchState wordWidth addrWidth regIdxWidth := { state with pc := target }

/-- Advance the program counter by one word (word-addressed default). -/
def ArchState.advancePc {wordWidth addrWidth regIdxWidth : Nat}
    (state : ArchState wordWidth addrWidth regIdxWidth) :
    ArchState wordWidth addrWidth regIdxWidth :=
  state.setPc (bitVecAdd state.pc bitVecOne)

/-- Fetch = read memory at the current PC (word-addressed). -/
def ArchState.fetch {wordWidth addrWidth regIdxWidth : Nat}
    (state : ArchState wordWidth addrWidth regIdxWidth) : BitVec wordWidth :=
  state.readMem state.pc

/-! ## Observational state laws (all zero-axiom, lifted from the store laws) -/

/-- Reading back a just-written register returns exactly what was written. -/
theorem ArchState.readReg_writeReg_same {wordWidth addrWidth regIdxWidth : Nat}
    (state : ArchState wordWidth addrWidth regIdxWidth) (idx : BitVec regIdxWidth)
    (value : BitVec wordWidth) : (state.writeReg idx value).readReg idx = value :=
  BitStore.read_write_same state.registers idx value

/-- Writing register `idx` leaves a different register `probe` unchanged. -/
theorem ArchState.readReg_writeReg_other {wordWidth addrWidth regIdxWidth : Nat}
    (state : ArchState wordWidth addrWidth regIdxWidth) (idx probe : BitVec regIdxWidth)
    (value : BitVec wordWidth) (distinct : probe ≠ idx) :
    (state.writeReg idx value).readReg probe = state.readReg probe :=
  BitStore.read_write_other state.registers idx probe value distinct

/-- Reading back a just-written memory slot returns exactly what was written. -/
theorem ArchState.readMem_writeMem_same {wordWidth addrWidth regIdxWidth : Nat}
    (state : ArchState wordWidth addrWidth regIdxWidth) (addr : BitVec addrWidth)
    (value : BitVec wordWidth) : (state.writeMem addr value).readMem addr = value :=
  BitStore.read_write_same state.memory addr value

/-- Writing memory `addr` leaves a different address `probe` unchanged. -/
theorem ArchState.readMem_writeMem_other {wordWidth addrWidth regIdxWidth : Nat}
    (state : ArchState wordWidth addrWidth regIdxWidth) (addr probe : BitVec addrWidth)
    (value : BitVec wordWidth) (distinct : probe ≠ addr) :
    (state.writeMem addr value).readMem probe = state.readMem probe :=
  BitStore.read_write_other state.memory addr probe value distinct

/-- Registers are unaffected by a memory write (independent projection). -/
theorem ArchState.readReg_writeMem {wordWidth addrWidth regIdxWidth : Nat}
    (state : ArchState wordWidth addrWidth regIdxWidth) (addr : BitVec addrWidth)
    (value : BitVec wordWidth) (idx : BitVec regIdxWidth) :
    (state.writeMem addr value).readReg idx = state.readReg idx := rfl

/-- Memory is unaffected by a register write (independent projection). -/
theorem ArchState.readMem_writeReg {wordWidth addrWidth regIdxWidth : Nat}
    (state : ArchState wordWidth addrWidth regIdxWidth) (idx : BitVec regIdxWidth)
    (value : BitVec wordWidth) (addr : BitVec addrWidth) :
    (state.writeReg idx value).readMem addr = state.readMem addr := rfl

/-- Registers are unaffected by a PC redirect (independent projection). -/
theorem ArchState.readReg_setPc {wordWidth addrWidth regIdxWidth : Nat}
    (state : ArchState wordWidth addrWidth regIdxWidth) (target : BitVec addrWidth)
    (idx : BitVec regIdxWidth) :
    (state.setPc target).readReg idx = state.readReg idx := rfl

/-- Fetch after redirecting the PC reads the target slot. -/
theorem ArchState.fetch_setPc {wordWidth addrWidth regIdxWidth : Nat}
    (state : ArchState wordWidth addrWidth regIdxWidth) (target : BitVec addrWidth) :
    (state.setPc target).fetch = state.readMem target := rfl

/-- The PC after a redirect is exactly the target. -/
theorem ArchState.pc_setPc {wordWidth addrWidth regIdxWidth : Nat}
    (state : ArchState wordWidth addrWidth regIdxWidth) (target : BitVec addrWidth) :
    (state.setPc target).pc = target := rfl

end FX1Poly.ComputerAlgebra
