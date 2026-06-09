import FX1Poly.Core.GeneratorAdmission
import FX1Poly.Core.GeneratorMetadata

/-! # FX1Poly/Typed/NatTypeCodeSubstrate
    — substrate certificate for the `gen_natCode` Nat type-code generator

The kernel ships VALUE generators `gen_natZero` / `gen_natSucc` (and the eliminators
`gen_natElim` / `gen_natRec`); like every ground datatype (`bool` / `unit` / `Empty`), the
type `Nat` itself needs a dedicated TYPE code to be a nameable cell.  `gen_natCode`
(`GeneratorCore.lean`) is the bespoke nullary type-code generator that names it — mirroring
`gen_boolCode` / `gen_emptyCode` — the substrate prerequisite for nat canonicity (every closed
`t : Nat` reduces to `natZero` or `natSucc(...)`).

This file is the substrate CERTIFICATE: it pins the generator's shape to exactly the
nullary-type-code profile the `Nat : Type@0` base-type formation consumes.  The serialization
round-trip (`Generator.toNat_injective` / `Generator.fromTag_toNat`) and the finite-polygraph
bound (`Generator.toNat_lt` over `Fin 197`) already re-verify `gen_natCode` automatically (they
are `cases generator`-uniform); this file adds the metadata-shape facts those uniform proofs do
not name.

## What is (and is NOT) shipped here

* `gen_natCode_isNullaryTypeCode` — arity `0`, `binderShifts = []`, `cellSort = .type`: the
  generator is a closed, childless, type-sorted leaf (structurally identical to `gen_boolCode` /
  `gen_emptyCode`).  This is exactly the nullary-type-code profile the base-type formation
  judgment (`HasTypeDescBaseType`) demands.
* `gen_natCode_isAdmitted` — `gen_natCode` is a `SupportedGenerator` under the default profile,
  so `natTypeCell` is a structurally admissible kernel cell.

`Nat : Type@0` formation (the `baseTypeRuleDescOf gen_natCode` row) and the `natZero` / `natSucc`
typing (`HasTypeDescNatIntro`) live in their own files; this certificate is the shared
structural prerequisite, identical in shape to `BoolTypeCodeSubstrate`.

## Zero-axiom verification

`gen_natCode_isNullaryTypeCode` is `⟨rfl, rfl, rfl⟩` (each metadata arm is a definitional
literal); `gen_natCode_isAdmitted` is the `SupportedGenerator.gen_natCode` constructor.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **`gen_natCode` has exactly the nullary-type-code shape.**  Arity `0` (no children),
`binderShifts = []` (no bound positions), `cellSort = .type` (a type-former, not a value): the
same structural profile as `gen_boolCode` / `gen_emptyCode`.  These three metadata facts are the
precondition the nullary base-type formation judgment (`HasTypeDescBaseType`) consumes to derive
`Nat : Type@0` once the `baseTypeRuleDescOf` row lands. -/
theorem gen_natCode_isNullaryTypeCode :
    Generator.arity .gen_natCode = 0
      ∧ Generator.binderShifts .gen_natCode = []
      ∧ Generator.cellSort .gen_natCode = CellSort.type :=
  ⟨rfl, rfl, rfl⟩

/-- **`gen_natCode` is admitted by the default profile.**  The `SupportedGenerator` witness for
`gen_natCode`, so `natTypeCell` (`mkGen gen_natCode () childNil`) is a structurally admissible
kernel cell under `fxProfile`.  A `def` (not `theorem`): `SupportedGenerator` is `Type`-valued
(it carries the admission witness as data), so this returns the witness constructor. -/
def gen_natCode_isAdmitted : SupportedGenerator .gen_natCode :=
  .gen_natCode

end FX1Poly.Typed
