import FX1Poly.Typed.HasType
import FX1Poly.Core.GeneratorAdmission
import FX1Poly.Core.GeneratorMetadata

/-! # FX1Poly/Typed/BoolTypeCodeSubstrate
    — substrate certificate for the `gen_boolCode` Bool type-code generator (SN-047)

The kernel ships VALUE generators `gen_boolTrue` / `gen_boolFalse` (and the eliminator
`gen_boolElim`) but, like every ground datatype (`nat` / `unit` / `Empty`), had NO TYPE code:
the type `Bool` was not a nameable cell.  `gen_boolCode` (`GeneratorCore.lean`) is the bespoke
nullary type-code generator that fills this gap — mirroring `gen_emptyCode` (CON-A1), the
substrate prerequisite for bool canonicity (SN-047: every closed `t : Bool` reduces to `boolTrue`
or `boolFalse`).

This file is the substrate CERTIFICATE: it pins the generator's shape to exactly the
nullary-type-code profile the future `Bool : Type@0` formation will consume.  The serialization
round-trip (`Generator.toNat_injective` / `Generator.fromTag_toNat`) and the finite-polygraph
bound (`Generator.toNat_lt` over `Fin 196`) already re-verify `gen_boolCode` automatically (they
are `cases generator`-uniform); this file adds the metadata-shape facts those uniform proofs do
not name.

## What is (and is NOT) shipped here

* `gen_boolCode_isNullaryTypeCode` — arity `0`, `binderShifts = []`, `cellSort = .type`: the
  generator is a closed, childless, type-sorted leaf (structurally identical to `gen_emptyCode`).
  This is exactly the precondition `hasTypeDescPi_nullaryFormation_viaGenArm` (`Empty`'s
  formation primitive) demands of a nullary former.
* `gen_boolCode_isAdmitted` — `gen_boolCode` is a `SupportedGenerator` under the default profile,
  so `boolTypeCell` is a structurally admissible kernel cell.

NOT here (deliberately, and honestly): `Bool : Type@0` formation, `boolTrue / boolFalse : Bool`
typing, and bool canonicity.  Formation needs a `typingRuleDescOf gen_boolCode` row, which is
gated behind the `by_cases pi/sigma` migration in `HasTypeDescSound.toHasType` (GTL-03/11) exactly
as `gen_emptyCode`'s `typingRuleDescOf` was deferred in CON-A1 — `typingRuleDescOf gen_boolCode`
is `none` today, so `boolTypeCell` is (correctly) not yet a typed type.  The reducibility-level
bool candidate (`boolCanonicalFormsCandidate`, #676) and the canonicity extraction (#677) are
already shipped; the missing link they await is this type-code plus the BFT-15 bridge (#768).

## Zero-axiom verification

`gen_boolCode_isNullaryTypeCode` is `⟨rfl, rfl, rfl⟩` (each metadata arm is a definitional
literal); `gen_boolCode_isAdmitted` is the `SupportedGenerator.gen_boolCode` constructor.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **`gen_boolCode` has exactly the nullary-type-code shape.**  Arity `0` (no children),
`binderShifts = []` (no bound positions), `cellSort = .type` (a type-former, not a value): the
same structural profile as `gen_emptyCode`.  These three metadata facts are the precondition the
nullary-former formation primitive (`hasTypeDescPi_nullaryFormation_viaGenArm`) consumes to derive
`Bool : Type@0` once the `typingRuleDescOf` row lands (GTL-11-gated). -/
theorem gen_boolCode_isNullaryTypeCode :
    Generator.arity .gen_boolCode = 0
      ∧ Generator.binderShifts .gen_boolCode = []
      ∧ Generator.cellSort .gen_boolCode = CellSort.type :=
  ⟨rfl, rfl, rfl⟩

/-- **`gen_boolCode` is admitted by the default profile.**  The `SupportedGenerator` witness for
`gen_boolCode`, so `boolTypeCell` (`mkGen gen_boolCode () childNil`) is a structurally admissible
kernel cell under `fxProfile`.  A `def` (not `theorem`): `SupportedGenerator` is `Type`-valued
(it carries the admission witness as data), so this returns the witness constructor. -/
def gen_boolCode_isAdmitted : SupportedGenerator .gen_boolCode :=
  .gen_boolCode

end FX1Poly.Typed
