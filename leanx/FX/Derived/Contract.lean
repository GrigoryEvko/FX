import FX.Kernel.Inductive
import FX.Kernel.Term

/-!
# Derived spec — Contract translation (§14, D9)

Contracts govern how a type behaves when it crosses a
boundary: client and server, application and database,
module and module, version N and version N+1.  A single
`contract` declaration produces a bundle of derived
operations — encode, decode, validate, migrate, project —
each of which elaborates to standard kernel terms.  No new
axiom is required; contracts compose Ind-family version
specs, Pi-typed validators and migrations, and refinement
predicates on payloads.

This module documents the translation and pins the expected
shape of the derived artifacts.  UNTRUSTED (L3 per SPEC.md
§5) — the load-bearing work lives in `FX/Kernel/Inductive.lean`
for the per-version IndSpec, in `FX/Kernel/Typing.lean` for
the Pi signatures, and in `FX/Elab/Elaborate.lean` for the
surface-to-kernel contract elaborator (which arrives with
M3 and §14 wiring; Phase-2 rejects `contract` at E010).

## Surface syntax (§14.1)

```
contract UserApi for UserRecord
  version 1 { id: nat; name: string; email: string };
  version 2 { id: nat; name: string; email: string; role: Role }
    migration add role default User;
  version 3 = UserRecord
    migration add created default epoch;

  compatibility {
    v1 -> v2 : backward;
    v2 -> v3 : backward;
    v3 -> v1 : not_compatible;
  };

  access id    : read_only;
  access role  : requires auth(Admin);

  format json     { id: "id"; created: "created_at"; };
  format protobuf { id: 1 as uint64; role: 4 as enum; };

  errors {
    InvalidEmail(string);
    Unauthorized;
    VersionMismatch(expected: nat, got: nat);
  };

  invariant name.length > 0;
  invariant role == Admin ==> email.ends_with("@company.com");
end contract;
```

One type may declare multiple contracts for different
boundary types — typically one per wire format or storage
backend.  Each is a separate `contract` declaration and
produces an independent set of derived operations.

## Translation to kernel

The elaborator takes a surface contract and produces four
kinds of artifact.

First, one `IndSpec` per declared version.  The version
block's field list becomes a single-ctor inductive with one
arg per field, preserving the surface field names in
`argNames`.  `version 1 { id: nat; name: string; email:
string }` for contract `UserApi` elaborates to:

```
IndSpec {
  name   := "UserApi.v1"
  params := []
  ctors  := [
    { name     := "UserApi_v1"
    , args     := [Term.ind "Nat" [], Term.ind "string" [], Term.ind "string" []]
    , argNames := ["id", "name", "email"] }
  ]
}
```

A version that binds to the underlying type directly
(`version N = T`) reuses `T`'s existing IndSpec rather than
introducing a new one.

Second, one validation Π per version.  The validator takes
a value at the version's shape and returns an `Either
errors T_valid` where `T_valid` is the version's IndSpec
refined by the contract's invariants.  The refinement
predicate is the conjunction of every `invariant` clause
the contract declares.  SMT discharges the invariants at
each construction site; runtime validation fires only at
boundary crossings where the source is untyped (§10.8).

Third, one migration Π per declared `migration N -> M`
clause.  A migration operates on the version-N IndSpec and
returns the version-M IndSpec, threading the declared
add/remove/rename/alter operations through the field list.
Each migration carries a totality obligation — every
version-N value maps to exactly one version-M value.  The
obligation is discharged by SMT at contract elaboration;
failure to discharge is error C001.

Fourth, format bindings.  Each `format` clause declares a
bidirectional binding between the IndSpec's fields and a
named wire-format schema (JSON, protobuf, SQL, and so on).
The elaborator generates encode and decode Πs for every
declared format.  The encoding map is stored as a data
table keyed by version and format; the decoder consults
the table to map incoming wire-format fields to the
IndSpec's argNames.

## Version migration and compatibility

Each `migration N -> M` clause declares one of four
operations on the field list: `add F default D`, `remove F`,
`rename F -> G`, and `alter F : T1 -> T2`.  The elaborator
composes these into a single Π and verifies its totality.

`compatibility` clauses classify version transitions as
backward, forward, both, or not-compatible.  A backward
transition means a version-M consumer can process
version-N data through the migration, and the migration is
total.  A forward transition means a version-N consumer
can process version-M data through the inverse migration.
The compiler computes the weakest classification consistent
with the declared migrations and emits a diagnostic when
the surface declaration conflicts with the computed
classification.

Migration totality together with compatibility underwrites
the automatic semver computation of §14.10.  An added
optional field produces a MINOR bump; a removed field or
strengthened precondition produces a MAJOR bump; the
direction of each bump follows from contravariant-on-input,
covariant-on-output subtyping at the contract level.

## Access modes and invariants

Each `access F : mode` clause constrains writes and reads
of field F through the contract's boundary.  The modes —
`read_only`, `write_once`, `append_only`, `monotonic`,
`guarded`, `unique`, and hardware-specific `W1C`, `W1S`,
`RC`, `RSVD` — correspond to refinements the elaborator
layers onto the validation Π.  A `write_once` field is
checked against its previous value at every write attempt;
`monotonic F order: O` requires the order's `≤` to hold
between old and new values.  Access modes compose with the
invariants declared in the same contract.

Invariants are ordinary refinement predicates on the
IndSpec.  They participate in the validator's returned-type
refinement and discharge through the same SMT machinery
that handles refinements on any other type.

## Generated operations

From a single contract declaration the elaborator produces
the following public surface:

```
UserApi.decode(fmt, raw)         : Either errors T
UserApi.encode(fmt, value)       : Bytes
UserApi.validate(value)          : Either errors T
UserApi.migrate(value, from, to) : Either migration_error T_new
UserApi.compatible(v1, v2)       : compatibility
UserApi.project(fmt)             : schema
```

Each is a top-level Π keyed by the contract's name.  The
operations are user-visible and addressable, and their
types are stable across contract evolution — they change
only when the corresponding version set changes.

## Deferred — surface contract declaration (E010)

`contract C for T ... end contract;` is parsed per
fx_grammar.md §11, but `elabDecl` rejects it at E010
(`contract declarations are not yet supported`).  The
elaborator lands with M3 and §14 wiring; the staged plan:

  1. Extend `elabTypeDeclSpec` with a `contract` branch that
     walks the version list, builds one `IndSpec` per
     version, and records the invariants as refinements.
  2. Build one migration Π per declared `migration N -> M`
     clause; SMT-discharge totality at elaboration.
  3. Generate encode, decode, validate, migrate, compatible,
     project Πs as top-level declarations scoped to the
     contract's name.
  4. Register format tables keyed by (contract, version,
     format) for the decoder to consult.
  5. Wire §14.10 automatic version computation to the
     contract diff produced during publish (§25.6).

No new kernel axiom is introduced.  Every contract-generated
operation reduces to Pi-form, Pi-intro, and Pi-elim over
the contract's per-version IndSpecs.
-/

namespace FX.Derived.Contract

open FX.Kernel

/-! ## Single-version contract

The minimal case: one record type, one contract version.
A single IndSpec captures the version's field layout, and
the derived operations reduce to trivial Πs over that
spec. -/

/-- Kernel IndSpec for version 1 of a three-field config
    record.  A single ctor named after the contract
    version; payload args match the surface field order;
    `argNames` preserve the declared names for use by the
    encode and decode tables. -/
def configApiV1Spec : IndSpec :=
  { name   := "ConfigApi.v1"
  , params := []
  , ctors  := [
      { name     := "ConfigApi_v1"
      , args     := [Term.ind "string" [], Term.ind "Nat" [], Term.ind "Bool" []]
      , argNames := ["host", "port", "tls"] }
    ]
  }

example : configApiV1Spec.ctorCount  = 1 := by decide
example : configApiV1Spec.paramCount = 0 := by decide

-- A version spec is a single-ctor inductive; every contract
-- version translates to this shape.
example : (configApiV1Spec.ctorAt? 0).map (·.args.length) = some 3 := by decide
example : (configApiV1Spec.ctorAt? 0).map (·.argNames)    =
    some ["host", "port", "tls"] := by decide

-- Field-index lookup drives encode and decode table
-- generation.
example :
    (configApiV1Spec.ctorAt? 0).bind (fun ctor =>
      ctor.argNames.idxOf? "port") = some 1 := by native_decide

example :
    (configApiV1Spec.ctorAt? 0).bind (fun ctor =>
      ctor.argNames.idxOf? "tls") = some 2 := by native_decide

example :
    (configApiV1Spec.ctorAt? 0).bind (fun ctor =>
      ctor.argNames.idxOf? "nonexistent") = none := by native_decide

/-! ## Multi-version contract

The §14.1 example: three versions of a user record, each
subsequent version adding a field.  The translation produces
three independent IndSpecs.  A regression that confused
versions — reusing one spec's IndCtor for another — would
surface at these examples' field counts. -/

/-- Version 1 of UserApi: three fields. -/
def userApiV1Spec : IndSpec :=
  { name   := "UserApi.v1"
  , params := []
  , ctors  := [
      { name     := "UserApi_v1"
      , args     := [Term.ind "Nat" [], Term.ind "string" [], Term.ind "string" []]
      , argNames := ["id", "name", "email"] }
    ]
  }

/-- Version 2 of UserApi: adds `role`. -/
def userApiV2Spec : IndSpec :=
  { name   := "UserApi.v2"
  , params := []
  , ctors  := [
      { name     := "UserApi_v2"
      , args     := [
          Term.ind "Nat" [],
          Term.ind "string" [],
          Term.ind "string" [],
          Term.ind "Role" []
        ]
      , argNames := ["id", "name", "email", "role"] }
    ]
  }

/-- Version 3 of UserApi: adds `created`. -/
def userApiV3Spec : IndSpec :=
  { name   := "UserApi.v3"
  , params := []
  , ctors  := [
      { name     := "UserApi_v3"
      , args     := [
          Term.ind "Nat" [],
          Term.ind "string" [],
          Term.ind "string" [],
          Term.ind "Role" [],
          Term.ind "timestamp" []
        ]
      , argNames := ["id", "name", "email", "role", "created"] }
    ]
  }

example : userApiV1Spec.ctorCount = 1 := by decide
example : userApiV2Spec.ctorCount = 1 := by decide
example : userApiV3Spec.ctorCount = 1 := by decide

-- Field counts grow across versions by the migrations'
-- `add` operations.
example : (userApiV1Spec.ctorAt? 0).map (·.args.length) = some 3 := by decide
example : (userApiV2Spec.ctorAt? 0).map (·.args.length) = some 4 := by decide
example : (userApiV3Spec.ctorAt? 0).map (·.args.length) = some 5 := by decide

-- The `role` field enters at v2 at index 3 and persists at
-- v3 at the same index.  Both pinnings catch a migration
-- bug that reorders fields.
example :
    (userApiV2Spec.ctorAt? 0).bind (fun ctor =>
      ctor.argNames.idxOf? "role") = some 3 := by native_decide

example :
    (userApiV3Spec.ctorAt? 0).bind (fun ctor =>
      ctor.argNames.idxOf? "role") = some 3 := by native_decide

-- `created` enters at v3 only.
example :
    (userApiV1Spec.ctorAt? 0).bind (fun ctor =>
      ctor.argNames.idxOf? "created") = none := by native_decide

example :
    (userApiV3Spec.ctorAt? 0).bind (fun ctor =>
      ctor.argNames.idxOf? "created") = some 4 := by native_decide

/-! ## Migration Π shape

A migration between adjacent versions translates to a Π
from the source IndSpec to the target IndSpec.  The body
operates on the field list — adding, removing, renaming,
or altering fields per the surface declaration — and the
totality obligation is discharged at elaboration.

Phase-2 pins only the Pi shape; the body elaboration lands
with M3.  A regression that used `app` or a non-Pi form for
the migration would fail this shape check. -/

/-- Kernel shape for `migrate_v1_to_v2`.  The Π takes a v1
    value and returns a v2 value.  Effect row is Tot — a
    pure field-addition migration performs no IO. -/
def migrateV1ToV2Shape : Term :=
  Term.pi Grade.default
    (Term.ind "UserApi.v1" [])
    (Term.ind "UserApi.v2" [])
    Effect.tot

example :
    (fun t => match t with
      | .pi _ _ _ _ => true
      | _           => false) migrateV1ToV2Shape = true := by native_decide

-- The migration's return-effect is Tot.  `add role default
-- User` does not perform IO.
example :
    (fun t => match t with
      | .pi _ _ _ eff => eff.io
      | _             => true) migrateV1ToV2Shape = false := by native_decide

/-- Kernel shape for `migrate_v2_to_v3`.  Same Pi pattern,
    different version names.  The elaborator emits one such
    Pi per declared migration clause. -/
def migrateV2ToV3Shape : Term :=
  Term.pi Grade.default
    (Term.ind "UserApi.v2" [])
    (Term.ind "UserApi.v3" [])
    Effect.tot

example :
    (fun t => match t with
      | .pi _ _ _ _ => true
      | _           => false) migrateV2ToV3Shape = true := by native_decide

/-! ## Validator Π

Every contract generates one top-level `validate` Π per
version.  It takes a raw value at the version's IndSpec and
returns an `Either errors T_refined` where the return type
carries the contract's invariants as refinements.  Phase-2
pins the outer Pi shape; the invariant refinements layer on
at elaboration. -/

/-- Kernel shape for `UserApi.validate_v2` — a Pi from the
    raw v2 record to a validated v2 record.  Effect is Tot;
    validation itself does no IO.  A full elaboration
    refines the return type with the declared invariants. -/
def validateV2Shape : Term :=
  Term.pi Grade.default
    (Term.ind "UserApi.v2" [])
    (Term.ind "UserApi.v2" [])
    Effect.tot

example :
    (fun t => match t with
      | .pi _ _ _ _ => true
      | _           => false) validateV2Shape = true := by native_decide

/-! ## Encoder and decoder Πs

Each `format NAME { ... }` clause produces one encoder and
one decoder Pi per version.  The encoder takes a contract
value and returns bytes; the decoder takes bytes and
returns an `Either errors value`.  Both carry Alloc on
their return-effect because they allocate a new byte
buffer or a new record.  A bug that declared the encoder
Tot would let it bypass allocation tracking. -/

/-- Kernel shape for `UserApi.encode_json_v2`.  Pi from a
    validated value to bytes; return-effect carries Alloc. -/
def encodeJsonV2Shape : Term :=
  Term.pi Grade.default
    (Term.ind "UserApi.v2" [])
    (Term.ind "Bytes" [])
    Effect.alloc_

example :
    (fun t => match t with
      | .pi _ _ _ eff => eff.alloc
      | _             => false) encodeJsonV2Shape = true := by native_decide

/-- Kernel shape for `UserApi.decode_json_v2`.  Pi from raw
    bytes to a value; return-effect carries Alloc because
    decoding constructs a new IndSpec value on the heap. -/
def decodeJsonV2Shape : Term :=
  Term.pi Grade.default
    (Term.ind "Bytes" [])
    (Term.ind "UserApi.v2" [])
    Effect.alloc_

example :
    (fun t => match t with
      | .pi _ _ _ eff => eff.alloc
      | _             => false) decodeJsonV2Shape = true := by native_decide

/-! ## Registry status

`contract` declarations land with M3 and §14 wiring; they
do not yet populate `Inductive.specByName?`.  The IndSpecs
built above are constructed by direct definition to pin the
translation shape; registry resolution of `UserApi.v1`,
`UserApi.v2`, and so on returns `none` at Phase-2 and will
begin returning the elaborated IndSpec once the contract
elaborator lands.  Surface `contract C for T ... end
contract;` falls through to E010 at elaboration. -/

example : Inductive.specByName? "UserApi.v1"   = none := rfl
example : Inductive.specByName? "UserApi.v2"   = none := rfl
example : Inductive.specByName? "UserApi.v3"   = none := rfl
example : Inductive.specByName? "ConfigApi.v1" = none := rfl

end FX.Derived.Contract
