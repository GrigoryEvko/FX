import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPi
import FX1Poly.Typed.Ledger.Cell.CellConstructors

/-! # FX1Poly/Typed/HasTypeDescTermIndexedFormer — NATIVE-12 [MEGA]: the TermIndexedFormer table + telescope

The term-indexed former premise — a carrier typed at a universe plus endpoint terms typed at that carrier —
is expressible over the grown engine; the bespoke bridge-formation premise (formerly
`HasTypeDescBridge.bridgeFormation`, retired NATIVE-45) was an instance of it.  This file ships the DATA every
term-indexed former (the identity former `Id A a b`, the bridge former `Bridge A a b`) is typed by: a
generator-table row (`termIndexedFormerDescOf`) plus a children-indexed premise telescope
(`TermIndexedFormerTelescope`).  ONE generic typing arm consumes a row + the telescope — and after
TABLE-CANON-6 that arm IS the unified judgment's own `HasTypeUnion.formationRule` table arm (term-indexed
family) (the
standalone `HasTypeDescTermIndexedFormer` engine that NATIVE-12 seeded was inlined into the union and retired;
this file keeps only the table + telescope it consumes).

This is the term-indexed analogue of the formation table (`typingRuleDescOf` + `HasTypeDesc.genFormation`):

  * **the formation table** types formers whose children are a CUMULATIVE telescope of TYPES (`DescTelescope`,
    each child a universe member, the context extending under each — the Π/Σ shape);
  * **the term-indexed table** (here) types formers whose FIRST child is the carrier type and whose REMAINING
    children are MEMBERS of that carrier (no context extension — the Id/Bridge shape `[A, a, b]`).

The two premise spines differ exactly in what classifies the later children: a universe code (formation) vs an
earlier child viewed as a type (term-indexed).  Both families are table-driven and cascade-free — adding a future
term-indexed former is one more row in `termIndexedFormerDescOf`, never a new arm (both families ride the single
`formationRule` arm).

## What ships

  * `TermIndexedFormerDesc` + `termIndexedCarrierOutput` + `termIndexedFormerDescOf` — the rule table, with the
    `gen_bridgeCode` and `gen_idCode` rows (both at the carrier-level output `Type@e`).
  * `TermIndexedEndpoints` — the endpoint sub-telescope (every later child typed at the fixed carrier, over
    the grown engine, indexed by the `RawTermChildren` spine — the children-data form of the back-reference
    endpoint spine).
  * `TermIndexedFormerTelescope` — the full premise indexed by the children: head = carrier typed at a
    universe, tail = endpoints typed at the carrier.  The union's `formationRule` arm (term-indexed family) consumes exactly
    this (the term-indexed analogue of `DescTelescope`).

The structural metatheory of the telescope (renaming/substitution) is `HasTypeDescTermIndexedFormerWeakening`;
the union arm that interprets a row + telescope into a typing — with its inversion/uniqueness/SR/reducibility —
is `HasTypeUnion` and its metatheory suite (NATIVE-13..16, now restated at the union level).

## Zero-axiom

The table is `if`-chained `Option`; the metadata witnesses collapse by `rfl`; the telescope is a positive
recursive inductive over the grown engine.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The term-indexed former rule description.**  The output classifier as a function of the scope, the
CARRIER's universe level, and the flag.  (A term-indexed former's output is the carrier's universe — `Bridge A
a b : Type@e` when `A : Type@e` — so unlike the formation table's `lmaxAll`, the level is the single carrier
level, not an iterated max.) -/
structure TermIndexedFormerDesc where
  /-- The rule's output classifier: a universe code at the carrier's level. -/
  outputType : (scope : Nat) → LevelExpr → UniverseFlag → RawTerm scope

/-- The output classifier shared by the term-indexed formers (Id, Bridge): a universe code at the CARRIER's
level — `Id A a b : Type@e` / `Bridge A a b : Type@e` when the carrier `A : Type@e`.  Factored out so the two
rows are visibly the same rule and the metadata lemmas reduce through one definition. -/
def termIndexedCarrierOutput (scope : Nat) (level : LevelExpr)
    (flag : UniverseFlag) : RawTerm scope :=
  universeCodeCell level flag

/-- **The per-generator term-indexed former table.**  `gen_bridgeCode` (the bridge/internal-parametricity
former) and `gen_idCode` (the identity-type former) are the two term-indexed formers, both arity-3
`[carrier, left, right]` and both at the carrier-level output.  Adding a future term-indexed former is one more
row here — never a new typing arm. -/
def termIndexedFormerDescOf (generator : Generator) : Option TermIndexedFormerDesc :=
  if generator = .gen_bridgeCode then some { outputType := termIndexedCarrierOutput }
  else if generator = .gen_idCode then some { outputType := termIndexedCarrierOutput }
  else none

/-- **The endpoint sub-telescope.**  Every later child (all at binder-shift `0`) is typed at the fixed
`carrier` via the grown engine — the children-data form of the back-reference endpoint spine.  Indexed by
the `RawTermChildren` spine so the generic arm can consume the children abstractly. -/
inductive TermIndexedEndpoints (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (carrier : RawTerm scope) :
    {shifts : List Nat} → RawTermChildren shifts scope → Prop where
  | nil : TermIndexedEndpoints profile context carrier .childNil
  | cons {restShifts : List Nat} (endpoint : RawTerm scope)
      (rest : RawTermChildren restShifts scope)
      (endpointTyped : HasTypeDescPi profile context endpoint carrier)
      (restTyped : TermIndexedEndpoints profile context carrier rest) :
      TermIndexedEndpoints profile context carrier
        (RawTermChildren.childCons (shift := 0) endpoint rest)

/-- **The full term-indexed former premise, indexed by the children.**  The head child is the carrier (typed at
a universe code), and the tail children are the endpoints (each typed at the carrier).  The union's
`formationRule` arm (term-indexed family) consumes exactly this — the term-indexed analogue of `DescTelescope`. -/
inductive TermIndexedFormerTelescope (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) :
    {shifts : List Nat} → RawTermChildren shifts scope →
      RawTerm scope → LevelExpr → UniverseFlag → Prop where
  | mk {restShifts : List Nat} (carrier : RawTerm scope)
      (rest : RawTermChildren restShifts scope)
      (level : LevelExpr) (flag : UniverseFlag)
      (carrierTyped : HasTypeDescPi profile context carrier (universeCodeCell level flag))
      (endpointsTyped : TermIndexedEndpoints profile context carrier rest) :
      TermIndexedFormerTelescope profile context
        (RawTermChildren.childCons (shift := 0) carrier rest) carrier level flag

/-! ## Table metadata (`rfl`) -/

/-- `gen_bridgeCode`'s term-indexed row is the carrier-level output. -/
theorem termIndexedFormerDescOf_bridgeCode :
    termIndexedFormerDescOf .gen_bridgeCode = some { outputType := termIndexedCarrierOutput } := rfl

/-- `gen_idCode`'s term-indexed row is the carrier-level output (the SAME rule — table-genericity). -/
theorem termIndexedFormerDescOf_idCode :
    termIndexedFormerDescOf .gen_idCode = some { outputType := termIndexedCarrierOutput } := rfl

/-- A non-term-indexed former (here `gen_piTyCode`) has no term-indexed row. -/
theorem termIndexedFormerDescOf_piTyCode :
    termIndexedFormerDescOf .gen_piTyCode = none := rfl

end FX1Poly.Typed
