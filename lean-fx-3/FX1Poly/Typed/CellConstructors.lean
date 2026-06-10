import FX1Poly.Core.RawTerm
import FX1Poly.Universe.LevelExpr
import FX1Poly.Universe.UniverseFlag

/-! # FX1Poly/Typed/CellConstructors — the `.type`/`.term`-cell smart constructors

The named smart-constructors for the fibrant `RawTerm` cells that the typed layer
classifies and forms: universe-code, empty-type, bool-type, variable, and the
dependent Π/Σ type-code cells.  These are PURE SYNTAX over the one polygraph
substrate (`RawTerm.mkGen` + the generator table) — they depend only on `RawTerm`
and the universe payload types (`LevelExpr`, `UniverseFlag`), NOT on any typing
judgment.

## Why this module exists

These constructors are used pervasively across the kernel — the reducibility
substrate, the grown engine `HasTypeDescPi`, the audit corpus.  Housing them in
their own pure-syntax module (depending only on `RawTerm` and the universe payload
types) keeps the cell vocabulary every layer shares free of any typing-judgment
dependency.  The fully-qualified names are `FX1Poly.Typed.universeCodeCell`, ….

## Zero-axiom verification

Each constructor is a single `RawTerm.mkGen` application — no proofs, no `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Audit-gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The universe-code classifier cell `Type@(levelExpr, flag)` — the
`.type`-sorted cell that classifies types at universe level `levelExpr`
under hierarchy flag `flag` (§11.8.2). -/
def universeCodeCell {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) : RawTerm scope :=
  .mkGen .gen_universeCode (levelExpr, flag) .childNil

/-- The empty-type code cell `Empty` — the `.type`-sorted nullary `gen_emptyCode`
cell (the bottom type, fx_design §3.9 `never`).  No payload data (`Unit`), no
children (`binderShifts = []`, hence `childNil`): a closed nullary type-former
leaf, structurally like `universeCodeCell` but at a distinct generator.  The
formation subject of CON-A2's dedicated `emptyFormation` arm (`Empty : Type@0`)
and the type whose reducibility candidate is the empty candidate (CON-A3), the
substrate of typed consistency (SN-050). -/
def emptyTypeCell {scope : Nat} : RawTerm scope :=
  .mkGen .gen_emptyCode () .childNil

/-- The bool-type code cell `Bool` — the `.type`-sorted nullary `gen_boolCode`
cell.  No payload data (`Unit`), no children (`binderShifts = []`, hence
`childNil`): a closed nullary type-former leaf, structurally identical to
`emptyTypeCell` but at a distinct generator (the `gen_boolCode` substrate).
The formation subject of `Bool : Type@0` (via the nullary-former formation
`hasTypeDescPi_nullaryFormation_viaGenArm` once the `typingRuleDescOf` row lands)
and the type whose reducibility candidate is the bool data candidate
(`boolCanonicalFormsCandidate`) — the substrate of bool canonicity.
Distinct from the VALUE cells `gen_boolTrue` / `gen_boolFalse`: this is the TYPE
code. -/
def boolTypeCell {scope : Nat} : RawTerm scope :=
  .mkGen .gen_boolCode () .childNil

/-- The nat-type code cell `Nat` — the `.type`-sorted nullary `gen_natCode`
cell.  No payload data (`Unit`), no children (`binderShifts = []`, hence
`childNil`): a closed nullary type-former leaf, structurally identical to
`boolTypeCell` / `emptyTypeCell` but at the distinct `gen_natCode` generator.
The formation subject of `Nat : Type@0` (via the nullary base-type formation
`HasTypeDescBaseType` once the `baseTypeRuleDescOf` row lands) and the type
whose closed members the nat data-intro value side (`natZero` / `natSucc`)
ranges over — the substrate of nat canonicity.  Distinct from the VALUE cells
`gen_natZero` / `gen_natSucc`: this is the TYPE code. -/
def natTypeCell {scope : Nat} : RawTerm scope :=
  .mkGen .gen_natCode () .childNil

/-- The unit-type code cell `Unit` — the `.type`-sorted nullary `gen_unitCode`
cell.  No payload data (`Unit`), no children: a closed nullary type-former
leaf, structurally identical to `boolTypeCell` / `natTypeCell` but at the
distinct `gen_unitCode` generator.  The formation subject of `Unit : Type@0`
(via the nullary base-type formation `HasTypeDescBaseType`) and the type whose
ONE closed canonical member is the value `unitCell` — the substrate of unit
canonicity and of the typed unit-eta judgment.  Distinct from the VALUE cell
`gen_unit`: this is the TYPE code. -/
def unitTypeCell {scope : Nat} : RawTerm scope :=
  .mkGen .gen_unitCode () .childNil

/-- The variable cell at de Bruijn position `index`. -/
def variableCell {scope : Nat} (index : Fin scope) : RawTerm scope :=
  .mkGen .gen_var index .childNil

/-- The dependent function-type code cell `Π domainCode. codomainCode` — the
`.type`-sorted `gen_piTyCode` cell (binder shifts `[0, 1]`: the codomain lives
under one fresh value binder, hence at `scope + 1`).  Payload is `Unit`; the two
children are the domain and codomain codes.  The subject cell of the
`piFormation` arm. -/
def piTyCodeCell {scope : Nat} (domainCode : RawTerm scope)
    (codomainCode : RawTerm (scope + 1)) : RawTerm scope :=
  .mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))

/-- The dependent pair-type code cell `Σ domainCode. codomainCode` — the
`.type`-sorted `gen_sigmaTyCode` cell.  Structurally identical to
`piTyCodeCell` (binder shifts `[0, 1]`: the codomain lives under one fresh
value binder, hence at `scope + 1`; payload is `Unit`; the two children are the
domain and codomain codes); only the head generator differs (`gen_sigmaTyCode`
vs `gen_piTyCode`).  The subject cell of the `sigmaFormation` arm, the dual of
the Π-formation cell. -/
def sigmaTyCodeCell {scope : Nat} (domainCode : RawTerm scope)
    (codomainCode : RawTerm (scope + 1)) : RawTerm scope :=
  .mkGen .gen_sigmaTyCode () (.childCons domainCode (.childCons codomainCode .childNil))

/-- The unit value cell — the nullary `gen_unit` leaf (no payload data, no
children).  The canonical inhabitant of the unit type; a `RawTerm` value used by
the unit canonical-forms / smoke fixtures.  Lives with the other cell
constructors, independent of any typing engine. -/
def unitCell {scope : Nat} : RawTerm scope :=
  .mkGen .gen_unit () .childNil

end FX1Poly.Typed
