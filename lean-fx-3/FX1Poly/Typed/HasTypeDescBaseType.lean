import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.CellConstructors

/-! # FX1Poly/Typed/HasTypeDescBaseType — the standalone NULLARY base-type formation judgment
    (`Bool : Type@0` / `Empty : Type@0`, with the universe flag PINNED by the rule).

The dependent type-formers (`piTyCode` / `sigmaTyCode` / `listCode` / `optionCode`) are typed at a
universe through the generic `genFormation` arm over `typingRuleDescOf`, whose `universeFormerOutput`
row sends a former to `universeCodeCell (lmaxAll levels) flag` — the universe FLAG is a free parameter
of `genFormation` that, for a ≥1-child former, is PINNED by the telescope's head child.  A NULLARY
type-former (`boolCode` / `emptyCode`, `binderShifts = []`) has NO head child, so routing it through
`genFormation` would leave its flag free — `genFormation` could type `boolCode` at `Type@0(standard)`
AND `Type@0(strict)`, two non-`Conv` classifiers, BREAKING `HasTypeDesc.uniqueness` (and, for
`emptyCode`, contradicting `HasTypeDescPi.emptyTypeCellHasNoTyping`, the refutation the SN-050
consistency proof relies on).  This is the future branch flagged at `HasTypeDesc.lean:281-283`:
"a nullary former's flag must be pinned by the formation RULE itself."

This file ships that as the established cascade-free standalone pattern (mirroring `HasTypeDescFlat`
and `HasTypeDescDataIntro`): a brand-new judgment `HasTypeDescBaseType` — NOT mutual with, NOT an arm
of, `HasTypeDescPi` — that types each nullary base type-code at a FIXED universe code through the
table `baseTypeRuleDescOf`.  Because the table FIXES the output (`Type@0(standard)`) with no free flag
parameter, the flag is pinned by construction: there is no uniqueness ambiguity, and the grown engine's
data-head refutations stay true (this is a different judgment about a different relation).

## What this gives

  * `Bool : Type@0` — the FORMATION half of bool canonicity (the type whose closed members the
    `boolCanonicalFormsCandidate` / `HasTypeDescDataIntro` value side ranges over).
  * `Empty : Type@0` — the FORMATION half of SN-050 (`Empty` IS a type — its NON-VACUITY), concretizing
    `NullaryFormerFormation`'s parametric `hasTypeDescPi_nullaryFormation_viaGenArm` along the route that
    does NOT collide with the consistency refutation.  Together with SN-050 (no closed inhabitant in the
    grown engine) this is the complete "`Empty` is an uninhabited type" story.

The n-ary / recursive type-code formers keep going through their own engines; this judgment's rows are
exactly the childless (nullary) base type-codes.

## Zero-axiom

`baseTypeRuleDescOf` is a pure-syntax `Option` table (metadata lemmas `rfl` on the diagonal); the
inductive is a single positive arm; the smokes are direct `baseFormation` applications with `rfl` table
lookups; the partition witnesses are `rfl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- A formation-rule description for a NULLARY base type-former: the FIXED output universe code (a
function of the scope), with the universe flag pinned INSIDE the description — `boolCode` and `emptyCode`
both output `Type@0(standard)`.  Pure syntax (no `HasTypeDescPi`), strictly positive, mirroring
`TypingRuleDesc` / `DataIntroNullaryRuleDesc`. -/
structure BaseTypeRuleDesc where
  outputUniverse : (scope : Nat) → RawTerm scope

/-- The per-generator NULLARY base-type formation table.  Its rows are exactly the childless type-code
formers (`binderShifts = []`); `boolCode` and `emptyCode` both form a member of `Type@0(standard)` — the
flag is FIXED here, never a free parameter, so the formation is flag-deterministic.  A new nullary
base type code is ONE more row, never a new arm — `unitCode` landed exactly that way (UNIT-1). -/
def baseTypeRuleDescOf (generator : Generator) : Option BaseTypeRuleDesc :=
  if generator = .gen_boolCode then
    some { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard }
  else if generator = .gen_emptyCode then
    some { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard }
  else if generator = .gen_natCode then
    some { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard }
  else if generator = .gen_unitCode then
    some { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard }
  else if generator = .gen_intervalCode then
    some { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard }
  else none

/-- `gen_boolCode` forms a member of `Type@0(standard)` (metadata check, `rfl` on the diagonal). -/
theorem baseTypeRuleDescOf_boolCode :
    baseTypeRuleDescOf .gen_boolCode
      = some { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard } :=
  rfl

/-- `gen_emptyCode` forms a member of `Type@0(standard)` (metadata check). -/
theorem baseTypeRuleDescOf_emptyCode :
    baseTypeRuleDescOf .gen_emptyCode
      = some { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard } :=
  rfl

/-- `gen_natCode` forms a member of `Type@0(standard)` (metadata check) — the Nat TYPE code's formation
row, the type whose closed members the data-intro value side (`natZero` / `natSucc : natCode`) ranges
over.  Same fixed output universe as `boolCode` / `emptyCode`, flag-pinned by the rule. -/
theorem baseTypeRuleDescOf_natCode :
    baseTypeRuleDescOf .gen_natCode
      = some { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard } :=
  rfl

/-- `gen_unitCode` forms a member of `Type@0(standard)` (metadata check) — the Unit TYPE code's
formation row, the type whose ONE closed canonical member is the value `unitCell` (the substrate of
unit canonicity and of the typed unit-eta judgment).  Same fixed output universe as the other
nullary base codes, flag-pinned by the rule. -/
theorem baseTypeRuleDescOf_unitCode :
    baseTypeRuleDescOf .gen_unitCode
      = some { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard } :=
  rfl

/-- `gen_intervalCode` forms a member of `Type@0(standard)` (metadata check) — the interval/dimension
TYPE code's formation row (NATIVE-06).  The bridge-dimension classifier `Interval : Type@0`, formed
through the standalone base-type engine on the same flag-pinned `Type@0(standard)` output as the other
nullary base codes — the cascade-free native home that retires the bridge engine's flag-parametric
`HasTypeDescBridge.intervalFormation` arm (whose `universeCodeCell lzero flag` for ANY flag was the
uniqueness hazard the base-type pinning fixes).  Carried into the grown formation table by the
NATIVE-44 BaseType→unified merge. -/
theorem baseTypeRuleDescOf_intervalCode :
    baseTypeRuleDescOf .gen_intervalCode
      = some { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard } :=
  rfl

/-- **The nullary base-type formation judgment.**  A standalone layer (NOT mutual with / NOT an arm of
`HasTypeDescPi`, mirroring `HasTypeDescFlat` / `HasTypeDescDataIntro`) typing the nullary base type-codes
at their FIXED universe code.  The single arm: a childless former in `baseTypeRuleDescOf` forms a member
of its tabled (flag-pinned) output universe — no premise telescope (there are no children).  Because the
table fixes the flag, the formation is flag-DETERMINISTIC by construction. -/
inductive HasTypeDescBaseType (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | baseFormation {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (payload : generator.payload scope)
      (children : RawTermChildren generator.binderShifts scope)
      (rule : BaseTypeRuleDesc)
      (isBaseType : baseTypeRuleDescOf generator = some rule) :
      HasTypeDescBaseType profile context (.mkGen generator payload children)
        (rule.outputUniverse scope)

/-- **★ `Bool : Type@0` in the base-type engine.**  The bool TYPE code is formed at `Type@0(standard)` —
the formation half of bool canonicity (the type whose closed members the data-intro value side, `boolTrue`
/ `boolFalse : boolCode`, ranges over).  The flag is pinned by the rule, so there is no uniqueness
ambiguity (the obstruction that blocked routing `boolCode` through the generic `genFormation` arm). -/
theorem HasTypeDescBaseType.boolCodeTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    HasTypeDescBaseType profile context boolTypeCell
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  HasTypeDescBaseType.baseFormation context .gen_boolCode () .childNil
    { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard } rfl

/-- **★ `Unit : Type@0` in the base-type engine.**  The unit TYPE code is formed at
`Type@0(standard)` — the formation half of the unit data story (the value half is
`HasTypeDescDataIntro.unitValueTyped`); the type whose one-value collapse the typed unit-eta
judgment is built on. -/
theorem HasTypeDescBaseType.unitCodeTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    HasTypeDescBaseType profile context unitTypeCell
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  HasTypeDescBaseType.baseFormation context .gen_unitCode () .childNil
    { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard } rfl

/-- **★ `Empty : Type@0` in the base-type engine.**  The empty TYPE code is formed at `Type@0(standard)`
— the formation half of SN-050 (`Empty` IS a type; its NON-VACUITY).  This is the standalone-judgment
concretization of `NullaryFormerFormation`'s parametric target, taking the route that does NOT collide
with `HasTypeDescPi.emptyTypeCellHasNoTyping` (the grown-engine refutation the consistency PROOF
consumes): typing `Empty` here is a different relation from the grown engine, so consistency stays
intact.  `Empty : Type@0` (here) + no closed grown inhabitant (SN-050) = the uninhabited-type story. -/
theorem HasTypeDescBaseType.emptyCodeTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    HasTypeDescBaseType profile context emptyTypeCell
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  HasTypeDescBaseType.baseFormation context .gen_emptyCode () .childNil
    { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard } rfl

/-- **★ `Nat : Type@0` in the base-type engine.**  The Nat TYPE code is formed at `Type@0(standard)` — the
formation half of Nat canonicity (the type whose closed members the data-intro value side, `natZero` /
`natSucc(n) : natCode`, ranges over).  Like `boolCode` / `emptyCode`, the flag is pinned by the rule, so
there is no uniqueness ambiguity; `gen_natCode` is a bespoke data type-code (NOT a generic `genFormation`
former — `typingRuleDescOf gen_natCode = none`), so its formation goes through this standalone base-type
judgment, never the cumulative `genFormation` telescope. -/
theorem HasTypeDescBaseType.natCodeTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    HasTypeDescBaseType profile context natTypeCell
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  HasTypeDescBaseType.baseFormation context .gen_natCode () .childNil
    { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard } rfl

/-- **★ `Interval : Type@0` in the base-type engine (NATIVE-06).**  The interval/dimension TYPE code is
formed at `Type@0(standard)` — the native (non-bridge-engine) formation row for the BCM bridge
dimension.  The flag is pinned by the rule, so the formation is flag-deterministic, FIXING the
uniqueness hazard of the bridge engine's `intervalFormation` arm (which typed `intervalTypeCell` at
`Type@0(flag)` for ANY flag).  This is the first BUILD-phase row of the unified-signature campaign; it
drains `gen_intervalCode` from the frankenstein hardcoded roster (now table-covered). -/
theorem HasTypeDescBaseType.intervalCodeTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    HasTypeDescBaseType profile context (.mkGen .gen_intervalCode () .childNil)
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  HasTypeDescBaseType.baseFormation context .gen_intervalCode () .childNil
    { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard } rfl

/-- **Partition witness: `boolCode` is NOT a generic formation former.**  `typingRuleDescOf gen_boolCode
= none` (the bool type code carries NO generic `genFormation` row — it is a nullary base type formed by
THIS judgment, not the ≥1-child generic engine), so the base-type judgment's domain is disjoint from the
generic formation table.  The base-type judgment is the engine that forms `boolCode`. -/
theorem typingRuleDescOf_boolCode_none :
    typingRuleDescOf .gen_boolCode = none := rfl

/-- **Partition witness: `natCode` is NOT a generic formation former.**  `typingRuleDescOf gen_natCode =
none` (the Nat type code carries NO generic `genFormation` row — it is a nullary base type formed by THIS
judgment, not the ≥1-child generic engine, and not a flat data former either).  So the base-type judgment's
domain stays disjoint from both the cumulative formation table and the flat data-former table; the
base-type judgment is the engine that forms `natCode`. -/
theorem typingRuleDescOf_natCode_none :
    typingRuleDescOf .gen_natCode = none := rfl

/-- **Partition witness: `emptyCode` is NOT a generic formation former.**  `typingRuleDescOf gen_emptyCode
= none` — `emptyCode`'s generic-engine row is DELIBERATELY absent (adding it would let `genFormation` type
`emptyTypeCell` at a universe, contradicting `HasTypeDescPi.emptyTypeCellHasNoTyping` and breaking SN-050).
`Empty`'s type-ness lives in the standalone base-type judgment instead. -/
theorem typingRuleDescOf_emptyCode_none :
    typingRuleDescOf .gen_emptyCode = none := rfl

end FX1Poly.Typed
