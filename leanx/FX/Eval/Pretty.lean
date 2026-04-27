import FX.Eval.Value
import FX.Kernel.Inductive

/-!
# Value pretty-printer

Renders `Value`s in a compact human-readable form suitable for
`fxi run`'s stdout.  Not a perfect round-trip back to source —
the goal is quick inspection, not reproducibility.

## Conventions

  * `universe 0` → `type`
  * `universe (succ 0)` → `type<1>`
  * `piType` → `(_ : A) -> B` — captured evalEnv shown only for debug
  * `closure` → `<closure>` (or the body with placeholder captures
    when `--verbose`)
  * `ctor "Nat" 0 [] []` → `Nat.Zero`; `Nat.Succ (…)` for recursive
  * Nat-specific rendering: chains of `Succ` around `Zero` render
    as integer literals so `Nat.succ (Nat.succ Nat.zero)` prints as
    `2` instead of the noisy tree.
  * `neutral head spine` → `?head[ spine ]` — makes stuck terms
    visible.

Phase 2.2 targets readable output for the prelude types; full
pretty-printing for records, HKTs, and contracts lands with the
matching derived features.

## Coverage audit

Every `Value` constructor has a branch in `pretty`: `closure`,
`piType`, `sigmaType`, `ctor`, `indType`, `universe`,
`forallLevelType`, `idType`, `reflVal`, `neutralIdJ`,
`quotType`, `quotMkVal`, `neutralQuotLift`, `neutral`,
`neutralRec`.  Adding a new constructor to `Value` requires
adding a branch here — the `match` is non-exhaustive otherwise
and `lake build` fails.

Known visual ambiguity: `Value.placeholder` is defined as
`universe .zero` and prints identically to a genuine `type<0>`
value.  Matters only at the boundary where uninitialized eval
state would leak to output — in practice `placeholder` is never
produced by `eval`, only by `Inhabited` defaults for internal
list accessors.  Documented here so future readers don't file
a "pretty-printer lies about placeholder" bug.
-/

namespace FX.Eval

open FX.Kernel

namespace Value

/-- Render a level as compact text. -/
partial def levelToStr : Level → String
  | .zero            => "0"
  | .succ inner      => s!"(succ {levelToStr inner})"
  | .max left right  => s!"(max {levelToStr left} {levelToStr right})"
  | .var varIndex    => s!"u{varIndex}"

/-- Try to render a `ctor "Nat" k _ [n]` chain as an integer
    literal.  Returns `some n` when the value is a Nat ctor
    chain terminating at `Nat.Zero`, else `none`. -/
partial def asNat? : Value → Option Nat
  | .ctor "Nat" 0 _ _         => some 0
  | .ctor "Nat" 1 _ [predecessor] =>
    match asNat? predecessor with
    | some predNat => some (predNat + 1)
    | none         => none
  | _ => none

/-- Try to render a `ctor "Bool" k _ []` as a boolean literal. -/
def asBool? : Value → Option Bool
  | .ctor "Bool" 0 _ [] => some false
  | .ctor "Bool" 1 _ [] => some true
  | _ => none

/-- Pretty-print a Value, consulting `userSpecs` for user-declared
    ADT ctor names so `color.0` renders as `color.Red`.  Call
    `pretty` directly for prelude-only output; `prettyWith` is the
    full-lookup form used by the CLI with `globals.userSpecs`. -/
partial def prettyWith (userSpecs : List IndSpec) : Value → String
  | value =>
    -- Try prelude fast paths first for readability.
    match asNat? value with
    | some natValue => toString natValue
    | none =>
    match asBool? value with
    | some true  => "true"
    | some false => "false"
    | none =>
    match value with
    | .closure _ _ _ => "<closure>"
    | .piType _domainTy _codomainTy _capturedEnv =>
      "<Pi>"  -- Phase 2.2 shortcut; full rendering needs de Bruijn context
    | .sigmaType _firstTy _secondTy _capturedEnv => "<Sigma>"
    | .ctor typeName ctorIndex _typeArgs ctorArgs =>
      -- Look up the ctor name from user specs (B9) first, then
      -- falls back to prelude specs.  `specByName?` does the
      -- user-first sweep; empty `userSpecs` yields prelude-only.
      let ctorLabel : String :=
        match Inductive.specByName? typeName userSpecs with
        | some indSpec =>
          match indSpec.ctorAt? ctorIndex with
          | some ctorSpec => ctorSpec.name
          | none          => toString ctorIndex
        | none => toString ctorIndex
      if ctorArgs.isEmpty then s!"{typeName}.{ctorLabel}"
      else
        let argStrings := ctorArgs.map (prettyWith userSpecs)
        s!"{typeName}.{ctorLabel}({String.intercalate ", " argStrings})"
    | .indType typeName typeArgs =>
      if typeArgs.isEmpty then typeName
      else
        let argStrings := typeArgs.map (prettyWith userSpecs)
        s!"{typeName}<{String.intercalate ", " argStrings}>"
    | .universe .zero           => "type"
    | .universe (.succ level)   => s!"type<(succ {levelToStr level})>"
    | .universe otherLevel      => s!"type<{levelToStr otherLevel}>"
    | .forallLevelType _body _captured => "<∀ k. …>"
    | .idType carrierTy leftEndpoint rightEndpoint =>
      s!"Id({prettyWith userSpecs carrierTy}, {prettyWith userSpecs leftEndpoint}, {prettyWith userSpecs rightEndpoint})"
    | .reflVal witnessValue =>
      s!"refl({prettyWith userSpecs witnessValue})"
    | .neutralIdJ _motive _base stuckEq =>
      s!"J(…, {prettyWith userSpecs stuckEq})"
    | .quotType carrierTy relation =>
      s!"Quot({prettyWith userSpecs carrierTy}, {prettyWith userSpecs relation})"
    | .quotMkVal _relation witnessValue =>
      s!"⟦{prettyWith userSpecs witnessValue}⟧"
    | .neutralQuotLift _lifted _respects stuckTarget =>
      s!"Quot.lift(…, {prettyWith userSpecs stuckTarget})"
    | .neutral headVar []          => s!"?var{headVar}"
    | .neutral headVar spineArgs   =>
      let spineStrings := spineArgs.map (prettyWith userSpecs)
      s!"?var{headVar}[{String.intercalate ", " spineStrings}]"
    | .neutralRec indName _motive _minorPremises scrutinee =>
      s!"{indName}.rec(… {prettyWith userSpecs scrutinee})"

/-- Prelude-only pretty-printer.  Backward-compatible with callers
    that don't have a `GlobalEnv` handy; equivalent to `prettyWith
    [] value`.  User ADT ctor names fall back to their numeric
    index under this entry point. -/
def pretty (value : Value) : String := prettyWith [] value

end Value

end FX.Eval
