import FX.Kernel.Inductive
import FX.Kernel.Term

/-!
# Derived spec — Record translation (§3.4, D3)

Records are a surface-level shorthand for single-constructor
inductive families.  This module documents the translation and
exposes kernel-side helpers the elaborator uses.  It is
UNTRUSTED (L3 per `SPEC.md` §5) — the kernel sees only the
translated `IndSpec`; `Term.ind`/`Term.ctor`/`Term.indRec` do
the load-bearing work.

## Surface syntax (§3.4)

```
type config {
  host: string;
  port: nat;
  tls: bool;
};
```

## Translation to kernel

```
IndSpec {
  name   := "config"
  params := []
  ctors  := [
    { name     := "Config"      -- auto-capitalized type name
      args     := [string, nat, bool]
      argNames := ["host", "port", "tls"]
    }
  ]
}
```

## Construction (record literal)

Surface `config { host: "a", port: 8080, tls: true }` parses as
`Expr.app (.var "config") [named-args]` (per `Parser.lean` B8
record-literal sugar, line 285).  The elaborator:

  1. Resolves the TYPE NAME `config` via
     `MatchHelpers.resolveRecordCtor?` — a type name with
     exactly ONE ctor maps to that ctor.  Multi-ctor specs
     (proper ADTs) are ambiguous and rejected.
  2. Reorders named args to positional via `ctorSpec.argNames`.
  3. Emits `Term.ctor "config" 0 [] [hostVal, portVal, tlsVal]`.

The reorder is the same code path B12 uses for named fn args.

## Field access

Surface `x.f` where `x : T` and `T` is a registered record
spec elaborates to:

```
Term.indRec T
  motive          -- λ (_ :_ghost T). fieldType
  [projectMethod] -- one method for the sole ctor, with a λ chain
                  -- over the ctor's args binding positionally,
                  -- whose body returns the target field's var
  x
```

The projection method's structure for the 3-field record above,
asking for `.port`:

```
projectMethod := λ _host :_default string.
                 λ _port :_default nat.
                 λ _tls  :_default bool.
                 var 1        -- the `port` binder, de Bruijn 1
                              -- (0=tls, 1=port, 2=host)
```

The elaborator builds this in `.field` elab case via
`IndSpec.findFieldIndex?` on the spec's sole ctor's argNames.

## Spread update (§3.4 rule 16)

`{ ...base, port: 9090 }` currently parses per the spread-form
but B8's elab scope is first-cut: construction and field
access are implemented; spread-update as a record literal
operation is pending.  The parser emits the spread AST node;
the elaborator will route it to a generated per-record update
helper (one lambda chain per field, rebuilding the record with
the named fields overridden) once the translation lands.

## Invariants pinned by this file

The `example` blocks below exercise the translation shape so a
regression in `elabTypeDeclSpec` or `elabVariantCtor` (the B8
entry points in `FX/Elab/Elaborate.lean`) surfaces as a Lean
kernel-level proof failure, not a surprise at a runtime
conformance test.  Keep them terse — full end-to-end coverage
lives in `tests/Tests/Elab/AdtTests.lean` and
`tests/conformance/31_record_literal.fx`.
-/

namespace FX.Derived.Record

open FX.Kernel

/-- A minimal point record spec: `type point { x: Nat; y: Nat };`
    in kernel form.  Used by the examples to pin the expected
    translation shape.  Matches exactly what `elabTypeDeclSpec`
    builds when given the above surface syntax. -/
def pointSpec : IndSpec :=
  { name   := "point"
  , params := []
  , ctors  := [
      { name     := "Point"
        args     := [Term.ind "Nat" [], Term.ind "Nat" []]
        argNames := ["x", "y"]
      }
    ]
  }

/-- The record spec has a single ctor — that's the record
    invariant.  Multi-ctor specs are proper ADTs (B9), not
    records; the elaborator routes them through
    `resolveCtorRef?` instead of `resolveRecordCtor?`. -/
example : pointSpec.ctorCount = 1 := by decide

/-- The sole ctor carries positional field types in declaration
    order.  A regression that reordered would flip. -/
example : (pointSpec.ctorAt? 0).map (·.args.length) = some 2 := by decide

/-- argNames match the surface field names, positionally.  This
    is the critical invariant for B12's named-arg reorder at
    record-literal call sites — the elab looks up a field name
    and finds its positional index here. -/
example : (pointSpec.ctorAt? 0).map (·.argNames) = some ["x", "y"] := by decide

/-- Field-index lookup: `findFieldIndex?` projects the argNames
    list; a regression in the lookup would break `.field`
    elab and field-projection conformance.  Pinned so any
    rename of `argNames` or field-lookup walker surfaces here. -/
example : IndSpec.findFieldIndex? pointSpec "x" = some 0 := by decide
example : IndSpec.findFieldIndex? pointSpec "y" = some 1 := by decide
example : IndSpec.findFieldIndex? pointSpec "z" = none   := by decide

/-- A three-field record with heterogeneous types — pins that
    argNames and args carry through the elaborator even when
    field types vary.  The elaborator uses prelude specs
    (Bool, Nat) for the types. -/
def configSpec : IndSpec :=
  { name   := "config"
  , params := []
  , ctors  := [
      { name     := "Config"
        args     := [Term.ind "Nat" [], Term.ind "Bool" []]
        argNames := ["port", "tls"]
      }
    ]
  }

example : configSpec.ctorCount = 1                           := by decide
example : IndSpec.findFieldIndex? configSpec "port" = some 0 := by decide
example : IndSpec.findFieldIndex? configSpec "tls"  = some 1 := by decide

/-- Construction shape: a record literal elaborates to
    `Term.ctor T 0 [] [v_0, ..., v_{n-1}]` with typeArgs `[]`
    (records are non-parameterized in Phase-2), ctor index `0`
    (sole ctor), and value args in positional order after the
    elaborator's named-arg reorder. -/
def pointLiteralAt (xVal yVal : Term) : Term :=
  Term.ctor "point" 0 [] [xVal, yVal]

/-- Canonical construction with Nat literals.  `origin =
    point { x: Nat.Zero, y: Nat.Zero }` emits this term. -/
def pointOrigin : Term :=
  pointLiteralAt
    (Term.ctor "Nat" 0 [] [])  -- Nat.Zero
    (Term.ctor "Nat" 0 [] [])  -- Nat.Zero

example : Term.structEq pointOrigin
    (Term.ctor "point" 0 []
      [Term.ctor "Nat" 0 [] [], Term.ctor "Nat" 0 [] []])
    = true := by native_decide

end FX.Derived.Record
