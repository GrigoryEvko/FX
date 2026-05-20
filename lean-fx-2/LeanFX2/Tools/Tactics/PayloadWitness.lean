/-! # Tools/Tactics/PayloadWitness — payload-substitution one-shot

`fx_subst_payload <name> from <leftSuccess> and <rightSuccess>` expands to

```lean
have <name> := Option.some.inj ((<leftSuccess>).symm.trans <rightSuccess>)
subst <name>
```

The named payload equality is materialized from two `some` observations
of the same `Option` value, then immediately substituted.  Use to
collapse the very common shape

```lean
have payloadEq : leftValue = rightValue :=
  Option.some.inj (leftSuccess.symm.trans rightSuccess)
subst payloadEq
```

into a single tactic invocation.  Appears ~95 times across
`Term/PartialStrengthen.lean`'s per-ctor strength-T1 arms.

Variant of `fx_subst_some_payload` from
`Tools/Tactics/Choreography.lean`.  This file avoids Choreography's
production-layer import — pure-syntax macro, zero kernel imports,
cache-immortal under all kernel changes.  Equivalent behaviour;
choose whichever name reads better at the call site.

## Why not an explicit-type variant

A proposed `fx_subst_payload nameEq from leftSuc and rightSuc showing leftT = rightT`
variant was investigated and rejected.  Lean v4.29.1's tactic-grammar
`term` antiquotation greedily consumes the trailing `=` from the
showing clause (because `_ = _` is a valid Lean term), leaving the
literal `=` separator inside my outer syntax unmatched.  Workarounds
(use `term:max` precedence-bounded antiquotation, comma-separator
form, paren-wrap) all introduce more cognitive load than they save.
Recommend: when the elaborator needs explicit type guidance, write
the bare `have :_ = _ := ...; subst _` and document why inline.
-/

namespace LeanFX2.Tools.Tactics

/-- Materialize and immediately substitute the payload equality
derived from two `some` observations of the same Option computation.

```lean
fx_subst_payload payloadEq from leftSuccess and rightSuccess
```

elaborates to `have payloadEq := Option.some.inj
(leftSuccess.symm.trans rightSuccess); subst payloadEq`. -/
syntax "fx_subst_payload " ident " from " term " and " term : tactic

macro_rules
  | `(tactic|
        fx_subst_payload $payloadEq from $leftSuccess and $rightSuccess) =>
      `(tactic|
        have $payloadEq :=
          Option.some.inj (($leftSuccess).symm.trans $rightSuccess);
        subst $payloadEq)

end LeanFX2.Tools.Tactics
