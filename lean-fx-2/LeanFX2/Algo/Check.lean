import LeanFX2.Algo.Infer

/-! # Algo/Check — type checking (bidirectional check mode)

```lean
def Term.check (ctx : Ctx mode level scope) (ty : Ty level scope)
    (raw : RawTerm scope) : Option (Term ctx ty raw)
```

Given a context + expected type + raw term, attempts to construct a
typed Term inhabiting `ty` whose raw form is `raw`.

## Algorithm

1. If `raw` is a synthesizable form (per `Algo/Infer.lean`), call
   `Term.infer` and verify the inferred type matches `ty` via Conv
2. Otherwise, dispatch on `raw`:
   * `lam body` — split `ty` into arrow domain/codomain, check body
   * `lamPi body` — split into piTy, check body in extended ctx
   * `pair fv sv` — split into sigmaTy, check both
   * `refl rawWitness` — split `ty` into id, verify endpoints
   * Modal intros — analogous

## Bidirectional discipline

Synthesis and checking complement each other:
* Synth: type discoverable from term
* Check: type provided, term filled in

The split avoids the need for full unification — checks are
syntactic Conv equality, not unification.

## Conv check fallthrough

When inferred type `ty_inf` differs from expected `ty`, attempt
`Conv ty_inf ty`.  If conv succeeds, accept; else reject.  This is
the "check fallthrough" pattern (lean-fx task #912).

## Dependencies

* `Algo/Infer.lean`

## Downstream

* `Surface/Elab.lean` — elaboration calls check at expected-type
  boundaries

## Implementation plan (Layer 9)

1. Define `Term.check` per raw form
2. Synth + Conv check fallthrough
3. Smoke: well-typed and ill-typed examples

Target: ~300 lines.
-/

namespace LeanFX2

variable {mode : Mode} {level : Nat}

/-- Bidirectional type check.  Given a context, an expected
type, and a raw term, returns `some t : Term ctx expectedType raw`
when the raw term is well-typed at `expectedType`, or `none`
otherwise.

## Coverage

* Atomic leaves (`var`, `unit`, `boolTrue/False`, `natZero`):
  expectedType must match the unique typing.
* Recursive nat (`natSucc`): expectedType = `Ty.nat`, check
  predecessor recursively.
* Parametric leaves (`listNil`, `optionNone`): expectedType must
  be the right type former with any element type.
* Recursive parametric (`listCons`, `optionSome`, `eitherInl`,
  `eitherInr`): expectedType determines the element type, then
  recurse.
* Binders + eliminators + dep forms: deferred to richer Check
  algorithm with motive synthesis.

## Zero-axiom

Uses DecidableEq on `Ty` for type matching.  The propositional
`▸` cast routes through `Eq.rec` (no `propext`).
-/
def Term.check : ∀ {scope : Nat}
    (context : Ctx mode level scope) (expectedType : Ty level scope)
    (raw : RawTerm scope),
    Option (Term context expectedType raw)
  | _, context, expectedType, raw => match raw with
  | .var position =>
      if h : expectedType = varType context position then
        some (h ▸ Term.var position)
      else
        none
  | .unit =>
      if h : expectedType = Ty.unit then
        some (h ▸ Term.unit)
      else
        none
  | .boolTrue =>
      if h : expectedType = Ty.bool then
        some (h ▸ Term.boolTrue)
      else
        none
  | .boolFalse =>
      if h : expectedType = Ty.bool then
        some (h ▸ Term.boolFalse)
      else
        none
  | .natZero =>
      if h : expectedType = Ty.nat then
        some (h ▸ Term.natZero)
      else
        none
  | .natSucc predRaw =>
      if h : expectedType = Ty.nat then
        match Term.check context Ty.nat predRaw with
        | some predTerm => some (h ▸ Term.natSucc predTerm)
        | none => none
      else
        none
  -- Parametric leaves: dispatch via Ty.headCtor projection
  -- (full-enum on Ty with wildcards leaks propext per Discipline #2)
  | .listNil =>
      match expectedType with
      | .listType _ => some Term.listNil
      | .unit | .bool | .nat | .arrow _ _ | .piTy _ _ | .sigmaTy _ _
      | .tyVar _ | .id _ _ _ | .optionType _ | .eitherType _ _ => none
  | .optionNone =>
      match expectedType with
      | .optionType _ => some Term.optionNone
      | .unit | .bool | .nat | .arrow _ _ | .piTy _ _ | .sigmaTy _ _
      | .tyVar _ | .id _ _ _ | .listType _ | .eitherType _ _ => none
  | .listCons headRaw tailRaw =>
      match expectedType with
      | .listType elementType =>
          match Term.check context elementType headRaw,
                Term.check context (.listType elementType) tailRaw with
          | some headTerm, some tailTerm =>
              some (Term.listCons headTerm tailTerm)
          | none, _ => none
          | _, none => none
      | .unit | .bool | .nat | .arrow _ _ | .piTy _ _ | .sigmaTy _ _
      | .tyVar _ | .id _ _ _ | .optionType _ | .eitherType _ _ => none
  | .optionSome valueRaw =>
      match expectedType with
      | .optionType elementType =>
          match Term.check context elementType valueRaw with
          | some valueTerm => some (Term.optionSome valueTerm)
          | none => none
      | .unit | .bool | .nat | .arrow _ _ | .piTy _ _ | .sigmaTy _ _
      | .tyVar _ | .id _ _ _ | .listType _ | .eitherType _ _ => none
  | .eitherInl valueRaw =>
      match expectedType with
      | .eitherType leftType _ =>
          match Term.check context leftType valueRaw with
          | some valueTerm => some (Term.eitherInl valueTerm)
          | none => none
      | .unit | .bool | .nat | .arrow _ _ | .piTy _ _ | .sigmaTy _ _
      | .tyVar _ | .id _ _ _ | .listType _ | .optionType _ => none
  | .eitherInr valueRaw =>
      match expectedType with
      | .eitherType _ rightType =>
          match Term.check context rightType valueRaw with
          | some valueTerm => some (Term.eitherInr valueTerm)
          | none => none
      | .unit | .bool | .nat | .arrow _ _ | .piTy _ _ | .sigmaTy _ _
      | .tyVar _ | .id _ _ _ | .listType _ | .optionType _ => none
  -- Lambda: expected type disambiguates non-dep arrow vs Π
  | .lam bodyRaw =>
      match expectedType with
      | .arrow domainType codomainType =>
          match Term.check (context.cons domainType)
                           codomainType.weaken bodyRaw with
          | some bodyTerm => some (Term.lam bodyTerm)
          | none => none
      | .piTy domainType codomainType =>
          match Term.check (context.cons domainType)
                           codomainType bodyRaw with
          | some bodyTerm => some (Term.lamPi bodyTerm)
          | none => none
      | .unit | .bool | .nat | .sigmaTy _ _ | .tyVar _ | .id _ _ _
      | .listType _ | .optionType _ | .eitherType _ _ => none
  -- App: deferred (requires inference of function's arrow domain)
  | .app _ _            => none
  | .pair _ _           => none
  | .fst _              => none
  | .snd _              => none
  | .boolElim _ _ _     => none
  | .natElim _ _ _      => none
  | .natRec _ _ _       => none
  | .listElim _ _ _     => none
  | .optionMatch _ _ _  => none
  | .eitherMatch _ _ _  => none
  | .refl _             => none
  | .idJ _ _            => none
  | .modIntro _         => none
  | .modElim _          => none
  | .subsume _          => none

end LeanFX2

namespace LeanFX2.Algo

-- TODO Layer 9: Term.check for binders + eliminators
-- TODO Layer 9: synth-then-Conv-check fallthrough

end LeanFX2.Algo
