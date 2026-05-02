import LeanFX2.Term
import LeanFX2.Algo.DecConv

/-! # Algo/Infer — type inference for synthesizable Term forms

Bidirectional type checking has two modes:
* `infer` — type can be synthesized from the term's structure
* `check` — type is given, term must match it

This file handles **inference**.  `Algo/Check.lean` handles **checking**.

## Synthesizable forms

Inference works for forms whose result type is determined by
sub-term types:
* `var i` — type from `varType ctx i`
* `app fn arg` — infer fn's arrow type, check arg against domain,
  return codomain
* `appPi fn arg` — infer fn's piTy, check arg against domain,
  substitute and return
* `fst pairTerm` — infer pairTerm's sigmaTy, return first component type
* `snd pairTerm` — return second component substituted with first
* `idJ baseCase witness` — infer witness's id type, infer base's type
* `boolElim/natElim/listElim/etc.` — synth scrutinee type, return
  branch type (when branches have explicit type annotation)
* `Term.refl rawWitness` — needs context (no inference; check mode only)

## Synthesis function signature

```lean
def Term.infer (ctx : Ctx mode level scope) (raw : RawTerm scope) :
    Option (Σ ty, Term ctx ty raw)
```

Given a raw term + context, attempts to infer a typed Term whose raw
form is `raw`.  Returns `Option` because:
* Some raw terms are not well-typed in the given context
* Some forms are check-only (lam without type annotation)

## Dependencies

* `Term.lean`
* `Algo/DecConv.lean` — Conv check at sub-term boundaries

## Downstream

* `Algo/Check.lean` — infer is a sub-routine of check
* `Algo/Synth.lean` — atomic synthesis cases
* `Surface/Elab.lean` — elaboration uses infer/check

## Implementation plan (Layer 9)

1. Define `Term.infer` by structural recursion on `raw`
2. Each ctor case: synthesize sub-term types, build typed Term
3. Smoke: identity function applied to unit

Target: ~400 lines.
-/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat}

/-- Type inference for atomic + unambiguous-recursive raw forms.
Returns `some ⟨ty, term⟩` when the raw form has a unique typed
witness; returns `none` for forms that need an expected type to
disambiguate (lam vs lamPi, app vs appPi, pair, refl, idJ,
eliminators).

## Coverage

* `RawTerm.var pos` — type from `varType context pos`
* Nullary canonical heads (`unit`, `boolTrue/False`, `natZero`)
* `RawTerm.natSucc inner` — recursively infer + verify nat-typed
* All other forms — `none` (defer to `Term.check` with expected type)

## Why partial

Several `RawTerm` forms have ambiguous typings:
* `lam bodyRaw` — could be `Term.lam` (non-dep arrow) or
  `Term.lamPi` (dep Π); same for `app`
* `pair`, `fst`, `snd` — depend on the σ-type structure
* `refl` — depends on identity-type carrier
* Eliminators — depend on motive type

These are check-mode constructors handled by `Algo/Check.lean`.

## Zero-axiom

Recursive cases use propositional `▸` casting via DecidableEq Ty,
which routes through `Eq.rec` (not `propext`).  Verified
zero-axiom for the inferable subset. -/
def Term.infer (context : Ctx mode level scope) :
    (raw : RawTerm scope) →
    Option (Σ (someType : Ty level scope), Term context someType raw)
  | .var position =>
      some ⟨varType context position, Term.var position⟩
  | .unit =>
      some ⟨Ty.unit, Term.unit⟩
  | .boolTrue =>
      some ⟨Ty.bool, Term.boolTrue⟩
  | .boolFalse =>
      some ⟨Ty.bool, Term.boolFalse⟩
  | .natZero =>
      some ⟨Ty.nat, Term.natZero⟩
  | .natSucc predRaw =>
      match Term.infer context predRaw with
      | some ⟨innerTy, innerTerm⟩ =>
          if natEq : innerTy = Ty.nat then
            some ⟨Ty.nat, Term.natSucc (natEq ▸ innerTerm)⟩
          else
            none
      | none => none
  -- Ambiguous forms: defer to check mode
  | .lam _        => none
  -- Function application: synth function (must be `Ty.arrow d c`),
  -- synth argument (must equal `d`), return `c`.
  --
  -- Why non-dep arrow only: dependent Π apps (`appPi`) need the
  -- argument's raw form for the result type (`codomainType.subst0
  -- domainType argRaw`), and our `RawTerm.app` constructor is shared
  -- between non-dep `app` and dep `appPi`.  Without an expected type
  -- to disambiguate, we default to `app`.  The check-mode counterpart
  -- in `Algo/Check.lean` can disambiguate via expected type.
  | .app fnRaw argRaw =>
      match Term.infer context fnRaw with
      | some ⟨.arrow domainType codomainType, fnTerm⟩ =>
          match Term.infer context argRaw with
          | some ⟨argTy, argTerm⟩ =>
              if domainEq : argTy = domainType then
                some ⟨codomainType, Term.app fnTerm (domainEq ▸ argTerm)⟩
              else
                none
          | none => none
      | some ⟨.unit, _⟩ | some ⟨.bool, _⟩ | some ⟨.nat, _⟩
      | some ⟨.piTy _ _, _⟩ | some ⟨.sigmaTy _ _, _⟩
      | some ⟨.tyVar _, _⟩ | some ⟨.id _ _ _, _⟩
      | some ⟨.listType _, _⟩ | some ⟨.optionType _, _⟩
      | some ⟨.eitherType _ _, _⟩ => none
      | none => none
  | .pair _ _     => none  -- pair needs sigmaTy ctor — defer to check
  -- Σ first projection: synth pair (must be `Ty.sigmaTy first second`),
  -- return `first`.
  | .fst pairRaw =>
      match Term.infer context pairRaw with
      | some ⟨.sigmaTy firstType _, pairTerm⟩ =>
          some ⟨firstType, Term.fst pairTerm⟩
      | some ⟨.unit, _⟩ | some ⟨.bool, _⟩ | some ⟨.nat, _⟩
      | some ⟨.arrow _ _, _⟩ | some ⟨.piTy _ _, _⟩
      | some ⟨.tyVar _, _⟩ | some ⟨.id _ _ _, _⟩
      | some ⟨.listType _, _⟩ | some ⟨.optionType _, _⟩
      | some ⟨.eitherType _ _, _⟩ => none
      | none => none
  -- Σ second projection: synth pair (must be `Ty.sigmaTy first second`),
  -- return `second.subst0 first (RawTerm.fst pairRaw)` — the well-typed
  -- result type carries the un-fired raw fst-of-pair (the type is
  -- propositionally equal to `second.subst0 first firstRaw` after a
  -- β-step at the type level; bidirectional check handles equating).
  | .snd pairRaw =>
      match Term.infer context pairRaw with
      | some ⟨.sigmaTy firstType secondType, pairTerm⟩ =>
          some ⟨secondType.subst0 firstType (RawTerm.fst pairRaw),
                Term.snd pairTerm⟩
      | some ⟨.unit, _⟩ | some ⟨.bool, _⟩ | some ⟨.nat, _⟩
      | some ⟨.arrow _ _, _⟩ | some ⟨.piTy _ _, _⟩
      | some ⟨.tyVar _, _⟩ | some ⟨.id _ _ _, _⟩
      | some ⟨.listType _, _⟩ | some ⟨.optionType _, _⟩
      | some ⟨.eitherType _ _, _⟩ => none
      | none => none
  | .boolElim _ _ _   => none
  | .natElim _ _ _    => none
  | .natRec _ _ _     => none
  | .listNil          => none
  | .listCons _ _     => none
  | .listElim _ _ _   => none
  | .optionNone       => none
  | .optionSome _     => none
  | .optionMatch _ _ _ => none
  | .eitherInl _      => none
  | .eitherInr _      => none
  | .eitherMatch _ _ _ => none
  | .refl _           => none
  | .idJ _ _          => none
  | .modIntro _       => none
  | .modElim _        => none
  | .subsume _        => none

end LeanFX2

namespace LeanFX2.Algo

-- TODO Layer 9: Term.check (expected-type bidirectional check)
-- TODO Layer 9: extend Term.infer to listNil/optionNone/etc.
--   (parametric but inferable with elementType erasure)

end LeanFX2.Algo
