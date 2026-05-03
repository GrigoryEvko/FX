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
      | some ⟨.eitherType _ _, _⟩
      | some ⟨.empty, _⟩ | some ⟨.interval, _⟩
      | some ⟨.path _ _ _, _⟩ | some ⟨.glue _ _, _⟩
      | some ⟨.oeq _ _ _, _⟩ | some ⟨.idStrict _ _ _, _⟩
      | some ⟨.equiv _ _, _⟩ | some ⟨.refine _ _, _⟩
      | some ⟨.record _, _⟩ | some ⟨.codata _ _, _⟩
      | some ⟨.session _, _⟩ | some ⟨.effect _ _, _⟩
      | some ⟨.modal _ _, _⟩
      | some ⟨.universe _ _, _⟩ => none
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
      | some ⟨.eitherType _ _, _⟩
      | some ⟨.empty, _⟩ | some ⟨.interval, _⟩
      | some ⟨.path _ _ _, _⟩ | some ⟨.glue _ _, _⟩
      | some ⟨.oeq _ _ _, _⟩ | some ⟨.idStrict _ _ _, _⟩
      | some ⟨.equiv _ _, _⟩ | some ⟨.refine _ _, _⟩
      | some ⟨.record _, _⟩ | some ⟨.codata _ _, _⟩
      | some ⟨.session _, _⟩ | some ⟨.effect _ _, _⟩
      | some ⟨.modal _ _, _⟩
      | some ⟨.universe _ _, _⟩ => none
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
      | some ⟨.eitherType _ _, _⟩
      | some ⟨.empty, _⟩ | some ⟨.interval, _⟩
      | some ⟨.path _ _ _, _⟩ | some ⟨.glue _ _, _⟩
      | some ⟨.oeq _ _ _, _⟩ | some ⟨.idStrict _ _ _, _⟩
      | some ⟨.equiv _ _, _⟩ | some ⟨.refine _ _, _⟩
      | some ⟨.record _, _⟩ | some ⟨.codata _ _, _⟩
      | some ⟨.session _, _⟩ | some ⟨.effect _ _, _⟩
      | some ⟨.modal _ _, _⟩
      | some ⟨.universe _ _, _⟩ => none
      | none => none
  | .boolElim _ _ _   => none
  | .natElim _ _ _    => none
  | .natRec _ _ _     => none
  | .listNil          => none  -- needs expected element type
  -- listCons: infer the head's type, then synthesize tail at
  -- listType of that head type.  When both succeed AND tail's
  -- inferred type is `listType elementType`, build listCons.
  | .listCons headRaw tailRaw =>
      match Term.infer context headRaw with
      | some ⟨elementType, headTerm⟩ =>
          match Term.infer context tailRaw with
          | some ⟨.listType tailElementType, tailTerm⟩ =>
              if elementEq : tailElementType = elementType then
                some ⟨Ty.listType elementType,
                      Term.listCons headTerm (elementEq ▸ tailTerm)⟩
              else
                none
          | some ⟨.unit, _⟩ | some ⟨.bool, _⟩ | some ⟨.nat, _⟩
          | some ⟨.arrow _ _, _⟩ | some ⟨.piTy _ _, _⟩
          | some ⟨.sigmaTy _ _, _⟩ | some ⟨.tyVar _, _⟩
          | some ⟨.id _ _ _, _⟩ | some ⟨.optionType _, _⟩
          | some ⟨.eitherType _ _, _⟩
          | some ⟨.empty, _⟩ | some ⟨.interval, _⟩
          | some ⟨.path _ _ _, _⟩ | some ⟨.glue _ _, _⟩
          | some ⟨.oeq _ _ _, _⟩ | some ⟨.idStrict _ _ _, _⟩
          | some ⟨.equiv _ _, _⟩ | some ⟨.refine _ _, _⟩
          | some ⟨.record _, _⟩ | some ⟨.codata _ _, _⟩
          | some ⟨.session _, _⟩ | some ⟨.effect _ _, _⟩
          | some ⟨.modal _ _, _⟩
          | some ⟨.universe _ _, _⟩ => none
          | none => none
      | none => none
  | .listElim _ _ _   => none
  | .optionNone       => none  -- needs expected element type
  -- optionSome: infer the inner value's type, build optionSome.
  -- Always inferable when the inner term is.
  | .optionSome valueRaw =>
      match Term.infer context valueRaw with
      | some ⟨elementType, valueTerm⟩ =>
          some ⟨Ty.optionType elementType, Term.optionSome valueTerm⟩
      | none => none
  | .optionMatch _ _ _ => none
  | .eitherInl _      => none  -- ambiguous: rightType free
  | .eitherInr _      => none  -- ambiguous: leftType free
  | .eitherMatch _ _ _ => none
  | .refl _           => none  -- needs expected Ty.id carrier endpts
  -- J eliminator: synth witness (must be Ty.id _ _ _), synth base
  -- (gives motive), build idJ.
  | .idJ baseRaw witnessRaw =>
      match Term.infer context witnessRaw with
      | some ⟨.id _ _ _, witnessTerm⟩ =>
          match Term.infer context baseRaw with
          | some ⟨motiveType, baseTerm⟩ =>
              some ⟨motiveType, Term.idJ baseTerm witnessTerm⟩
          | none => none
      | some ⟨.unit, _⟩ | some ⟨.bool, _⟩ | some ⟨.nat, _⟩
      | some ⟨.arrow _ _, _⟩ | some ⟨.piTy _ _, _⟩
      | some ⟨.sigmaTy _ _, _⟩ | some ⟨.tyVar _, _⟩
      | some ⟨.listType _, _⟩ | some ⟨.optionType _, _⟩
      | some ⟨.eitherType _ _, _⟩
      | some ⟨.empty, _⟩ | some ⟨.interval, _⟩
      | some ⟨.path _ _ _, _⟩ | some ⟨.glue _ _, _⟩
      | some ⟨.oeq _ _ _, _⟩ | some ⟨.idStrict _ _ _, _⟩
      | some ⟨.equiv _ _, _⟩ | some ⟨.refine _ _, _⟩
      | some ⟨.record _, _⟩ | some ⟨.codata _ _, _⟩
      | some ⟨.session _, _⟩ | some ⟨.effect _ _, _⟩
      | some ⟨.modal _ _, _⟩
      | some ⟨.universe _ _, _⟩ => none
      | none => none
  -- Modal markers preserve inner type — synth the inner.
  | .modIntro innerRaw =>
      match Term.infer context innerRaw with
      | some ⟨innerType, innerTerm⟩ =>
          some ⟨innerType, Term.modIntro innerTerm⟩
      | none => none
  | .modElim innerRaw =>
      match Term.infer context innerRaw with
      | some ⟨innerType, innerTerm⟩ =>
          some ⟨innerType, Term.modElim innerTerm⟩
      | none => none
  | .subsume innerRaw =>
      match Term.infer context innerRaw with
      | some ⟨innerType, innerTerm⟩ =>
          some ⟨innerType, Term.subsume innerTerm⟩
      | none => none
  -- D1.6: 27 new RawTerm ctors do not have typed Term counterparts
  -- yet (D1.9 task #1302).  Return `none` so the inferrer is total
  -- and behavioural-equivalent to its pre-D1.6 form on the inferable
  -- subset.  Once D1.9 lands, replace each with the proper typed
  -- inference rule.
  | .interval0          => none
  | .interval1          => none
  | .intervalOpp _      => none
  | .intervalMeet _ _   => none
  | .intervalJoin _ _   => none
  | .pathLam _          => none
  | .pathApp _ _        => none
  | .glueIntro _ _      => none
  | .glueElim _         => none
  | .transp _ _         => none
  | .hcomp _ _          => none
  | .oeqRefl _          => none
  | .oeqJ _ _           => none
  | .oeqFunext _        => none
  | .idStrictRefl _     => none
  | .idStrictRec _ _    => none
  | .equivIntro _ _     => none
  | .equivApp _ _       => none
  | .refineIntro _ _    => none
  | .refineElim _       => none
  | .recordIntro _      => none
  | .recordProj _       => none
  | .codataUnfold _ _   => none
  | .codataDest _       => none
  | .sessionSend _ _    => none
  | .sessionRecv _      => none
  | .effectPerform _ _  => none
  | .universeCode _     => none

end LeanFX2

namespace LeanFX2.Algo

-- TODO Layer 9: Term.check (expected-type bidirectional check)
-- TODO Layer 9: extend Term.infer to listNil/optionNone/etc.
--   (parametric but inferable with elementType erasure)

end LeanFX2.Algo
