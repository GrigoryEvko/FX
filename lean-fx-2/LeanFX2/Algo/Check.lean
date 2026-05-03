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
      | .tyVar _ | .id _ _ _ | .optionType _ | .eitherType _ _
      | .empty | .interval | .path _ _ _ | .glue _ _ | .oeq _ _ _
      | .idStrict _ _ _ | .equiv _ _ | .refine _ _ | .record _
      | .codata _ _ | .session _ | .effect _ _ | .modal _ _
      | .universe _ _ => none
  | .optionNone =>
      match expectedType with
      | .optionType _ => some Term.optionNone
      | .unit | .bool | .nat | .arrow _ _ | .piTy _ _ | .sigmaTy _ _
      | .tyVar _ | .id _ _ _ | .listType _ | .eitherType _ _
      | .empty | .interval | .path _ _ _ | .glue _ _ | .oeq _ _ _
      | .idStrict _ _ _ | .equiv _ _ | .refine _ _ | .record _
      | .codata _ _ | .session _ | .effect _ _ | .modal _ _
      | .universe _ _ => none
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
      | .tyVar _ | .id _ _ _ | .optionType _ | .eitherType _ _
      | .empty | .interval | .path _ _ _ | .glue _ _ | .oeq _ _ _
      | .idStrict _ _ _ | .equiv _ _ | .refine _ _ | .record _
      | .codata _ _ | .session _ | .effect _ _ | .modal _ _
      | .universe _ _ => none
  | .optionSome valueRaw =>
      match expectedType with
      | .optionType elementType =>
          match Term.check context elementType valueRaw with
          | some valueTerm => some (Term.optionSome valueTerm)
          | none => none
      | .unit | .bool | .nat | .arrow _ _ | .piTy _ _ | .sigmaTy _ _
      | .tyVar _ | .id _ _ _ | .listType _ | .eitherType _ _
      | .empty | .interval | .path _ _ _ | .glue _ _ | .oeq _ _ _
      | .idStrict _ _ _ | .equiv _ _ | .refine _ _ | .record _
      | .codata _ _ | .session _ | .effect _ _ | .modal _ _
      | .universe _ _ => none
  | .eitherInl valueRaw =>
      match expectedType with
      | .eitherType leftType _ =>
          match Term.check context leftType valueRaw with
          | some valueTerm => some (Term.eitherInl valueTerm)
          | none => none
      | .unit | .bool | .nat | .arrow _ _ | .piTy _ _ | .sigmaTy _ _
      | .tyVar _ | .id _ _ _ | .listType _ | .optionType _
      | .empty | .interval | .path _ _ _ | .glue _ _ | .oeq _ _ _
      | .idStrict _ _ _ | .equiv _ _ | .refine _ _ | .record _
      | .codata _ _ | .session _ | .effect _ _ | .modal _ _
      | .universe _ _ => none
  | .eitherInr valueRaw =>
      match expectedType with
      | .eitherType _ rightType =>
          match Term.check context rightType valueRaw with
          | some valueTerm => some (Term.eitherInr valueTerm)
          | none => none
      | .unit | .bool | .nat | .arrow _ _ | .piTy _ _ | .sigmaTy _ _
      | .tyVar _ | .id _ _ _ | .listType _ | .optionType _
      | .empty | .interval | .path _ _ _ | .glue _ _ | .oeq _ _ _
      | .idStrict _ _ _ | .equiv _ _ | .refine _ _ | .record _
      | .codata _ _ | .session _ | .effect _ _ | .modal _ _
      | .universe _ _ => none
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
      | .listType _ | .optionType _ | .eitherType _ _
      | .empty | .interval | .path _ _ _ | .glue _ _ | .oeq _ _ _
      | .idStrict _ _ _ | .equiv _ _ | .refine _ _ | .record _
      | .codata _ _ | .session _ | .effect _ _ | .modal _ _
      | .universe _ _ => none
  -- App: synth-then-check fallthrough.  `Term.infer` handles
  -- `RawTerm.app` for non-dep arrows; we then verify the inferred
  -- result type matches the expected type via DecidableEq.
  | .app fnRaw argRaw =>
      match Term.infer context (RawTerm.app fnRaw argRaw) with
      | some ⟨inferredType, inferredTerm⟩ =>
          if typeEq : expectedType = inferredType then
            some (typeEq ▸ inferredTerm)
          else
            none
      | none => none
  -- Σ pair construction: expected type must be `Ty.sigmaTy first second`.
  -- Check first component against `first`, infer the type of the second
  -- component (must equal `second.subst0 first firstRaw`).  This is
  -- check-mode for first (since inferring requires the sigma type),
  -- and synth-mode for second to recover its type.
  | .pair firstRaw secondRaw =>
      match expectedType with
      | .sigmaTy firstType secondType =>
          match Term.check context firstType firstRaw with
          | some firstTerm =>
              match Term.check context (secondType.subst0 firstType firstRaw)
                                       secondRaw with
              | some secondTerm => some (Term.pair firstTerm secondTerm)
              | none => none
          | none => none
      | .unit | .bool | .nat | .arrow _ _ | .piTy _ _ | .tyVar _
      | .id _ _ _ | .listType _ | .optionType _ | .eitherType _ _
      | .empty | .interval | .path _ _ _ | .glue _ _ | .oeq _ _ _
      | .idStrict _ _ _ | .equiv _ _ | .refine _ _ | .record _
      | .codata _ _ | .session _ | .effect _ _ | .modal _ _
      | .universe _ _ => none
  -- Σ first projection: synth-then-check fallthrough via Term.infer.
  | .fst pairRaw =>
      match Term.infer context (RawTerm.fst pairRaw) with
      | some ⟨inferredType, inferredTerm⟩ =>
          if typeEq : expectedType = inferredType then
            some (typeEq ▸ inferredTerm)
          else
            none
      | none => none
  -- Σ second projection: synth-then-check fallthrough.
  | .snd pairRaw =>
      match Term.infer context (RawTerm.snd pairRaw) with
      | some ⟨inferredType, inferredTerm⟩ =>
          if typeEq : expectedType = inferredType then
            some (typeEq ▸ inferredTerm)
          else
            none
      | none => none
  -- Boolean eliminator: motive is the expected type (no separate
  -- elementType to infer).  Check scrutinee at Ty.bool, both branches
  -- at expectedType.
  | .boolElim scrutineeRaw thenRaw elseRaw =>
      match Term.check context Ty.bool scrutineeRaw,
            Term.check context expectedType thenRaw,
            Term.check context expectedType elseRaw with
      | some scrutineeTerm, some thenTerm, some elseTerm =>
          some (Term.boolElim scrutineeTerm thenTerm elseTerm)
      | none, _, _ => none
      | _, none, _ => none
      | _, _, none => none
  -- Nat eliminator (non-dep): motive is the expected type, succBranch
  -- is at `Ty.arrow Ty.nat expectedType`.
  | .natElim scrutineeRaw zeroRaw succRaw =>
      match Term.check context Ty.nat scrutineeRaw,
            Term.check context expectedType zeroRaw,
            Term.check context (Ty.arrow Ty.nat expectedType) succRaw with
      | some scrutineeTerm, some zeroTerm, some succTerm =>
          some (Term.natElim scrutineeTerm zeroTerm succTerm)
      | none, _, _ => none
      | _, none, _ => none
      | _, _, none => none
  -- Nat recursor (non-dep): motive is expected, succBranch at
  -- `Ty.arrow Ty.nat (Ty.arrow expectedType expectedType)`.
  | .natRec scrutineeRaw zeroRaw succRaw =>
      match Term.check context Ty.nat scrutineeRaw,
            Term.check context expectedType zeroRaw,
            Term.check context
              (Ty.arrow Ty.nat (Ty.arrow expectedType expectedType)) succRaw with
      | some scrutineeTerm, some zeroTerm, some succTerm =>
          some (Term.natRec scrutineeTerm zeroTerm succTerm)
      | none, _, _ => none
      | _, none, _ => none
      | _, _, none => none
  -- List eliminator: scrutinee must infer to `Ty.listType elementType`,
  -- which determines the cons branch's parameter type.  Motive is
  -- the expected type.
  | .listElim scrutineeRaw nilRaw consRaw =>
      match Term.infer context scrutineeRaw with
      | some ⟨.listType elementType, scrutineeTerm⟩ =>
          match Term.check context expectedType nilRaw,
                Term.check context
                  (Ty.arrow elementType
                    (Ty.arrow (Ty.listType elementType) expectedType)) consRaw with
          | some nilTerm, some consTerm =>
              some (Term.listElim scrutineeTerm nilTerm consTerm)
          | none, _ => none
          | _, none => none
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
  -- Option matcher: scrutinee must infer to `Ty.optionType elementType`.
  | .optionMatch scrutineeRaw noneRaw someRaw =>
      match Term.infer context scrutineeRaw with
      | some ⟨.optionType elementType, scrutineeTerm⟩ =>
          match Term.check context expectedType noneRaw,
                Term.check context (Ty.arrow elementType expectedType) someRaw with
          | some noneTerm, some someTerm =>
              some (Term.optionMatch scrutineeTerm noneTerm someTerm)
          | none, _ => none
          | _, none => none
      | some ⟨.unit, _⟩ | some ⟨.bool, _⟩ | some ⟨.nat, _⟩
      | some ⟨.arrow _ _, _⟩ | some ⟨.piTy _ _, _⟩
      | some ⟨.sigmaTy _ _, _⟩ | some ⟨.tyVar _, _⟩
      | some ⟨.id _ _ _, _⟩ | some ⟨.listType _, _⟩
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
  -- Either matcher: scrutinee must infer to `Ty.eitherType left right`,
  -- which determines both branch parameter types.
  | .eitherMatch scrutineeRaw leftRaw rightRaw =>
      match Term.infer context scrutineeRaw with
      | some ⟨.eitherType leftType rightType, scrutineeTerm⟩ =>
          match Term.check context (Ty.arrow leftType expectedType) leftRaw,
                Term.check context (Ty.arrow rightType expectedType) rightRaw with
          | some leftTerm, some rightTerm =>
              some (Term.eitherMatch scrutineeTerm leftTerm rightTerm)
          | none, _ => none
          | _, none => none
      | some ⟨.unit, _⟩ | some ⟨.bool, _⟩ | some ⟨.nat, _⟩
      | some ⟨.arrow _ _, _⟩ | some ⟨.piTy _ _, _⟩
      | some ⟨.sigmaTy _ _, _⟩ | some ⟨.tyVar _, _⟩
      | some ⟨.id _ _ _, _⟩ | some ⟨.listType _, _⟩
      | some ⟨.optionType _, _⟩
      | some ⟨.empty, _⟩ | some ⟨.interval, _⟩
      | some ⟨.path _ _ _, _⟩ | some ⟨.glue _ _, _⟩
      | some ⟨.oeq _ _ _, _⟩ | some ⟨.idStrict _ _ _, _⟩
      | some ⟨.equiv _ _, _⟩ | some ⟨.refine _ _, _⟩
      | some ⟨.record _, _⟩ | some ⟨.codata _ _, _⟩
      | some ⟨.session _, _⟩ | some ⟨.effect _ _, _⟩
      | some ⟨.modal _ _, _⟩
      | some ⟨.universe _ _, _⟩ => none
      | none => none
  -- Identity introduction (refl): expected Ty must be `Ty.id carrier
  -- endpointA endpointB` where both endpoints equal `rawWitness`.
  -- That requires endpointA = endpointB (the type carries reflexivity)
  -- AND rawWitness = endpointA.  Two Eq.rec steps cast each endpoint
  -- independently — keeps the cast propext-free (no congrArg₂ tactic).
  | .refl rawWitness =>
      match expectedType with
      | .id carrier endpointA endpointB =>
          if endpointEq : endpointA = endpointB then
            if witnessMatchesA : rawWitness = endpointA then
              let leftEq : rawWitness = endpointA := witnessMatchesA
              let rightEq : rawWitness = endpointB :=
                witnessMatchesA.trans endpointEq
              let baseTerm : Term context (Ty.id carrier rawWitness rawWitness)
                                          (RawTerm.refl rawWitness) :=
                Term.refl carrier rawWitness
              -- Step 1: rewrite RIGHT endpoint via rightEq.
              let withRightCast : Term context
                  (Ty.id carrier rawWitness endpointB) (RawTerm.refl rawWitness) :=
                @Eq.rec (RawTerm _) rawWitness
                  (fun (rightSlot : RawTerm _) _ =>
                    Term context (Ty.id carrier rawWitness rightSlot)
                                 (RawTerm.refl rawWitness))
                  baseTerm endpointB rightEq
              -- Step 2: rewrite LEFT endpoint via leftEq.
              let withBothCasts : Term context
                  (Ty.id carrier endpointA endpointB) (RawTerm.refl rawWitness) :=
                @Eq.rec (RawTerm _) rawWitness
                  (fun (leftSlot : RawTerm _) _ =>
                    Term context (Ty.id carrier leftSlot endpointB)
                                 (RawTerm.refl rawWitness))
                  withRightCast endpointA leftEq
              some withBothCasts
            else none
          else none
      | .unit | .bool | .nat | .arrow _ _ | .piTy _ _ | .sigmaTy _ _
      | .tyVar _ | .listType _ | .optionType _ | .eitherType _ _
      | .empty | .interval | .path _ _ _ | .glue _ _ | .oeq _ _ _
      | .idStrict _ _ _ | .equiv _ _ | .refine _ _ | .record _
      | .codata _ _ | .session _ | .effect _ _ | .modal _ _
      | .universe _ _ => none
  -- J eliminator: expected Ty is the motive.  Synth the witness to
  -- recover its id-type structure (carrier + endpoints), then check
  -- the base case at the motive.
  | .idJ baseRaw witnessRaw =>
      match Term.infer context witnessRaw with
      | some ⟨.id _ _ _, witnessTerm⟩ =>
          match Term.check context expectedType baseRaw with
          | some baseTerm => some (Term.idJ baseTerm witnessTerm)
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
  -- Modal — Layer 1 ships RAW-SIDE SCAFFOLDING ONLY (per Term.lean
  -- comment).  Inner type is preserved across modal markers; checking
  -- delegates to checking the inner raw at the same expected type.
  | .modIntro innerRaw =>
      match Term.check context expectedType innerRaw with
      | some innerTerm => some (Term.modIntro innerTerm)
      | none => none
  | .modElim innerRaw =>
      match Term.check context expectedType innerRaw with
      | some innerTerm => some (Term.modElim innerTerm)
      | none => none
  | .subsume innerRaw =>
      match Term.check context expectedType innerRaw with
      | some innerTerm => some (Term.subsume innerTerm)
      | none => none
  -- D1.6: 27 new RawTerm ctors don't have typed Term counterparts
  -- yet (D1.9 task #1302).  Returning `none` keeps the checker total
  -- and behavioural-equivalent to its pre-D1.6 form on the checkable
  -- subset.  Once D1.9 lands, replace each with the proper typed
  -- check rule.
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

-- TODO Layer 9: Term.check for binders + eliminators
-- TODO Layer 9: synth-then-Conv-check fallthrough

end LeanFX2.Algo
