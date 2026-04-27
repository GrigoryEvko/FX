import FX.Kernel.Term

/-!
# De Bruijn substitution

Per `fx_design.md` §31.3 (de Bruijn indices internally).

Three operations:

  * `Term.shift cutoffIndex shiftAmount termBeingWalked` — lift every
    free variable `encounteredVarIndex ≥ cutoffIndex` in the walked
    term by `shiftAmount`.  Used when a term crosses a new binder.
  * `Term.subst substitutionIndex replacementTerm termBeingWalked` —
    substitute `replacementTerm` for variable `substitutionIndex` in
    the walked term, shifting the replacement under each binder
    crossed.  Free variables above `substitutionIndex` are decremented
    by 1 (to keep indices consistent after the substituted binder is
    removed).
  * `Term.openWith replacementTerm termBeingWalked` — substitute the
    replacement for variable `0` in the walked term.  This is the
    canonical "apply a function's body to an argument" operation:
    `openWith replacementTerm termBeingWalked ==
     subst 0 replacementTerm termBeingWalked`.

Conventions:

  * de Bruijn **indices** (not levels): `var 0` is the nearest
    binder, `var 1` the next, and so on.  This means shifting
    happens on indices ≥ cutoffIndex (not > cutoffIndex) — variables
    *at* the cutoff also shift, because new binders introduced above
    them move them further from scope.
  * Substitution is capture-avoiding by construction: when we
    recurse under a `lam`/`pi`/`sigma` binder, we increment the
    substitution index and shift the replacement term up by 1.
  * These are total functions.  Every `Term` constructor is
    handled — `ind`/`coind` spec payloads are `Unit` at Phase 2,
    so there are no sub-terms inside them to rewrite.

Zero `axiom`, zero `sorry`.  Every identity we need downstream
(shift-by-0, subst-no-op on closed terms, open-close round-trip)
is a theorem provable by structural induction.
-/

namespace FX.Kernel

namespace Term

/-! ## Shift -/

/- Lift every free variable `encounteredVarIndex ≥ cutoffIndex` by
   `shiftAmount`.  Variables below the cutoff (bound by binders we
   are currently inside) are unchanged.  Uses structural mutual
   recursion with `shiftList` so `simp [shift]` reduces correctly
   through `ind`/`ctor`/`indRec` sub-term lists. -/

mutual

def shift (cutoffIndex : Nat) (shiftAmount : Nat) : Term → Term
  | var encounteredVarIndex =>
    if encounteredVarIndex < cutoffIndex then var encounteredVarIndex
    else var (encounteredVarIndex + shiftAmount)
  | app funTerm argTerm =>
    app (shift cutoffIndex shiftAmount funTerm)
        (shift cutoffIndex shiftAmount argTerm)
  | lam binderGrade binderType bodyUnderBinder =>
    lam binderGrade (shift cutoffIndex shiftAmount binderType)
        (shift (cutoffIndex + 1) shiftAmount bodyUnderBinder)
  | pi binderGrade binderType bodyUnderBinder returnEffect =>
    pi binderGrade (shift cutoffIndex shiftAmount binderType)
       (shift (cutoffIndex + 1) shiftAmount bodyUnderBinder)
       returnEffect
  | sigma binderGrade binderType bodyUnderBinder =>
    sigma binderGrade (shift cutoffIndex shiftAmount binderType)
          (shift (cutoffIndex + 1) shiftAmount bodyUnderBinder)
  | type universeLevel => type universeLevel
  | const declName => const declName
  | forallLevel bodyTerm =>
    -- Level binders are orthogonal to term-level de Bruijn;
    -- the term-var cutoff passes through unchanged.  Level
    -- scope increments at typing time via
    -- `TypingContext.extendLevel`, not here.
    forallLevel (shift cutoffIndex shiftAmount bodyTerm)
  | ind indName indArgs =>
    ind indName (shiftList cutoffIndex shiftAmount indArgs)
  | ctor ctorName ctorIndex typeArgs valueArgs =>
    ctor ctorName ctorIndex
      (shiftList cutoffIndex shiftAmount typeArgs)
      (shiftList cutoffIndex shiftAmount valueArgs)
  | indRec recName motiveTerm methodTerms targetTerm =>
    indRec recName (shift cutoffIndex shiftAmount motiveTerm)
      (shiftList cutoffIndex shiftAmount methodTerms)
      (shift cutoffIndex shiftAmount targetTerm)
  | coind typeName typeArgs =>
    coind typeName (shiftList cutoffIndex shiftAmount typeArgs)
  | coindUnfold typeName typeArgs arms =>
    -- No self-binder: arms live in the same de Bruijn scope as
    -- the enclosing `coindUnfold`.  Shift typeArgs and arms
    -- pointwise at the outer cutoff — parallel to `ctor`.
    coindUnfold typeName
      (shiftList cutoffIndex shiftAmount typeArgs)
      (shiftList cutoffIndex shiftAmount arms)
  | coindDestruct typeName destructorIndex targetTerm =>
    coindDestruct typeName destructorIndex
      (shift cutoffIndex shiftAmount targetTerm)
  | id idType leftTerm rightTerm =>
    id (shift cutoffIndex shiftAmount idType)
       (shift cutoffIndex shiftAmount leftTerm)
       (shift cutoffIndex shiftAmount rightTerm)
  | refl witnessTerm =>
    refl (shift cutoffIndex shiftAmount witnessTerm)
  | idJ motiveTerm baseTerm eqProofTerm =>
    idJ (shift cutoffIndex shiftAmount motiveTerm)
        (shift cutoffIndex shiftAmount baseTerm)
        (shift cutoffIndex shiftAmount eqProofTerm)
  | quot quotType quotRel =>
    quot (shift cutoffIndex shiftAmount quotType)
         (shift cutoffIndex shiftAmount quotRel)
  | quotMk relationTerm witnessTerm =>
    quotMk (shift cutoffIndex shiftAmount relationTerm)
           (shift cutoffIndex shiftAmount witnessTerm)
  | quotLift liftedTerm respectsTerm targetTerm =>
    quotLift (shift cutoffIndex shiftAmount liftedTerm)
             (shift cutoffIndex shiftAmount respectsTerm)
             (shift cutoffIndex shiftAmount targetTerm)

def shiftList (cutoffIndex : Nat) (shiftAmount : Nat)
    : List Term → List Term
  | []        => []
  | walkedTerm :: remainingTerms =>
    shift cutoffIndex shiftAmount walkedTerm
      :: shiftList cutoffIndex shiftAmount remainingTerms

end

/-! ## Substitution -/

/- Substitute `replacementTerm` for variable `substitutionIndex` in
   the walked term.  Structural mutual recursion with `substList`
   for sub-term lists.

   * If we meet `var encounteredVarIndex` matching the substitution
     index, the entire replacement is inserted — but the replacement
     was constructed outside the binders we have crossed, so it must
     be shifted up to match the current scope.
   * If we meet `var encounteredVarIndex` with the index greater than
     `substitutionIndex`, the substituted slot is about to be
     removed, so the encountered variable becomes
     `var (encounteredVarIndex - 1)` to keep downstream references
     correct.
   * If the encountered index is below the substitution index,
     leave it. -/

mutual

def subst (substitutionIndex : Nat) (replacementTerm : Term)
    : Term → Term
  | var encounteredVarIndex =>
    if encounteredVarIndex = substitutionIndex then
      shift 0 substitutionIndex replacementTerm
    else if encounteredVarIndex > substitutionIndex then
      var (encounteredVarIndex - 1)
    else var encounteredVarIndex
  | app funTerm argTerm =>
    app (subst substitutionIndex replacementTerm funTerm)
        (subst substitutionIndex replacementTerm argTerm)
  | lam binderGrade binderType bodyUnderBinder =>
    lam binderGrade
      (subst substitutionIndex replacementTerm binderType)
      (subst (substitutionIndex + 1) replacementTerm bodyUnderBinder)
  | pi binderGrade binderType bodyUnderBinder returnEffect =>
    pi binderGrade
      (subst substitutionIndex replacementTerm binderType)
      (subst (substitutionIndex + 1) replacementTerm bodyUnderBinder)
      returnEffect
  | sigma binderGrade binderType bodyUnderBinder =>
    sigma binderGrade
      (subst substitutionIndex replacementTerm binderType)
      (subst (substitutionIndex + 1) replacementTerm bodyUnderBinder)
  | type universeLevel => type universeLevel
  | const declName => const declName
  | forallLevel bodyTerm =>
    forallLevel (subst substitutionIndex replacementTerm bodyTerm)
  | ind indName indArgs =>
    ind indName (substList substitutionIndex replacementTerm indArgs)
  | ctor ctorName ctorIndex typeArgs valueArgs =>
    ctor ctorName ctorIndex
      (substList substitutionIndex replacementTerm typeArgs)
      (substList substitutionIndex replacementTerm valueArgs)
  | indRec recName motiveTerm methodTerms targetTerm =>
    indRec recName
      (subst substitutionIndex replacementTerm motiveTerm)
      (substList substitutionIndex replacementTerm methodTerms)
      (subst substitutionIndex replacementTerm targetTerm)
  | coind typeName typeArgs =>
    coind typeName (substList substitutionIndex replacementTerm typeArgs)
  | coindUnfold typeName typeArgs arms =>
    coindUnfold typeName
      (substList substitutionIndex replacementTerm typeArgs)
      (substList substitutionIndex replacementTerm arms)
  | coindDestruct typeName destructorIndex targetTerm =>
    coindDestruct typeName destructorIndex
      (subst substitutionIndex replacementTerm targetTerm)
  | id idType leftTerm rightTerm =>
    id (subst substitutionIndex replacementTerm idType)
       (subst substitutionIndex replacementTerm leftTerm)
       (subst substitutionIndex replacementTerm rightTerm)
  | refl witnessTerm =>
    refl (subst substitutionIndex replacementTerm witnessTerm)
  | idJ motiveTerm baseTerm eqProofTerm =>
    idJ (subst substitutionIndex replacementTerm motiveTerm)
        (subst substitutionIndex replacementTerm baseTerm)
        (subst substitutionIndex replacementTerm eqProofTerm)
  | quot quotType quotRel =>
    quot (subst substitutionIndex replacementTerm quotType)
         (subst substitutionIndex replacementTerm quotRel)
  | quotMk relationTerm witnessTerm =>
    quotMk (subst substitutionIndex replacementTerm relationTerm)
           (subst substitutionIndex replacementTerm witnessTerm)
  | quotLift liftedTerm respectsTerm targetTerm =>
    quotLift (subst substitutionIndex replacementTerm liftedTerm)
             (subst substitutionIndex replacementTerm respectsTerm)
             (subst substitutionIndex replacementTerm targetTerm)

def substList (substitutionIndex : Nat) (replacementTerm : Term)
    : List Term → List Term
  | []        => []
  | walkedTerm :: remainingTerms =>
    subst substitutionIndex replacementTerm walkedTerm
      :: substList substitutionIndex replacementTerm remainingTerms

end

/-! ## Open -/

/--
Open a binder with a term.
`openWith replacementTerm bodyUnderBinder =
 subst 0 replacementTerm bodyUnderBinder`.

This is the beta-rule's substitution step:
`app (lam _ _ bodyUnderBinder) replacementTerm` reduces to
`openWith replacementTerm bodyUnderBinder`.
-/
def openWith (replacementTerm : Term) (termBeingWalked : Term) : Term :=
  subst 0 replacementTerm termBeingWalked

/-!
Instantiate a parameterized spec's constructor arg type (or
return type) with concrete type arguments.  `substParams
typeArgs t` substitutes each `typeArgs[i]` for the binder `var
i` in the spec-param telescope scope that `t` was built under.

Convention: spec params are bound in declaration order, so with
params `[a, b]` the ctor-arg scope has `var 0 = b` (innermost
binder, second param) and `var 1 = a` (outer binder, first
param).  `typeArgs` are passed IN param-declaration order —
`typeArgs[0] = a`, `typeArgs[1] = b`.

The fold applies `openWith` on `typeArgs.reverse`: innermost
first (substituting `var 0`), then outer (substituting what
becomes the new `var 0` after the first open's shift).  After
N opens, all N params have been substituted and the term lives
in the enclosing scope (no longer mentioning the spec params).

Used by `Typing.lean` at `.ind`, `.ctor`, `.indRec` rules to
thread type arguments into the spec's declared arg types (A10
follow-up for parameterized inductives).  Preserves §H.4
Ind-form/intro/elim shape — no kernel axiom change.
-/
def substParams (typeArgs : List Term) (t : Term) : Term :=
  typeArgs.reverse.foldl (fun acc arg => openWith arg acc) t

/-! ## Free-variable probe

`mentionsVar targetIndex term` is `true` iff `term` contains a
free reference to the de Bruijn variable `targetIndex`.
Accounts for binders: under a `lam`/`pi`/`sigma` body, the
target is bumped by 1 to follow the de Bruijn shift.

Used by Pi-η in `FX/Kernel/Conversion.lean`: a lambda body
`app headF (var 0)` is η-reducible iff `headF` does not mention
the outer-scope `var 0`.  A generic free-variable check is also
useful for future tasks (A9 linearity checking, dead-code
analysis), so `mentionsVar` lives in the shared Substitution
module rather than being private to Conversion.

Zero `axiom`, zero `sorry`.  Structural recursion mutual with
`mentionsVarList` for sub-term lists inside
`ind`/`ctor`/`indRec`. -/

mutual

def mentionsVar (targetIndex : Nat) : Term → Bool
  | var encounteredVarIndex => encounteredVarIndex = targetIndex
  | app funTerm argTerm =>
    mentionsVar targetIndex funTerm || mentionsVar targetIndex argTerm
  | lam _grade domainTerm bodyTerm =>
    mentionsVar targetIndex domainTerm
      || mentionsVar (targetIndex + 1) bodyTerm
  | pi _grade domainTerm bodyTerm _returnEffect =>
    mentionsVar targetIndex domainTerm
      || mentionsVar (targetIndex + 1) bodyTerm
  | sigma _grade domainTerm bodyTerm =>
    mentionsVar targetIndex domainTerm
      || mentionsVar (targetIndex + 1) bodyTerm
  | type _universeLevel => false
  | const _declName     => false
  | forallLevel bodyTerm => mentionsVar targetIndex bodyTerm
  | coind _coindName coindArgs =>
    mentionsVarList targetIndex coindArgs
  | coindUnfold _typeName typeArgs arms =>
    mentionsVarList targetIndex typeArgs
      || mentionsVarList targetIndex arms
  | coindDestruct _typeName _destructorIndex targetTerm =>
    mentionsVar targetIndex targetTerm
  | ind _typeName typeArgs =>
    mentionsVarList targetIndex typeArgs
  | ctor _typeName _ctorIndex typeArgs valueArgs =>
    mentionsVarList targetIndex typeArgs
      || mentionsVarList targetIndex valueArgs
  | indRec _typeName motiveTerm methodTerms targetTerm =>
    mentionsVar targetIndex motiveTerm
      || mentionsVarList targetIndex methodTerms
      || mentionsVar targetIndex targetTerm
  | id idType leftTerm rightTerm =>
    mentionsVar targetIndex idType
      || mentionsVar targetIndex leftTerm
      || mentionsVar targetIndex rightTerm
  | refl witnessTerm => mentionsVar targetIndex witnessTerm
  | idJ motiveTerm baseTerm eqProofTerm =>
    mentionsVar targetIndex motiveTerm
      || mentionsVar targetIndex baseTerm
      || mentionsVar targetIndex eqProofTerm
  | quot carrierTerm relationTerm =>
    mentionsVar targetIndex carrierTerm
      || mentionsVar targetIndex relationTerm
  | quotMk relationTerm witnessTerm =>
    mentionsVar targetIndex relationTerm
      || mentionsVar targetIndex witnessTerm
  | quotLift liftedTerm respectsTerm targetProofTerm =>
    mentionsVar targetIndex liftedTerm
      || mentionsVar targetIndex respectsTerm
      || mentionsVar targetIndex targetProofTerm

def mentionsVarList (targetIndex : Nat) : List Term → Bool
  | []                       => false
  | headTerm :: remainingTerms =>
    mentionsVar targetIndex headTerm
      || mentionsVarList targetIndex remainingTerms

end

/-! ## Runtime-usage counting (linearity / Pi-intro exit check)

`countVarAt targetIndex term` counts how many times `var targetIndex`
appears in `term`'s **runtime-relevant** positions — the semiring
sum of occurrences, treating type-position subterms as erased
(per `fx_design.md` §1.5 compile-time erasure).

The distinction matters because the Pi-intro exit check (`A9`
linearity enforcement) compares the counted usage against the
binder's declared grade.  A variable referenced only in a type
annotation (e.g., the inner `lam`'s domain in `λ(a : type). λ(x
: a). x`) does not consume the binding at runtime and so must
not inflate the count.

## Type-vs-value classification

Per §31.2 and Appendix H, these constructors are **type-formers**
and their subterms are all types — they contribute `zero` to the
runtime-usage count:

  * `type u`            — universe
  * `pi g A B`           — dependent function type
  * `sigma g A B`        — dependent pair type
  * `forallLevel body`   — universe-polymorphic type
  * `ind typeName args`  — inductive type applied to params
  * `coind specRef`      — codata type
  * `id T a b`           — identity type
  * `quot T R`           — quotient type

These constructors have subterms in **value position** — their
subterms' usage sums:

  * `var i`              — single-occurrence witness
  * `app f a`            — function and argument both value
  * `ctor _ _ typeArgs ctorArgs`  — `ctorArgs` are value payload
                                     (typeArgs erase)
  * `indRec _ motive methods target` — motive erases (is a type
                                         function); methods and
                                         target are value
  * `refl w`             — witness is value
  * `idJ motive b e`     — motive erases; base and eq are value
  * `quotMk rel w`       — relation erases; witness is value
  * `quotLift f p t`     — all three are value terms

The `lam` constructor has a mixed role: the domain is a type
(erases) and the body is a value (counts, shifted by +1 for
the new binder).  `const n` has no subterms — counts `zero`.

## Branch semantics — JOIN not SUM

`indRec`'s methods are branches — only one arm executes at
runtime per target-scrutinee value.  A binding used once in
each of two arms is consumed once in total, not twice, so the
branch-arm combinator is `Usage.join` (lattice max), not
`Usage.add` (semiring sum).  Without this distinction the
elaborated form of `match n ; Zero => m; Succ(k) => ... m ...`
would count `m` as `one + one = omega`, spuriously rejecting
any linear binding that's used in multiple arms — including
everyday pattern-matched code.

Two list-fold helpers:

  * `countVarAtList` — SUM over value-position lists (ctor
    payloads, `quotLift` arg triples); the elements compose
    sequentially at runtime.
  * `countVarAtJoinList` — JOIN over branch-alternative lists
    (`indRec` methods); only one element executes at runtime.

## Termination

Structural recursion, mutual with `countVarAtList` /
`countVarAtJoinList` for the list cases.  Zero `axiom`, zero
`sorry`, zero `partial`. -/

mutual

def countVarAt (targetIndex : Nat) : Term → Usage
  | var encounteredVarIndex =>
    if encounteredVarIndex = targetIndex then Usage.one else Usage.zero
  | type _universeLevel   => Usage.zero
  | const _declName       => Usage.zero
  | coind _coindName _coindArgs => Usage.zero  -- type-former
  | coindUnfold _typeName _typeArgs arms =>
    -- Unfold arms are branch alternatives in the same sense as
    -- `indRec` methods — each destructor observation fires ONE
    -- arm at a time, so per-observation usage is the JOIN of
    -- arm costs (lattice max), not the SUM.  The multi-
    -- observation case (firing `head` then `tail` on the same
    -- value) is bounded by the Size dimension (§3.5 / §6.3
    -- dim 20) at typing time and is not surfaced here.
    countVarAtJoinList targetIndex arms
  | coindDestruct _typeName _destructorIndex targetTerm =>
    -- Destructor call consumes its target exactly once per
    -- firing; target is the only value-position subterm.
    countVarAt targetIndex targetTerm
  | forallLevel bodyTerm  => countVarAt targetIndex bodyTerm
  | app funcTerm argTerm  =>
    Usage.add (countVarAt targetIndex funcTerm) (countVarAt targetIndex argTerm)
  | lam _grade _domainTerm bodyTerm =>
    -- Domain is a type (erases); body shifts past the new binder.
    countVarAt (targetIndex + 1) bodyTerm
  | pi _grade _domainTerm _bodyTerm _returnEffect => Usage.zero  -- type-former
  | sigma _grade _domainTerm _bodyTerm => Usage.zero  -- type-former
  | ind _typeName _typeArgs           => Usage.zero  -- type-former
  | ctor _typeName _ctorIndex _typeArgs ctorArgs =>
    -- Ctor payload args are sequential (all executed at runtime).
    countVarAtList targetIndex ctorArgs
  | indRec _typeName _motiveTerm methodTerms targetTerm =>
    -- Methods are branches (only one runs per target-value);
    -- join them.  Target is evaluated to pick the method; sum
    -- the target's usage with the arm-join result.
    Usage.add (countVarAtJoinList targetIndex methodTerms)
              (countVarAt targetIndex targetTerm)
  | id _idType _leftTerm _rightTerm   => Usage.zero  -- type-former
  | refl witnessTerm                   => countVarAt targetIndex witnessTerm
  | idJ _motiveTerm baseTerm eqProofTerm =>
    Usage.add (countVarAt targetIndex baseTerm)
              (countVarAt targetIndex eqProofTerm)
  | quot _carrierTerm _relationTerm    => Usage.zero  -- type-former
  | quotMk _relationTerm witnessTerm   => countVarAt targetIndex witnessTerm
  | quotLift liftedTerm respectsTerm targetProofTerm =>
    Usage.add (countVarAt targetIndex liftedTerm)
      (Usage.add (countVarAt targetIndex respectsTerm)
                 (countVarAt targetIndex targetProofTerm))

def countVarAtList (targetIndex : Nat) : List Term → Usage
  | []                       => Usage.zero
  | headTerm :: remainingTerms =>
    Usage.add (countVarAt targetIndex headTerm)
              (countVarAtList targetIndex remainingTerms)

def countVarAtJoinList (targetIndex : Nat) : List Term → Usage
  | []                       => Usage.zero
  | headTerm :: remainingTerms =>
    Usage.join (countVarAt targetIndex headTerm)
               (countVarAtJoinList targetIndex remainingTerms)

end

/-! ## Lemmas -/

/- `shift cutoffIndex 0` is the identity — shifting by zero changes
   nothing.

   Because `Term` is a nested inductive (carries `List Term`
   inside `ind`/`ctor`/`indRec`), we can't use the default
   `induction` tactic.  Instead we do structural recursion via
   mutual recursion with `shift_zero_list`, a helper about
   `List.map (shift cutoffIndex 0) = id`. -/

mutual

theorem shift_zero (cutoffIndex : Nat) (termBeingWalked : Term)
    : shift cutoffIndex 0 termBeingWalked = termBeingWalked := by
  match termBeingWalked with
  | .var encounteredVarIndex => simp [shift]
  | .app funTerm argTerm =>
    simp [shift, shift_zero cutoffIndex funTerm,
      shift_zero cutoffIndex argTerm]
  | .lam binderGrade binderType bodyUnderBinder =>
    simp [shift, shift_zero cutoffIndex binderType,
      shift_zero (cutoffIndex + 1) bodyUnderBinder]
  | .pi binderGrade binderType bodyUnderBinder returnEffect =>
    simp [shift, shift_zero cutoffIndex binderType,
      shift_zero (cutoffIndex + 1) bodyUnderBinder]
  | .sigma binderGrade binderType bodyUnderBinder =>
    simp [shift, shift_zero cutoffIndex binderType,
      shift_zero (cutoffIndex + 1) bodyUnderBinder]
  | .type universeLevel => simp [shift]
  | .const declName => simp [shift]
  | .forallLevel bodyTerm =>
    simp [shift, shift_zero cutoffIndex bodyTerm]
  | .ind indName indArgs =>
    simp [shift, shift_zero_list cutoffIndex indArgs]
  | .ctor ctorName ctorIndex typeArgs valueArgs =>
    simp [shift, shift_zero_list cutoffIndex typeArgs,
      shift_zero_list cutoffIndex valueArgs]
  | .indRec recName motiveTerm methodTerms targetTerm =>
    simp [shift, shift_zero cutoffIndex motiveTerm,
      shift_zero_list cutoffIndex methodTerms,
      shift_zero cutoffIndex targetTerm]
  | .coind coindName coindArgs =>
    simp [shift, shift_zero_list cutoffIndex coindArgs]
  | .coindUnfold typeName typeArgs arms =>
    simp [shift, shift_zero_list cutoffIndex typeArgs,
      shift_zero_list cutoffIndex arms]
  | .coindDestruct typeName destructorIndex targetTerm =>
    simp [shift, shift_zero cutoffIndex targetTerm]
  | .id idType leftTerm rightTerm =>
    simp [shift, shift_zero cutoffIndex idType,
      shift_zero cutoffIndex leftTerm,
      shift_zero cutoffIndex rightTerm]
  | .refl witnessTerm =>
    simp [shift, shift_zero cutoffIndex witnessTerm]
  | .idJ motiveTerm baseTerm eqProofTerm =>
    simp [shift, shift_zero cutoffIndex motiveTerm,
      shift_zero cutoffIndex baseTerm,
      shift_zero cutoffIndex eqProofTerm]
  | .quot quotType quotRel =>
    simp [shift, shift_zero cutoffIndex quotType,
      shift_zero cutoffIndex quotRel]
  | .quotMk relationTerm witnessTerm =>
    simp [shift, shift_zero cutoffIndex relationTerm,
      shift_zero cutoffIndex witnessTerm]
  | .quotLift liftedTerm respectsTerm targetTerm =>
    simp [shift, shift_zero cutoffIndex liftedTerm,
      shift_zero cutoffIndex respectsTerm,
      shift_zero cutoffIndex targetTerm]

theorem shift_zero_list (cutoffIndex : Nat) (walkedTerms : List Term)
    : shiftList cutoffIndex 0 walkedTerms = walkedTerms := by
  match walkedTerms with
  | [] => simp [shiftList]
  | walkedTerm :: remainingTerms =>
    simp [shiftList, shift_zero cutoffIndex walkedTerm,
      shift_zero_list cutoffIndex remainingTerms]

end

end Term

end FX.Kernel
