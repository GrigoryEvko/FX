import FX1Poly.Core.RawTermSubst0

/-! # Foundation/PolyCell/Core/Step — single-step reduction on V2

The `Step` inductive relation per polycell.md §11.6.1: beta + uniform
cong + iota covering all standard inductive types (bool / nat / list /
option / either / pair / identity).  Eta lives in the `Step.eta` sibling
inductive in `StepEta.lean`.

Five iota SHAPES; sixteen iota constructors total:

  * SHAPE 1 (branch-selection): bool×2, nat zero×2, list nil,
    option none, idJ refl, idStrictRec refl -- 8 ctors
  * SHAPE 2 (content-projection): pair fst, pair snd -- 2 ctors
  * SHAPE 3 (1-arg app-chain build): option some, either inl/inr -- 3
  * SHAPE 4 (SUBSTITUTING w/ recursive call): natElim/natRec
    on natSucc -- 2 ctors
  * SHAPE 5 (3-arg app-chain w/ recursive call): listElim on
    listCons -- 1 ctor

## The iota shapes in detail

* **SHAPE 1 (branch-selection)** for boolElim / nat-zero / list-nil /
  option-none / idJ-refl / idStrictRec-refl: pure tag-selection at the
  same scope.  Bool's two-ctor scheme + zero binders is the simplest
  case.  For identity elimination the substrate gives idJ arity 2
  (baseCase, witness) with no explicit motive child, so the iota just
  returns the base case when the witness is `refl`; motive and
  dependent-elimination semantics live in the PROFILE layer.
* **SHAPE 2 (content-projection)** for `fst`/`snd` on `pair`: the
  eliminator unwraps a constructor and returns one of its components
  rather than selecting one of several branches.
* **SHAPE 3 (1-arg app-chain build)** for `iotaOptionMatchSome` /
  `iotaEitherMatchInl` / `iotaEitherMatchInr`: the reduct is
  `app branch wrappedValue` rather than just `branch`.  No direct
  substitution at iota -- beta handles the binding work in a subsequent
  reduction.
* **SHAPE 4 (SUBSTITUTING iota with recursive call)** for
  `iotaNatElimSucc` / `iotaNatRecSucc`: the reduct SUBSTITUTES into the
  succ-branch (which lives under TWO binders at `scope + 2`): `var 0`
  (innermost = the inductive hypothesis) is replaced by `recursiveCall`
  (the original eliminator applied to the predecessor, threading the
  same motive/branches) and `var 1` is replaced by `predecessor`.  This
  is the substrate's FIRST substituting iota (beta is the only prior
  substitution rule).  Historic change: the succ-iota used to build an
  app-chain `app (app succBranch predecessor) recursiveCall`; the
  Phase-Z motive shape moves to direct substitution so dependent nat
  elimination is syntax-directed with the IH/predecessor pinned by de
  Bruijn position.  This shape gives induction principles their
  inductive power -- the recursive call appears as the substituent for
  `var 0` that subsequent reductions fold down.
* **SHAPE 5 (3-arg app-chain with recursive call)** for
  `iotaListElimCons`: a triple-nested app `app (app (app consBranch
  head) tail) (listElim tail nil cons)` -- one curried argument per
  piece of the cons payload (head + tail) plus the recursive call.

Subject reduction, confluence, strong normalization, and decidable Conv
build on this relation together with `RawTerm.subst0`.

## The beta-reduction rule

The beta constructor:

  Step (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
            (.childCons arg .childNil)))
       (RawTerm.subst0 body arg)

Textbook lambda calculus beta rule, formulated over V2's un-indexed
raw substrate.  Church-style: the lambda carries its domain annotation
as a first (shift-`0`) child; contraction discards the annotation.

## The uniform congruence rule

The `cong` constructor:

  Step.cong (gen) (payload)
            (childStep : StepChildren children children')
    : Step (.mkGen gen payload children)
           (.mkGen gen payload children')

Reading: whenever a `StepChildren` chain witnesses reduction
somewhere inside a `RawTermChildren` spine, the wrapped term
reduces under the SAME generator + payload, with the spine
substituted.  ONE rule, all generators.

The `StepChildren` mutual inductive expresses "Step at some position
in the spine":

  here  : Step head head' --> StepChildren (childCons head rest)
                                            (childCons head' rest)
  there : StepChildren rest rest' --> StepChildren (childCons head rest)
                                                    (childCons head rest')

Together: walk down the spine via `there` until you find the position
you want, then fire `here` with a Step at that position.

## Why mutual?

The cong rule recurses on a `StepChildren` argument whose `here`
constructor in turn recurses on a `Step`.  These two inductives
reference each other's constructors, so they MUST be in a `mutual`
block.

The mutual block requires both inductives to share the SAME
parameter telescope.  Since `StepChildren`'s scope varies across
constructors (child positions at `parentScope + headShift`), scope
cannot be a parameter on either inductive -- it must be an INDEX
on both.  Hence the `: {scope : Nat} → ...` form (implicit index).

The implicit-index syntax preserves the existing API shape: callers
write `Step first second` and Lean infers scope from `first`'s type
(verified in StepStar.lean -- which compiles unchanged).

## Why scope-indexed rather than scope-quantified

`Step : {scope : Nat} → RawTerm scope → RawTerm scope → Prop`
makes scope an implicit index of every Step instance.  Each Step
fixes one scope and the constructor's terms are at that scope.
Reduction across scopes is mediated by `Step` + `RawTerm.rename`.

## Scope of this file

This relation operates on `RawTerm`.  Reduction at the `RawCell`
(cell) layer is a separate concern not handled here.  Eta lives in
`Step.eta` (`StepEta.lean`); subject reduction is proved in the
`Step.preservesShape` umbrella.

## Why the uniform cong is the L3 leverage point

The PolyCell thesis is "ONE generic operation covers all 194
generators uniformly".  `beta` covers only the beta-redex shape;
`cong + StepChildren` is the uniform congruence rule -- reduction
under any generator's children spine, without enumerating
generators.

Every L3 theorem (SR, confluence, SN) handles "congruence under any
ctor" as a single mutual-induction case rather than 194 enumerated
cases.  This is the L3 expression of the L2 Allais-fold leverage.

## Zero-axiom verification

The mutual block (`Step`, `StepChildren`) and every smoke pass
`#assert_no_axioms`.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

mutual

/-- Single-step reduction relation on `RawTerm`.

Carries `beta`, the uniform `cong` rule (reduction under any
generator's children spine, mutually with `StepChildren`), and the 18
iota constructors.

The relation is parameterized by `scope : Nat` (implicit index): each
Step instance fixes one scope and relates terms at that scope.
Reduction across scopes is mediated by `RawTerm.rename`. -/
inductive Step : {scope : Nat} → RawTerm scope → RawTerm scope → Prop where
  /-- **Beta reduction.**  Applying a lambda to an argument contracts
      to `subst0 body arg`.

      Textbook lambda calculus beta rule, formulated over V2's
      un-indexed raw substrate. -/
  | beta {scope : Nat} {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
      {arg : RawTerm scope} :
      Step
        (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
            (.childCons arg .childNil)))
        (RawTerm.subst0 body arg)
  /-- **Uniform congruence under any generator.**  When a
      `StepChildren` chain witnesses reduction somewhere inside the
      `RawTermChildren` spine, the wrapped term reduces under the
      SAME generator + payload, with the spine replaced.

      ONE rule covers all 194 generators -- this is the L3 leverage
      point that v2's uniform substrate buys. -/
  | cong {scope : Nat} (gen : Generator) (payload : gen.payload scope)
         {children children' : RawTermChildren gen.binderShifts scope}
         (childStep :
            StepChildren (binderShifts := gen.binderShifts) children children') :
      Step (.mkGen gen payload children) (.mkGen gen payload children')
  /-- **Iota for boolElim on boolTrue.**  Eliminating on `boolTrue`
      selects the then-branch.  No substitution involved -- pure tag-
      selection at the same scope.  The Phase-Z motive shape
      (`binderShifts [1, 0, 0, 0]`): children are
      `(motive, thenBranch, elseBranch, scrutinee)` with the motive a
      term under one binder (it binds the scrutinee).  The iota rule
      DISCARDS the motive operationally — the same discard pattern as
      beta dropping `gen_lam`'s domain annotation; the motive's role is
      TYPING (dependent elimination), not computation.

      The simplest iota rule: bool's two-constructor scheme makes this
      the textbook minimal iota.  More complex iota (natRec on natSucc,
      listElim on listCons) follow the same pattern: pattern-match the
      scrutinee's constructor in the children spine, then return the
      branch term (Church-encoded, no direct subst). -/
  | iotaBoolTrue {scope : Nat}
                 {motive : RawTerm (scope + 1)}
                 {thenBranch elseBranch : RawTerm scope} :
      Step
        (.mkGen .gen_boolElim ()
          (.childCons motive
            (.childCons thenBranch
              (.childCons elseBranch
                (.childCons (.mkGen .gen_boolTrue () .childNil)
                  .childNil)))))
        thenBranch
  /-- **Iota for boolElim on boolFalse.**  Eliminating on `boolFalse`
      selects the else-branch.  Symmetric to `iotaBoolTrue`. -/
  | iotaBoolFalse {scope : Nat}
                  {motive : RawTerm (scope + 1)}
                  {thenBranch elseBranch : RawTerm scope} :
      Step
        (.mkGen .gen_boolElim ()
          (.childCons motive
            (.childCons thenBranch
              (.childCons elseBranch
                (.childCons (.mkGen .gen_boolFalse () .childNil)
                  .childNil)))))
        elseBranch
  /-- **Iota for fst on pair.**  Projecting the first component of an
      explicitly-constructed pair returns the first value.

      The CONTENT-PROJECTION iota shape (vs. boolElim's BRANCH-
      SELECTION shape).  Same scope discipline: `binderShifts [0]`
      for `gen_fst` and `[0, 0]` for `gen_pair` means everything
      lives at the ambient `scope`.  No substitution involved -- the
      reduction simply unwraps the pair and discards the second
      component. -/
  | iotaFstPair {scope : Nat}
                {firstValue secondValue : RawTerm scope} :
      Step
        (.mkGen .gen_fst ()
          (.childCons
            (.mkGen .gen_pair ()
              (.childCons firstValue (.childCons secondValue .childNil)))
            .childNil))
        firstValue
  /-- **Iota for snd on pair.**  Projecting the second component of
      an explicitly-constructed pair returns the second value.
      Symmetric to `iotaFstPair`. -/
  | iotaSndPair {scope : Nat}
                {firstValue secondValue : RawTerm scope} :
      Step
        (.mkGen .gen_snd ()
          (.childCons
            (.mkGen .gen_pair ()
              (.childCons firstValue (.childCons secondValue .childNil)))
            .childNil))
        secondValue
  /-- **Iota for natElim on natZero (base case).**  Eliminating on
      `natZero` selects the zero-branch.  Same branch-selection
      shape as `iotaBoolTrue` -- the 0-arity constructor's iota is
      always pure projection.  Phase-Z motive shape (`binderShifts
      [1, 0, 2, 0]`): children are `(motive, zeroBranch, succBranch,
      scrutinee)` with the motive a term under one binder, the
      succ-branch under TWO binders, and the scrutinee LAST; the
      base-case iota DISCARDS the motive (typing-only role). -/
  | iotaNatElimZero {scope : Nat}
                    {motive : RawTerm (scope + 1)}
                    {zeroBranch : RawTerm scope}
                    {succBranch : RawTerm (scope + 2)} :
      Step
        (.mkGen .gen_natElim ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch
                (.childCons (.mkGen .gen_natZero () .childNil) .childNil)))))
        zeroBranch
  /-- **Iota for natRec on natZero (base case).**  Symmetric to
      `iotaNatElimZero`; the v2 substrate treats `gen_natElim` and
      `gen_natRec` with identical arity and binderShifts, so their
      base-case iotas are structurally identical. -/
  | iotaNatRecZero {scope : Nat}
                   {motive : RawTerm (scope + 1)}
                   {zeroBranch : RawTerm scope}
                   {succBranch : RawTerm (scope + 2)} :
      Step
        (.mkGen .gen_natRec ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch
                (.childCons (.mkGen .gen_natZero () .childNil) .childNil)))))
        zeroBranch
  /-- **Iota for listElim on listNil (base case).**  Eliminating on
      `listNil` selects the nil-branch.  Same branch-selection shape
      as `iotaBoolTrue` / `iotaNatElimZero`; pure projection.  Phase-Z
      motive shape: children `(motive, nilBranch, consBranch, scrutinee)`
      with the motive a term under one binder and the scrutinee LAST;
      the base-case iota DISCARDS the motive (typing-only role). -/
  | iotaListElimNil {scope : Nat}
                    {motive : RawTerm (scope + 1)}
                    {nilBranch consBranch : RawTerm scope} :
      Step
        (.mkGen .gen_listElim ()
          (.childCons motive
            (.childCons nilBranch
              (.childCons consBranch
                (.childCons (.mkGen .gen_listNil () .childNil)
                  .childNil)))))
        nilBranch
  /-- **Iota for optionMatch on optionNone (base case).**  Matching
      on `optionNone` selects the none-branch.  Phase-Z spine
      `(motive, noneBranch, someBranch, scrutinee)` — the motive is
      a term under one binder, discarded by the iota.  Same
      branch-selection shape; pure projection. -/
  | iotaOptionMatchNone {scope : Nat}
                        {motive : RawTerm (scope + 1)}
                        {noneBranch someBranch : RawTerm scope} :
      Step
        (.mkGen .gen_optionMatch ()
          (.childCons motive
            (.childCons noneBranch
              (.childCons someBranch
                (.childCons (.mkGen .gen_optionNone () .childNil)
                  .childNil)))))
        noneBranch
  /-- **Iota for optionMatch on optionSome (step case, 1-arg app-chain).**

      Matching on `optionSome value` applies the some-branch to the
      wrapped value: `optionMatch m n s (optionSome v) ↝ app s v`
      (the Phase-Z motive is discarded).  The THIRD iota shape:
      build an `app` term rather than projecting.  No direct
      substitution -- beta handles the binding work in a subsequent
      reduction step, separating iota's "tag-recognition" duty from
      beta's "argument-binding" duty. -/
  | iotaOptionMatchSome {scope : Nat}
                        {motive : RawTerm (scope + 1)}
                        {value : RawTerm scope}
                        {noneBranch someBranch : RawTerm scope} :
      Step
        (.mkGen .gen_optionMatch ()
          (.childCons motive
            (.childCons noneBranch
              (.childCons someBranch
                (.childCons
                  (.mkGen .gen_optionSome () (.childCons value .childNil))
                  .childNil)))))
        (.mkGen .gen_app ()
          (.childCons someBranch (.childCons value .childNil)))
  /-- **Iota for eitherMatch on eitherInl (step case, 1-arg
      app-chain).**

      Matching on `eitherInl value` applies the left-branch to the
      wrapped value: `eitherMatch m l r (inl v) ↝ app l v` (the
      Phase-Z motive is discarded).  Same 1-arg app-chain shape as
      `iotaOptionMatchSome`. -/
  | iotaEitherMatchInl {scope : Nat}
                       {motive : RawTerm (scope + 1)}
                       {value : RawTerm scope}
                       {leftBranch rightBranch : RawTerm scope} :
      Step
        (.mkGen .gen_eitherMatch ()
          (.childCons motive
            (.childCons leftBranch
              (.childCons rightBranch
                (.childCons
                  (.mkGen .gen_eitherInl () (.childCons value .childNil))
                  .childNil)))))
        (.mkGen .gen_app ()
          (.childCons leftBranch (.childCons value .childNil)))
  /-- **Iota for eitherMatch on eitherInr (step case, 1-arg
      app-chain).**

      Symmetric to `iotaEitherMatchInl`: matching on `eitherInr
      value` applies the right-branch to the wrapped value. -/
  | iotaEitherMatchInr {scope : Nat}
                       {motive : RawTerm (scope + 1)}
                       {value : RawTerm scope}
                       {leftBranch rightBranch : RawTerm scope} :
      Step
        (.mkGen .gen_eitherMatch ()
          (.childCons motive
            (.childCons leftBranch
              (.childCons rightBranch
                (.childCons
                  (.mkGen .gen_eitherInr () (.childCons value .childNil))
                  .childNil)))))
        (.mkGen .gen_app ()
          (.childCons rightBranch (.childCons value .childNil)))
  /-- **Iota for natElim on natSucc (step case, SUBSTITUTING with
      recursive call).**

      Eliminating on `natSucc predecessor` SUBSTITUTES into the
      succ-branch (which lives under TWO binders at `scope + 2`):

        natElim m z s (natSucc n)
          ↝  s[var 0 := natElim m z s n, var 1 := n]

      where `var 0` (innermost) is the inductive hypothesis -- the
      recursive call `natElim m z s n` threading the SAME motive `m`
      and branches `z`/`s` at the predecessor `n` -- and `var 1` is
      the predecessor `n` itself.

      Historic change: the succ-iota used to build a NESTED app-chain
      `app (app s n) (natElim n z s)`.  The Phase-Z motive shape moves
      to DIRECT substitution -- this is the substrate's FIRST
      substituting iota (beta is the only prior substitution rule).
      The recursive call still appears in the reduct (as the
      substituent for `var 0`), so iota's "structural" recursion that
      gives induction principles their power is preserved.

      The two-substituent cons is built `RawTermSubst.cons
      recursiveCall (RawTermSubst.singleton predecessor)`: position 0
      maps to `recursiveCall` (the IH), position 1 maps to
      `predecessor` (via singleton's position-0 entry). -/
  | iotaNatElimSucc {scope : Nat}
                    {motive : RawTerm (scope + 1)}
                    {predecessor : RawTerm scope}
                    {zeroBranch : RawTerm scope}
                    {succBranch : RawTerm (scope + 2)} :
      Step
        (.mkGen .gen_natElim ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch
                (.childCons
                  (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
                  .childNil)))))
        (RawTerm.subst
          (RawTermSubst.cons
            (.mkGen .gen_natElim ()
              (.childCons motive
                (.childCons zeroBranch
                  (.childCons succBranch
                    (.childCons predecessor .childNil)))))
            (RawTermSubst.singleton predecessor))
          succBranch)
  /-- **Iota for natRec on natSucc (step case, SUBSTITUTING with
      recursive call).**

      Symmetric to `iotaNatElimSucc` but for the dependent recursor
      `gen_natRec`.  The v2 substrate treats `gen_natElim` and
      `gen_natRec` identically at the metadata level (same arity,
      same binderShifts), so the iota rules are structurally
      identical too -- the dependent-vs-non-dependent distinction
      is a profile-layer interpretation, not a substrate
      distinction. -/
  | iotaNatRecSucc {scope : Nat}
                   {motive : RawTerm (scope + 1)}
                   {predecessor : RawTerm scope}
                   {zeroBranch : RawTerm scope}
                   {succBranch : RawTerm (scope + 2)} :
      Step
        (.mkGen .gen_natRec ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch
                (.childCons
                  (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
                  .childNil)))))
        (RawTerm.subst
          (RawTermSubst.cons
            (.mkGen .gen_natRec ()
              (.childCons motive
                (.childCons zeroBranch
                  (.childCons succBranch
                    (.childCons predecessor .childNil)))))
            (RawTermSubst.singleton predecessor))
          succBranch)
  /-- **Iota for listElim on listCons (step case, 3-arg app-chain
      with recursive call).**

      The deepest app-chain nesting in the design.  Eliminating on
      `listCons head tail` builds:

        listElim (listCons h t) n c
          ↝  app (app (app c h) t) (listElim t n c)

      Three arguments curried through the cons-branch (head,
      tail, recursive result) -- the cons-branch is expected to
      be a triple-curried lambda `λh.λt.λrec. body`.  beta
      reduces the three apps in three subsequent steps, unwrapping
      the curried function and substituting each argument in turn.

      The recursive call `listElim t n c` (applied to the tail)
      appears in the reduct as a syntactic sub-term -- same
      inductive shape as `iotaNatElimSucc` but with one more
      curried argument.

      Phase-Z motive shape: children `(motive, nilBranch, consBranch,
      scrutinee)` with the motive under one binder and the scrutinee
      LAST.  Unlike the base-case iotas, the step case does NOT fully
      discard the motive: the recursive call in the reduct rebuilds a
      `gen_listElim` spine and THREADS the same motive through (the
      recursive occurrence eliminates the tail at the same motive). -/
  | iotaListElimCons {scope : Nat}
                     {motive : RawTerm (scope + 1)}
                     {headVal tailVal : RawTerm scope}
                     {nilBranch consBranch : RawTerm scope} :
      Step
        (.mkGen .gen_listElim ()
          (.childCons motive
            (.childCons nilBranch
              (.childCons consBranch
                (.childCons
                  (.mkGen .gen_listCons ()
                    (.childCons headVal (.childCons tailVal .childNil)))
                  .childNil)))))
        (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons
                (.mkGen .gen_app ()
                  (.childCons consBranch (.childCons headVal .childNil)))
                (.childCons tailVal .childNil)))
            (.childCons
              (.mkGen .gen_listElim ()
                (.childCons motive
                  (.childCons nilBranch
                    (.childCons consBranch
                      (.childCons tailVal .childNil)))))
              .childNil)))
  /-- **Iota for idJ on refl (identity-type elimination).**

      Eliminating the identity type at `refl rawWitness` returns
      the base case:

        idJ baseCase (refl rawWitness)  ↝  baseCase

      Same SHAPE-1 (branch-selection / pure projection) as
      `iotaBoolTrue` and the other base-case iotas.  Identity-type
      elimination is simpler than textbook MLTT in v2's design
      because the motive and endpoint information lives in the
      PROFILE layer (which interprets identity types), not in the
      substrate's metadata.  The iota just discards the refl
      witness and returns the base case; the profile checks that
      the base case has the right type relative to the motive. -/
  | iotaIdJRefl {scope : Nat}
                {baseCase rawWitness : RawTerm scope} :
      Step
        (.mkGen .gen_idJ ()
          (.childCons
            baseCase
            (.childCons
              (.mkGen .gen_refl () (.childCons rawWitness .childNil))
              .childNil)))
        baseCase
  /-- **Iota for idStrictRec on refl (strict identity-type
      elimination).**

      Symmetric to `iotaIdJRefl` for the strict variant
      `gen_idStrictRec`.  The substrate treats both identity
      eliminators identically (same arity, same binderShifts) --
      the strict-vs-relaxed distinction is a profile-layer
      concern, not a reduction-rule concern. -/
  | iotaIdStrictRecRefl {scope : Nat}
                        {baseCase rawWitness : RawTerm scope} :
      Step
        (.mkGen .gen_idStrictRec ()
          (.childCons
            baseCase
            (.childCons
              (.mkGen .gen_refl () (.childCons rawWitness .childNil))
              .childNil)))
        baseCase

/-- **Step at some position in a children spine.**

The mutual companion to `Step.cong`.  Expresses "the children spine
has a Step somewhere inside it" generically:

* `here`  -- the Step is at the head child position
* `there` -- the Step is somewhere in the tail

Walking down a spine via `there` and firing `here` at the right
position lets `Step.cong` congruence-reduce under ANY child of ANY
generator, uniformly across all 194 generators.

Indices: `parentScope` is the outer scope; `binderShifts` is the
list of per-position scope shifts (from `Generator.binderShifts`).
Both are implicit so call sites infer from the spine arguments. -/
inductive StepChildren :
    {parentScope : Nat} → {binderShifts : List Nat} →
    RawTermChildren binderShifts parentScope →
    RawTermChildren binderShifts parentScope → Prop where
  /-- **Reduction at the head child position.**  When the head
      `RawTerm (parentScope + headShift)` Step-reduces, the whole
      spine StepChildren-reduces with the tail unchanged. -/
  | here {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
         {head head' : RawTerm (parentScope + headShift)}
         (rest : RawTermChildren restShifts parentScope)
         (childStep : Step head head') :
      StepChildren
        (RawTermChildren.childCons head rest)
        (RawTermChildren.childCons head' rest)
  /-- **Reduction somewhere in the tail.**  When the tail spine
      StepChildren-reduces, the whole spine StepChildren-reduces
      with the head unchanged. -/
  | there {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
          (head : RawTerm (parentScope + headShift))
          {rest rest' : RawTermChildren restShifts parentScope}
          (restStep : StepChildren rest rest') :
      StepChildren
        (RawTermChildren.childCons head rest)
        (RawTermChildren.childCons head rest')

end

/-- **Smoke: identity-lambda applied to unit beta-reduces to unit.**

The simplest concrete beta-reduction instance.  The LHS is
`app (lam (var 0)) unit` -- the identity lambda applied to the
unit value.  The RHS is `unit`.

Closes by `apply Step.beta`: Lean's unifier discharges the
implicit equation `subst0 (var 0) unit = unit` via
`subst0_var_zero` (closes by `rfl` thanks to the `@[reducible]`
attribute on `singleton` + `subst0`). -/
theorem Step.identity_lam_applied_to_unit :
    let identityLamBody : RawTerm 1 :=
      .mkGen .gen_var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1) .childNil
    let domainAnn : RawTerm 0 :=
      .mkGen .gen_unit () .childNil
    let unitArg : RawTerm 0 :=
      .mkGen .gen_unit () .childNil
    let app : RawTerm 0 :=
      .mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons domainAnn (.childCons identityLamBody .childNil)))
          (.childCons unitArg .childNil))
    Step app unitArg := by
  apply Step.beta

/-- **Smoke: cong rule fires under `lam`.**

Witnesses the uniform `cong` rule on a concrete fixture.  The
LHS is `lam (app (lam (var 0)) unit)` -- a lambda whose body contains
a beta-redex.  The RHS is `lam unit` -- the same lambda with the
body reduced.

Closes by:
1. `apply Step.cong .gen_lam ()` -- fire the uniform cong rule
   under the `gen_lam` generator with unit payload.
2. The remaining goal is `StepChildren ... ...` over a one-element
   spine where the head is the beta-redex and the tail is empty.
3. `apply StepChildren.here .childNil` -- the Step happens at the
   head child position (the lambda's body).
4. The remaining goal is `Step (app (lam (var 0)) unit) unit` --
   which is exactly `Step.identity_lam_applied_to_unit`'s claim.
5. `apply Step.beta` discharges it.

This smoke witnesses BOTH the uniform cong rule and the typical
"walk into a binder, beta-reduce inside" reduction pattern -- the
core motion the L3 cascade will compose. -/
theorem Step.cong_lam_body_beta :
    let identityLamBody : RawTerm 2 :=
      .mkGen .gen_var (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2) .childNil
    let innerDomainAnn : RawTerm 1 :=
      .mkGen .gen_unit () .childNil
    let outerDomainAnn : RawTerm 0 :=
      .mkGen .gen_unit () .childNil
    let unitArg : RawTerm 1 :=
      .mkGen .gen_unit () .childNil
    let innerApp : RawTerm 1 :=
      .mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons innerDomainAnn (.childCons identityLamBody .childNil)))
          (.childCons unitArg .childNil))
    let outerLamBefore : RawTerm 0 :=
      .mkGen .gen_lam () (.childCons outerDomainAnn (.childCons innerApp .childNil))
    let outerLamAfter : RawTerm 0 :=
      .mkGen .gen_lam () (.childCons outerDomainAnn (.childCons unitArg .childNil))
    Step outerLamBefore outerLamAfter := by
  apply Step.cong .gen_lam ()
  apply StepChildren.there
  apply StepChildren.here .childNil
  apply Step.beta

/-- **Smoke: iotaBoolTrue selects the then-branch.**

Distinct then/else branches verify that the right one is selected:

  `boolElim boolTrue boolTrue boolFalse  ↝  boolTrue`

(The scrutinee `boolTrue` selects the then-branch, which is itself
`boolTrue` -- the result is `boolTrue`, distinct from the
discarded else-branch `boolFalse`.)

Closes by `apply Step.iotaBoolTrue`. -/
theorem Step.iotaBoolTrue_selects_then :
    let trueScrutinee : RawTerm 0 :=
      .mkGen .gen_boolTrue () .childNil
    let varMotive : RawTerm 1 :=
      .mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil
    let thenBranch : RawTerm 0 :=
      .mkGen .gen_boolTrue () .childNil
    let elseBranch : RawTerm 0 :=
      .mkGen .gen_boolFalse () .childNil
    let elimTerm : RawTerm 0 :=
      .mkGen .gen_boolElim ()
        (.childCons varMotive
          (.childCons thenBranch
            (.childCons elseBranch
              (.childCons trueScrutinee .childNil))))
    Step elimTerm thenBranch := by
  apply Step.iotaBoolTrue

/-- **Smoke: iotaBoolFalse selects the else-branch.**

Symmetric to `iotaBoolTrue_selects_then`.  Distinct branches verify
the right selection:

  `boolElim boolFalse boolTrue boolFalse  ↝  boolFalse`

(The scrutinee `boolFalse` selects the else-branch, which is itself
`boolFalse` -- the result is `boolFalse`, distinct from the
discarded then-branch `boolTrue`.)

Closes by `apply Step.iotaBoolFalse`. -/
theorem Step.iotaBoolFalse_selects_else :
    let falseScrutinee : RawTerm 0 :=
      .mkGen .gen_boolFalse () .childNil
    let varMotive : RawTerm 1 :=
      .mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil
    let thenBranch : RawTerm 0 :=
      .mkGen .gen_boolTrue () .childNil
    let elseBranch : RawTerm 0 :=
      .mkGen .gen_boolFalse () .childNil
    let elimTerm : RawTerm 0 :=
      .mkGen .gen_boolElim ()
        (.childCons varMotive
          (.childCons thenBranch
            (.childCons elseBranch
              (.childCons falseScrutinee .childNil))))
    Step elimTerm elseBranch := by
  apply Step.iotaBoolFalse

/-- **Smoke: iotaFstPair projects the first component.**

Distinct first/second components verify the RIGHT component is
projected:

  `fst (pair boolTrue boolFalse)  ↝  boolTrue`

(The first component is `boolTrue`, the second is `boolFalse`; the
result is `boolTrue`, distinct from the discarded `boolFalse`.)

Closes by `apply Step.iotaFstPair`. -/
theorem Step.iotaFstPair_projects_first :
    let firstValue : RawTerm 0 :=
      .mkGen .gen_boolTrue () .childNil
    let secondValue : RawTerm 0 :=
      .mkGen .gen_boolFalse () .childNil
    let pairTerm : RawTerm 0 :=
      .mkGen .gen_pair ()
        (.childCons firstValue (.childCons secondValue .childNil))
    let fstTerm : RawTerm 0 :=
      .mkGen .gen_fst () (.childCons pairTerm .childNil)
    Step fstTerm firstValue := by
  apply Step.iotaFstPair

/-- **Smoke: iotaSndPair projects the second component.**

Symmetric to `iotaFstPair_projects_first`.  Distinct components
verify the right projection:

  `snd (pair boolTrue boolFalse)  ↝  boolFalse`

(The first component is `boolTrue`, the second is `boolFalse`; the
result is `boolFalse`, distinct from the discarded `boolTrue`.)

Closes by `apply Step.iotaSndPair`. -/
theorem Step.iotaSndPair_projects_second :
    let firstValue : RawTerm 0 :=
      .mkGen .gen_boolTrue () .childNil
    let secondValue : RawTerm 0 :=
      .mkGen .gen_boolFalse () .childNil
    let pairTerm : RawTerm 0 :=
      .mkGen .gen_pair ()
        (.childCons firstValue (.childCons secondValue .childNil))
    let sndTerm : RawTerm 0 :=
      .mkGen .gen_snd () (.childCons pairTerm .childNil)
    Step sndTerm secondValue := by
  apply Step.iotaSndPair

/-- **Smoke: iotaNatElimZero selects the zero-branch.**

  `natElim natZero boolTrue boolFalse  ↝  boolTrue`

Distinct zero/succ branches verify the RIGHT one is selected.
(The zero-branch `boolTrue` is selected; the succ-branch
`boolFalse` is discarded.)

Phase-Z motive shape: children `(motive, zeroBranch, succBranch,
scrutinee)` with the scrutinee LAST; the motive is a `var 0` at
scope 1, the succ-branch a `var 0` at scope 2 (both discarded by
the zero-iota).  Closes by `apply Step.iotaNatElimZero`. -/
theorem Step.iotaNatElimZero_selects_zero :
    let zeroScrutinee : RawTerm 0 :=
      .mkGen .gen_natZero () .childNil
    let motive : RawTerm 1 :=
      .mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil
    let zeroBranch : RawTerm 0 :=
      .mkGen .gen_boolTrue () .childNil
    let succBranch : RawTerm 2 :=
      .mkGen .gen_var ⟨0, Nat.zero_lt_succ 1⟩ .childNil
    let elimTerm : RawTerm 0 :=
      .mkGen .gen_natElim ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons zeroScrutinee .childNil))))
    Step elimTerm zeroBranch := by
  apply Step.iotaNatElimZero

/-- **Smoke: iotaNatRecZero selects the zero-branch.**

Symmetric to `iotaNatElimZero_selects_zero` -- same shape on
`gen_natRec` instead of `gen_natElim`. -/
theorem Step.iotaNatRecZero_selects_zero :
    let zeroScrutinee : RawTerm 0 :=
      .mkGen .gen_natZero () .childNil
    let motive : RawTerm 1 :=
      .mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil
    let zeroBranch : RawTerm 0 :=
      .mkGen .gen_boolTrue () .childNil
    let succBranch : RawTerm 2 :=
      .mkGen .gen_var ⟨0, Nat.zero_lt_succ 1⟩ .childNil
    let recTerm : RawTerm 0 :=
      .mkGen .gen_natRec ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons zeroScrutinee .childNil))))
    Step recTerm zeroBranch := by
  apply Step.iotaNatRecZero

/-- **Smoke: iotaListElimNil selects the nil-branch.**

  `listElim listNil boolTrue boolFalse  ↝  boolTrue`

Distinct nil/cons branches verify the RIGHT one is selected. -/
theorem Step.iotaListElimNil_selects_nil :
    let nilScrutinee : RawTerm 0 :=
      .mkGen .gen_listNil () .childNil
    let varMotive : RawTerm 1 :=
      .mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil
    let nilBranch : RawTerm 0 :=
      .mkGen .gen_boolTrue () .childNil
    let consBranch : RawTerm 0 :=
      .mkGen .gen_boolFalse () .childNil
    let elimTerm : RawTerm 0 :=
      .mkGen .gen_listElim ()
        (.childCons varMotive
          (.childCons nilBranch
            (.childCons consBranch
              (.childCons nilScrutinee .childNil))))
    Step elimTerm nilBranch := by
  apply Step.iotaListElimNil

/-- **Smoke: iotaOptionMatchNone selects the none-branch.**

  `optionMatch motive boolTrue boolFalse optionNone  ↝  boolTrue`

Distinct none/some branches verify the RIGHT one is selected; the
Phase-Z motive (a throwaway `var 0` under the binder) is discarded. -/
theorem Step.iotaOptionMatchNone_selects_none :
    let throwawayMotive : RawTerm 1 :=
      .mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil
    let noneScrutinee : RawTerm 0 :=
      .mkGen .gen_optionNone () .childNil
    let noneBranch : RawTerm 0 :=
      .mkGen .gen_boolTrue () .childNil
    let someBranch : RawTerm 0 :=
      .mkGen .gen_boolFalse () .childNil
    let matchTerm : RawTerm 0 :=
      .mkGen .gen_optionMatch ()
        (.childCons throwawayMotive
          (.childCons noneBranch
            (.childCons someBranch
              (.childCons noneScrutinee .childNil))))
    Step matchTerm noneBranch := by
  apply Step.iotaOptionMatchNone

/-- **Smoke: iotaOptionMatchSome builds app chain.**

  `optionMatch motive boolTrue boolFalse (optionSome unit)
     ↝  app boolFalse unit`

The result is the `app` term (not just `boolFalse`); the wrapped
value is preserved as the application's argument. -/
theorem Step.iotaOptionMatchSome_builds_app :
    let throwawayMotive : RawTerm 1 :=
      .mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil
    let unitVal : RawTerm 0 :=
      .mkGen .gen_unit () .childNil
    let someScrutinee : RawTerm 0 :=
      .mkGen .gen_optionSome () (.childCons unitVal .childNil)
    let noneBranch : RawTerm 0 :=
      .mkGen .gen_boolTrue () .childNil
    let someBranch : RawTerm 0 :=
      .mkGen .gen_boolFalse () .childNil
    let matchTerm : RawTerm 0 :=
      .mkGen .gen_optionMatch ()
        (.childCons throwawayMotive
          (.childCons noneBranch
            (.childCons someBranch
              (.childCons someScrutinee .childNil))))
    let appResult : RawTerm 0 :=
      .mkGen .gen_app ()
        (.childCons someBranch (.childCons unitVal .childNil))
    Step matchTerm appResult := by
  apply Step.iotaOptionMatchSome

/-- **Smoke: iotaEitherMatchInl builds app chain.**

  `eitherMatch motive boolTrue boolFalse (eitherInl unit)
     ↝  app boolTrue unit`

Distinct left/right branches verify the RIGHT branch is applied.
The wrapped value is preserved as the application's argument. -/
theorem Step.iotaEitherMatchInl_builds_app :
    let throwawayMotive : RawTerm 1 :=
      .mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil
    let unitVal : RawTerm 0 :=
      .mkGen .gen_unit () .childNil
    let inlScrutinee : RawTerm 0 :=
      .mkGen .gen_eitherInl () (.childCons unitVal .childNil)
    let leftBranch : RawTerm 0 :=
      .mkGen .gen_boolTrue () .childNil
    let rightBranch : RawTerm 0 :=
      .mkGen .gen_boolFalse () .childNil
    let matchTerm : RawTerm 0 :=
      .mkGen .gen_eitherMatch ()
        (.childCons throwawayMotive
          (.childCons leftBranch
            (.childCons rightBranch
              (.childCons inlScrutinee .childNil))))
    let appResult : RawTerm 0 :=
      .mkGen .gen_app ()
        (.childCons leftBranch (.childCons unitVal .childNil))
    Step matchTerm appResult := by
  apply Step.iotaEitherMatchInl

/-- **Smoke: iotaEitherMatchInr builds app chain.**

  `eitherMatch motive boolTrue boolFalse (eitherInr unit)
     ↝  app boolFalse unit`

Symmetric to `iotaEitherMatchInl_builds_app`. -/
theorem Step.iotaEitherMatchInr_builds_app :
    let throwawayMotive : RawTerm 1 :=
      .mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil
    let unitVal : RawTerm 0 :=
      .mkGen .gen_unit () .childNil
    let inrScrutinee : RawTerm 0 :=
      .mkGen .gen_eitherInr () (.childCons unitVal .childNil)
    let leftBranch : RawTerm 0 :=
      .mkGen .gen_boolTrue () .childNil
    let rightBranch : RawTerm 0 :=
      .mkGen .gen_boolFalse () .childNil
    let matchTerm : RawTerm 0 :=
      .mkGen .gen_eitherMatch ()
        (.childCons throwawayMotive
          (.childCons leftBranch
            (.childCons rightBranch
              (.childCons inrScrutinee .childNil))))
    let appResult : RawTerm 0 :=
      .mkGen .gen_app ()
        (.childCons rightBranch (.childCons unitVal .childNil))
    Step matchTerm appResult := by
  apply Step.iotaEitherMatchInr

/-- **Smoke: iotaNatElimSucc substitutes into the succ-branch with
the recursive call.**

  `natElim motive zeroBranch (var 0) (natSucc natZero)
     ↝  (var 0)[var 0 := recursiveCall, var 1 := natZero]
     =  recursiveCall`

where `recursiveCall = natElim motive zeroBranch (var 0) natZero`.

Concrete fixture: the succ-branch is exactly `var 0` (the
innermost binder = the inductive hypothesis), so the simultaneous
substitution `cons recursiveCall (singleton predecessor)` projects
position 0 = `recursiveCall`.  The reduct therefore computes (by
`rfl`/`apply`-unification) to the recursive call -- the ORIGINAL
eliminator applied to the predecessor -- which subsequent
reductions (via cong + iotaNatElimZero) would fold to the
zero-branch.  The predecessor is `natZero`.

Closes by `apply Step.iotaNatElimSucc`. -/
theorem Step.iotaNatElimSucc_substitutes_recursive_call :
    let predecessor : RawTerm 0 :=
      .mkGen .gen_natZero () .childNil
    let succScrutinee : RawTerm 0 :=
      .mkGen .gen_natSucc () (.childCons predecessor .childNil)
    let motive : RawTerm 1 :=
      .mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil
    let zeroBranch : RawTerm 0 :=
      .mkGen .gen_boolTrue () .childNil
    let succBranch : RawTerm 2 :=
      .mkGen .gen_var ⟨0, Nat.zero_lt_succ 1⟩ .childNil
    let elimTerm : RawTerm 0 :=
      .mkGen .gen_natElim ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons succScrutinee .childNil))))
    let recursiveCall : RawTerm 0 :=
      .mkGen .gen_natElim ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons predecessor .childNil))))
    Step elimTerm recursiveCall := by
  apply Step.iotaNatElimSucc

/-- **Smoke: iotaNatRecSucc substitutes into the succ-branch with
the recursive call.**

Symmetric to `iotaNatElimSucc_substitutes_recursive_call` -- same
substituting shape, with `gen_natRec` instead of `gen_natElim` in
both the redex and the recursive call that is substituted for the
inductive-hypothesis variable `var 0`. -/
theorem Step.iotaNatRecSucc_substitutes_recursive_call :
    let predecessor : RawTerm 0 :=
      .mkGen .gen_natZero () .childNil
    let succScrutinee : RawTerm 0 :=
      .mkGen .gen_natSucc () (.childCons predecessor .childNil)
    let motive : RawTerm 1 :=
      .mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil
    let zeroBranch : RawTerm 0 :=
      .mkGen .gen_boolTrue () .childNil
    let succBranch : RawTerm 2 :=
      .mkGen .gen_var ⟨0, Nat.zero_lt_succ 1⟩ .childNil
    let recTerm : RawTerm 0 :=
      .mkGen .gen_natRec ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons succScrutinee .childNil))))
    let recursiveCall : RawTerm 0 :=
      .mkGen .gen_natRec ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons predecessor .childNil))))
    Step recTerm recursiveCall := by
  apply Step.iotaNatRecSucc

/-- **Smoke: iotaListElimCons builds triple-nested app
with recursion.**

  `listElim (listCons unit listNil) boolTrue boolFalse
     ↝  app (app (app boolFalse unit) listNil)
            (listElim listNil boolTrue boolFalse)`

Concrete fixture uses `unit` as the head and `listNil` as the
tail (smallest non-empty list possible).  The recursive call in
the reduct is `listElim listNil ...` -- which subsequent
reductions (via cong + iotaListElimNil) would fold to `boolTrue`
(the nil-branch).

This is the DEEPEST nesting in the v2 iota suite: three layers of
`app` wrapping, with the recursive call as the second argument of
the outermost app.  Closes by `apply Step.iotaListElimCons`. -/
theorem Step.iotaListElimCons_builds_triple_app :
    let headVal : RawTerm 0 :=
      .mkGen .gen_unit () .childNil
    let tailVal : RawTerm 0 :=
      .mkGen .gen_listNil () .childNil
    let consScrutinee : RawTerm 0 :=
      .mkGen .gen_listCons ()
        (.childCons headVal (.childCons tailVal .childNil))
    let varMotive : RawTerm 1 :=
      .mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil
    let nilBranch : RawTerm 0 :=
      .mkGen .gen_boolTrue () .childNil
    let consBranch : RawTerm 0 :=
      .mkGen .gen_boolFalse () .childNil
    let elimTerm : RawTerm 0 :=
      .mkGen .gen_listElim ()
        (.childCons varMotive
          (.childCons nilBranch
            (.childCons consBranch
              (.childCons consScrutinee .childNil))))
    let recursiveCall : RawTerm 0 :=
      .mkGen .gen_listElim ()
        (.childCons varMotive
          (.childCons nilBranch
            (.childCons consBranch
              (.childCons tailVal .childNil))))
    let appHead : RawTerm 0 :=
      .mkGen .gen_app ()
        (.childCons consBranch (.childCons headVal .childNil))
    let appHeadTail : RawTerm 0 :=
      .mkGen .gen_app ()
        (.childCons appHead (.childCons tailVal .childNil))
    let tripleApp : RawTerm 0 :=
      .mkGen .gen_app ()
        (.childCons appHeadTail (.childCons recursiveCall .childNil))
    Step elimTerm tripleApp := by
  apply Step.iotaListElimCons

/-- **Smoke: iotaIdJRefl selects the base case.**

  `idJ boolTrue (refl unit)  ↝  boolTrue`

The witness `refl unit` is discarded; the base case `boolTrue` is
returned.  Closes by `apply Step.iotaIdJRefl`. -/
theorem Step.iotaIdJRefl_selects_base :
    let baseCase : RawTerm 0 :=
      .mkGen .gen_boolTrue () .childNil
    let rawWitness : RawTerm 0 :=
      .mkGen .gen_unit () .childNil
    let reflTerm : RawTerm 0 :=
      .mkGen .gen_refl () (.childCons rawWitness .childNil)
    let idJTerm : RawTerm 0 :=
      .mkGen .gen_idJ ()
        (.childCons baseCase (.childCons reflTerm .childNil))
    Step idJTerm baseCase := by
  apply Step.iotaIdJRefl

/-- **Smoke: iotaIdStrictRecRefl selects the base case.**

Symmetric to `iotaIdJRefl_selects_base` for `gen_idStrictRec`. -/
theorem Step.iotaIdStrictRecRefl_selects_base :
    let baseCase : RawTerm 0 :=
      .mkGen .gen_boolTrue () .childNil
    let rawWitness : RawTerm 0 :=
      .mkGen .gen_unit () .childNil
    let reflTerm : RawTerm 0 :=
      .mkGen .gen_refl () (.childCons rawWitness .childNil)
    let idStrictRecTerm : RawTerm 0 :=
      .mkGen .gen_idStrictRec ()
        (.childCons baseCase (.childCons reflTerm .childNil))
    Step idStrictRecTerm baseCase := by
  apply Step.iotaIdStrictRecRefl

end FX1Poly.Core
