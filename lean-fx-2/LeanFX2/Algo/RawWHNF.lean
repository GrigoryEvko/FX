import LeanFX2.Foundation.RawSubst

/-! # Algo/RawWHNF — fuel-bounded weak head normal form on raw terms

`RawTerm.whnf : Nat → RawTerm scope → RawTerm scope` reduces a raw
term to weak head normal form by repeatedly firing β/ι at the head.
The fuel parameter ensures termination regardless of strong-
normalization status (Tot terms terminate naturally; Div terms get
truncated at the fuel ceiling).

## Why raw-side first

Typed `Term.whnf` would need to thread typed Term constructors and
HEq-cast through every β/ι contractum.  Raw-side `RawTerm.whnf`
operates on plain data — no dependent indices, no type-level
threading.  Once we have the raw operation, we lift via the typed-
to-raw bridge.

## Reduction strategy

Call-by-name: head reduction first.  No reduction under binders
beyond the head.

## Termination

The function terminates structurally on the `Nat` fuel parameter.
No SN proof required; if fuel is exhausted, return the term as-is
(which may not be in WHNF — caller's responsibility to use
sufficient fuel).

## Architecture: zero-axiom recipe

Three discipline rules keep this function propext-free:

1. **Outer Nat match, inner RawTerm match** — combining a Nat
   ctor pattern (`0` vs `_+1`) with a dependent RawTerm pattern
   in a single multi-discriminator match leaks propext.  The
   workaround is to nest: outer `match fuel with`, inner
   `match term with`.

2. **Full enumeration in every match arm** — every `match` over
   `RawTerm` or over `RawTerm.HeadCtor` lists every constructor
   explicitly (no `| _ => ...` wildcards).  Wildcards on
   dependent inductives leak propext per
   `feedback_lean_zero_axiom_match.md`.

3. **Flat-enum dispatch via `headCtor`** — when we only need to
   know "did the recursively-whnf'd subterm reach a canonical
   form?", we project to `RawTerm.HeadCtor` (a flat enum) and
   match there.  Component extraction is delegated to dedicated
   `?`-projection helpers (`lamBody?`, `pairComponents?`, ...)
   each of which uses full 28-arm enumeration.
-/

namespace LeanFX2

/-- Flat enum tagging the head constructor of a `RawTerm`.  Used
by `RawTerm.whnf` to dispatch on the head shape of a recursively-
whnf'd subterm without nested pattern-matches that would leak
propext via wildcards. -/
inductive RawTerm.HeadCtor : Type
  | var | unit | lam | app | pair | fst | snd
  | boolTrue | boolFalse | boolElim
  | natZero | natSucc | natElim | natRec
  | listNil | listCons | listElim
  | optionNone | optionSome | optionMatch
  | eitherInl | eitherInr | eitherMatch
  | refl | idJ
  | modIntro | modElim | subsume

/-- Project a raw term to its head-ctor tag.  Full enumeration of
all 28 RawTerm ctors keeps this propext-free. -/
def RawTerm.headCtor {scope : Nat} (term : RawTerm scope) : RawTerm.HeadCtor :=
  match term with
  | .var _ => .var | .unit => .unit | .lam _ => .lam
  | .app _ _ => .app | .pair _ _ => .pair
  | .fst _ => .fst | .snd _ => .snd
  | .boolTrue => .boolTrue | .boolFalse => .boolFalse
  | .boolElim _ _ _ => .boolElim
  | .natZero => .natZero | .natSucc _ => .natSucc
  | .natElim _ _ _ => .natElim | .natRec _ _ _ => .natRec
  | .listNil => .listNil | .listCons _ _ => .listCons
  | .listElim _ _ _ => .listElim
  | .optionNone => .optionNone | .optionSome _ => .optionSome
  | .optionMatch _ _ _ => .optionMatch
  | .eitherInl _ => .eitherInl | .eitherInr _ => .eitherInr
  | .eitherMatch _ _ _ => .eitherMatch
  | .refl _ => .refl | .idJ _ _ => .idJ
  | .modIntro _ => .modIntro | .modElim _ => .modElim
  | .subsume _ => .subsume

/-! ## ?-projection helpers — full 28-arm enumeration

Each helper extracts data from a specific RawTerm constructor.
Full enumeration of all 28 ctors keeps every match propext-free
(per `feedback_lean_zero_axiom_match.md`: wildcards on dependent
inductives always leak propext, full enumeration is clean for
universal-index projection targets).

Verbose but mechanical — each non-matching ctor returns `none`
(or `false` for `isRefl`).  The compiler reduces these helpers
on closed terms, so smoke tests via `rfl` work. -/

/-- Project the body of a `lam` term.  See file-level comment
for the "full enumeration not wildcard" rule. -/
def RawTerm.lamBody? {scope : Nat} (term : RawTerm scope) :
    Option (RawTerm (scope + 1)) :=
  match term with
  | .lam body => some body
  | .var _ => none | .unit => none | .app _ _ => none
  | .pair _ _ => none | .fst _ => none | .snd _ => none
  | .boolTrue => none | .boolFalse => none | .boolElim _ _ _ => none
  | .natZero => none | .natSucc _ => none
  | .natElim _ _ _ => none | .natRec _ _ _ => none
  | .listNil => none | .listCons _ _ => none | .listElim _ _ _ => none
  | .optionNone => none | .optionSome _ => none | .optionMatch _ _ _ => none
  | .eitherInl _ => none | .eitherInr _ => none | .eitherMatch _ _ _ => none
  | .refl _ => none | .idJ _ _ => none
  | .modIntro _ => none | .modElim _ => none | .subsume _ => none

/-- Project the components of a `pair` term. -/
def RawTerm.pairComponents? {scope : Nat} (term : RawTerm scope) :
    Option (RawTerm scope × RawTerm scope) :=
  match term with
  | .pair firstValue secondValue => some (firstValue, secondValue)
  | .var _ => none | .unit => none | .lam _ => none | .app _ _ => none
  | .fst _ => none | .snd _ => none
  | .boolTrue => none | .boolFalse => none | .boolElim _ _ _ => none
  | .natZero => none | .natSucc _ => none
  | .natElim _ _ _ => none | .natRec _ _ _ => none
  | .listNil => none | .listCons _ _ => none | .listElim _ _ _ => none
  | .optionNone => none | .optionSome _ => none | .optionMatch _ _ _ => none
  | .eitherInl _ => none | .eitherInr _ => none | .eitherMatch _ _ _ => none
  | .refl _ => none | .idJ _ _ => none
  | .modIntro _ => none | .modElim _ => none | .subsume _ => none

/-- Project the predecessor from a `natSucc` term. -/
def RawTerm.natSuccPred? {scope : Nat} (term : RawTerm scope) :
    Option (RawTerm scope) :=
  match term with
  | .natSucc predecessor => some predecessor
  | .var _ => none | .unit => none | .lam _ => none | .app _ _ => none
  | .pair _ _ => none | .fst _ => none | .snd _ => none
  | .boolTrue => none | .boolFalse => none | .boolElim _ _ _ => none
  | .natZero => none
  | .natElim _ _ _ => none | .natRec _ _ _ => none
  | .listNil => none | .listCons _ _ => none | .listElim _ _ _ => none
  | .optionNone => none | .optionSome _ => none | .optionMatch _ _ _ => none
  | .eitherInl _ => none | .eitherInr _ => none | .eitherMatch _ _ _ => none
  | .refl _ => none | .idJ _ _ => none
  | .modIntro _ => none | .modElim _ => none | .subsume _ => none

/-- Project head/tail from a `listCons`. -/
def RawTerm.listConsParts? {scope : Nat} (term : RawTerm scope) :
    Option (RawTerm scope × RawTerm scope) :=
  match term with
  | .listCons headTerm tailTerm => some (headTerm, tailTerm)
  | .var _ => none | .unit => none | .lam _ => none | .app _ _ => none
  | .pair _ _ => none | .fst _ => none | .snd _ => none
  | .boolTrue => none | .boolFalse => none | .boolElim _ _ _ => none
  | .natZero => none | .natSucc _ => none
  | .natElim _ _ _ => none | .natRec _ _ _ => none
  | .listNil => none | .listElim _ _ _ => none
  | .optionNone => none | .optionSome _ => none | .optionMatch _ _ _ => none
  | .eitherInl _ => none | .eitherInr _ => none | .eitherMatch _ _ _ => none
  | .refl _ => none | .idJ _ _ => none
  | .modIntro _ => none | .modElim _ => none | .subsume _ => none

/-- Project the value from `optionSome`. -/
def RawTerm.optionSomeValue? {scope : Nat} (term : RawTerm scope) :
    Option (RawTerm scope) :=
  match term with
  | .optionSome valueTerm => some valueTerm
  | .var _ => none | .unit => none | .lam _ => none | .app _ _ => none
  | .pair _ _ => none | .fst _ => none | .snd _ => none
  | .boolTrue => none | .boolFalse => none | .boolElim _ _ _ => none
  | .natZero => none | .natSucc _ => none
  | .natElim _ _ _ => none | .natRec _ _ _ => none
  | .listNil => none | .listCons _ _ => none | .listElim _ _ _ => none
  | .optionNone => none | .optionMatch _ _ _ => none
  | .eitherInl _ => none | .eitherInr _ => none | .eitherMatch _ _ _ => none
  | .refl _ => none | .idJ _ _ => none
  | .modIntro _ => none | .modElim _ => none | .subsume _ => none

/-- Project the value from `eitherInl`. -/
def RawTerm.eitherInlValue? {scope : Nat} (term : RawTerm scope) :
    Option (RawTerm scope) :=
  match term with
  | .eitherInl valueTerm => some valueTerm
  | .var _ => none | .unit => none | .lam _ => none | .app _ _ => none
  | .pair _ _ => none | .fst _ => none | .snd _ => none
  | .boolTrue => none | .boolFalse => none | .boolElim _ _ _ => none
  | .natZero => none | .natSucc _ => none
  | .natElim _ _ _ => none | .natRec _ _ _ => none
  | .listNil => none | .listCons _ _ => none | .listElim _ _ _ => none
  | .optionNone => none | .optionSome _ => none | .optionMatch _ _ _ => none
  | .eitherInr _ => none | .eitherMatch _ _ _ => none
  | .refl _ => none | .idJ _ _ => none
  | .modIntro _ => none | .modElim _ => none | .subsume _ => none

/-- Project the value from `eitherInr`. -/
def RawTerm.eitherInrValue? {scope : Nat} (term : RawTerm scope) :
    Option (RawTerm scope) :=
  match term with
  | .eitherInr valueTerm => some valueTerm
  | .var _ => none | .unit => none | .lam _ => none | .app _ _ => none
  | .pair _ _ => none | .fst _ => none | .snd _ => none
  | .boolTrue => none | .boolFalse => none | .boolElim _ _ _ => none
  | .natZero => none | .natSucc _ => none
  | .natElim _ _ _ => none | .natRec _ _ _ => none
  | .listNil => none | .listCons _ _ => none | .listElim _ _ _ => none
  | .optionNone => none | .optionSome _ => none | .optionMatch _ _ _ => none
  | .eitherInl _ => none | .eitherMatch _ _ _ => none
  | .refl _ => none | .idJ _ _ => none
  | .modIntro _ => none | .modElim _ => none | .subsume _ => none

/-- Test whether a term is a `refl` (independent of the witness). -/
def RawTerm.isRefl {scope : Nat} (term : RawTerm scope) : Bool :=
  match term with
  | .refl _ => true
  | .var _ => false | .unit => false | .lam _ => false | .app _ _ => false
  | .pair _ _ => false | .fst _ => false | .snd _ => false
  | .boolTrue => false | .boolFalse => false | .boolElim _ _ _ => false
  | .natZero => false | .natSucc _ => false
  | .natElim _ _ _ => false | .natRec _ _ _ => false
  | .listNil => false | .listCons _ _ => false | .listElim _ _ _ => false
  | .optionNone => false | .optionSome _ => false | .optionMatch _ _ _ => false
  | .eitherInl _ => false | .eitherInr _ => false | .eitherMatch _ _ _ => false
  | .idJ _ _ => false
  | .modIntro _ => false | .modElim _ => false | .subsume _ => false

/-- Fuel-bounded weak head normal form reduction on raw terms.
Fires β/ι at the head until reaching a canonical/neutral form
or running out of fuel.

Inner dispatches use the `?`-projection helpers to avoid
wildcard match patterns inside the recursive body, keeping the
function propext-free.

Reductions performed:
* `app (lam body) arg`           → `body.subst0 arg`
* `fst (pair fv sv)`             → `fv`
* `snd (pair fv sv)`             → `sv`
* `boolElim true t e`            → `t`
* `boolElim false t e`           → `e`
* `natElim 0 z s`                → `z`
* `natElim (succ n) z s`         → `app s n`
* `natRec 0 z s`                 → `z`
* `natRec (succ n) z s`          → `app (app s n) (natRec n z s)`
* `listElim nil n c`             → `n`
* `listElim (cons h t) n c`      → `app (app c h) t`
* `optionMatch none n s`         → `n`
* `optionMatch (some v) n s`     → `app s v`
* `eitherMatch (inl v) l r`      → `app l v`
* `eitherMatch (inr v) l r`      → `app r v`
* `idJ b (refl _)`               → `b`

Modal `modElim (modIntro _)` reduces are deferred to Layer 6;
this WHNF treats modal forms as canonical for now. -/
def RawTerm.whnf (fuel : Nat) {scope : Nat} (term : RawTerm scope) :
    RawTerm scope :=
  match fuel with
  | 0 => term
  | fuel + 1 =>
    match term with
    | .var position => .var position
    | .unit => .unit
    | .lam body => .lam body
    | .app functionTerm argumentTerm =>
        let functionWhnf := RawTerm.whnf fuel functionTerm
        match RawTerm.lamBody? functionWhnf with
        | some body => RawTerm.whnf fuel (body.subst0 argumentTerm)
        | none      => .app functionWhnf argumentTerm
    | .pair firstValue secondValue => .pair firstValue secondValue
    | .fst pairTerm =>
        let pairWhnf := RawTerm.whnf fuel pairTerm
        match RawTerm.pairComponents? pairWhnf with
        | some (firstValue, _) => RawTerm.whnf fuel firstValue
        | none                 => .fst pairWhnf
    | .snd pairTerm =>
        let pairWhnf := RawTerm.whnf fuel pairTerm
        match RawTerm.pairComponents? pairWhnf with
        | some (_, secondValue) => RawTerm.whnf fuel secondValue
        | none                  => .snd pairWhnf
    | .boolTrue => .boolTrue
    | .boolFalse => .boolFalse
    | .boolElim scrutinee thenBranch elseBranch =>
        let scrutineeWhnf := RawTerm.whnf fuel scrutinee
        match scrutineeWhnf.headCtor with
        | .boolTrue  => RawTerm.whnf fuel thenBranch
        | .boolFalse => RawTerm.whnf fuel elseBranch
        | .var | .unit | .lam | .app | .pair | .fst | .snd
        | .boolElim | .natZero | .natSucc | .natElim | .natRec
        | .listNil | .listCons | .listElim
        | .optionNone | .optionSome | .optionMatch
        | .eitherInl | .eitherInr | .eitherMatch
        | .refl | .idJ | .modIntro | .modElim | .subsume =>
            .boolElim scrutineeWhnf thenBranch elseBranch
    | .natZero => .natZero
    | .natSucc predecessor => .natSucc predecessor
    | .natElim scrutinee zeroBranch succBranch =>
        let scrutineeWhnf := RawTerm.whnf fuel scrutinee
        match scrutineeWhnf.headCtor with
        | .natZero =>
            RawTerm.whnf fuel zeroBranch
        | .natSucc =>
            match RawTerm.natSuccPred? scrutineeWhnf with
            | some predecessor =>
                RawTerm.whnf fuel (.app succBranch predecessor)
            | none =>
                .natElim scrutineeWhnf zeroBranch succBranch
        | .var | .unit | .lam | .app | .pair | .fst | .snd
        | .boolTrue | .boolFalse | .boolElim
        | .natElim | .natRec
        | .listNil | .listCons | .listElim
        | .optionNone | .optionSome | .optionMatch
        | .eitherInl | .eitherInr | .eitherMatch
        | .refl | .idJ | .modIntro | .modElim | .subsume =>
            .natElim scrutineeWhnf zeroBranch succBranch
    | .natRec scrutinee zeroBranch succBranch =>
        let scrutineeWhnf := RawTerm.whnf fuel scrutinee
        match scrutineeWhnf.headCtor with
        | .natZero =>
            RawTerm.whnf fuel zeroBranch
        | .natSucc =>
            match RawTerm.natSuccPred? scrutineeWhnf with
            | some predecessor =>
                RawTerm.whnf fuel
                  (.app (.app succBranch predecessor)
                        (.natRec predecessor zeroBranch succBranch))
            | none =>
                .natRec scrutineeWhnf zeroBranch succBranch
        | .var | .unit | .lam | .app | .pair | .fst | .snd
        | .boolTrue | .boolFalse | .boolElim
        | .natElim | .natRec
        | .listNil | .listCons | .listElim
        | .optionNone | .optionSome | .optionMatch
        | .eitherInl | .eitherInr | .eitherMatch
        | .refl | .idJ | .modIntro | .modElim | .subsume =>
            .natRec scrutineeWhnf zeroBranch succBranch
    | .listNil => .listNil
    | .listCons headTerm tailTerm => .listCons headTerm tailTerm
    | .listElim scrutinee nilBranch consBranch =>
        let scrutineeWhnf := RawTerm.whnf fuel scrutinee
        match scrutineeWhnf.headCtor with
        | .listNil =>
            RawTerm.whnf fuel nilBranch
        | .listCons =>
            match RawTerm.listConsParts? scrutineeWhnf with
            | some (headTerm, tailTerm) =>
                RawTerm.whnf fuel (.app (.app consBranch headTerm) tailTerm)
            | none =>
                .listElim scrutineeWhnf nilBranch consBranch
        | .var | .unit | .lam | .app | .pair | .fst | .snd
        | .boolTrue | .boolFalse | .boolElim
        | .natZero | .natSucc | .natElim | .natRec
        | .listElim
        | .optionNone | .optionSome | .optionMatch
        | .eitherInl | .eitherInr | .eitherMatch
        | .refl | .idJ | .modIntro | .modElim | .subsume =>
            .listElim scrutineeWhnf nilBranch consBranch
    | .optionNone => .optionNone
    | .optionSome valueTerm => .optionSome valueTerm
    | .optionMatch scrutinee noneBranch someBranch =>
        let scrutineeWhnf := RawTerm.whnf fuel scrutinee
        match scrutineeWhnf.headCtor with
        | .optionNone =>
            RawTerm.whnf fuel noneBranch
        | .optionSome =>
            match RawTerm.optionSomeValue? scrutineeWhnf with
            | some valueTerm =>
                RawTerm.whnf fuel (.app someBranch valueTerm)
            | none =>
                .optionMatch scrutineeWhnf noneBranch someBranch
        | .var | .unit | .lam | .app | .pair | .fst | .snd
        | .boolTrue | .boolFalse | .boolElim
        | .natZero | .natSucc | .natElim | .natRec
        | .listNil | .listCons | .listElim
        | .optionMatch
        | .eitherInl | .eitherInr | .eitherMatch
        | .refl | .idJ | .modIntro | .modElim | .subsume =>
            .optionMatch scrutineeWhnf noneBranch someBranch
    | .eitherInl valueTerm => .eitherInl valueTerm
    | .eitherInr valueTerm => .eitherInr valueTerm
    | .eitherMatch scrutinee leftBranch rightBranch =>
        let scrutineeWhnf := RawTerm.whnf fuel scrutinee
        match scrutineeWhnf.headCtor with
        | .eitherInl =>
            match RawTerm.eitherInlValue? scrutineeWhnf with
            | some valueTerm =>
                RawTerm.whnf fuel (.app leftBranch valueTerm)
            | none =>
                .eitherMatch scrutineeWhnf leftBranch rightBranch
        | .eitherInr =>
            match RawTerm.eitherInrValue? scrutineeWhnf with
            | some valueTerm =>
                RawTerm.whnf fuel (.app rightBranch valueTerm)
            | none =>
                .eitherMatch scrutineeWhnf leftBranch rightBranch
        | .var | .unit | .lam | .app | .pair | .fst | .snd
        | .boolTrue | .boolFalse | .boolElim
        | .natZero | .natSucc | .natElim | .natRec
        | .listNil | .listCons | .listElim
        | .optionNone | .optionSome | .optionMatch
        | .eitherMatch
        | .refl | .idJ | .modIntro | .modElim | .subsume =>
            .eitherMatch scrutineeWhnf leftBranch rightBranch
    | .refl rawWitness => .refl rawWitness
    | .idJ baseCase witness =>
        let witnessWhnf := RawTerm.whnf fuel witness
        match witnessWhnf.headCtor with
        | .refl =>
            RawTerm.whnf fuel baseCase
        | .var | .unit | .lam | .app | .pair | .fst | .snd
        | .boolTrue | .boolFalse | .boolElim
        | .natZero | .natSucc | .natElim | .natRec
        | .listNil | .listCons | .listElim
        | .optionNone | .optionSome | .optionMatch
        | .eitherInl | .eitherInr | .eitherMatch
        | .idJ | .modIntro | .modElim | .subsume =>
            .idJ baseCase witnessWhnf
    -- Modal: no reduction rules yet (Layer 6 will add iotaModal).
    | .modIntro innerTerm => .modIntro innerTerm
    | .modElim innerTerm => .modElim innerTerm
    | .subsume innerTerm => .subsume innerTerm

end LeanFX2
