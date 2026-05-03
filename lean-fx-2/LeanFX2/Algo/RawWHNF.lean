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
  -- D1.6 cubical / HOTT / refine / record / codata / session / effect / strict
  | interval0 | interval1 | intervalOpp | intervalMeet | intervalJoin
  | pathLam | pathApp | glueIntro | glueElim | transp | hcomp
  | oeqRefl | oeqJ | oeqFunext | idStrictRefl | idStrictRec
  | equivIntro | equivApp | refineIntro | refineElim
  | recordIntro | recordProj | codataUnfold | codataDest
  | sessionSend | sessionRecv | effectPerform

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
  -- D1.6
  | .interval0 => .interval0 | .interval1 => .interval1
  | .intervalOpp _ => .intervalOpp
  | .intervalMeet _ _ => .intervalMeet
  | .intervalJoin _ _ => .intervalJoin
  | .pathLam _ => .pathLam | .pathApp _ _ => .pathApp
  | .glueIntro _ _ => .glueIntro | .glueElim _ => .glueElim
  | .transp _ _ => .transp | .hcomp _ _ => .hcomp
  | .oeqRefl _ => .oeqRefl | .oeqJ _ _ => .oeqJ
  | .oeqFunext _ => .oeqFunext
  | .idStrictRefl _ => .idStrictRefl | .idStrictRec _ _ => .idStrictRec
  | .equivIntro _ _ => .equivIntro | .equivApp _ _ => .equivApp
  | .refineIntro _ _ => .refineIntro | .refineElim _ => .refineElim
  | .recordIntro _ => .recordIntro | .recordProj _ => .recordProj
  | .codataUnfold _ _ => .codataUnfold | .codataDest _ => .codataDest
  | .sessionSend _ _ => .sessionSend | .sessionRecv _ => .sessionRecv
  | .effectPerform _ _ => .effectPerform

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
  | .interval0 => none | .interval1 => none
  | .intervalOpp _ => none | .intervalMeet _ _ => none | .intervalJoin _ _ => none
  | .pathLam _ => none | .pathApp _ _ => none
  | .glueIntro _ _ => none | .glueElim _ => none
  | .transp _ _ => none | .hcomp _ _ => none
  | .oeqRefl _ => none | .oeqJ _ _ => none | .oeqFunext _ => none
  | .idStrictRefl _ => none | .idStrictRec _ _ => none
  | .equivIntro _ _ => none | .equivApp _ _ => none
  | .refineIntro _ _ => none | .refineElim _ => none
  | .recordIntro _ => none | .recordProj _ => none
  | .codataUnfold _ _ => none | .codataDest _ => none
  | .sessionSend _ _ => none | .sessionRecv _ => none
  | .effectPerform _ _ => none

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
  | .interval0 => none | .interval1 => none
  | .intervalOpp _ => none | .intervalMeet _ _ => none | .intervalJoin _ _ => none
  | .pathLam _ => none | .pathApp _ _ => none
  | .glueIntro _ _ => none | .glueElim _ => none
  | .transp _ _ => none | .hcomp _ _ => none
  | .oeqRefl _ => none | .oeqJ _ _ => none | .oeqFunext _ => none
  | .idStrictRefl _ => none | .idStrictRec _ _ => none
  | .equivIntro _ _ => none | .equivApp _ _ => none
  | .refineIntro _ _ => none | .refineElim _ => none
  | .recordIntro _ => none | .recordProj _ => none
  | .codataUnfold _ _ => none | .codataDest _ => none
  | .sessionSend _ _ => none | .sessionRecv _ => none
  | .effectPerform _ _ => none

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
  | .interval0 => none | .interval1 => none
  | .intervalOpp _ => none | .intervalMeet _ _ => none | .intervalJoin _ _ => none
  | .pathLam _ => none | .pathApp _ _ => none
  | .glueIntro _ _ => none | .glueElim _ => none
  | .transp _ _ => none | .hcomp _ _ => none
  | .oeqRefl _ => none | .oeqJ _ _ => none | .oeqFunext _ => none
  | .idStrictRefl _ => none | .idStrictRec _ _ => none
  | .equivIntro _ _ => none | .equivApp _ _ => none
  | .refineIntro _ _ => none | .refineElim _ => none
  | .recordIntro _ => none | .recordProj _ => none
  | .codataUnfold _ _ => none | .codataDest _ => none
  | .sessionSend _ _ => none | .sessionRecv _ => none
  | .effectPerform _ _ => none

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
  | .interval0 => none | .interval1 => none
  | .intervalOpp _ => none | .intervalMeet _ _ => none | .intervalJoin _ _ => none
  | .pathLam _ => none | .pathApp _ _ => none
  | .glueIntro _ _ => none | .glueElim _ => none
  | .transp _ _ => none | .hcomp _ _ => none
  | .oeqRefl _ => none | .oeqJ _ _ => none | .oeqFunext _ => none
  | .idStrictRefl _ => none | .idStrictRec _ _ => none
  | .equivIntro _ _ => none | .equivApp _ _ => none
  | .refineIntro _ _ => none | .refineElim _ => none
  | .recordIntro _ => none | .recordProj _ => none
  | .codataUnfold _ _ => none | .codataDest _ => none
  | .sessionSend _ _ => none | .sessionRecv _ => none
  | .effectPerform _ _ => none

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
  | .interval0 => none | .interval1 => none
  | .intervalOpp _ => none | .intervalMeet _ _ => none | .intervalJoin _ _ => none
  | .pathLam _ => none | .pathApp _ _ => none
  | .glueIntro _ _ => none | .glueElim _ => none
  | .transp _ _ => none | .hcomp _ _ => none
  | .oeqRefl _ => none | .oeqJ _ _ => none | .oeqFunext _ => none
  | .idStrictRefl _ => none | .idStrictRec _ _ => none
  | .equivIntro _ _ => none | .equivApp _ _ => none
  | .refineIntro _ _ => none | .refineElim _ => none
  | .recordIntro _ => none | .recordProj _ => none
  | .codataUnfold _ _ => none | .codataDest _ => none
  | .sessionSend _ _ => none | .sessionRecv _ => none
  | .effectPerform _ _ => none

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
  | .interval0 => none | .interval1 => none
  | .intervalOpp _ => none | .intervalMeet _ _ => none | .intervalJoin _ _ => none
  | .pathLam _ => none | .pathApp _ _ => none
  | .glueIntro _ _ => none | .glueElim _ => none
  | .transp _ _ => none | .hcomp _ _ => none
  | .oeqRefl _ => none | .oeqJ _ _ => none | .oeqFunext _ => none
  | .idStrictRefl _ => none | .idStrictRec _ _ => none
  | .equivIntro _ _ => none | .equivApp _ _ => none
  | .refineIntro _ _ => none | .refineElim _ => none
  | .recordIntro _ => none | .recordProj _ => none
  | .codataUnfold _ _ => none | .codataDest _ => none
  | .sessionSend _ _ => none | .sessionRecv _ => none
  | .effectPerform _ _ => none

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
  | .interval0 => none | .interval1 => none
  | .intervalOpp _ => none | .intervalMeet _ _ => none | .intervalJoin _ _ => none
  | .pathLam _ => none | .pathApp _ _ => none
  | .glueIntro _ _ => none | .glueElim _ => none
  | .transp _ _ => none | .hcomp _ _ => none
  | .oeqRefl _ => none | .oeqJ _ _ => none | .oeqFunext _ => none
  | .idStrictRefl _ => none | .idStrictRec _ _ => none
  | .equivIntro _ _ => none | .equivApp _ _ => none
  | .refineIntro _ _ => none | .refineElim _ => none
  | .recordIntro _ => none | .recordProj _ => none
  | .codataUnfold _ _ => none | .codataDest _ => none
  | .sessionSend _ _ => none | .sessionRecv _ => none
  | .effectPerform _ _ => none

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
  | .interval0 => false | .interval1 => false
  | .intervalOpp _ => false | .intervalMeet _ _ => false | .intervalJoin _ _ => false
  | .pathLam _ => false | .pathApp _ _ => false
  | .glueIntro _ _ => false | .glueElim _ => false
  | .transp _ _ => false | .hcomp _ _ => false
  | .oeqRefl _ => false | .oeqJ _ _ => false | .oeqFunext _ => false
  | .idStrictRefl _ => false | .idStrictRec _ _ => false
  | .equivIntro _ _ => false | .equivApp _ _ => false
  | .refineIntro _ _ => false | .refineElim _ => false
  | .recordIntro _ => false | .recordProj _ => false
  | .codataUnfold _ _ => false | .codataDest _ => false
  | .sessionSend _ _ => false | .sessionRecv _ => false
  | .effectPerform _ _ => false

/-! ## Eq-witness recovery for the projection helpers

When a typed `Term.headStep?` dispatcher uses
`RawTerm.natSuccPred?` (etc) to detect a redex, it gets only an
Option result.  To then apply the typed `Term.natSuccDestruct`,
the dispatcher needs an Eq witness that the underlying raw IS
of the form `RawTerm.natSucc predRaw`.

These helpers recover that Eq from a `some predRaw` witness via
full-enum dispatch on the raw term.  Propext-clean (RawTerm is
non-indexed). -/

/-! Five iff-recovery lemmas, one per `?`-projection helper.
Each follows the match-with-witness pattern: combine `someTerm`
with the Eq witness, and non-matching ctors auto-discharge as
`none = some _` constructor mismatch.  Propext-clean. -/

/-- `term.natSuccPred? = some predRaw` implies `term = RawTerm.natSucc predRaw`. -/
theorem RawTerm.natSuccPred?_eq_some
    {scope : Nat} {someTerm : RawTerm scope} {predRaw : RawTerm scope}
    (witness : someTerm.natSuccPred? = some predRaw) :
    someTerm = RawTerm.natSucc predRaw :=
  match someTerm, witness with
  | .natSucc innerPred, witnessEq => by
      have someEq : (some innerPred : Option (RawTerm scope)) = some predRaw :=
        witnessEq
      injection someEq with predEq
      rw [predEq]

/-- `term.listConsParts? = some (h, t)` implies
`term = RawTerm.listCons h t`.  Uses direct `injection` on
both Option and Prod constructors — no propext via
`Prod.mk.injEq`. -/
theorem RawTerm.listConsParts?_eq_some
    {scope : Nat} {someTerm : RawTerm scope} {headRaw tailRaw : RawTerm scope}
    (witness : someTerm.listConsParts? = some (headRaw, tailRaw)) :
    someTerm = RawTerm.listCons headRaw tailRaw :=
  match someTerm, witness with
  | .listCons innerHead innerTail, witnessEq => by
      have someEq :
          (some (innerHead, innerTail) : Option (RawTerm scope × RawTerm scope))
            = some (headRaw, tailRaw) :=
        witnessEq
      injection someEq with pairEq
      injection pairEq with headEq tailEq
      rw [headEq, tailEq]

/-- `term.optionSomeValue? = some valueRaw` implies
`term = RawTerm.optionSome valueRaw`. -/
theorem RawTerm.optionSomeValue?_eq_some
    {scope : Nat} {someTerm : RawTerm scope} {valueRaw : RawTerm scope}
    (witness : someTerm.optionSomeValue? = some valueRaw) :
    someTerm = RawTerm.optionSome valueRaw :=
  match someTerm, witness with
  | .optionSome innerValue, witnessEq => by
      have someEq : (some innerValue : Option (RawTerm scope)) = some valueRaw :=
        witnessEq
      injection someEq with valueEq
      rw [valueEq]

/-- `term.eitherInlValue? = some valueRaw` implies
`term = RawTerm.eitherInl valueRaw`. -/
theorem RawTerm.eitherInlValue?_eq_some
    {scope : Nat} {someTerm : RawTerm scope} {valueRaw : RawTerm scope}
    (witness : someTerm.eitherInlValue? = some valueRaw) :
    someTerm = RawTerm.eitherInl valueRaw :=
  match someTerm, witness with
  | .eitherInl innerValue, witnessEq => by
      have someEq : (some innerValue : Option (RawTerm scope)) = some valueRaw :=
        witnessEq
      injection someEq with valueEq
      rw [valueEq]

/-- `term.eitherInrValue? = some valueRaw` implies
`term = RawTerm.eitherInr valueRaw`. -/
theorem RawTerm.eitherInrValue?_eq_some
    {scope : Nat} {someTerm : RawTerm scope} {valueRaw : RawTerm scope}
    (witness : someTerm.eitherInrValue? = some valueRaw) :
    someTerm = RawTerm.eitherInr valueRaw :=
  match someTerm, witness with
  | .eitherInr innerValue, witnessEq => by
      have someEq : (some innerValue : Option (RawTerm scope)) = some valueRaw :=
        witnessEq
      injection someEq with valueEq
      rw [valueEq]

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
        | .refl | .idJ | .modIntro | .modElim | .subsume
        | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
        | .pathLam | .pathApp | .glueIntro | .glueElim | .transp | .hcomp
        | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec
        | .equivIntro | .equivApp | .refineIntro | .refineElim
        | .recordIntro | .recordProj | .codataUnfold | .codataDest
        | .sessionSend | .sessionRecv | .effectPerform =>
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
        | .refl | .idJ | .modIntro | .modElim | .subsume
        | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
        | .pathLam | .pathApp | .glueIntro | .glueElim | .transp | .hcomp
        | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec
        | .equivIntro | .equivApp | .refineIntro | .refineElim
        | .recordIntro | .recordProj | .codataUnfold | .codataDest
        | .sessionSend | .sessionRecv | .effectPerform =>
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
        | .refl | .idJ | .modIntro | .modElim | .subsume
        | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
        | .pathLam | .pathApp | .glueIntro | .glueElim | .transp | .hcomp
        | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec
        | .equivIntro | .equivApp | .refineIntro | .refineElim
        | .recordIntro | .recordProj | .codataUnfold | .codataDest
        | .sessionSend | .sessionRecv | .effectPerform =>
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
        | .refl | .idJ | .modIntro | .modElim | .subsume
        | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
        | .pathLam | .pathApp | .glueIntro | .glueElim | .transp | .hcomp
        | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec
        | .equivIntro | .equivApp | .refineIntro | .refineElim
        | .recordIntro | .recordProj | .codataUnfold | .codataDest
        | .sessionSend | .sessionRecv | .effectPerform =>
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
        | .refl | .idJ | .modIntro | .modElim | .subsume
        | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
        | .pathLam | .pathApp | .glueIntro | .glueElim | .transp | .hcomp
        | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec
        | .equivIntro | .equivApp | .refineIntro | .refineElim
        | .recordIntro | .recordProj | .codataUnfold | .codataDest
        | .sessionSend | .sessionRecv | .effectPerform =>
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
        | .refl | .idJ | .modIntro | .modElim | .subsume
        | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
        | .pathLam | .pathApp | .glueIntro | .glueElim | .transp | .hcomp
        | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec
        | .equivIntro | .equivApp | .refineIntro | .refineElim
        | .recordIntro | .recordProj | .codataUnfold | .codataDest
        | .sessionSend | .sessionRecv | .effectPerform =>
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
        | .idJ | .modIntro | .modElim | .subsume
        | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
        | .pathLam | .pathApp | .glueIntro | .glueElim | .transp | .hcomp
        | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec
        | .equivIntro | .equivApp | .refineIntro | .refineElim
        | .recordIntro | .recordProj | .codataUnfold | .codataDest
        | .sessionSend | .sessionRecv | .effectPerform =>
            .idJ baseCase witnessWhnf
    -- Modal: no reduction rules yet (Layer 6 will add iotaModal).
    | .modIntro innerTerm => .modIntro innerTerm
    | .modElim innerTerm => .modElim innerTerm
    | .subsume innerTerm => .subsume innerTerm
    -- D1.6: 27 new ctors are terminal at WHNF (no β/ι rules at raw
    -- level yet; cubical/HOTT/refine/record/codata/session/effect
    -- reductions land in D2.5–D2.7).
    | .interval0 => .interval0
    | .interval1 => .interval1
    | .intervalOpp intervalTerm => .intervalOpp intervalTerm
    | .intervalMeet leftInterval rightInterval => .intervalMeet leftInterval rightInterval
    | .intervalJoin leftInterval rightInterval => .intervalJoin leftInterval rightInterval
    | .pathLam body => .pathLam body
    | .pathApp pathTerm intervalArg => .pathApp pathTerm intervalArg
    | .glueIntro baseValue partialValue => .glueIntro baseValue partialValue
    | .glueElim gluedValue => .glueElim gluedValue
    | .transp pathTerm sourceTerm => .transp pathTerm sourceTerm
    | .hcomp sidesTerm capTerm => .hcomp sidesTerm capTerm
    | .oeqRefl witnessTerm => .oeqRefl witnessTerm
    | .oeqJ baseCase witness => .oeqJ baseCase witness
    | .oeqFunext pointwiseEquality => .oeqFunext pointwiseEquality
    | .idStrictRefl witnessTerm => .idStrictRefl witnessTerm
    | .idStrictRec baseCase witness => .idStrictRec baseCase witness
    | .equivIntro forwardFn backwardFn => .equivIntro forwardFn backwardFn
    | .equivApp equivTerm argument => .equivApp equivTerm argument
    | .refineIntro rawValue predicateProof => .refineIntro rawValue predicateProof
    | .refineElim refinedValue => .refineElim refinedValue
    | .recordIntro firstField => .recordIntro firstField
    | .recordProj recordValue => .recordProj recordValue
    | .codataUnfold initialState transition => .codataUnfold initialState transition
    | .codataDest codataValue => .codataDest codataValue
    | .sessionSend channel payload => .sessionSend channel payload
    | .sessionRecv channel => .sessionRecv channel
    | .effectPerform operationTag arguments => .effectPerform operationTag arguments

end LeanFX2
