import LeanFX2.Reduction.Step

/-! # Algo/WHNF — weak head normal form classifier

`Term.isWHNF` returns `true` iff a typed term is in **weak head normal
form** — that is, the head constructor is a value-form (lam, pair,
refl, ...) or a neutral form (variable, application of variable, or
elimination of a neutral) rather than a redex.

## WHNF classification table

| Head ctor | WHNF? | Reason |
|---|---|---|
| `var` | yes | head reduction stops at variables |
| `unit`, `boolTrue`, `boolFalse`, `natZero` | yes | canonical leaf values |
| `lam`, `lamPi`, `pair`, `refl` | yes | value introductions |
| `natSucc t` | yes | canonical successor |
| `listNil`, `listCons _ _` | yes | canonical list values |
| `optionNone`, `optionSome _` | yes | canonical option values |
| `eitherInl _`, `eitherInr _` | yes | canonical either values |
| `modIntro _`, `subsume _` | yes | modal value introduction |
| `app (lam _) _` | NO | β-redex |
| `appPi (lamPi _) _` | NO | β-redex (Π) |
| `fst (pair _ _)`, `snd (pair _ _)` | NO | β-redex (Σ projection) |
| `boolElim` of canonical bool | NO | ι-redex |
| `natElim/natRec` of canonical nat | NO | ι-redex |
| `listElim` of canonical list | NO | ι-redex |
| `optionMatch` of canonical option | NO | ι-redex |
| `eitherMatch` of canonical either | NO | ι-redex |
| `idJ _ (refl _ _)` | NO | ι-redex |
| `modElim (modIntro _)` | NO | ι-redex (modal) |
| any eliminator on neutral | yes | neutral |

## Why classify

`Algo/DecConv` decides convertibility by reducing both sides to WHNF
and structurally comparing.  WHNF is finer than full normal form
(strictly weaker reduction), but enough for decidable conversion
because Church-Rosser ensures common reducts share WHNF heads.

## Implementation discipline

To avoid propext leaks (wildcards on dep-indexed matches always leak),
we project Term ctor identity to a flat enum `Term.HeadCtor` via full
enumeration first, then use Bool dispatch on the flat enum.  The
result: `Term.isWHNF` is zero-axiom.
-/

namespace LeanFX2

/-- Flat enum tagging the head constructor of a `Term`.  Used by
`isWHNF` to dispatch on the head shape without nested dep-indexed
matches that would leak `propext`. -/
inductive Term.HeadCtor : Type
  | var
  | unit
  | lam
  | app
  | lamPi
  | appPi
  | pair
  | fst
  | snd
  | boolTrue
  | boolFalse
  | boolElim
  | natZero
  | natSucc
  | natElim
  | natRec
  | listNil
  | listCons
  | listElim
  | optionNone
  | optionSome
  | optionMatch
  | eitherInl
  | eitherInr
  | eitherMatch
  | refl
  | idJ
  | idStrictRefl
  | idStrictRec
  | modIntro
  | modElim
  | subsume
  | interval0
  | interval1
  | intervalOpp
  | intervalMeet
  | intervalJoin
  | pathLam
  | pathApp
  | glueIntro
  | glueElim
  | transp
  | hcomp
  | recordIntro
  | recordProj
  | refineIntro
  | refineElim
  | codataUnfold
  | codataDest
  | sessionSend
  | sessionRecv
  | effectPerform
  | universeCode
  | cumulUp
  | equivReflId
  | funextRefl
  | equivReflIdAtId
  | funextReflAtId
  | equivIntroHet
  | equivApp
  | uaIntroHet
  | funextIntroHet
  -- CUMUL-2.4 typed type-code constructors (VALUE-shaped).
  | arrowCode
  | piTyCode
  | sigmaTyCode
  | productCode
  | sumCode
  | listCode
  | optionCode
  | eitherCode
  | idCode
  | equivCode
  deriving DecidableEq

/-- Project a typed Term to its flat head-ctor tag.  Full enumeration
of all current ctors — no wildcards, so no propext leak. -/
def Term.headCtor {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context someType raw) : Term.HeadCtor :=
  match someTerm with
  | .var _ => .var
  | .unit => .unit
  | .lam _ => .lam
  | .app _ _ => .app
  | .lamPi _ => .lamPi
  | .appPi _ _ => .appPi
  | .pair _ _ => .pair
  | .fst _ => .fst
  | .snd _ => .snd
  | .boolTrue => .boolTrue
  | .boolFalse => .boolFalse
  | .boolElim _ _ _ => .boolElim
  | .natZero => .natZero
  | .natSucc _ => .natSucc
  | .natElim _ _ _ => .natElim
  | .natRec _ _ _ => .natRec
  | .listNil => .listNil
  | .listCons _ _ => .listCons
  | .listElim _ _ _ => .listElim
  | .optionNone => .optionNone
  | .optionSome _ => .optionSome
  | .optionMatch _ _ _ => .optionMatch
  | .eitherInl _ => .eitherInl
  | .eitherInr _ => .eitherInr
  | .eitherMatch _ _ _ => .eitherMatch
  | .refl _ _ => .refl
  | .idJ _ _ => .idJ
  | .idStrictRefl _ _ => .idStrictRefl
  | .idStrictRec _ _ => .idStrictRec
  | .modIntro _ => .modIntro
  | .modElim _ => .modElim
  | .subsume _ => .subsume
  | .interval0 => .interval0
  | .interval1 => .interval1
  | .intervalOpp _ => .intervalOpp
  | .intervalMeet _ _ => .intervalMeet
  | .intervalJoin _ _ => .intervalJoin
  | .pathLam _ _ _ _ => .pathLam
  | .pathApp _ _ => .pathApp
  | .glueIntro _ _ _ _ => .glueIntro
  | .glueElim _ => .glueElim
  | .transp _ _ _ _ _ _ _ _ => .transp
  | .hcomp _ _ => .hcomp
  | .recordIntro _ => .recordIntro
  | .recordProj _ => .recordProj
  | .refineIntro _ _ _ => .refineIntro
  | .refineElim _ => .refineElim
  | .codataUnfold _ _ => .codataUnfold
  | .codataDest _ => .codataDest
  | .sessionSend _ _ _ => .sessionSend
  | .sessionRecv _ => .sessionRecv
  | .effectPerform _ _ _ => .effectPerform
  | .universeCode _ _ _ _ => .universeCode
  | .cumulUp _ _ _ _ _ _ => .cumulUp
  | .equivReflId _ => .equivReflId
  | .funextRefl _ _ _ => .funextRefl
  | .equivReflIdAtId _ _ _ _ => .equivReflIdAtId
  | .funextReflAtId _ _ _ => .funextReflAtId
  | .equivIntroHet _ _ => .equivIntroHet
  | .equivApp _ _ => .equivApp
  | .uaIntroHet _ _ _ _ _ => .uaIntroHet
  | .funextIntroHet _ _ _ _ => .funextIntroHet
  -- CUMUL-2.4 typed type-code constructors (VALUE-shaped).
  | .arrowCode _ _ _ _ => .arrowCode
  | .piTyCode _ _ _ _ => .piTyCode
  | .sigmaTyCode _ _ _ _ => .sigmaTyCode
  | .productCode _ _ _ _ => .productCode
  | .sumCode _ _ _ _ => .sumCode
  | .listCode _ _ _ => .listCode
  | .optionCode _ _ _ => .optionCode
  | .eitherCode _ _ _ _ => .eitherCode
  | .idCode _ _ _ _ _ => .idCode
  | .equivCode _ _ _ _ => .equivCode

/-- True iff the Term is in weak head normal form: head ctor is not
a β/ι redex.  Recursion happens only on the immediate head shape;
deeper redexes elsewhere don't disqualify WHNF.  Implemented via
`Term.headCtor` projection to keep the dispatch propext-free. -/
def Term.isWHNF {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context someType raw) : Bool :=
  match someTerm with
  -- Variables and canonical leaf values are WHNF
  | .var _ => true
  | .unit => true
  | .boolTrue => true
  | .boolFalse => true
  | .natZero => true
  | .listNil => true
  | .optionNone => true
  -- Value introductions are WHNF
  | .lam _ => true
  | .lamPi _ => true
  | .pair _ _ => true
  | .refl _ _ => true
  | .idStrictRefl _ _ => true
  | .natSucc _ => true
  | .listCons _ _ => true
  | .optionSome _ => true
  | .eitherInl _ => true
  | .eitherInr _ => true
  | .modIntro _ => true
  | .subsume _ => true
  | .interval0 => true
  | .interval1 => true
  | .intervalOpp _ => true
  | .intervalMeet _ _ => true
  | .intervalJoin _ _ => true
  | .pathLam _ _ _ _ => true
  | .glueIntro _ _ _ _ => true
  | .transp _ _ _ _ _ _ _ _ => true
  | .hcomp _ _ => true
  | .recordIntro _ => true
  | .refineIntro _ _ _ => true
  | .codataUnfold _ _ => true
  | .sessionSend _ _ _ => true
  | .sessionRecv _ => true
  | .effectPerform _ _ _ => true
  -- Universe-code is a value (no β/ι redex possible at this head)
  | .universeCode _ _ _ _ => true
  -- Cumul-up is a value (the inner term is a closed universe-code,
  -- and cumulUp itself is not a β/ι redex head)
  | .cumulUp _ _ _ _ _ _ => true
  -- HoTT canonical equivalence/funext refl-fragment witnesses are
  -- values (not β/ι redex heads).
  | .equivReflId _ => true
  | .funextRefl _ _ _ => true
  | .equivReflIdAtId _ _ _ _ => true
  | .funextReflAtId _ _ _ => true
  -- HoTT heterogeneous-carrier equivIntroHet is a value (canonical
  -- equivalence form, not a β/ι redex head).
  | .equivIntroHet _ _ => true
  -- Equivalence application has congruence parity only; no raw β-rule
  -- fires from `RawTerm.equivApp` in the current Day 2 layer.
  | .equivApp _ _ => true
  -- HoTT heterogeneous-carrier uaIntroHet (Phase 12.A.B8.5b) is a value
  -- (canonical path-from-equivalence form at the universe; the future
  -- Step.eqTypeHet rule reduces from it but the headStep? machinery
  -- doesn't yet fire it).
  | .uaIntroHet _ _ _ _ _ => true
  -- HoTT heterogeneous-carrier funextIntroHet (Phase 12.A.B8.8) is a value
  -- (canonical heterogeneous-funext witness at Id-of-arrow; the future
  -- Step.eqArrowHet rule reduces from it but headStep? doesn't yet
  -- fire it).
  | .funextIntroHet _ _ _ _ => true
  -- CUMUL-2.4 typed type-code constructors (VALUE-shaped, all WHNF —
  -- not β/ι redex heads).  No new Step rules fire from these ctors.
  | .arrowCode _ _ _ _ => true
  | .piTyCode _ _ _ _ => true
  | .sigmaTyCode _ _ _ _ => true
  | .productCode _ _ _ _ => true
  | .sumCode _ _ _ _ => true
  | .listCode _ _ _ => true
  | .optionCode _ _ _ => true
  | .eitherCode _ _ _ _ => true
  | .idCode _ _ _ _ _ => true
  | .equivCode _ _ _ _ => true
  -- Application is WHNF iff function head is NOT .lam
  | .app functionTerm _ =>
      !(functionTerm.headCtor == .lam)
  -- Π-application is WHNF iff function head is NOT .lamPi
  | .appPi functionTerm _ =>
      !(functionTerm.headCtor == .lamPi)
  -- Σ projections are WHNF iff pair head is NOT .pair
  | .fst pairTerm =>
      !(pairTerm.headCtor == .pair)
  | .snd pairTerm =>
      !(pairTerm.headCtor == .pair)
  -- Boolean elimination is WHNF iff scrutinee head is not a canonical bool
  | .boolElim scrutinee _ _ =>
      let scrutineeHead := scrutinee.headCtor
      !(scrutineeHead == .boolTrue) && !(scrutineeHead == .boolFalse)
  -- Nat elimination is WHNF iff scrutinee head is not a canonical nat
  | .natElim scrutinee _ _ =>
      let scrutineeHead := scrutinee.headCtor
      !(scrutineeHead == .natZero) && !(scrutineeHead == .natSucc)
  | .natRec scrutinee _ _ =>
      let scrutineeHead := scrutinee.headCtor
      !(scrutineeHead == .natZero) && !(scrutineeHead == .natSucc)
  -- List elimination
  | .listElim scrutinee _ _ =>
      let scrutineeHead := scrutinee.headCtor
      !(scrutineeHead == .listNil) && !(scrutineeHead == .listCons)
  -- Option match
  | .optionMatch scrutinee _ _ =>
      let scrutineeHead := scrutinee.headCtor
      !(scrutineeHead == .optionNone) && !(scrutineeHead == .optionSome)
  -- Either match
  | .eitherMatch scrutinee _ _ =>
      let scrutineeHead := scrutinee.headCtor
      !(scrutineeHead == .eitherInl) && !(scrutineeHead == .eitherInr)
  -- Identity J: WHNF iff witness head is NOT .refl
  | .idJ _ witness =>
      !(witness.headCtor == .refl)
  -- Strict identity recursor currently has cong parity only; no strict
  -- β-rule is present in the raw layer, so it is neutral at WHNF.
  | .idStrictRec _ _ => true
  -- Modal eliminator: WHNF iff inner head is NOT .modIntro
  | .modElim innerTerm =>
      !(innerTerm.headCtor == .modIntro)
  -- Path application is WHNF iff the path head is NOT .pathLam.
  | .pathApp pathTerm _ =>
      !(pathTerm.headCtor == .pathLam)
  -- Glue elimination is WHNF iff the glued value head is NOT .glueIntro.
  | .glueElim gluedValue =>
      !(gluedValue.headCtor == .glueIntro)
  -- Record projection is WHNF iff the record head is NOT .recordIntro.
  | .recordProj recordValue =>
      !(recordValue.headCtor == .recordIntro)
  | .refineElim refinedValue =>
      !(refinedValue.headCtor == .refineIntro)
  -- Codata destruction currently has congruence parity only; the raw
  -- layer has no codata observation β-rule yet.
  | .codataDest _ => true

/-! ## headCtor inversion bridges

If `term.headCtor = X`, then term's raw form is uniquely determined
by `X` for nullary canonical heads (boolTrue/False, natZero, listNil,
optionNone).  These bridge lemmas convert the Bool-level dispatch
in `Term.headStep?` back into typed-level facts about the term's
raw projection — useful for deriving Step witnesses from headStep?
behavior (Algo/Soundness, Phase 9.G). -/

/-- If a term's `headCtor` is `boolTrue`, its raw projection
is `RawTerm.boolTrue`.  Zero-axiom via full Term enumeration with
`nomatch` for the contradictory cases. -/
theorem Term.headCtor_boolTrue_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.boolTrue) :
    raw = RawTerm.boolTrue := by
  cases someTerm with
  | var _ => nomatch headEq
  | unit => nomatch headEq
  | lam _ => nomatch headEq
  | app _ _ => nomatch headEq
  | lamPi _ => nomatch headEq
  | appPi _ _ => nomatch headEq
  | pair _ _ => nomatch headEq
  | fst _ => nomatch headEq
  | snd _ => nomatch headEq
  | boolTrue => rfl
  | boolFalse => nomatch headEq
  | boolElim _ _ _ => nomatch headEq
  | natZero => nomatch headEq
  | natSucc _ => nomatch headEq
  | natElim _ _ _ => nomatch headEq
  | natRec _ _ _ => nomatch headEq
  | listNil => nomatch headEq
  | listCons _ _ => nomatch headEq
  | listElim _ _ _ => nomatch headEq
  | optionNone => nomatch headEq
  | optionSome _ => nomatch headEq
  | optionMatch _ _ _ => nomatch headEq
  | eitherInl _ => nomatch headEq
  | eitherInr _ => nomatch headEq
  | eitherMatch _ _ _ => nomatch headEq
  | refl _ _ => nomatch headEq
  | idJ _ _ => nomatch headEq
  | idStrictRefl _ _ => nomatch headEq
  | idStrictRec _ _ => nomatch headEq
  | modIntro _ => nomatch headEq
  | modElim _ => nomatch headEq
  | subsume _ => nomatch headEq
  | interval0 => nomatch headEq
  | interval1 => nomatch headEq
  | intervalOpp _ => nomatch headEq
  | intervalMeet _ _ => nomatch headEq
  | intervalJoin _ _ => nomatch headEq
  | pathLam _ _ _ _ => nomatch headEq
  | pathApp _ _ => nomatch headEq
  | glueIntro _ _ _ _ => nomatch headEq
  | glueElim _ => nomatch headEq
  | transp _ _ _ _ _ _ _ _ => nomatch headEq
  | hcomp _ _ => nomatch headEq
  | recordIntro _ => nomatch headEq
  | recordProj _ => nomatch headEq
  | refineIntro _ _ _ => nomatch headEq
  | refineElim _ => nomatch headEq
  | codataUnfold _ _ => nomatch headEq
  | codataDest _ => nomatch headEq
  | sessionSend _ _ _ => nomatch headEq
  | sessionRecv _ => nomatch headEq
  | effectPerform _ _ _ => nomatch headEq
  | universeCode _ _ _ _ => nomatch headEq
  | cumulUp _ _ _ _ _ _ => nomatch headEq
  | equivReflId _ => nomatch headEq
  | funextRefl _ _ _ => nomatch headEq
  | equivReflIdAtId _ _ _ _ => nomatch headEq
  | funextReflAtId _ _ _ => nomatch headEq
  | equivIntroHet _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If a term's `headCtor` is `boolFalse`, its raw is `RawTerm.boolFalse`. -/
theorem Term.headCtor_boolFalse_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.boolFalse) :
    raw = RawTerm.boolFalse := by
  cases someTerm with
  | var _ => nomatch headEq
  | unit => nomatch headEq
  | lam _ => nomatch headEq
  | app _ _ => nomatch headEq
  | lamPi _ => nomatch headEq
  | appPi _ _ => nomatch headEq
  | pair _ _ => nomatch headEq
  | fst _ => nomatch headEq
  | snd _ => nomatch headEq
  | boolTrue => nomatch headEq
  | boolFalse => rfl
  | boolElim _ _ _ => nomatch headEq
  | natZero => nomatch headEq
  | natSucc _ => nomatch headEq
  | natElim _ _ _ => nomatch headEq
  | natRec _ _ _ => nomatch headEq
  | listNil => nomatch headEq
  | listCons _ _ => nomatch headEq
  | listElim _ _ _ => nomatch headEq
  | optionNone => nomatch headEq
  | optionSome _ => nomatch headEq
  | optionMatch _ _ _ => nomatch headEq
  | eitherInl _ => nomatch headEq
  | eitherInr _ => nomatch headEq
  | eitherMatch _ _ _ => nomatch headEq
  | refl _ _ => nomatch headEq
  | idJ _ _ => nomatch headEq
  | idStrictRefl _ _ => nomatch headEq
  | idStrictRec _ _ => nomatch headEq
  | modIntro _ => nomatch headEq
  | modElim _ => nomatch headEq
  | subsume _ => nomatch headEq
  | interval0 => nomatch headEq
  | interval1 => nomatch headEq
  | intervalOpp _ => nomatch headEq
  | intervalMeet _ _ => nomatch headEq
  | intervalJoin _ _ => nomatch headEq
  | pathLam _ _ _ _ => nomatch headEq
  | pathApp _ _ => nomatch headEq
  | glueIntro _ _ _ _ => nomatch headEq
  | glueElim _ => nomatch headEq
  | transp _ _ _ _ _ _ _ _ => nomatch headEq
  | hcomp _ _ => nomatch headEq
  | recordIntro _ => nomatch headEq
  | recordProj _ => nomatch headEq
  | refineIntro _ _ _ => nomatch headEq
  | refineElim _ => nomatch headEq
  | codataUnfold _ _ => nomatch headEq
  | codataDest _ => nomatch headEq
  | sessionSend _ _ _ => nomatch headEq
  | sessionRecv _ => nomatch headEq
  | effectPerform _ _ _ => nomatch headEq
  | universeCode _ _ _ _ => nomatch headEq
  | cumulUp _ _ _ _ _ _ => nomatch headEq
  | equivReflId _ => nomatch headEq
  | funextRefl _ _ _ => nomatch headEq
  | equivReflIdAtId _ _ _ _ => nomatch headEq
  | funextReflAtId _ _ _ => nomatch headEq
  | equivIntroHet _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If a term's `headCtor` is `natZero`, its raw is `RawTerm.natZero`. -/
theorem Term.headCtor_natZero_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.natZero) :
    raw = RawTerm.natZero := by
  cases someTerm with
  | var _ => nomatch headEq
  | unit => nomatch headEq
  | lam _ => nomatch headEq
  | app _ _ => nomatch headEq
  | lamPi _ => nomatch headEq
  | appPi _ _ => nomatch headEq
  | pair _ _ => nomatch headEq
  | fst _ => nomatch headEq
  | snd _ => nomatch headEq
  | boolTrue => nomatch headEq
  | boolFalse => nomatch headEq
  | boolElim _ _ _ => nomatch headEq
  | natZero => rfl
  | natSucc _ => nomatch headEq
  | natElim _ _ _ => nomatch headEq
  | natRec _ _ _ => nomatch headEq
  | listNil => nomatch headEq
  | listCons _ _ => nomatch headEq
  | listElim _ _ _ => nomatch headEq
  | optionNone => nomatch headEq
  | optionSome _ => nomatch headEq
  | optionMatch _ _ _ => nomatch headEq
  | eitherInl _ => nomatch headEq
  | eitherInr _ => nomatch headEq
  | eitherMatch _ _ _ => nomatch headEq
  | refl _ _ => nomatch headEq
  | idJ _ _ => nomatch headEq
  | idStrictRefl _ _ => nomatch headEq
  | idStrictRec _ _ => nomatch headEq
  | modIntro _ => nomatch headEq
  | modElim _ => nomatch headEq
  | subsume _ => nomatch headEq
  | interval0 => nomatch headEq
  | interval1 => nomatch headEq
  | intervalOpp _ => nomatch headEq
  | intervalMeet _ _ => nomatch headEq
  | intervalJoin _ _ => nomatch headEq
  | pathLam _ _ _ _ => nomatch headEq
  | pathApp _ _ => nomatch headEq
  | glueIntro _ _ _ _ => nomatch headEq
  | glueElim _ => nomatch headEq
  | transp _ _ _ _ _ _ _ _ => nomatch headEq
  | hcomp _ _ => nomatch headEq
  | recordIntro _ => nomatch headEq
  | recordProj _ => nomatch headEq
  | refineIntro _ _ _ => nomatch headEq
  | refineElim _ => nomatch headEq
  | codataUnfold _ _ => nomatch headEq
  | codataDest _ => nomatch headEq
  | sessionSend _ _ _ => nomatch headEq
  | sessionRecv _ => nomatch headEq
  | effectPerform _ _ _ => nomatch headEq
  | universeCode _ _ _ _ => nomatch headEq
  | cumulUp _ _ _ _ _ _ => nomatch headEq
  | equivReflId _ => nomatch headEq
  | funextRefl _ _ _ => nomatch headEq
  | equivReflIdAtId _ _ _ _ => nomatch headEq
  | funextReflAtId _ _ _ => nomatch headEq
  | equivIntroHet _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If a term's `headCtor` is `listNil`, its raw is `RawTerm.listNil`. -/
theorem Term.headCtor_listNil_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.listNil) :
    raw = RawTerm.listNil := by
  cases someTerm with
  | var _ => nomatch headEq
  | unit => nomatch headEq
  | lam _ => nomatch headEq
  | app _ _ => nomatch headEq
  | lamPi _ => nomatch headEq
  | appPi _ _ => nomatch headEq
  | pair _ _ => nomatch headEq
  | fst _ => nomatch headEq
  | snd _ => nomatch headEq
  | boolTrue => nomatch headEq
  | boolFalse => nomatch headEq
  | boolElim _ _ _ => nomatch headEq
  | natZero => nomatch headEq
  | natSucc _ => nomatch headEq
  | natElim _ _ _ => nomatch headEq
  | natRec _ _ _ => nomatch headEq
  | listNil => rfl
  | listCons _ _ => nomatch headEq
  | listElim _ _ _ => nomatch headEq
  | optionNone => nomatch headEq
  | optionSome _ => nomatch headEq
  | optionMatch _ _ _ => nomatch headEq
  | eitherInl _ => nomatch headEq
  | eitherInr _ => nomatch headEq
  | eitherMatch _ _ _ => nomatch headEq
  | refl _ _ => nomatch headEq
  | idJ _ _ => nomatch headEq
  | idStrictRefl _ _ => nomatch headEq
  | idStrictRec _ _ => nomatch headEq
  | modIntro _ => nomatch headEq
  | modElim _ => nomatch headEq
  | subsume _ => nomatch headEq
  | interval0 => nomatch headEq
  | interval1 => nomatch headEq
  | intervalOpp _ => nomatch headEq
  | intervalMeet _ _ => nomatch headEq
  | intervalJoin _ _ => nomatch headEq
  | pathLam _ _ _ _ => nomatch headEq
  | pathApp _ _ => nomatch headEq
  | glueIntro _ _ _ _ => nomatch headEq
  | glueElim _ => nomatch headEq
  | transp _ _ _ _ _ _ _ _ => nomatch headEq
  | hcomp _ _ => nomatch headEq
  | recordIntro _ => nomatch headEq
  | recordProj _ => nomatch headEq
  | refineIntro _ _ _ => nomatch headEq
  | refineElim _ => nomatch headEq
  | codataUnfold _ _ => nomatch headEq
  | codataDest _ => nomatch headEq
  | sessionSend _ _ _ => nomatch headEq
  | sessionRecv _ => nomatch headEq
  | effectPerform _ _ _ => nomatch headEq
  | universeCode _ _ _ _ => nomatch headEq
  | cumulUp _ _ _ _ _ _ => nomatch headEq
  | equivReflId _ => nomatch headEq
  | funextRefl _ _ _ => nomatch headEq
  | equivReflIdAtId _ _ _ _ => nomatch headEq
  | funextReflAtId _ _ _ => nomatch headEq
  | equivIntroHet _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If a term's `headCtor` is `optionNone`, its raw is `RawTerm.optionNone`. -/
theorem Term.headCtor_optionNone_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.optionNone) :
    raw = RawTerm.optionNone := by
  cases someTerm with
  | var _ => nomatch headEq
  | unit => nomatch headEq
  | lam _ => nomatch headEq
  | app _ _ => nomatch headEq
  | lamPi _ => nomatch headEq
  | appPi _ _ => nomatch headEq
  | pair _ _ => nomatch headEq
  | fst _ => nomatch headEq
  | snd _ => nomatch headEq
  | boolTrue => nomatch headEq
  | boolFalse => nomatch headEq
  | boolElim _ _ _ => nomatch headEq
  | natZero => nomatch headEq
  | natSucc _ => nomatch headEq
  | natElim _ _ _ => nomatch headEq
  | natRec _ _ _ => nomatch headEq
  | listNil => nomatch headEq
  | listCons _ _ => nomatch headEq
  | listElim _ _ _ => nomatch headEq
  | optionNone => rfl
  | optionSome _ => nomatch headEq
  | optionMatch _ _ _ => nomatch headEq
  | eitherInl _ => nomatch headEq
  | eitherInr _ => nomatch headEq
  | eitherMatch _ _ _ => nomatch headEq
  | refl _ _ => nomatch headEq
  | idJ _ _ => nomatch headEq
  | idStrictRefl _ _ => nomatch headEq
  | idStrictRec _ _ => nomatch headEq
  | modIntro _ => nomatch headEq
  | modElim _ => nomatch headEq
  | subsume _ => nomatch headEq
  | interval0 => nomatch headEq
  | interval1 => nomatch headEq
  | intervalOpp _ => nomatch headEq
  | intervalMeet _ _ => nomatch headEq
  | intervalJoin _ _ => nomatch headEq
  | pathLam _ _ _ _ => nomatch headEq
  | pathApp _ _ => nomatch headEq
  | glueIntro _ _ _ _ => nomatch headEq
  | glueElim _ => nomatch headEq
  | transp _ _ _ _ _ _ _ _ => nomatch headEq
  | hcomp _ _ => nomatch headEq
  | recordIntro _ => nomatch headEq
  | recordProj _ => nomatch headEq
  | refineIntro _ _ _ => nomatch headEq
  | refineElim _ => nomatch headEq
  | codataUnfold _ _ => nomatch headEq
  | codataDest _ => nomatch headEq
  | sessionSend _ _ _ => nomatch headEq
  | sessionRecv _ => nomatch headEq
  | effectPerform _ _ _ => nomatch headEq
  | universeCode _ _ _ _ => nomatch headEq
  | cumulUp _ _ _ _ _ _ => nomatch headEq
  | equivReflId _ => nomatch headEq
  | funextRefl _ _ _ => nomatch headEq
  | equivReflIdAtId _ _ _ _ => nomatch headEq
  | funextReflAtId _ _ _ => nomatch headEq
  | equivIntroHet _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-! ## Payload-bearing canonical heads — existential raw recovery

For `natSucc / listCons / optionSome / eitherInl / eitherInr`,
the raw form has a payload (predecessor / head-tail / value).
Each headCtor witness gives an EXISTENTIAL: the raw is some
ctor-application with a specific payload.

These extend the no-payload lemmas above to support extending
`Term.headStep?` with payload-bearing β/ι firings (M08). -/

/-- If `someTerm.headCtor = .natSucc`, the raw is `natSucc`-shaped
for some predecessor raw. -/
theorem Term.headCtor_natSucc_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.natSucc) :
    ∃ (predRaw : RawTerm scope), raw = RawTerm.natSucc predRaw := by
  cases someTerm with
  | var _ => nomatch headEq
  | unit => nomatch headEq
  | lam _ => nomatch headEq
  | app _ _ => nomatch headEq
  | lamPi _ => nomatch headEq
  | appPi _ _ => nomatch headEq
  | pair _ _ => nomatch headEq
  | fst _ => nomatch headEq
  | snd _ => nomatch headEq
  | boolTrue => nomatch headEq
  | boolFalse => nomatch headEq
  | boolElim _ _ _ => nomatch headEq
  | natZero => nomatch headEq
  | natSucc _ => exact ⟨_, rfl⟩
  | natElim _ _ _ => nomatch headEq
  | natRec _ _ _ => nomatch headEq
  | listNil => nomatch headEq
  | listCons _ _ => nomatch headEq
  | listElim _ _ _ => nomatch headEq
  | optionNone => nomatch headEq
  | optionSome _ => nomatch headEq
  | optionMatch _ _ _ => nomatch headEq
  | eitherInl _ => nomatch headEq
  | eitherInr _ => nomatch headEq
  | eitherMatch _ _ _ => nomatch headEq
  | refl _ _ => nomatch headEq
  | idJ _ _ => nomatch headEq
  | idStrictRefl _ _ => nomatch headEq
  | idStrictRec _ _ => nomatch headEq
  | modIntro _ => nomatch headEq
  | modElim _ => nomatch headEq
  | subsume _ => nomatch headEq
  | interval0 => nomatch headEq
  | interval1 => nomatch headEq
  | intervalOpp _ => nomatch headEq
  | intervalMeet _ _ => nomatch headEq
  | intervalJoin _ _ => nomatch headEq
  | pathLam _ _ _ _ => nomatch headEq
  | pathApp _ _ => nomatch headEq
  | glueIntro _ _ _ _ => nomatch headEq
  | glueElim _ => nomatch headEq
  | transp _ _ _ _ _ _ _ _ => nomatch headEq
  | hcomp _ _ => nomatch headEq
  | recordIntro _ => nomatch headEq
  | recordProj _ => nomatch headEq
  | refineIntro _ _ _ => nomatch headEq
  | refineElim _ => nomatch headEq
  | codataUnfold _ _ => nomatch headEq
  | codataDest _ => nomatch headEq
  | sessionSend _ _ _ => nomatch headEq
  | sessionRecv _ => nomatch headEq
  | effectPerform _ _ _ => nomatch headEq
  | universeCode _ _ _ _ => nomatch headEq
  | cumulUp _ _ _ _ _ _ => nomatch headEq
  | equivReflId _ => nomatch headEq
  | funextRefl _ _ _ => nomatch headEq
  | equivReflIdAtId _ _ _ _ => nomatch headEq
  | funextReflAtId _ _ _ => nomatch headEq
  | equivIntroHet _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If `someTerm.headCtor = .listCons`, the raw is `listCons`-shaped. -/
theorem Term.headCtor_listCons_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.listCons) :
    ∃ (headRaw tailRaw : RawTerm scope), raw = RawTerm.listCons headRaw tailRaw := by
  cases someTerm with
  | var _ => nomatch headEq
  | unit => nomatch headEq
  | lam _ => nomatch headEq
  | app _ _ => nomatch headEq
  | lamPi _ => nomatch headEq
  | appPi _ _ => nomatch headEq
  | pair _ _ => nomatch headEq
  | fst _ => nomatch headEq
  | snd _ => nomatch headEq
  | boolTrue => nomatch headEq
  | boolFalse => nomatch headEq
  | boolElim _ _ _ => nomatch headEq
  | natZero => nomatch headEq
  | natSucc _ => nomatch headEq
  | natElim _ _ _ => nomatch headEq
  | natRec _ _ _ => nomatch headEq
  | listNil => nomatch headEq
  | listCons _ _ => exact ⟨_, _, rfl⟩
  | listElim _ _ _ => nomatch headEq
  | optionNone => nomatch headEq
  | optionSome _ => nomatch headEq
  | optionMatch _ _ _ => nomatch headEq
  | eitherInl _ => nomatch headEq
  | eitherInr _ => nomatch headEq
  | eitherMatch _ _ _ => nomatch headEq
  | refl _ _ => nomatch headEq
  | idJ _ _ => nomatch headEq
  | idStrictRefl _ _ => nomatch headEq
  | idStrictRec _ _ => nomatch headEq
  | modIntro _ => nomatch headEq
  | modElim _ => nomatch headEq
  | subsume _ => nomatch headEq
  | interval0 => nomatch headEq
  | interval1 => nomatch headEq
  | intervalOpp _ => nomatch headEq
  | intervalMeet _ _ => nomatch headEq
  | intervalJoin _ _ => nomatch headEq
  | pathLam _ _ _ _ => nomatch headEq
  | pathApp _ _ => nomatch headEq
  | glueIntro _ _ _ _ => nomatch headEq
  | glueElim _ => nomatch headEq
  | transp _ _ _ _ _ _ _ _ => nomatch headEq
  | hcomp _ _ => nomatch headEq
  | recordIntro _ => nomatch headEq
  | recordProj _ => nomatch headEq
  | refineIntro _ _ _ => nomatch headEq
  | refineElim _ => nomatch headEq
  | codataUnfold _ _ => nomatch headEq
  | codataDest _ => nomatch headEq
  | sessionSend _ _ _ => nomatch headEq
  | sessionRecv _ => nomatch headEq
  | effectPerform _ _ _ => nomatch headEq
  | universeCode _ _ _ _ => nomatch headEq
  | cumulUp _ _ _ _ _ _ => nomatch headEq
  | equivReflId _ => nomatch headEq
  | funextRefl _ _ _ => nomatch headEq
  | equivReflIdAtId _ _ _ _ => nomatch headEq
  | funextReflAtId _ _ _ => nomatch headEq
  | equivIntroHet _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If `someTerm.headCtor = .optionSome`, the raw is `optionSome`-shaped. -/
theorem Term.headCtor_optionSome_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.optionSome) :
    ∃ (valueRaw : RawTerm scope), raw = RawTerm.optionSome valueRaw := by
  cases someTerm with
  | var _ => nomatch headEq
  | unit => nomatch headEq
  | lam _ => nomatch headEq
  | app _ _ => nomatch headEq
  | lamPi _ => nomatch headEq
  | appPi _ _ => nomatch headEq
  | pair _ _ => nomatch headEq
  | fst _ => nomatch headEq
  | snd _ => nomatch headEq
  | boolTrue => nomatch headEq
  | boolFalse => nomatch headEq
  | boolElim _ _ _ => nomatch headEq
  | natZero => nomatch headEq
  | natSucc _ => nomatch headEq
  | natElim _ _ _ => nomatch headEq
  | natRec _ _ _ => nomatch headEq
  | listNil => nomatch headEq
  | listCons _ _ => nomatch headEq
  | listElim _ _ _ => nomatch headEq
  | optionNone => nomatch headEq
  | optionSome _ => exact ⟨_, rfl⟩
  | optionMatch _ _ _ => nomatch headEq
  | eitherInl _ => nomatch headEq
  | eitherInr _ => nomatch headEq
  | eitherMatch _ _ _ => nomatch headEq
  | refl _ _ => nomatch headEq
  | idJ _ _ => nomatch headEq
  | idStrictRefl _ _ => nomatch headEq
  | idStrictRec _ _ => nomatch headEq
  | modIntro _ => nomatch headEq
  | modElim _ => nomatch headEq
  | subsume _ => nomatch headEq
  | interval0 => nomatch headEq
  | interval1 => nomatch headEq
  | intervalOpp _ => nomatch headEq
  | intervalMeet _ _ => nomatch headEq
  | intervalJoin _ _ => nomatch headEq
  | pathLam _ _ _ _ => nomatch headEq
  | pathApp _ _ => nomatch headEq
  | glueIntro _ _ _ _ => nomatch headEq
  | glueElim _ => nomatch headEq
  | transp _ _ _ _ _ _ _ _ => nomatch headEq
  | hcomp _ _ => nomatch headEq
  | recordIntro _ => nomatch headEq
  | recordProj _ => nomatch headEq
  | refineIntro _ _ _ => nomatch headEq
  | refineElim _ => nomatch headEq
  | codataUnfold _ _ => nomatch headEq
  | codataDest _ => nomatch headEq
  | sessionSend _ _ _ => nomatch headEq
  | sessionRecv _ => nomatch headEq
  | effectPerform _ _ _ => nomatch headEq
  | universeCode _ _ _ _ => nomatch headEq
  | cumulUp _ _ _ _ _ _ => nomatch headEq
  | equivReflId _ => nomatch headEq
  | funextRefl _ _ _ => nomatch headEq
  | equivReflIdAtId _ _ _ _ => nomatch headEq
  | funextReflAtId _ _ _ => nomatch headEq
  | equivIntroHet _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If `someTerm.headCtor = .eitherInl`, the raw is `eitherInl`-shaped. -/
theorem Term.headCtor_eitherInl_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.eitherInl) :
    ∃ (valueRaw : RawTerm scope), raw = RawTerm.eitherInl valueRaw := by
  cases someTerm with
  | var _ => nomatch headEq
  | unit => nomatch headEq
  | lam _ => nomatch headEq
  | app _ _ => nomatch headEq
  | lamPi _ => nomatch headEq
  | appPi _ _ => nomatch headEq
  | pair _ _ => nomatch headEq
  | fst _ => nomatch headEq
  | snd _ => nomatch headEq
  | boolTrue => nomatch headEq
  | boolFalse => nomatch headEq
  | boolElim _ _ _ => nomatch headEq
  | natZero => nomatch headEq
  | natSucc _ => nomatch headEq
  | natElim _ _ _ => nomatch headEq
  | natRec _ _ _ => nomatch headEq
  | listNil => nomatch headEq
  | listCons _ _ => nomatch headEq
  | listElim _ _ _ => nomatch headEq
  | optionNone => nomatch headEq
  | optionSome _ => nomatch headEq
  | optionMatch _ _ _ => nomatch headEq
  | eitherInl _ => exact ⟨_, rfl⟩
  | eitherInr _ => nomatch headEq
  | eitherMatch _ _ _ => nomatch headEq
  | refl _ _ => nomatch headEq
  | idJ _ _ => nomatch headEq
  | idStrictRefl _ _ => nomatch headEq
  | idStrictRec _ _ => nomatch headEq
  | modIntro _ => nomatch headEq
  | modElim _ => nomatch headEq
  | subsume _ => nomatch headEq
  | interval0 => nomatch headEq
  | interval1 => nomatch headEq
  | intervalOpp _ => nomatch headEq
  | intervalMeet _ _ => nomatch headEq
  | intervalJoin _ _ => nomatch headEq
  | pathLam _ _ _ _ => nomatch headEq
  | pathApp _ _ => nomatch headEq
  | glueIntro _ _ _ _ => nomatch headEq
  | glueElim _ => nomatch headEq
  | transp _ _ _ _ _ _ _ _ => nomatch headEq
  | hcomp _ _ => nomatch headEq
  | recordIntro _ => nomatch headEq
  | recordProj _ => nomatch headEq
  | refineIntro _ _ _ => nomatch headEq
  | refineElim _ => nomatch headEq
  | codataUnfold _ _ => nomatch headEq
  | codataDest _ => nomatch headEq
  | sessionSend _ _ _ => nomatch headEq
  | sessionRecv _ => nomatch headEq
  | effectPerform _ _ _ => nomatch headEq
  | universeCode _ _ _ _ => nomatch headEq
  | cumulUp _ _ _ _ _ _ => nomatch headEq
  | equivReflId _ => nomatch headEq
  | funextRefl _ _ _ => nomatch headEq
  | equivReflIdAtId _ _ _ _ => nomatch headEq
  | funextReflAtId _ _ _ => nomatch headEq
  | equivIntroHet _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If `someTerm.headCtor = .eitherInr`, the raw is `eitherInr`-shaped. -/
theorem Term.headCtor_eitherInr_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.eitherInr) :
    ∃ (valueRaw : RawTerm scope), raw = RawTerm.eitherInr valueRaw := by
  cases someTerm with
  | var _ => nomatch headEq
  | unit => nomatch headEq
  | lam _ => nomatch headEq
  | app _ _ => nomatch headEq
  | lamPi _ => nomatch headEq
  | appPi _ _ => nomatch headEq
  | pair _ _ => nomatch headEq
  | fst _ => nomatch headEq
  | snd _ => nomatch headEq
  | boolTrue => nomatch headEq
  | boolFalse => nomatch headEq
  | boolElim _ _ _ => nomatch headEq
  | natZero => nomatch headEq
  | natSucc _ => nomatch headEq
  | natElim _ _ _ => nomatch headEq
  | natRec _ _ _ => nomatch headEq
  | listNil => nomatch headEq
  | listCons _ _ => nomatch headEq
  | listElim _ _ _ => nomatch headEq
  | optionNone => nomatch headEq
  | optionSome _ => nomatch headEq
  | optionMatch _ _ _ => nomatch headEq
  | eitherInl _ => nomatch headEq
  | eitherInr _ => exact ⟨_, rfl⟩
  | eitherMatch _ _ _ => nomatch headEq
  | refl _ _ => nomatch headEq
  | idJ _ _ => nomatch headEq
  | idStrictRefl _ _ => nomatch headEq
  | idStrictRec _ _ => nomatch headEq
  | modIntro _ => nomatch headEq
  | modElim _ => nomatch headEq
  | subsume _ => nomatch headEq
  | interval0 => nomatch headEq
  | interval1 => nomatch headEq
  | intervalOpp _ => nomatch headEq
  | intervalMeet _ _ => nomatch headEq
  | intervalJoin _ _ => nomatch headEq
  | pathLam _ _ _ _ => nomatch headEq
  | pathApp _ _ => nomatch headEq
  | glueIntro _ _ _ _ => nomatch headEq
  | glueElim _ => nomatch headEq
  | transp _ _ _ _ _ _ _ _ => nomatch headEq
  | hcomp _ _ => nomatch headEq
  | recordIntro _ => nomatch headEq
  | recordProj _ => nomatch headEq
  | refineIntro _ _ _ => nomatch headEq
  | refineElim _ => nomatch headEq
  | codataUnfold _ _ => nomatch headEq
  | codataDest _ => nomatch headEq
  | sessionSend _ _ _ => nomatch headEq
  | sessionRecv _ => nomatch headEq
  | effectPerform _ _ _ => nomatch headEq
  | universeCode _ _ _ _ => nomatch headEq
  | cumulUp _ _ _ _ _ _ => nomatch headEq
  | equivReflId _ => nomatch headEq
  | funextRefl _ _ _ => nomatch headEq
  | equivReflIdAtId _ _ _ _ => nomatch headEq
  | funextReflAtId _ _ _ => nomatch headEq
  | equivIntroHet _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If a term's `headCtor` is `unit`, its raw is `RawTerm.unit`. -/
theorem Term.headCtor_unit_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.unit) :
    raw = RawTerm.unit := by
  cases someTerm with
  | var _ => nomatch headEq
  | unit => rfl
  | lam _ => nomatch headEq
  | app _ _ => nomatch headEq
  | lamPi _ => nomatch headEq
  | appPi _ _ => nomatch headEq
  | pair _ _ => nomatch headEq
  | fst _ => nomatch headEq
  | snd _ => nomatch headEq
  | boolTrue => nomatch headEq
  | boolFalse => nomatch headEq
  | boolElim _ _ _ => nomatch headEq
  | natZero => nomatch headEq
  | natSucc _ => nomatch headEq
  | natElim _ _ _ => nomatch headEq
  | natRec _ _ _ => nomatch headEq
  | listNil => nomatch headEq
  | listCons _ _ => nomatch headEq
  | listElim _ _ _ => nomatch headEq
  | optionNone => nomatch headEq
  | optionSome _ => nomatch headEq
  | optionMatch _ _ _ => nomatch headEq
  | eitherInl _ => nomatch headEq
  | eitherInr _ => nomatch headEq
  | eitherMatch _ _ _ => nomatch headEq
  | refl _ _ => nomatch headEq
  | idJ _ _ => nomatch headEq
  | idStrictRefl _ _ => nomatch headEq
  | idStrictRec _ _ => nomatch headEq
  | modIntro _ => nomatch headEq
  | modElim _ => nomatch headEq
  | subsume _ => nomatch headEq
  | interval0 => nomatch headEq
  | interval1 => nomatch headEq
  | intervalOpp _ => nomatch headEq
  | intervalMeet _ _ => nomatch headEq
  | intervalJoin _ _ => nomatch headEq
  | pathLam _ _ _ _ => nomatch headEq
  | pathApp _ _ => nomatch headEq
  | glueIntro _ _ _ _ => nomatch headEq
  | glueElim _ => nomatch headEq
  | transp _ _ _ _ _ _ _ _ => nomatch headEq
  | hcomp _ _ => nomatch headEq
  | recordIntro _ => nomatch headEq
  | recordProj _ => nomatch headEq
  | refineIntro _ _ _ => nomatch headEq
  | refineElim _ => nomatch headEq
  | codataUnfold _ _ => nomatch headEq
  | codataDest _ => nomatch headEq
  | sessionSend _ _ _ => nomatch headEq
  | sessionRecv _ => nomatch headEq
  | effectPerform _ _ _ => nomatch headEq
  | universeCode _ _ _ _ => nomatch headEq
  | cumulUp _ _ _ _ _ _ => nomatch headEq
  | equivReflId _ => nomatch headEq
  | funextRefl _ _ _ => nomatch headEq
  | equivReflIdAtId _ _ _ _ => nomatch headEq
  | funextReflAtId _ _ _ => nomatch headEq
  | equivIntroHet _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

end LeanFX2
