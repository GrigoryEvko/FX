import LeanFX2.Algo.WHNF.Evaluator
import LeanFX2.Algo.RawWHNF.HeadCtor

/-! # LeanFX2.Algo.WHNF.HeadCtorBridge - raw-routed head-ctor classification

`Term.headCtor` (Evaluator.lean) projects a typed `Term` to a flat
`Term.HeadCtor` tag.  Inverting it - "if `headCtor = X` then the raw
projection has shape `RawTerm.Y ...`" - is what every `headCtor_X_raw`
canonical-form lemma needs.  The naive proof does `cases someTerm`
over the 78-ctor INDEXED `Term` family, paying `Term.rec` (whose
motive and minor premises carry the full `Ty`/`Ctx` dependency) once
per lemma.  That kernel recheck is the dominant cost.

This file pays the `Term.rec` exactly ONCE, in `Term.headCtor_toRawTag`,
then lets the per-lemma inversions route through `cases raw` over the
plain `RawTerm` family (`RawTerm.rec` has no `Ty`/`Ctx` motive).

## Why a coarsening is required (not a 1:1 bridge)

`Term.headCtor` is NOT a function of the raw index alone.  Several
DISTINCT `Term` ctors share one raw outer ctor but project to
DIFFERENT head tags:

* `RawTerm.lam` <- `Term.lam` (-> `.lam`), `Term.lamPi` (-> `.lamPi`),
  `Term.funextRefl` / `funextReflAtId` / `funextIntroHet`
  (raw `RawTerm.lam (RawTerm.refl _)`).
* `RawTerm.app` <- `Term.app` (-> `.app`), `Term.appPi` (-> `.appPi`).
* `RawTerm.hcomp` <- `Term.hcomp` and `Term.hcompPath` (both -> `.hcomp`).
* `RawTerm.equivIntro` <- `Term.equivReflId`, `equivReflIdAtId`,
  `equivIntroHet`, `uaIntroHet` (the last has raw pinned to
  `RawTerm.equivIntro` by its TYPE index, not a free raw).

So a uniform equation `someTerm.headCtor = raw.headCtor`
is FALSE (it fails on `lamPi` / `appPi` / the equivIntro family).
The fix is to coarsen BOTH sides to the representative tag of the raw
OUTER ctor: `Term.HeadCtor.toRawTag` returns the corresponding
`RawTerm.HeadCtor`: it collapses `.lamPi -> .lam`, `.appPi -> .app`,
the equivIntro family -> `.equivIntro`, and the funext family -> `.lam`.
The coarsened equation

  `someTerm.headCtor.toRawTag = someTerm.toRaw.headCtor`

IS uniformly true and proved by the single `Term.rec`.

## How the inversions consume the bridge

For an introduction inversion (`headCtor_lam_raw`, target raw
`RawTerm.lam`), the head tag `.lam` maps to raw tag `.lam`, so
`headEq : headCtor = .lam` plus the bridge gives `raw.headCtor = .lam`.
Then `cases raw`
discharges every non-`lam` raw arm by `HeadCtor.noConfusion` and the
`lam` arm builds the witness.  All ten introduction heads inverted in
`Algo/Progress/CanonicalIntroductions.lean` are fixed points of
`toRawTag` (or, for `lamPi`, map to the same raw shape as `lam`), so
this routing is sound for each.

## Root status

Layer 3 typed-algorithm WHNF helper.  Zero-axiom under
`LeanFX2Audit`. -/

namespace LeanFX2

/-- Coarsen a `Term.HeadCtor` to the representative tag of its raw
OUTER ctor.  Identity on every head whose raw outer ctor is unshared;
collapses the colliding heads onto their representative:
`.lamPi -> .lam`, `.appPi -> .app`, the funext family -> `.lam`, the
equivIntro family -> `.equivIntro`.  Full enumeration of all 78
tags - no wildcard - so the function reduces by `rfl` and is
`propext`-free. -/
def Term.HeadCtor.toRawTag (tag : Term.HeadCtor) : RawTerm.HeadCtor :=
  match tag with
  | .var => .var
  | .unit => .unit
  | .lam => .lam
  | .app => .app
  | .lamPi => .lam
  | .appPi => .app
  | .pair => .pair
  | .fst => .fst
  | .snd => .snd
  | .boolTrue => .boolTrue
  | .boolFalse => .boolFalse
  | .boolElim => .boolElim
  | .natZero => .natZero
  | .natSucc => .natSucc
  | .natElim => .natElim
  | .natRec => .natRec
  | .listNil => .listNil
  | .listCons => .listCons
  | .listElim => .listElim
  | .optionNone => .optionNone
  | .optionSome => .optionSome
  | .optionMatch => .optionMatch
  | .eitherInl => .eitherInl
  | .eitherInr => .eitherInr
  | .eitherMatch => .eitherMatch
  | .refl => .refl
  | .idJ => .idJ
  | .oeqRefl => .oeqRefl
  | .oeqJ => .oeqJ
  | .oeqFunext => .oeqFunext
  | .idStrictRefl => .idStrictRefl
  | .idStrictRec => .idStrictRec
  | .modIntro => .modIntro
  | .modElim => .modElim
  | .subsume => .subsume
  | .interval0 => .interval0
  | .interval1 => .interval1
  | .intervalOpp => .intervalOpp
  | .intervalMeet => .intervalMeet
  | .intervalJoin => .intervalJoin
  | .pathLam => .pathLam
  | .pathApp => .pathApp
  | .glueIntro => .glueIntro
  | .glueElim => .glueElim
  | .transp => .transp
  | .hcomp => .hcomp
  | .recordIntro => .recordIntro
  | .recordProj => .recordProj
  | .refineIntro => .refineIntro
  | .refineElim => .refineElim
  | .codataUnfold => .codataUnfold
  | .codataDest => .codataDest
  | .sessionSend => .sessionSend
  | .sessionRecv => .sessionRecv
  | .effectPerform => .effectPerform
  | .universeCode => .universeCode
  | .cumulUp => .cumulUpMarker
  | .equivReflId => .equivIntro
  | .funextRefl => .lam
  | .equivReflIdAtId => .equivIntro
  | .funextReflAtId => .lam
  | .equivIntroHet => .equivIntro
  | .equivApp => .equivApp
  | .uaIntroHet => .equivIntro
  | .funextIntroHet => .lam
  | .uaToEquiv => .uaToEquiv
  | .equivApply => .equivApply
  | .arrowCode => .arrowCode
  | .piTyCode => .piTyCode
  | .sigmaTyCode => .sigmaTyCode
  | .productCode => .productCode
  | .sumCode => .sumCode
  | .listCode => .listCode
  | .optionCode => .optionCode
  | .eitherCode => .eitherCode
  | .idCode => .idCode
  | .equivCode => .equivCode

/-- The single `Term.rec`.  The coarsened head tag of any typed `Term`
equals the representative tag of its raw projection.  Every arm
reduces by `rfl`: the left side computes `someTerm.headCtor` (matching
the Term ctor) then `toRawTag`; the right side computes
`RawTerm.headCtor` on the Term ctor's raw index - both land on the
same representative tag.  This is the ONLY 78-arm structural recursion
over the indexed `Term` family in the head-ctor inversion stack. -/
theorem Term.headCtor_toRawTag {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {someType : Ty level scope}
    {raw : RawTerm scope} (someTerm : Term context someType raw) :
    someTerm.headCtor.toRawTag = raw.headCtor := by
  cases someTerm <;> rfl

end LeanFX2
