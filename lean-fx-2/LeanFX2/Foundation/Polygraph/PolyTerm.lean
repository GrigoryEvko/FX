import LeanFX2.Foundation.Polygraph.RawPolyTerm
import LeanFX2.Foundation.Mode
import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.Subst
import LeanFX2.Foundation.SubstActsOnTy
import LeanFX2.Foundation.Context
import LeanFX2.Foundation.Effect
import LeanFX2.Foundation.TermHelpers

/-! # `PolyTerm` — typed mirror of `Term` indexed by `RawPolyTerm`.

K11.9 ships the typed polygraph-encoding column of the four-encoding
lattice (K14.13 "Tree <-> PolyTerm <-> ValueTerm <-> EGraph").  Where
`Term ctx ty rawTerm` carries the raw `RawTerm` payload, `PolyTerm
ctx ty rawPoly` carries the polygraph-cell `RawPolyTerm` payload.

## Intrinsic indexing

`PolyTerm : ∀ {mode level scope}, Ctx mode level scope -> Ty level
scope -> RawPolyTerm scope -> Type`.  Every constructor pins:

* The typing context `ctx : Ctx mode level scope`
* The kernel type `Ty level scope` (well-formed at the same level
  and scope)
* The polygraph raw payload `RawPolyTerm scope`

The Ctx and Ty machinery is shared with `Term`; only the raw payload
is swapped.

## The `toRawTerm` bridge

`Ty.subst0` and similar kernel substitution operators take `RawTerm`
at type level (because `Ty` itself is indexed by `RawTerm` for
dependent types).  When a `PolyTerm` constructor's signature would
need to mention "the RawTerm corresponding to this RawPolyTerm" at
type level, it calls `RawPolyTerm.toRawTerm` — a structural recursion
shipping with this file.  Marked `@[reducible]` so the elaborator can
chain definitional equalities through it.

The full bidirectional bijection (`RawTerm <-> RawPolyTerm` and
`Term <-> PolyTerm`) lives in K11.10 / K11.11 / K11.12; this file
ships ONLY the forward `toRawTerm` direction at the raw layer plus
the typed inductive.

## Phase A + Phase B scope

Phase A (commit 9af612d) shipped the structural raw converter
`RawPolyTerm.toRawTerm` plus the typed inductive's core MLTT
fragment (var/unit/lam/app/lamPi/appPi/pair/fst/snd/booleans/
naturals/lists/options/eithers/refl/idJ — 27 ctors).

Phase B (this commit) extends `PolyTerm` to ALL 77 typed Term
constructors, covering every frontier type theory layer in one
typed inductive: observational equality (oeqRefl/J/Funext),
strict identity (idStrictRefl/Rec), modal (modIntro/Elim/
subsume), cubical (interval0/1/Opp/Meet/Join, pathLam/App,
glueIntro/Elim, transp, hcomp), records, refinements, codata,
sessions, effects, universe codes + 10 type-shape codes,
cumulativity (cumulUp), and the full univalence vocabulary
(equivReflId, funextRefl, equivReflIdAtId, funextReflAtId,
equivIntroHet, equivApp, uaIntroHet, funextIntroHet, uaToEquiv,
equivApply).

## Proof-obligation handling

Two Term ctors (`equivIntroHet`, `oeqFunext`) carry proof-witness
subterms whose typed signatures use Layer-1 helpers
(`equivIntroHetLeftInverseType`, `equivIntroHetRightInverseType`,
`oeqFunextPointwiseType`) defined in `Term.lean`.  Because
`Foundation/Polygraph/PolyTerm.lean` is Layer 0, it cannot import
Layer 1 helpers.  The PolyTerm versions of these ctors take their
proof-witness subterms with OPAQUE motive types (kept as implicit
`Ty`-typed fields); the precise pinning to the Layer-1 helper
types happens at K11.10 (Term → PolyTerm forward bijection), at
which point the helpers are visible.

This is architecturally clean: PolyTerm at dim-0 is the
*computational arity* of each ctor (how many typed subterms;
their carriers); the *coherence-obligation type pinning* is a
property of the Term-PolyTerm bijection, not of PolyTerm itself.

## Audit

Every declaration ships zero-axiom.  Verified via
`Smoke/AuditPolyTerm.lean`. -/

namespace LeanFX2.Foundation.Polygraph

/-- Structural raw-level converter from `RawPolyTerm` to `RawTerm`.
Every constructor maps one-to-one to its `RawTerm` counterpart.
Marked `@[reducible]` so the elaborator can chain definitional
equalities through call sites in `PolyTerm` constructor types. -/
@[reducible] def RawPolyTerm.toRawTerm :
    ∀ {scope : Nat}, RawPolyTerm scope → LeanFX2.RawTerm scope
  | _, .var position => .var position
  | _, .unit => .unit
  | _, .lam body => .lam body.toRawTerm
  | _, .app functionTerm argumentTerm =>
      .app functionTerm.toRawTerm argumentTerm.toRawTerm
  | _, .pair firstValue secondValue =>
      .pair firstValue.toRawTerm secondValue.toRawTerm
  | _, .fst pairTerm => .fst pairTerm.toRawTerm
  | _, .snd pairTerm => .snd pairTerm.toRawTerm
  | _, .boolTrue => .boolTrue
  | _, .boolFalse => .boolFalse
  | _, .boolElim scrutinee thenBranch elseBranch =>
      .boolElim scrutinee.toRawTerm thenBranch.toRawTerm
        elseBranch.toRawTerm
  | _, .natZero => .natZero
  | _, .natSucc predecessor => .natSucc predecessor.toRawTerm
  | _, .natElim scrutinee zeroBranch succBranch =>
      .natElim scrutinee.toRawTerm zeroBranch.toRawTerm
        succBranch.toRawTerm
  | _, .natRec scrutinee zeroBranch succBranch =>
      .natRec scrutinee.toRawTerm zeroBranch.toRawTerm
        succBranch.toRawTerm
  | _, .listNil => .listNil
  | _, .listCons headTerm tailTerm =>
      .listCons headTerm.toRawTerm tailTerm.toRawTerm
  | _, .listElim scrutinee nilBranch consBranch =>
      .listElim scrutinee.toRawTerm nilBranch.toRawTerm
        consBranch.toRawTerm
  | _, .optionNone => .optionNone
  | _, .optionSome valueTerm => .optionSome valueTerm.toRawTerm
  | _, .optionMatch scrutinee noneBranch someBranch =>
      .optionMatch scrutinee.toRawTerm noneBranch.toRawTerm
        someBranch.toRawTerm
  | _, .eitherInl valueTerm => .eitherInl valueTerm.toRawTerm
  | _, .eitherInr valueTerm => .eitherInr valueTerm.toRawTerm
  | _, .eitherMatch scrutinee leftBranch rightBranch =>
      .eitherMatch scrutinee.toRawTerm leftBranch.toRawTerm
        rightBranch.toRawTerm
  | _, .refl rawWitness => .refl rawWitness.toRawTerm
  | _, .idJ baseCase witness =>
      .idJ baseCase.toRawTerm witness.toRawTerm
  | _, .modIntro inner => .modIntro inner.toRawTerm
  | _, .modElim inner => .modElim inner.toRawTerm
  | _, .subsume inner => .subsume inner.toRawTerm
  | _, .interval0 => .interval0
  | _, .interval1 => .interval1
  | _, .intervalOpp intervalTerm =>
      .intervalOpp intervalTerm.toRawTerm
  | _, .intervalMeet leftInterval rightInterval =>
      .intervalMeet leftInterval.toRawTerm rightInterval.toRawTerm
  | _, .intervalJoin leftInterval rightInterval =>
      .intervalJoin leftInterval.toRawTerm rightInterval.toRawTerm
  | _, .pathLam body => .pathLam body.toRawTerm
  | _, .pathApp pathTerm intervalArg =>
      .pathApp pathTerm.toRawTerm intervalArg.toRawTerm
  | _, .glueIntro baseValue partialValue =>
      .glueIntro baseValue.toRawTerm partialValue.toRawTerm
  | _, .glueElim gluedValue => .glueElim gluedValue.toRawTerm
  | _, .transp path source =>
      .transp path.toRawTerm source.toRawTerm
  | _, .hcomp sides cap => .hcomp sides.toRawTerm cap.toRawTerm
  | _, .oeqRefl witness => .oeqRefl witness.toRawTerm
  | _, .oeqJ baseCase witness =>
      .oeqJ baseCase.toRawTerm witness.toRawTerm
  | _, .oeqFunext pointwiseEquality =>
      .oeqFunext pointwiseEquality.toRawTerm
  | _, .idStrictRefl witness => .idStrictRefl witness.toRawTerm
  | _, .idStrictRec baseCase witness =>
      .idStrictRec baseCase.toRawTerm witness.toRawTerm
  | _, .equivIntro forwardFn backwardFn =>
      .equivIntro forwardFn.toRawTerm backwardFn.toRawTerm
  | _, .equivApp equivTerm argument =>
      .equivApp equivTerm.toRawTerm argument.toRawTerm
  | _, .refineIntro rawValue predicateProof =>
      .refineIntro rawValue.toRawTerm predicateProof.toRawTerm
  | _, .refineElim refinedValue =>
      .refineElim refinedValue.toRawTerm
  | _, .recordIntro firstField =>
      .recordIntro firstField.toRawTerm
  | _, .recordProj recordValue =>
      .recordProj recordValue.toRawTerm
  | _, .codataUnfold initialState transition =>
      .codataUnfold initialState.toRawTerm transition.toRawTerm
  | _, .codataDest codataValue =>
      .codataDest codataValue.toRawTerm
  | _, .sessionSend channel payload =>
      .sessionSend channel.toRawTerm payload.toRawTerm
  | _, .sessionRecv channel =>
      .sessionRecv channel.toRawTerm
  | _, .effectPerform operationTag arguments =>
      .effectPerform operationTag.toRawTerm arguments.toRawTerm
  | _, .universeCode innerLevel => .universeCode innerLevel
  | _, .arrowCode domainCode codomainCode =>
      .arrowCode domainCode.toRawTerm codomainCode.toRawTerm
  | _, .piTyCode domainCode codomainCode =>
      .piTyCode domainCode.toRawTerm codomainCode.toRawTerm
  | _, .sigmaTyCode domainCode codomainCode =>
      .sigmaTyCode domainCode.toRawTerm codomainCode.toRawTerm
  | _, .productCode firstCode secondCode =>
      .productCode firstCode.toRawTerm secondCode.toRawTerm
  | _, .sumCode leftCode rightCode =>
      .sumCode leftCode.toRawTerm rightCode.toRawTerm
  | _, .listCode elementCode => .listCode elementCode.toRawTerm
  | _, .optionCode elementCode => .optionCode elementCode.toRawTerm
  | _, .eitherCode leftCode rightCode =>
      .eitherCode leftCode.toRawTerm rightCode.toRawTerm
  | _, .idCode typeCode leftRaw rightRaw =>
      .idCode typeCode.toRawTerm leftRaw.toRawTerm
        rightRaw.toRawTerm
  | _, .equivCode leftTypeCode rightTypeCode =>
      .equivCode leftTypeCode.toRawTerm rightTypeCode.toRawTerm
  | _, .cumulUpMarker innerCodeRaw =>
      .cumulUpMarker innerCodeRaw.toRawTerm
  | _, .uaToEquiv proofRaw => .uaToEquiv proofRaw.toRawTerm
  | _, .equivApply equivRaw argRaw =>
      .equivApply equivRaw.toRawTerm argRaw.toRawTerm
  | _, .pathCompose leftPathRaw rightPathRaw =>
      .pathCompose leftPathRaw.toRawTerm rightPathRaw.toRawTerm
  | _, .idToEquiv proofRaw => .idToEquiv proofRaw.toRawTerm
  | _, .oeqTrans firstProof secondProof =>
      .oeqTrans firstProof.toRawTerm secondProof.toRawTerm
  | _, .equivCompose firstEquiv secondEquiv =>
      .equivCompose firstEquiv.toRawTerm secondEquiv.toRawTerm

end LeanFX2.Foundation.Polygraph

namespace LeanFX2

/-- Structural raw-level converter from `RawTerm` to `RawPolyTerm` —
the forward direction of the K11.12 raw-level bijection.  Every
`RawTerm` constructor maps one-to-one to its `RawPolyTerm`
counterpart.  Marked `@[reducible]` so the elaborator can chain
definitional equalities through call sites in `Term.toPoly`
(K11.10-B). -/
@[reducible] def RawTerm.toRawPoly :
    ∀ {scope : Nat}, RawTerm scope →
      LeanFX2.Foundation.Polygraph.RawPolyTerm scope
  | _, .var position => .var position
  | _, .unit => .unit
  | _, .lam body => .lam body.toRawPoly
  | _, .app functionTerm argumentTerm =>
      .app functionTerm.toRawPoly argumentTerm.toRawPoly
  | _, .pair firstValue secondValue =>
      .pair firstValue.toRawPoly secondValue.toRawPoly
  | _, .fst pairTerm => .fst pairTerm.toRawPoly
  | _, .snd pairTerm => .snd pairTerm.toRawPoly
  | _, .boolTrue => .boolTrue
  | _, .boolFalse => .boolFalse
  | _, .boolElim scrutinee thenBranch elseBranch =>
      .boolElim scrutinee.toRawPoly thenBranch.toRawPoly
        elseBranch.toRawPoly
  | _, .natZero => .natZero
  | _, .natSucc predecessor => .natSucc predecessor.toRawPoly
  | _, .natElim scrutinee zeroBranch succBranch =>
      .natElim scrutinee.toRawPoly zeroBranch.toRawPoly
        succBranch.toRawPoly
  | _, .natRec scrutinee zeroBranch succBranch =>
      .natRec scrutinee.toRawPoly zeroBranch.toRawPoly
        succBranch.toRawPoly
  | _, .listNil => .listNil
  | _, .listCons headTerm tailTerm =>
      .listCons headTerm.toRawPoly tailTerm.toRawPoly
  | _, .listElim scrutinee nilBranch consBranch =>
      .listElim scrutinee.toRawPoly nilBranch.toRawPoly
        consBranch.toRawPoly
  | _, .optionNone => .optionNone
  | _, .optionSome valueTerm => .optionSome valueTerm.toRawPoly
  | _, .optionMatch scrutinee noneBranch someBranch =>
      .optionMatch scrutinee.toRawPoly noneBranch.toRawPoly
        someBranch.toRawPoly
  | _, .eitherInl valueTerm => .eitherInl valueTerm.toRawPoly
  | _, .eitherInr valueTerm => .eitherInr valueTerm.toRawPoly
  | _, .eitherMatch scrutinee leftBranch rightBranch =>
      .eitherMatch scrutinee.toRawPoly leftBranch.toRawPoly
        rightBranch.toRawPoly
  | _, .refl rawWitness => .refl rawWitness.toRawPoly
  | _, .idJ baseCase witness =>
      .idJ baseCase.toRawPoly witness.toRawPoly
  | _, .modIntro inner => .modIntro inner.toRawPoly
  | _, .modElim inner => .modElim inner.toRawPoly
  | _, .subsume inner => .subsume inner.toRawPoly
  | _, .interval0 => .interval0
  | _, .interval1 => .interval1
  | _, .intervalOpp intervalTerm =>
      .intervalOpp intervalTerm.toRawPoly
  | _, .intervalMeet leftInterval rightInterval =>
      .intervalMeet leftInterval.toRawPoly rightInterval.toRawPoly
  | _, .intervalJoin leftInterval rightInterval =>
      .intervalJoin leftInterval.toRawPoly rightInterval.toRawPoly
  | _, .pathLam body => .pathLam body.toRawPoly
  | _, .pathApp pathTerm intervalArg =>
      .pathApp pathTerm.toRawPoly intervalArg.toRawPoly
  | _, .glueIntro baseValue partialValue =>
      .glueIntro baseValue.toRawPoly partialValue.toRawPoly
  | _, .glueElim gluedValue => .glueElim gluedValue.toRawPoly
  | _, .transp path source =>
      .transp path.toRawPoly source.toRawPoly
  | _, .hcomp sides cap => .hcomp sides.toRawPoly cap.toRawPoly
  | _, .oeqRefl witness => .oeqRefl witness.toRawPoly
  | _, .oeqJ baseCase witness =>
      .oeqJ baseCase.toRawPoly witness.toRawPoly
  | _, .oeqFunext pointwiseEquality =>
      .oeqFunext pointwiseEquality.toRawPoly
  | _, .idStrictRefl witness => .idStrictRefl witness.toRawPoly
  | _, .idStrictRec baseCase witness =>
      .idStrictRec baseCase.toRawPoly witness.toRawPoly
  | _, .equivIntro forwardFn backwardFn =>
      .equivIntro forwardFn.toRawPoly backwardFn.toRawPoly
  | _, .equivApp equivTerm argument =>
      .equivApp equivTerm.toRawPoly argument.toRawPoly
  | _, .refineIntro rawValue predicateProof =>
      .refineIntro rawValue.toRawPoly predicateProof.toRawPoly
  | _, .refineElim refinedValue =>
      .refineElim refinedValue.toRawPoly
  | _, .recordIntro firstField =>
      .recordIntro firstField.toRawPoly
  | _, .recordProj recordValue =>
      .recordProj recordValue.toRawPoly
  | _, .codataUnfold initialState transition =>
      .codataUnfold initialState.toRawPoly transition.toRawPoly
  | _, .codataDest codataValue =>
      .codataDest codataValue.toRawPoly
  | _, .sessionSend channel payload =>
      .sessionSend channel.toRawPoly payload.toRawPoly
  | _, .sessionRecv channel =>
      .sessionRecv channel.toRawPoly
  | _, .effectPerform operationTag arguments =>
      .effectPerform operationTag.toRawPoly arguments.toRawPoly
  | _, .universeCode innerLevel => .universeCode innerLevel
  | _, .arrowCode domainCode codomainCode =>
      .arrowCode domainCode.toRawPoly codomainCode.toRawPoly
  | _, .piTyCode domainCode codomainCode =>
      .piTyCode domainCode.toRawPoly codomainCode.toRawPoly
  | _, .sigmaTyCode domainCode codomainCode =>
      .sigmaTyCode domainCode.toRawPoly codomainCode.toRawPoly
  | _, .productCode firstCode secondCode =>
      .productCode firstCode.toRawPoly secondCode.toRawPoly
  | _, .sumCode leftCode rightCode =>
      .sumCode leftCode.toRawPoly rightCode.toRawPoly
  | _, .listCode elementCode => .listCode elementCode.toRawPoly
  | _, .optionCode elementCode => .optionCode elementCode.toRawPoly
  | _, .eitherCode leftCode rightCode =>
      .eitherCode leftCode.toRawPoly rightCode.toRawPoly
  | _, .idCode typeCode leftRaw rightRaw =>
      .idCode typeCode.toRawPoly leftRaw.toRawPoly
        rightRaw.toRawPoly
  | _, .equivCode leftTypeCode rightTypeCode =>
      .equivCode leftTypeCode.toRawPoly rightTypeCode.toRawPoly
  | _, .cumulUpMarker innerCodeRaw =>
      .cumulUpMarker innerCodeRaw.toRawPoly
  | _, .uaToEquiv proofRaw => .uaToEquiv proofRaw.toRawPoly
  | _, .equivApply equivRaw argRaw =>
      .equivApply equivRaw.toRawPoly argRaw.toRawPoly
  | _, .pathCompose leftPathRaw rightPathRaw =>
      .pathCompose leftPathRaw.toRawPoly rightPathRaw.toRawPoly
  | _, .idToEquiv proofRaw => .idToEquiv proofRaw.toRawPoly
  | _, .oeqTrans firstProof secondProof =>
      .oeqTrans firstProof.toRawPoly secondProof.toRawPoly
  | _, .equivCompose firstEquiv secondEquiv =>
      .equivCompose firstEquiv.toRawPoly secondEquiv.toRawPoly

end LeanFX2

namespace LeanFX2

/-- Typed polygraph-encoding mirror of `Term`.  Indexed by the same
typing context and kernel type as `Term`, but carries a
`RawPolyTerm` raw payload instead of a `RawTerm`.

## Phase A — core MLTT fragment

This commit ships 27 constructors covering the MLTT base: variables,
unit, non-dependent and dependent function intro/elim, dependent
pair intro/elim, booleans + eliminator, naturals + two eliminators,
lists + eliminator, options + match, eithers + match, identity-type
refl + J.

## Remaining ctors (Phase B, K11.9.B)

* Modal (modIntro, modElim, subsume) — 3 ctors
* Cubical interval + path + glue + transp/hcomp — 10 ctors
* Observational equality (oeqRefl, oeqJ, oeqFunext) — 3 ctors
* Strict identity (idStrictRefl, idStrictRec) — 2 ctors
* Equivalence (equivIntro, equivApp) — 2 ctors
* Refinement (refineIntro, refineElim) — 2 ctors
* Records (recordIntro, recordProj) — 2 ctors
* Codata (codataUnfold, codataDest) — 2 ctors
* Session (sessionSend, sessionRecv) — 2 ctors
* Effect (effectPerform) — 1 ctor
* Universe-code + type-shape codes (10 ctors)
* CumulUp marker + 6 univalence-beta vocabulary ctors

Total Phase B: ~46 ctors lifting PolyTerm to full Term parity. -/
inductive PolyTerm : ∀ {mode : Mode} {level scope : Nat},
    Ctx mode level scope → Ty level scope →
    LeanFX2.Foundation.Polygraph.RawPolyTerm scope → Type
  -- Variable lookup
  | var {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (position : Fin scope) :
      PolyTerm context (varType context position)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.var position)
  -- Unit
  | unit {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope} :
      PolyTerm context Ty.unit
        LeanFX2.Foundation.Polygraph.RawPolyTerm.unit
  -- Non-dependent function intro / elim
  | lam {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {domainType codomainType : Ty level scope}
      {bodyPolyRaw : LeanFX2.Foundation.Polygraph.RawPolyTerm (scope + 1)}
      (body :
        PolyTerm (Ctx.cons context domainType)
          codomainType.weaken bodyPolyRaw) :
      PolyTerm context (Ty.arrow domainType codomainType)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.lam bodyPolyRaw)
  | app {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {domainType codomainType : Ty level scope}
      {functionPolyRaw argumentPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (functionTerm :
        PolyTerm context (Ty.arrow domainType codomainType)
          functionPolyRaw)
      (argumentTerm : PolyTerm context domainType argumentPolyRaw) :
      PolyTerm context codomainType
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.app functionPolyRaw
          argumentPolyRaw)
  -- Dependent Π intro / elim
  | lamPi {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {domainType : Ty level scope}
      {codomainType : Ty level (scope + 1)}
      {bodyPolyRaw : LeanFX2.Foundation.Polygraph.RawPolyTerm (scope + 1)}
      (body :
        PolyTerm (Ctx.cons context domainType) codomainType
          bodyPolyRaw) :
      PolyTerm context (Ty.piTy domainType codomainType)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.lam bodyPolyRaw)
  | appPi {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {domainType : Ty level scope}
      {codomainType : Ty level (scope + 1)}
      {functionPolyRaw argumentPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (functionTerm :
        PolyTerm context (Ty.piTy domainType codomainType)
          functionPolyRaw)
      (argumentTerm :
        PolyTerm context domainType argumentPolyRaw) :
      PolyTerm context
        (codomainType.subst0 domainType argumentPolyRaw.toRawTerm)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.app functionPolyRaw
          argumentPolyRaw)
  -- Σ intro / elim
  | pair {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {firstType : Ty level scope}
      {secondType : Ty level (scope + 1)}
      {firstPolyRaw secondPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (firstValue :
        PolyTerm context firstType firstPolyRaw)
      (secondValue :
        PolyTerm context
          (secondType.subst0 firstType firstPolyRaw.toRawTerm)
          secondPolyRaw) :
      PolyTerm context (Ty.sigmaTy firstType secondType)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.pair firstPolyRaw
          secondPolyRaw)
  | fst {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {firstType : Ty level scope}
      {secondType : Ty level (scope + 1)}
      {pairPolyRaw : LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (pairTerm :
        PolyTerm context (Ty.sigmaTy firstType secondType)
          pairPolyRaw) :
      PolyTerm context firstType
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.fst pairPolyRaw)
  | snd {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {firstType : Ty level scope}
      {secondType : Ty level (scope + 1)}
      {pairPolyRaw : LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (pairTerm :
        PolyTerm context (Ty.sigmaTy firstType secondType)
          pairPolyRaw) :
      PolyTerm context
        (secondType.subst0 firstType
          (LeanFX2.Foundation.Polygraph.RawPolyTerm.fst
            pairPolyRaw).toRawTerm)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.snd pairPolyRaw)
  -- Booleans
  | boolTrue {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope} :
      PolyTerm context Ty.bool
        LeanFX2.Foundation.Polygraph.RawPolyTerm.boolTrue
  | boolFalse {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope} :
      PolyTerm context Ty.bool
        LeanFX2.Foundation.Polygraph.RawPolyTerm.boolFalse
  | boolElim {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {motiveType : Ty level (scope + 1)}
      {scrutineePolyRaw thenPolyRaw elsePolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (scrutinee :
        PolyTerm context Ty.bool scrutineePolyRaw)
      (thenBranch :
        PolyTerm context
          (motiveType.subst0 Ty.bool LeanFX2.RawTerm.boolTrue)
          thenPolyRaw)
      (elseBranch :
        PolyTerm context
          (motiveType.subst0 Ty.bool LeanFX2.RawTerm.boolFalse)
          elsePolyRaw) :
      PolyTerm context
        (motiveType.subst0 Ty.bool scrutineePolyRaw.toRawTerm)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.boolElim
          scrutineePolyRaw thenPolyRaw elsePolyRaw)
  -- Naturals
  | natZero {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope} :
      PolyTerm context Ty.nat
        LeanFX2.Foundation.Polygraph.RawPolyTerm.natZero
  | natSucc {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {predecessorPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (predecessor : PolyTerm context Ty.nat predecessorPolyRaw) :
      PolyTerm context Ty.nat
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.natSucc
          predecessorPolyRaw)
  | natElim {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineePolyRaw zeroPolyRaw succPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (scrutinee : PolyTerm context Ty.nat scrutineePolyRaw)
      (zeroBranch : PolyTerm context motiveType zeroPolyRaw)
      (succBranch :
        PolyTerm context (Ty.arrow Ty.nat motiveType) succPolyRaw) :
      PolyTerm context motiveType
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.natElim
          scrutineePolyRaw zeroPolyRaw succPolyRaw)
  | natRec {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineePolyRaw zeroPolyRaw succPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (scrutinee : PolyTerm context Ty.nat scrutineePolyRaw)
      (zeroBranch : PolyTerm context motiveType zeroPolyRaw)
      (succBranch :
        PolyTerm context
          (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
          succPolyRaw) :
      PolyTerm context motiveType
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.natRec
          scrutineePolyRaw zeroPolyRaw succPolyRaw)
  -- Lists
  | listNil {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {elementType : Ty level scope} :
      PolyTerm context (Ty.listType elementType)
        LeanFX2.Foundation.Polygraph.RawPolyTerm.listNil
  | listCons {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {elementType : Ty level scope}
      {headPolyRaw tailPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (headTerm : PolyTerm context elementType headPolyRaw)
      (tailTerm :
        PolyTerm context (Ty.listType elementType) tailPolyRaw) :
      PolyTerm context (Ty.listType elementType)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.listCons
          headPolyRaw tailPolyRaw)
  | listElim {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {scrutineePolyRaw nilPolyRaw consPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (scrutinee :
        PolyTerm context (Ty.listType elementType) scrutineePolyRaw)
      (nilBranch : PolyTerm context motiveType nilPolyRaw)
      (consBranch :
        PolyTerm context
          (Ty.arrow elementType
            (Ty.arrow (Ty.listType elementType) motiveType))
          consPolyRaw) :
      PolyTerm context motiveType
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.listElim
          scrutineePolyRaw nilPolyRaw consPolyRaw)
  -- Options
  | optionNone {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {elementType : Ty level scope} :
      PolyTerm context (Ty.optionType elementType)
        LeanFX2.Foundation.Polygraph.RawPolyTerm.optionNone
  | optionSome {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {elementType : Ty level scope}
      {valuePolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (valueTerm : PolyTerm context elementType valuePolyRaw) :
      PolyTerm context (Ty.optionType elementType)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.optionSome
          valuePolyRaw)
  | optionMatch {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {scrutineePolyRaw nonePolyRaw somePolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (scrutinee :
        PolyTerm context (Ty.optionType elementType)
          scrutineePolyRaw)
      (noneBranch : PolyTerm context motiveType nonePolyRaw)
      (someBranch :
        PolyTerm context (Ty.arrow elementType motiveType)
          somePolyRaw) :
      PolyTerm context motiveType
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.optionMatch
          scrutineePolyRaw nonePolyRaw somePolyRaw)
  -- Eithers
  | eitherInl {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftType rightType : Ty level scope}
      {valuePolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (valueTerm : PolyTerm context leftType valuePolyRaw) :
      PolyTerm context (Ty.eitherType leftType rightType)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.eitherInl
          valuePolyRaw)
  | eitherInr {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftType rightType : Ty level scope}
      {valuePolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (valueTerm : PolyTerm context rightType valuePolyRaw) :
      PolyTerm context (Ty.eitherType leftType rightType)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.eitherInr
          valuePolyRaw)
  | eitherMatch {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftType rightType motiveType : Ty level scope}
      {scrutineePolyRaw leftPolyRaw rightPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (scrutinee :
        PolyTerm context (Ty.eitherType leftType rightType)
          scrutineePolyRaw)
      (leftBranch :
        PolyTerm context (Ty.arrow leftType motiveType) leftPolyRaw)
      (rightBranch :
        PolyTerm context (Ty.arrow rightType motiveType)
          rightPolyRaw) :
      PolyTerm context motiveType
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.eitherMatch
          scrutineePolyRaw leftPolyRaw rightPolyRaw)
  -- Identity types (HoTT)
  | refl {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (carrier : Ty level scope)
      (rawPolyWitness :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope) :
      PolyTerm context
        (Ty.id carrier rawPolyWitness.toRawTerm
          rawPolyWitness.toRawTerm)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.refl
          rawPolyWitness)
  | idJ {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {carrier : Ty level scope}
      {leftEndpoint rightEndpoint : LeanFX2.RawTerm scope}
      {motiveType : Ty level scope}
      {basePolyRaw witnessPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (baseCase : PolyTerm context motiveType basePolyRaw)
      (witness :
        PolyTerm context
          (Ty.id carrier leftEndpoint rightEndpoint)
          witnessPolyRaw) :
      PolyTerm context motiveType
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.idJ basePolyRaw
          witnessPolyRaw)
  -- Observational equality
  | oeqRefl {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (carrier : Ty level scope)
      (rawPolyWitness :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope) :
      PolyTerm context
        (Ty.oeq carrier rawPolyWitness.toRawTerm
          rawPolyWitness.toRawTerm)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.oeqRefl
          rawPolyWitness)
  | oeqJ {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {carrier : Ty level scope}
      {leftEndpoint rightEndpoint : LeanFX2.RawTerm scope}
      {motiveType : Ty level scope}
      {basePolyRaw witnessPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (baseCase : PolyTerm context motiveType basePolyRaw)
      (witness :
        PolyTerm context
          (Ty.oeq carrier leftEndpoint rightEndpoint)
          witnessPolyRaw) :
      PolyTerm context motiveType
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.oeqJ
          basePolyRaw witnessPolyRaw)
  /-- Funext at observational equality.  Pointwise proof carries
  the same motive type as `Term.oeqFunext`
  (`oeqFunextPointwiseType domainType codomainType leftFunctionRaw
  rightFunctionRaw`), migrated to Foundation/TermHelpers for shared
  Layer-0 access.  Strict-lossless bijection. -/
  | oeqFunext {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (domainType codomainType : Ty level scope)
      (leftFunctionRaw rightFunctionRaw : LeanFX2.RawTerm scope)
      {pointwisePolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (pointwiseProof :
        PolyTerm context
          (oeqFunextPointwiseType domainType codomainType
            leftFunctionRaw rightFunctionRaw)
          pointwisePolyRaw) :
      PolyTerm context
        (Ty.oeq (Ty.arrow domainType codomainType)
          leftFunctionRaw rightFunctionRaw)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.oeqFunext
          pointwisePolyRaw)
  -- Strict identity (strict-mode J recursor)
  | idStrictRefl {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (modeIsStrict : mode = Mode.strict)
      (carrier : Ty level scope)
      (rawPolyWitness :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope) :
      PolyTerm context
        (Ty.idStrict carrier rawPolyWitness.toRawTerm
          rawPolyWitness.toRawTerm)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.idStrictRefl
          rawPolyWitness)
  | idStrictRec {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (modeIsStrict : mode = Mode.strict)
      {carrier : Ty level scope}
      {leftEndpoint rightEndpoint : LeanFX2.RawTerm scope}
      {motiveType : Ty level scope}
      {basePolyRaw witnessPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (baseCase : PolyTerm context motiveType basePolyRaw)
      (witness :
        PolyTerm context
          (Ty.idStrict carrier leftEndpoint rightEndpoint)
          witnessPolyRaw) :
      PolyTerm context motiveType
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.idStrictRec
          basePolyRaw witnessPolyRaw)
  -- Modal scaffolding (Layer 6 will refine Ty.modal interaction)
  | modIntro {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {innerType : Ty level scope}
      {innerPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (innerTerm : PolyTerm context innerType innerPolyRaw) :
      PolyTerm context innerType
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.modIntro
          innerPolyRaw)
  | modElim {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {innerType : Ty level scope}
      {innerPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (innerTerm : PolyTerm context innerType innerPolyRaw) :
      PolyTerm context innerType
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.modElim
          innerPolyRaw)
  | subsume {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {innerType : Ty level scope}
      {innerPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (innerTerm : PolyTerm context innerType innerPolyRaw) :
      PolyTerm context innerType
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.subsume
          innerPolyRaw)
  -- Cubical interval algebra
  | interval0 {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope} :
      PolyTerm context Ty.interval
        LeanFX2.Foundation.Polygraph.RawPolyTerm.interval0
  | interval1 {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope} :
      PolyTerm context Ty.interval
        LeanFX2.Foundation.Polygraph.RawPolyTerm.interval1
  | intervalOpp {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {innerPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (innerValue : PolyTerm context Ty.interval innerPolyRaw) :
      PolyTerm context Ty.interval
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.intervalOpp
          innerPolyRaw)
  | intervalMeet {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftPolyRaw rightPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (leftValue : PolyTerm context Ty.interval leftPolyRaw)
      (rightValue : PolyTerm context Ty.interval rightPolyRaw) :
      PolyTerm context Ty.interval
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.intervalMeet
          leftPolyRaw rightPolyRaw)
  | intervalJoin {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftPolyRaw rightPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (leftValue : PolyTerm context Ty.interval leftPolyRaw)
      (rightValue : PolyTerm context Ty.interval rightPolyRaw) :
      PolyTerm context Ty.interval
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.intervalJoin
          leftPolyRaw rightPolyRaw)
  -- Cubical paths
  | pathLam {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      (carrierType : Ty level scope)
      (leftEndpoint rightEndpoint : LeanFX2.RawTerm scope)
      {bodyPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm (scope + 1)}
      (body :
        PolyTerm (context.cons Ty.interval) carrierType.weaken
          bodyPolyRaw) :
      PolyTerm context (Ty.path carrierType leftEndpoint rightEndpoint)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.pathLam bodyPolyRaw)
  | pathApp {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      {carrierType : Ty level scope}
      {leftEndpoint rightEndpoint : LeanFX2.RawTerm scope}
      {pathPolyRaw intervalPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (pathTerm :
        PolyTerm context
          (Ty.path carrierType leftEndpoint rightEndpoint)
          pathPolyRaw)
      (intervalTerm :
        PolyTerm context Ty.interval intervalPolyRaw) :
      PolyTerm context carrierType
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.pathApp
          pathPolyRaw intervalPolyRaw)
  -- Cubical Glue
  | glueIntro {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      (baseType : Ty level scope)
      (boundaryWitness : LeanFX2.RawTerm scope)
      {basePolyRaw partialPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (baseValue : PolyTerm context baseType basePolyRaw)
      (partialValue : PolyTerm context baseType partialPolyRaw) :
      PolyTerm context (Ty.glue baseType boundaryWitness)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.glueIntro
          basePolyRaw partialPolyRaw)
  | glueElim {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      {baseType : Ty level scope}
      {boundaryWitness : LeanFX2.RawTerm scope}
      {gluedPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (gluedValue :
        PolyTerm context (Ty.glue baseType boundaryWitness)
          gluedPolyRaw) :
      PolyTerm context baseType
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.glueElim
          gluedPolyRaw)
  -- Cubical Kan ops
  | transp {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      (universeLevel : UniverseLevel)
      (universeLevelLt : universeLevel.toNat + 1 ≤ level)
      (sourceType targetType : Ty level scope)
      (sourceTypeRaw targetTypeRaw : LeanFX2.RawTerm scope)
      {pathPolyRaw sourcePolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (typePath :
        PolyTerm context
          (Ty.path (Ty.universe universeLevel universeLevelLt)
            sourceTypeRaw targetTypeRaw)
          pathPolyRaw)
      (sourceValue :
        PolyTerm context sourceType sourcePolyRaw) :
      PolyTerm context targetType
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.transp
          pathPolyRaw sourcePolyRaw)
  | hcomp {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      {carrierType : Ty level scope}
      {sidesPolyRaw capPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (sidesValue :
        PolyTerm context carrierType sidesPolyRaw)
      (capValue :
        PolyTerm context carrierType capPolyRaw) :
      PolyTerm context carrierType
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.hcomp
          sidesPolyRaw capPolyRaw)
  -- Records (single-field; multi-field elaborates to nested)
  | recordIntro {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {singleFieldType : Ty level scope}
      {firstPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (firstField :
        PolyTerm context singleFieldType firstPolyRaw) :
      PolyTerm context (Ty.record singleFieldType)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.recordIntro
          firstPolyRaw)
  | recordProj {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {singleFieldType : Ty level scope}
      {recordPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (recordValue :
        PolyTerm context (Ty.record singleFieldType) recordPolyRaw) :
      PolyTerm context singleFieldType
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.recordProj
          recordPolyRaw)
  -- Refinement
  | refineIntro {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {baseType : Ty level scope}
      (predicate : LeanFX2.RawTerm (scope + 1))
      {valuePolyRaw proofPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (baseValue : PolyTerm context baseType valuePolyRaw)
      (predicateProof : PolyTerm context Ty.unit proofPolyRaw) :
      PolyTerm context (Ty.refine baseType predicate)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.refineIntro
          valuePolyRaw proofPolyRaw)
  | refineElim {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {baseType : Ty level scope}
      {predicate : LeanFX2.RawTerm (scope + 1)}
      {refinedPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (refinedValue :
        PolyTerm context (Ty.refine baseType predicate)
          refinedPolyRaw) :
      PolyTerm context baseType
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.refineElim
          refinedPolyRaw)
  -- Codata
  | codataUnfold {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {stateType outputType : Ty level scope}
      {statePolyRaw transitionPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (initialState : PolyTerm context stateType statePolyRaw)
      (transition :
        PolyTerm context (Ty.arrow stateType outputType)
          transitionPolyRaw) :
      PolyTerm context (Ty.codata stateType outputType)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.codataUnfold
          statePolyRaw transitionPolyRaw)
  | codataDest {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {stateType outputType : Ty level scope}
      {codataPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (codataValue :
        PolyTerm context (Ty.codata stateType outputType)
          codataPolyRaw) :
      PolyTerm context outputType
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.codataDest
          codataPolyRaw)
  -- Sessions
  | sessionSend {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (protocolStep : LeanFX2.RawTerm scope)
      {payloadType : Ty level scope}
      {channelPolyRaw payloadPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (channel :
        PolyTerm context (Ty.session protocolStep) channelPolyRaw)
      (payload : PolyTerm context payloadType payloadPolyRaw) :
      PolyTerm context (Ty.session protocolStep)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.sessionSend
          channelPolyRaw payloadPolyRaw)
  | sessionRecv {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {protocolStep : LeanFX2.RawTerm scope}
      {channelPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (channel :
        PolyTerm context (Ty.session protocolStep) channelPolyRaw) :
      PolyTerm context (Ty.session protocolStep)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.sessionRecv
          channelPolyRaw)
  -- Effects (with row-permission evidence)
  | effectPerform {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (effectTag : LeanFX2.RawTerm scope)
      (effectRow : Effects.EffectRow)
      (operationSignature :
        Effects.OperationSignature (Ty level scope))
      (canPerformOperation :
        Effects.CanPerform effectRow operationSignature)
      {operationPolyRaw argumentsPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (operationTag :
        PolyTerm context
          (Ty.effect operationSignature.argumentCarrier effectTag)
          operationPolyRaw)
      (arguments :
        PolyTerm context operationSignature.argumentCarrier
          argumentsPolyRaw) :
      PolyTerm context
        (Ty.effect operationSignature.resultCarrier effectTag)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.effectPerform
          operationPolyRaw argumentsPolyRaw)
  -- Universe code
  | universeCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (innerLevel outerLevel : UniverseLevel)
      (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
      (levelLe : outerLevel.toNat + 1 ≤ level) :
      PolyTerm context (Ty.universe outerLevel levelLe)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.universeCode
          innerLevel.toNat)
  -- Cross-level cumulativity (CUMUL-2.6 Design D)
  | cumulUp {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (lowerLevel higherLevel : UniverseLevel)
      (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
      (levelLeLow : lowerLevel.toNat + 1 ≤ level)
      (levelLeHigh : higherLevel.toNat + 1 ≤ level)
      {codePolyRaw : LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (typeCode :
        PolyTerm context (Ty.universe lowerLevel levelLeLow)
          codePolyRaw) :
      PolyTerm context (Ty.universe higherLevel levelLeHigh)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.cumulUpMarker
          codePolyRaw)
  /-- Canonical identity equivalence `A ≃ A`.  Mirrors
  `Term.equivReflId`; raw form is `equivIntro (lam (var 0))
  (lam (var 0))` in RawPolyTerm. -/
  | equivReflId {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (carrier : Ty level scope) :
      PolyTerm context (Ty.equiv carrier carrier)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.equivIntro
          (LeanFX2.Foundation.Polygraph.RawPolyTerm.lam
            (LeanFX2.Foundation.Polygraph.RawPolyTerm.var
              ⟨0, Nat.zero_lt_succ scope⟩))
          (LeanFX2.Foundation.Polygraph.RawPolyTerm.lam
            (LeanFX2.Foundation.Polygraph.RawPolyTerm.var
              ⟨0, Nat.zero_lt_succ scope⟩)))
  /-- Canonical pointwise-refl funext witness.  Mirrors
  `Term.funextRefl`. -/
  | funextRefl {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (domainType : Ty level scope) (codomainType : Ty level scope)
      (applyPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm (scope + 1)) :
      PolyTerm context
        (Ty.piTy domainType
          (Ty.id codomainType.weaken applyPolyRaw.toRawTerm
            applyPolyRaw.toRawTerm))
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.lam
          (LeanFX2.Foundation.Polygraph.RawPolyTerm.refl
            applyPolyRaw))
  /-- Canonical Id-typed identity equivalence at the universe.
  Mirrors `Term.equivReflIdAtId`. -/
  | equivReflIdAtId {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (innerLevel : UniverseLevel)
      (innerLevelLt : innerLevel.toNat + 1 ≤ level)
      (carrier : Ty level scope)
      (carrierRaw : LeanFX2.RawTerm scope) :
      PolyTerm context
        (Ty.id (Ty.universe innerLevel innerLevelLt) carrierRaw
          carrierRaw)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.equivIntro
          (LeanFX2.Foundation.Polygraph.RawPolyTerm.lam
            (LeanFX2.Foundation.Polygraph.RawPolyTerm.var
              ⟨0, Nat.zero_lt_succ scope⟩))
          (LeanFX2.Foundation.Polygraph.RawPolyTerm.lam
            (LeanFX2.Foundation.Polygraph.RawPolyTerm.var
              ⟨0, Nat.zero_lt_succ scope⟩)))
  /-- Canonical Id-typed funext witness at arrow types.  Mirrors
  `Term.funextReflAtId`. -/
  | funextReflAtId {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (domainType codomainType : Ty level scope)
      (applyPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm (scope + 1)) :
      PolyTerm context
        (Ty.id (Ty.arrow domainType codomainType)
          (LeanFX2.RawTerm.lam (LeanFX2.RawTerm.refl applyPolyRaw.toRawTerm))
          (LeanFX2.RawTerm.lam (LeanFX2.RawTerm.refl applyPolyRaw.toRawTerm)))
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.lam
          (LeanFX2.Foundation.Polygraph.RawPolyTerm.refl
            applyPolyRaw))
  /-- Heterogeneous-carrier equivalence introduction.  leftInv /
  rightInv proof obligations carry the same motive types as
  `Term.equivIntroHet` (`equivIntroHetLeftInverseType` /
  `equivIntroHetRightInverseType`), migrated to
  Foundation/TermHelpers for shared Layer-0 access.  Forward+
  backward subterms project to the raw-level `equivIntro`; leftInv
  / rightInv are proof-erased at the raw projection.  Strict-
  lossless bijection. -/
  | equivIntroHet {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {carrierA carrierB : Ty level scope}
      {forwardPolyRaw backwardPolyRaw leftInvPolyRaw rightInvPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (forward :
        PolyTerm context (Ty.arrow carrierA carrierB) forwardPolyRaw)
      (backward :
        PolyTerm context (Ty.arrow carrierB carrierA) backwardPolyRaw)
      (leftInv :
        PolyTerm context
          (equivIntroHetLeftInverseType carrierA
            forwardPolyRaw.toRawTerm backwardPolyRaw.toRawTerm)
          leftInvPolyRaw)
      (rightInv :
        PolyTerm context
          (equivIntroHetRightInverseType carrierB
            forwardPolyRaw.toRawTerm backwardPolyRaw.toRawTerm)
          rightInvPolyRaw) :
      PolyTerm context (Ty.equiv carrierA carrierB)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.equivIntro
          forwardPolyRaw backwardPolyRaw)
  /-- Equivalence application (kernel-internal form, distinct raw from
  univalence-β `equivApply`). -/
  | equivApp {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {carrierA carrierB : Ty level scope}
      {equivPolyRaw argumentPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (equivTerm :
        PolyTerm context (Ty.equiv carrierA carrierB) equivPolyRaw)
      (argumentTerm :
        PolyTerm context carrierA argumentPolyRaw) :
      PolyTerm context carrierB
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.equivApp
          equivPolyRaw argumentPolyRaw)
  /-- Heterogeneous-carrier path-from-equivalence (univalence
  intro).  Mirrors `Term.uaIntroHet`. -/
  | uaIntroHet {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (innerLevel : UniverseLevel)
      (innerLevelLt : innerLevel.toNat + 1 ≤ level)
      {carrierA carrierB : Ty level scope}
      (carrierARaw carrierBRaw : LeanFX2.RawTerm scope)
      {forwardPolyRaw backwardPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (equivWitness :
        PolyTerm context (Ty.equiv carrierA carrierB)
          (LeanFX2.Foundation.Polygraph.RawPolyTerm.equivIntro
            forwardPolyRaw backwardPolyRaw)) :
      PolyTerm context
        (Ty.id (Ty.universe innerLevel innerLevelLt) carrierARaw
          carrierBRaw)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.equivIntro
          forwardPolyRaw backwardPolyRaw)
  /-- Heterogeneous-carrier funext at Id-of-arrow.  Mirrors
  `Term.funextIntroHet`. -/
  | funextIntroHet {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (domainType codomainType : Ty level scope)
      (applyAPolyRaw applyBPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm (scope + 1)) :
      PolyTerm context
        (Ty.id (Ty.arrow domainType codomainType)
          (LeanFX2.RawTerm.lam applyAPolyRaw.toRawTerm)
          (LeanFX2.RawTerm.lam applyBPolyRaw.toRawTerm))
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.lam
          (LeanFX2.Foundation.Polygraph.RawPolyTerm.refl
            applyAPolyRaw))
  -- Type-shape codes (CUMUL-2.4 schematic VALUE-shaped ctors)
  | arrowCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (domainCodePolyRaw codomainCodePolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope) :
      PolyTerm context (Ty.universe outerLevel levelLe)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.arrowCode
          domainCodePolyRaw codomainCodePolyRaw)
  | piTyCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (domainCodePolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope)
      (codomainCodePolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm (scope + 1)) :
      PolyTerm context (Ty.universe outerLevel levelLe)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.piTyCode
          domainCodePolyRaw codomainCodePolyRaw)
  | sigmaTyCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (domainCodePolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope)
      (codomainCodePolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm (scope + 1)) :
      PolyTerm context (Ty.universe outerLevel levelLe)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.sigmaTyCode
          domainCodePolyRaw codomainCodePolyRaw)
  | productCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (firstCodePolyRaw secondCodePolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope) :
      PolyTerm context (Ty.universe outerLevel levelLe)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.productCode
          firstCodePolyRaw secondCodePolyRaw)
  | sumCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (leftCodePolyRaw rightCodePolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope) :
      PolyTerm context (Ty.universe outerLevel levelLe)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.sumCode
          leftCodePolyRaw rightCodePolyRaw)
  | listCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (elementCodePolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope) :
      PolyTerm context (Ty.universe outerLevel levelLe)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.listCode
          elementCodePolyRaw)
  | optionCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (elementCodePolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope) :
      PolyTerm context (Ty.universe outerLevel levelLe)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.optionCode
          elementCodePolyRaw)
  | eitherCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (leftCodePolyRaw rightCodePolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope) :
      PolyTerm context (Ty.universe outerLevel levelLe)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.eitherCode
          leftCodePolyRaw rightCodePolyRaw)
  | idCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (typeCodePolyRaw leftPolyRaw rightPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope) :
      PolyTerm context (Ty.universe outerLevel levelLe)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.idCode
          typeCodePolyRaw leftPolyRaw rightPolyRaw)
  | equivCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (leftTypeCodePolyRaw rightTypeCodePolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope) :
      PolyTerm context (Ty.universe outerLevel levelLe)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.equivCode
          leftTypeCodePolyRaw rightTypeCodePolyRaw)
  /-- Univalence-β extractor: proof of `Id (Universe lvl) A B` to
  `Equiv A B`.  Mirrors `Term.uaToEquiv`. -/
  | uaToEquiv {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (innerLevel : UniverseLevel)
      (innerLevelLt : innerLevel.toNat + 1 ≤ level)
      (leftTy rightTy : Ty level scope)
      (leftTyRaw rightTyRaw : LeanFX2.RawTerm scope)
      {proofPolyRaw : LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (proof :
        PolyTerm context
          (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw
            rightTyRaw)
          proofPolyRaw) :
      PolyTerm context (Ty.equiv leftTy rightTy)
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.uaToEquiv
          proofPolyRaw)
  /-- Univalence-β application.  Mirrors `Term.equivApply`. -/
  | equivApply {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {carrierA carrierB : Ty level scope}
      {equivPolyRaw argumentPolyRaw :
        LeanFX2.Foundation.Polygraph.RawPolyTerm scope}
      (equivTerm :
        PolyTerm context (Ty.equiv carrierA carrierB) equivPolyRaw)
      (argumentTerm :
        PolyTerm context carrierA argumentPolyRaw) :
      PolyTerm context carrierB
        (LeanFX2.Foundation.Polygraph.RawPolyTerm.equivApply
          equivPolyRaw argumentPolyRaw)

end LeanFX2
