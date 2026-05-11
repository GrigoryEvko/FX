import LeanFX2.Foundation.Polygraph.RawPolyTerm
import LeanFX2.Foundation.Mode
import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.Subst
import LeanFX2.Foundation.SubstActsOnTy
import LeanFX2.Foundation.Context

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

## Phase A scope

This Phase A commit ships:

1. `RawPolyTerm.toRawTerm` — structural raw-level converter (73
   arms, one per `RawPolyTerm` ctor).
2. `PolyTerm` — typed mirror with the core MLTT fragment: `var`,
   `unit`, `lam`/`app`, `lamPi`/`appPi`, `pair`/`fst`/`snd`,
   `boolTrue`/`False`/`boolElim`, `natZero`/`Succ`/`natElim`/
   `natRec`, `listNil`/`Cons`/`Elim`, `optionNone`/`Some`/`Match`,
   `eitherInl`/`Inr`/`Match`, `refl`, `idJ` (27 ctors).

Phase B (K11.9.B follow-up) extends with the remaining ~46 ctors
(modal/cubical/HoTT-special/refine/record/codata/session/effect/
type-codes/cumulUp/univalence-beta).

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

end LeanFX2
