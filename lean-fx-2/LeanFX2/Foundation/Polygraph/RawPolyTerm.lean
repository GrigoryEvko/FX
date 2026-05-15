import LeanFX2.Foundation.Polygraph.PolyCell

/-! # `RawPolyTerm` — dim-0 polygraph encoding of raw terms.

Per K11.8 of the K-lineage: `RawPolyTerm` is the polygraph perspective
on raw terms.  Each constructor mirrors the corresponding `RawTerm`
constructor exactly — same arity, same field semantics, same scope
indexing — but lives in the `LeanFX2.Foundation.Polygraph` namespace
to give it a separate dispatch surface from `RawTerm`.

## Why a separate inductive (not `def RawPolyTerm := RawTerm`)

The four-encoding-column lattice (K14.13 "Tree ↔ PolyTerm ↔ ValueTerm
↔ EGraph") relies on each column being a distinct type.  A type-
alias collapse would defeat:

* K11.13 — Action framework integration: `rename` / `subst` on
  `RawPolyTerm` will dispatch through Polygraph-specific instances.
* K11.14 — `Step.toDim1Cell` embedding: needs `RawPolyTerm` and
  `Step` as distinct dim-0 / dim-1 polygraph cells.
* K11.16 — `Step ⇌ Dim1Cell` equivalence: requires a structural
  distinction between dim-0 terms and dim-1 reductions.
* K11.19 — Cost-tropical strategy framework: indexes cost via
  per-term-encoding metrics, which need separate types.

Keeping `RawPolyTerm` distinct preserves the K-lineage roadmap's
"four encodings" architecture.

## Constructor alignment

Every constructor name matches `RawTerm`'s constructor exactly.  The
K11.12 roundtrip theorem builds a structural bijection
`toRawTerm : RawPolyTerm scope → RawTerm scope` and
`fromRawTerm : RawTerm scope → RawPolyTerm scope` via case-by-case
mirroring, with both compositions producing `rfl` via the matched
names.

## Scope index

Single `Nat` scope index matches `RawTerm`'s convention.  All binder
constructors (`lam`, `pathLam`) carry their bodies at `scope + 1`
exactly as `RawTerm` does — the dim-0 polygraph encoding does not
flatten binders into the polygraph cell representation; binders
remain syntactic.

## Audit

Every declaration in this file ships zero-axiom.  `deriving
DecidableEq` is propext-clean because RawTerm has 73 ctors all of
which have decidable-equal Nat / RawPolyTerm payloads, and Lean's
`deriving DecidableEq` macro emits direct ctor-comparison code — no
auto-generated propext leak.  Verified via
`Smoke/AuditPhase12B1RawPolyTerm.lean`. -/

namespace LeanFX2.Foundation.Polygraph

/-- Dim-0 polygraph encoding of `LeanFX2.RawTerm`.  Constructors
mirror `RawTerm`'s 73 ctors exactly. -/
inductive RawPolyTerm : Nat → Type
  -- Variable
  | var {scope : Nat} (position : Fin scope) : RawPolyTerm scope
  -- Unit
  | unit {scope : Nat} : RawPolyTerm scope
  -- Function intro / elim
  | lam {scope : Nat} (body : RawPolyTerm (scope + 1)) :
      RawPolyTerm scope
  | app {scope : Nat}
      (functionTerm argumentTerm : RawPolyTerm scope) :
      RawPolyTerm scope
  -- Pair intro / elim
  | pair {scope : Nat}
      (firstValue secondValue : RawPolyTerm scope) :
      RawPolyTerm scope
  | fst {scope : Nat} (pairTerm : RawPolyTerm scope) :
      RawPolyTerm scope
  | snd {scope : Nat} (pairTerm : RawPolyTerm scope) :
      RawPolyTerm scope
  -- Booleans
  | boolTrue {scope : Nat} : RawPolyTerm scope
  | boolFalse {scope : Nat} : RawPolyTerm scope
  | boolElim {scope : Nat}
      (scrutinee thenBranch elseBranch : RawPolyTerm scope) :
      RawPolyTerm scope
  -- Naturals
  | natZero {scope : Nat} : RawPolyTerm scope
  | natSucc {scope : Nat} (predecessor : RawPolyTerm scope) :
      RawPolyTerm scope
  | natElim {scope : Nat}
      (scrutinee zeroBranch succBranch : RawPolyTerm scope) :
      RawPolyTerm scope
  | natRec {scope : Nat}
      (scrutinee zeroBranch succBranch : RawPolyTerm scope) :
      RawPolyTerm scope
  -- Lists
  | listNil {scope : Nat} : RawPolyTerm scope
  | listCons {scope : Nat}
      (headTerm tailTerm : RawPolyTerm scope) : RawPolyTerm scope
  | listElim {scope : Nat}
      (scrutinee nilBranch consBranch : RawPolyTerm scope) :
      RawPolyTerm scope
  -- Options
  | optionNone {scope : Nat} : RawPolyTerm scope
  | optionSome {scope : Nat} (valueTerm : RawPolyTerm scope) :
      RawPolyTerm scope
  | optionMatch {scope : Nat}
      (scrutinee noneBranch someBranch : RawPolyTerm scope) :
      RawPolyTerm scope
  -- Eithers
  | eitherInl {scope : Nat} (valueTerm : RawPolyTerm scope) :
      RawPolyTerm scope
  | eitherInr {scope : Nat} (valueTerm : RawPolyTerm scope) :
      RawPolyTerm scope
  | eitherMatch {scope : Nat}
      (scrutinee leftBranch rightBranch : RawPolyTerm scope) :
      RawPolyTerm scope
  -- HoTT identity types
  | refl {scope : Nat} (rawWitness : RawPolyTerm scope) :
      RawPolyTerm scope
  | idJ {scope : Nat}
      (baseCase witness : RawPolyTerm scope) : RawPolyTerm scope
  -- Modal (Layer 6)
  | modIntro {scope : Nat} (raw : RawPolyTerm scope) :
      RawPolyTerm scope
  | modElim {scope : Nat} (raw : RawPolyTerm scope) :
      RawPolyTerm scope
  | subsume {scope : Nat} (raw : RawPolyTerm scope) :
      RawPolyTerm scope
  -- Cubical interval lattice
  | interval0 {scope : Nat} : RawPolyTerm scope
  | interval1 {scope : Nat} : RawPolyTerm scope
  | intervalOpp {scope : Nat} (intervalTerm : RawPolyTerm scope) :
      RawPolyTerm scope
  | intervalMeet {scope : Nat}
      (leftInterval rightInterval : RawPolyTerm scope) :
      RawPolyTerm scope
  | intervalJoin {scope : Nat}
      (leftInterval rightInterval : RawPolyTerm scope) :
      RawPolyTerm scope
  -- Cubical path types
  | pathLam {scope : Nat} (body : RawPolyTerm (scope + 1)) :
      RawPolyTerm scope
  | pathApp {scope : Nat}
      (pathTerm intervalArg : RawPolyTerm scope) :
      RawPolyTerm scope
  -- Cubical glue + transport / composition
  | glueIntro {scope : Nat}
      (baseValue partialValue : RawPolyTerm scope) :
      RawPolyTerm scope
  | glueElim {scope : Nat} (gluedValue : RawPolyTerm scope) :
      RawPolyTerm scope
  | transp {scope : Nat}
      (path source : RawPolyTerm scope) : RawPolyTerm scope
  | transpFill {scope : Nat}
      (pathTy currentInterval source : RawPolyTerm scope) : RawPolyTerm scope
  | hcomp {scope : Nat}
      (sides cap : RawPolyTerm scope) : RawPolyTerm scope
  -- Observational equality
  | oeqRefl {scope : Nat} (witness : RawPolyTerm scope) :
      RawPolyTerm scope
  | oeqJ {scope : Nat}
      (baseCase witness : RawPolyTerm scope) : RawPolyTerm scope
  | oeqFunext {scope : Nat}
      (pointwiseEquality : RawPolyTerm scope) : RawPolyTerm scope
  -- Strict (definitional) identity
  | idStrictRefl {scope : Nat} (witness : RawPolyTerm scope) :
      RawPolyTerm scope
  | idStrictRec {scope : Nat}
      (baseCase witness : RawPolyTerm scope) : RawPolyTerm scope
  -- Type equivalence
  | equivIntro {scope : Nat}
      (forwardFn backwardFn : RawPolyTerm scope) :
      RawPolyTerm scope
  | equivApp {scope : Nat}
      (equivTerm argument : RawPolyTerm scope) : RawPolyTerm scope
  -- Refinement types
  | refineIntro {scope : Nat}
      (rawValue predicateProof : RawPolyTerm scope) :
      RawPolyTerm scope
  | refineElim {scope : Nat} (refinedValue : RawPolyTerm scope) :
      RawPolyTerm scope
  -- Record types
  | recordIntro {scope : Nat} (firstField : RawPolyTerm scope) :
      RawPolyTerm scope
  | recordProj {scope : Nat} (recordValue : RawPolyTerm scope) :
      RawPolyTerm scope
  -- Codata
  | codataUnfold {scope : Nat}
      (initialState transition : RawPolyTerm scope) :
      RawPolyTerm scope
  | codataDest {scope : Nat} (codataValue : RawPolyTerm scope) :
      RawPolyTerm scope
  -- Session-typed channels
  | sessionSend {scope : Nat}
      (channel payload : RawPolyTerm scope) : RawPolyTerm scope
  | sessionRecv {scope : Nat} (channel : RawPolyTerm scope) :
      RawPolyTerm scope
  -- Algebraic effects
  | effectPerform {scope : Nat}
      (operationTag arguments : RawPolyTerm scope) :
      RawPolyTerm scope
  -- Universe-code term
  | universeCode {scope : Nat} (innerLevel : Nat) :
      RawPolyTerm scope
  -- Per-shape type codes (CUMUL-2.1)
  | arrowCode {scope : Nat}
      (domainCode codomainCode : RawPolyTerm scope) :
      RawPolyTerm scope
  | piTyCode {scope : Nat}
      (domainCode : RawPolyTerm scope)
      (codomainCode : RawPolyTerm (scope + 1)) :
      RawPolyTerm scope
  | sigmaTyCode {scope : Nat}
      (domainCode : RawPolyTerm scope)
      (codomainCode : RawPolyTerm (scope + 1)) :
      RawPolyTerm scope
  | productCode {scope : Nat}
      (firstCode secondCode : RawPolyTerm scope) :
      RawPolyTerm scope
  | sumCode {scope : Nat}
      (leftCode rightCode : RawPolyTerm scope) :
      RawPolyTerm scope
  | listCode {scope : Nat} (elementCode : RawPolyTerm scope) :
      RawPolyTerm scope
  | optionCode {scope : Nat} (elementCode : RawPolyTerm scope) :
      RawPolyTerm scope
  | eitherCode {scope : Nat}
      (leftCode rightCode : RawPolyTerm scope) :
      RawPolyTerm scope
  | idCode {scope : Nat}
      (typeCode leftRaw rightRaw : RawPolyTerm scope) :
      RawPolyTerm scope
  | equivCode {scope : Nat}
      (leftTypeCode rightTypeCode : RawPolyTerm scope) :
      RawPolyTerm scope
  -- CUMUL-2.6 marker
  | cumulUpMarker {scope : Nat}
      (innerCodeRaw : RawPolyTerm scope) : RawPolyTerm scope
  -- D3.6 univalence / equivalence vocabulary
  | uaToEquiv {scope : Nat} (proofRaw : RawPolyTerm scope) :
      RawPolyTerm scope
  | equivApply {scope : Nat}
      (equivRaw argRaw : RawPolyTerm scope) : RawPolyTerm scope
  | pathCompose {scope : Nat}
      (leftPathRaw rightPathRaw : RawPolyTerm scope) :
      RawPolyTerm scope
  | idToEquiv {scope : Nat} (proofRaw : RawPolyTerm scope) :
      RawPolyTerm scope
  | oeqTrans {scope : Nat}
      (firstProof secondProof : RawPolyTerm scope) :
      RawPolyTerm scope
  | equivCompose {scope : Nat}
      (firstEquiv secondEquiv : RawPolyTerm scope) :
      RawPolyTerm scope
  deriving DecidableEq

end LeanFX2.Foundation.Polygraph
