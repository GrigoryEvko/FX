import LeanFX2.Foundation.Polygraph.PolyTerm

/-! # K11.12 — raw-level roundtrip theorems for the polygraph bijection.

The K-lineage's polygraph encoding (Burroni 1993) ships two raw-level
converters:

* `RawTerm.toRawPoly : RawTerm scope → RawPolyTerm scope` (K11.10-A).
* `RawPolyTerm.toRawTerm : RawPolyTerm scope → RawTerm scope` (K11.8).

This file proves both directions of the roundtrip identity:

* `RawTerm.toRawPoly_toRawTerm : r.toRawPoly.toRawTerm = r`
* `RawPolyTerm.toRawTerm_toRawPoly : p.toRawTerm.toRawPoly = p`

Each is by structural induction on the source, with one arm per
constructor (73 each).  Both functions are `@[reducible]`, so each
recursive case collapses via `congrArg` / `congrArg2` / `congrArg3`
combinators applied to the inductive hypotheses.  No axiom dependency.

## Why these matter

K11.10-B (`Term.toPoly`, the typed forward bijection) needs
`RawTerm.toRawPoly_toRawTerm` to discharge the index alignment for
PolyTerm constructors whose `Ty` indices embed
`argumentPolyRaw.toRawTerm`.  Without this roundtrip identity, the
forward typed direction has a structural blocker (see
`Term/PolyToTerm.lean` docstring).

## Audit

* `#print axioms RawTerm.toRawPoly_toRawTerm` reports "does not
  depend on any axioms"
* `#print axioms RawPolyTerm.toRawTerm_toRawPoly` likewise
-/

namespace LeanFX2

open LeanFX2.Foundation.Polygraph

/-- Local 2-argument congruence — `f a b = f a' b'` from
component-wise equalities.  Zero-axiom: built from core `congrArg`
and `congr` (both propext-free in Init.Prelude). -/
private theorem congrArg2 {alpha beta gamma : Sort _}
    (functionMap : alpha → beta → gamma)
    {leftFirst rightFirst : alpha} {leftSecond rightSecond : beta}
    (firstEq : leftFirst = rightFirst)
    (secondEq : leftSecond = rightSecond) :
    functionMap leftFirst leftSecond =
      functionMap rightFirst rightSecond :=
  congr (congrArg functionMap firstEq) secondEq

/-- Local 3-argument congruence — `f a b c = f a' b' c'` from
component-wise equalities.  Zero-axiom. -/
private theorem congrArg3 {alpha beta gamma delta : Sort _}
    (functionMap : alpha → beta → gamma → delta)
    {leftFirst rightFirst : alpha}
    {leftSecond rightSecond : beta}
    {leftThird rightThird : gamma}
    (firstEq : leftFirst = rightFirst)
    (secondEq : leftSecond = rightSecond)
    (thirdEq : leftThird = rightThird) :
    functionMap leftFirst leftSecond leftThird =
      functionMap rightFirst rightSecond rightThird :=
  congr (congrArg2 functionMap firstEq secondEq) thirdEq

/-! ## Forward roundtrip: `RawTerm → RawPolyTerm → RawTerm = id`. -/

/-- `r.toRawPoly.toRawTerm = r` for every `RawTerm`.  Structural
induction on `r`; each case reduces both `@[reducible]` converters
to a constructor application whose subterms are themselves
`subterm.toRawPoly.toRawTerm`, then closes via the IH and
`congrArg{,2,3}`. -/
theorem RawTerm.toRawPoly_toRawTerm {scope : Nat} (rawTerm : RawTerm scope) :
    rawTerm.toRawPoly.toRawTerm = rawTerm := by
  induction rawTerm with
  | var _ => rfl
  | unit => rfl
  | lam _ ihBody => exact congrArg RawTerm.lam ihBody
  | app _ _ ihFunction ihArgument =>
      exact congrArg2 RawTerm.app ihFunction ihArgument
  | pair _ _ ihFirst ihSecond =>
      exact congrArg2 RawTerm.pair ihFirst ihSecond
  | fst _ ihPair => exact congrArg RawTerm.fst ihPair
  | snd _ ihPair => exact congrArg RawTerm.snd ihPair
  | boolTrue => rfl
  | boolFalse => rfl
  | boolElim _ _ _ ihScrutinee ihThen ihElse =>
      exact congrArg3 RawTerm.boolElim ihScrutinee ihThen ihElse
  | natZero => rfl
  | natSucc _ ihPredecessor =>
      exact congrArg RawTerm.natSucc ihPredecessor
  | natElim _ _ _ ihScrutinee ihZero ihSucc =>
      exact congrArg3 RawTerm.natElim ihScrutinee ihZero ihSucc
  | natRec _ _ _ ihScrutinee ihZero ihSucc =>
      exact congrArg3 RawTerm.natRec ihScrutinee ihZero ihSucc
  | listNil => rfl
  | listCons _ _ ihHead ihTail =>
      exact congrArg2 RawTerm.listCons ihHead ihTail
  | listElim _ _ _ ihScrutinee ihNil ihCons =>
      exact congrArg3 RawTerm.listElim ihScrutinee ihNil ihCons
  | optionNone => rfl
  | optionSome _ ihValue => exact congrArg RawTerm.optionSome ihValue
  | optionMatch _ _ _ ihScrutinee ihNone ihSome =>
      exact congrArg3 RawTerm.optionMatch ihScrutinee ihNone ihSome
  | eitherInl _ ihValue => exact congrArg RawTerm.eitherInl ihValue
  | eitherInr _ ihValue => exact congrArg RawTerm.eitherInr ihValue
  | eitherMatch _ _ _ ihScrutinee ihLeft ihRight =>
      exact congrArg3 RawTerm.eitherMatch ihScrutinee ihLeft ihRight
  | refl _ ihWitness => exact congrArg RawTerm.refl ihWitness
  | idJ _ _ ihBaseCase ihWitness =>
      exact congrArg2 RawTerm.idJ ihBaseCase ihWitness
  | modIntro _ ihInner => exact congrArg RawTerm.modIntro ihInner
  | modElim _ ihInner => exact congrArg RawTerm.modElim ihInner
  | subsume _ ihInner => exact congrArg RawTerm.subsume ihInner
  | interval0 => rfl
  | interval1 => rfl
  | intervalOpp _ ihInner =>
      exact congrArg RawTerm.intervalOpp ihInner
  | intervalMeet _ _ ihLeft ihRight =>
      exact congrArg2 RawTerm.intervalMeet ihLeft ihRight
  | intervalJoin _ _ ihLeft ihRight =>
      exact congrArg2 RawTerm.intervalJoin ihLeft ihRight
  | pathLam _ ihBody => exact congrArg RawTerm.pathLam ihBody
  | pathApp _ _ ihPath ihInterval =>
      exact congrArg2 RawTerm.pathApp ihPath ihInterval
  | glueIntro _ _ ihBase ihPartial =>
      exact congrArg2 RawTerm.glueIntro ihBase ihPartial
  | glueElim _ ihGlued => exact congrArg RawTerm.glueElim ihGlued
  | transp _ _ ihPath ihSource =>
      exact congrArg2 RawTerm.transp ihPath ihSource
  | transpFill _ _ _ ihPath ihInterval ihSource =>
      exact congrArg3 RawTerm.transpFill ihPath ihInterval ihSource
  | hcomp _ _ ihSides ihCap =>
      exact congrArg2 RawTerm.hcomp ihSides ihCap
  | oeqRefl _ ihWitness => exact congrArg RawTerm.oeqRefl ihWitness
  | oeqJ _ _ ihBaseCase ihWitness =>
      exact congrArg2 RawTerm.oeqJ ihBaseCase ihWitness
  | oeqFunext _ ihPointwise =>
      exact congrArg RawTerm.oeqFunext ihPointwise
  | idStrictRefl _ ihWitness =>
      exact congrArg RawTerm.idStrictRefl ihWitness
  | idStrictRec _ _ ihBaseCase ihWitness =>
      exact congrArg2 RawTerm.idStrictRec ihBaseCase ihWitness
  | equivIntro _ _ ihForward ihBackward =>
      exact congrArg2 RawTerm.equivIntro ihForward ihBackward
  | equivApp _ _ ihEquiv ihArgument =>
      exact congrArg2 RawTerm.equivApp ihEquiv ihArgument
  | refineIntro _ _ ihRaw ihProof =>
      exact congrArg2 RawTerm.refineIntro ihRaw ihProof
  | refineElim _ ihRefined =>
      exact congrArg RawTerm.refineElim ihRefined
  | recordIntro _ ihFirst =>
      exact congrArg RawTerm.recordIntro ihFirst
  | recordProj _ ihRecord =>
      exact congrArg RawTerm.recordProj ihRecord
  | codataUnfold _ _ ihInitial ihTransition =>
      exact congrArg2 RawTerm.codataUnfold ihInitial ihTransition
  | codataDest _ ihCodata =>
      exact congrArg RawTerm.codataDest ihCodata
  | sessionSend _ _ ihChannel ihPayload =>
      exact congrArg2 RawTerm.sessionSend ihChannel ihPayload
  | sessionRecv _ ihChannel =>
      exact congrArg RawTerm.sessionRecv ihChannel
  | effectPerform _ _ ihTag ihArguments =>
      exact congrArg2 RawTerm.effectPerform ihTag ihArguments
  | universeCode _ => rfl
  | arrowCode _ _ ihDomain ihCodomain =>
      exact congrArg2 RawTerm.arrowCode ihDomain ihCodomain
  | piTyCode _ _ ihDomain ihCodomain =>
      exact congrArg2 RawTerm.piTyCode ihDomain ihCodomain
  | sigmaTyCode _ _ ihDomain ihCodomain =>
      exact congrArg2 RawTerm.sigmaTyCode ihDomain ihCodomain
  | productCode _ _ ihFirst ihSecond =>
      exact congrArg2 RawTerm.productCode ihFirst ihSecond
  | sumCode _ _ ihLeft ihRight =>
      exact congrArg2 RawTerm.sumCode ihLeft ihRight
  | listCode _ ihElement =>
      exact congrArg RawTerm.listCode ihElement
  | optionCode _ ihElement =>
      exact congrArg RawTerm.optionCode ihElement
  | eitherCode _ _ ihLeft ihRight =>
      exact congrArg2 RawTerm.eitherCode ihLeft ihRight
  | idCode _ _ _ ihTypeCode ihLeft ihRight =>
      exact congrArg3 RawTerm.idCode ihTypeCode ihLeft ihRight
  | equivCode _ _ ihLeft ihRight =>
      exact congrArg2 RawTerm.equivCode ihLeft ihRight
  | cumulUpMarker _ ihInner =>
      exact congrArg RawTerm.cumulUpMarker ihInner
  | uaToEquiv _ ihProof =>
      exact congrArg RawTerm.uaToEquiv ihProof
  | equivApply _ _ ihEquiv ihArg =>
      exact congrArg2 RawTerm.equivApply ihEquiv ihArg
  | pathCompose _ _ ihLeft ihRight =>
      exact congrArg2 RawTerm.pathCompose ihLeft ihRight
  | idToEquiv _ ihProof =>
      exact congrArg RawTerm.idToEquiv ihProof
  | oeqTrans _ _ ihFirst ihSecond =>
      exact congrArg2 RawTerm.oeqTrans ihFirst ihSecond
  | equivCompose _ _ ihFirst ihSecond =>
      exact congrArg2 RawTerm.equivCompose ihFirst ihSecond

end LeanFX2

namespace LeanFX2.Foundation.Polygraph

/-! ## Backward roundtrip: `RawPolyTerm → RawTerm → RawPolyTerm = id`. -/

/-- `p.toRawTerm.toRawPoly = p` for every `RawPolyTerm`.  Mirror of
`RawTerm.toRawPoly_toRawTerm`, same structural recursion pattern.

Lives in `LeanFX2.Foundation.Polygraph` namespace so the resulting
constant is `LeanFX2.Foundation.Polygraph.RawPolyTerm.toRawTerm_toRawPoly`
— matching the namespace of `RawPolyTerm` itself.  -/
theorem RawPolyTerm.toRawTerm_toRawPoly {scope : Nat}
    (rawPolyTerm : RawPolyTerm scope) :
    rawPolyTerm.toRawTerm.toRawPoly = rawPolyTerm := by
  induction rawPolyTerm with
  | var _ => rfl
  | unit => rfl
  | lam _ ihBody => exact congrArg RawPolyTerm.lam ihBody
  | app _ _ ihFunction ihArgument =>
      exact congrArg2 RawPolyTerm.app ihFunction ihArgument
  | pair _ _ ihFirst ihSecond =>
      exact congrArg2 RawPolyTerm.pair ihFirst ihSecond
  | fst _ ihPair => exact congrArg RawPolyTerm.fst ihPair
  | snd _ ihPair => exact congrArg RawPolyTerm.snd ihPair
  | boolTrue => rfl
  | boolFalse => rfl
  | boolElim _ _ _ ihScrutinee ihThen ihElse =>
      exact congrArg3 RawPolyTerm.boolElim ihScrutinee ihThen ihElse
  | natZero => rfl
  | natSucc _ ihPredecessor =>
      exact congrArg RawPolyTerm.natSucc ihPredecessor
  | natElim _ _ _ ihScrutinee ihZero ihSucc =>
      exact congrArg3 RawPolyTerm.natElim ihScrutinee ihZero ihSucc
  | natRec _ _ _ ihScrutinee ihZero ihSucc =>
      exact congrArg3 RawPolyTerm.natRec ihScrutinee ihZero ihSucc
  | listNil => rfl
  | listCons _ _ ihHead ihTail =>
      exact congrArg2 RawPolyTerm.listCons ihHead ihTail
  | listElim _ _ _ ihScrutinee ihNil ihCons =>
      exact congrArg3 RawPolyTerm.listElim ihScrutinee ihNil ihCons
  | optionNone => rfl
  | optionSome _ ihValue =>
      exact congrArg RawPolyTerm.optionSome ihValue
  | optionMatch _ _ _ ihScrutinee ihNone ihSome =>
      exact congrArg3 RawPolyTerm.optionMatch ihScrutinee ihNone ihSome
  | eitherInl _ ihValue =>
      exact congrArg RawPolyTerm.eitherInl ihValue
  | eitherInr _ ihValue =>
      exact congrArg RawPolyTerm.eitherInr ihValue
  | eitherMatch _ _ _ ihScrutinee ihLeft ihRight =>
      exact congrArg3 RawPolyTerm.eitherMatch ihScrutinee ihLeft ihRight
  | refl _ ihWitness => exact congrArg RawPolyTerm.refl ihWitness
  | idJ _ _ ihBaseCase ihWitness =>
      exact congrArg2 RawPolyTerm.idJ ihBaseCase ihWitness
  | modIntro _ ihInner => exact congrArg RawPolyTerm.modIntro ihInner
  | modElim _ ihInner => exact congrArg RawPolyTerm.modElim ihInner
  | subsume _ ihInner => exact congrArg RawPolyTerm.subsume ihInner
  | interval0 => rfl
  | interval1 => rfl
  | intervalOpp _ ihInner =>
      exact congrArg RawPolyTerm.intervalOpp ihInner
  | intervalMeet _ _ ihLeft ihRight =>
      exact congrArg2 RawPolyTerm.intervalMeet ihLeft ihRight
  | intervalJoin _ _ ihLeft ihRight =>
      exact congrArg2 RawPolyTerm.intervalJoin ihLeft ihRight
  | pathLam _ ihBody => exact congrArg RawPolyTerm.pathLam ihBody
  | pathApp _ _ ihPath ihInterval =>
      exact congrArg2 RawPolyTerm.pathApp ihPath ihInterval
  | glueIntro _ _ ihBase ihPartial =>
      exact congrArg2 RawPolyTerm.glueIntro ihBase ihPartial
  | glueElim _ ihGlued => exact congrArg RawPolyTerm.glueElim ihGlued
  | transp _ _ ihPath ihSource =>
      exact congrArg2 RawPolyTerm.transp ihPath ihSource
  | transpFill _ _ _ ihPath ihInterval ihSource =>
      exact congrArg3 RawPolyTerm.transpFill ihPath ihInterval ihSource
  | hcomp _ _ ihSides ihCap =>
      exact congrArg2 RawPolyTerm.hcomp ihSides ihCap
  | oeqRefl _ ihWitness => exact congrArg RawPolyTerm.oeqRefl ihWitness
  | oeqJ _ _ ihBaseCase ihWitness =>
      exact congrArg2 RawPolyTerm.oeqJ ihBaseCase ihWitness
  | oeqFunext _ ihPointwise =>
      exact congrArg RawPolyTerm.oeqFunext ihPointwise
  | idStrictRefl _ ihWitness =>
      exact congrArg RawPolyTerm.idStrictRefl ihWitness
  | idStrictRec _ _ ihBaseCase ihWitness =>
      exact congrArg2 RawPolyTerm.idStrictRec ihBaseCase ihWitness
  | equivIntro _ _ ihForward ihBackward =>
      exact congrArg2 RawPolyTerm.equivIntro ihForward ihBackward
  | equivApp _ _ ihEquiv ihArgument =>
      exact congrArg2 RawPolyTerm.equivApp ihEquiv ihArgument
  | refineIntro _ _ ihRaw ihProof =>
      exact congrArg2 RawPolyTerm.refineIntro ihRaw ihProof
  | refineElim _ ihRefined =>
      exact congrArg RawPolyTerm.refineElim ihRefined
  | recordIntro _ ihFirst =>
      exact congrArg RawPolyTerm.recordIntro ihFirst
  | recordProj _ ihRecord =>
      exact congrArg RawPolyTerm.recordProj ihRecord
  | codataUnfold _ _ ihInitial ihTransition =>
      exact congrArg2 RawPolyTerm.codataUnfold ihInitial ihTransition
  | codataDest _ ihCodata =>
      exact congrArg RawPolyTerm.codataDest ihCodata
  | sessionSend _ _ ihChannel ihPayload =>
      exact congrArg2 RawPolyTerm.sessionSend ihChannel ihPayload
  | sessionRecv _ ihChannel =>
      exact congrArg RawPolyTerm.sessionRecv ihChannel
  | effectPerform _ _ ihTag ihArguments =>
      exact congrArg2 RawPolyTerm.effectPerform ihTag ihArguments
  | universeCode _ => rfl
  | arrowCode _ _ ihDomain ihCodomain =>
      exact congrArg2 RawPolyTerm.arrowCode ihDomain ihCodomain
  | piTyCode _ _ ihDomain ihCodomain =>
      exact congrArg2 RawPolyTerm.piTyCode ihDomain ihCodomain
  | sigmaTyCode _ _ ihDomain ihCodomain =>
      exact congrArg2 RawPolyTerm.sigmaTyCode ihDomain ihCodomain
  | productCode _ _ ihFirst ihSecond =>
      exact congrArg2 RawPolyTerm.productCode ihFirst ihSecond
  | sumCode _ _ ihLeft ihRight =>
      exact congrArg2 RawPolyTerm.sumCode ihLeft ihRight
  | listCode _ ihElement =>
      exact congrArg RawPolyTerm.listCode ihElement
  | optionCode _ ihElement =>
      exact congrArg RawPolyTerm.optionCode ihElement
  | eitherCode _ _ ihLeft ihRight =>
      exact congrArg2 RawPolyTerm.eitherCode ihLeft ihRight
  | idCode _ _ _ ihTypeCode ihLeft ihRight =>
      exact congrArg3 RawPolyTerm.idCode ihTypeCode ihLeft ihRight
  | equivCode _ _ ihLeft ihRight =>
      exact congrArg2 RawPolyTerm.equivCode ihLeft ihRight
  | cumulUpMarker _ ihInner =>
      exact congrArg RawPolyTerm.cumulUpMarker ihInner
  | uaToEquiv _ ihProof =>
      exact congrArg RawPolyTerm.uaToEquiv ihProof
  | equivApply _ _ ihEquiv ihArg =>
      exact congrArg2 RawPolyTerm.equivApply ihEquiv ihArg
  | pathCompose _ _ ihLeft ihRight =>
      exact congrArg2 RawPolyTerm.pathCompose ihLeft ihRight
  | idToEquiv _ ihProof =>
      exact congrArg RawPolyTerm.idToEquiv ihProof
  | oeqTrans _ _ ihFirst ihSecond =>
      exact congrArg2 RawPolyTerm.oeqTrans ihFirst ihSecond
  | equivCompose _ _ ihFirst ihSecond =>
      exact congrArg2 RawPolyTerm.equivCompose ihFirst ihSecond

end LeanFX2.Foundation.Polygraph
