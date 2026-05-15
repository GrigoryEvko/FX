import LeanFX2.Foundation.RawPartialRename.UnweakenInversion

/-! # LeanFX2.Foundation.RawPartialRename.TranspPiPathRecognizer

CCHM transpPi β path-body recognizer.  When the developed transp's
path argument is `RawTerm.pathLam pathBody`, the `cdTranspCase`
dispatcher (Phase F of D2.5.5) needs to decide whether `pathBody` has
the CCHM transpPi β shape:

  `pathBody = piTyCode domainCode codomainCode`  AND
  `unweaken? domainCode = some _` (domain doesn't bind the interval).

This file ships the recognizer as a single `Option`-valued kernel
primitive, propext-clean via 73-arm full enumeration.

## Dispatch contract (per `TranspPiContractum.lean` RFC)

The `cdTranspCase` dispatcher checks rules in priority order:

  1. `unweaken? pathBody = some _`  →  transpReflBeta fires (return source)
  2. `matchTranspPiBetaShape? pathBody = some (A, B)`  →  transpPiBeta
     fires (return `transpPiBetaContractum B source`)
  3. otherwise  →  cong rebuild

The recognizer only fires inside step 2 (after step 1 fails), so the
matching ordering enforces disjointness even though the predicates
themselves are not strictly disjoint (a CCHM Π type with BOTH domain
and codomain constant in the interval would match BOTH `unweaken?
pathBody = some _` and `matchTranspPiBetaShape?` — step 1's priority
resolves this).

## Root status

Layer 0 raw-syntax foundation primitive.  Strict zero-axiom.  Consumed
by future Phase F (`Confluence/RawCd/CubicalAndEquiv.lean` extension of
`cdTranspCase`) and Phase G (`RawStep.par.transpPiBeta` ctor LHS shape
check). -/

namespace LeanFX2

/-- Recognizer for the CCHM transpPi β path-body shape.  Returns
`some (innerDomain, codomainCode)` when `pathBody` is exactly
`RawTerm.piTyCode domainCode codomainCode` AND `domainCode`'s slot 0
(the path-interval position) is not used (i.e. `unweaken? domainCode
= some innerDomain` with `domainCode = innerDomain.weaken`).  Returns
`none` otherwise.

The 73-arm full enumeration keeps Lean 4's match compiler propext-
clean (no wildcard arms, per `feedback_lean_zero_axiom_match.md`).
Only the `piTyCode` arm does real work; the other 72 ctor arms map
to `.none` definitionally. -/
def RawTerm.matchTranspPiBetaShape? {scope : Nat}
    (pathBody : RawTerm (scope + 1)) :
    Option (RawTerm scope × RawTerm (scope + 2)) :=
  match pathBody with
  | RawTerm.piTyCode domainCode codomainCode =>
      match RawTerm.unweaken? domainCode with
      | some innerDomain => some (innerDomain, codomainCode)
      | none => none
  | RawTerm.var _ => none
  | RawTerm.unit => none
  | RawTerm.lam _ => none
  | RawTerm.app _ _ => none
  | RawTerm.pair _ _ => none
  | RawTerm.fst _ => none
  | RawTerm.snd _ => none
  | RawTerm.boolTrue => none
  | RawTerm.boolFalse => none
  | RawTerm.boolElim _ _ _ => none
  | RawTerm.natZero => none
  | RawTerm.natSucc _ => none
  | RawTerm.natElim _ _ _ => none
  | RawTerm.natRec _ _ _ => none
  | RawTerm.listNil => none
  | RawTerm.listCons _ _ => none
  | RawTerm.listElim _ _ _ => none
  | RawTerm.optionNone => none
  | RawTerm.optionSome _ => none
  | RawTerm.optionMatch _ _ _ => none
  | RawTerm.eitherInl _ => none
  | RawTerm.eitherInr _ => none
  | RawTerm.eitherMatch _ _ _ => none
  | RawTerm.refl _ => none
  | RawTerm.idJ _ _ => none
  | RawTerm.modIntro _ => none
  | RawTerm.modElim _ => none
  | RawTerm.subsume _ => none
  | RawTerm.interval0 => none
  | RawTerm.interval1 => none
  | RawTerm.intervalOpp _ => none
  | RawTerm.intervalMeet _ _ => none
  | RawTerm.intervalJoin _ _ => none
  | RawTerm.pathLam _ => none
  | RawTerm.pathApp _ _ => none
  | RawTerm.glueIntro _ _ => none
  | RawTerm.glueElim _ => none
  | RawTerm.transp _ _ => none
  | RawTerm.hcomp _ _ => none
  | RawTerm.oeqRefl _ => none
  | RawTerm.oeqJ _ _ => none
  | RawTerm.oeqFunext _ => none
  | RawTerm.idStrictRefl _ => none
  | RawTerm.idStrictRec _ _ => none
  | RawTerm.equivIntro _ _ => none
  | RawTerm.equivApp _ _ => none
  | RawTerm.refineIntro _ _ => none
  | RawTerm.refineElim _ => none
  | RawTerm.recordIntro _ => none
  | RawTerm.recordProj _ => none
  | RawTerm.codataUnfold _ _ => none
  | RawTerm.codataDest _ => none
  | RawTerm.sessionSend _ _ => none
  | RawTerm.sessionRecv _ => none
  | RawTerm.effectPerform _ _ => none
  | RawTerm.universeCode _ => none
  | RawTerm.arrowCode _ _ => none
  | RawTerm.sigmaTyCode _ _ => none
  | RawTerm.productCode _ _ => none
  | RawTerm.sumCode _ _ => none
  | RawTerm.listCode _ => none
  | RawTerm.optionCode _ => none
  | RawTerm.eitherCode _ _ => none
  | RawTerm.idCode _ _ _ => none
  | RawTerm.equivCode _ _ => none
  | RawTerm.cumulUpMarker _ => none
  | RawTerm.uaToEquiv _ => none
  | RawTerm.equivApply _ _ => none
  | RawTerm.pathCompose _ _ => none
  | RawTerm.idToEquiv _ => none
  | RawTerm.oeqTrans _ _ => none
  | RawTerm.equivCompose _ _ => none

end LeanFX2
