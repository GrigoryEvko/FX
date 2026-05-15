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

/-- Soundness for `matchTranspPiBetaShape?`: a successful recognizer
hit witnesses that `pathBody` has exactly the CCHM transpPi β shape,
with the domain expressed as a weaken of `innerDomain`.

The proof case-analyzes `pathBody`.  Only the `piTyCode` arm permits
a `some _` return (all 72 other arms return `none` definitionally, so
their `success` hypotheses contradict `none = some _` via constructor
injectivity).  Inside the `piTyCode` arm, we further case on
`unweaken? domainCode`: success path extracts `inner` via `injection`
and uses `unweaken?_imp_weaken` to recover `domainCode =
innerDomain.weaken`.

Consumed by future Phase F `cdTranspCase` extension to bridge the
recognizer output to the `transpPiBetaContractum` builder. -/
theorem RawTerm.matchTranspPiBetaShape?_imp_piTyCode_weaken {scope : Nat}
    (pathBody : RawTerm (scope + 1)) (innerDomain : RawTerm scope)
    (codomainCode : RawTerm (scope + 2))
    (success : RawTerm.matchTranspPiBetaShape? pathBody =
                 some (innerDomain, codomainCode)) :
    pathBody = RawTerm.piTyCode innerDomain.weaken codomainCode := by
  cases pathBody with
  | piTyCode domainCode codomainCode' =>
      cases unweakenResult : RawTerm.unweaken? domainCode with
      | some inner =>
          have stepEq :
              RawTerm.matchTranspPiBetaShape?
                  (RawTerm.piTyCode domainCode codomainCode') =
                some (inner, codomainCode') := by
            show (match RawTerm.unweaken? domainCode with
                  | some innerInner => some (innerInner, codomainCode')
                  | none => none) = some (inner, codomainCode')
            rw [unweakenResult]
          rw [stepEq] at success
          injection success with somePayload
          injection somePayload with innerEq codomainEq
          subst innerEq
          subst codomainEq
          exact congrArg (RawTerm.piTyCode · codomainCode')
                  (RawTerm.unweaken?_imp_weaken domainCode inner unweakenResult)
      | none =>
          have stepEq :
              RawTerm.matchTranspPiBetaShape?
                  (RawTerm.piTyCode domainCode codomainCode') = none := by
            show (match RawTerm.unweaken? domainCode with
                  | some innerInner => some (innerInner, codomainCode')
                  | none => none) = none
            rw [unweakenResult]
          rw [stepEq] at success
          cases success
  | var _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | unit =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | lam _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | app _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | pair _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | fst _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | snd _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | boolTrue =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | boolFalse =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | boolElim _ _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | natZero =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | natSucc _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | natElim _ _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | natRec _ _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | listNil =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | listCons _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | listElim _ _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | optionNone =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | optionSome _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | optionMatch _ _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | eitherInl _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | eitherInr _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | eitherMatch _ _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | refl _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | idJ _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | modIntro _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | modElim _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | subsume _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | interval0 =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | interval1 =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | intervalOpp _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | intervalMeet _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | intervalJoin _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | pathLam _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | pathApp _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | glueIntro _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | glueElim _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | transp _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | hcomp _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | oeqRefl _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | oeqJ _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | oeqFunext _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | idStrictRefl _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | idStrictRec _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | equivIntro _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | equivApp _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | refineIntro _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | refineElim _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | recordIntro _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | recordProj _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | codataUnfold _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | codataDest _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | sessionSend _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | sessionRecv _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | effectPerform _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | universeCode _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | arrowCode _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | sigmaTyCode _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | productCode _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | sumCode _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | listCode _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | optionCode _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | eitherCode _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | idCode _ _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | equivCode _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | cumulUpMarker _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | uaToEquiv _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | equivApply _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | pathCompose _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | idToEquiv _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | oeqTrans _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success
  | equivCompose _ _ =>
      simp only [RawTerm.matchTranspPiBetaShape?] at success
      cases success

end LeanFX2
