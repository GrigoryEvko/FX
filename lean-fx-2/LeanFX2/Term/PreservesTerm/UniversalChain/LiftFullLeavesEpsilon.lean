import LeanFX2.Term.PreservesTerm.UniversalChain.LiftFullTerm
import LeanFX2.Term.PreservesTerm.UniversalChain.LiftFullLeavesAlpha

/-! # LeanFX2.Term.PreservesTerm.UniversalChain.LiftFullLeavesEpsilon

Witness-builder layer for the CONVTRANS-C universal chain close-out
(#2070 — "drop the `DispatchAtom` restriction"), extending the
constructible fragment shipped in
`UniversalChain/LiftFullLeavesAlpha.lean`.

Alpha covered the closed-leaf atoms (`unit`/`boolTrue`/…/`var`), the
recursive interval/list/option/either/record value ctors, and the
canonical nat-literal totality.  This file adds the remaining
*constructible* `DispatchAtom` arms — those whose witness needs only

* nothing (schematic-leaf and type-code arms carry raw payloads and
  level data, no typed children, no `IsClosedTy`, no baked `*Lift`
  callback), or
* sub-`DispatchAtom` witnesses plus `IsClosedTy` facts on closed
  types (the recursive eliminator / modal-scaffold arms).

It deliberately SKIPS the data-carrying arms (`idJ`, `oeqJ`,
`idStrictRec`, `fst`, `snd`, `refineElim`, `glueElim`, `pathApp`,
`appPi`, `sessionRecv`, `sessionSend`, `effectPerform`, `oeqFunext`,
`uaToEquiv`, `pair`, `hcomp`, `equivApply`, `transp`, `hcompPath`,
`uaIntroHet`, `equivIntroHet`): each of those bakes an irreducible
caller-supplied `*Lift`/retarget callback into its `DispatchAtom`
arm, so no total builder can construct them.

Coverage shipped here:

* **Schematic-value builders** (4) — `ofRefl`, `ofOeqRefl`,
  `ofEquivReflId`, `ofEquivReflIdAtId`: a carrier `Ty` plus raw
  witnesses, no typed children.
* **Schematic-leaf builders** (3) — `ofFunextRefl`,
  `ofFunextReflAtId`, `ofFunextIntroHet`: raw binder/refl payloads
  only.
* **Type-code builders** (11) — `ofUniverseCode`, `ofArrowCode`,
  `ofPiTyCode`, `ofSigmaTyCode`, `ofProductCode`, `ofSumCode`,
  `ofListCode`, `ofOptionCode`, `ofEitherCode`, `ofIdCode`,
  `ofEquivCode`: universe-code values whose raw payloads are
  schematic codes with no typed children.
* **Modal-scaffold builders** (3) — `ofModIntro`, `ofModElim`,
  `ofSubsume`: single closed-inner child threaded recursively.
* **Recursive eliminator builders** (5) — `ofNatElim`, `ofNatRec`,
  `ofListElim`, `ofOptionMatch`, `ofEitherMatch`: scrutinee + branch
  children threaded with the matching `IsClosedTy` witnesses.
* **Gate-free universal lifts** — one per schematic builder above
  (no `DispatchAtom` hypothesis exposed), via
  `RawStep.par.lift_full_term`.
* **Canonical interval-literal totality** — `IntervalExpr`,
  `rawIntervalLiteral`, `intervalLiteral`,
  `intervalLiteral_isDispatchable`, and
  `lift_universal_intervalLiteral`: a whole interval-lattice value
  family proven dispatchable by structural recursion on a syntactic
  descriptor, mirroring Alpha's `natLiteral_isDispatchable`.

Every declaration is verified zero-axiom by the matching
`#print axioms` line in `Smoke/AuditUniversalChainEpsilon.lean`.
-/

namespace LeanFX2

/-! ## Schematic-value `DispatchAtom` builders

The refl-style value ctors carry a carrier `Ty` and raw witnesses but
have NO typed children, so the builder is a direct re-naming of the
matching `DispatchAtom` arm. -/

/-- `Term.refl` is dispatchable at any carrier and witness. -/
theorem DispatchAtom.ofRefl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    DispatchAtom (Term.refl (context := context) carrier rawWitness
                  : Term context (Ty.id carrier rawWitness rawWitness)
                                 (RawTerm.refl rawWitness)) :=
  DispatchAtom.refl carrier rawWitness

/-- `Term.oeqRefl` is dispatchable at any carrier and witness. -/
theorem DispatchAtom.ofOeqRefl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    DispatchAtom (Term.oeqRefl (context := context) carrier rawWitness
                  : Term context (Ty.oeq carrier rawWitness rawWitness)
                                 (RawTerm.oeqRefl rawWitness)) :=
  DispatchAtom.oeqRefl carrier rawWitness

/-- `Term.equivReflId` is dispatchable at any carrier. -/
theorem DispatchAtom.ofEquivReflId
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (carrier : Ty level scope) :
    DispatchAtom (Term.equivReflId (context := context) carrier
                  : Term context (Ty.equiv carrier carrier)
                                 (RawTerm.equivIntro
                                   (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
                                   (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)))) :=
  DispatchAtom.equivReflId carrier

/-- `Term.equivReflIdAtId` is dispatchable at any carrier code. -/
theorem DispatchAtom.ofEquivReflIdAtId
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope) (carrierRaw : RawTerm scope) :
    DispatchAtom (Term.equivReflIdAtId (context := context)
                                        innerLevel innerLevelLt
                                        carrier carrierRaw
                  : Term context
                      (Ty.id (Ty.universe innerLevel innerLevelLt)
                             carrierRaw carrierRaw)
                      (RawTerm.equivIntro
                        (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
                        (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)))) :=
  DispatchAtom.equivReflIdAtId innerLevel innerLevelLt carrier carrierRaw

/-! ## Schematic-leaf `DispatchAtom` builders

The universe-funext rfl-witness leaves carry only raw binder/refl
payloads — no typed children, no IH-closure data. -/

/-- `Term.funextRefl` is dispatchable at any domain/codomain and apply
payload. -/
theorem DispatchAtom.ofFunextRefl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    DispatchAtom (Term.funextRefl (context := context)
                                   domainType codomainType applyRaw
                  : Term context
                      (funextReflType domainType codomainType applyRaw)
                      (RawTerm.lam (RawTerm.refl applyRaw))) :=
  DispatchAtom.funextRefl domainType codomainType applyRaw

/-- `Term.funextReflAtId` is dispatchable at any domain/codomain and
apply payload. -/
theorem DispatchAtom.ofFunextReflAtId
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    DispatchAtom (Term.funextReflAtId (context := context)
                                       domainType codomainType applyRaw
                  : Term context
                      (Ty.id (Ty.arrow domainType codomainType)
                             (RawTerm.lam (RawTerm.refl applyRaw))
                             (RawTerm.lam (RawTerm.refl applyRaw)))
                      (RawTerm.lam (RawTerm.refl applyRaw))) :=
  DispatchAtom.funextReflAtId domainType codomainType applyRaw

/-- `Term.funextIntroHet` is dispatchable at any domain/codomain and
two apply payloads. -/
theorem DispatchAtom.ofFunextIntroHet
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyARaw applyBRaw : RawTerm (scope + 1)) :
    DispatchAtom (Term.funextIntroHet (context := context)
                                       domainType codomainType
                                       applyARaw applyBRaw
                  : Term context
                      (Ty.id (Ty.arrow domainType codomainType)
                             (RawTerm.lam applyARaw)
                             (RawTerm.lam applyBRaw))
                      (RawTerm.lam (RawTerm.refl applyARaw))) :=
  DispatchAtom.funextIntroHet domainType codomainType applyARaw applyBRaw

/-! ## Type-code `DispatchAtom` builders

Each universe-code value lives at `Ty.universe outerLevel levelLe` and
carries only schematic raw codes plus level data — no typed children,
no `IsClosedTy`, no baked callback.  The builders re-name the matching
`DispatchAtom` arm directly. -/

/-- `Term.universeCode` is dispatchable. -/
theorem DispatchAtom.ofUniverseCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    DispatchAtom (Term.universeCode (context := context) innerLevel outerLevel
                                     cumulOk levelLe
                  : Term context (Ty.universe outerLevel levelLe)
                                 (RawTerm.universeCode innerLevel.toNat)) :=
  DispatchAtom.universeCode innerLevel outerLevel cumulOk levelLe

/-- `Term.arrowCode` is dispatchable. -/
theorem DispatchAtom.ofArrowCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm scope) :
    DispatchAtom (Term.arrowCode (context := context) outerLevel levelLe
                                  domainCodeRaw codomainCodeRaw
                  : Term context (Ty.universe outerLevel levelLe)
                                 (RawTerm.arrowCode domainCodeRaw codomainCodeRaw)) :=
  DispatchAtom.arrowCode outerLevel levelLe domainCodeRaw codomainCodeRaw

/-- `Term.piTyCode` is dispatchable. -/
theorem DispatchAtom.ofPiTyCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1)) :
    DispatchAtom (Term.piTyCode (context := context) outerLevel levelLe
                                 domainCodeRaw codomainCodeRaw
                  : Term context (Ty.universe outerLevel levelLe)
                                 (RawTerm.piTyCode domainCodeRaw codomainCodeRaw)) :=
  DispatchAtom.piTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw

/-- `Term.sigmaTyCode` is dispatchable. -/
theorem DispatchAtom.ofSigmaTyCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1)) :
    DispatchAtom (Term.sigmaTyCode (context := context) outerLevel levelLe
                                    domainCodeRaw codomainCodeRaw
                  : Term context (Ty.universe outerLevel levelLe)
                                 (RawTerm.sigmaTyCode domainCodeRaw codomainCodeRaw)) :=
  DispatchAtom.sigmaTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw

/-- `Term.productCode` is dispatchable. -/
theorem DispatchAtom.ofProductCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm scope) :
    DispatchAtom (Term.productCode (context := context) outerLevel levelLe
                                    firstCodeRaw secondCodeRaw
                  : Term context (Ty.universe outerLevel levelLe)
                                 (RawTerm.productCode firstCodeRaw secondCodeRaw)) :=
  DispatchAtom.productCode outerLevel levelLe firstCodeRaw secondCodeRaw

/-- `Term.sumCode` is dispatchable. -/
theorem DispatchAtom.ofSumCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope) :
    DispatchAtom (Term.sumCode (context := context) outerLevel levelLe
                                leftCodeRaw rightCodeRaw
                  : Term context (Ty.universe outerLevel levelLe)
                                 (RawTerm.sumCode leftCodeRaw rightCodeRaw)) :=
  DispatchAtom.sumCode outerLevel levelLe leftCodeRaw rightCodeRaw

/-- `Term.listCode` is dispatchable. -/
theorem DispatchAtom.ofListCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope) :
    DispatchAtom (Term.listCode (context := context) outerLevel levelLe
                                 elementCodeRaw
                  : Term context (Ty.universe outerLevel levelLe)
                                 (RawTerm.listCode elementCodeRaw)) :=
  DispatchAtom.listCode outerLevel levelLe elementCodeRaw

/-- `Term.optionCode` is dispatchable. -/
theorem DispatchAtom.ofOptionCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope) :
    DispatchAtom (Term.optionCode (context := context) outerLevel levelLe
                                   elementCodeRaw
                  : Term context (Ty.universe outerLevel levelLe)
                                 (RawTerm.optionCode elementCodeRaw)) :=
  DispatchAtom.optionCode outerLevel levelLe elementCodeRaw

/-- `Term.eitherCode` is dispatchable. -/
theorem DispatchAtom.ofEitherCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope) :
    DispatchAtom (Term.eitherCode (context := context) outerLevel levelLe
                                   leftCodeRaw rightCodeRaw
                  : Term context (Ty.universe outerLevel levelLe)
                                 (RawTerm.eitherCode leftCodeRaw rightCodeRaw)) :=
  DispatchAtom.eitherCode outerLevel levelLe leftCodeRaw rightCodeRaw

/-- `Term.idCode` is dispatchable. -/
theorem DispatchAtom.ofIdCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm scope) :
    DispatchAtom (Term.idCode (context := context) outerLevel levelLe
                               typeCodeRaw leftRaw rightRaw
                  : Term context (Ty.universe outerLevel levelLe)
                                 (RawTerm.idCode typeCodeRaw leftRaw rightRaw)) :=
  DispatchAtom.idCode outerLevel levelLe typeCodeRaw leftRaw rightRaw

/-- `Term.equivCode` is dispatchable. -/
theorem DispatchAtom.ofEquivCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope) :
    DispatchAtom (Term.equivCode (context := context) outerLevel levelLe
                                  leftTypeCodeRaw rightTypeCodeRaw
                  : Term context (Ty.universe outerLevel levelLe)
                                 (RawTerm.equivCode leftTypeCodeRaw rightTypeCodeRaw)) :=
  DispatchAtom.equivCode outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw

/-! ## Modal-scaffold `DispatchAtom` builders

The Layer-1 modal-intro/modal-elim/subsume scaffolds preserve the
inner type, so a closed-inner witness threads through directly. -/

/-- `Term.modIntro` is dispatchable when its inner value is and the
inner type is closed. -/
theorem DispatchAtom.ofModIntro
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {innerType : Ty level scope}
    (innerClosed : IsClosedTy innerType)
    {innerRaw : RawTerm scope}
    {innerTerm : Term context innerType innerRaw}
    (innerDispatch : DispatchAtom innerTerm) :
    DispatchAtom (Term.modIntro (context := context) innerTerm
                  : Term context innerType (RawTerm.modIntro innerRaw)) :=
  DispatchAtom.modIntro innerClosed innerTerm innerDispatch

/-- `Term.modElim` is dispatchable when its inner value is and the
inner type is closed. -/
theorem DispatchAtom.ofModElim
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {innerType : Ty level scope}
    (innerClosed : IsClosedTy innerType)
    {innerRaw : RawTerm scope}
    {innerTerm : Term context innerType innerRaw}
    (innerDispatch : DispatchAtom innerTerm) :
    DispatchAtom (Term.modElim (context := context) innerTerm
                  : Term context innerType (RawTerm.modElim innerRaw)) :=
  DispatchAtom.modElim innerClosed innerTerm innerDispatch

/-- `Term.subsume` is dispatchable when its inner value is and the
inner type is closed. -/
theorem DispatchAtom.ofSubsume
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {innerType : Ty level scope}
    (innerClosed : IsClosedTy innerType)
    {innerRaw : RawTerm scope}
    {innerTerm : Term context innerType innerRaw}
    (innerDispatch : DispatchAtom innerTerm) :
    DispatchAtom (Term.subsume (context := context) innerTerm
                  : Term context innerType (RawTerm.subsume innerRaw)) :=
  DispatchAtom.subsume innerClosed innerTerm innerDispatch

/-! ## Recursive eliminator `DispatchAtom` builders

The non-dependent-motive eliminators are dispatchable when scrutinee
and every branch are dispatchable and the relevant types are closed. -/

/-- `Term.natElim` is dispatchable at a closed motive when its
scrutinee, zero branch, and successor branch are dispatchable. -/
theorem DispatchAtom.ofNatElim
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    (motiveClosed : IsClosedTy motiveType)
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term context Ty.nat scrutineeRaw}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw}
    (scrutDispatch : DispatchAtom scrutinee)
    (zeroDispatch : DispatchAtom zeroBranch)
    (succDispatch : DispatchAtom succBranch) :
    DispatchAtom (Term.natElim (context := context) scrutinee
                                zeroBranch succBranch
                  : Term context motiveType
                                 (RawTerm.natElim scrutineeRaw zeroRaw succRaw)) :=
  DispatchAtom.natElim motiveClosed scrutinee zeroBranch succBranch
                       scrutDispatch zeroDispatch succDispatch

/-- `Term.natRec` is dispatchable at a closed motive when its
scrutinee, zero branch, and successor branch are dispatchable. -/
theorem DispatchAtom.ofNatRec
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    (motiveClosed : IsClosedTy motiveType)
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term context Ty.nat scrutineeRaw}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw}
    (scrutDispatch : DispatchAtom scrutinee)
    (zeroDispatch : DispatchAtom zeroBranch)
    (succDispatch : DispatchAtom succBranch) :
    DispatchAtom (Term.natRec (context := context) scrutinee
                               zeroBranch succBranch
                  : Term context motiveType
                                 (RawTerm.natRec scrutineeRaw zeroRaw succRaw)) :=
  DispatchAtom.natRec motiveClosed scrutinee zeroBranch succBranch
                      scrutDispatch zeroDispatch succDispatch

/-- `Term.listElim` is dispatchable at closed element/motive types when
its scrutinee, nil branch, and cons branch are dispatchable. -/
theorem DispatchAtom.ofListElim
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    (elementClosed : IsClosedTy elementType)
    (motiveClosed : IsClosedTy motiveType)
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    {scrutinee : Term context (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term context motiveType nilRaw}
    {consBranch :
      Term context
        (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
        consRaw}
    (scrutDispatch : DispatchAtom scrutinee)
    (nilDispatch : DispatchAtom nilBranch)
    (consDispatch : DispatchAtom consBranch) :
    DispatchAtom (Term.listElim (context := context) scrutinee
                                 nilBranch consBranch
                  : Term context motiveType
                                 (RawTerm.listElim scrutineeRaw nilRaw consRaw)) :=
  DispatchAtom.listElim elementClosed motiveClosed scrutinee nilBranch consBranch
                        scrutDispatch nilDispatch consDispatch

/-- `Term.optionMatch` is dispatchable at closed element/motive types
when its scrutinee, none branch, and some branch are dispatchable. -/
theorem DispatchAtom.ofOptionMatch
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    (elementClosed : IsClosedTy elementType)
    (motiveClosed : IsClosedTy motiveType)
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    {scrutinee : Term context (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term context motiveType noneRaw}
    {someBranch : Term context (Ty.arrow elementType motiveType) someRaw}
    (scrutDispatch : DispatchAtom scrutinee)
    (noneDispatch : DispatchAtom noneBranch)
    (someDispatch : DispatchAtom someBranch) :
    DispatchAtom (Term.optionMatch (context := context) scrutinee
                                    noneBranch someBranch
                  : Term context motiveType
                                 (RawTerm.optionMatch scrutineeRaw noneRaw someRaw)) :=
  DispatchAtom.optionMatch elementClosed motiveClosed scrutinee
                           noneBranch someBranch
                           scrutDispatch noneDispatch someDispatch

/-- `Term.eitherMatch` is dispatchable at closed left/right/motive types
when its scrutinee, left branch, and right branch are dispatchable. -/
theorem DispatchAtom.ofEitherMatch
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    (leftClosed : IsClosedTy leftType)
    (rightClosed : IsClosedTy rightType)
    (motiveClosed : IsClosedTy motiveType)
    {scrutineeRaw leftBranchRaw rightBranchRaw : RawTerm scope}
    {scrutinee : Term context (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch : Term context (Ty.arrow leftType motiveType) leftBranchRaw}
    {rightBranch : Term context (Ty.arrow rightType motiveType) rightBranchRaw}
    (scrutDispatch : DispatchAtom scrutinee)
    (leftDispatch : DispatchAtom leftBranch)
    (rightDispatch : DispatchAtom rightBranch) :
    DispatchAtom (Term.eitherMatch (context := context) scrutinee
                                    leftBranch rightBranch
                  : Term context motiveType
                                 (RawTerm.eitherMatch scrutineeRaw
                                                       leftBranchRaw
                                                       rightBranchRaw)) :=
  DispatchAtom.eitherMatch leftClosed rightClosed motiveClosed scrutinee
                           leftBranch rightBranch
                           scrutDispatch leftDispatch rightDispatch

/-! ## Derived universal lifts for the schematic builders

Combining a schematic builder with the dispatcher gives a
`StepParExists` for the source term directly — the close-out shape
that does not expose the `DispatchAtom` hypothesis.  These cover the
zero-child arms, whose lift threads no IH callback. -/

/-- Universal lift for `Term.refl`. -/
theorem RawStep.par.lift_universal_refl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (carrier : Ty level scope) (rawWitness : RawTerm scope)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.refl rawWitness) targetRaw) :
    StepParExists (Term.refl (context := context) carrier rawWitness
                   : Term context (Ty.id carrier rawWitness rawWitness)
                                  (RawTerm.refl rawWitness))
                  targetRaw :=
  RawStep.par.lift_full_term (DispatchAtom.ofRefl carrier rawWitness) rawStep

/-- Universal lift for `Term.oeqRefl`. -/
theorem RawStep.par.lift_universal_oeqRefl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (carrier : Ty level scope) (rawWitness : RawTerm scope)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.oeqRefl rawWitness) targetRaw) :
    StepParExists (Term.oeqRefl (context := context) carrier rawWitness
                   : Term context (Ty.oeq carrier rawWitness rawWitness)
                                  (RawTerm.oeqRefl rawWitness))
                  targetRaw :=
  RawStep.par.lift_full_term (DispatchAtom.ofOeqRefl carrier rawWitness) rawStep

/-- Universal lift for `Term.equivReflId`. -/
theorem RawStep.par.lift_universal_equivReflId
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (carrier : Ty level scope)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par
      (RawTerm.equivIntro
        (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
        (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))) targetRaw) :
    StepParExists (Term.equivReflId (context := context) carrier
                   : Term context (Ty.equiv carrier carrier)
                                  (RawTerm.equivIntro
                                    (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
                                    (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))))
                  targetRaw :=
  RawStep.par.lift_full_term (DispatchAtom.ofEquivReflId carrier) rawStep

/-- Universal lift for `Term.equivReflIdAtId`. -/
theorem RawStep.par.lift_universal_equivReflIdAtId
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope) (carrierRaw : RawTerm scope)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par
      (RawTerm.equivIntro
        (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
        (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))) targetRaw) :
    StepParExists (Term.equivReflIdAtId (context := context)
                                         innerLevel innerLevelLt carrier carrierRaw
                   : Term context
                       (Ty.id (Ty.universe innerLevel innerLevelLt)
                              carrierRaw carrierRaw)
                       (RawTerm.equivIntro
                         (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
                         (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))))
                  targetRaw :=
  RawStep.par.lift_full_term
    (DispatchAtom.ofEquivReflIdAtId innerLevel innerLevelLt carrier carrierRaw)
    rawStep

/-- Universal lift for `Term.funextRefl`. -/
theorem RawStep.par.lift_universal_funextRefl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.lam (RawTerm.refl applyRaw)) targetRaw) :
    StepParExists (Term.funextRefl (context := context)
                                    domainType codomainType applyRaw
                   : Term context
                       (funextReflType domainType codomainType applyRaw)
                       (RawTerm.lam (RawTerm.refl applyRaw)))
                  targetRaw :=
  RawStep.par.lift_full_term
    (DispatchAtom.ofFunextRefl domainType codomainType applyRaw) rawStep

/-- Universal lift for `Term.funextReflAtId`. -/
theorem RawStep.par.lift_universal_funextReflAtId
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.lam (RawTerm.refl applyRaw)) targetRaw) :
    StepParExists (Term.funextReflAtId (context := context)
                                        domainType codomainType applyRaw
                   : Term context
                       (Ty.id (Ty.arrow domainType codomainType)
                              (RawTerm.lam (RawTerm.refl applyRaw))
                              (RawTerm.lam (RawTerm.refl applyRaw)))
                       (RawTerm.lam (RawTerm.refl applyRaw)))
                  targetRaw :=
  RawStep.par.lift_full_term
    (DispatchAtom.ofFunextReflAtId domainType codomainType applyRaw) rawStep

/-- Universal lift for `Term.funextIntroHet`. -/
theorem RawStep.par.lift_universal_funextIntroHet
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyARaw applyBRaw : RawTerm (scope + 1))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.lam (RawTerm.refl applyARaw)) targetRaw) :
    StepParExists (Term.funextIntroHet (context := context)
                                        domainType codomainType
                                        applyARaw applyBRaw
                   : Term context
                       (Ty.id (Ty.arrow domainType codomainType)
                              (RawTerm.lam applyARaw)
                              (RawTerm.lam applyBRaw))
                       (RawTerm.lam (RawTerm.refl applyARaw)))
                  targetRaw :=
  RawStep.par.lift_full_term
    (DispatchAtom.ofFunextIntroHet domainType codomainType applyARaw applyBRaw)
    rawStep

/-- Universal lift for `Term.arrowCode`. -/
theorem RawStep.par.lift_universal_arrowCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm scope)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.arrowCode domainCodeRaw codomainCodeRaw)
                           targetRaw) :
    StepParExists (Term.arrowCode (context := context) outerLevel levelLe
                                   domainCodeRaw codomainCodeRaw
                   : Term context (Ty.universe outerLevel levelLe)
                                  (RawTerm.arrowCode domainCodeRaw codomainCodeRaw))
                  targetRaw :=
  RawStep.par.lift_full_term
    (DispatchAtom.ofArrowCode outerLevel levelLe domainCodeRaw codomainCodeRaw)
    rawStep

/-- Universal lift for `Term.idCode`. -/
theorem RawStep.par.lift_universal_idCode
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm scope)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.idCode typeCodeRaw leftRaw rightRaw)
                           targetRaw) :
    StepParExists (Term.idCode (context := context) outerLevel levelLe
                                typeCodeRaw leftRaw rightRaw
                   : Term context (Ty.universe outerLevel levelLe)
                                  (RawTerm.idCode typeCodeRaw leftRaw rightRaw))
                  targetRaw :=
  RawStep.par.lift_full_term
    (DispatchAtom.ofIdCode outerLevel levelLe typeCodeRaw leftRaw rightRaw)
    rawStep

/-! ## Canonical interval-literal totality

The interval-lattice values built from `interval0`/`interval1` via
`intervalOpp`/`intervalJoin`/`intervalMeet` are all dispatchable by
construction.  `IntervalExpr` is a finite syntactic descriptor of such
a value; `intervalLiteral` realises it as a `Term` at `Ty.interval`,
and `intervalLiteral_isDispatchable` proves it dispatchable by
structural recursion on the descriptor.  This is a second totality
fragment toward #2070 — a whole constructor sub-family whose dispatch
witness is produced with no caller-supplied data, mirroring Alpha's
`natLiteral_isDispatchable`. -/

/-- Syntactic descriptor of a canonical interval-lattice value: the two
endpoints plus the unary opposite and binary meet/join operators. -/
inductive IntervalExpr : Type
  | zero
  | one
  | opp (inner : IntervalExpr)
  | meet (left right : IntervalExpr)
  | join (left right : IntervalExpr)
  deriving Repr

/-- The raw form of a canonical interval literal, matching the raw index
of `intervalLiteral`. -/
def rawIntervalLiteral {scope : Nat} : IntervalExpr → RawTerm scope
  | .zero => RawTerm.interval0
  | .one => RawTerm.interval1
  | .opp inner => RawTerm.intervalOpp (rawIntervalLiteral inner)
  | .meet left right =>
      RawTerm.intervalMeet (rawIntervalLiteral left) (rawIntervalLiteral right)
  | .join left right =>
      RawTerm.intervalJoin (rawIntervalLiteral left) (rawIntervalLiteral right)

/-- The canonical `Ty.interval` value for a descriptor, built as an
iterated lattice expression over `interval0`/`interval1`. -/
def intervalLiteral {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    (expr : IntervalExpr) →
    Term context (Ty.interval (level := level)) (rawIntervalLiteral expr)
  | .zero => Term.interval0
  | .one => Term.interval1
  | .opp inner => Term.intervalOpp (intervalLiteral inner)
  | .meet left right =>
      Term.intervalMeet (intervalLiteral left) (intervalLiteral right)
  | .join left right =>
      Term.intervalJoin (intervalLiteral left) (intervalLiteral right)

/-- Every canonical interval literal is dispatchable.  Structural
recursion on the descriptor: the endpoints are atoms, the lattice
operators thread their children's dispatch witnesses through the
recursive interval builders. -/
theorem intervalLiteral_isDispatchable
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    (expr : IntervalExpr) →
    DispatchAtom (intervalLiteral (context := context) (level := level) expr)
  | .zero => DispatchAtom.ofInterval0
  | .one => DispatchAtom.ofInterval1
  | .opp inner =>
      DispatchAtom.ofIntervalOpp (intervalLiteral_isDispatchable inner)
  | .meet left right =>
      DispatchAtom.ofIntervalMeet (intervalLiteral_isDispatchable left)
                                  (intervalLiteral_isDispatchable right)
  | .join left right =>
      DispatchAtom.ofIntervalJoin (intervalLiteral_isDispatchable left)
                                  (intervalLiteral_isDispatchable right)

/-- Universal lift for any canonical interval literal — no
`DispatchAtom` hypothesis exposed; the witness is built internally from
the descriptor. -/
theorem RawStep.par.lift_universal_intervalLiteral
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (expr : IntervalExpr)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (rawIntervalLiteral expr) targetRaw) :
    StepParExists (intervalLiteral (context := context) (level := level) expr)
                  targetRaw :=
  RawStep.par.lift_full_term (intervalLiteral_isDispatchable expr) rawStep

end LeanFX2
