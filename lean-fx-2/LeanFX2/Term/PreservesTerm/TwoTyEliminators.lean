import LeanFX2.Term.PreservesTerm.EliminatorConstantMotive
import LeanFX2.Term.PreservesTerm.EliminatorShallowBeta

/-! # LeanFX2.Term.PreservesTerm.TwoTyEliminators

Tier 3 eliminator lifts re-expressed at the two-Ty existential.
Wraps the fixed-Ty companions from `EliminatorConstantMotive`
(natElim, natRec, listElim, optionMatch, eitherMatch) and
`EliminatorShallowBeta` (modElim, recordProj, refineElim,
glueElim, codataDest), exposing the target Ty as part of the
witness for headline assembly.

Closed out by the project-wide coverage status block: 70 of 75
Term ctors ship full lifts; the remaining 5 ctors (pair,
appPi-full, transp-full, funextRefl, funextIntroHet) are
deferred per the walls catalogued in `PreservesTerm.lean`.

## Root status

Zero-axiom; carved from `Term/PreservesTerm.lean`. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}


/-- **Tier 3 — Term.natElim at two-Ty.** -/
theorem RawStep.par.lift_full_natElim
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context Ty.nat targetRawIH,
        Step.par scrutinee scrutTarget)
    (zeroLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par zeroRaw targetRawIH →
      ∃ zeroTarget : Term context motiveType targetRawIH,
        Step.par zeroBranch zeroTarget)
    (succLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par succRaw targetRawIH →
      ∃ succTarget : Term context (Ty.arrow Ty.nat motiveType) targetRawIH,
        Step.par succBranch succTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.natElim scrutineeRaw zeroRaw succRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.natElim scrutinee zeroBranch succBranch) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_natElim scrutinee zeroBranch succBranch
                             scrutLift zeroLift succLift rawStep
  exact ⟨motiveType, target, step⟩

/-- **Tier 3 — Term.natRec at two-Ty.** -/
theorem RawStep.par.lift_full_natRec
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context Ty.nat targetRawIH,
        Step.par scrutinee scrutTarget)
    (zeroLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par zeroRaw targetRawIH →
      ∃ zeroTarget : Term context motiveType targetRawIH,
        Step.par zeroBranch zeroTarget)
    (succLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par succRaw targetRawIH →
      ∃ succTarget :
          Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
                       targetRawIH,
        Step.par succBranch succTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.natRec scrutineeRaw zeroRaw succRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.natRec scrutinee zeroBranch succBranch) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_natRec scrutinee zeroBranch succBranch
                            scrutLift zeroLift succLift rawStep
  exact ⟨motiveType, target, step⟩

/-- **Tier 3 — Term.listElim at two-Ty.** -/
theorem RawStep.par.lift_full_listElim
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    (scrutinee : Term context (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context
        (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
        consRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context (Ty.listType elementType) targetRawIH,
        Step.par scrutinee scrutTarget)
    (nilLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par nilRaw targetRawIH →
      ∃ nilTarget : Term context motiveType targetRawIH,
        Step.par nilBranch nilTarget)
    (consLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par consRaw targetRawIH →
      ∃ consTarget :
          Term context
            (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
            targetRawIH,
        Step.par consBranch consTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.listElim scrutineeRaw nilRaw consRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.listElim scrutinee nilBranch consBranch) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_listElim scrutinee nilBranch consBranch
                              scrutLift nilLift consLift rawStep
  exact ⟨motiveType, target, step⟩

/-- **Tier 3 — Term.optionMatch at two-Ty.** -/
theorem RawStep.par.lift_full_optionMatch
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    (scrutinee : Term context (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context (Ty.optionType elementType) targetRawIH,
        Step.par scrutinee scrutTarget)
    (noneLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par noneRaw targetRawIH →
      ∃ noneTarget : Term context motiveType targetRawIH,
        Step.par noneBranch noneTarget)
    (someLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par someRaw targetRawIH →
      ∃ someTarget :
          Term context (Ty.arrow elementType motiveType) targetRawIH,
        Step.par someBranch someTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par
        (RawTerm.optionMatch scrutineeRaw noneRaw someRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.optionMatch scrutinee noneBranch someBranch) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_optionMatch scrutinee noneBranch someBranch
                                 scrutLift noneLift someLift rawStep
  exact ⟨motiveType, target, step⟩

/-- **Tier 3 — Term.eitherMatch at two-Ty.** -/
theorem RawStep.par.lift_full_eitherMatch
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    (scrutinee : Term context (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget :
          Term context (Ty.eitherType leftType rightType) targetRawIH,
        Step.par scrutinee scrutTarget)
    (leftLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par leftRaw targetRawIH →
      ∃ leftTarget :
          Term context (Ty.arrow leftType motiveType) targetRawIH,
        Step.par leftBranch leftTarget)
    (rightLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par rightRaw targetRawIH →
      ∃ rightTarget :
          Term context (Ty.arrow rightType motiveType) targetRawIH,
        Step.par rightBranch rightTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par
        (RawTerm.eitherMatch scrutineeRaw leftRaw rightRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.eitherMatch scrutinee leftBranch rightBranch) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_eitherMatch scrutinee leftBranch rightBranch
                                 scrutLift leftLift rightLift rawStep
  exact ⟨motiveType, target, step⟩

/-- **Tier 3 — Term.modElim at two-Ty.** -/
theorem RawStep.par.lift_full_modElim
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par innerRaw targetRawIH →
      ∃ innerTarget : Term context innerType targetRawIH,
        Step.par innerTerm innerTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.modElim innerRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.modElim innerTerm) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_modElim innerTerm innerLift rawStep
  exact ⟨innerType, target, step⟩

/-- **Tier 3 — Term.recordProj at two-Ty.** -/
theorem RawStep.par.lift_full_recordProj
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    (recordValue : Term context (Ty.record singleFieldType) recordRaw)
    (recordLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par recordRaw targetRawIH →
      ∃ recordTarget :
          Term context (Ty.record singleFieldType) targetRawIH,
        Step.par recordValue recordTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.recordProj recordRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.recordProj recordValue) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_recordProj recordValue recordLift rawStep
  exact ⟨singleFieldType, target, step⟩

/-- **Tier 3 — Term.refineElim at two-Ty.** -/
theorem RawStep.par.lift_full_refineElim
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    (refinedValue : Term context (Ty.refine baseType predicate) refinedRaw)
    (refinedLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par refinedRaw targetRawIH →
      ∃ refinedTarget :
          Term context (Ty.refine baseType predicate) targetRawIH,
        Step.par refinedValue refinedTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.refineElim refinedRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.refineElim refinedValue) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_refineElim refinedValue refinedLift rawStep
  exact ⟨baseType, target, step⟩

/-- **Tier 3 — Term.glueElim at two-Ty.** -/
theorem RawStep.par.lift_full_glueElim
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {gluedRaw : RawTerm scope}
    (gluedValue : Term context (Ty.glue baseType boundaryWitness) gluedRaw)
    (gluedLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par gluedRaw targetRawIH →
      ∃ gluedTarget :
          Term context (Ty.glue baseType boundaryWitness) targetRawIH,
        Step.par gluedValue gluedTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.glueElim gluedRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.glueElim modeIsUnivalent gluedValue) targetTerm := by
  obtain ⟨target, step⟩ :=
    RawStep.par.lift_glueElim modeIsUnivalent gluedValue gluedLift rawStep
  exact ⟨baseType, target, step⟩

/-- **Tier 3 — Term.codataDest at two-Ty.** -/
theorem RawStep.par.lift_full_codataDest
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    (codataValue : Term context (Ty.codata stateType outputType) codataRaw)
    (codataLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par codataRaw targetRawIH →
      ∃ codataTarget :
          Term context (Ty.codata stateType outputType) targetRawIH,
        Step.par codataValue codataTarget)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.codataDest codataRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par (Term.codataDest codataValue) targetTerm := by
  obtain ⟨target, step⟩ := RawStep.par.lift_codataDest codataValue codataLift rawStep
  exact ⟨outputType, target, step⟩

/-! ## Coverage status (post-juggernaut Phase 5 / #1590-CORE)

**Total Term ctors**: 75
**Full lifts shipped**: 70 (93%)
**Deferred**: 5 (pair, appPi, transp, funextRefl, funextIntroHet)

### Shipped this juggernaut (Phase 5)

**Type-code ctors via free-the-type-via-suffices + Ty.universe alignment**
(10 ctors): arrowCode, piTyCode, sigmaTyCode, productCode, sumCode,
listCode, optionCode, eitherCode, idCode, equivCode.

**Schematic-payload value ctors with new typed cong rules**:
- refl (via Step.par.reflCong, suffices destructor)
- equivReflId (atom-shaped — only refl applies)
- equivReflIdAtId (atom-shaped — only refl applies)

**Heterogeneous-carrier ctors**:
- uaIntroHet (single typed equivWitness child)
- equivIntroHet (forward + backward typed children, leftInv/rightInv
  via fresh-supplier parameters)

### Shipped in prior juggernauts (Phases 1-4)

**Atoms (Tier 0)** (9): unit, boolTrue, boolFalse, natZero, listNil,
optionNone, interval0, interval1, var.

**Unary cong (Tier 1)** (9): natSucc, optionSome, eitherInl, eitherInr,
intervalOpp, modIntro, subsume, recordIntro, sessionRecv.

**Binders (Tier 1)** (3): lam, lamPi, pathLam.

**Binary cong (Tier 2)** (10): intervalMeet, intervalJoin, glueIntro,
hcomp, codataUnfold, sessionSend, listCons, equivApp, refineIntro,
effectPerform.

**Eliminators (Tier 3)** (10): natElim, natRec, listElim, optionMatch,
eitherMatch, modElim, recordProj, refineElim, glueElim, codataDest.

**β cast wall demolished (full lifts)** (4): app, pathApp, fst, snd.

**Type-changing iota** (3): idJ, idStrictRec, boolElim.

**Schematic-payload value (oldcong)** (3): oeqRefl, idStrictRefl, oeqFunext.

**Universe / cumul** (2): universeCode, cumulUp.

### Deferred (5 ctors)

* **pair**: heterogeneous Step.par signature; second has type
  `secondType.subst0 firstType firstRaw` which CHANGES when firstRaw
  steps.  IH structure needs extension to allow target-type-changing
  second IH.
* **appPi (full)**: β cast wall same as `app`; cong-only variant
  shipped.  Full version has additional dep-elim wall via piTy
  vs funextRefl shape ambiguity.
* **transp (full)**: typed `transpReflBetaDeep` Step.par ctor doesn't
  exist; cong-only variant shipped.
* **funextRefl**: raw form `RawTerm.lam (RawTerm.refl applyRaw)`
  shape-collides with Term.lamPi (Term.refl ...) at identical
  (Ty.piTy, raw) signatures.
* **funextIntroHet**: raw form `RawTerm.lam (RawTerm.refl applyARaw)`
  shape-collides with Term.funextReflAtId at identical
  (Ty.id (Ty.arrow ...), raw) signatures.  An earlier draft of
  `lift_full_funextReflAtId` was found to LEAK 2 axioms (Quot.sound,
  propext) via the `cases genericTerm` + `all_goals first | nomatch`
  pattern; hence the entire family is deferred to a redesigned
  ctor-by-ctor casesOn dispatch.

### Headline assembly status

The full `Term.preserves` over Term induction remains deferred — its
assembly requires:
1. Resolving the 5 deferred ctors above.
2. A unified IH shape that handles atoms (0 IHs), unary (1 IH),
   binary (2 IHs), eliminators (3+ IHs).

What's shipped is the 70 compositional bricks, each with `#assert_no_axioms`
verified or smoke-audited zero-axiom (see `Smoke/AuditPhase1590CorePreservesTerm.lean`).
When the full headline is assembled, child IHs are supplied by Term
induction. -/

end LeanFX2
