import FX1Poly.Typed.GrownPinnedReflection
import FX1Poly.Typed.PlateauDescentSubstrate

/-! # FX1Poly/Typed/GuardedPinnedReflection — the SIZE-GUARDED conditional master

The conditional grown master (`GrownPinnedReflection`) with a SIZE BOUND + NORMALITY threaded
through the mutual.  This is the knot-cutting form for the plateau induction:

  * `PinnedReflectionPiElimResidualGuarded profile bound` — the piElim residual restricted to
    NORMAL applications of size within `bound`;
  * `HasTypeDescPi.pinnedReflectionGuarded` / `DescTelescopePi.pinnedReflectionTelescopeGuarded`
    — the master with `(sizeBound : subject.size ≤ bound)` and
    `(subjectNormal : isStepNormalForm subject)` hypotheses; every recursive call descends to a
    SUBTERM, so both guards re-establish from the plateau descent substrate
    (`size_lt_lamCell_body` / `size_lt_appCell_*` / `size_lt_childCons_*`,
    `lamNormal_bodyNormal` / `appNormal_*Normal` / the generic mkGen child-normality extraction);
    the conv arm keeps the subject and passes the guards through.

WHY THIS CUTS THE KNOT: the unguarded master demands a GLOBAL residual, but the residual's own
discharge (the spine analysis) needs the master back on reduct subterms — circular.  The guarded
residual at bound `N` only ever consumes the guarded master at strictly smaller pieces, so
`∀ bound, PinnedReflectionPiElimResidualGuarded profile bound` is provable by STRONG INDUCTION on
the bound: at `N`, the spine analysis invokes `pinnedReflectionGuarded` at bounds `< N` with the
induction hypothesis as its residual.  The plateau master (next brick) is exactly that induction.

## Zero-axiom verification

The arms are the shipped zero-axiom bricks; the guard threading adds only the descent substrate.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The guarded piElim residual**: the residual restricted to NORMAL applications of size within
`bound`.  The plateau induction proves `∀ bound, PinnedReflectionPiElimResidualGuarded profile
bound` by strong induction — at each bound the spine analysis only consumes the guarded master at
strictly smaller pieces. -/
def PinnedReflectionPiElimResidualGuarded (profile : PolyProfile) (bound : Nat) : Prop :=
  ∀ {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {functionTerm argument domainCode : RawTerm targetScope}
    {codomainCode : RawTerm (targetScope + 1)},
    HasTypeDescPi profile targetContext functionTerm
      (piTyCodeCell domainCode codomainCode) →
    HasTypeDescPi profile targetContext argument domainCode →
    (appCell functionTerm argument).size ≤ bound →
    RawTerm.isStepNormalForm (appCell functionTerm argument) →
    PinnedReflectionConclusion profile targetContext functionTerm
      (piTyCodeCell domainCode codomainCode) →
    PinnedReflectionConclusion profile targetContext argument domainCode →
    PinnedReflectionConclusion profile targetContext (appCell functionTerm argument)
      (RawTerm.subst0 codomainCode argument)

mutual

/-- **The GUARDED conditional master**: the conditional grown master with (size ≤ bound) +
normality threaded — every recursive call's guards discharge by the plateau descent substrate. -/
theorem HasTypeDescPi.pinnedReflectionGuarded {profile : PolyProfile} {bound : Nat}
    (residual : PinnedReflectionPiElimResidualGuarded profile bound)
    (flagUnique : SourceUniverseFlagUnique profile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier : RawTerm targetScope}
    (derivation : HasTypeDescPi profile targetContext subject classifier)
    (sizeBound : subject.size ≤ bound)
    (subjectNormal : RawTerm.isStepNormalForm subject) :
    PinnedReflectionConclusion profile targetContext subject classifier :=
  match derivation with
  | .ofFormation formationTyped =>
      pinnedReflectionOfFormationArm profile formationTyped
  | .conv _levelExpr _flag typedPremise converts _reclassifierTyped =>
      pinnedReflectionConvArm profile converts
        (HasTypeDescPi.pinnedReflectionGuarded residual flagUnique typedPremise sizeBound
          subjectNormal)
  | .piIntro domainLevel _codomainLevel flag domainTyped _codomainTyped bodyTyped =>
      pinnedReflectionPiIntroArm profile flagUnique domainTyped
        (HasTypeDescPi.pinnedReflectionGuarded residual flagUnique domainTyped
          (Nat.le_of_lt (Nat.lt_of_lt_of_le (RawTerm.size_lt_lamCell_domain _ _) sizeBound))
          (lamNormal_domainNormal _ _ subjectNormal))
        (HasTypeDescPi.pinnedReflectionGuarded residual flagUnique bodyTyped
          (Nat.le_of_lt (Nat.lt_of_lt_of_le (RawTerm.size_lt_lamCell_body _ _) sizeBound))
          (lamNormal_bodyNormal _ _ subjectNormal))
  | .piElim functionTyped argumentTyped =>
      residual functionTyped argumentTyped sizeBound subjectNormal
        (HasTypeDescPi.pinnedReflectionGuarded residual flagUnique functionTyped
          (Nat.le_of_lt
            (Nat.lt_of_lt_of_le (RawTerm.size_lt_appCell_function _ _) sizeBound))
          (appNormal_functionNormal _ _ subjectNormal))
        (HasTypeDescPi.pinnedReflectionGuarded residual flagUnique argumentTyped
          (Nat.le_of_lt
            (Nat.lt_of_lt_of_le (RawTerm.size_lt_appCell_argument _ _) sizeBound))
          (appNormal_argumentNormal _ _ subjectNormal))
  | .genFormationPi _targetContext generator payload children levels flag rule
      isFormation premises => by
      intro targetWellFormed sourceScope rho sourceContext rhoInjective condition
        wellFormed sourceSubject pinBase subjectInImage pinned pinBaseTyped
      have hNotVar : generator ≠ Generator.gen_var :=
        formationRuleImpliesNotVariable isFormation
      obtain rfl : rule = { outputType := universeFormerOutput } :=
        formationRuleIsUniverseFormer isFormation
      obtain ⟨sourcePayload, sourceChildren, hSource, hChildren⟩ :=
        renameEqMkGenInversion rho hNotVar subjectInImage.symm
      subst hSource
      have childrenBound : children.size ≤ bound :=
        Nat.le_of_succ_le sizeBound
      have childrenNormal : RawTermChildren.areStepNormalFormsBool children = true :=
        RawTerm.isStepNormalForm_childrenNormal subjectNormal
      have sourceTelescope :=
        DescTelescopePi.pinnedReflectionTelescopeGuarded residual flagUnique premises
          childrenBound childrenNormal targetWellFormed rho sourceContext rhoInjective
          condition wellFormed hChildren
      refine ⟨universeFormerOutput _ levels flag, ?_, ?_⟩
      · show Conv (universeCodeCell (lmaxAll levels) flag)
          (RawTerm.rename rho (universeCodeCell (lmaxAll levels) flag))
        rw [rename_universeCodeCell]
        exact Conv.refl _
      · exact HasTypeDescPi.genFormationPi sourceContext generator sourcePayload
          sourceChildren levels flag { outputType := universeFormerOutput }
          isFormation sourceTelescope

/-- The guarded grown telescope leg: heads recurse with bounds and normality extracted from the
spine by the plateau descent substrate. -/
theorem DescTelescopePi.pinnedReflectionTelescopeGuarded {profile : PolyProfile} {bound : Nat}
    (residual : PinnedReflectionPiElimResidualGuarded profile bound)
    (flagUnique : SourceUniverseFlagUnique profile)
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {targetContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile targetContext levels flag children)
    (childrenBound : children.size ≤ bound)
    (childrenNormal : RawTermChildren.areStepNormalFormsBool children = true) :
    WfContextDescPi targetContext →
    ∀ {sourceBaseScope : Nat} (rho : RawRenaming sourceBaseScope baseScope)
      (sourceContext : TypingContext profile (sourceBaseScope + currentDepth)),
      Function.Injective rho →
      ContextReflectsRename profile (iterateLiftRaw rho currentDepth)
        sourceContext targetContext →
      WfContextDescPi sourceContext →
      ∀ {sourceChildren : RawTermChildren binderShifts sourceBaseScope},
        children = RawTermChildren.rename rho sourceChildren →
        DescTelescopePi profile sourceContext levels flag sourceChildren :=
  match telescope with
  | .nil _targetContext flag => by
      intro _targetWellFormed sourceBaseScope rho sourceContext _rhoInjective
        _condition _wellFormed sourceChildren hChildren
      cases sourceChildren with
      | childNil => exact DescTelescopePi.nil sourceContext flag
  | .cons _targetContext head headLevel restLevels flag rest headTyped restTyped => by
      intro targetWellFormed sourceBaseScope rho sourceContext rhoInjective condition
        wellFormed sourceChildren hChildren
      cases sourceChildren with
        | childCons sourceHead sourceRest =>
          have hChildrenReduced :
              RawTermChildren.childCons head rest =
                RawTermChildren.childCons
                  (RawTerm.rename (iterateLiftRaw rho currentDepth) sourceHead)
                  (RawTermChildren.rename rho sourceRest) := hChildren
          injection hChildrenReduced with hHeadScope hHeadShift hRestShifts hHead hTail
          have headBound : head.size ≤ bound :=
            Nat.le_of_lt (Nat.lt_of_lt_of_le
              (RawTermChildren.size_lt_childCons_head head rest) childrenBound)
          have restBound : rest.size ≤ bound :=
            Nat.le_of_lt (Nat.lt_of_lt_of_le
              (RawTermChildren.size_lt_childCons_tail head rest) childrenBound)
          have headNormal : RawTerm.isStepNormalForm head :=
            RawTermChildren.areStepNormalFormsBool_head childrenNormal
          have restNormal : RawTermChildren.areStepNormalFormsBool rest = true :=
            RawTermChildren.areStepNormalFormsBool_tail childrenNormal
          have headPin :
              Conv (universeCodeCell headLevel flag)
                (RawTerm.rename (iterateLiftRaw rho currentDepth)
                  (universeCodeCell headLevel flag)) := by
            rw [rename_universeCodeCell]
            exact Conv.refl _
          obtain ⟨reflectedClassifier, classifierConv, reflectedTyped⟩ :=
            HasTypeDescPi.pinnedReflectionGuarded residual flagUnique headTyped headBound headNormal
              targetWellFormed (iterateLiftRaw rho currentDepth) sourceContext
              (RawRenaming.iterateLiftRaw_injective rhoInjective currentDepth)
              condition wellFormed hHead headPin
              ⟨headLevel.lsucc, flag,
                HasTypeDescPi.ofFormation
                  (HasTypeDesc.universeFormation sourceContext headLevel flag)⟩
          have sourceHeadTyped :
              HasTypeDescPi profile sourceContext sourceHead
                (universeCodeCell headLevel flag) :=
            HasTypeDescPi.retypeAtUniverse (iterateLiftRaw rho currentDepth)
              (RawRenaming.iterateLiftRaw_injective rhoInjective currentDepth)
              classifierConv reflectedTyped
          have headPinned :
              Conv head
                (RawTerm.rename (iterateLiftRaw rho currentDepth) sourceHead) :=
            hHead ▸ Conv.refl _
          have condition' :
              ContextReflectsRename profile (iterateLiftRaw rho (currentDepth + 1))
                (sourceContext.cons sourceHead) (_targetContext.cons head) :=
            ContextReflectsRename.consConv profile condition headPinned
          have wellFormed' : WfContextDescPi (sourceContext.cons sourceHead) :=
            ⟨wellFormed, headLevel, flag, sourceHeadTyped⟩
          have targetWellFormed' : WfContextDescPi (_targetContext.cons head) :=
            ⟨targetWellFormed, headLevel, flag, headTyped⟩
          exact DescTelescopePi.cons sourceContext sourceHead headLevel restLevels
            flag sourceRest sourceHeadTyped
            (DescTelescopePi.pinnedReflectionTelescopeGuarded residual flagUnique restTyped
              restBound restNormal targetWellFormed' rho
              (sourceContext.cons sourceHead) rhoInjective condition' wellFormed' hTail)

end -- mutual

end FX1Poly.Typed
