import FX1Poly.Typed.FormationPinnedReflection

/-! Probe: STR-8 brick 8 — THE CONDITIONAL GROWN MASTER.  Mutual induction over
`HasTypeDescPi`/`DescTelescopePi` in the pinned motive, with every arm discharged by the shipped
brick kit EXCEPT piElim, which is the explicit residual hypothesis (the function-Π float — the
campaign's open core). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The piElim residual** — the single open core of the pinned reflection: reflect an in-image
application whose OUTPUT classifier is pinned, given reflections for the function and argument
premises.  The function's Π classifier is the float (no pin is available for it from the output
pin alone). -/
def PinnedReflectionPiElimResidual (profile : PolyProfile) : Prop :=
  ∀ {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {functionTerm argument domainCode : RawTerm targetScope}
    {codomainCode : RawTerm (targetScope + 1)},
    HasTypeDescPi profile targetContext functionTerm
      (piTyCodeCell domainCode codomainCode) →
    HasTypeDescPi profile targetContext argument domainCode →
    PinnedReflectionConclusion profile targetContext functionTerm
      (piTyCodeCell domainCode codomainCode) →
    PinnedReflectionConclusion profile targetContext argument domainCode →
    PinnedReflectionConclusion profile targetContext (appCell functionTerm argument)
      (RawTerm.subst0 codomainCode argument)

/-- Grown twin of `HasTypeDesc.retypeAtUniverse`: re-pin a reflected GROWN typing to an exact
universe classifier via injective Conv reflection + the grown `conv` rule. -/
theorem HasTypeDescPi.retypeAtUniverse {profile : PolyProfile}
    {sourceScope targetScope : Nat} (rho : RawRenaming sourceScope targetScope)
    (rhoInjective : Function.Injective rho)
    {sourceContext : TypingContext profile sourceScope}
    {sourceSubject reflectedClassifier : RawTerm sourceScope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (imagePinned :
      Conv (universeCodeCell levelExpr flag) (RawTerm.rename rho reflectedClassifier))
    (typed : HasTypeDescPi profile sourceContext sourceSubject reflectedClassifier) :
    HasTypeDescPi profile sourceContext sourceSubject
      (universeCodeCell levelExpr flag) := by
  have imagesConv :
      Conv (RawTerm.rename rho reflectedClassifier)
        (RawTerm.rename rho (universeCodeCell levelExpr flag)) := by
    rw [rename_universeCodeCell]
    exact imagePinned.sym
  have sourceConv : Conv reflectedClassifier (universeCodeCell levelExpr flag) :=
    Conv.reflectRenameOfFinInjective rho rhoInjective imagesConv
  exact HasTypeDescPi.conv levelExpr.lsucc flag typed sourceConv
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation sourceContext levelExpr flag))

/-- The `ofFormation` arm: the formation master reflection is pin-free; wrap its output. -/
theorem pinnedReflectionOfFormationArm (profile : PolyProfile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier : RawTerm targetScope}
    (formationTyped : HasTypeDesc profile targetContext subject classifier) :
    PinnedReflectionConclusion profile targetContext subject classifier := by
  intro sourceScope rho sourceContext rhoInjective condition _wellFormed
    sourceSubject pinBase subjectInImage pinned pinBaseTyped
  obtain ⟨reflectedClassifier, classifierConv, reflectedTyped⟩ :=
    HasTypeDesc.pinnedReflection formationTyped rho sourceContext rhoInjective
      condition subjectInImage
  exact ⟨reflectedClassifier, classifierConv, HasTypeDescPi.ofFormation reflectedTyped⟩

/-- The grown `conv` arm: re-pin the premise through the conversion (same pin base). -/
theorem pinnedReflectionConvArm (profile : PolyProfile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier reclassifier : RawTerm targetScope}
    (converts : Conv classifier reclassifier)
    (premiseIH : PinnedReflectionConclusion profile targetContext subject classifier) :
    PinnedReflectionConclusion profile targetContext subject reclassifier := by
  intro sourceScope rho sourceContext rhoInjective condition wellFormed
    sourceSubject pinBase subjectInImage pinned pinBaseTyped
  obtain ⟨reflectedClassifier, classifierConv, reflectedTyped⟩ :=
    premiseIH rho sourceContext rhoInjective condition wellFormed
      subjectInImage (converts.trans pinned) pinBaseTyped
  exact ⟨reflectedClassifier, converts.sym.trans classifierConv, reflectedTyped⟩

mutual

/-- **THE CONDITIONAL GROWN MASTER pinned reflection** — every arm discharged except piElim,
which is the explicit `residual` hypothesis. -/
theorem HasTypeDescPi.pinnedReflectionConditional {profile : PolyProfile}
    (residual : PinnedReflectionPiElimResidual profile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier : RawTerm targetScope}
    (derivation : HasTypeDescPi profile targetContext subject classifier) :
    PinnedReflectionConclusion profile targetContext subject classifier :=
  match derivation with
  | .ofFormation formationTyped =>
      pinnedReflectionOfFormationArm profile formationTyped
  | .conv _levelExpr _flag typedPremise converts _reclassifierTyped =>
      pinnedReflectionConvArm profile converts
        (HasTypeDescPi.pinnedReflectionConditional residual typedPremise)
  | .piIntro _domainLevel _codomainLevel _flag _domainTyped _codomainTyped bodyTyped =>
      pinnedReflectionPiIntroArm profile
        (HasTypeDescPi.pinnedReflectionConditional residual bodyTyped)
  | .piElim functionTyped argumentTyped =>
      residual functionTyped argumentTyped
        (HasTypeDescPi.pinnedReflectionConditional residual functionTyped)
        (HasTypeDescPi.pinnedReflectionConditional residual argumentTyped)
  | .genFormationPi _targetContext generator payload children levels flag rule
      isFormation premises => by
      intro rho sourceContext rhoInjective condition wellFormed
        sourceSubject pinBase subjectInImage pinned pinBaseTyped
      have hNotVar : generator ≠ Generator.gen_var :=
        formationRuleImpliesNotVariable isFormation
      obtain rfl : rule = { outputType := universeFormerOutput } :=
        formationRuleIsUniverseFormer isFormation
      obtain ⟨sourcePayload, sourceChildren, hSource, hChildren⟩ :=
        renameEqMkGenInversion rho hNotVar subjectInImage.symm
      subst hSource
      have sourceTelescope :=
        DescTelescopePi.pinnedReflectionTelescopeConditional residual premises rho
          sourceContext rhoInjective condition wellFormed hChildren
      refine ⟨universeFormerOutput _ levels flag, ?_, ?_⟩
      · show Conv (universeCodeCell (lmaxAll levels) flag)
          (RawTerm.rename rho (universeCodeCell (lmaxAll levels) flag))
        rw [rename_universeCodeCell]
        exact Conv.refl _
      · exact HasTypeDescPi.genFormationPi sourceContext generator sourcePayload
          sourceChildren levels flag { outputType := universeFormerOutput }
          isFormation sourceTelescope

/-- **The grown telescope reflection leg (conditional)** — exact-image heads, exact telescope
conclusion; heads re-pin to their universe classifiers via `HasTypeDescPi.retypeAtUniverse`
(pin base = the rename-invariant universe code, typed by `universeFormation`). -/
theorem DescTelescopePi.pinnedReflectionTelescopeConditional {profile : PolyProfile}
    (residual : PinnedReflectionPiElimResidual profile)
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {targetContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile targetContext levels flag children) :
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
  | .nil _targetContext flag =>
      fun rho sourceContext _rhoInjective _condition _wellFormed sourceChildren
          hChildren => by
        cases sourceChildren with
        | childNil => exact DescTelescopePi.nil sourceContext flag
  | .cons _targetContext head headLevel restLevels flag rest headTyped restTyped =>
      fun rho sourceContext rhoInjective condition wellFormed sourceChildren
          hChildren => by
        cases sourceChildren with
        | childCons sourceHead sourceRest =>
          have hChildrenReduced :
              RawTermChildren.childCons head rest =
                RawTermChildren.childCons
                  (RawTerm.rename (iterateLiftRaw rho currentDepth) sourceHead)
                  (RawTermChildren.rename rho sourceRest) := hChildren
          injection hChildrenReduced with hHeadScope hHeadShift hRestShifts hHead hTail
          have headPin :
              Conv (universeCodeCell headLevel flag)
                (RawTerm.rename (iterateLiftRaw rho currentDepth)
                  (universeCodeCell headLevel flag)) := by
            rw [rename_universeCodeCell]
            exact Conv.refl _
          obtain ⟨reflectedClassifier, classifierConv, reflectedTyped⟩ :=
            HasTypeDescPi.pinnedReflectionConditional residual headTyped
              (iterateLiftRaw rho currentDepth) sourceContext
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
          exact DescTelescopePi.cons sourceContext sourceHead headLevel restLevels
            flag sourceRest sourceHeadTyped
            (DescTelescopePi.pinnedReflectionTelescopeConditional residual restTyped
              rho (sourceContext.cons sourceHead) rhoInjective condition'
              wellFormed' hTail)

end -- mutual

end FX1Poly.Typed

#print axioms FX1Poly.Typed.HasTypeDescPi.retypeAtUniverse
#print axioms FX1Poly.Typed.pinnedReflectionOfFormationArm
#print axioms FX1Poly.Typed.pinnedReflectionConvArm
#print axioms FX1Poly.Typed.HasTypeDescPi.pinnedReflectionConditional
#print axioms FX1Poly.Typed.DescTelescopePi.pinnedReflectionTelescopeConditional
