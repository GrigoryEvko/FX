import FX1Poly.Typed.PinnedReflectionPiIntro
import FX1Poly.Typed.HasTypeDescWeakening

/-! Probe: STR-8 brick 7 — the FORMATION-ENGINE master reflection, UNCONDITIONAL.  The formation
engine has no piElim, so its pinned reflection closes with NO residual and — stronger — NO PIN:
var/universeFormation are leaves, conv passes the existential through, and genFormation's
classifier is a rename-invariant universe code whose telescope heads re-pin via injective Conv
reflection.  Mutual with the telescope leg (exact-image heads, exact telescope conclusion). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- Re-pin a reflected typing to an EXACT universe classifier: if the image of the reflected
classifier is `Conv` to a (rename-invariant) universe code, injective reflection moves the `Conv`
to the source and the formation `conv` rule re-types at the universe code. -/
theorem HasTypeDesc.retypeAtUniverse {profile : PolyProfile}
    {sourceScope targetScope : Nat} (rho : RawRenaming sourceScope targetScope)
    (rhoInjective : Function.Injective rho)
    {sourceContext : TypingContext profile sourceScope}
    {sourceSubject reflectedClassifier : RawTerm sourceScope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (imagePinned :
      Conv (universeCodeCell levelExpr flag) (RawTerm.rename rho reflectedClassifier))
    (typed : HasTypeDesc profile sourceContext sourceSubject reflectedClassifier) :
    HasTypeDesc profile sourceContext sourceSubject (universeCodeCell levelExpr flag) := by
  have imagesConv :
      Conv (RawTerm.rename rho reflectedClassifier)
        (RawTerm.rename rho (universeCodeCell levelExpr flag)) := by
    rw [rename_universeCodeCell]
    exact imagePinned.sym
  have sourceConv : Conv reflectedClassifier (universeCodeCell levelExpr flag) :=
    Conv.reflectRenameOfFinInjective rho rhoInjective imagesConv
  exact HasTypeDesc.conv levelExpr.lsucc flag typed sourceConv
    (HasTypeDesc.universeFormation sourceContext levelExpr flag)

/-- **Non-variable cell rename inversion**: an image term that IS a non-var `mkGen` cell comes from
a cell at the SAME generator with exact-image children (the payload equation is dropped — formation
rules do not constrain payloads). -/
theorem renameEqMkGenInversion {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {sourceTerm : RawTerm sourceScope}
    {generator : Generator} (hNotVar : generator ≠ .gen_var)
    {payload : generator.payload targetScope}
    {children : RawTermChildren generator.binderShifts targetScope}
    (imageEq : RawTerm.rename rho sourceTerm = .mkGen generator payload children) :
    ∃ (sourcePayload : generator.payload sourceScope)
      (sourceChildren : RawTermChildren generator.binderShifts sourceScope),
      sourceTerm = .mkGen generator sourcePayload sourceChildren ∧
      children = RawTermChildren.rename rho sourceChildren := by
  cases sourceTerm with
  | mkGen sourceGenerator sourcePayload sourceChildren =>
    by_cases hVar : sourceGenerator = .gen_var
    · subst hVar
      cases sourceChildren with
      | childNil =>
        rw [RawTerm.rename_var_reduces] at imageEq
        injection imageEq with hScope hGenerator hPayload hChildren
        exact absurd hGenerator.symm hNotVar
    · rw [RawTerm.rename_mkGen_of_ne_var rho hVar] at imageEq
      injection imageEq with hScope hGenerator hPayload hChildren
      subst hGenerator
      exact ⟨sourcePayload, sourceChildren, rfl, (eq_of_heq hChildren).symm⟩

mutual

/-- **The formation-engine master pinned reflection — UNCONDITIONAL and PIN-FREE.**  An in-image
formation subject reflects to a source formation typing at a classifier whose image is `Conv` to
the original.  No pin premise: formation classifiers are lookups (the context condition), universe
codes (rename-invariant), or pass through `conv`. -/
theorem HasTypeDesc.pinnedReflection {profile : PolyProfile}
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier : RawTerm targetScope}
    (derivation : HasTypeDesc profile targetContext subject classifier) :
    ∀ {sourceScope : Nat} (rho : RawRenaming sourceScope targetScope)
      (sourceContext : TypingContext profile sourceScope),
      Function.Injective rho →
      ContextReflectsRename profile rho sourceContext targetContext →
      ∀ {sourceSubject : RawTerm sourceScope},
        subject = RawTerm.rename rho sourceSubject →
        ∃ reflectedClassifier : RawTerm sourceScope,
          Conv classifier (RawTerm.rename rho reflectedClassifier) ∧
          HasTypeDesc profile sourceContext sourceSubject reflectedClassifier :=
  match derivation with
  | .var _targetContext index =>
      fun rho sourceContext _rhoInjective condition sourceSubject subjectInImage =>
        HasTypeDesc.varArmPinnedReflection profile rho condition subjectInImage.symm
  | .conv levelExpr flag typedPremise converts _reclassifierTyped =>
      fun rho sourceContext rhoInjective condition sourceSubject subjectInImage => by
        obtain ⟨reflectedClassifier, classifierConv, reflectedTyped⟩ :=
          HasTypeDesc.pinnedReflection typedPremise rho sourceContext rhoInjective
            condition subjectInImage
        exact ⟨reflectedClassifier, converts.sym.trans classifierConv, reflectedTyped⟩
  | .universeFormation _targetContext levelExpr flag =>
      fun rho sourceContext _rhoInjective _condition sourceSubject subjectInImage =>
        HasTypeDesc.universeArmPinnedReflection profile rho sourceContext subjectInImage.symm
  | .genFormation _targetContext generator payload children levels flag rule
      isFormation premises =>
      fun rho sourceContext rhoInjective condition sourceSubject subjectInImage => by
        have hNotVar : generator ≠ Generator.gen_var :=
          formationRuleImpliesNotVariable isFormation
        obtain rfl : rule = { outputType := universeFormerOutput } :=
          formationRuleIsUniverseFormer isFormation
        obtain ⟨sourcePayload, sourceChildren, hSource, hChildren⟩ :=
          renameEqMkGenInversion rho hNotVar subjectInImage.symm
        subst hSource
        have sourceTelescope :=
          DescTelescope.pinnedReflectionTelescope premises rho sourceContext
            rhoInjective condition hChildren
        refine ⟨universeFormerOutput _ levels flag, ?_, ?_⟩
        · show Conv (universeCodeCell (lmaxAll levels) flag)
            (RawTerm.rename rho (universeCodeCell (lmaxAll levels) flag))
          rw [rename_universeCodeCell]
          exact Conv.refl _
        · exact HasTypeDesc.genFormation sourceContext generator sourcePayload
            sourceChildren levels flag { outputType := universeFormerOutput }
            isFormation sourceTelescope

/-- **The formation telescope reflection leg** — EXACT-image heads, EXACT telescope conclusion:
each head is an exact image at the depth-lifted renaming, the head reflection re-pins to its
universe classifier via `retypeAtUniverse`, and the context grows by the exact-image instance of
the Kripke extension. -/
theorem DescTelescope.pinnedReflectionTelescope {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {targetContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescope profile targetContext levels flag children) :
    ∀ {sourceBaseScope : Nat} (rho : RawRenaming sourceBaseScope baseScope)
      (sourceContext : TypingContext profile (sourceBaseScope + currentDepth)),
      Function.Injective rho →
      ContextReflectsRename profile (iterateLiftRaw rho currentDepth)
        sourceContext targetContext →
      ∀ {sourceChildren : RawTermChildren binderShifts sourceBaseScope},
        children = RawTermChildren.rename rho sourceChildren →
        DescTelescope profile sourceContext levels flag sourceChildren :=
  match telescope with
  | .nil _targetContext flag =>
      fun rho sourceContext _rhoInjective _condition sourceChildren hChildren => by
        cases sourceChildren with
        | childNil => exact DescTelescope.nil sourceContext flag
  | .cons _targetContext head headLevel restLevels flag rest headTyped restTyped =>
      fun rho sourceContext rhoInjective condition sourceChildren hChildren => by
        cases sourceChildren with
        | childCons sourceHead sourceRest =>
          have hChildrenReduced :
              RawTermChildren.childCons head rest =
                RawTermChildren.childCons
                  (RawTerm.rename (iterateLiftRaw rho currentDepth) sourceHead)
                  (RawTermChildren.rename rho sourceRest) := hChildren
          injection hChildrenReduced with hHeadScope hHeadShift hRestShifts hHead hTail
          obtain ⟨reflectedClassifier, classifierConv, reflectedTyped⟩ :=
            HasTypeDesc.pinnedReflection headTyped (iterateLiftRaw rho currentDepth)
              sourceContext
              (RawRenaming.iterateLiftRaw_injective rhoInjective currentDepth)
              condition hHead
          have sourceHeadTyped :
              HasTypeDesc profile sourceContext sourceHead
                (universeCodeCell headLevel flag) :=
            HasTypeDesc.retypeAtUniverse (iterateLiftRaw rho currentDepth)
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
          exact DescTelescope.cons sourceContext sourceHead headLevel restLevels flag
            sourceRest sourceHeadTyped
            (DescTelescope.pinnedReflectionTelescope restTyped rho
              (sourceContext.cons sourceHead) rhoInjective condition' hTail)

end -- mutual

end FX1Poly.Typed

#print axioms FX1Poly.Typed.HasTypeDesc.retypeAtUniverse
#print axioms FX1Poly.Typed.renameEqMkGenInversion
#print axioms FX1Poly.Typed.HasTypeDesc.pinnedReflection
#print axioms FX1Poly.Typed.DescTelescope.pinnedReflectionTelescope
