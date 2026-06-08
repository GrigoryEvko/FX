import FX1Poly.Typed.HasTypeDescPiSubjectReductionMutual
import FX1Poly.Typed.HasTypeDescPiContextConversionWf

/-! # FX1Poly/Typed/GrownMutualMetatheoryFromPiValidity
    — the grown mutual fundamental-metatheory bundle, conditional on the SINGLE residual (GTL-20 / #834)

`HasTypeDescPiContextConversionPiElimReduction.lean` (`#1092`) named the lone GrownCtxConv-5 residual,
`ConvContextPreservesPiValidity` (a `Π`-type-code's validity is stable under context conversion), and
proved that the grown context-conversion piElim arm reduces to it.  `#1093` threaded `WfContextDescPi`
through the grown context-conversion mutual pair conditional on that residual.  This file is the GTL-20
"state + open the mutual fundamental-metatheory bundle" capstone: it proves that the SAME single residual
discharges BOTH open release-blocker metatheory tasks —

  * **grown context-conversion** (GrownCtxConv-5, `#842`) — `grownContextConversionFromPiValidity`, and
  * **the grown master subject reduction** (SRD-2, `#845` / SN-055 / `#558`) —
    `masterSubjectReductionFromPiValidity ⋈ DescTelescopePi.subjectReductionFromPiValidity`.

So the entire grown metatheory frontier is now provably ONE obligation: `ConvContextPreservesPiValidity`.

## Why the SR side needed a re-statement (the Wf-threading correction)

The shipped master SR `HasTypeDescPi.subjectReductionOfPiElimArm` (SRD-1/SRD-2) is conditional on the
WHOLE grown context-conversion `piElim` arm as a `WfContextDescPi`-FREE hypothesis.  That arm CANNOT be
discharged from `ConvContextPreservesPiValidity` directly: the discharge route
(`piElimArmFromPiValidityTransfer`, `#1092`) needs `WfContextDescPi` to expose the function's
`Π`-classifier as a validity (`classifierIsTypeDescPi`), and `HasTypeDescPi Γ t T → WfContextDesc Γ` is
REFUTED (`ContextValidityFails.lean`: the `var` rule types in ill-formed contexts), so well-formedness
cannot be recovered inside the `Wf`-free arm.

The fix is to thread `WfContextDescPi` through the master SR itself.  The shipped master SR consumes its
`piElim` arm in exactly ONE place — the telescope `here` arm's grown telescope context-conversion
`convTelescopeOfPiElimArm`.  Replacing that ONE call with `#1093`'s `Wf`-threading
`convTelescopeWfOfPiValidity` (supplying the source `WfContextDescPi (Γ.cons head)` from
`WfContextDescPi.cons`) re-bases the whole mutual block on the residual, with every other arm — `conv`,
`piIntro` (body SR under the extended binder), `piElim` (function/argument SR via
`subjectReductionPiElimArmDescPi`), `genFormationPi` (`former_step_inv` + the mutual telescope SR) —
unchanged.  A mechanical re-statement, NOT a new proof.

## The bundle

  * `HasTypeDescPi.grownContextConversionFromPiValidity` — the clean top-level GrownCtxConv-5 closure modulo the
    residual (a `#1093` consequence: residual + `WfContextDescPi` ⟹ context-conversion at a `Conv`-equal
    classifier).
  * `HasTypeDescPi.masterSubjectReductionFromPiValidity` ⋈ `DescTelescopePi.subjectReductionFromPiValidity`
    — the `Wf`-threading master SR + telescope SR, conditional on the residual.  Discharging
    `ConvContextPreservesPiValidity` makes the grown master SR (and hence SN-055 / the unified SR
    dispatcher) unconditional.
  * `HasTypeDescPi.grownMutualMetatheoryFromPiValidity` — the explicit unification: ONE residual ⟹ BOTH
    context-conversion AND master SR.

## Zero-axiom verification

The context-conversion half wraps `#1093` (`convContextWfOfPiValidity`).  The SR half is the shipped
`subjectReductionOfPiElimArm` mutual block with the `piElim`-arm hypothesis replaced by the residual and
the single telescope context-conversion call swapped to `convTelescopeWfOfPiValidity` — reusing
`subjectReductionPiIntroArm` / `subjectReductionPiElimArmDescPi` / `subjectAdmitsNoStep` /
`former_step_inv` / `convContextCondition_consStep` / `WfContextDescPi.cons` unchanged.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated
in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **GrownCtxConv-5 closure modulo the single residual.**  Under `ConvContextPreservesPiValidity` and source
well-formedness `WfContextDescPi sourceContext`, a grown derivation survives replacing the context by any
pointwise-`Conv`-related one, at a `Conv`-equal classifier.  The clean top-level form of the `#1093`
`WfContextDescPi`-threaded mutual context-conversion — the grown context-conversion (`#814` / GrownCtxConv-5,
`#842`) reduced to the lone obligation `ConvContextPreservesPiValidity`. -/
theorem HasTypeDescPi.grownContextConversionFromPiValidity {profile : PolyProfile}
    (piValidityTransfers : ConvContextPreservesPiValidity profile)
    {scope : Nat} {sourceContext : TypingContext profile scope} {subject classifier : RawTerm scope}
    (sourceWellFormed : WfContextDescPi sourceContext)
    (derivation : HasTypeDescPi profile sourceContext subject classifier)
    (targetContext : TypingContext profile scope)
    (contextConv : ∀ index : Fin scope, Conv (sourceContext.lookup index) (targetContext.lookup index)) :
    ∃ classifier', Conv classifier classifier' ∧
      HasTypeDescPi profile targetContext subject classifier' :=
  HasTypeDescPi.convContextWfOfPiValidity piValidityTransfers sourceWellFormed derivation
    targetContext contextConv

mutual

/-- **The grown master subject reduction, conditional on the single residual** (the SRD-2 / `#845`
discharge modulo `ConvContextPreservesPiValidity`).  A grown-typed subject is preserved under a `Step`, at
the SAME classifier, given only `ConvContextPreservesPiValidity` (and the threaded `WfContextDescPi`).  The
`Wf`-threading re-statement of `subjectReductionOfPiElimArm`: `ofFormation` vacuous, `conv` recurses,
`piIntro` / `piElim` use the shipped function-space arms with the children's SR obtained recursively,
`genFormationPi` re-types its premise telescope via the mutual telescope SR.  Discharging the residual
yields the unconditional grown master SR (SN-055). -/
theorem HasTypeDescPi.masterSubjectReductionFromPiValidity {profile : PolyProfile}
    (piValidityTransfers : ConvContextPreservesPiValidity profile)
    {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescPi profile context subject classifier)
    (wellFormed : WfContextDescPi context) :
    ∀ reduct : RawTerm scope, Step subject reduct →
      HasTypeDescPi profile context reduct classifier :=
  match derivation with
  | .ofFormation formationTyped => fun reduct step =>
      absurd step (formationTyped.subjectAdmitsNoStep reduct)
  | .conv levelExpr flag typed converts reclassifierTyped => fun reduct step =>
      HasTypeDescPi.conv levelExpr flag
        (HasTypeDescPi.masterSubjectReductionFromPiValidity piValidityTransfers typed wellFormed
          reduct step)
        converts reclassifierTyped
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel codomainLevel flag
      domainTyped codomainTyped bodyTyped => fun reduct step =>
      HasTypeDescPi.subjectReductionPiIntroArm domainTyped codomainTyped step
        (fun {bodyReduct} bodyStep =>
          HasTypeDescPi.masterSubjectReductionFromPiValidity piValidityTransfers bodyTyped
            (WfContextDescPi.cons wellFormed ⟨domainLevel, flag, domainTyped⟩) bodyReduct bodyStep)
  | .piElim functionTyped argumentTyped => fun reduct step =>
      HasTypeDescPi.subjectReductionPiElimArmDescPi functionTyped argumentTyped step
        (fun {functionReduct} functionStep =>
          HasTypeDescPi.masterSubjectReductionFromPiValidity piValidityTransfers functionTyped
            wellFormed functionReduct functionStep)
        (fun {argumentReduct} argumentStep =>
          HasTypeDescPi.masterSubjectReductionFromPiValidity piValidityTransfers argumentTyped
            wellFormed argumentReduct argumentStep)
        wellFormed
  | .genFormationPi formerContext generator payload children levels flag rule isFormation premises =>
      fun reduct step => by
      obtain ⟨children', reductEq, stepChildren⟩ := former_step_inv isFormation step
      subst reductEq
      exact HasTypeDescPi.genFormationPi formerContext generator payload children' levels flag rule
        isFormation
        (DescTelescopePi.subjectReductionFromPiValidity piValidityTransfers premises wellFormed
          children' stepChildren)

/-- **The grown premise-telescope subject reduction, conditional on the single residual** (the mutual
companion).  `cons`/`here` (the binding head steps): re-type the head via the mutual dispatcher, then
re-type the tail under the stepped binding via the residual-conditional `Wf`-threading telescope
context-conversion `convTelescopeWfOfPiValidity` (the ONE place the old `Wf`-free `piElim` arm was
consumed); `cons`/`there` (a tail child steps): recurse under the extended `WfContextDescPi`. -/
theorem DescTelescopePi.subjectReductionFromPiValidity {profile : PolyProfile}
    (piValidityTransfers : ConvContextPreservesPiValidity profile)
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile context levels flag children)
    (wellFormed : WfContextDescPi context) :
    ∀ (children' : RawTermChildren binderShifts baseScope),
      StepChildren children children' → DescTelescopePi profile context levels flag children' :=
  match telescope with
  | .nil _context _flag => fun _children' stepChildren =>
      (StepChildren.no_step_at_empty_spine stepChildren).elim
  | .cons context head headLevel restLevels flag rest headTyped restTyped =>
      fun _children' stepChildren => by
        cases stepChildren with
        | here _rest headStep =>
            rename_i headAfter
            refine DescTelescopePi.cons context headAfter headLevel restLevels flag rest
              (HasTypeDescPi.masterSubjectReductionFromPiValidity piValidityTransfers headTyped
                wellFormed headAfter headStep) ?_
            exact DescTelescopePi.convTelescopeWfOfPiValidity piValidityTransfers restTyped
              (WfContextDescPi.cons wellFormed ⟨headLevel, flag, headTyped⟩)
              (context.cons headAfter)
              (convContextCondition_consStep ⟨headAfter, StepStar.single headStep, StepStar.refl _⟩)
        | there _head restStep =>
            rename_i restAfter
            exact DescTelescopePi.cons context head headLevel restLevels flag restAfter headTyped
              (DescTelescopePi.subjectReductionFromPiValidity piValidityTransfers restTyped
                (WfContextDescPi.cons wellFormed ⟨headLevel, flag, headTyped⟩) restAfter restStep)

end

/-- **The grown mutual fundamental-metatheory bundle, conditional on the single residual** (GTL-20).  The
ONE obligation `ConvContextPreservesPiValidity` discharges BOTH open grown-metatheory release blockers at
once: grown context-conversion (GrownCtxConv-5, `#842`) AND the grown master subject reduction (SRD-2, `#845` /
SN-055).  The explicit statement that the two frontier tasks share a single residual — the precise,
green, zero-axiom hand-off for either the syntactic discharge (GTL-21) or the semantic/reducibility
route. -/
theorem HasTypeDescPi.grownMutualMetatheoryFromPiValidity {profile : PolyProfile}
    (piValidityTransfers : ConvContextPreservesPiValidity profile) :
    (∀ {scope : Nat} {sourceContext : TypingContext profile scope} {subject classifier : RawTerm scope},
        WfContextDescPi sourceContext →
        HasTypeDescPi profile sourceContext subject classifier →
        ∀ targetContext : TypingContext profile scope,
          (∀ index : Fin scope, Conv (sourceContext.lookup index) (targetContext.lookup index)) →
          ∃ classifier', Conv classifier classifier' ∧
            HasTypeDescPi profile targetContext subject classifier')
      ∧ (∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope},
          HasTypeDescPi profile context subject classifier →
          WfContextDescPi context →
          ∀ reduct : RawTerm scope, Step subject reduct →
            HasTypeDescPi profile context reduct classifier) :=
  ⟨fun wf derivation targetContext contextConv =>
      HasTypeDescPi.grownContextConversionFromPiValidity piValidityTransfers wf derivation
        targetContext contextConv,
   fun derivation wf reduct step =>
      HasTypeDescPi.masterSubjectReductionFromPiValidity piValidityTransfers derivation wf reduct step⟩

end FX1Poly.Typed
