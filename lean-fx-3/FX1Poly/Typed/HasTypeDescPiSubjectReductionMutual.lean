import FX1Poly.Typed.HasTypeDescPiSubjectReductionDescPi
import FX1Poly.Typed.HasTypeDescPiSubjectReductionInlineArms
import FX1Poly.Typed.HasTypeDescPiSubjectReductionConvOfFormationArms
import FX1Poly.Typed.HasTypeDescSubjectReduction
import FX1Poly.Typed.HasTypeDescPiContextConversionConditional

/-! # FX1Poly/Typed/HasTypeDescPiSubjectReductionMutual
    — the grown-engine master subject reduction ⋈ grown telescope SR, conditional on the SINGLE piElim crux
      (SRD-2 / SRD-4, SN-055)

`HasTypeDescPiSubjectReduction.lean` (SRD-1) shipped the master SR dispatcher conditional on the grown TELESCOPE
SR as an explicit hypothesis.  This file DISCHARGES that hypothesis by proving the telescope SR as the mutual
companion of the dispatcher — leaving a single, sharper residual: the grown context-conversion `piElim` arm
(GrownCtxConv-5), which is ALSO the lone residual of `HasTypeDescPiContextConversionConditional.lean`.  So the entire
grown subject-reduction metatheory is now conditional on the SAME ONE lemma as the grown context-conversion: the
mutual fundamental-metatheory crux (type-correctness + Π-injectivity + SR + context-conversion proven together).

The pair `HasTypeDescPi.subjectReductionOfPiElimArm ⋈ DescTelescopePi.subjectReductionOfPiElimArm` mirrors the
formation `HasTypeDesc.subjectReduction ⋈ DescTelescope.subjectReduction` exactly, with three grown upgrades:
the well-formedness is the EXTENDABLE `WfContextDescPi` (reaches under a grown `piIntro` binder); the `piIntro` /
`piElim` arms use the shipped grown function-space SR arms (`subjectReductionPiIntroArm` /
`subjectReductionPiElimArmDescPi`); and the telescope `here` arm re-types the tail under the stepped head via the
grown telescope context-conversion `DescTelescopePi.convTelescopeOfPiElimArm` (which carries the `piElim` arm).

  * **`HasTypeDescPi.subjectReductionOfPiElimArm`** — the master dispatcher.  `ofFormation` vacuous
    (`subjectAdmitsNoStep`); `conv` recurses; `piIntro` / `piElim` use the function-space arms with the children's
    SR obtained from the recursive call (extending `WfContextDescPi` at the λ binder); `genFormationPi`
    decomposes via `former_step_inv` and re-types the premise telescope via the mutual telescope SR.
  * **`DescTelescopePi.subjectReductionOfPiElimArm`** — the telescope SR.  `cons`/`here` (head steps): re-type
    the head via the mutual dispatcher, then re-type the tail under the stepped head via
    `convTelescopeOfPiElimArm` + `convContextCondition_consStep`; `cons`/`there` (a tail child steps): recurse
    under the extended `WfContextDescPi`.

Note the argument order `(telescope) (wellFormed)` (telescope BEFORE well-formedness) — required for Lean's
mutual-recursion implicit inference (the telescope determines all the `levels`/`flag`/`children` implicits; a
leading `wellFormed` only partially does, leaving the recursive call's implicits as metavariables).

## Zero-axiom verification

Mutual structural recursion on the derivation / telescope + the shipped per-arm SR lemmas
(`subjectReductionPiIntroArm` / `subjectReductionPiElimArmDescPi`) + `subjectAdmitsNoStep` + `former_step_inv` +
the grown telescope context-conversion `convTelescopeOfPiElimArm` + `convContextCondition_consStep` +
`WfContextDescPi.cons`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

mutual

/-- **The grown-engine master subject reduction, conditional on the grown context-conversion `piElim` arm.**
A grown-typed subject is preserved under a `Step`, at the SAME classifier, given the lone `piElim`
context-conversion arm (`piElimArm`, the GrownCtxConv-5 fundamental-metatheory crux).  Threads the EXTENDABLE
`WfContextDescPi`; `ofFormation` is vacuous, `conv` recurses, `piIntro` / `piElim` use the shipped
function-space arms with the children's SR obtained recursively, `genFormationPi` re-types its premise telescope
via the mutual `DescTelescopePi.subjectReductionOfPiElimArm`.  Discharging `piElimArm` yields the unconditional
master SR (SN-055). -/
theorem HasTypeDescPi.subjectReductionOfPiElimArm {profile : PolyProfile}
    (piElimArm : ∀ {armScope : Nat} {armSrc : TypingContext profile armScope}
        {fn arg armDomain : RawTerm armScope} {armCodomain : RawTerm (armScope + 1)},
        HasTypeDescPi profile armSrc fn (piTyCodeCell armDomain armCodomain) →
        HasTypeDescPi profile armSrc arg armDomain →
        ∀ armTgt : TypingContext profile armScope,
          (∀ index : Fin armScope, Conv (armSrc.lookup index) (armTgt.lookup index)) →
          ∃ classifier', Conv (RawTerm.subst0 armCodomain arg) classifier' ∧
            HasTypeDescPi profile armTgt (appCell fn arg) classifier')
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
        (HasTypeDescPi.subjectReductionOfPiElimArm piElimArm typed wellFormed reduct step)
        converts reclassifierTyped
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel codomainLevel flag
      domainTyped codomainTyped bodyTyped => fun reduct step =>
      HasTypeDescPi.subjectReductionPiIntroArm domainTyped codomainTyped step
        (fun {bodyReduct} bodyStep =>
          HasTypeDescPi.subjectReductionOfPiElimArm piElimArm bodyTyped
            (WfContextDescPi.cons wellFormed ⟨domainLevel, flag, domainTyped⟩) bodyReduct bodyStep)
  | .piElim functionTyped argumentTyped => fun reduct step =>
      HasTypeDescPi.subjectReductionPiElimArmDescPi functionTyped argumentTyped step
        (fun {functionReduct} functionStep =>
          HasTypeDescPi.subjectReductionOfPiElimArm piElimArm functionTyped wellFormed
            functionReduct functionStep)
        (fun {argumentReduct} argumentStep =>
          HasTypeDescPi.subjectReductionOfPiElimArm piElimArm argumentTyped wellFormed
            argumentReduct argumentStep)
        wellFormed
  | .genFormationPi formerContext generator payload children levels flag rule isFormation premises =>
      fun reduct step => by
      obtain ⟨children', reductEq, stepChildren⟩ := former_step_inv isFormation step
      subst reductEq
      exact HasTypeDescPi.genFormationPi formerContext generator payload children' levels flag rule
        isFormation
        (DescTelescopePi.subjectReductionOfPiElimArm piElimArm premises wellFormed children'
          stepChildren)

/-- **The grown premise-telescope subject reduction** (the mutual companion).  A grown premise telescope is
preserved under a child `Step`.  `cons`/`here` (the binding head steps): re-type the head via the mutual
dispatcher, then re-type the tail under the stepped binding via the grown telescope context-conversion
`convTelescopeOfPiElimArm` (with `convContextCondition_consStep` supplying the `cons head ⤳ cons headAfter`
context-condition); `cons`/`there` (a tail child steps): recurse under the extended `WfContextDescPi`. -/
theorem DescTelescopePi.subjectReductionOfPiElimArm {profile : PolyProfile}
    (piElimArm : ∀ {armScope : Nat} {armSrc : TypingContext profile armScope}
        {fn arg armDomain : RawTerm armScope} {armCodomain : RawTerm (armScope + 1)},
        HasTypeDescPi profile armSrc fn (piTyCodeCell armDomain armCodomain) →
        HasTypeDescPi profile armSrc arg armDomain →
        ∀ armTgt : TypingContext profile armScope,
          (∀ index : Fin armScope, Conv (armSrc.lookup index) (armTgt.lookup index)) →
          ∃ classifier', Conv (RawTerm.subst0 armCodomain arg) classifier' ∧
            HasTypeDescPi profile armTgt (appCell fn arg) classifier')
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
              (HasTypeDescPi.subjectReductionOfPiElimArm piElimArm headTyped wellFormed headAfter
                headStep) ?_
            exact DescTelescopePi.convTelescopeOfPiElimArm piElimArm restTyped
              (context.cons headAfter)
              (convContextCondition_consStep ⟨headAfter, StepStar.single headStep, StepStar.refl _⟩)
        | there _head restStep =>
            rename_i restAfter
            exact DescTelescopePi.cons context head headLevel restLevels flag restAfter headTyped
              (DescTelescopePi.subjectReductionOfPiElimArm piElimArm restTyped
                (WfContextDescPi.cons wellFormed ⟨headLevel, flag, headTyped⟩) restAfter restStep)

end

end FX1Poly.Typed
