import FX1Poly.Typed.HasTypeDescPiSubjectReductionDescPi
import FX1Poly.Typed.HasTypeDescPiSubjectReductionInlineArms
import FX1Poly.Typed.HasTypeDescPiSubjectReductionConvOfFormationArms
import FX1Poly.Typed.HasTypeDescSubjectReduction
import FX1Poly.Typed.SubjectReductionAtFormerGeneric

/-! # FX1Poly/Typed/HasTypeDescPiSubjectReduction
    — the master subject-reduction dispatcher for the GROWN engine, conditional on the grown telescope SR

The grown engine `HasTypeDescPi` adds λ (`piIntro`) and application (`piElim`) over the formation engine.  Its
subject reduction `HasTypeDescPi Γ subject classifier → Step subject reduct → HasTypeDescPi Γ reduct classifier`
inducts on the typing derivation, with the well-formedness threaded as the EXTENDABLE `WfContextDescPi`
so it can reach under a grown `piIntro` binder; `WfContextDescPi.cons` extends because the binder's domain
typing IS its `IsTypeDescPi`.

Every arm is assembled here except the `genFormationPi` case (a grown former `mkGen generator () children`, whose
children are grown-typed and so CAN step — unlike the formation engine, whose formers have formation-typed,
hence normal, children).  That case is ROUTED through the ONE table-generic former arm
`subjectReductionAtFormerGeneric` — which decomposes the step (root-redex-free over the formation
family) and re-types the premise telescope — which needs the grown telescope SR
`DescTelescopePi.subjectReduction`, itself gated on grown telescope context-conversion (`DescTelescopePi.
convTelescope`).  So this file ships the dispatcher with that grown telescope SR as the LONE explicit hypothesis
(`telescopeSR`): bundle the assembled machinery, expose the single residual.  Discharging `telescopeSR` once
grown context-conversion lands yields the unconditional master SR.

## The arms (assembled here)

  * **`ofFormation`** — VACUOUS: a formation-typed subject admits no step (`HasTypeDesc.subjectAdmitsNoStep`;
    the formation engine types only normal forms), so `absurd step (subjectAdmitsNoStep _)`.
  * **`conv`** — re-type the premise recursively (same subject, same context), re-wrap at the reclassifier.
  * **`piIntro`** — `subjectReductionPiIntroArm` with the body SR obtained recursively under the EXTENDED
    `WfContextDescPi.cons wellFormed (domain's IsTypeDescPi)`.
  * **`piElim`** — `subjectReductionPiElimArmDescPi` with the function / argument SR obtained recursively, plus
    `wellFormed` (the grown β / output-move classifier validity).
  * **`genFormationPi`** — routed through the ONE table-generic `subjectReductionAtFormerGeneric`: it
    decomposes the former step, re-types the premise telescope via the `telescopeSR` hypothesis, and
    reassembles via the generic `genFormationPi`.  The dispatcher names NO formation generator, so a new
    formation row is absorbed by that single arm (the cascade-free design).

## Zero-axiom verification

Structural recursion on the derivation (recursive calls under the arm closures) + the shipped per-arm SR lemmas
+ `subjectAdmitsNoStep` + the table-generic `subjectReductionAtFormerGeneric` + `WfContextDescPi.cons`.  No
`axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The master subject-reduction dispatcher for the grown engine, conditional on the grown telescope SR.**
A grown-typed subject is preserved under a `Step`, at the SAME classifier, given the grown telescope SR
`telescopeSR` (re-typing a premise telescope under a child step — the lone GCC-gated residual).  Inducts on the
derivation, threading the EXTENDABLE `WfContextDescPi`; `ofFormation` is vacuous (formation subjects are
normal), `conv` recurses, `piIntro` / `piElim` use the function-space arms with the children's SR
obtained recursively (extending well-formedness at the λ binder), `genFormationPi` routes through the
table-generic `subjectReductionAtFormerGeneric`, re-typing the telescope via `telescopeSR`.  Discharging
`telescopeSR` (once grown context-conversion lands) yields the unconditional master SR. -/
theorem HasTypeDescPi.subjectReductionOfGrownTelescopeSR {profile : PolyProfile}
    (telescopeSR : ∀ {baseScope currentDepth : Nat} {binderShifts : List Nat}
        {telescopeContext : TypingContext profile (baseScope + currentDepth)}
        {levels : List LevelExpr} {flag : UniverseFlag}
        {children : RawTermChildren binderShifts baseScope},
        DescTelescopePi profile telescopeContext levels flag children →
        ∀ children' : RawTermChildren binderShifts baseScope,
          StepChildren children children' →
          DescTelescopePi profile telescopeContext levels flag children')
    {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (derivation : HasTypeDescPi profile context subject classifier) :
    ∀ reduct : RawTerm scope, Step subject reduct →
      HasTypeDescPi profile context reduct classifier :=
  match derivation with
  | .ofFormation formationTyped => fun reduct step =>
      absurd step (formationTyped.subjectAdmitsNoStep reduct)
  | .conv levelExpr flag typed converts reclassifierTyped => fun reduct step =>
      HasTypeDescPi.conv levelExpr flag
        (HasTypeDescPi.subjectReductionOfGrownTelescopeSR telescopeSR wellFormed typed reduct step)
        converts reclassifierTyped
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel _codomainLevel flag
      domainTyped codomainTyped bodyTyped => fun _reduct step =>
      HasTypeDescPi.subjectReductionPiIntroArm domainTyped codomainTyped step
        (fun {bodyReduct} bodyStep =>
          HasTypeDescPi.subjectReductionOfGrownTelescopeSR telescopeSR
            (WfContextDescPi.cons wellFormed ⟨domainLevel, flag, domainTyped⟩)
            bodyTyped bodyReduct bodyStep)
  | .piElim functionTyped argumentTyped => fun _reduct step =>
      HasTypeDescPi.subjectReductionPiElimArmDescPi functionTyped argumentTyped step
        (fun {functionReduct} functionStep =>
          HasTypeDescPi.subjectReductionOfGrownTelescopeSR telescopeSR wellFormed functionTyped
            functionReduct functionStep)
        (fun {argumentReduct} argumentStep =>
          HasTypeDescPi.subjectReductionOfGrownTelescopeSR telescopeSR wellFormed argumentTyped
            argumentReduct argumentStep)
        wellFormed
  | .genFormationPi _formerContext _generator _payload _children _levels _flag _rule isFormation premises =>
      fun _reduct step =>
      HasTypeDescPi.subjectReductionAtFormerGeneric isFormation step
        (fun {childrenAfter} stepChildren => telescopeSR premises childrenAfter stepChildren)

end FX1Poly.Typed
