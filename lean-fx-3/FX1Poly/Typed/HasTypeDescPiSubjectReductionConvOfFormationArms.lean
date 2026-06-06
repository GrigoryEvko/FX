import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.HasTypeDescSubjectReduction

/-! # FX1Poly/Typed/HasTypeDescPiSubjectReductionConvOfFormationArms
    — the two remaining (non-function-space, non-former) routing arms of the grown SR dispatcher

The grown-engine subject-reduction dispatcher `HasTypeDescPi Γ s S → Step s s' → HasTypeDescPi Γ s' S` inducts
on the typing derivation; its FIVE arms route a `Step` at each typing head to the right reconstruction.  Three
arms live elsewhere — λ (`subjectReductionPiIntroArm`), application (`subjectReductionPiElimArm`), and
the Π/Σ former (`subjectReductionPiFormerArm` / `subjectReductionSigmaFormerArm`).  This file ships the
remaining two, both trivial (no children-SR, no well-formedness use):

  * **`subjectReductionAtOfFormation`** — a FORMATION-typed subject admits NO step (`subjectAdmitsNoStep`: the
    formation engine types only normal forms), so the dispatcher's `ofFormation` case is vacuous (`absurd`).
  * **`subjectReductionAtConv`** — the `conv` rule's subject is the inner derivation's subject; given the inner
    reduct's typing (the recursive call's output), re-wrap it at the reclassifier via the `conv` constructor.

With these the per-arm ROUTING set is complete (all five typing arms have a routing lemma).

## Dispatcher-assembly status

Closing the recursive dispatcher `HasTypeDescPi.subjectReduction` is the fundamental-metatheory bundle, not a
clean single brick.  The recursive `piIntro` / `piElim` arms thread a context-well-formedness witness through
the structural recursion via the grown `WfContextDescPi`, which extends at a grown `piIntro` binder
(`WfContextDescPi.cons` + the binder's domain typing IS its `IsTypeDescPi`).  The SR dispatcher, the grown
context-conversion bundle, and grown classifier-validity are one mutually-entangled bundle — a deliberate
multi-fire mutual development.

## Zero-axiom verification

`subjectAdmitsNoStep` (`absurd`) + the `conv` constructor.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **SR routing arm at an `ofFormation` subject.**  A formation-typed subject admits no `Step`
(`HasTypeDesc.subjectAdmitsNoStep`: the formation engine types only normal forms), so any reduct claim follows
vacuously.  The dispatcher's `ofFormation` case. -/
theorem HasTypeDescPi.subjectReductionAtOfFormation {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier reduct : RawTerm scope}
    (formationTyped : HasTypeDesc profile context subject classifier)
    (step : Step subject reduct) :
    HasTypeDescPi profile context reduct classifier :=
  absurd step (formationTyped.subjectAdmitsNoStep reduct)

/-- **SR routing arm at a `conv` subject.**  The `conv` rule leaves the subject unchanged and re-classifies it;
given the inner reduct's typing at the original classifier (the recursive SR call's result), re-wrap at the
reclassifier via the `conv` constructor.  The dispatcher's `conv` case. -/
theorem HasTypeDescPi.subjectReductionAtConv {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {reduct reclassifier classifier : RawTerm scope}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (innerReductTyped : HasTypeDescPi profile context reduct classifier)
    (converts : Conv classifier reclassifier)
    (reclassifierTyped : HasTypeDescPi profile context reclassifier
      (universeCodeCell levelExpr flag)) :
    HasTypeDescPi profile context reduct reclassifier :=
  HasTypeDescPi.conv levelExpr flag innerReductTyped converts reclassifierTyped

end FX1Poly.Typed
