import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.HasTypeDescSubjectReduction

/-! # FX1Poly/Typed/HasTypeDescPiSubjectReductionConvOfFormationArms
    — the two remaining (non-function-space, non-former) routing arms of the grown SR dispatcher (SN-055)

The grown-engine subject-reduction dispatcher `HasTypeDescPi Γ s S → Step s s' → HasTypeDescPi Γ s' S` inducts
on the typing derivation; its FIVE arms route a `Step` at each typing head to the right reconstruction.  Three
arms are shipped elsewhere — λ (`subjectReductionPiIntroArm`), application (`subjectReductionPiElimArm`), and
the Π/Σ former (`subjectReductionPiFormerArm` / `subjectReductionSigmaFormerArm`).  This file ships the
remaining two, both trivial (no children-SR, no `WfContext`):

  * **`subjectReductionAtOfFormation`** — a FORMATION-typed subject admits NO step (`subjectAdmitsNoStep`: the
    formation engine types only normal forms), so the dispatcher's `ofFormation` case is vacuous (`absurd`).
  * **`subjectReductionAtConv`** — the `conv` rule's subject is the inner derivation's subject; given the inner
    reduct's typing (the recursive call's output), re-wrap it at the reclassifier via the `conv` constructor.

With these the per-arm ROUTING set is complete (all five typing arms have a routing lemma).

## Dispatcher-assembly status (the genuine blocker, sharpened)

The remaining work — actually CLOSING the recursive dispatcher `HasTypeDescPi.subjectReduction` — is NOT a
clean single brick: it is blocked on the fundamental-metatheory bundle, NOT merely on the `genFormationPi`
former arm.  The recursive `piIntro` / `piElim` arms must thread a context-well-formedness witness through the
structural recursion, but the shipped routing arms (`subjectReductionPiElimArm` via `betaSubjectReduction` /
`classifierIsTypeDesc`) consume `WfContext` (the HasType-based well-formedness), whereas a grown `piIntro`
domain typing only yields `WfContextDescPi` (the grown well-formedness) — the `HasTypeDescPi → IsType` bridge
that `WfContext.cons` needs does not exist (see `WfContextDescPi.lean` header).  So the dispatcher requires
either (a) `WfContextDescPi`-form routing arms, which need grown classifier-validity (WFG-3, `#857`,
itself entangled with `HasType.classifierIsType`), or (b) the bridge.  The SR dispatcher (SN-055), GCC
context-conversion (`#838`-`#843`), and WFG-3 are one mutually-entangled bundle — a deliberate multi-fire
mutual development, with no isolated clean entry point.

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
