import FX1Poly.Typed.Metatheory.SubjectReduction.ElimObligationsDrift

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/CleanElimObligationsDrift
    — SR-DSL-4: build `ObligationsDrift` from an arg step for the CLEAN eliminators (no binder-extended branches)

The context-fixed driver `premisesHoldUnderObligationsDrift` needs the positional `ObligationsDrift` between an
eliminator's obligations at `args` and at `argsAfter`.  For the CLEAN eliminators — `app` / `pathApp` / `fst` /
`snd` — every obligation's classifier reads only the type-index PARAMS (which a child step leaves fixed) and the
context is the ambient context (no binder extension), so when one arg steps the obligation drift is exactly:
the obligation whose SUBJECT is the stepping arg gets a single-step subject drift, every other obligation is
literally unchanged, and no classifier drifts.  This is `ObligationsDrift` with `StepStar.single` at the stepping
position and `StepStar.refl` everywhere else.

This file ships that construction for `app` (the canonical two-premise eliminator), end-to-end through the
shipped substrate: `cases` the `StepChildren` to find the stepping arg, then assemble the `ObligationsDrift`
spine.  It validates the whole SR-DSL-4 pipeline (gate input → drift → driver) on a real rule and is the template
the remaining clean rows (`pathApp` / `fst` / `snd`) follow.

The two classifier-formedness witnesses (`functionClassifierFormed` / `argumentClassifierFormed`) are what the
gate supplies via `classifierIsType` over `WfContextUnion` — they are NOT re-derived here.

## Zero-axiom

`cases` on the (mutual-inductive) `StepChildren` + `StepStar.single` / `StepStar.refl` + the `ObligationsDrift`
constructors.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **`app`'s obligation drift under one arg step.**  When one of `app`'s two children (`function` / `argument`)
steps, the obligation list `appElimRule.obligations … (function, argument) …` drifts to the list at the stepped
children by `ObligationsDrift`: the stepping child's obligation gets a `StepStar.single` subject drift, the other
is unchanged, and neither classifier (`piTyCodeCell domainCode codomainCode` / `domainCode`) moves — both read only
the fixed params.  `cases` the `StepChildren` into the three positions (function steps / argument steps / the empty
tail, vacuous). -/
theorem appObligationsDriftUnderArgStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {function argument : RawTerm scope} {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (functionClassifierFormed : UnionClassifierIsType profile context (piTyCodeCell domainCode codomainCode))
    (argumentClassifierFormed : UnionClassifierIsType profile context domainCode)
    {argsAfter : RawTermChildren [0, 0] scope}
    (childStep : StepChildren
      (.childCons function (.childCons argument .childNil) : RawTermChildren [0, 0] scope) argsAfter) :
    ObligationsDrift profile
      (appElimRule.obligations scope context
        (.childCons function (.childCons argument .childNil))
        (.childCons domainCode (.childCons codomainCode .childNil)) level0 level1 flag)
      (appElimRule.obligations scope context argsAfter
        (.childCons domainCode (.childCons codomainCode .childNil)) level0 level1 flag) := by
  cases childStep with
  | here _ functionStep =>
      exact ObligationsDrift.cons (StepStar.single functionStep) (StepStar.refl _) functionClassifierFormed
        (ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) argumentClassifierFormed ObligationsDrift.nil)
  | there _ tailStep =>
      cases tailStep with
      | here _ argumentStep =>
          exact ObligationsDrift.cons (StepStar.refl _) (StepStar.refl _) functionClassifierFormed
            (ObligationsDrift.cons (StepStar.single argumentStep) (StepStar.refl _) argumentClassifierFormed
              ObligationsDrift.nil)
      | there _ emptyTailStep => cases emptyTailStep

end FX1Poly.Typed
