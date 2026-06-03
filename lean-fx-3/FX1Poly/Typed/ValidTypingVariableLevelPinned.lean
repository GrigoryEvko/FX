import FX1Poly.Typed.ValidTyping
import FX1Poly.Typed.UniverseCodeShape

/-! # FX1Poly/Typed/ValidTypingVariableLevelPinned
    — a variable's typing level is PINNED, and the type-variable obstruction it witnesses (SN-027, #662)

This file pins a load-bearing NEGATIVE finding about the refined-motive total-bridge route (SN-027): the refined
motive's level-flexibility conjunct (`∀ level, ValidTyping … (level+1) …`) is UNSATISFIABLE for a bare type
VARIABLE, so the refined-motive-via-`ValidTyping` induction cannot, on its own, close the dependent assembly's
neutral cases.  The neutral type-codes (a type variable, and — by the matching `piElim` finding — a type-family
application) must instead route through the reducibility-layer all-levels machinery (`consTypeVariable` /
`ReducibleTypeAtAllLevelsPiNeutralDomain`), exactly as `LevelingBridge.lean`'s SN-025 deferral already planned.

## The inversion

`validTypingVariableLevelPinned` — a `ValidTyping` derivation whose subject is `variableCell index` types it at
EXACTLY the level `contextLevels index`, regardless of the classifier.  Proof by induction on the derivation:

* `var` pins the level to `contextLevels index` directly (subject-index injectivity);
* `conv` preserves the level (its output level is its sub-derivation's level), so the IH closes it;
* every other constructor produces a subject with a DIFFERENT head generator (`gen_universeCode` / `gen_lam` /
  `gen_app` / `gen_piTyCode` / `gen_sigmaTyCode`, refuted by `headGenerator`; the generic `genFormationPi` would
  force its generator to be `gen_var`, contradicting `typingRuleDescOf gen_var = none`).

## The obstruction it witnesses

`typeVariableNotLevelFlexible` — a type variable (`context.lookup index = universeCodeCell levelExpr flag`)
cannot be level-flexible: instantiating the would-be `∀ level` flexibility at `level := contextLevels index`
gives, via the inversion, `contextLevels index + 1 = contextLevels index` — refuted by `Nat.succ_ne_self`.  This
is exactly the refined motive's conjunct-2 obligation for a type variable, so it cannot be discharged at the
`ValidTyping` layer.  (The matching obstruction for a type-family application is the `piElim`
finding in `ValidTypingTermArms.lean`.)

**Consequence for the assembly (#662):** the total-bridge induction's neutral type-code cases (var-at-universe,
type-family app) do NOT produce `ValidTyping` all-level flexibility; they route through the reducibility env at the
single conv-coordinated level (the conv consumer needs only ONE level — see
`validTypingBridgeConvFromAllLevelReclassifier`).  The shipped refined-motive arms remain correct building blocks
for the FORMER and value-subject cases.

## Zero-axiom verification

The inversion uses `injection` (propext-free subject-index extraction), `congrArg RawTerm.headGenerator` +
`decide` on `Generator` disequalities, and `nomatch` on `none = some _`; the corollary is one application of
`Nat.succ_ne_self`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- **A variable's typing level is pinned.**  Any `ValidTyping` derivation whose subject is `variableCell index`
types it at exactly `contextLevels index` — `var` fixes it, `conv` preserves it, and every other constructor
produces a subject with a distinct head generator. -/
theorem validTypingVariableLevelPinned {profile : PolyProfile} {scope : Nat}
    {contextLevels : Fin scope → Nat} {level : Nat} {context : TypingContext profile scope}
    {index : Fin scope} {classifier : RawTerm scope}
    (typed : ValidTyping profile contextLevels level context (variableCell index) classifier) :
    level = contextLevels index := by
  generalize subjectEq : variableCell index = subject at typed
  induction typed with
  | var armContextLevels armContext armIndex =>
      have indexEq : index = armIndex := by
        injection (show RawTerm.mkGen Generator.gen_var index RawTermChildren.childNil
                    = RawTerm.mkGen Generator.gen_var armIndex RawTermChildren.childNil from subjectEq) with eq1
      rw [indexEq]
  | conv armContextLevels armSubjectLevel _typedSub _converts _reclassifierTyped typedIH _reclassifierIH =>
      exact typedIH subjectEq
  | universeFormation _ _ _ _ _ =>
      exfalso
      have hg : Generator.gen_var = Generator.gen_universeCode := congrArg RawTerm.headGenerator subjectEq
      exact absurd hg (by decide)
  | piIntro _ _ _ _ _ _ =>
      exfalso
      have hg : Generator.gen_var = Generator.gen_lam := congrArg RawTerm.headGenerator subjectEq
      exact absurd hg (by decide)
  | piElim _ _ _ _ =>
      exfalso
      have hg : Generator.gen_var = Generator.gen_app := congrArg RawTerm.headGenerator subjectEq
      exact absurd hg (by decide)
  | piFormation _ _ _ _ =>
      exfalso
      have hg : Generator.gen_var = Generator.gen_piTyCode := congrArg RawTerm.headGenerator subjectEq
      exact absurd hg (by decide)
  | sigmaFormation _ _ _ _ =>
      exfalso
      have hg : Generator.gen_var = Generator.gen_sigmaTyCode := congrArg RawTerm.headGenerator subjectEq
      exact absurd hg (by decide)
  | genFormationPi _ _ armGenerator _ armIsFormation _ _ =>
      have hg : Generator.gen_var = armGenerator := congrArg RawTerm.headGenerator subjectEq
      rw [← hg, show typingRuleDescOf Generator.gen_var = none from rfl] at armIsFormation
      nomatch armIsFormation

/-- **A type variable is not level-flexible** — the formal obstruction to the refined-motive route's conjunct-2.
A variable whose looked-up type is a universe code cannot be valid at every level `level + 1`: instantiating the
would-be flexibility at `contextLevels index` and applying the level-pinning gives `contextLevels index + 1 =
contextLevels index`, refuted by `Nat.succ_ne_self`.  Hence the assembly routes type variables through the
reducibility env, not `ValidTyping` all-level flexibility. -/
theorem typeVariableNotLevelFlexible {profile : PolyProfile} {scope : Nat}
    {contextLevels : Fin scope → Nat} {context : TypingContext profile scope}
    {index : Fin scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (flexible : ∀ level : Nat,
      ValidTyping profile contextLevels (level + 1) context
        (variableCell index) (universeCodeCell levelExpr flag)) :
    False :=
  Nat.succ_ne_self (contextLevels index)
    (validTypingVariableLevelPinned (flexible (contextLevels index)))

end FX1Poly.Typed
