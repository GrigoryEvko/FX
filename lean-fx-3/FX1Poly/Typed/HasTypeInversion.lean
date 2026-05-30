import FX1Poly.Typed.HasTypeValidity
import FX1Poly.Typed.HasTypeStronglyNormalizing
import FX1Poly.Typed.HasTypeHonesty

/-! # FX1Poly/Typed/HasTypeInversion — per-shape typing inversion (#454)

Inversion characterizes the classifier of a well-typed cell *up to
conversion*: whatever type a variable cell is given, that type is convertible
to the variable's principal type (its context lookup); likewise a universe-code
cell's type is convertible to the next universe.  These are the lemmas
uniqueness-of-typing (#469) consumes — they let two derivations of the same
subject be compared through a shared principal type.

## Proof shape (equation-motive, not `cases`)

A variable subject `variableCell idx = mkGen gen_var idx childNil` is a
*compound constructor index* of `HasType`; inverting it with `cases`/`induction`
directly would leak `propext` through the match compiler's equation lemmas.  So
each inversion generalizes the subject to a free variable and threads an
explicit `subject = variableCell idx` equation, moving all constructor
discrimination onto a plain `Eq`: `injection` extracts the payload in the
matching arm, and `congrArg RawTerm.headGenerator` refutes the impossible arm
by generator mismatch.

The `conv` arm is the load-bearing one: it rewrites the classifier, so the
induction hypothesis is collapsed through the premise's classifier, which is a
type by validity (`HasType.classifierIsType`, needing `WfContext`) and hence a
legal Newman middle for `Conv.trans_of_typedMiddle`.

## Zero-axiom verification

Equation-motive induction + `injection` (propext-free) + the head-generator
refutation + the proven typed `Conv.trans`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Inversion for a variable cell.**  Any classifier a variable cell receives
is convertible to the variable's principal type (its context lookup).  Needs
`WfContext` so the `conv` arm's intermediate classifier is a type (validity)
and therefore strongly normalizing — a legal middle for the typed Newman
bridge. -/
theorem HasType.inversionVariable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (wellFormed : WfContext context)
    {index : Fin scope} {classifier : RawTerm scope}
    (typed : HasType profile context (variableCell index) classifier) :
    Conv classifier (context.lookup index) := by
  suffices general :
      ∀ {subject reachedClassifier : RawTerm scope},
        HasType profile context subject reachedClassifier →
          ∀ {targetIndex : Fin scope}, subject = variableCell targetIndex →
            Conv reachedClassifier (context.lookup targetIndex) from
    general typed rfl
  intro subject reachedClassifier derivation
  induction derivation with
  | var armIndex =>
      intro targetIndex subjectEq
      have indicesAgree : armIndex = targetIndex := by
        injection subjectEq
      subst indicesAgree
      exact Conv.refl _
  | conv levelExpr flag typedPremise converts reclassifierTyped
      ihPremise _ihReclassifier =>
      intro targetIndex subjectEq
      exact Conv.trans_of_typedMiddle
        (HasType.classifierIsType wellFormed typedPremise)
        converts.sym
        (ihPremise subjectEq)
  | universeFormation armLevel armFlag =>
      intro targetIndex subjectEq
      have headGeneratorsAgree :
          Generator.gen_universeCode = Generator.gen_var :=
        congrArg RawTerm.headGenerator subjectEq
      exact Generator.noConfusion headGeneratorsAgree

/-- **Inversion for a universe-code cell.**  Any classifier a universe-code
cell `Type@(e, flag)` receives is convertible to the next universe
`Type@(e+1, flag)`.  Mirror of `inversionVariable`: the `var` arm is the
impossible one (refuted by generator mismatch), and `universeFormation` lands
the principal type by reflexivity. -/
theorem HasType.inversionUniverseCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (wellFormed : WfContext context)
    {levelExpr : LevelExpr} {flag : UniverseFlag} {classifier : RawTerm scope}
    (typed :
      HasType profile context (universeCodeCell levelExpr flag) classifier) :
    Conv classifier (universeCodeCell levelExpr.lsucc flag) := by
  suffices general :
      ∀ {subject reachedClassifier : RawTerm scope},
        HasType profile context subject reachedClassifier →
          ∀ {targetLevel : LevelExpr} {targetFlag : UniverseFlag},
            subject = universeCodeCell targetLevel targetFlag →
              Conv reachedClassifier
                (universeCodeCell targetLevel.lsucc targetFlag) from
    general typed rfl
  intro subject reachedClassifier derivation
  induction derivation with
  | var armIndex =>
      intro targetLevel targetFlag subjectEq
      have headGeneratorsAgree :
          Generator.gen_var = Generator.gen_universeCode :=
        congrArg RawTerm.headGenerator subjectEq
      exact Generator.noConfusion headGeneratorsAgree
  | conv levelExprArm flagArm typedPremise converts reclassifierTyped
      ihPremise _ihReclassifier =>
      intro targetLevel targetFlag subjectEq
      exact Conv.trans_of_typedMiddle
        (HasType.classifierIsType wellFormed typedPremise)
        converts.sym
        (ihPremise subjectEq)
  | universeFormation armLevel armFlag =>
      intro targetLevel targetFlag subjectEq
      have payloadEq : (armLevel, armFlag) = (targetLevel, targetFlag) := by
        injection subjectEq
      injection payloadEq with levelAgree flagAgree
      subst levelAgree
      subst flagAgree
      exact Conv.refl _

end FX1Poly.Typed
