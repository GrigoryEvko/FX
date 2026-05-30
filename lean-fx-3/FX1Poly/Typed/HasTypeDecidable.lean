import FX1Poly.Typed.IsTypeDecidable

/-! # FX1Poly/Typed/HasTypeDecidable
    — typed checking collapses to classifier equality (current fragment)

On the current `HasType` fragment (`var` / `conv` / `universeFormation`), deciding
`HasType context subject classifier` does NOT require a `Conv` decision: validity
(`HasType.classifierIsType`) makes every classifier an `IsType`, hence a
non-stepping normal leaf, and the per-shape inversions hand back a `Conv` to
another normal cell — so normal-form rigidity (`Conv.eq_of_isType`) collapses the
whole judgment to *syntactic equality of the classifier*:

* `HasType context (variableCell i) classifier ↔ classifier = context.lookup i`
  (`HasType.variableCell_iff_classifierEqLookup`);
* `HasType context (universeCodeCell e f) classifier
   ↔ classifier = universeCodeCell e.lsucc f`
  (`HasType.universeCodeCell_iff_classifierEqSucc`);
* a subject whose head is neither `gen_var` nor `gen_universeCode` is never typed
  (`HasType.not_of_headGenerator`).

These are the full content of `Decidable (HasType …)` (#461) for this fragment —
the decision procedure then assembles them over `DecidableEq RawTerm`, with no
normalizer (the feared general-`Conv` / NbE dependency never arises, because a
non-type classifier is exactly the no-derivation case).

## Zero-axiom verification

Forward directions rest on `classifierIsType` + the inversions + rigidity
(`Conv.eq_of_isType`), all zero-axiom; backward directions `subst` the classifier
equality and apply the `var` / `universeFormation` rule.  The refutation reuses
`typedSubjectIsVariableOrUniverseCode` + the concrete-cell head computations.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- `variableCell index` is typed by exactly its looked-up classifier (and
nothing else): forward by `inversionVariable` + validity + rigidity, backward by
the `var` rule.  No `Conv` decision survives — both `classifier` (validity) and
`context.lookup index` (well-formedness) are normal, so the convertibility
becomes an equality. -/
theorem HasType.variableCell_iff_classifierEqLookup {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    (wellFormed : WfContext context) (index : Fin scope)
    (classifier : RawTerm scope) :
    HasType profile context (variableCell index) classifier
      ↔ classifier = context.lookup index := by
  constructor
  · intro typed
    have converts : Conv classifier (context.lookup index) :=
      HasType.inversionVariable wellFormed typed
    have classifierIsType : IsType profile context classifier :=
      HasType.classifierIsType wellFormed typed
    have lookupIsType : IsType profile context (context.lookup index) :=
      WfContext.lookupIsType context wellFormed index
    exact Conv.eq_of_isType classifierIsType lookupIsType converts
  · intro classifierEqualsLookup
    subst classifierEqualsLookup
    exact HasType.var context index

/-- A universe-code cell `universeCodeCell e flag` is typed by exactly the next
universe `universeCodeCell e.lsucc flag` (and nothing else): forward by
`inversionUniverseCode` + validity + rigidity, backward by `universeFormation`. -/
theorem HasType.universeCodeCell_iff_classifierEqSucc {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    (wellFormed : WfContext context) (levelExpr : LevelExpr) (flag : UniverseFlag)
    (classifier : RawTerm scope) :
    HasType profile context (universeCodeCell levelExpr flag) classifier
      ↔ classifier = universeCodeCell levelExpr.lsucc flag := by
  constructor
  · intro typed
    have converts :
        Conv classifier (universeCodeCell levelExpr.lsucc flag) :=
      HasType.inversionUniverseCode wellFormed typed
    have classifierIsType : IsType profile context classifier :=
      HasType.classifierIsType wellFormed typed
    have succIsType :
        IsType profile context (universeCodeCell levelExpr.lsucc flag) :=
      IsType.ofUniverseCodeCell levelExpr.lsucc flag
    exact Conv.eq_of_isType classifierIsType succIsType converts
  · intro classifierEqualsSucc
    subst classifierEqualsSucc
    exact HasType.universeFormation context levelExpr flag

/-- A subject whose head generator is neither `gen_var` nor `gen_universeCode`
has no typing derivation under any classifier: every typed subject is a variable
or universe-code cell (`typedSubjectIsVariableOrUniverseCode`). -/
theorem HasType.not_of_headGenerator {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (notVariable : RawTerm.headGenerator subject ≠ Generator.gen_var)
    (notUniverseCode :
      RawTerm.headGenerator subject ≠ Generator.gen_universeCode) :
    ¬ HasType profile context subject classifier := by
  intro typed
  rcases typed.typedSubjectIsVariableOrUniverseCode with
    ⟨index, subjectIsVariable⟩ | ⟨codeLevel, codeFlag, subjectIsUniverseCode⟩
  · subst subjectIsVariable
    exact notVariable (headGenerator_variableCell index)
  · subst subjectIsUniverseCode
    exact notUniverseCode (headGenerator_universeCodeCell codeLevel codeFlag)

end FX1Poly.Typed
