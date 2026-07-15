import FX1Poly.Typed.Metatheory.Validity.TypedAtUniverseFibrantlyUsable

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/StepPreservesDimensionalSubjectUsability
    — the `.dimensional` usability bridge (the dimensional dual of the `.fibrant` step-preservation theorem)

The fibrant residual `reductUsable` of the SR congruence/gate cascade is discharged UNCONDITIONALLY by
`HasTypeUnion.stepPreservesFibrantSubjectUsability` (for ANY subject type): every reduction-table obligation
is at the FIBRANT modality, so the redex's own branch/argument obligations force every contractum fibrantly
usable.  The `pathApp` ARGUMENT congruence (`pathAppArgumentCongruenceSubjectReduction`) instead defers a
`.dimensional` residual on the stepped interval argument — and that one is NOT the same story.

## Why the dimensional analogue is FALSE unconditionally

`isSubjectUsableAtModality x m` is `true` for any NON-variable `x`, but for a bare variable `var k` it is
`isAccessibleAtModality k m`, and the two modalities are EXCLUSIVE-OR there
(`isSubjectUsableAtModality_var_notBoth`): a `cons`-bound variable is fibrantly usable but NOT dimensionally
usable; only a `lockCons`-bound dimension is dimensionally usable.  Since every reduction-table obligation is
FIBRANT, a contractum that is a `cons`-bound variable is fibrantly usable yet dimensionally UNusable.

Concretely — the interval is an ordinary `Type@0(standard)` (its non-fibrancy is a use-site lock discipline,
NOT a universe/formation restriction), so `Π Bool Interval` forms and is inhabited
(`constantIntervalLambdaNativelyTyped`), `cons intervalTypeCell` is admitted by `WfContextUnion`, and a
`cons`-bound interval variable is FIBRANTLY (not dimensionally) accessible.  Hence, in a context binding the
interval ordinarily,

    app (lam boolTypeCell (var 1)) boolTrue : intervalTypeCell

is a well-typed β-redex, is dimensionally usable (its head `gen_app` is non-variable), and β-reduces to the
`cons`-bound interval dimension variable `var 0` — fibrantly, NOT dimensionally, usable.  So a single `Step`
does NOT preserve `.dimensional` usability in general; the unconditional analogue of the fibrant theorem is
false.

## The precise precondition — the interval-non-fibrancy discipline

The counterexample needs an ORDINARY (`cons`) binding of the interval.  The fibrant bridge rests on
`AllLocksAreInterval` (every `lockCons` IS the interval → `lockedLookupIsInterval`); the dimensional bridge
rests on the DUAL `NoConsBindingIsInterval` (no `cons` lookup is the interval).  Under it every interval-typed
variable is necessarily a LOCKED dimension, hence dimensionally accessible — this is exactly "the interval is
non-fibrant" stated at the use site (interval variables only ever appear locked, never ordinary).  It is NOT
implied by `WfContextUnion` (which admits `cons intervalTypeCell`); it is the precise residual the dimensional
bridge rests on, threaded until that discipline is pinned into context well-formedness upstream.

## Zero-axiom verification

`invertAtVarHeadGeneric` + the `isSubjectUsableAtModality` var / non-var unfolders + `absurd` — the exact
mirror of `typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax

/-- **The interval-non-fibrancy discipline (dual of `AllLocksAreInterval`).**  No `cons`-bound
(dimensionally-INaccessible) position looks up to the interval: an ordinary binding is never the interval, so
an interval-typed variable is necessarily a LOCKED dimension (dimensionally accessible).  The lookup-level
dual of `lockedLookupIsInterval` (which reads off `AllLocksAreInterval` that every NON-fibrantly-accessible
position looks up to the interval).  NOT implied by `WfContextUnion` (which admits `cons intervalTypeCell`);
the precise precondition the dimensional usability bridge needs — the use-site statement of "the interval is
non-fibrant", threaded until that discipline is pinned into context well-formedness upstream. -/
def TypingContext.NoConsBindingIsInterval {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) : Prop :=
  ∀ index : Fin scope, context.isDimensionallyAccessibleAt index = false →
    ¬ Conv (context.lookup index) intervalTypeCell

/-- **★ The typed-implies-dimensionally-usable bridge.**  Under the interval-non-fibrancy discipline
`NoConsBindingIsInterval`, a subject typed at the interval code is DIMENSIONALLY usable.  The `.dimensional`
dual of `typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval`: a NON-variable head is unconditionally
usable (`isSubjectUsableAtModality_ofNonVarHead`); a variable head inverts (`invertAtVarHeadGeneric`) to
`subject = variableCell index` with the context lookup convertible to the interval, and usability there is
exactly `isDimensionallyAccessibleAt context index` — were it `false`, the discipline would refute that
`Conv (lookup index) intervalTypeCell`. -/
theorem typedAtIntervalImpliesDimensionallyUsable_ofNoConsInterval {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject : RawTerm scope}
    (noConsInterval : context.NoConsBindingIsInterval)
    (typed : HasTypeUnion profile context subject intervalTypeCell) :
    context.isSubjectUsableAtModality subject ObligationModality.dimensional = true := by
  by_cases headIsVar : RawTerm.headGenerator subject = Generator.gen_var
  · obtain ⟨index, subjectShape, lookupConv⟩ :=
      HasTypeUnion.invertAtVarHeadGeneric typed headIsVar
    subst subjectShape
    rw [show variableCell index = (.mkGen Generator.gen_var index .childNil : RawTerm scope) from rfl,
      isSubjectUsableAtModality_var, isAccessibleAtModality_dimensional]
    cases dimensionalCheck : context.isDimensionallyAccessibleAt index with
    | true => rfl
    | false => exact absurd lookupConv (noConsInterval index dimensionalCheck)
  · cases subject with
    | mkGen generator payload children =>
        exact isSubjectUsableAtModality_ofNonVarHead context generator payload children
          ObligationModality.dimensional headIsVar

/-- **★ Dimensional usability preserved under reduction — the SR-residual closer (interval-typed reduct,
interval-non-fibrancy discipline).**  The `.dimensional` analogue of `stepPreservesFibrantSubjectUsability`,
restricted to the regime where it is TRUE and stated at the SR use site.  UNLIKE the fibrant theorem
(unconditional, type-agnostic, fed only the subject's usability), the dimensional one is FALSE in that form
(see the file-header counterexample: a single `Step` need not preserve `.dimensional` usability), so it is
instead fed the REDUCT's interval typing — exactly what subject reduction produces (the `childSubjectReduction`
IH at the `pathApp`-argument congruence) — and the interval-non-fibrancy discipline `NoConsBindingIsInterval`.
A thin alias of the typing bridge, naming the SR-residual it discharges. -/
theorem HasTypeUnion.stepPreservesDimensionalSubjectUsability {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {reduct : RawTerm scope}
    (noConsInterval : context.NoConsBindingIsInterval)
    (reductTyped : HasTypeUnion profile context reduct intervalTypeCell) :
    context.isSubjectUsableAtModality reduct ObligationModality.dimensional = true :=
  typedAtIntervalImpliesDimensionallyUsable_ofNoConsInterval noConsInterval reductTyped

end FX1Poly.Typed
