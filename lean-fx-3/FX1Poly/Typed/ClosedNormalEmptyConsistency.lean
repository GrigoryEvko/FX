import FX1Poly.Typed.GrownClosedNormalClassifierShape
import FX1Poly.Typed.EmptyTypeValueInversion

/-! # FX1Poly/Typed/ClosedNormalEmptyConsistency — combined 3-engine empty-type consistency, unconditional.

The empty type is THE consistency type (`SN-050`: the grown engine has no closed inhabitant of `Empty`).
The nullary formation/intro content of the kernel — the `dataIntroNullary` row (data values) and the
`baseTypeFormation` row (base type codes) of `HasTypeNativeUnion` — sits alongside the grown `HasTypeDescPi`.
This file confirms those layers PRESERVE consistency: no formation/intro layer inhabits `emptyTypeCell` for
closed-normal subjects.  The empty-type twin of `closedNormalSigmaTypeUninhabited`, and the consistency-grade
counterpart of `closedNormalBoolCanonicalForms`.

  * **`HasTypeDescPi.noClosedNormalTermAtEmptyTypeViaGeneric`** — the grown empty rule-out, re-derived as an
    INSTANCE of the CANON-1c corollary `noClosedNormalTermAtDataClassifier` (`emptyTypeCell` is `Conv`
    neither a Π-code — `Conv.piTyCode_not_emptyTypeCode` — nor a universe code —
    `Conv.universeCode_not_emptyTypeCode`).  Parallel to `noClosedNormalTermAtSigmaType`: it demonstrates
    the abstraction SUBSUMES the concrete `GrownCanonicalForms.noClosedNormalTermAtEmptyType` (the same fact
    proved through the reusable engine instead of a bespoke head-by-head case-split).  The empty rigidities
    are oriented OPPOSITE the bool ones — `emptyTypeCell` is on the RIGHT of the shipped `*_not_emptyTypeCode`
    lemmas, so the corollary's `Conv classifier …` witness needs `.sym` (whereas the bool rule-out did not).

  * **`closedNormalEmptyTypeUninhabited` (★)** — combined: NO formation/intro layer (`dataIntroNullary` /
    `baseTypeFormation` / grown) types a closed-NORMAL cell at `emptyTypeCell`.  The data-intro and base-type
    disjuncts are ruled out by `standaloneEmptyUninhabited` (#1063 — their classifiers are non-empty data codes
    / `Type@0`, head-distinct from `emptyCode`); the grown disjunct by the via-generic rule-out.  The
    multi-layer normal-form consistency statement: adding the nullary data layers did not break `Empty`'s
    emptiness.

## Unconditional (no GrownCtxConv-5 / §5)

The grown classifier is read only at an ALREADY-normal subject (the corollary inverts the typing of a normal
term; it never types a reduction step), so no `piElim` context-conversion (#842) is invoked — exactly as the
bool / sigma rule-outs.  Full closed consistency (every closed `t : Empty`, not just every normal one) is
`SN-050` (shipped via the reducibility leg, `CON-A5`) — this file is the normal-form, multi-engine face.

## Zero-axiom

`noClosedNormalTermAtDataClassifier` (the CANON-1c corollary) + `Conv.piTyCode_not_emptyTypeCode` /
`Conv.universeCode_not_emptyTypeCode` (with `.sym`) + `standaloneEmptyUninhabited`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The grown empty rule-out, via the CANON-1c abstraction.**  An instance of
`noClosedNormalTermAtDataClassifier` at `emptyTypeCell`: `Empty` is `Conv` neither a Π-code nor a universe
code, so the grown engine has no closed-normal inhabitant of it.  Demonstrates the abstraction subsumes the
concrete `noClosedNormalTermAtEmptyType` — the empty parallel of `noClosedNormalTermAtSigmaType`.  The empty
rigidities place `emptyTypeCell` on the right, so the `Conv classifier …` witnesses need `.sym`. -/
theorem HasTypeDescPi.noClosedNormalTermAtEmptyTypeViaGeneric {profile : PolyProfile} {subject : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (emptyTypeCell (scope := 0)))
    (normal : RawTerm.isStepNormalForm subject) :
    False :=
  HasTypeDescPi.noClosedNormalTermAtDataClassifier typed normal
    (fun _domainCode _codomainCode convToPiCode => Conv.piTyCode_not_emptyTypeCode convToPiCode.sym)
    (fun _levelExpr _flag convToUniverseCode => Conv.universeCode_not_emptyTypeCode convToUniverseCode.sym)

/-- **★ Combined: no formation/intro layer inhabits the empty type (closed-normal).**  No closed-normal cell
is typed at `emptyTypeCell` by the union `dataIntroNullary` row (classifier one of the four non-empty data
codes), the union `baseTypeFormation` row (classifier `Type@0`), or `HasTypeDescPi` (the empty rule-out).  The
multi-layer normal-form consistency statement — the two nullary-formation arms (#1063) plus the grown engine
all leave `Empty` uninhabited.  The empty twin of `closedNormalSigmaTypeUninhabited`; the consistency-grade
counterpart of `closedNormalBoolCanonicalForms`.  The strength is unchanged from the pre-union three-engine
statement: the `dataIntroNullary` / `baseTypeFormation` rows ARE the inlined formation/intro content of the
two retired nullary data engines, so the consistency claim is identical. -/
theorem closedNormalEmptyTypeUninhabited {profile : PolyProfile} {subject : RawTerm 0}
    (normal : RawTerm.isStepNormalForm subject)
    (typed :
      (∃ (generator : Generator) (payload : generator.payload 0)
          (children : RawTermChildren generator.binderShifts 0) (rule : DataIntroNullaryRuleDesc),
          subject = RawTerm.mkGen generator payload children ∧
          dataIntroNullaryRuleDescOf generator = some rule ∧
          rule.outputTypeCode 0 = emptyTypeCell (scope := 0)) ∨
      (∃ (generator : Generator) (payload : generator.payload 0)
          (children : RawTermChildren generator.binderShifts 0) (rule : BaseTypeRuleDesc),
          subject = RawTerm.mkGen generator payload children ∧
          baseTypeRuleDescOf generator = some rule ∧
          rule.outputUniverse 0 = emptyTypeCell (scope := 0)) ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
        (emptyTypeCell (scope := 0))) :
    False := by
  rcases typed with
      ⟨generator, payload, children, rule, _subjectEq, isDataIntro, classifierEq⟩
    | ⟨generator, payload, children, rule, _subjectEq, isBaseType, classifierEq⟩
    | grownTyped
  · exact standaloneEmptyUninhabited (scope := 0) (generator := generator)
      (Or.inl ⟨rule, isDataIntro, classifierEq⟩)
  · exact standaloneEmptyUninhabited (scope := 0) (generator := generator)
      (Or.inr ⟨rule, isBaseType, classifierEq⟩)
  · exact HasTypeDescPi.noClosedNormalTermAtEmptyTypeViaGeneric grownTyped normal

end FX1Poly.Typed
