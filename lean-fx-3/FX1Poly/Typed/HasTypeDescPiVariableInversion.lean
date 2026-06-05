import FX1Poly.Typed.HasTypeDescPiInversion
import FX1Poly.Typed.HasTypeDescInversion
import FX1Poly.Core.RawConfluence

/-! # FX1Poly/Typed/HasTypeDescPiVariableInversion
    — variable inversion for the grown engine `HasTypeDescPi` (a uniqueness leaf for the bidirectional checker)

Any classifier a VARIABLE cell receives in the grown engine is `Conv`-equal to the variable's principal type
(its context lookup).  This is the grown analogue of `HasTypeDesc.inversionVariable` (the formation engine),
and it is exactly the per-subject UNIQUENESS the SN-052 COMPARE step
(`HasTypeDescPi.decidableCheckOfInferredUniqueAtType`) needs at a variable position: the variable's inferred
type is `context.lookup index`, and every other type it can receive is `Conv` to it — so checking a variable
against a target is decided by `Conv`.

## Recipe

Term-mode recursion on the derivation:
* `ofFormation` delegates to the formation-engine `HasTypeDesc.inversionVariableGeneral`;
* `conv` chains through the converted classifier with the UNCONDITIONAL raw `Conv.trans` (#714 — raw
  conversion is an equivalence with no SN hypothesis, so no typed-middle is needed, unlike
  `Conv.trans_of_typedMiddle`);
* `piIntro` / `piElim` are impossible on a variable subject — `congrArg RawTerm.headGenerator` exposes
  `gen_lam = gen_var` / `gen_app = gen_var`, refuted by `Generator.noConfusion`;
* `genFormationPi` is impossible — after aligning the generator to `gen_var`, its `isFormation` witness
  (`typingRuleDescOf gen_var = some …`) clashes with `typingRuleDescOf gen_var = none`.

## Zero-axiom verification

Term-mode `match` + the formation var-inversion + unconditional `Conv.trans` + `Generator.noConfusion` +
the `isFormation` clash.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Subject-generalised recursive workhorse for grown variable inversion.**  For a derivation whose subject
is forced to a variable cell (via `subjectEq`), the reached classifier is `Conv` to the variable's context
lookup.  Generalising the subject (rather than matching the variable index directly) keeps the recursive
`conv` arm well-typed. -/
theorem HasTypeDescPi.inversionVariableGeneral {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject reachedClassifier : RawTerm generalScope}
    (derivation : HasTypeDescPi profile generalContext subject reachedClassifier)
    (wellFormed : WfContext generalContext) :
    ∀ {targetIndex : Fin generalScope},
      subject = variableCell targetIndex →
        Conv reachedClassifier (generalContext.lookup targetIndex) :=
  fun {_targetIndexImplicit} =>
    match derivation with
    | .ofFormation formationTyped => fun subjectEq =>
        HasTypeDesc.inversionVariableGeneral formationTyped wellFormed subjectEq
    | .conv _levelExpr _flag typedPremise converts _reclassifierTyped => fun subjectEq =>
        Conv.trans converts.sym
          (HasTypeDescPi.inversionVariableGeneral typedPremise wellFormed subjectEq)
    | .piIntro _domainLevel _codomainLevel _flag _domainTyped _codomainTyped _bodyTyped =>
        fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_lam = Generator.gen_var)
    | .piElim _functionTyped _argumentTyped => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_app = Generator.gen_var)
    | .genFormationPi _armContext armGenerator _armPayload _armChildren _armLevels _armFlag
        _armRule armIsFormation _armPremises => fun subjectEq => by
        have generatorAgree : armGenerator = Generator.gen_var :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorAgree
        contradiction

/-- **Variable inversion for the grown engine.**  Any classifier a variable cell receives is convertible to
the variable's principal type (its context lookup) — the grown analogue of `HasTypeDesc.inversionVariable`,
and the per-subject uniqueness the SN-052 COMPARE step consumes at a variable. -/
theorem HasTypeDescPi.inversionVariable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {index : Fin scope} {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (variableCell index) classifier)
    (wellFormed : WfContext context) :
    Conv classifier (context.lookup index) :=
  HasTypeDescPi.inversionVariableGeneral typed wellFormed rfl

end FX1Poly.Typed
