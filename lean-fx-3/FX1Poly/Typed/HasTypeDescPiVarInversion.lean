import FX1Poly.Typed.HasTypeDescPiAppInversion

/-! # FX1Poly/Typed/HasTypeDescPiVarInversion — VARIABLE inversion for the GROWN engine

For a `variableCell index` SUBJECT typed in the grown engine `HasTypeDescPi`, this file recovers the only
fact a variable's typing can carry: the classifier is convertible to the looked-up type `context.lookup
index`.  This is the spine-re-typing prerequisite for the Abel-reflection neutral-application reconstruction
of the grown context-conversion piElim crux (GrownCtxConv-5, #842): a var-headed function `var j` re-types
under a converted target context by combining

  * `invertVar` on the source typing — `Conv classifier (sourceContext.lookup j)`,
  * the context-conversion premise — `Conv (sourceContext.lookup j) (targetContext.lookup j)`, and
  * the var rule under the target — `HasTypeDescPi targetContext (var j) (targetContext.lookup j)`,

producing the `functionConverted` (the function re-typed at a `Conv`-equal classifier under the target) that
`HasTypeDescPi.reassembleApplicationUnderContextConversion` (#1092) consumes to reassemble the application.

## The recipe (propext-free, mirroring invertApp)

Subject-generalised structural recursion (`subject = variableCell index` threaded as an `Eq`), at BOTH engine
layers (the grown `ofFormation` arm delegates to the formation inversion):

  * `var` (the real case) — the var rule classifies at `context.lookup index`; the subject `injection` pins
    `index`, leaving `Conv.refl`.
  * `conv` (both engines have one) — recurse on the typed premise (same subject), re-thread the classifier
    `Conv` by `Conv.trans converts.sym recursiveConv`.  (This is why the conclusion is `Conv`, not equality:
    the `conv` arm changes the classifier up to `Conv`.)
  * `universeFormation` — the subject is a `universeCodeCell`; `congrArg headGenerator` clashes
    `gen_universeCode` against `gen_var`.
  * `piIntro` / `piElim` — the subject is `lamCell` / `appCell`; `headGenerator` clashes `gen_lam` / `gen_app`.
  * `genFormation` / `genFormationPi` — the subject is a former cell; `headGenerator` pins the generator to
    `gen_var`, but `typingRuleDescOf gen_var = none` contradicts the `isFormation` witness.

## Zero-axiom verification

Subject-generalised structural recursion + the subject `injection` + the unconditional `Conv.trans` /
`Conv.sym` / `Conv.refl` + the `headGenerator` / `Generator.noConfusion` refutations + the
`typingRuleDescOf gen_var = none` reduction.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- Formation-engine var inversion: a `variableCell index` typed in the FORMATION engine has its classifier
convertible to the looked-up type.  Subject-generalised so the match stays propext-free; the formation `conv`
arm threads the `Conv` (hence the conclusion is `Conv`, not equality). -/
theorem HasTypeDesc.invertVarFormationGeneral {profile : PolyProfile} {generalScope : Nat}
    {generalContext : TypingContext profile generalScope}
    {subject classifier : RawTerm generalScope}
    (derivation : HasTypeDesc profile generalContext subject classifier) :
    ∀ {index : Fin generalScope}, subject = variableCell index →
      Conv classifier (generalContext.lookup index) :=
  fun {indexImplicit} =>
    match derivation with
    | .var _context index => fun subjectEq => by
        injection subjectEq with _scopeEq _generatorEq payloadEq _childrenEq
        subst payloadEq
        exact Conv.refl _
    | .conv _levelExpr _flag typedPremise converts _reclassifierTyped => fun subjectEq =>
        Conv.trans converts.sym (HasTypeDesc.invertVarFormationGeneral typedPremise subjectEq)
    | .universeFormation _context _levelExpr _flag => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_universeCode = Generator.gen_var)
    | .genFormation _armContext armGenerator _armPayload _armChildren _armLevels _armFlag
        armRule armIsFormation _armPremises => fun subjectEq => by
        have generatorIsVar : armGenerator = Generator.gen_var :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorIsVar
        rw [show typingRuleDescOf Generator.gen_var = none from rfl] at armIsFormation
        nomatch armIsFormation

/-- Subject-generalised recursive workhorse for grown variable inversion: any grown derivation whose subject
is a `variableCell index` has its classifier convertible to `generalContext.lookup index`.  The `ofFormation`
arm delegates to the formation inversion; the `conv` arm re-threads the conversion through the unconditional
raw `Conv.trans`. -/
theorem HasTypeDescPi.invertVarGeneral {profile : PolyProfile} {generalScope : Nat}
    {generalContext : TypingContext profile generalScope}
    {subject classifier : RawTerm generalScope}
    (derivation : HasTypeDescPi profile generalContext subject classifier) :
    ∀ {index : Fin generalScope}, subject = variableCell index →
      Conv classifier (generalContext.lookup index) :=
  fun {indexImplicit} =>
    match derivation with
    | .ofFormation formationTyped => fun subjectEq =>
        HasTypeDesc.invertVarFormationGeneral formationTyped subjectEq
    | .conv _levelExpr _flag typedPremise converts _reclassifierTyped => fun subjectEq =>
        Conv.trans converts.sym (HasTypeDescPi.invertVarGeneral typedPremise subjectEq)
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
        armRule armIsFormation _armPremises => fun subjectEq => by
        have generatorIsVar : armGenerator = Generator.gen_var :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorIsVar
        rw [show typingRuleDescOf Generator.gen_var = none from rfl] at armIsFormation
        nomatch armIsFormation

/-- **Grown variable inversion.**  A `variableCell index` typed at `classifier` in the grown engine has
`classifier` convertible to the looked-up type `context.lookup index` — the clean corollary of
`invertVarGeneral` at `subject = variableCell index` (`rfl`).  The spine-re-typing primitive the
Abel-reflection neutral-application reconstruction (GrownCtxConv-5, #842) threads: it lets a var-headed
function be re-typed under a `Conv`-converted target context. -/
theorem HasTypeDescPi.invertVar {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {index : Fin scope} {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (variableCell index) classifier) :
    Conv classifier (context.lookup index) :=
  HasTypeDescPi.invertVarGeneral typed rfl

end FX1Poly.Typed
