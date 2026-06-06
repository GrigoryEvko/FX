import FX1Poly.Typed.HasTypeDescPiInversion
import FX1Poly.Typed.HasTypeDescInversion
import FX1Poly.Core.RawConfluence

/-! # FX1Poly/Typed/HasTypeDescPiUniverseCodeInversion
    — universe-code inversion for the grown engine `HasTypeDescPi` (the second uniqueness leaf for SN-052)

Any classifier a UNIVERSE-CODE cell `Type@(e, flag)` receives in the grown engine is `Conv`-equal to the next
universe `Type@(e+1, flag)`.  This is the grown analogue of `HasTypeDesc.inversionUniverseCode` (the formation
engine), and the per-subject UNIQUENESS the SN-052 COMPARE step
(`HasTypeDescPi.decidableCheckOfInferredUniqueAtType`) needs at a universe-code position — the SECOND leaf
position of the bidirectional checker, alongside the variable (`HasTypeDescPiVariableInversion`).  A
universe-code cell's principal type is `Type@(e+1, flag)`, and every other type it can receive is `Conv` to
it — so checking a universe code against a target is decided by `Conv`.

## Recipe (the variable-inversion recipe, with the universe-formation model)

Term-mode recursion on the derivation, identical in shape to `HasTypeDescPi.inversionVariableGeneral`:
* `ofFormation` delegates to the formation-engine `HasTypeDesc.inversionUniverseCodeGeneral`;
* `conv` chains through the converted classifier with the UNCONDITIONAL raw `Conv.trans` (#714 — no
  typed-middle needed);
* `piIntro` / `piElim` are impossible on a universe-code subject — `congrArg RawTerm.headGenerator` exposes
  `gen_lam = gen_universeCode` / `gen_app = gen_universeCode`, refuted by `Generator.noConfusion`;
* `genFormationPi` is impossible — after aligning the generator to `gen_universeCode`, its `isFormation`
  witness (`typingRuleDescOf gen_universeCode = some …`) clashes with `typingRuleDescOf gen_universeCode =
  none` (the universe code is not a formation former in the rule table — only `pi` / `sigma` are).

## Zero-axiom verification

Term-mode `match` + the formation universe-code inversion + unconditional `Conv.trans` +
`Generator.noConfusion` + the `isFormation` clash.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Subject-generalised recursive workhorse for grown universe-code inversion.**  For a derivation whose
subject is forced to a universe-code cell (via `subjectEq`), the reached classifier is `Conv` to the next
universe `Type@(e+1, flag)`.  Generalising the subject (rather than matching the level/flag directly) keeps the
recursive `conv` arm well-typed. -/
theorem HasTypeDescPi.inversionUniverseCodeGeneral {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject reachedClassifier : RawTerm generalScope}
    (derivation : HasTypeDescPi profile generalContext subject reachedClassifier) :
    ∀ {targetLevel : LevelExpr} {targetFlag : UniverseFlag},
      subject = universeCodeCell targetLevel targetFlag →
        Conv reachedClassifier (universeCodeCell targetLevel.lsucc targetFlag) :=
  fun {_targetLevelImplicit} {_targetFlagImplicit} =>
    match derivation with
    | .ofFormation formationTyped => fun subjectEq =>
        HasTypeDesc.inversionUniverseCodeGeneral formationTyped subjectEq
    | .conv _levelExpr _flag typedPremise converts _reclassifierTyped => fun subjectEq =>
        Conv.trans converts.sym
          (HasTypeDescPi.inversionUniverseCodeGeneral typedPremise subjectEq)
    | .piIntro _domainLevel _codomainLevel _flag _domainTyped _codomainTyped _bodyTyped =>
        fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_lam = Generator.gen_universeCode)
    | .piElim _functionTyped _argumentTyped => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_app = Generator.gen_universeCode)
    | .genFormationPi _armContext armGenerator _armPayload _armChildren _armLevels _armFlag
        _armRule armIsFormation _armPremises => fun subjectEq => by
        have generatorAgree : armGenerator = Generator.gen_universeCode :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorAgree
        contradiction

/-- **Universe-code inversion for the grown engine.**  Any classifier a universe-code cell `Type@(e, flag)`
receives is convertible to the next universe `Type@(e+1, flag)` — the grown analogue of
`HasTypeDesc.inversionUniverseCode`, and the per-subject uniqueness the SN-052 COMPARE step consumes at a
universe-code position. -/
theorem HasTypeDescPi.inversionUniverseCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag} {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (universeCodeCell levelExpr flag) classifier) :
    Conv classifier (universeCodeCell levelExpr.lsucc flag) :=
  HasTypeDescPi.inversionUniverseCodeGeneral typed rfl

end FX1Poly.Typed
