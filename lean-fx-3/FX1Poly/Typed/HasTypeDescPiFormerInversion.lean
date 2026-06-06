import FX1Poly.Typed.HasTypeDescPiInversion
import FX1Poly.Core.RawConfluence

/-! # FX1Poly/Typed/HasTypeDescPiFormerInversion — Conv-KEEPING Π/Σ-code former inversion (toward #458)

`HasTypeDescPi.inversionPiCodeComponents` / `inversionSigmaCodeComponents` recover a former's
domain/codomain component typings but DROP the classifier-`Conv` conjunct (their telescope workhorse
`inversionPiCodeTelescopeGeneral` discards `_convToCode` / `_converts` at every arm — the telescope
conclusion carries no classifier relationship).  That is enough for output VALIDITY but NOT for the
subject-reduction `cong` arm on a former head: to re-assemble `piTyCodeCell domainCode' codomainCode`
(after the domain steps) AT THE ORIGINAL `classifier`, we must rebuild at the former's own output type
`universeCodeCell (lmaxAll levels) flag` and then `conv` back along `Conv classifier output` — which we
do not have unless the inversion keeps it.

This file ships the Conv-KEEPING former inversion — the exact former analogue of the shipped
`invertLam` (#454) and `invertApp` (#769), which keep their classifier `Conv`s — by threading the
conversion through the same subject-generalised recursion the telescope workhorse uses:

  * `ofFormation` — a former IS a formation term (unlike λ/app), so this arm is HANDLED, not refuted:
    `HasTypeDesc.inversionPiCodeWithConvGeneral` already returns the formation telescope together with
    `Conv reachedClassifier (universeCodeCell (lmaxAll levels) flag)`; lift the telescope via
    `toDescTelescopePi` and keep the `Conv`.
  * `conv` — recurse on the typed premise, then re-thread by `Conv.trans converts.sym recursiveConv`
    (the unconditional raw `Conv`), exactly as `invertApp` does.
  * `piIntro` / `piElim` — refuted: `congrArg headGenerator` clashes `gen_lam` / `gen_app` against the
    former generator.
  * `genFormationPi` — the MATCH: the former's output is definitionally `universeFormerOutput scope
    levels flag = universeCodeCell (lmaxAll levels) flag` once the rule is pinned by
    `typingRuleDescOf_piTyCode`, so the classifier `Conv` is `Conv.refl`.

The corollary `invertPiTyCode` / `invertSigmaTyCode` destructures the two-entry telescope (the same
`cons`/`cons`/`nil` walk as `inversionPiCodeComponents`) and keeps the `Conv`, yielding the
domain/codomain component typings AND `Conv classifier (universeCodeCell (lmaxAll [domainLevel,
codomainLevel]) flag)`.

## Zero-axiom verification

Subject-generalised structural recursion + `HasTypeDesc.inversionPiCodeWithConvGeneral` +
`DescTelescope.toDescTelescopePi` + the unconditional `Conv.trans` / `Conv.sym` / `Conv.refl` +
`congrArg headGenerator` / `Generator.noConfusion` refutations + the `typingRuleDescOf_piTyCode`
rule-pin.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- Subject-generalised recursive workhorse for Conv-KEEPING grown Π-code inversion: any grown
derivation whose subject is a `gen_piTyCode` cell exposes its children as a grown premise telescope
`DescTelescopePi` AND a classifier `Conv` to the former's output universe code `universeCodeCell
(lmaxAll levels) flag`.  The Conv-keeping refinement of `inversionPiCodeTelescopeGeneral`. -/
theorem HasTypeDescPi.invertPiCodeTelescopeWithConvGeneral {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject reachedClassifier : RawTerm generalScope}
    (derivation : HasTypeDescPi profile generalContext subject reachedClassifier)
    (wellFormed : WfContext generalContext) :
    ∀ {payload : Generator.gen_piTyCode.payload generalScope}
      {children : RawTermChildren Generator.gen_piTyCode.binderShifts generalScope},
      subject = RawTerm.mkGen Generator.gen_piTyCode payload children →
        ∃ (levels : List LevelExpr) (flag : UniverseFlag),
          DescTelescopePi profile (currentDepth := 0) generalContext levels flag children ∧
            Conv reachedClassifier (universeCodeCell (lmaxAll levels) flag) :=
  fun {payloadImplicit} {childrenImplicit} =>
    match derivation with
    | .ofFormation formationTyped => fun subjectEq => by
        obtain ⟨levels, flag, telescope, convToCode⟩ :=
          HasTypeDesc.inversionPiCodeWithConvGeneral formationTyped subjectEq
        exact ⟨levels, flag, telescope.toDescTelescopePi, convToCode⟩
    | .conv _levelExpr _flag typedPremise converts _reclassifierTyped => fun subjectEq => by
        obtain ⟨levels, flag, telescope, recursiveConv⟩ :=
          HasTypeDescPi.invertPiCodeTelescopeWithConvGeneral typedPremise wellFormed subjectEq
        exact ⟨levels, flag, telescope, Conv.trans converts.sym recursiveConv⟩
    | .piIntro _domainLevel _codomainLevel _flag _domainTyped _codomainTyped _bodyTyped =>
        fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_lam = Generator.gen_piTyCode)
    | .piElim _functionTyped _argumentTyped => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_app = Generator.gen_piTyCode)
    | .genFormationPi _armContext armGenerator _armPayload _armChildren armLevels armFlag
        armRule armIsFormation armPremises => fun subjectEq => by
        have generatorAgree : armGenerator = Generator.gen_piTyCode :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorAgree
        obtain rfl : armRule = { outputType := universeFormerOutput } :=
          Option.some.inj (typingRuleDescOf_piTyCode ▸ armIsFormation).symm
        injection subjectEq
        subst_vars
        exact ⟨armLevels, armFlag, armPremises, Conv.refl _⟩

/-- **Conv-keeping Π-code former inversion for the grown engine.**  A `piTyCodeCell domainCode
codomainCode` typed at `classifier` (over a well-formed context) has the domain typed at a universe
code, the codomain typed at a universe code under the domain binder, AND `classifier` convertible to
the former's output `universeCodeCell (lmaxAll [domainLevel, codomainLevel]) flag`.  The former
analogue of `invertApp` — keeps the `Conv` the subject-reduction `cong` arm needs to return a
re-assembled former to its original classifier. -/
theorem HasTypeDescPi.invertPiTyCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed :
      HasTypeDescPi profile context (piTyCodeCell domainCode codomainCode) classifier)
    (wellFormed : WfContext context) :
    ∃ (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
      HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag) ∧
        HasTypeDescPi profile (context.cons domainCode) codomainCode
          (universeCodeCell codomainLevel flag) ∧
        Conv classifier (universeCodeCell (lmaxAll [domainLevel, codomainLevel]) flag) := by
  obtain ⟨levels, flag, telescope, convToCode⟩ :=
    HasTypeDescPi.invertPiCodeTelescopeWithConvGeneral typed wellFormed rfl
  cases telescope with
  | cons _ _domain domainLevel _restLevels _flag _rest domainTyped restTelescope =>
      cases restTelescope with
      | cons _ _codomain codomainLevel _restLevels2 _flag2 _rest2 codomainTyped
          nilTelescope =>
          cases nilTelescope with
          | nil _ _ =>
              exact ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped, convToCode⟩

/-- Subject-generalised recursive workhorse for Conv-KEEPING grown Σ-code inversion — the dual of
`invertPiCodeTelescopeWithConvGeneral`, identical recipe over `gen_sigmaTyCode`. -/
theorem HasTypeDescPi.invertSigmaCodeTelescopeWithConvGeneral {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject reachedClassifier : RawTerm generalScope}
    (derivation : HasTypeDescPi profile generalContext subject reachedClassifier)
    (wellFormed : WfContext generalContext) :
    ∀ {payload : Generator.gen_sigmaTyCode.payload generalScope}
      {children : RawTermChildren Generator.gen_sigmaTyCode.binderShifts generalScope},
      subject = RawTerm.mkGen Generator.gen_sigmaTyCode payload children →
        ∃ (levels : List LevelExpr) (flag : UniverseFlag),
          DescTelescopePi profile (currentDepth := 0) generalContext levels flag children ∧
            Conv reachedClassifier (universeCodeCell (lmaxAll levels) flag) :=
  fun {payloadImplicit} {childrenImplicit} =>
    match derivation with
    | .ofFormation formationTyped => fun subjectEq => by
        obtain ⟨levels, flag, telescope, convToCode⟩ :=
          HasTypeDesc.inversionSigmaCodeWithConvGeneral formationTyped subjectEq
        exact ⟨levels, flag, telescope.toDescTelescopePi, convToCode⟩
    | .conv _levelExpr _flag typedPremise converts _reclassifierTyped => fun subjectEq => by
        obtain ⟨levels, flag, telescope, recursiveConv⟩ :=
          HasTypeDescPi.invertSigmaCodeTelescopeWithConvGeneral typedPremise wellFormed subjectEq
        exact ⟨levels, flag, telescope, Conv.trans converts.sym recursiveConv⟩
    | .piIntro _domainLevel _codomainLevel _flag _domainTyped _codomainTyped _bodyTyped =>
        fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_lam = Generator.gen_sigmaTyCode)
    | .piElim _functionTyped _argumentTyped => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_app = Generator.gen_sigmaTyCode)
    | .genFormationPi _armContext armGenerator _armPayload _armChildren armLevels armFlag
        armRule armIsFormation armPremises => fun subjectEq => by
        have generatorAgree : armGenerator = Generator.gen_sigmaTyCode :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorAgree
        obtain rfl : armRule = { outputType := universeFormerOutput } :=
          Option.some.inj (typingRuleDescOf_sigmaTyCode ▸ armIsFormation).symm
        injection subjectEq
        subst_vars
        exact ⟨armLevels, armFlag, armPremises, Conv.refl _⟩

/-- **Conv-keeping Σ-code former inversion for the grown engine** — the dual of `invertPiTyCode`,
identical recipe over `sigmaTyCodeCell`. -/
theorem HasTypeDescPi.invertSigmaTyCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed :
      HasTypeDescPi profile context (sigmaTyCodeCell domainCode codomainCode) classifier)
    (wellFormed : WfContext context) :
    ∃ (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
      HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag) ∧
        HasTypeDescPi profile (context.cons domainCode) codomainCode
          (universeCodeCell codomainLevel flag) ∧
        Conv classifier (universeCodeCell (lmaxAll [domainLevel, codomainLevel]) flag) := by
  obtain ⟨levels, flag, telescope, convToCode⟩ :=
    HasTypeDescPi.invertSigmaCodeTelescopeWithConvGeneral typed wellFormed rfl
  cases telescope with
  | cons _ _domain domainLevel _restLevels _flag _rest domainTyped restTelescope =>
      cases restTelescope with
      | cons _ _codomain codomainLevel _restLevels2 _flag2 _rest2 codomainTyped
          nilTelescope =>
          cases nilTelescope with
          | nil _ _ =>
              exact ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped, convToCode⟩

end FX1Poly.Typed
