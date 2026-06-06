import FX1Poly.Typed.HasTypeDescPiInversion
import FX1Poly.Typed.WfContextDescPiValidity
import FX1Poly.Typed.HasTypeDescPiValidity

/-! # FX1Poly/Typed/HasTypeDescPiClassifierValidity
    — grown classifier-validity over the GROWN well-formedness `WfContextDescPi`

Grown classifier-validity: given `WfContextDescPi Γ` and a grown derivation, the classifier is a grown type.
`HasTypeDescPi.classifierIsTypeDescPi` threads the GROWN well-formedness `WfContextDescPi`, which EXTENDS at a
grown `piIntro` binder via `WfContextDescPi.cons` — exactly what the master subject-reduction dispatcher needs.

The grown classifier-validity needs only the component telescope (the child typings), NOT the classifier
`Conv` — so it routes through the **`Conv`-free** formation inversion `HasTypeDesc.inversionPiCodeGeneral`
(whose `conv` arm forwards the descent IH verbatim, no `Conv.trans`).  That yields an UNCONDITIONAL grown
Π-code inversion chain, hence a `WfContextDescPi`-only classifier-validity.

## The chain

  * `HasTypeDescPi.inversionPiCodeTelescopeUnconditional` — a grown Π-code-subject derivation exposes its
    children as a grown premise telescope `DescTelescopePi`, with NO well-formedness premise (the `ofFormation`
    arm uses the `Conv`-free `inversionPiCodeGeneral`; `conv` recurses; `piIntro`/`piElim` are refuted by
    `Generator.noConfusion`; `genFormationPi` returns the premise telescope).
  * `HasTypeDescPi.inversionPiCodeComponentsUnconditional` — the two-entry-telescope corollary (`cases`
    cons/cons/nil): domain is a grown type, codomain is a grown type under the domain binder.  The
    well-formedness-free twin of `HasTypeDescPi.inversionPiCodeComponents`.
  * `HasTypeDescPi.piCodeInstantiationIsTypeUnconditional` — grown dependent-Π-elimination output validity:
    `subst0 codomainCode argument` is a grown type, needing only the argument typing (inversion +
    `IsTypeDescPi.substituteUnderBinding`).  The well-formedness-free twin of `piCodeInstantiationIsType`.
  * `HasTypeDescPi.classifierIsTypeDescPi` — **the payoff**: a grown-typed subject's classifier is a grown
    type under `WfContextDescPi`.  `ofFormation` delegates to the shipped formation grown classifier-validity
    `HasTypeDesc.classifierIsTypeDescPi`; `conv` reads off the reclassifier typing the `conv` ctor carries
    directly (no transitivity); `piIntro` / `genFormationPi` build the universe
    code via `genFormationPi`; `piElim` uses the unconditional instantiation above on the recursively-obtained
    function classifier.  Threads the extendable `WfContextDescPi` — the leg the master SR dispatcher consumes.

## Zero-axiom verification

Subject-generalised structural recursion + the `Conv`-free formation inversion + `toDescTelescopePi` +
`Generator.noConfusion`/`injection`/`subst_vars` + `IsTypeDescPi.substituteUnderBinding` + `genFormationPi` +
the `typingRuleDescOf_outputIsUniverseFormer` table fact.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Unconditional grown Π-code telescope inversion.**  A grown derivation whose subject is a `gen_piTyCode`
cell exposes its children as a grown premise telescope `DescTelescopePi`, with NO well-formedness premise.  Like
`HasTypeDescPi.inversionPiCodeTelescopeGeneral` but routed through the `Conv`-free, well-formedness-free formation
inversion `HasTypeDesc.inversionPiCodeGeneral` (the `ofFormation` arm), so the recursion carries no context
hypothesis.  The substrate that lets grown classifier-validity thread the extendable `WfContextDescPi`. -/
theorem HasTypeDescPi.inversionPiCodeTelescopeUnconditional {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject reachedClassifier : RawTerm generalScope}
    (derivation : HasTypeDescPi profile generalContext subject reachedClassifier) :
    ∀ {payload : Generator.gen_piTyCode.payload generalScope}
      {children : RawTermChildren Generator.gen_piTyCode.binderShifts generalScope},
      subject = RawTerm.mkGen Generator.gen_piTyCode payload children →
        ∃ (levels : List LevelExpr) (flag : UniverseFlag),
          DescTelescopePi profile (currentDepth := 0) generalContext levels flag children :=
  fun {payloadImplicit} {childrenImplicit} =>
    match derivation with
    | .ofFormation formationTyped => fun subjectEq => by
        obtain ⟨levels, flag, telescope⟩ :=
          HasTypeDesc.inversionPiCodeGeneral formationTyped subjectEq
        exact ⟨levels, flag, telescope.toDescTelescopePi⟩
    | .conv _levelExpr _flag typedPremise _converts _reclassifierTyped => fun subjectEq =>
        HasTypeDescPi.inversionPiCodeTelescopeUnconditional typedPremise subjectEq
    | .piIntro _domainLevel _codomainLevel _flag _domainTyped _codomainTyped _bodyTyped =>
        fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq : Generator.gen_lam = Generator.gen_piTyCode)
    | .piElim _functionTyped _argumentTyped => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq : Generator.gen_app = Generator.gen_piTyCode)
    | .genFormationPi _armContext armGenerator _armPayload armChildren armLevels armFlag
        _armRule _armIsFormation armPremises => fun subjectEq => by
        have generatorAgree : armGenerator = Generator.gen_piTyCode :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorAgree
        injection subjectEq
        subst_vars
        exact ⟨armLevels, armFlag, armPremises⟩

/-- **Unconditional grown Π-code component inversion.**  A `piTyCodeCell` cell's domain is a grown type and its
codomain is a grown type under the domain binder, with NO well-formedness premise.  Cases the two-entry telescope
from `inversionPiCodeTelescopeUnconditional`.  The well-formedness-free twin of
`HasTypeDescPi.inversionPiCodeComponents`. -/
theorem HasTypeDescPi.inversionPiCodeComponentsUnconditional {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (piTyCodeCell domainCode codomainCode) classifier) :
    ∃ (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
      HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag) ∧
        HasTypeDescPi profile (context.cons domainCode) codomainCode
          (universeCodeCell codomainLevel flag) := by
  obtain ⟨levels, flag, telescope⟩ :=
    HasTypeDescPi.inversionPiCodeTelescopeUnconditional typed rfl
  cases telescope with
  | cons _ _domain domainLevel _restLevels _flag _rest domainTyped restTelescope =>
      cases restTelescope with
      | cons _ _codomain codomainLevel _restLevels2 _flag2 _rest2 codomainTyped nilTelescope =>
          cases nilTelescope with
          | nil _ _ => exact ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped⟩

/-- **Unconditional grown dependent-Π-elimination output validity.**  The eliminator's classifier
`subst0 codomainCode argument` is a grown type, needing only the argument typing (no well-formedness): invert the
Π-code type to the codomain's grown-type witness, then `IsTypeDescPi.substituteUnderBinding`.  The
well-formedness-free twin of `HasTypeDescPi.piCodeInstantiationIsType`. -/
theorem HasTypeDescPi.piCodeInstantiationIsTypeUnconditional {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)} {argument : RawTerm scope}
    (piIsType : IsTypeDescPi profile context (piTyCodeCell domainCode codomainCode))
    (argumentTyped : HasTypeDescPi profile context argument domainCode) :
    IsTypeDescPi profile context (RawTerm.subst0 codomainCode argument) := by
  obtain ⟨_piLevel, _piFlag, piTyped⟩ := piIsType
  obtain ⟨_domainLevel, codomainLevel, flag, _domainTyped, codomainTyped⟩ :=
    HasTypeDescPi.inversionPiCodeComponentsUnconditional piTyped
  exact IsTypeDescPi.substituteUnderBinding ⟨codomainLevel, flag, codomainTyped⟩ argument argumentTyped

/-- **Grown classifier-validity over `WfContextDescPi`**.  A grown-typed subject's classifier
is a grown type (`IsTypeDescPi`) under the GROWN well-formedness `WfContextDescPi`, which EXTENDS at a grown
`piIntro` binder (`WfContextDescPi.cons`), so the master subject-reduction dispatcher can thread it.
`ofFormation` delegates to
the shipped formation grown classifier-validity; `conv` reads off the reclassifier typing the `conv` ctor
carries (no transitivity); `piIntro` / `genFormationPi` build the universe code via `genFormationPi`; `piElim`
uses the unconditional instantiation on the recursively-obtained function classifier. -/
theorem HasTypeDescPi.classifierIsTypeDescPi {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (derivation : HasTypeDescPi profile context subject classifier) :
    IsTypeDescPi profile context classifier :=
  match derivation with
  | .ofFormation formationTyped =>
      formationTyped.classifierIsTypeDescPi wellFormed
  | .conv levelExpr flag _typed _converts reclassifierTyped =>
      ⟨levelExpr, flag, reclassifierTyped⟩
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode _body domainLevel codomainLevel flag
      domainTyped codomainTyped _bodyTyped => by
      refine ⟨LevelExpr.lmax domainLevel codomainLevel, flag,
        HasTypeDescPi.genFormationPi context Generator.gen_piTyCode ()
          (.childCons domainCode (.childCons codomainCode .childNil))
          [domainLevel, codomainLevel] flag
          { outputType := universeFormerOutput } typingRuleDescOf_piTyCode ?_⟩
      exact DescTelescopePi.cons (currentDepth := 0) context domainCode domainLevel [codomainLevel]
        flag (.childCons codomainCode .childNil) domainTyped
        (DescTelescopePi.cons (context.cons domainCode) codomainCode codomainLevel [] flag
          .childNil codomainTyped (DescTelescopePi.nil _ flag))
  | .piElim functionTyped argumentTyped =>
      HasTypeDescPi.piCodeInstantiationIsTypeUnconditional
        (functionTyped.classifierIsTypeDescPi wellFormed) argumentTyped
  | .genFormationPi context generator _payload _children levels flag rule isFormation _premises => by
      rw [typingRuleDescOf_outputIsUniverseFormer isFormation]
      exact ⟨(lmaxAll levels).lsucc, flag,
        HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation context (lmaxAll levels) flag)⟩

end FX1Poly.Typed
