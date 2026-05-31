import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.HasTypeDescInversion

/-! # FX1Poly/Typed/HasTypeDescPiInversion — Π/Σ-CODE component descent for the GROWN engine
    (the inversion the dependent-eliminator output-validity + canonicity consume).

For a `piTyCodeCell`/`sigmaTyCodeCell` SUBJECT typed in the grown engine `HasTypeDescPi`, this
file recovers its COMPONENT type-hoods: the domain is a type, the codomain is a type under the
domain binder.  The grown analogue of the formation engine's `HasTypeDesc.inversionPiCodeComponents`.

## Why this inverts cleanly (no `Conv.trans`, no grown validity)

The formation inversion `inversionPiCodeWithConv` ALSO returns the classifier-`Conv` to the canonical
universe code, and its `conv` arm composes that `Conv` via `Conv.trans_of_typedMiddle` — which needs
the middle classifier's `IsType`, obtained by routing the premise through `toHasType`.  The GROWN
engine has NO `toHasType` (it adds `lamCell`/`appCell` no bespoke `HasType` arm types), so that route
is unavailable.

This inversion therefore DROPS the classifier-`Conv` conjunct and returns ONLY the component
type-hoods (exactly what `piApplicationOutputIsType` / canonicity consume — they `_`-discard the
formation inversion's `Conv`).  Without the `Conv` to compose, the `conv` arm just RECURSES on its
typed premise (the conversion changed the classifier, never the children), so no `Conv.trans` arises.

## The recipe (propext-free, per the equation-motive cell-index inversion)

Subject-generalised recursion (`subject = mkGen gen_piTyCode payload children` threaded as an
`Eq`), one arm per grown constructor:

* `ofFormation` — route to the FORMATION workhorse `HasTypeDesc.inversionPiCodeWithConvGeneral` on
  the opaque `formationTyped`, lift its telescope through `DescTelescope.toDescTelescopePi`, discard
  the `Conv`.
* `conv` — recurse on the typed premise (same subject; the conversion is irrelevant to the children).
* `piIntro` / `piElim` — the subject is `lamCell`/`appCell`; `congrArg headGenerator` clashes
  `gen_lam`/`gen_app` against `gen_piTyCode`, refuted by `Generator.noConfusion`.
* `genFormationPi` — the base: pin the generator (`congrArg headGenerator`), `injection` the cell
  equality to identify the children, return the premise telescope (`DescTelescopePi`) verbatim.

The component corollary then `cases` the two-entry telescope (cons/cons/nil) — the SAME casing the
formation `inversionPiCodeComponents` performs.

## Zero-axiom

Subject-generalised structural recursion + the formation workhorse + `toDescTelescopePi` + the
`headGenerator`/`Generator.noConfusion` refutation + `injection`/`subst_vars`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- Subject-generalised recursive workhorse for grown Π-code inversion: any grown derivation whose
subject is a `gen_piTyCode` cell exposes its children as a grown premise telescope `DescTelescopePi`.
The `conv` arm recurses (the conversion never touches the children), so no `Conv.trans` is needed. -/
theorem HasTypeDescPi.inversionPiCodeTelescopeGeneral {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject reachedClassifier : RawTerm generalScope}
    (derivation : HasTypeDescPi profile generalContext subject reachedClassifier)
    (wellFormed : WfContext generalContext) :
    ∀ {payload : Generator.gen_piTyCode.payload generalScope}
      {children : RawTermChildren Generator.gen_piTyCode.binderShifts generalScope},
      subject = RawTerm.mkGen Generator.gen_piTyCode payload children →
        ∃ (levels : List LevelExpr) (flag : UniverseFlag),
          DescTelescopePi profile (currentDepth := 0) generalContext levels flag children :=
  fun {payloadImplicit} {childrenImplicit} =>
    match derivation with
    | .ofFormation formationTyped => fun subjectEq => by
        obtain ⟨levels, flag, telescope, _convToCode⟩ :=
          HasTypeDesc.inversionPiCodeWithConvGeneral formationTyped wellFormed subjectEq
        exact ⟨levels, flag, telescope.toDescTelescopePi⟩
    | .conv _levelExpr _flag typedPremise _converts _reclassifierTyped => fun subjectEq =>
        HasTypeDescPi.inversionPiCodeTelescopeGeneral typedPremise wellFormed subjectEq
    | .piIntro _domainLevel _codomainLevel _flag _domainTyped _codomainTyped _bodyTyped =>
        fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_lam = Generator.gen_piTyCode)
    | .piElim _functionTyped _argumentTyped => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_app = Generator.gen_piTyCode)
    | .genFormationPi _armContext armGenerator _armPayload armChildren armLevels armFlag
        _armRule _armIsFormation armPremises => fun subjectEq => by
        have generatorAgree : armGenerator = Generator.gen_piTyCode :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorAgree
        injection subjectEq
        subst_vars
        exact ⟨armLevels, armFlag, armPremises⟩

/-- Π-FORMATION component descent for the grown engine: a `piTyCodeCell` cell's domain is a grown
type, and its codomain is a grown type under the domain binder.  The grown analogue of
`HasTypeDesc.inversionPiCodeComponents` (with the classifier-`Conv` conjunct dropped — see file
docstring).  The inversion the grown dependent-eliminator output-validity consumes. -/
theorem HasTypeDescPi.inversionPiCodeComponents {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed :
      HasTypeDescPi profile context (piTyCodeCell domainCode codomainCode) classifier)
    (wellFormed : WfContext context) :
    ∃ (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
      HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag) ∧
        HasTypeDescPi profile (context.cons domainCode) codomainCode
          (universeCodeCell codomainLevel flag) := by
  obtain ⟨levels, flag, telescope⟩ :=
    HasTypeDescPi.inversionPiCodeTelescopeGeneral typed wellFormed rfl
  cases telescope with
  | cons _ _domain domainLevel _restLevels _flag _rest domainTyped restTelescope =>
      cases restTelescope with
      | cons _ _codomain codomainLevel _restLevels2 _flag2 _rest2 codomainTyped
          nilTelescope =>
          cases nilTelescope with
          | nil _ _ =>
              exact ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped⟩

/-- Subject-generalised recursive workhorse for grown Σ-code inversion — the dual of
`inversionPiCodeTelescopeGeneral`, identical recipe over `gen_sigmaTyCode`. -/
theorem HasTypeDescPi.inversionSigmaCodeTelescopeGeneral {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject reachedClassifier : RawTerm generalScope}
    (derivation : HasTypeDescPi profile generalContext subject reachedClassifier)
    (wellFormed : WfContext generalContext) :
    ∀ {payload : Generator.gen_sigmaTyCode.payload generalScope}
      {children : RawTermChildren Generator.gen_sigmaTyCode.binderShifts generalScope},
      subject = RawTerm.mkGen Generator.gen_sigmaTyCode payload children →
        ∃ (levels : List LevelExpr) (flag : UniverseFlag),
          DescTelescopePi profile (currentDepth := 0) generalContext levels flag children :=
  fun {payloadImplicit} {childrenImplicit} =>
    match derivation with
    | .ofFormation formationTyped => fun subjectEq => by
        obtain ⟨levels, flag, telescope, _convToCode⟩ :=
          HasTypeDesc.inversionSigmaCodeWithConvGeneral formationTyped wellFormed subjectEq
        exact ⟨levels, flag, telescope.toDescTelescopePi⟩
    | .conv _levelExpr _flag typedPremise _converts _reclassifierTyped => fun subjectEq =>
        HasTypeDescPi.inversionSigmaCodeTelescopeGeneral typedPremise wellFormed subjectEq
    | .piIntro _domainLevel _codomainLevel _flag _domainTyped _codomainTyped _bodyTyped =>
        fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_lam = Generator.gen_sigmaTyCode)
    | .piElim _functionTyped _argumentTyped => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_app = Generator.gen_sigmaTyCode)
    | .genFormationPi _armContext armGenerator _armPayload armChildren armLevels armFlag
        _armRule _armIsFormation armPremises => fun subjectEq => by
        have generatorAgree : armGenerator = Generator.gen_sigmaTyCode :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorAgree
        injection subjectEq
        subst_vars
        exact ⟨armLevels, armFlag, armPremises⟩

/-- Σ-FORMATION component descent for the grown engine — the dual of `inversionPiCodeComponents`,
identical recipe over `sigmaTyCodeCell`. -/
theorem HasTypeDescPi.inversionSigmaCodeComponents {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed :
      HasTypeDescPi profile context (sigmaTyCodeCell domainCode codomainCode) classifier)
    (wellFormed : WfContext context) :
    ∃ (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
      HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag) ∧
        HasTypeDescPi profile (context.cons domainCode) codomainCode
          (universeCodeCell codomainLevel flag) := by
  obtain ⟨levels, flag, telescope⟩ :=
    HasTypeDescPi.inversionSigmaCodeTelescopeGeneral typed wellFormed rfl
  cases telescope with
  | cons _ _domain domainLevel _restLevels _flag _rest domainTyped restTelescope =>
      cases restTelescope with
      | cons _ _codomain codomainLevel _restLevels2 _flag2 _rest2 codomainTyped
          nilTelescope =>
          cases nilTelescope with
          | nil _ _ =>
              exact ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped⟩

end FX1Poly.Typed
