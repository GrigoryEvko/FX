import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Typed.HasTypeHonesty
import FX1Poly.Typed.HasTypeDescSound
import FX1Poly.Typed.HasTypeValidity
import FX1Poly.Typed.HasTypeStronglyNormalizing

/-! # FX1Poly/Typed/HasTypeDescInversion — INVERSION (P8 descent) for the description engine.

polycell.md §11.8.5 P8 ("Inversion = descent"): `HasType Γ (mkGen g p ch) T ⇒
children typed at the TypingRule's expected types ∧ Conv T (rule.outputType …)`,
"one lemma per shape; feeds the typechecker and canonicity" — the sheaf/glue
direction.  This ships the PREMISE half of P8 for the FORMATION shape on the
description engine `HasTypeDesc`: from a formation cell's typing, recover the
`DescTelescope` premise witnessing its children form the expected telescope of types.

Why the premise half is a distinct cut: **it is `Conv`-FREE.**  Full P8's
classifier-`Conv` conjunct needs `Conv.trans` on the `conv` arm (typed
`Conv.trans_of_typedMiddle`, available only with a `WfContext`).  But the CHILDREN
are determined by the SUBJECT (`mkGen g p ch`), which `conv` leaves unchanged — so the
`conv` arm forwards the descent IH VERBATIM, needing no `Conv` and no `WfContext`.
This isolates the genuinely-useful descent content (the children's telescope — what
the typechecker + canonicity consume) from the `Conv`-dependent part.

## The full half (classifier-`Conv` conjunct) — `…WithConv`

Built on the same recipe, the FULL P8 for the dependent-binary formation family:
`…WithConv` adds `Conv reachedClassifier (universeCodeCell (lmaxAll levels) flag)` —
the subject's classifier converts to the canonical formation output.  This is the
conjunct intrinsic UNIQUENESS (P7) and the typechecker's conv-check consume, wiring
typed `Conv.trans` into the description engine.  Three deltas over the premise half:
(1) a `WfContext` parameter (threaded as an OUTER argument — the term-mode `match`
keeps the context index fixed, so unlike the bespoke `induction`-based inversion it
need not revert `WfContext` into the motive); (2) the `conv` arm composes `Conv`s via
`Conv.trans_of_typedMiddle`, the middle's `IsType` coming from `classifierIsType ∘
toHasType` on the `conv` premise; (3) the `genFormation` arm additionally pins the
`TypingRuleDesc` (`Option.some.inj`) so the output reduces to `universeCodeCell
(lmaxAll …) …` and `Conv.refl` closes the conjunct.  The premise half stays — it is
strictly more general (no `WfContext`).

Both the Π-formation shape (`piTyCodeCell`) and the Σ shape (`gen_sigmaTyCode`, the
identical mirror) are covered.  A FULLY generic version (one descent lemma over every
whitelisted generator, refuting non-formers via `typingRuleDescOf … = none`) is
blocked by a dependent-`subst` wall: unifying a free generator variable with the arm's
generator fails Lean's scope/occurs check both directions.  The concrete-former shape
sidesteps it (`subst armGenerator := gen_piTyCode` against a CONSTANT is clean) — which
is why the bespoke layer also carries `inversionPiCode`/`inversionSigmaCode` as a pair.

## Recipe (equation-motive, adapted to the MUTUAL engine)

`induction` REJECTS `HasTypeDesc` ("mutually inductive"), so the recursion is a
term-mode recursive `match` (the propext-free structural form of
`HasTypeDesc.toHasType`) in a helper generalizing the subject + threading `subject =
mkGen g p ch`.  It recurses ONLY into the `conv` premise — a LONE recursion on
`HasTypeDesc` (no mutual block), exactly as `DescTelescope.toTermTelescope` recurses
on one mutual member alone.

* `var` / `universeFormation` — impossible: `congrArg RawTerm.headGenerator` on the
  subject equation gives `gen_var = gen_piTyCode` / `gen_universeCode = gen_piTyCode`,
  killed by `Generator.noConfusion` (both generators concrete — no `typingRuleDescOf`
  reduction needed).
* `conv` — forwards the recursive call on its premise (same subject), unchanged.
* `genFormation` — the principal arm: `headGenerator` gives `armGenerator =
  gen_piTyCode`; `subst` (against the CONSTANT `gen_piTyCode`) makes both sides of the
  subject equation literal `mkGen gen_piTyCode …`; `injection` + `subst_vars` align the
  arm's children with the target; the arm's `DescTelescope` premise IS the result.

## Zero-axiom

Term-mode recursive `match` + `congrArg RawTerm.headGenerator` + `Generator.noConfusion`
+ `injection` + `subst_vars`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The equation-motive recursive workhorse for formation-shape descent: subject
generalized to a free variable, threading `subject = mkGen generator payload children`
and the `typingRuleDescOf generator = some rule` whitelist witness.  Recursion via
term-mode `match` (the `conv` arm recurses on its structurally-smaller premise; every
other arm is a leaf), so this is a LONE structural recursion on the mutual
`HasTypeDesc`. -/
theorem HasTypeDesc.inversionPiCodeGeneral {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject reachedClassifier : RawTerm generalScope}
    (derivation : HasTypeDesc profile generalContext subject reachedClassifier) :
    ∀ {payload : Generator.gen_piTyCode.payload generalScope}
      {children : RawTermChildren Generator.gen_piTyCode.binderShifts generalScope},
      subject = RawTerm.mkGen Generator.gen_piTyCode payload children →
        ∃ (levels : List LevelExpr) (flag : UniverseFlag),
          DescTelescope profile (currentDepth := 0) generalContext levels flag
            children :=
  fun {payloadImplicit} {childrenImplicit} =>
    match derivation with
    | .var _armContext _armIndex => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_var = Generator.gen_piTyCode)
    | .conv _levelExpr _flag typedPremise _converts _reclassifierTyped =>
        fun subjectEq => HasTypeDesc.inversionPiCodeGeneral typedPremise subjectEq
    | .universeFormation _armContext _armLevel _armFlag => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_universeCode = Generator.gen_piTyCode)
    | .genFormation _armContext armGenerator _armPayload armChildren armLevels armFlag
        _armRule _armIsFormation armPremises => fun subjectEq => by
        have generatorAgree : armGenerator = Generator.gen_piTyCode :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorAgree
        injection subjectEq
        subst_vars
        exact ⟨armLevels, armFlag, armPremises⟩

/-- **Inversion (P8 descent, premise half) for the Π-type FORMATION shape** on the
description engine.  Any `HasTypeDesc`-typing of `piTyCodeCell domainCode
codomainCode` arises — through `conv` — from a `genFormation` whose `DescTelescope`
premise types the two children as the expected telescope of types.  `Conv`-free (the
children are fixed by the subject, so `conv` forwards the descent IH verbatim — no
`Conv.trans`, no `WfContext`); feeds the typechecker and canonicity.  The
description-engine analogue of the bespoke `inversionPiCode`.  (The Σ shape is the
mirror over `gen_sigmaTyCode`, below.) -/
theorem HasTypeDesc.inversionPiCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed :
      HasTypeDesc profile context (piTyCodeCell domainCode codomainCode) classifier) :
    ∃ (levels : List LevelExpr) (flag : UniverseFlag),
      DescTelescope profile (currentDepth := 0) context levels flag
        (RawTermChildren.binderShape domainCode codomainCode) :=
  HasTypeDesc.inversionPiCodeGeneral typed rfl

/-- The Σ mirror of `inversionPiCodeGeneral` — IDENTICAL recipe over `gen_sigmaTyCode`
(only the concrete generator changes; the dependent-`subst` wall is again sidestepped
by `subst armGenerator := gen_sigmaTyCode` against a constant).  Completes the P8
descent for the dependent-binary formation family (Π AND Σ). -/
theorem HasTypeDesc.inversionSigmaCodeGeneral {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject reachedClassifier : RawTerm generalScope}
    (derivation : HasTypeDesc profile generalContext subject reachedClassifier) :
    ∀ {payload : Generator.gen_sigmaTyCode.payload generalScope}
      {children : RawTermChildren Generator.gen_sigmaTyCode.binderShifts generalScope},
      subject = RawTerm.mkGen Generator.gen_sigmaTyCode payload children →
        ∃ (levels : List LevelExpr) (flag : UniverseFlag),
          DescTelescope profile (currentDepth := 0) generalContext levels flag
            children :=
  fun {payloadImplicit} {childrenImplicit} =>
    match derivation with
    | .var _armContext _armIndex => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_var = Generator.gen_sigmaTyCode)
    | .conv _levelExpr _flag typedPremise _converts _reclassifierTyped =>
        fun subjectEq => HasTypeDesc.inversionSigmaCodeGeneral typedPremise subjectEq
    | .universeFormation _armContext _armLevel _armFlag => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_universeCode = Generator.gen_sigmaTyCode)
    | .genFormation _armContext armGenerator _armPayload armChildren armLevels armFlag
        _armRule _armIsFormation armPremises => fun subjectEq => by
        have generatorAgree : armGenerator = Generator.gen_sigmaTyCode :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorAgree
        injection subjectEq
        subst_vars
        exact ⟨armLevels, armFlag, armPremises⟩

/-- **Inversion (P8 descent, premise half) for the Σ-type FORMATION shape** on the
description engine — the dual of `inversionPiCode`.  Any `HasTypeDesc`-typing of
`sigmaTyCodeCell domainCode codomainCode` arises (through `conv`) from a
`genFormation` whose `DescTelescope` premise types the two children as the expected
telescope of types.  `Conv`-free, same recipe as the Π shape. -/
theorem HasTypeDesc.inversionSigmaCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed :
      HasTypeDesc profile context (sigmaTyCodeCell domainCode codomainCode) classifier) :
    ∃ (levels : List LevelExpr) (flag : UniverseFlag),
      DescTelescope profile (currentDepth := 0) context levels flag
        (RawTermChildren.binderShape domainCode codomainCode) :=
  HasTypeDesc.inversionSigmaCodeGeneral typed rfl

/-- The equation-motive recursive workhorse for the FULL Π-formation inversion (premise
telescope AND classifier-`Conv`).  Same shape as `inversionPiCodeGeneral`, with three
deltas: an outer `WfContext` (the term-mode `match` keeps the context index fixed, so
it need not be reverted into the motive); the `conv` arm composes `Conv`s through the
premise's classifier (a type by validity) via `Conv.trans_of_typedMiddle`; the
`genFormation` arm pins the `TypingRuleDesc` so its output reduces to the canonical
universe code, discharging the `Conv` conjunct with `Conv.refl`. -/
theorem HasTypeDesc.inversionPiCodeWithConvGeneral {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject reachedClassifier : RawTerm generalScope}
    (derivation : HasTypeDesc profile generalContext subject reachedClassifier)
    (wellFormed : WfContext generalContext) :
    ∀ {payload : Generator.gen_piTyCode.payload generalScope}
      {children : RawTermChildren Generator.gen_piTyCode.binderShifts generalScope},
      subject = RawTerm.mkGen Generator.gen_piTyCode payload children →
        ∃ (levels : List LevelExpr) (flag : UniverseFlag),
          DescTelescope profile (currentDepth := 0) generalContext levels flag
            children ∧
          Conv reachedClassifier (universeCodeCell (lmaxAll levels) flag) :=
  fun {payloadImplicit} {childrenImplicit} =>
    match derivation with
    | .var _armContext _armIndex => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_var = Generator.gen_piTyCode)
    | .conv _levelExpr _flag typedPremise converts _reclassifierTyped =>
        fun subjectEq => by
          obtain ⟨levels, flag, telescope, convToCode⟩ :=
            HasTypeDesc.inversionPiCodeWithConvGeneral typedPremise wellFormed subjectEq
          exact ⟨levels, flag, telescope,
            Conv.trans_of_typedMiddle
              (HasType.classifierIsType wellFormed
                (HasTypeDesc.toHasType typedPremise))
              converts.sym convToCode⟩
    | .universeFormation _armContext _armLevel _armFlag => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_universeCode = Generator.gen_piTyCode)
    | .genFormation _armContext armGenerator _armPayload armChildren armLevels armFlag
        armRule armIsFormation armPremises => fun subjectEq => by
        have generatorAgree : armGenerator = Generator.gen_piTyCode :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorAgree
        have ruleAgree : armRule = { outputType := universeFormerOutput } :=
          Option.some.inj armIsFormation.symm
        subst ruleAgree
        injection subjectEq
        subst_vars
        exact ⟨armLevels, armFlag, armPremises, Conv.refl _⟩

/-- **Inversion (P8, FULL) for the Π-type FORMATION shape** on the description engine:
the premise telescope (children form the expected telescope of types) AND the
classifier-`Conv` conjunct (the cell's classifier converts to the canonical formation
output `Type@(lmaxAll levels, flag)`).  The description-engine analogue of the bespoke
`HasType.inversionPiCode`, wiring typed `Conv.trans` into the engine — the conjunct
intrinsic uniqueness (P7) and the typechecker's conv-check consume.
Needs `WfContext` (the `conv` arm's `Conv` composition uses validity). -/
theorem HasTypeDesc.inversionPiCodeWithConv {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed :
      HasTypeDesc profile context (piTyCodeCell domainCode codomainCode) classifier)
    (wellFormed : WfContext context) :
    ∃ (levels : List LevelExpr) (flag : UniverseFlag),
      DescTelescope profile (currentDepth := 0) context levels flag
        (RawTermChildren.binderShape domainCode codomainCode) ∧
      Conv classifier (universeCodeCell (lmaxAll levels) flag) :=
  HasTypeDesc.inversionPiCodeWithConvGeneral typed wellFormed rfl

/-- The Σ mirror of `inversionPiCodeWithConvGeneral` — IDENTICAL recipe over
`gen_sigmaTyCode`.  Completes the FULL P8 (premise telescope + classifier-`Conv`) for
the dependent-binary formation family. -/
theorem HasTypeDesc.inversionSigmaCodeWithConvGeneral {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject reachedClassifier : RawTerm generalScope}
    (derivation : HasTypeDesc profile generalContext subject reachedClassifier)
    (wellFormed : WfContext generalContext) :
    ∀ {payload : Generator.gen_sigmaTyCode.payload generalScope}
      {children : RawTermChildren Generator.gen_sigmaTyCode.binderShifts generalScope},
      subject = RawTerm.mkGen Generator.gen_sigmaTyCode payload children →
        ∃ (levels : List LevelExpr) (flag : UniverseFlag),
          DescTelescope profile (currentDepth := 0) generalContext levels flag
            children ∧
          Conv reachedClassifier (universeCodeCell (lmaxAll levels) flag) :=
  fun {payloadImplicit} {childrenImplicit} =>
    match derivation with
    | .var _armContext _armIndex => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_var = Generator.gen_sigmaTyCode)
    | .conv _levelExpr _flag typedPremise converts _reclassifierTyped =>
        fun subjectEq => by
          obtain ⟨levels, flag, telescope, convToCode⟩ :=
            HasTypeDesc.inversionSigmaCodeWithConvGeneral typedPremise wellFormed
              subjectEq
          exact ⟨levels, flag, telescope,
            Conv.trans_of_typedMiddle
              (HasType.classifierIsType wellFormed
                (HasTypeDesc.toHasType typedPremise))
              converts.sym convToCode⟩
    | .universeFormation _armContext _armLevel _armFlag => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_universeCode = Generator.gen_sigmaTyCode)
    | .genFormation _armContext armGenerator _armPayload armChildren armLevels armFlag
        armRule armIsFormation armPremises => fun subjectEq => by
        have generatorAgree : armGenerator = Generator.gen_sigmaTyCode :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorAgree
        have ruleAgree : armRule = { outputType := universeFormerOutput } :=
          Option.some.inj armIsFormation.symm
        subst ruleAgree
        injection subjectEq
        subst_vars
        exact ⟨armLevels, armFlag, armPremises, Conv.refl _⟩

/-- **Inversion (P8, FULL) for the Σ-type FORMATION shape** on the description engine —
the dual of `inversionPiCodeWithConv`: premise telescope AND classifier-`Conv` to the
canonical output `Type@(lmaxAll levels, flag)`.  Same recipe over `gen_sigmaTyCode`. -/
theorem HasTypeDesc.inversionSigmaCodeWithConv {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed :
      HasTypeDesc profile context (sigmaTyCodeCell domainCode codomainCode) classifier)
    (wellFormed : WfContext context) :
    ∃ (levels : List LevelExpr) (flag : UniverseFlag),
      DescTelescope profile (currentDepth := 0) context levels flag
        (RawTermChildren.binderShape domainCode codomainCode) ∧
      Conv classifier (universeCodeCell (lmaxAll levels) flag) :=
  HasTypeDesc.inversionSigmaCodeWithConvGeneral typed wellFormed rfl

/-! ### Leaf inversions (`var`, `universeCode`) for the description engine

The two NON-compound subjects: a variable cell's classifier is convertible to its
context lookup; a universe-code cell's classifier is convertible to the next universe.
Direct analogues of the bespoke `HasType.inversion{Variable,UniverseCode}`, ported to
the term-mode recursive `match` (the mutual `HasTypeDesc` rejects `induction`).  These
complete the per-shape inversion suite for the engine (var / universeCode / Π / Σ) and
are the leaf cases intrinsic UNIQUENESS (P7) consumes when inverting the SECOND
derivation.  Recipe identical to `…WithConv`: the `conv` arm composes through the
premise's classifier (a type by validity) via `Conv.trans_of_typedMiddle`; the
`genFormation` arm — reachable only with a non-formation generator (`gen_var` /
`gen_universeCode` are NOT in the `typingRuleDescOf` whitelist) — is refuted by
`subst`-ing the pinned generator and `Option.noConfusion`-ing the impossible
`typingRuleDescOf … = some rule`; the matching leaf arm closes by `Conv.refl` after
`injection` extracts the payload. -/

/-- Subject-generalized recursive workhorse for variable-cell inversion. -/
theorem HasTypeDesc.inversionVariableGeneral {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject reachedClassifier : RawTerm generalScope}
    (derivation : HasTypeDesc profile generalContext subject reachedClassifier)
    (wellFormed : WfContext generalContext) :
    ∀ {targetIndex : Fin generalScope},
      subject = variableCell targetIndex →
        Conv reachedClassifier (generalContext.lookup targetIndex) :=
  fun {targetIndexImplicit} =>
    match derivation with
    | .var _armContext armIndex => fun subjectEq => by
        have indicesAgree : armIndex = targetIndexImplicit := by injection subjectEq
        subst indicesAgree
        exact Conv.refl _
    | .conv _levelExpr _flag typedPremise converts _reclassifierTyped =>
        fun subjectEq =>
          Conv.trans_of_typedMiddle
            (HasType.classifierIsType wellFormed (HasTypeDesc.toHasType typedPremise))
            converts.sym
            (HasTypeDesc.inversionVariableGeneral typedPremise wellFormed subjectEq)
    | .universeFormation _armContext _armLevel _armFlag => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_universeCode = Generator.gen_var)
    | .genFormation _armContext armGenerator _armPayload _armChildren _armLevels
        _armFlag _armRule armIsFormation _armPremises => fun subjectEq => by
        have generatorAgree : armGenerator = Generator.gen_var :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorAgree
        -- `gen_var` is not a formation former: `typingRuleDescOf gen_var` reduces to
        -- `none`, clashing with the arm's `… = some armRule` whitelist witness.
        contradiction

/-- **Inversion for a variable cell** on the description engine.  Any classifier a
variable cell receives is convertible to the variable's principal type (its context
lookup).  The `HasTypeDesc` analogue of the bespoke `HasType.inversionVariable`. -/
theorem HasTypeDesc.inversionVariable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {index : Fin scope} {classifier : RawTerm scope}
    (typed : HasTypeDesc profile context (variableCell index) classifier)
    (wellFormed : WfContext context) :
    Conv classifier (context.lookup index) :=
  HasTypeDesc.inversionVariableGeneral typed wellFormed rfl

/-- Subject-generalized recursive workhorse for universe-code-cell inversion. -/
theorem HasTypeDesc.inversionUniverseCodeGeneral {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject reachedClassifier : RawTerm generalScope}
    (derivation : HasTypeDesc profile generalContext subject reachedClassifier)
    (wellFormed : WfContext generalContext) :
    ∀ {targetLevel : LevelExpr} {targetFlag : UniverseFlag},
      subject = universeCodeCell targetLevel targetFlag →
        Conv reachedClassifier (universeCodeCell targetLevel.lsucc targetFlag) :=
  fun {targetLevelImplicit} {targetFlagImplicit} =>
    match derivation with
    | .var _armContext _armIndex => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_var = Generator.gen_universeCode)
    | .conv _levelExpr _flag typedPremise converts _reclassifierTyped =>
        fun subjectEq =>
          Conv.trans_of_typedMiddle
            (HasType.classifierIsType wellFormed (HasTypeDesc.toHasType typedPremise))
            converts.sym
            (HasTypeDesc.inversionUniverseCodeGeneral typedPremise wellFormed subjectEq)
    | .universeFormation _armContext armLevel armFlag => fun subjectEq => by
        have payloadEq :
            (armLevel, armFlag) = (targetLevelImplicit, targetFlagImplicit) := by
          injection subjectEq
        injection payloadEq with levelAgree flagAgree
        subst levelAgree
        subst flagAgree
        exact Conv.refl _
    | .genFormation _armContext armGenerator _armPayload _armChildren _armLevels
        _armFlag _armRule armIsFormation _armPremises => fun subjectEq => by
        have generatorAgree : armGenerator = Generator.gen_universeCode :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorAgree
        -- `gen_universeCode` is not a formation former: `typingRuleDescOf` reduces to
        -- `none`, clashing with the arm's `… = some armRule` whitelist witness.
        contradiction

/-- **Inversion for a universe-code cell** on the description engine.  Any classifier a
universe-code cell `Type@(e, flag)` receives is convertible to the next universe
`Type@(e+1, flag)`.  The `HasTypeDesc` analogue of the bespoke
`HasType.inversionUniverseCode`. -/
theorem HasTypeDesc.inversionUniverseCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag} {classifier : RawTerm scope}
    (typed :
      HasTypeDesc profile context (universeCodeCell levelExpr flag) classifier)
    (wellFormed : WfContext context) :
    Conv classifier (universeCodeCell levelExpr.lsucc flag) :=
  HasTypeDesc.inversionUniverseCodeGeneral typed wellFormed rfl

/-! ### Component descent (P8) — projecting the typed children of a formation cell

The `…WithConv` inversions yield the premise TELESCOPE; the typechecker and canonicity
actually consume the DOMAIN and CODOMAIN typings directly.  These corollaries case the
two-child formation telescope (over `RawTermChildren.binderShape`) to project them out,
alongside the classifier-`Conv` to the canonical `Type@(lmax domainLevel codomainLevel,
flag)` — the INTRINSIC description-engine analogue of the bespoke `HasType.inversionPiCode`
(P8 in its component form, the shape the elimination/formation typing rules read).

The casing is the SAME shape the soundness map (`HasTypeDesc.toHasType`'s `genFormation`
arm) already performs.  Two definitional facts make the projection transport-free:
`scope + 0 ≡ scope` (so `binderShape`'s `Nat.add_zero ▸ domainCode` head is just
`domainCode`) and `lmaxAll [domainLevel, codomainLevel] = lmaxFold domainLevel
[codomainLevel] = LevelExpr.lmax domainLevel codomainLevel` (so the inverted `Conv`'s
universe code is already the goal's). -/

/-- Π-FORMATION component descent: a `piTyCodeCell` cell's domain is a type, its codomain
is a type under the domain binder, and the classifier converts to the canonical Π output
universe.  INTRINSIC (built on `inversionPiCodeWithConv`, no route through `HasType`). -/
theorem HasTypeDesc.inversionPiCodeComponents {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed :
      HasTypeDesc profile context (piTyCodeCell domainCode codomainCode) classifier)
    (wellFormed : WfContext context) :
    ∃ (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
      HasTypeDesc profile context domainCode (universeCodeCell domainLevel flag) ∧
        HasTypeDesc profile (context.cons domainCode) codomainCode
          (universeCodeCell codomainLevel flag) ∧
        Conv classifier
          (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag) := by
  obtain ⟨levels, flag, telescope, convToCode⟩ :=
    HasTypeDesc.inversionPiCodeWithConv typed wellFormed
  cases telescope with
  | cons _ _domain domainLevel _restLevels _flag _rest domainTyped restTelescope =>
      cases restTelescope with
      | cons _ _codomain codomainLevel _restLevels2 _flag2 _rest2 codomainTyped
          nilTelescope =>
          cases nilTelescope with
          | nil _ _ =>
              exact ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped,
                convToCode⟩

/-- Σ-FORMATION component descent — the dual of `inversionPiCodeComponents`, IDENTICAL
recipe over `sigmaTyCodeCell`. -/
theorem HasTypeDesc.inversionSigmaCodeComponents {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed :
      HasTypeDesc profile context (sigmaTyCodeCell domainCode codomainCode) classifier)
    (wellFormed : WfContext context) :
    ∃ (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
      HasTypeDesc profile context domainCode (universeCodeCell domainLevel flag) ∧
        HasTypeDesc profile (context.cons domainCode) codomainCode
          (universeCodeCell codomainLevel flag) ∧
        Conv classifier
          (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag) := by
  obtain ⟨levels, flag, telescope, convToCode⟩ :=
    HasTypeDesc.inversionSigmaCodeWithConv typed wellFormed
  cases telescope with
  | cons _ _domain domainLevel _restLevels _flag _rest domainTyped restTelescope =>
      cases restTelescope with
      | cons _ _codomain codomainLevel _restLevels2 _flag2 _rest2 codomainTyped
          nilTelescope =>
          cases nilTelescope with
          | nil _ _ =>
              exact ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped,
                convToCode⟩

end FX1Poly.Typed
