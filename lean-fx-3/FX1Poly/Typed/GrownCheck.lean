import FX1Poly.Typed.GrownStrengtheningRefutation

/-! # FX1Poly/Typed/GrownCheck — the syntax-directed grown checking relation

The grown-strengthening campaign's central object: `GrownCheck`, a SYNTAX-DIRECTED checking
RELATION for the grown engine — one arm per subject head shape, every recursive premise on a
STRICT SUBTERM, `Conv` only at compare leaves, and NO typehood premises.  Strengthening
(the inverse of `weakenUnderBinding`, immune to the `conv` escape refuted in
`GrownStrengtheningRefutation`) is proven as completeness ∘ rename-reflection ∘ soundness over
this relation.

## Why a relation, and why this exact shape

  * **Not a `Decidable`.**  Typing is non-unique at a bare Curry-style λ
    (`HasTypeDescPiTypingNonUnique`), so no total checker function exists for arbitrary subjects —
    β-redex subjects `app (lam body) argument` have genuinely free domains.  A relation carries
    the λ-domain nondeterministically (`lam`/`app` arms quantify it) at zero cost.
  * **Syntax-directed, premises on strict subterms.**  Direct derivation induction on
    `HasTypeDescPi` dies at the binder arms: a freely-chosen domain can mention the fresh variable
    (escape the rename image), repairing the context needs context conversion, and the converted
    derivation has no induction hypothesis.  With every recursive premise on a strict subterm,
    the reflection induction runs on SUBJECT STRUCTURE — context conversion does not change the
    subject, so convert-then-recurse is sound.
  * **`Conv` uniformly at the leaves.**  Each arm compares its natural classifier to the target
    through one `Conv` leaf (the λ arm compares the Π-code it abstracts at).  Consequence:
    conv-absorption (`absorbConv`) is per-arm `Conv.trans`, recursion-free — which makes
    completeness (`HasTypeDescPi` → `GrownCheck`) a direct induction.
  * **No typehood premises.**  The relation is RAW — its leaves mention only `Conv`.  Typehood is
    reconstructed in SOUNDNESS, threaded from the target's own typing (leaf arms here; the λ/app
    arms recover component typehood from the target via `Conv.reducesToPiTyCode` + SR-star +
    Π-code inversion, the STR-4/5 bricks).  A typehood premise inside the relation would put a
    non-subterm subject under the reflection induction — the exact wall the design avoids.
  * **The former arm is itself syntax-directed** via the mutual `GrownCheckTelescope` (the
    `DescTelescopePi` shape with `GrownCheck` heads).  Bundling a whole `HasTypeDesc` premise
    instead would smuggle the formation engine's same-subject `conv` arm back into the induction.

## Shipped here (STR-3)

  * `GrownCheck` / `GrownCheckTelescope` — the mutual relation pair.
  * `GrownCheck.absorbConv` — every arm absorbs a trailing `Conv`, recursion-free.
  * `GrownCheck.variableSoundAtTypedTarget` / `universeCodeSoundAtTypedTarget` — leaf-arm
    soundness at a typed target (var rule / `universeFormation` + the grown `conv` rule).
  * Smokes: the identity λ checks at its Π-code; STR-1's escaping reclassifier is
    `GrownCheck`-reachable (the β-expansion the Conv-existential reflection must absorb).

λ/app/former-arm soundness and the telescope soundness recursion are STR-4/5 (former-arm
soundness recurses through children that may be λ/app subjects, so it needs the full mutual
soundness induction); completeness is STR-6; rename-reflection is STR-8.

## Zero-axiom verification

The inductive pair mirrors `HasTypeDescPi`/`DescTelescopePi`'s index discipline exactly (no
sibling references in index signatures, positive occurrences only).  `absorbConv` is a full
6-arm structural match composing `Conv.trans`; the soundness lemmas compose
`ofFormation`/`var`/`universeFormation` with the grown `conv` rule.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

mutual

/-- Syntax-directed grown checking: one arm per subject head shape, recursive premises only on
strict subterms, `Conv` only at compare leaves, no typehood premises. -/
inductive GrownCheck (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope →
      RawTerm scope → RawTerm scope → Prop where
  | var {scope : Nat} {context : TypingContext profile scope}
      (index : Fin scope) {target : RawTerm scope}
      (lookupConverts : Conv (context.lookup index) target) :
      GrownCheck profile context (variableCell index) target
  | universeCode {scope : Nat} {context : TypingContext profile scope}
      (levelExpr : LevelExpr) (flag : UniverseFlag) {target : RawTerm scope}
      (successorConverts : Conv (universeCodeCell levelExpr.lsucc flag) target) :
      GrownCheck profile context (universeCodeCell levelExpr flag) target
  | former {scope : Nat} {context : TypingContext profile scope}
      (generator : Generator) (payload : generator.payload scope)
      (children : RawTermChildren generator.binderShifts scope)
      (levels : List LevelExpr) (flag : UniverseFlag)
      (rule : TypingRuleDesc) {target : RawTerm scope}
      (isFormation : typingRuleDescOf generator = some rule)
      (premises :
        GrownCheckTelescope profile (currentDepth := 0) context levels flag children)
      (outputConverts : Conv (rule.outputType scope levels flag) target) :
      GrownCheck profile context (.mkGen generator payload children) target
  | lam {scope : Nat} {context : TypingContext profile scope}
      {body : RawTerm (scope + 1)}
      (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
      {target : RawTerm scope}
      (targetConverts : Conv (piTyCodeCell domainCode codomainCode) target)
      (bodyChecks : GrownCheck profile (context.cons domainCode) body codomainCode) :
      GrownCheck profile context (lamCell body) target
  | app {scope : Nat} {context : TypingContext profile scope}
      {functionTerm argument : RawTerm scope}
      (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
      {target : RawTerm scope}
      (functionChecks :
        GrownCheck profile context functionTerm (piTyCodeCell domainCode codomainCode))
      (argumentChecks : GrownCheck profile context argument domainCode)
      (outputConverts : Conv (RawTerm.subst0 codomainCode argument) target) :
      GrownCheck profile context (appCell functionTerm argument) target

/-- The check relation's premise spine — `DescTelescopePi` with `GrownCheck` heads. -/
inductive GrownCheckTelescope (profile : PolyProfile) :
    {baseScope : Nat} → {currentDepth : Nat} → {binderShifts : List Nat} →
      TypingContext profile (baseScope + currentDepth) →
      List LevelExpr → UniverseFlag →
      RawTermChildren binderShifts baseScope → Prop where
  | nil {baseScope currentDepth : Nat}
      (context : TypingContext profile (baseScope + currentDepth))
      (flag : UniverseFlag) :
      GrownCheckTelescope profile context [] flag .childNil
  | cons {baseScope currentDepth : Nat} {restShifts : List Nat}
      (context : TypingContext profile (baseScope + currentDepth))
      (head : RawTerm (baseScope + currentDepth))
      (headLevel : LevelExpr) (restLevels : List LevelExpr) (flag : UniverseFlag)
      (rest : RawTermChildren restShifts baseScope)
      (headChecks : GrownCheck profile context head (universeCodeCell headLevel flag))
      (restChecks :
        GrownCheckTelescope profile (currentDepth := currentDepth + 1)
          (context.cons head) restLevels flag rest) :
      GrownCheckTelescope profile context (headLevel :: restLevels) flag
        (.childCons head rest)

end

/-- Conv-ABSORPTION: every arm absorbs a trailing `Conv` into its compare leaf by `Conv.trans` —
recursion-free because `Conv` appears uniformly at the leaves.  The completeness induction's
`conv`-arm discharge. -/
theorem GrownCheck.absorbConv {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject target reclassifier : RawTerm scope}
    (checked : GrownCheck profile context subject target)
    (converts : Conv target reclassifier) :
    GrownCheck profile context subject reclassifier :=
  match checked with
  | .var index lookupConverts =>
      .var index (lookupConverts.trans converts)
  | .universeCode levelExpr flag successorConverts =>
      .universeCode levelExpr flag (successorConverts.trans converts)
  | .former generator payload children levels flag rule isFormation premises outputConverts =>
      .former generator payload children levels flag rule isFormation premises
        (outputConverts.trans converts)
  | .lam domainCode codomainCode targetConverts bodyChecks =>
      .lam domainCode codomainCode (targetConverts.trans converts) bodyChecks
  | .app domainCode codomainCode functionChecks argumentChecks outputConverts =>
      .app domainCode codomainCode functionChecks argumentChecks
        (outputConverts.trans converts)

/-- Variable-arm SOUNDNESS at a typed target: the var rule at the natural lookup, reclassified
through the leaf `Conv` by the grown `conv` rule. -/
theorem GrownCheck.variableSoundAtTypedTarget {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (index : Fin scope)
    {target : RawTerm scope} {targetLevel : LevelExpr} {targetFlag : UniverseFlag}
    (targetTyped :
      HasTypeDescPi profile context target (universeCodeCell targetLevel targetFlag))
    (lookupConverts : Conv (context.lookup index) target) :
    HasTypeDescPi profile context (variableCell index) target :=
  HasTypeDescPi.conv targetLevel targetFlag
    (HasTypeDescPi.ofFormation (HasTypeDesc.var context index)) lookupConverts targetTyped

/-- Universe-code-arm SOUNDNESS at a typed target — twin of the variable arm. -/
theorem GrownCheck.universeCodeSoundAtTypedTarget {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    {target : RawTerm scope} {targetLevel : LevelExpr} {targetFlag : UniverseFlag}
    (targetTyped :
      HasTypeDescPi profile context target (universeCodeCell targetLevel targetFlag))
    (successorConverts : Conv (universeCodeCell levelExpr.lsucc flag) target) :
    HasTypeDescPi profile context (universeCodeCell levelExpr flag) target :=
  HasTypeDescPi.conv targetLevel targetFlag
    (HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation context levelExpr flag))
    successorConverts targetTyped

/-- Smoke: the identity λ checks at its Π-type (lam arm, `Conv.refl` leaves). -/
theorem grownCheckIdentityLambdaSmoke (profile : PolyProfile) :
    GrownCheck profile (TypingContext.empty (profile := profile))
      (lamCell (variableCell ⟨0, Nat.zero_lt_succ 0⟩))
      (piTyCodeCell (typeZeroCode 0) (typeZeroCode 1)) :=
  GrownCheck.lam (typeZeroCode 0) (typeZeroCode 1)
    (Conv.refl _)
    (GrownCheck.var ⟨0, Nat.zero_lt_succ 0⟩ (Conv.refl _))

/-- Smoke: STR-1's escaping reclassifier is `GrownCheck`-reachable — `weaken Type@0` checks at
`(λ. Type@1)(var 0)` through the universe arm's `Conv` leaf.  This is the β-expansion the
Conv-existential reflection statement (STR-8) must absorb, and the reason its conclusion is
`∃ S₀, Conv S (rename S₀) ∧ …` rather than the syntactic image form. -/
theorem grownCheckEscapingReclassifierSmoke (profile : PolyProfile) :
    GrownCheck profile
      ((TypingContext.empty (profile := profile)).cons (typeZeroCode 0))
      (RawTerm.weaken (typeZeroCode 0))
      escapingReclassifier :=
  have betaStep : Step escapingReclassifier
      (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard) :=
    Step.beta
  GrownCheck.universeCode LevelExpr.lzero UniverseFlag.standard
    (Conv.fromStep betaStep).sym

end FX1Poly.Typed
