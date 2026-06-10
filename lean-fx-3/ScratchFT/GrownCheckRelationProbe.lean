import FX1Poly.Typed.GrownStrengtheningRefutation

/-! Probe: GrownCheck — the syntax-directed grown checking RELATION (STR-3).

Per the STR-2 census verdicts: a relation (not a Decidable), every recursive premise on a strict
subterm, `Conv` ONLY at compare leaves (uniform — so conv-absorption is per-arm `Conv.trans`,
recursion-free), NO typehood premises (maximal reflectability).  Mutual telescope sub-relation
mirrors `DescTelescopePi` with `GrownCheck` heads. -/

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
recursion-free because `Conv` appears uniformly at the leaves. -/
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

/-- Smoke: STR-1's escaping reclassifier is GrownCheck-reachable — `weaken Type@0` checks at
`(λ. Type@1)(var 0)` through the universe arm's `Conv` leaf (the β-expansion the conv-existential
reflection statement must absorb). -/
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

#print axioms FX1Poly.Typed.GrownCheck
#print axioms FX1Poly.Typed.GrownCheckTelescope
#print axioms FX1Poly.Typed.GrownCheck.absorbConv
#print axioms FX1Poly.Typed.GrownCheck.variableSoundAtTypedTarget
#print axioms FX1Poly.Typed.GrownCheck.universeCodeSoundAtTypedTarget
#print axioms FX1Poly.Typed.grownCheckIdentityLambdaSmoke
#print axioms FX1Poly.Typed.grownCheckEscapingReclassifierSmoke

end FX1Poly.Typed
