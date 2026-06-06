import FX1Poly.Typed.FundamentalLevelIndexed
import FX1Poly.Typed.ClosedLevelIndexed

/-! # FX1Poly/Typed/ValidTyping
    — the level-annotated typing (Abel validity-derivation-indexed relation): the recursor, var/universe/conv/Π/Σ core

The level-indexed fundamental theorem has all its per-constructor ARMS shipped as standalone lemmas
(`FundamentalLevelIndexed.lean`).  The RECURSOR that assembles them must work around the var/conv coordination
wall: a single level-free motive cannot serve both `var` (concludes at its env-fixed level `contextLevels
index`) and `conv` (needs the reclassifier reducible one level ABOVE the subject).

The Abel/Adjedj resolution (arXiv:2310.06376) is to index the relation by a VALIDITY DERIVATION carrying each
node's level.  `ValidTyping` realizes this directly: it is the formation typing with the level annotated INTO
the inductive, so the coordination holds BY CONSTRUCTION —

* `var` concludes at `contextLevels index` (its env level);
* `conv`'s `reclassifierTyped` is at `subjectLevel + 1` (one level up, exactly what `tarskiDecode` + the
  conv-transport need);
* `universeFormation` is level-polymorphic (any `predLevel + 1`);
* `piIntro` checks domain & codomain codes at `predLevel + 1 + 1` (their universe sits one above the function's
  level) and the body at `predLevel + 1` under `levelCons (predLevel + 1)` (the bound variable's env level);
* `piElim` keeps function, argument, and application at one shared `subjectLevel`;
* `piFormation` / `sigmaFormation` (the TYPE formers): the domain children are `∀ aboveLevel`-quantified — a type
  CODE's membership in a universe is fuel-polymorphic (unlike a term, whose level is env-pinned), so the former
  needs the domain reducible at every level (Π/Σ formation consumes it at `predLevel` AND `predLevel + 1`).  Π's
  codomain is likewise `∀ headLevel`; Σ's codomain is a single derivation at `predLevel + 1` (the data-former
  route, classified by SN of the domain alone).

With the levels pinned by the constructor, the fundamental theorem `ValidTyping.fundamental` is a CLEAN single
induction (`ValidTyping.rec`): each arm is discharged verbatim by the shipped level-indexed arm
(`fundamentalVarLevelIndexed` / `…UniverseFormation…` / `…Conv…` / `…PiIntro…` / `…PiElim…` / `…PiFormation…` /
`…SigmaFormation…`).  `conv` threads two IHs, `piIntro` three (under the extended env), and the former arms
thread `∀`-quantified IHs (the recursor turns a `∀ aboveLevel, ValidTyping …` premise into a `∀ aboveLevel,
FundamentalConclusion…` IH — exactly the fuel-polymorphic shape the former arm consumes).  This is the assembled
recursor on the dependent-FT lane — the var/conv wall broken, extended through the COMPUTATIONAL core
(λ-introduction + application) and the TYPE-former core (Π/Σ codes).

## Honest scope

This covers `var` / `universeFormation` / `conv` / `piIntro` / `piElim` / `piFormation` / `sigmaFormation` — the
leaf+conv core, the function/application computational core, AND the Π/Σ type-former core.  Worked SN witnesses
through the recursor: the closed identity `λx.x : Π(_ : U). U` (`validTyping_identity_stronglyNormalizing`, a
binder with a bound-variable occurrence) and the closed Π/Σ codes between universes
(`validTyping_{pi,sigma}BetweenUniverses_stronglyNormalizing`).  Two pieces remain to land full
SN-for-well-typed: (1) the GENERIC `genFormation` arm — the table-driven former over an arbitrary
`DescTelescope` (threading the shipped `fundamentalGenFormationFormerLevelIndexed`), of which the specific Π/Σ
formers here are the concrete instances; (2) the LEVELING bridge `HasTypeDescPi → ValidTyping` (every level-free
derivation admits a consistent leveling — `var` at the context's recorded level, `conv`'s reclassifier re-leveled
one up since universe-code members are level-polymorphic).  This file establishes that, once levels are
annotated, the recursor assembles through the binder AND former arms.

## Zero-axiom verification

The inductive is strictly positive (mentions `Conv` and itself only positively; index signature is
non-self-referential).  `fundamental` is `ValidTyping.rec` (propext-free recursor) + the shipped arms;
`closedStronglyNormalizing` composes it with the closed-SN handoff.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **Level-annotated formation typing** (the Abel validity-derivation-indexed relation, leaf+conv core).  The
levels are part of the inductive, so the var/conv level coordination that blocks the level-free recursor holds
by construction. -/
inductive ValidTyping (profile : PolyProfile) :
    {scope : Nat} → (Fin scope → Nat) → Nat → TypingContext profile scope →
      RawTerm scope → RawTerm scope → Prop where
  | var {scope : Nat} (contextLevels : Fin scope → Nat)
      (context : TypingContext profile scope) (index : Fin scope) :
      ValidTyping profile contextLevels (contextLevels index) context
        (variableCell index) (context.lookup index)
  | universeFormation {scope : Nat} (contextLevels : Fin scope → Nat) (predLevel : Nat)
      (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag) :
      ValidTyping profile contextLevels (predLevel + 1) context
        (universeCodeCell levelExpr flag) (universeCodeCell levelExpr.lsucc flag)
  | conv {scope : Nat} (contextLevels : Fin scope → Nat) (subjectLevel : Nat)
      {context : TypingContext profile scope}
      {subject classifier reclassifier : RawTerm scope}
      {levelExpr : LevelExpr} {flag : UniverseFlag}
      (typed : ValidTyping profile contextLevels subjectLevel context subject classifier)
      (converts : Conv classifier reclassifier)
      (reclassifierTyped : ValidTyping profile contextLevels (subjectLevel + 1) context
        reclassifier (universeCodeCell levelExpr flag)) :
      ValidTyping profile contextLevels subjectLevel context subject reclassifier
  | piIntro {scope : Nat} (contextLevels : Fin scope → Nat) (predLevel : Nat)
      {context : TypingContext profile scope}
      {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
      {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
      (domainTyped : ValidTyping profile contextLevels (predLevel + 1 + 1) context
        domainCode (universeCodeCell domainLevel flag))
      (codomainTyped : ValidTyping profile (levelCons (predLevel + 1) contextLevels)
        (predLevel + 1 + 1) (context.cons domainCode) codomainCode (universeCodeCell codomainLevel flag))
      (bodyTyped : ValidTyping profile (levelCons (predLevel + 1) contextLevels)
        (predLevel + 1) (context.cons domainCode) body codomainCode) :
      ValidTyping profile contextLevels (predLevel + 1) context
        (lamCell body) (piTyCodeCell domainCode codomainCode)
  | piElim {scope : Nat} (contextLevels : Fin scope → Nat) (subjectLevel : Nat)
      {context : TypingContext profile scope}
      {functionTerm argument domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
      (functionTyped : ValidTyping profile contextLevels subjectLevel context functionTerm
        (piTyCodeCell domainCode codomainCode))
      (argumentTyped : ValidTyping profile contextLevels subjectLevel context argument domainCode) :
      ValidTyping profile contextLevels subjectLevel context
        (appCell functionTerm argument) (RawTerm.subst0 codomainCode argument)
  | piFormation {scope : Nat} (contextLevels : Fin scope → Nat) (predLevel : Nat)
      {context : TypingContext profile scope}
      {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
      {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
      (domainTyped : ∀ aboveLevel : Nat,
        ValidTyping profile contextLevels (aboveLevel + 1) context domainCode
          (universeCodeCell domainLevel flag))
      (codomainTyped : ∀ headLevel : Nat,
        ValidTyping profile (levelCons headLevel contextLevels) (predLevel + 1)
          (context.cons domainCode) codomainCode (universeCodeCell codomainLevel flag)) :
      ValidTyping profile contextLevels (predLevel + 1) context
        (piTyCodeCell domainCode codomainCode) (universeCodeCell formerLevel flag)
  | sigmaFormation {scope : Nat} (contextLevels : Fin scope → Nat) (predLevel : Nat)
      {context : TypingContext profile scope}
      {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
      {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
      (domainTyped : ∀ aboveLevel : Nat,
        ValidTyping profile contextLevels (aboveLevel + 1) context domainCode
          (universeCodeCell domainLevel flag))
      (codomainTyped : ValidTyping profile (levelCons (predLevel + 1) contextLevels) (predLevel + 1)
        (context.cons domainCode) codomainCode (universeCodeCell codomainLevel flag)) :
      ValidTyping profile contextLevels (predLevel + 1) context
        (sigmaTyCodeCell domainCode codomainCode) (universeCodeCell formerLevel flag)
  | genFormationPi {scope : Nat} (contextLevels : Fin scope → Nat) (predLevel : Nat)
      {context : TypingContext profile scope}
      (generator : Generator) (payload : generator.payload scope)
      {children : RawTermChildren generator.binderShifts scope}
      {levels : List LevelExpr} {flag : UniverseFlag} {rule : TypingRuleDesc}
      (isFormation : typingRuleDescOf generator = some rule)
      (premises : DescTelescopePi profile (currentDepth := 0) context levels flag children)
      (telescopeFundamental :
        ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
          (_env : ReducibleEnvVec contextLevels context substitution)
          (shapeEq : generator.binderShifts = consecutiveShifts 0 levels.length),
          TelescopeReducible flag 0 levels.length substitution levels (shapeEq ▸ children)) :
      ValidTyping profile contextLevels (predLevel + 1) context
        (.mkGen generator payload children) (rule.outputType scope levels flag)

/-- **The fundamental theorem over `ValidTyping`** — the assembled recursor for the var/universe/conv/Π/Σ core
plus the generic `genFormationPi` former arm (SN-021), discharged by `fundamentalGenFormationFormerLevelIndexed`
from the ctor's carried `premises`/`telescopeFundamental`.  A
clean single induction (`ValidTyping.rec`): each arm is discharged verbatim by the shipped level-indexed arm
(`fundamentalVarLevelIndexed` / `…UniverseFormation…` / `…Conv…` / `…PiIntro…` / `…PiElim…` / `…PiFormation…` /
`…SigmaFormation…`).  `conv` threads its two IHs (subject at `subjectLevel`, reclassifier at `subjectLevel + 1`);
`piIntro` threads three (domain & codomain codes at `predLevel + 1 + 1`, body at `predLevel + 1`, under the
extended `levelCons` environment); `piElim` threads function & argument at the same level; `piFormation` /
`sigmaFormation` thread `∀`-quantified IHs (the recursor lifts each `∀ aboveLevel, ValidTyping …` premise to a
`∀ aboveLevel, FundamentalConclusion…` IH — the fuel-polymorphic shape the former arms require for a type code's
universe membership).  Because the inductive carries the per-arm level environments as genuine indices,
`induction` binds `contextLevels` as a named arm variable in every arm (it is threaded explicitly to each shipped
lemma, not inferred). -/
theorem ValidTyping.fundamental {profile : PolyProfile} {scope : Nat}
    {contextLevels : Fin scope → Nat} {subjectLevel : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : ValidTyping profile contextLevels subjectLevel context subject classifier) :
    FundamentalConclusionLevelIndexed contextLevels subjectLevel context subject classifier := by
  induction typed with
  | var contextLevels context index =>
      exact fundamentalVarLevelIndexed contextLevels context index
  | universeFormation contextLevels predLevel context levelExpr flag =>
      exact fundamentalUniverseFormationLevelIndexed contextLevels predLevel context levelExpr flag
  | conv contextLevels subjectLevel _typed converts _reclassifierTyped typedIH reclassifierIH =>
      exact fundamentalConvLevelIndexed contextLevels subjectLevel typedIH reclassifierIH converts
  | piIntro contextLevels predLevel _domainTyped _codomainTyped _bodyTyped domainIH codomainIH bodyIH =>
      exact fundamentalPiIntroLevelIndexed contextLevels predLevel domainIH codomainIH bodyIH
  | piElim contextLevels subjectLevel _functionTyped _argumentTyped functionIH argumentIH =>
      exact fundamentalPiElimLevelIndexed contextLevels subjectLevel functionIH argumentIH
  | piFormation contextLevels predLevel _domainTyped _codomainTyped domainIH codomainIH =>
      exact fundamentalPiFormationLevelIndexed contextLevels predLevel domainIH codomainIH
  | sigmaFormation contextLevels predLevel _domainTyped _codomainTyped domainIH codomainIH =>
      exact fundamentalSigmaFormationLevelIndexed contextLevels predLevel domainIH codomainIH
  | genFormationPi contextLevels predLevel _generator payload isFormation premises telescopeFundamental =>
      exact fundamentalGenFormationFormerLevelIndexed contextLevels predLevel payload isFormation
        premises telescopeFundamental

/-- **Closed strong normalization from `ValidTyping`** — the recursor's payoff for this fragment: a closed
`ValidTyping` derivation at a positive level is UNCONDITIONALLY strongly normalizing (FT + the empty-context
closed-SN handoff).  This is SN-for-well-typed for the leaf+conv core, assembled through the recursor. -/
theorem ValidTyping.closedStronglyNormalizing {profile : PolyProfile} (predLevel : Nat)
    {subject classifier : RawTerm 0}
    (typed : ValidTyping profile emptyLevelVector (predLevel + 1)
      (TypingContext.empty : TypingContext profile 0) subject classifier) :
    IsStronglyNormalizing subject :=
  closedSubjectStronglyNormalizingFromLevelIndexed predLevel typed.fundamental

/-- **Smoke: the recursor path lands SN end-to-end.**  A closed universe code is `ValidTyping`-derivable (the
`universeFormation` arm at the empty context), and `closedStronglyNormalizing` discharges it to plain SN
through the assembled fundamental theorem — demonstrating the recursor is non-vacuous (it produces genuine SN,
not just a vacuous conclusion). -/
theorem validTyping_universeCode_stronglyNormalizing {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing (universeCodeCell levelExpr flag : RawTerm 0) :=
  ValidTyping.closedStronglyNormalizing (profile := profile) 0
    (ValidTyping.universeFormation emptyLevelVector 0
      (TypingContext.empty : TypingContext profile 0) levelExpr flag)

/-- **Smoke: the closed identity `λx.x` is SN through the recursor's `piIntro` arm.**  This exercises the
computational core: the lambda binds a real variable (`bodyTyped` is the `var` arm at the extended context), so
`piIntro` is applied non-vacuously — the recursor threads `var` under a binder and `closedStronglyNormalizing`
discharges the whole lambda to plain SN.  The function has type `Π(_ : U). U` (universe-to-universe identity).
This is the first SN witness on the dependent-FT lane whose subject contains a binder AND a bound-variable
occurrence — the shape where β-redexes live. -/
theorem validTyping_identity_stronglyNormalizing {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) : RawTerm 0) :=
  ValidTyping.closedStronglyNormalizing (profile := profile) 0
    (ValidTyping.piIntro emptyLevelVector 0
      (domainLevel := levelExpr.lsucc) (codomainLevel := levelExpr.lsucc) (flag := flag)
      (ValidTyping.universeFormation emptyLevelVector 1
        (TypingContext.empty : TypingContext profile 0) levelExpr flag)
      (ValidTyping.universeFormation (levelCons 1 emptyLevelVector) 1
        ((TypingContext.empty : TypingContext profile 0).cons (universeCodeCell levelExpr flag))
        levelExpr flag)
      (ValidTyping.var (levelCons 1 emptyLevelVector)
        ((TypingContext.empty : TypingContext profile 0).cons (universeCodeCell levelExpr flag))
        (⟨0, Nat.succ_pos 0⟩ : Fin 1)))

/-- **Smoke: a closed Π type-code between universes is SN through the recursor's `piFormation` arm.**  The
former's domain children are supplied at EVERY level — `fun aboveLevel => universeFormation … aboveLevel …`
realizes the `∀ aboveLevel` premise, reflecting that a type CODE's membership in a universe is fuel-polymorphic
(unlike a term/variable, whose level is env-pinned).  The codomain children likewise at every head level.  So
`Π(Type@e). Type@e : Type@(e+1)` is strongly normalizing through the recursor. -/
theorem validTyping_piBetweenUniverses_stronglyNormalizing {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing
      (piTyCodeCell (universeCodeCell levelExpr flag) (universeCodeCell levelExpr flag) : RawTerm 0) :=
  ValidTyping.closedStronglyNormalizing (profile := profile) 0
    (ValidTyping.piFormation emptyLevelVector 0
      (domainLevel := levelExpr.lsucc) (codomainLevel := levelExpr.lsucc)
      (formerLevel := levelExpr.lsucc) (flag := flag)
      (fun aboveLevel => ValidTyping.universeFormation emptyLevelVector aboveLevel
        (TypingContext.empty : TypingContext profile 0) levelExpr flag)
      (fun headLevel => ValidTyping.universeFormation (levelCons headLevel emptyLevelVector) 0
        ((TypingContext.empty : TypingContext profile 0).cons (universeCodeCell levelExpr flag))
        levelExpr flag))

/-- **Smoke: a closed Σ type-code between universes is SN through the recursor's `sigmaFormation` arm.**  The
data-former twin — Σ formation is classified by SN of the domain alone, so its codomain child is a SINGLE
fixed-level derivation (at `predLevel + 1`) rather than the `∀ headLevel` family the Π codomain needs. -/
theorem validTyping_sigmaBetweenUniverses_stronglyNormalizing {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing
      (sigmaTyCodeCell (universeCodeCell levelExpr flag) (universeCodeCell levelExpr flag) : RawTerm 0) :=
  ValidTyping.closedStronglyNormalizing (profile := profile) 0
    (ValidTyping.sigmaFormation emptyLevelVector 0
      (domainLevel := levelExpr.lsucc) (codomainLevel := levelExpr.lsucc)
      (formerLevel := levelExpr.lsucc) (flag := flag)
      (fun aboveLevel => ValidTyping.universeFormation emptyLevelVector aboveLevel
        (TypingContext.empty : TypingContext profile 0) levelExpr flag)
      (ValidTyping.universeFormation (levelCons (0 + 1) emptyLevelVector) 0
        ((TypingContext.empty : TypingContext profile 0).cons (universeCodeCell levelExpr flag))
        levelExpr flag))

/-! ## Open-context handoffs (UNCONDITIONAL)

The closed-SN handoffs in `ClosedLevelIndexed.lean` (`closedSubject{Reducible,StronglyNormalizing}FromLevelIndexed`)
take the level-indexed fundamental conclusion as an explicit HYPOTHESIS.  Over `ValidTyping` the fundamental
theorem is PROVED (`ValidTyping.fundamental`), so the corresponding handoffs are UNCONDITIONAL, and they hold in
ANY context (not just the empty one): a ValidTyping
subject is a reducible member — hence strongly normalizing — under EVERY reducible closing environment.
`ValidTyping.closedStronglyNormalizing` is the empty-context special case (vacuous environment). -/

/-- **Open reducibility handoff (unconditional).**  A `ValidTyping` derivation at a positive level is a reducible
member of its (substituted) classifier under any reducible closing environment — `ValidTyping.fundamental`
instantiated at that environment.  The open generalization of `closedSubjectReducibleFromLevelIndexed`, now with
no hypothesis (the fundamental theorem is assembled). -/
theorem ValidTyping.substReducible {profile : PolyProfile} {scope targetScope : Nat}
    (predLevel : Nat) {contextLevels : Fin scope → Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : ValidTyping profile contextLevels (predLevel + 1) context subject classifier)
    (substitution : RawTermSubst scope (targetScope + 1))
    (env : ReducibleEnvVec contextLevels context substitution) :
    IsReducibleMemberAt (predLevel + 1)
      (RawTerm.subst substitution classifier) (RawTerm.subst substitution subject) :=
  typed.fundamental substitution env

/-- **Open strong-normalization handoff (unconditional).**  The substituted subject of a `ValidTyping` derivation
is strongly normalizing under any reducible closing environment: open reducibility (`substReducible`) followed by
CR1 (`IsReducibleMemberAt.stronglyNormalizing`, at the positive level `predLevel + 1`; the substituted subject
lands in the positive scope `targetScope + 1` CR1 requires).  The open generalization of
`closedSubjectStronglyNormalizingFromLevelIndexed`, unconditional through the assembled recursor. -/
theorem ValidTyping.substStronglyNormalizing {profile : PolyProfile} {scope targetScope : Nat}
    (predLevel : Nat) {contextLevels : Fin scope → Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : ValidTyping profile contextLevels (predLevel + 1) context subject classifier)
    (substitution : RawTermSubst scope (targetScope + 1))
    (env : ReducibleEnvVec contextLevels context substitution) :
    IsStronglyNormalizing (RawTerm.subst substitution subject) :=
  (typed.substReducible predLevel substitution env).stronglyNormalizing

/-- **Smoke: an OPEN term is SN through the open handoff.**  A free variable `x : Type@(e+1)` in a one-entry
context, closed by the substitution `x ↦ Type@e` (which IS a reducible member of `x`'s type, by
`IsReducibleMemberAt.universeFormation`), is strongly normalizing through `substStronglyNormalizing`.  The first
SN witness in this file for a NON-closed subject — exercising the open handoff with a genuine (non-vacuous)
reducible environment.  The environment is built by the propext-free `Fin 1` position split (the impossible
`k + 1` position is refuted structurally via `Nat.lt_of_succ_lt_succ`, never `omega`/`Fin.cases`). -/
theorem validTyping_openVariable_substStronglyNormalizing {profile : PolyProfile}
    (predLevel : Nat) (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing
      (RawTerm.subst
        (fun _index => (universeCodeCell levelExpr flag : RawTerm 1))
        (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) := by
  have typed :
      ValidTyping profile (levelCons (predLevel + 1) emptyLevelVector) (predLevel + 1)
        ((TypingContext.empty : TypingContext profile 0).cons
          (universeCodeCell levelExpr.lsucc flag))
        (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
        (((TypingContext.empty : TypingContext profile 0).cons
          (universeCodeCell levelExpr.lsucc flag)).lookup (⟨0, Nat.succ_pos 0⟩ : Fin 1)) :=
    ValidTyping.var (levelCons (predLevel + 1) emptyLevelVector)
      ((TypingContext.empty : TypingContext profile 0).cons (universeCodeCell levelExpr.lsucc flag))
      (⟨0, Nat.succ_pos 0⟩ : Fin 1)
  exact typed.substStronglyNormalizing predLevel
    (fun _index => (universeCodeCell levelExpr flag : RawTerm 1))
    (fun index =>
      match index with
      | ⟨0, _⟩ => IsReducibleMemberAt.universeFormation predLevel levelExpr flag
      | ⟨_priorValue + 1, isLtSucc⟩ =>
          (Nat.not_lt_zero _priorValue (Nat.lt_of_succ_lt_succ isLtSucc)).elim)

/-! ## Per-arm recursor non-vacuity corpus (completing piElim + conv)

The smokes above witness the recursor's `universeFormation` / `piIntro` / `var` / `piFormation` /
`sigmaFormation` arms producing genuine SN.  These two complete the corpus — `piElim` (application, the genuine
β-reducing arm) and `conv` (the type-reclassification arm). -/

/-- **Smoke: a closed β-redex is SN through the recursor's `piElim` arm.**  `(λx.x)(Type@e)` — the closed
identity applied to a universe code — reduces (β) and is strongly normalizing through the recursor's application
arm, composed over `piIntro` (the identity, `λ(x : Type@(e+2)). x : Π(Type@(e+2)). Type@(e+2)`) and
`universeFormation` (the argument `Type@e : Type@(e+2)`).  The genuinely-reducing witness for `piElim`. -/
theorem validTyping_betaRedex_stronglyNormalizing {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing
      (appCell (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
        (universeCodeCell levelExpr flag) : RawTerm 0) :=
  ValidTyping.closedStronglyNormalizing (profile := profile) 0
    (ValidTyping.piElim emptyLevelVector 1
      (ValidTyping.piIntro emptyLevelVector 0
        (domainLevel := levelExpr.lsucc.lsucc) (codomainLevel := levelExpr.lsucc.lsucc) (flag := flag)
        (ValidTyping.universeFormation emptyLevelVector 1
          (TypingContext.empty : TypingContext profile 0) levelExpr.lsucc flag)
        (ValidTyping.universeFormation (levelCons 1 emptyLevelVector) 1
          ((TypingContext.empty : TypingContext profile 0).cons
            (universeCodeCell levelExpr.lsucc flag)) levelExpr.lsucc flag)
        (ValidTyping.var (levelCons 1 emptyLevelVector)
          ((TypingContext.empty : TypingContext profile 0).cons
            (universeCodeCell levelExpr.lsucc flag))
          (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
      (ValidTyping.universeFormation emptyLevelVector 0
        (TypingContext.empty : TypingContext profile 0) levelExpr flag))

/-- **Smoke: a universe code re-typed through the recursor's `conv` arm is SN.**  The conversion is REFLEXIVITY —
a closed ValidTyping-derived term never has a REDEX type (`piElim`'s result is `subst0`, already computed; the
other arms conclude at universe codes), so no genuine closed type-conversion is constructible in this fragment.
The arm's level coordination is still exercised end-to-end: the subject sits at `subjectLevel`, the reclassifier
is typed as a universe member ONE LEVEL UP (`subjectLevel + 1`), and `fundamentalConvLevelIndexed` runs its
`tarskiDecode` + `castAlongConv` transport through the recursor.  The non-vacuity witness for `conv`. -/
theorem validTyping_convRefl_stronglyNormalizing {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing (universeCodeCell levelExpr flag : RawTerm 0) :=
  ValidTyping.closedStronglyNormalizing (profile := profile) 0
    (ValidTyping.conv emptyLevelVector 1
      (ValidTyping.universeFormation emptyLevelVector 0
        (TypingContext.empty : TypingContext profile 0) levelExpr flag)
      (Conv.refl _)
      (ValidTyping.universeFormation emptyLevelVector 1
        (TypingContext.empty : TypingContext profile 0) levelExpr.lsucc flag))

end FX1Poly.Typed
