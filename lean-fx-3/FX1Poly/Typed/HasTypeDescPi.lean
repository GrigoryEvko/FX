import FX1Poly.Typed.HasTypeDescApplication

/-! # FX1Poly/Typed/HasTypeDescPi — GROWING THE ENGINE PAST FORMATION: Π-introduction +
    Π-elimination, and the FIRST non-vacuous subject reduction in the kernel.

For many fires the typed-layer decouple was complete for the FORMATION fragment (validity,
inversion, uniqueness-spine, weakening+substitution for both spines, dependent-eliminator
output-validity) but BLOCKED on growth: subject reduction and canonicity are DEGENERATE on
the redex-free formation fragment, and the redex-creating term-formers (λ/app) could not land
in `HasTypeDesc` without breaking the shipped TOTAL `toHasType ⟺ HasType` cross-check (any new
gen row makes the soundness map non-exhaustive), which cascades into decidability + uniqueness.

## The unblock (polycell.md §11.8.5): 0-FP is FREE BY CONSTRUCTION

§11.8.5: "0 false positives = soundness = intrinsic introduction rules ⇒ empty fiber over the
unsound.  Free by construction, not a theorem to chase."  The `toHasType ⟺ HasType` map was
only ever a CROSS-CHECK for the formation fragment, NOT the source of soundness.  So the engine
can grow past formation ADDITIVELY: `HasTypeDescPi` EMBEDS the whole formation fragment
(`ofFormation`) and adds the Π term-formers, with soundness by-construction (correct intro
rules) plus the already-proven dependent-eliminator output-validity.  This leaves `HasTypeDesc`,
`toHasType`, `HasTypeDesc.decidableOfWellFormed`, and the uniqueness proofs UNTOUCHED and green
— it sidesteps the decidability/uniqueness cascade that a direct `HasTypeDesc` extension forces.

`HasTypeDesc` cannot type `lamCell`/`appCell` (their generators `gen_lam`/`gen_app` have no
`typingRuleDescOf` row, so the `genFormation` arm cannot produce them) — so `ofFormation` of a
β-redex is impossible, and `HasTypeDescPi` genuinely EXTENDS coverage rather than relabelling.

## The arms

* `ofFormation` — embed any formation derivation (var/conv/universeFormation/genFormation).
* `conv` — conversion at the grown level (mirror of `HasTypeDesc.conv`; the formation `conv`
  only relates formation terms, so the grown engine needs its own).
* `piFormation` / `sigmaFormation` — NATIVE dependent type-former formation: `domain : Type@dl`
  and `codomain : Type@cl` (under the domain binder) give `Π/Σ domain. codomain : Type@(dl ⊔
  cl)`.  These exist (rather than only `ofFormation`) so the engine is SUBSTITUTION-CLOSED:
  substituting a grown term (e.g. an application) into a `piTyCodeCell` component yields a Π type
  with a NON-formation component, which `ofFormation` cannot type — but `piFormation` can.  They
  are the prerequisite for the grown-engine substitution leg (the `ofFormation` case of
  `substRespectingContext` rebuilds a substituted formation Π/Σ via these native arms).
* `piIntro` (λ) — `body : codomainCode` under `context.cons domainCode`, with `domainCode` a
  type (witness exposed as `domainLevel`/`domainFlag`/`domainTyped`, per the
  nested-`Exists`-in-a-ctor-premise rejection), gives `lamCell body : Π domainCode. codomainCode`.
* `piElim` (app) — `functionTerm : Π domainCode. codomainCode` and `argument : domainCode` give
  `appCell functionTerm argument : codomainCode[argument]` (`subst0`, the motive-dependent
  output realised via the intrinsic β-engine).

## The headline: first non-vacuous subject reduction

`betaCoherence_formationBody` proves that for a β-redex built from FORMATION components, the
redex `appCell (lamCell body) argument` AND its β-reduct `subst0 body argument` are BOTH typed
at `subst0 codomainCode argument` — the β-rule preserves typing.  Honest scope: this is the
PRESERVATION direction for COMPONENT-derived redexes (built from the pieces), reusing the
shipped intrinsic `HasTypeDesc.substituteUnderBinding`; the fully-general inverted SR (arbitrary
`HasTypeDescPi` derivation modulo `conv`, arbitrary `HasTypeDescPi` body) follows once Π-arm
inversion + the grown-engine substitution land (next fires).  It is the FIRST SR in the kernel
that is genuinely non-vacuous — a redex that actually reduces, whose reduct retypes.

## Zero-axiom

A new inductive (strictly positive: `HasTypeDescPi` only in premises, `HasTypeDesc` positively
in `ofFormation`) + the shipped `HasTypeDesc.substituteUnderBinding` + `ofFormation`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- The λ cell: `gen_lam` with the single body child (under one fresh value binder, shift `1`). -/
def lamCell {scope : Nat} (body : RawTerm (scope + 1)) : RawTerm scope :=
  .mkGen .gen_lam () (.childCons body .childNil)

/-- The application cell: `gen_app` with the function and argument children (both at the parent
scope, shifts `[0, 0]`). -/
def appCell {scope : Nat} (functionTerm argument : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil))

mutual

/-- The GROWN description engine: the formation fragment (`ofFormation`) extended with
Π-introduction (`piIntro`/λ), Π-elimination (`piElim`/app), the GENERIC cascade-free
type-former formation arm (`genFormationPi`, over `typingRuleDescOf` — the grown-engine mirror
of `HasTypeDesc.genFormation`, mutual with `DescTelescopePi`), plus its own `conv`.  Additive
over `HasTypeDesc` (which appears only positively, in `ofFormation`; `HasTypeDescPi` itself only
in premises) — disturbs neither `HasTypeDesc` nor the `toHasType` ⟺ cross-check.

`genFormationPi` SUBSUMES the binary `piFormation`/`sigmaFormation` (kept for now; see
`DescTelescope.toDescTelescopePi`) and is what makes the grown engine SUBSTITUTION-CLOSED
GENERICALLY: substituting a grown term into a type-former component yields a former with a grown
component, typed by `genFormationPi` with no per-former dispatch — whereas the binary arms would
force a partial-match on the child telescope (the indexed-inductive propext trap).  This is the
§5-endgame direction: formation typing GENERIC over the cell table, not bespoke per-former — a
new dependent former is ONE `typingRuleDescOf` row, ZERO new arms (P13 cascade-freedom), now at
the grown layer too. -/
inductive HasTypeDescPi (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope →
      RawTerm scope → RawTerm scope → Prop where
  | ofFormation {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (formationTyped : HasTypeDesc profile context subject classifier) :
      HasTypeDescPi profile context subject classifier
  | conv {scope : Nat} {context : TypingContext profile scope}
      {subject classifier reclassifier : RawTerm scope}
      (levelExpr : LevelExpr) (flag : UniverseFlag)
      (typed : HasTypeDescPi profile context subject classifier)
      (converts : Conv classifier reclassifier)
      (reclassifierTyped :
        HasTypeDescPi profile context reclassifier
          (universeCodeCell levelExpr flag)) :
      HasTypeDescPi profile context subject reclassifier
  | piIntro {scope : Nat} {context : TypingContext profile scope}
      {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
      (domainLevel : LevelExpr) (domainFlag : UniverseFlag)
      (domainTyped :
        HasTypeDescPi profile context domainCode
          (universeCodeCell domainLevel domainFlag))
      (bodyTyped :
        HasTypeDescPi profile (context.cons domainCode) body codomainCode) :
      HasTypeDescPi profile context (lamCell body)
        (piTyCodeCell domainCode codomainCode)
  | piElim {scope : Nat} {context : TypingContext profile scope}
      {functionTerm argument domainCode : RawTerm scope}
      {codomainCode : RawTerm (scope + 1)}
      (functionTyped :
        HasTypeDescPi profile context functionTerm
          (piTyCodeCell domainCode codomainCode))
      (argumentTyped : HasTypeDescPi profile context argument domainCode) :
      HasTypeDescPi profile context (appCell functionTerm argument)
        (RawTerm.subst0 codomainCode argument)
  | piFormation {scope : Nat} {context : TypingContext profile scope}
      {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
      (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
      (domainTyped :
        HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag))
      (codomainTyped :
        HasTypeDescPi profile (context.cons domainCode) codomainCode
          (universeCodeCell codomainLevel flag)) :
      HasTypeDescPi profile context (piTyCodeCell domainCode codomainCode)
        (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag)
  | sigmaFormation {scope : Nat} {context : TypingContext profile scope}
      {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
      (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
      (domainTyped :
        HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag))
      (codomainTyped :
        HasTypeDescPi profile (context.cons domainCode) codomainCode
          (universeCodeCell codomainLevel flag)) :
      HasTypeDescPi profile context (sigmaTyCodeCell domainCode codomainCode)
        (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag)
  | genFormationPi {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (payload : generator.payload scope)
      (children : RawTermChildren generator.binderShifts scope)
      (levels : List LevelExpr) (flag : UniverseFlag)
      (rule : TypingRuleDesc)
      (isFormation : typingRuleDescOf generator = some rule)
      (premises :
        DescTelescopePi profile (currentDepth := 0) context levels flag children) :
      HasTypeDescPi profile context (.mkGen generator payload children)
        (rule.outputType scope levels flag)

/-- The grown engine's premise spine: the children form a cumulative dependent telescope of
TYPES at `levels`, each typed by `HasTypeDescPi` (so children may be GROWN — applications,
λ-abstractions, nested formers — not only formation terms).  Mutual with `HasTypeDescPi`; its
index signature references only `PolyProfile`/`Nat`/`List Nat`/`LevelExpr`/`UniverseFlag`/
`TypingContext`/`RawTermChildren`, never `HasTypeDescPi` (mutual-index rule), and `HasTypeDescPi`
appears only POSITIVELY in `cons`'s `headTyped`.  The grown mirror of `DescTelescope`, with the
same fixed-`baseScope`/growing-`currentDepth` rebasing discipline. -/
inductive DescTelescopePi (profile : PolyProfile) :
    {baseScope : Nat} → {currentDepth : Nat} → {binderShifts : List Nat} →
      TypingContext profile (baseScope + currentDepth) →
      List LevelExpr → UniverseFlag →
      RawTermChildren binderShifts baseScope → Prop where
  | nil {baseScope : Nat} {currentDepth : Nat}
      (context : TypingContext profile (baseScope + currentDepth))
      (flag : UniverseFlag) :
      DescTelescopePi profile context [] flag .childNil
  | cons {baseScope : Nat} {currentDepth : Nat} {restShifts : List Nat}
      (context : TypingContext profile (baseScope + currentDepth))
      (head : RawTerm (baseScope + currentDepth))
      (headLevel : LevelExpr) (restLevels : List LevelExpr) (flag : UniverseFlag)
      (rest : RawTermChildren restShifts baseScope)
      (headTyped :
        HasTypeDescPi profile context head (universeCodeCell headLevel flag))
      (restTyped :
        DescTelescopePi profile (currentDepth := currentDepth + 1)
          (context.cons head) restLevels flag rest) :
      DescTelescopePi profile context (headLevel :: restLevels) flag
        (.childCons head rest)

end

/-- A grown-engine type: the classifier inhabits some universe code in `HasTypeDescPi`. -/
def IsTypeDescPi (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (classifier : RawTerm scope) : Prop :=
  ∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
    HasTypeDescPi profile context classifier (universeCodeCell levelExpr flag)

/-- The formation engine embeds faithfully into the grown engine (the `ofFormation` arm, named).
Every formation typing is a grown-engine typing — so all the shipped formation metatheory
(validity, inversion, uniqueness, weakening, substitution) transfers to the embedded fragment. -/
theorem HasTypeDesc.toHasTypeDescPi {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDesc profile context subject classifier) :
    HasTypeDescPi profile context subject classifier :=
  HasTypeDescPi.ofFormation derivation

/-- Formation subsumption at the spine level: every FORMATION premise telescope is a grown
premise telescope — lift each head through `ofFormation`, recurse on the tail.  Structural on the
formation telescope.  The witness that the grown engine's children-spine is at least as
inhabited as the formation engine's. -/
theorem DescTelescope.toDescTelescopePi {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescope profile context levels flag children) :
    DescTelescopePi profile context levels flag children :=
  match telescope with
  | .nil context flag => DescTelescopePi.nil context flag
  | .cons context head headLevel restLevels flag rest headTyped restTyped =>
      DescTelescopePi.cons context head headLevel restLevels flag rest
        (HasTypeDescPi.ofFormation headTyped)
        restTyped.toDescTelescopePi

/-- The generic grown `genFormationPi` arm SUBSUMES the formation `genFormation` arm: any
description-engine type-former formation is a grown-engine formation, via `toDescTelescopePi`.
The §11.8.5 cascade-free subsumption at the judgment level — the grown engine is at least as
strong as the formation engine on the WHOLE `typingRuleDescOf` family, through ONE generic arm
(not per-former).  (Note `ofFormation` already embeds the same conclusion whole; this exhibits
the SECOND, structural route — the one the substitution leg will rebuild grown components
through.) -/
theorem HasTypeDesc.genFormationToHasTypeDescPi {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {levels : List LevelExpr} {flag : UniverseFlag} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule)
    (premises : DescTelescope profile (currentDepth := 0) context levels flag children) :
    HasTypeDescPi profile context (.mkGen generator payload children)
      (rule.outputType scope levels flag) :=
  HasTypeDescPi.genFormationPi context generator payload children levels flag rule
    isFormation premises.toDescTelescopePi

/-- FIRST NON-VACUOUS SUBJECT REDUCTION IN THE KERNEL: the β-rule preserves typing.

For a β-redex built from FORMATION components — `body : codomainCode` under `context.cons
domainCode`, `argument : domainCode`, and `domainCode` a type — BOTH the redex
`appCell (lamCell body) argument` and its β-reduct `subst0 body argument` (the contractum of
`Step.beta`) are typed at `subst0 codomainCode argument` in the grown engine.

The redex types by `piElim ∘ piIntro` (over `ofFormation`-embedded components); the reduct
types by the shipped intrinsic `HasTypeDesc.substituteUnderBinding` (the β-engine — substituting
`argument` for de Bruijn 0 throughout `body` preserves typing, with the classifier
`codomainCode` instantiated to `subst0 codomainCode argument`), then `ofFormation`.  Both land
at the SAME type, which IS subject reduction for the β-redex.

Honest scope: PRESERVATION for component-derived redexes; the fully-general inverted SR
(arbitrary `HasTypeDescPi` derivation modulo `conv`, arbitrary grown-engine body) follows once
Π-arm inversion + the grown-engine substitution land.  But it is genuinely non-vacuous — unlike
formation-fragment SR, the redex here actually reduces and the reduct retypes. -/
theorem HasTypeDescPi.betaCoherence_formationBody {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {argument : RawTerm scope}
    (bodyTyped : HasTypeDesc profile (context.cons domainCode) body codomainCode)
    (argumentTyped : HasTypeDesc profile context argument domainCode)
    (domainIsType : IsTypeDesc profile context domainCode) :
    HasTypeDescPi profile context (appCell (lamCell body) argument)
        (RawTerm.subst0 codomainCode argument)
      ∧ HasTypeDescPi profile context (RawTerm.subst0 body argument)
        (RawTerm.subst0 codomainCode argument) := by
  obtain ⟨domainLevel, domainFlag, domainFormationTyped⟩ := domainIsType
  refine ⟨?_, ?_⟩
  · exact HasTypeDescPi.piElim
      (HasTypeDescPi.piIntro domainLevel domainFlag
        (HasTypeDescPi.ofFormation domainFormationTyped)
        (HasTypeDescPi.ofFormation bodyTyped))
      (HasTypeDescPi.ofFormation argumentTyped)
  · exact HasTypeDescPi.ofFormation
      (HasTypeDesc.substituteUnderBinding argument bodyTyped argumentTyped)

end FX1Poly.Typed
