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

/-- The GROWN description engine: the formation fragment (`ofFormation`) extended with
Π-introduction (`piIntro`/λ) and Π-elimination (`piElim`/app), plus its own `conv`.  Additive
over `HasTypeDesc` — `HasTypeDesc` appears only positively in `ofFormation`, `HasTypeDescPi`
only in premises, so this disturbs neither `HasTypeDesc` nor the `toHasType` ⟺ cross-check. -/
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
