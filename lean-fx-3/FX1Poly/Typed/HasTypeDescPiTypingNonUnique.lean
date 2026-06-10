import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.HasTypeDescPiLamInversion
import FX1Poly.Typed.ConvCodeInjectivity
import FX1Poly.Typed.UniverseCodeConversion

/-! # FX1Poly/Typed/HasTypeDescPiTypingNonUnique
    — the grown engine's λ-DOMAIN is PINNED by the syntactic annotation (the T2 design fact;
    Curry-style non-uniqueness DIES under Church-style annotation)

The pre-T2 grown engine typed a BARE Curry-style abstraction `lamCell body` whose `lamCell` carried no
domain annotation, so the SAME closed identity λ inhabited `Π (Type@e) (Type@e)` for EVERY level `e` —
typing was NON-UNIQUE up to `Conv`.  The T2 Church-style migration makes the λ carry its domain
annotation IN THE SUBJECT (`lamCell domainAnn body`), and `HasTypeDescPi.piIntro`'s domain IS that
annotation.  The non-uniqueness witness is now FALSE BY DESIGN: the annotation pins the domain.

This file records the T2-TRUE analogue: a single annotated λ `lamCell domainAnn body`, typed at ANY two
classifiers, has BOTH classifiers convertible to a Π-code whose DOMAIN IS the syntactic annotation
`domainAnn` — so the two Π-domains AGREE (each `Conv` `domainAnn`, hence `Conv` each other).  The
syntactic domain is no longer free; it is determined by the subject.

## Why this matters: the checker can SYNTHESISE the domain

Pre-T2 the checker had to be BIDIRECTIONAL at a λ (CHECK mode against a given Π target) because there was
no unique domain to synthesise.  Under Church-style annotation the domain IS in the subject, so a λ
SYNTHESISES its domain directly from the annotation — `invertLam` extracts the Π-code against the
syntactic `domainAnn` with NO domain existential.  (The codomain still varies with the body's check, so
full type synthesis remains body-directed, but the domain leg is now syntactic.)

## Zero-axiom verification

The annotated identity λ types by a direct `piIntro` (domain/codomain by `universeFormation`, body by
`var`, all via `ofFormation`); the domain-agreement fact composes `invertLam` (which pins the Π-domain to
the annotation) with the unconditional raw `Conv.trans` / `Conv.sym`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The annotated identity λ types at `Π (Type@e) (Type@e)`, with the domain PINNED by the
annotation.**  Built directly from the grown `piIntro` arm: the domain ANNOTATION is the universe code
`Type@e` (typed at `Type@(e+1)` by the formation engine's `universeFormation`), the codomain matches, and
the body `var 0` is typed at the consed domain `Type@e` by the `var` arm.  Unlike the pre-T2 bare λ, the
level `e` is FIXED by the subject's annotation `domainAnn = universeCodeCell e flag` — it is no longer
free. -/
theorem hasTypeDescPi_identityLambda_atUniverse {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (lamCell (universeCodeCell levelExpr flag)
        (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
      (piTyCodeCell (universeCodeCell levelExpr flag) (universeCodeCell levelExpr flag)) :=
  HasTypeDescPi.piIntro levelExpr.lsucc levelExpr.lsucc flag
    (.ofFormation (HasTypeDesc.universeFormation _ levelExpr flag))
    (.ofFormation (HasTypeDesc.universeFormation _ levelExpr flag))
    (.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 0⟩ : Fin 1)))

/-- **The λ-domain is PINNED by the annotation: any two classifiers of one annotated λ agree on the
syntactic domain.**  An annotated λ `lamCell domainAnn body` typed at TWO classifiers has both classifiers
convertible to a Π-code whose DOMAIN IS the syntactic annotation `domainAnn` — so the two recovered
Π-domains are `Conv domainAnn` (each), hence `Conv` each other.  This is the T2-TRUE successor to the
defunct Curry-style non-uniqueness witness: the domain is no longer free, it is determined by the subject.
Consequence: the grown-engine checker SYNTHESISES the λ's domain from the annotation (no CHECK-mode
guessing of the domain). -/
theorem hasTypeDescPi_lambdaDomain_pinnedByAnnotation {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
    {firstType secondType : RawTerm scope}
    (firstTyped : HasTypeDescPi profile context (lamCell domainAnn body) firstType)
    (secondTyped : HasTypeDescPi profile context (lamCell domainAnn body) secondType) :
    ∃ (firstCodomain secondCodomain : RawTerm (scope + 1)),
      Conv firstType (piTyCodeCell domainAnn firstCodomain) ∧
        Conv secondType (piTyCodeCell domainAnn secondCodomain) := by
  obtain ⟨firstCodomain, _firstDomainLevel, _firstCodomainLevel, _firstFlag,
      firstConvToPi, _, _, _⟩ := firstTyped.invertLam
  obtain ⟨secondCodomain, _secondDomainLevel, _secondCodomainLevel, _secondFlag,
      secondConvToPi, _, _, _⟩ := secondTyped.invertLam
  exact ⟨firstCodomain, secondCodomain, firstConvToPi, secondConvToPi⟩

/-- **Corollary: the two Π-domains of one annotated λ are SYNTACTICALLY IDENTICAL (each `Conv domainAnn`,
hence `Conv` each other).**  From `hasTypeDescPi_lambdaDomain_pinnedByAnnotation`, both recovered Π-codes
have the SAME syntactic domain `domainAnn`, so their domains are trivially `Conv`-equal (`Conv.refl
domainAnn`) — the precise sense in which Church-style annotation RESTORES the domain agreement that the
bare Curry-style λ lacked.  (The CODOMAINS may still differ — only the body's check pins them — so the
FULL Π-codes are not in general `Conv`; the domain leg alone is now syntactic.) -/
theorem hasTypeDescPi_lambdaDomains_agree {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
    {firstType secondType : RawTerm scope}
    (firstTyped : HasTypeDescPi profile context (lamCell domainAnn body) firstType)
    (secondTyped : HasTypeDescPi profile context (lamCell domainAnn body) secondType) :
    ∃ (firstCodomain secondCodomain : RawTerm (scope + 1)),
      Conv firstType (piTyCodeCell domainAnn firstCodomain) ∧
        Conv secondType (piTyCodeCell domainAnn secondCodomain) ∧
        Conv domainAnn domainAnn := by
  obtain ⟨firstCodomain, secondCodomain, firstConvToPi, secondConvToPi⟩ :=
    hasTypeDescPi_lambdaDomain_pinnedByAnnotation firstTyped secondTyped
  exact ⟨firstCodomain, secondCodomain, firstConvToPi, secondConvToPi, Conv.refl domainAnn⟩

end FX1Poly.Typed
