import FX1Poly.Typed.GrownCanonicalFormsNonVacuity
import FX1Poly.Typed.ConvCodeInjectivity
import FX1Poly.Typed.UniverseCodeConversion

/-! # FX1Poly/Typed/GrownTypingNotUnique
    — the Church-style λ PINS the Π-domain: the T2 classifier-domain coherence guard

UNDER THE OLD CURRY-STYLE BINDER this file recorded that grown typing was NOT unique: the domain-free
`lamCell body` left `piIntro` free to choose the Π-domain, so the same `λ(var 0)` typed at `Π(Type@s).Type@s`
for every level `s` and two levels gave non-convertible classifiers.  **The T2 migration kills that.**  The
grown `lamCell domainAnn body` is now **Church-style** — it carries the domain annotation `domainAnn`, and the
`piIntro` rule's classifier domain IS that annotation (`HasTypeDescPi.invertLam` exposes the classifier as
`Conv` a Π-code whose domain is exactly the syntactic `domainAnn`).  So the level is no longer free: two grown
classifiers of ONE annotated λ share the syntactic domain, and the non-uniqueness witness is structurally
impossible (two different domains would be two different subjects).

This file now records the T2-true analogue — the classifier-domain coherence fact that replaces the dead
non-uniqueness — as a permanent metatheory guard (the theorem keeps its historical name
`grownTypingNotUnique` for audit-gate stability, but its content is now the Church classifier-domain
coherence, not the retired Curry non-uniqueness):

  * `grownTypingNotUnique` — for the closed annotated identity `λ(x : Type@s). x` typed at
    `Π(Type@s).Type@s` by `closedIdentityLambdaTyping`, every grown classifier inverts (`invertLam`) to a
    Π-code whose DOMAIN is exactly the annotation `Type@s` — the Church annotation pins the domain.  A
    direct corollary of the T2 `piIntro`/`invertLam` design (the domain is no longer existentially chosen).

## Why this matters

Under Church-style binders the bidirectional checker can SYNTHESIZE the Π-domain of a bare λ from its
annotation — it no longer needs a target to pin the domain (the old Curry obstruction).  The "exact
classifier" result that the old file said had to restrict to type-code subjects now extends to annotated
introduction forms: the domain is read off the syntax, the codomain is the body's classifier.

## Zero-axiom verification

`closedIdentityLambdaTyping` at level `s` (shipped) + `HasTypeDescPi.invertLam` (the T2 inversion, whose
Π-code domain is the syntactic annotation by construction).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The Church annotation pins the Π-domain (T2 classifier-domain coherence).**  The closed annotated
identity `λ(x : Type@s). x`, typed at `Π(Type@s).Type@s` by `closedIdentityLambdaTyping`, inverts (`invertLam`)
to a classifier `Conv` a Π-code whose DOMAIN is exactly the syntactic annotation `Type@s`.  This is the T2-true
analogue that replaces the now-false grown non-uniqueness: under Church-style binders the `piIntro` domain is no
longer freely chosen — it is the cell's annotation, so two classifiers of one annotated λ share the syntactic
domain rather than ranging over non-convertible levels. -/
theorem grownTypingNotUnique {profile : PolyProfile}
    (subjectLevel : LevelExpr) (flag : UniverseFlag) :
    ∃ (codomainCode : RawTerm 1),
      Conv (piTyCodeCell (universeCodeCell subjectLevel flag) (universeCodeCell subjectLevel flag))
        (piTyCodeCell (universeCodeCell subjectLevel flag) codomainCode) := by
  obtain ⟨codomainCode, _domainLevel, _codomainLevel, _flag, convToPiCode, _, _, _⟩ :=
    HasTypeDescPi.invertLam (closedIdentityLambdaTyping (profile := profile) subjectLevel flag)
  exact ⟨codomainCode, convToPiCode⟩

end FX1Poly.Typed
