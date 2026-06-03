import FX1Poly.Typed.ValidTypingRefinedMotive
import FX1Poly.Typed.UniverseCodeShape

/-! # FX1Poly/Typed/ValidTypingTermArms
    — the term-subject arms of the refined-motive total bridge (SN-027, #660)

The total bridge `HasTypeDescPi → ∃ contextLevels predLevel, ValidTyping …` (SN-027) is an induction on
`HasTypeDescPi` whose motive is `RefinedTotalBridgeConclusion` (`ValidTypingRefinedMotive.lean`).  The arms split
two ways:

* **type-code arms** (`universeFormation` / `piFormation` / `sigmaFormation` / `genFormationPi`) — the subject is
  a TYPE CODE, classified by a universe code; they discharge the motive through `ofLevelFlexible`, supplying the
  all-level (level-flexible) form the `conv` / `piElim` arms need.
* **term-subject arms** (`piIntro` / `piElim` / `var` at a term-variable) — the subject is a TERM, classified by
  something that is NOT a universe code (a Π code, a Σ code, a context lookup).  For these the level-flexibility
  conjunct of the motive is VACUOUS: a non-universe classifier can never equal `universeCodeCell …`, so the
  obligation discharges by head-generator discrimination.

This file ships the term-subject machinery and the first term arm:

* `RefinedTotalBridgeConclusion.ofTermValidity` — the uniform term-arm wrapper: single-level `ValidTyping` plus a
  proof that the classifier is not a universe code yields the refined motive (vacuous second conjunct).
* `piTyCodeCell_ne_universeCodeCell` — the structural discriminator: a Π code is never a universe code.
* `RefinedTotalBridgeConclusion.piIntro` — the λ arm: mirrors `ValidTyping.piIntro`'s coordinated premises and
  wraps the result through `ofTermValidity` (classifier `piTyCodeCell …`, never a universe).

The genuinely hard LEVEL coordination — turning each sub-derivation's `∃`-level (or its level-flexible all-level
form) into the SHARED `predLevel` the premises here demand — is the ASSEMBLY's job (#662), not these arms'.  Each
arm states exactly the premises `ValidTyping`'s matching constructor requires, so the assembly's per-case work is
"coordinate the levels, then apply this arm".

## Zero-axiom verification

`ofTermValidity` is an anonymous constructor plus `absurd`; `piTyCodeCell_ne_universeCodeCell` rewrites both head
generators and discharges by `decide` on a `Generator` disequality; `piIntro` is `ofTermValidity` applied to
`ValidTyping.piIntro`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- **The uniform term-subject arm wrapper.**  A subject that is valid at SOME single level and whose classifier
is NOT a universe code satisfies the refined motive: the first conjunct is the supplied validity, and the
second (level-flexibility) conjunct is vacuous because its hypothesis `classifier = universeCodeCell …` is
impossible. -/
theorem RefinedTotalBridgeConclusion.ofTermValidity {profile : PolyProfile} {scope : Nat}
    {contextLevels : Fin scope → Nat} {subjectLevel : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : ValidTyping profile contextLevels subjectLevel context subject classifier)
    (notUniverse : ∀ (levelExpr : LevelExpr) (flag : UniverseFlag),
      classifier ≠ universeCodeCell levelExpr flag) :
    RefinedTotalBridgeConclusion profile contextLevels context subject classifier :=
  ⟨⟨subjectLevel, typed⟩, fun levelExpr flag eq => absurd eq (notUniverse levelExpr flag)⟩

/-- A Π type code cell is never a universe code cell: their head generators (`gen_piTyCode` vs
`gen_universeCode`) are distinct, so an equality would force `gen_piTyCode = gen_universeCode`, refuted by
`decide`. -/
theorem piTyCodeCell_ne_universeCodeCell {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    piTyCodeCell domainCode codomainCode ≠ universeCodeCell levelExpr flag := by
  intro eq
  have headEq := congrArg RawTerm.headGenerator eq
  rw [headGenerator_piTyCodeCell, headGenerator_universeCodeCell] at headEq
  exact absurd headEq (by decide)

/-- **The piIntro (λ) arm of the refined motive.**  A λ-term is a term subject classified by a Π code
(`piTyCodeCell domainCode codomainCode`), which is never a universe code, so the level-flexibility conjunct is
vacuous.  The single-level validity is `ValidTyping.piIntro` over the coordinated premises — exactly the levels
that constructor demands (domain/codomain codes one level above the body's `predLevel + 1`).  Producing those
coordinated premises from the inductive hypotheses is the assembly's task; this arm consumes them and discharges
the motive. -/
theorem RefinedTotalBridgeConclusion.piIntro {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (predLevel : Nat)
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainTyped : ValidTyping profile contextLevels (predLevel + 1 + 1) context
      domainCode (universeCodeCell domainLevel flag))
    (codomainTyped : ValidTyping profile (levelCons (predLevel + 1) contextLevels)
      (predLevel + 1 + 1) (context.cons domainCode) codomainCode (universeCodeCell codomainLevel flag))
    (bodyTyped : ValidTyping profile (levelCons (predLevel + 1) contextLevels)
      (predLevel + 1) (context.cons domainCode) body codomainCode) :
    RefinedTotalBridgeConclusion profile contextLevels context
      (lamCell body) (piTyCodeCell domainCode codomainCode) :=
  RefinedTotalBridgeConclusion.ofTermValidity
    (ValidTyping.piIntro contextLevels predLevel domainTyped codomainTyped bodyTyped)
    (fun levelExpr flag => piTyCodeCell_ne_universeCodeCell levelExpr flag)

end FX1Poly.Typed
