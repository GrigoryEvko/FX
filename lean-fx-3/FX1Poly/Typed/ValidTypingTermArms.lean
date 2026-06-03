import FX1Poly.Typed.ValidTypingRefinedMotive
import FX1Poly.Typed.UniverseCodeShape

/-! # FX1Poly/Typed/ValidTypingTermArms
    — the term-subject arms of the refined-motive total bridge (SN-027, #660/#661)

The total bridge `HasTypeDescPi → ∃ contextLevels predLevel, ValidTyping …` (SN-027) is an induction on
`HasTypeDescPi` whose motive is `RefinedTotalBridgeConclusion` (`ValidTypingRefinedMotive.lean`).  The arms split
two ways:

* **type-code arms** (`universeFormation` / `piFormation` / `sigmaFormation` / `genFormationPi`) — the subject is
  a TYPE CODE, classified by a universe code; they discharge the motive through `ofLevelFlexible`, supplying the
  all-level (level-flexible) form the `conv` arm needs.
* **term-subject arms** (`piIntro` / `piElim` / `var` at a term-variable) — the subject is a TERM, discharged
  through `ofTermValidity`: single-level validity plus a proof its classifier is NOT a universe code (making the
  level-flexibility conjunct vacuous).

The two term arms differ in HOW that non-universe proof is obtained, and that difference is load-bearing:

* `piIntro`'s classifier `piTyCodeCell …` is a Π code — UNCONDITIONALLY distinct from a universe code
  (`piTyCodeCell_ne_universeCodeCell`).  So its non-universe obligation is a PROOF, discharged in full.
* `piElim`'s classifier `subst0 codomainCode argument` IS a universe code precisely when the function is a type
  family (`f : Π(x:A). Type@e`).  In that case `appCell f a` is a NEUTRAL type pinned to one level by
  `ValidTyping` (the function — a `var`/neutral — has no derivation at any other level), so the motive's
  conjunct-2 (`∀ level`) is UNSATISFIABLE at the `ValidTyping` layer.  That type-family case is NOT handled here;
  it routes through the reducibility-layer neutral machinery in the assembly, which needs only ONE level (the
  `conv` consumer instantiates `∀ level` at exactly `subjectLevel`).  So `piElim` takes the non-universe fact as
  a HYPOTHESIS `resultNotUniverse`, discharged by the assembly for value-producing applications.

This file ships the term-subject machinery and the two term arms (`var` is #659, still pending):

* `RefinedTotalBridgeConclusion.ofTermValidity` — the uniform term-arm wrapper: single-level `ValidTyping` plus a
  proof that the classifier is not a universe code yields the refined motive (vacuous second conjunct).
* `piTyCodeCell_ne_universeCodeCell` — the structural discriminator: a Π code is never a universe code.
* `RefinedTotalBridgeConclusion.piIntro` — the λ arm (non-universe PROVED).
* `RefinedTotalBridgeConclusion.piElim` — the application arm (non-universe HYPOTHESIZED; type-family case env-routed).

The genuinely hard LEVEL coordination — turning each sub-derivation's `∃`-level into the SHARED level the premises
here demand — is the ASSEMBLY's job (#662), not these arms'.  Each arm states exactly the premises `ValidTyping`'s
matching constructor requires, so the assembly's per-case work is "coordinate the levels, then apply this arm".

## Zero-axiom verification

`ofTermValidity` is an anonymous constructor plus `absurd`; `piTyCodeCell_ne_universeCodeCell` rewrites both head
generators and discharges by `decide` on a `Generator` disequality; `piIntro` / `piElim` are `ofTermValidity`
applied to the matching `ValidTyping` constructor.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
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

/-- **The piElim (application) arm of the refined motive.**  An application `appCell functionTerm argument`
(function and argument at a common `subjectLevel`) whose RESULT classifier `subst0 codomainCode argument` is NOT
a universe code is a term subject — discharged through `ofTermValidity` exactly like `piIntro`.

The contrast with `piIntro` is the crux of why this arm carries a hypothesis where `piIntro` carried a proof.
`piIntro`'s classifier `piTyCodeCell …` is a Π code, UNCONDITIONALLY distinct from a universe code, so its
conjunct-2 is provably vacuous.  An application's classifier `subst0 codomainCode argument` IS a universe code
precisely when the function is a type family (`functionTerm : Π(x:A). Type@e`, whose `codomainCode` is a closed
universe code unaffected by `subst0`).  In that case `appCell functionTerm argument` is a NEUTRAL type pinned to
the single `subjectLevel` by `ValidTyping` (the function — a `var` or neutral — has no derivation at any other
level), so the refined motive's conjunct-2 (`∀ level, ValidTyping … (level+1) …`) is UNSATISFIABLE at the
`ValidTyping` layer.  That type-family case therefore does NOT flow through this arm; it routes through the
reducibility-layer neutral-member machinery in the assembly.  Conv-arm consumers only ever need the reclassifier
at ONE level (`validTypingBridgeConvFromAllLevelReclassifier` instantiates `∀ level` at exactly `subjectLevel`),
so the assembly supplies the neutral case by level-COORDINATION, not all-level flexibility.

Hence the honest signature: given coordinated function/argument premises and a proof that the result is not a
universe code, the application satisfies the refined motive (conjunct-2 vacuous).  The assembly discharges
`resultNotUniverse` for value-producing applications by head-generator discrimination, and handles the
type-family case separately. -/
theorem RefinedTotalBridgeConclusion.piElim {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (subjectLevel : Nat)
    {context : TypingContext profile scope}
    {functionTerm argument domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (functionTyped : ValidTyping profile contextLevels subjectLevel context
      functionTerm (piTyCodeCell domainCode codomainCode))
    (argumentTyped : ValidTyping profile contextLevels subjectLevel context argument domainCode)
    (resultNotUniverse : ∀ (levelExpr : LevelExpr) (flag : UniverseFlag),
      RawTerm.subst0 codomainCode argument ≠ universeCodeCell levelExpr flag) :
    RefinedTotalBridgeConclusion profile contextLevels context
      (appCell functionTerm argument) (RawTerm.subst0 codomainCode argument) :=
  RefinedTotalBridgeConclusion.ofTermValidity
    (ValidTyping.piElim contextLevels subjectLevel functionTyped argumentTyped)
    resultNotUniverse

end FX1Poly.Typed
