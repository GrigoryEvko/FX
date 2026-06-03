import FX1Poly.Typed.ValidTypingRefinedMotive
import FX1Poly.Typed.ConvCodeInjectivity

/-! # FX1Poly/Typed/ValidTypingPiArms
    — the piIntro / piElim term arms of the total-bridge motive (SN-027/#662 assembly)

The total-bridge motive `TotalBridgeConclusion` (`ValidTypingRefinedMotive.lean`) already has its leaf arms
shipped — `var`, `universeFormation`, `convNonVariableReclassifier` (that file),
`convVariableReclassifier` (`ValidTypingConvArm.lean`), and the term wrapper `ofTermValidity`.  This file ships
the two BINDER/ELIMINATION term arms.

Both subjects are TERMS, so both arms discharge through `TotalBridgeConclusion.ofTermValidity` (conjunct-1 the
supplied `ValidTyping`, conjunct-2 vacuous because the classifier is not convertible to a universe code):

* **piIntro** — subject `lamCell body`, classifier `piTyCodeCell domainCode codomainCode`.  The classifier is a
  Π code, UNCONDITIONALLY not convertible to a universe code (`Conv.piTyCode_not_universeCode`,
  `ConvCodeInjectivity.lean`, via Π-head-shape-stability under `StepStar` + universe-NF rigidity).  So conjunct-2
  is provably vacuous and the arm carries a PROOF, not a hypothesis.

* **piElim** — subject `appCell functionTerm argument`, classifier `subst0 codomainCode argument`.  The classifier
  is arbitrary: it IS convertible to a universe code precisely when the function is a type family
  (`functionTerm : Π(x:A). Type@e`, `codomainCode` a closed universe code unaffected by `subst0`), where
  `appCell functionTerm argument` is a NEUTRAL type pinned to one `subjectLevel` by `ValidTyping` — so the
  motive's conjunct-2 cannot hold at the `ValidTyping` layer.  That type-family case routes separately in the
  assembly (a pinned-reclassifier coordination, like the conv-variable case); this arm covers the value-result
  case via the `resultNotConvUniverse` hypothesis the assembly discharges by head-generator discrimination.

The shared `subjectLevel` on `functionTyped` / `argumentTyped` is the level-ALIGNMENT the application needs:
`ValidTyping.piElim` is a same-level rule, so the assembly must present the function and argument at one common
level (a bare `∃ subjectLevel` per sub-derivation cannot force this — verified: independent existential levels do
not align).  The arm takes the aligned pair; the assembly's level synthesis supplies it.

## Zero-axiom verification

`ofTermValidity` composed with `ValidTyping.piIntro` / `.piElim` and `Conv.piTyCode_not_universeCode`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- **The piIntro (λ-introduction) arm of the motive.**  A lambda `lamCell body` at the Π type
`piTyCodeCell domainCode codomainCode` (domain/codomain codes at `predLevel + 1 + 1`, body at `predLevel + 1`
under the `levelCons (predLevel + 1)`-extended level vector — `ValidTyping.piIntro`'s discipline) satisfies the
motive.  Conjunct-1 is `ValidTyping.piIntro`; conjunct-2 is provably vacuous — the classifier is a Π code, never
convertible to a universe code (`Conv.piTyCode_not_universeCode`). -/
theorem TotalBridgeConclusion.piIntro {profile : PolyProfile} {scope : Nat}
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
    TotalBridgeConclusion profile contextLevels context
      (lamCell body) (piTyCodeCell domainCode codomainCode) :=
  TotalBridgeConclusion.ofTermValidity
    (ValidTyping.piIntro contextLevels predLevel domainTyped codomainTyped bodyTyped)
    (fun _levelExpr _flag convertibility => Conv.piTyCode_not_universeCode convertibility)

/-- **The piElim (application) arm of the motive.**  An application `appCell functionTerm argument`
(function and argument ALIGNED at a common `subjectLevel` — `ValidTyping.piElim` is a same-level rule) whose
result classifier `subst0 codomainCode argument` is NOT convertible to any universe code satisfies the motive.
Conjunct-1 is `ValidTyping.piElim`; conjunct-2 is vacuous via the `resultNotConvUniverse` hypothesis.  The
type-family case (result convertible to a universe code) routes separately in the assembly — there the
application is a pinned neutral type, coordinated like the conv-variable reclassifier, not made level-flexible. -/
theorem TotalBridgeConclusion.piElim {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (subjectLevel : Nat)
    {context : TypingContext profile scope}
    {functionTerm argument domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (functionTyped : ValidTyping profile contextLevels subjectLevel context
      functionTerm (piTyCodeCell domainCode codomainCode))
    (argumentTyped : ValidTyping profile contextLevels subjectLevel context argument domainCode)
    (resultNotConvUniverse : ∀ (levelExpr : LevelExpr) (flag : UniverseFlag),
      ¬ Conv (RawTerm.subst0 codomainCode argument) (universeCodeCell levelExpr flag)) :
    TotalBridgeConclusion profile contextLevels context
      (appCell functionTerm argument) (RawTerm.subst0 codomainCode argument) :=
  TotalBridgeConclusion.ofTermValidity
    (ValidTyping.piElim contextLevels subjectLevel functionTyped argumentTyped)
    resultNotConvUniverse

end FX1Poly.Typed
