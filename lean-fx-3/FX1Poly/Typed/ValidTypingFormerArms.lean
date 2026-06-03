import FX1Poly.Typed.ValidTypingRefinedMotive
import FX1Poly.Typed.UniverseCodeShape

/-! # FX1Poly/Typed/ValidTypingFormerArms
    — the generic-former arm of the refined-motive total bridge (SN-027, #658)

The total bridge `HasTypeDescPi → ∃ contextLevels predLevel, ValidTyping …` (SN-027) inducts on
`HasTypeDescPi` against the motive `RefinedTotalBridgeConclusion` (`ValidTypingRefinedMotive.lean`).  Its arms
split three ways:

* the **fixed formers** (`universeFormation` / `piFormation` / `sigmaFormation`) discharge through
  `ofLevelFlexible` applied to the matching `*_isLevelFlexible` witness — their output classifier is SYNTACTICALLY
  a universe code, so the assembly inlines them as one-liners (no dedicated arm theorem needed);
* the **term subjects** (`piIntro` / `piElim` / `var`) discharge through `ofTermValidity`
  (`ValidTypingTermArms.lean`) — their classifier is never a universe code, so the level-flexibility conjunct is
  vacuous;
* the **generic former** `genFormationPi` is neither.  Its subject `.mkGen generator payload children` IS a type
  code, but its classifier is the GENERIC `rule.outputType scope levels flag`, NOT syntactically a universe code.
  So it cannot route through `ofLevelFlexible` (which needs a syntactic universe-code classifier), and it is not a
  term arm (its classifier may well be a universe code).  It needs its own arm theorem — this file.

The key structural fact (read off the `ValidTyping.genFormationPi` constructor): its three premises
(`isFormation`, `premises`, `telescopeFundamental`) are ALL `predLevel`-independent — `predLevel` is a free
parameter of the constructor, exactly as in the fixed formers.  So the generic former is level-flexible by the
same mechanism: refire it at any `predLevel`.

## What is proved

* `RefinedTotalBridgeConclusion.genFormationPi` — the generic-former arm.  Conjunct 1 (single-level validity)
  fires `ValidTyping.genFormationPi` at the carried `predLevel`.  Conjunct 2 (level-flexibility, only when the
  generic output classifier `rule.outputType scope levels flag` happens to match a universe code) refires it at
  EVERY `level` and casts the classifier through the match equality `eq`.  Because the premises are
  `predLevel`-independent, the same `isFormation`/`premises`/`telescopeFundamental` serve every level.

## Zero-axiom verification

Conjunct 1 is an anonymous constructor over `ValidTyping.genFormationPi`; conjunct 2 is a `▸` rewrite of the
classifier through the universe-code-match equality.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- **The generic-former (`genFormationPi`) arm of the refined motive.**  A generic type former
`.mkGen generator payload children`, classified by the rule's generic `outputType`, satisfies the refined motive:

* **conjunct 1** (single-level validity) is `ValidTyping.genFormationPi` at the carried `predLevel`;
* **conjunct 2** (level-flexibility) applies only when the generic classifier `rule.outputType scope levels flag`
  matches a universe code — and then it refires the former at every `level` (the constructor's premises are
  `predLevel`-independent) and casts the classifier through the match equality.

This is the generic-former analogue of `piFormation_isLevelFlexible`, but stated directly over the refined motive
because the output classifier is not syntactically a universe code. -/
theorem RefinedTotalBridgeConclusion.genFormationPi {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (predLevel : Nat)
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
    RefinedTotalBridgeConclusion profile contextLevels context
      (.mkGen generator payload children) (rule.outputType scope levels flag) :=
  ⟨⟨predLevel + 1,
    ValidTyping.genFormationPi contextLevels predLevel generator payload isFormation premises
      telescopeFundamental⟩,
   fun _matchedLevelExpr _matchedFlag eq level =>
     eq ▸ ValidTyping.genFormationPi contextLevels level generator payload isFormation premises
       telescopeFundamental⟩

end FX1Poly.Typed
