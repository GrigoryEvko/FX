import FX1Poly.Typed.ValidTypingRefinedMotive

/-! # FX1Poly/Typed/ValidTypingFormerArms
    — the generic-former (`genFormationPi`) arm of the total-bridge motive (SN-027/#662 assembly)

The total-bridge motive `TotalBridgeConclusion` (`ValidTypingRefinedMotive.lean`) has its leaf and binder/elim
arms shipped — `var`, `universeFormation`, `convNonVariableReclassifier`, `ofTermValidity`
(`ValidTypingRefinedMotive.lean`), `convVariableReclassifier` (`ValidTypingConvArm.lean`), `piIntro` / `piElim`
(`ValidTypingPiArms.lean`).  This file ships the remaining per-constructor arm: the GENERIC FORMER.

`genFormationPi` is neither a fixed former (its classifier is the GENERIC `rule.outputType scope levels flag`,
NOT syntactically a universe code, so it cannot route through `universeFormation`'s one-liner) nor a term arm (its
classifier MAY be convertible to a universe code — the subject IS a type code).  So it needs its own arm.

The key structural fact (read off the `ValidTyping.genFormationPi` constructor): its three premises
(`isFormation`, `premises`, `telescopeFundamental`) are ALL `predLevel`-independent — `predLevel` is a free
parameter of the constructor, exactly as in the fixed formers.  So the generic former is level-flexible by
refiring at any `predLevel`:

* **conjunct-1** (single-level validity) fires `ValidTyping.genFormationPi` at the carried `predLevel`;
* **conjunct-2** (level-flexibility — only when the generic classifier is convertible to a universe code) refires
  the former at EVERY `level` (classifier `rule.outputType …` at `level + 1`) and RECLASSIFIES it to the universe
  code via `ValidTyping.conv` through the convertibility witness — `ValidTyping.universeFormation` supplies the
  reclassifier at `(level + 1) + 1`.  (The earlier syntactic-guard motive used a bare `eq ▸` here; the
  convertibility guard needs the `conv` reclassification.)

## Zero-axiom verification

conjunct-1 is `ValidTyping.genFormationPi`; conjunct-2 is `ValidTyping.conv` composing a refired
`ValidTyping.genFormationPi` with `ValidTyping.universeFormation` through the convertibility witness.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- **The generic-former (`genFormationPi`) arm of the total-bridge motive.**  A generic type former
`.mkGen generator payload children`, classified by the rule's generic `outputType`, satisfies the motive:

* **conjunct-1** (single-level validity) is `ValidTyping.genFormationPi` at the carried `predLevel`;
* **conjunct-2** (level-flexibility) applies when the generic classifier `rule.outputType scope levels flag` is
  CONVERTIBLE to a universe code `universeCodeCell outLevel outFlag` — then it refires the former at every `level`
  (the constructor's premises are `predLevel`-independent) and reclassifies through `converts` via
  `ValidTyping.conv`, with `ValidTyping.universeFormation` providing the universe-code reclassifier at
  `(level + 1) + 1`.

The generic-former analogue of `piFormation_isLevelFlexible`, stated directly over the total-bridge motive
because the output classifier is not syntactically a universe code. -/
theorem TotalBridgeConclusion.genFormationPi {profile : PolyProfile} {scope : Nat}
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
    TotalBridgeConclusion profile contextLevels context
      (.mkGen generator payload children) (rule.outputType scope levels flag) :=
  ⟨⟨predLevel + 1,
    ValidTyping.genFormationPi contextLevels predLevel generator payload isFormation premises
      telescopeFundamental⟩,
   fun outLevel outFlag converts _subjectNotVariable level =>
     ValidTyping.conv contextLevels (level + 1)
       (ValidTyping.genFormationPi contextLevels level generator payload isFormation premises
         telescopeFundamental)
       converts
       (ValidTyping.universeFormation contextLevels (level + 1) context outLevel outFlag)⟩

end FX1Poly.Typed
