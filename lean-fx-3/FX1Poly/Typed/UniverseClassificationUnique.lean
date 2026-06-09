import FX1Poly.Typed.HasTypeDescPiVariableInversion
import FX1Poly.Typed.IdentityTowerFamily

/-! # FX1Poly/Typed/UniverseClassificationUnique — universe-code Conv-rigidity + the negotiation leaf
     (route-H reflection, enrichment spike E2.5 GO)

The flag-negotiation keystone, validated at the leaf the plateau pin-extraction bottoms out at:

  * `universeCodeCell_isStepNormalFormAt` — universe codes are normal at EVERY scope.
  * `Conv.universeCode_injective` — convertible universe codes are EQUAL: both normal, the join
    collapses to syntactic identity, payloads agree.  So a Conv-class contains AT MOST ONE
    universe code — any two universe classifications drawn from one Conv-class coincide.
  * `HasTypeDescPi.variableUniverseClassificationUnique` — a variable's two grown universe
    classifications agree on (level, flag): both are Conv to the fixed lookup
    (`inversionVariable`), hence Conv to each other, hence equal by rigidity.  The caller's
    `invertLam` (level, flag) therefore SELECTS the flag-coherent condition pair's at variables.

## Zero-axiom verification

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- Universe codes are normal at EVERY scope (payload-only, childless). -/
theorem universeCodeCell_isStepNormalFormAt {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    RawTerm.isStepNormalForm (universeCodeCell (scope := scope) levelExpr flag) :=
  rfl

/-- **Universe-code `Conv`-rigidity**: convertible universe codes are EQUAL — both sides are
normal, so the join collapses to syntactic identity and the payloads agree. -/
theorem Conv.universeCode_injective {scope : Nat}
    {firstLevel secondLevel : LevelExpr} {firstFlag secondFlag : UniverseFlag}
    (codesConvertible : Conv (universeCodeCell (scope := scope) firstLevel firstFlag)
      (universeCodeCell secondLevel secondFlag)) :
    firstLevel = secondLevel ∧ firstFlag = secondFlag := by
  obtain ⟨commonReduct, firstChain, secondChain⟩ := codesConvertible
  have firstCollapses : commonReduct = universeCodeCell firstLevel firstFlag :=
    StepStar.eq_of_noStep
      (fun reduct step =>
        RawTerm.isStepNormalForm_blocks_step
          (universeCodeCell_isStepNormalFormAt firstLevel firstFlag) reduct step)
      firstChain
  have secondCollapses : commonReduct = universeCodeCell secondLevel secondFlag :=
    StepStar.eq_of_noStep
      (fun reduct step =>
        RawTerm.isStepNormalForm_blocks_step
          (universeCodeCell_isStepNormalFormAt secondLevel secondFlag) reduct step)
      secondChain
  have codesEqual : universeCodeCell (scope := scope) firstLevel firstFlag
      = universeCodeCell secondLevel secondFlag :=
    firstCollapses.symm.trans secondCollapses
  injection codesEqual with _hScope _hGenerator hPayload _hChildren
  exact ⟨congrArg Prod.fst hPayload, congrArg Prod.snd hPayload⟩

/-- **Universe classification is unique at VARIABLES** (the negotiation leaf): a variable's two
universe classifications agree on (level, flag) — both are `Conv` to the fixed lookup
(`inversionVariable`), hence `Conv` to each other, hence equal by rigidity. -/
theorem HasTypeDescPi.variableUniverseClassificationUnique {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope} {index : Fin scope}
    {firstLevel secondLevel : LevelExpr} {firstFlag secondFlag : UniverseFlag}
    (firstClassified : HasTypeDescPi profile context (variableCell index)
      (universeCodeCell firstLevel firstFlag))
    (secondClassified : HasTypeDescPi profile context (variableCell index)
      (universeCodeCell secondLevel secondFlag)) :
    firstLevel = secondLevel ∧ firstFlag = secondFlag :=
  Conv.universeCode_injective
    (Conv.trans (HasTypeDescPi.inversionVariable firstClassified)
      (HasTypeDescPi.inversionVariable secondClassified).sym)

end FX1Poly.Typed

