import FX1Poly.Typed.HasTypeDescPiCheckOfInferred
import FX1Poly.Typed.HasTypeDescPiUniverseCodeInversion

/-! # FX1Poly/Typed/HasTypeDescPiCheckUniverseCode
    — the UNIVERSE-CODE case of the bidirectional grown-engine checker (SN-052), in CHECK mode

The SECOND COMPLETE case of the SN-052 decidable checker (alongside the variable case,
`HasTypeDescPiCheckVariable`), and the simpler of the two leaf positions.  Deciding
`universeCodeCell level flag : targetType` (given the target's typehood threaded as input — the CHECK-mode
discipline, SR-free since there is no λ) reduces to deciding `Conv (universeCodeCell level.lsucc flag)
targetType`:

  * INFERENCE: the universe code's principal type is the NEXT universe `Type@(level+1, flag)`, derived directly
    by `.ofFormation (HasTypeDesc.universeFormation …)`;
  * the principal type's OWN typehood is *also* direct — `Type@(level+1, flag)` is typed at `Type@(level+2,
    flag)` by a second `universeFormation`, so (unlike the variable case) NO `IsType.decideWithWitness` is
    needed; the universe hierarchy supplies the witness definitionally;
  * UNIQUENESS: `HasTypeDescPi.inversionUniverseCode` — every type a universe code receives is `Conv` to the
    next universe;
  * the COMPARE step `HasTypeDescPi.decidableCheckOfInferredUniqueAtType` assembles these into the decision.

With the variable and universe-code leaves complete, the SR-free leaf fragment of the checker is closed; the
remaining positions are the recursive elimination position (application) and the introduction position (λ),
the latter gated on exposing the target's Π-components (subject reduction).

## Zero-axiom verification

Two `universeFormation` constructors (inference + its principal type's typing) feeding the shipped COMPARE step
+ universe-code inversion.  No `match`, no `IsType` decision, no `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Decidable checking of a universe code against a known-type target.**  `universeCodeCell level flag :
targetType` is decided by `Conv (universeCodeCell level.lsucc flag) targetType` (the COMPARE step): the
universe code's inferred type is the next universe `Type@(level+1, flag)`, its principal-type typing is the
universe above that, and its per-subject uniqueness is `inversionUniverseCode`.  Strictly simpler than the
variable case — both the inference and its classifier-typing are direct `universeFormation` constructors, so
no `IsType.decideWithWitness` is required.  The target's typehood `targetTyped` is threaded as input (CHECK
mode). -/
def HasTypeDescPi.decidableCheckUniverseCodeAtType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (wellFormed : WfContext context)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    {targetType : RawTerm scope} {targetLevel : LevelExpr} {targetFlag : UniverseFlag}
    (targetTyped :
      HasTypeDescPi profile context targetType (universeCodeCell targetLevel targetFlag)) :
    Decidable (HasTypeDescPi profile context (universeCodeCell levelExpr flag) targetType) :=
  HasTypeDescPi.decidableCheckOfInferredUniqueAtType wellFormed
    (inferred := .ofFormation (HasTypeDesc.universeFormation context levelExpr flag))
    (inferredTypeTyped := .ofFormation (HasTypeDesc.universeFormation context levelExpr.lsucc flag))
    (targetTyped := targetTyped)
    (uniqueAtSubject := fun derivation =>
      (HasTypeDescPi.inversionUniverseCode derivation wellFormed).sym)

end FX1Poly.Typed
