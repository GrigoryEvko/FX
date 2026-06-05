import FX1Poly.Typed.HasTypeDescSubjectReduction

/-! # FX1Poly/Typed/FormationNormalSmoke
    — a non-vacuous regression witness for the formation fragment's normality (`subjectAdmitsNoStep`)

`HasTypeDesc.subjectAdmitsNoStep` (the honest characterization shipped alongside the vacuous formation SR) says
EVERY formation-typed subject admits no `Step`.  This file pins that on a CONCRETE, closed, two-child former: a
Π-code `Π (Type@0). Type@0` whose domain and codomain are both the universe code `Type@0` (`standard` flag),
formation-typed via `hasTypeDesc_piFormation_viaGenArm` (the `genFormation` arm over a real `DescTelescope`
spine).  Applying `subjectAdmitsNoStep` to that derivation gives a concrete `∀ reduct, ¬ Step piCode reduct` —
exercising the `genFormation` + telescope arms of the no-step mutual on an actual former (not a leaf).

This is the formation-engine analogue of the SN smoke corpora (`ClosedSNSmoke` / `OpenSNSmoke` / the per-former
SN smoke): a permanent regression that would break if the no-step lemma or the formation typing of Π-codes ever
silently regressed.  Non-vacuous: the witness is a real, closed, formation-typed type former.

## Zero-axiom verification

`hasTypeDesc_piFormation_viaGenArm` + `HasTypeDesc.universeFormation` + `subjectAdmitsNoStep`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- A concrete closed Π-code `Π (Type@0). Type@0` is formation-typed at `Type@(lmax (lsucc 0) (lsucc 0))`:
both components are the universe code `Type@0` (typed at `Type@(lsucc 0)` by `universeFormation`), combined by
the generic `genFormation` arm. -/
theorem formationNormalSmoke_piCodeTyped {profile : PolyProfile} :
    HasTypeDesc profile (TypingContext.empty : TypingContext profile 0)
      (piTyCodeCell (universeCodeCell LevelExpr.lzero .standard)
        (universeCodeCell LevelExpr.lzero .standard))
      (universeCodeCell (LevelExpr.lmax LevelExpr.lzero.lsucc LevelExpr.lzero.lsucc) .standard) :=
  hasTypeDesc_piFormation_viaGenArm (TypingContext.empty : TypingContext profile 0)
    (universeCodeCell LevelExpr.lzero .standard) (universeCodeCell LevelExpr.lzero .standard)
    LevelExpr.lzero.lsucc LevelExpr.lzero.lsucc .standard
    (HasTypeDesc.universeFormation (TypingContext.empty : TypingContext profile 0)
      LevelExpr.lzero .standard)
    (HasTypeDesc.universeFormation
      ((TypingContext.empty : TypingContext profile 0).cons
        (universeCodeCell LevelExpr.lzero .standard))
      LevelExpr.lzero .standard)

/-- **Regression: the concrete closed Π-code admits no `Step`** — the formation fragment's normality
(`subjectAdmitsNoStep`) fired on a genuine two-child former.  Demonstrates the no-step lemma is non-vacuous:
its `genFormation` + telescope arms close a real, closed, formation-typed type former. -/
theorem formationNormalSmoke_piCodeAdmitsNoStep {profile : PolyProfile} (reduct : RawTerm 0) :
    ¬ Step
      (piTyCodeCell (universeCodeCell LevelExpr.lzero .standard)
        (universeCodeCell LevelExpr.lzero .standard) : RawTerm 0) reduct :=
  (formationNormalSmoke_piCodeTyped (profile := profile)).subjectAdmitsNoStep reduct

end FX1Poly.Typed
