import FX1Poly.Typed.DenoteKeyedClosedMember
import FX1Poly.Typed.DenoteKeyedSigmaFromChildMembers

/-! # FX1Poly/Typed/DenoteKeyedClosedTypeCodeSN
    — closed strong normalization for a UNIVERSE-classified closed subject (SN-D6 type-code fragment, SN-D7-adjacent)

The route-E "wire-to-SN" (SN-D6) composes the denote fundamental-theorem conclusion at the empty context with
denote CR1.  For a GENERAL classifier the denote CR1 (`ReducibleTypeStepDenote.isReducibilityCandidate`) carries
the `denoteBelowFamily` neutral-inclusion leg, which is only dischargeable below the ambient level
(`denoteBelowFamily_neutralInclusion_of_lt`, bounded by `lvl < level`) — the same threshold the cumulativity
obstruction (`DenoteKeyedCumulativityObstruction.lean`) pins.  But for a UNIVERSE classifier `Type@levelExpr`
that leg is supplied concretely by the decoded-level bound `denote levelExpr env < level`, and the denote
universe-member CR1 `stronglyNormalizing_of_universeMemberAtDenote` is already packaged with exactly that bound.

So the type-code fragment of SN-D6 closes cleanly NOW, conditional only on the (still-blocked) FT conclusion: a
CLOSED subject classified by `Type@levelExpr` whose decoded level is below the ambient, satisfying the denote
fundamental conclusion at the empty context, is strongly normalizing.  This is the SN-D7-adjacent early win for
the universe-classified (type-code) case — the subjects that ARE types (the genFormationPi/universeFormation
outputs), where CR1 is bound-packaged — de-risking the full SN-D5 assembly without waiting on the non-uniform
genFormationPi residual (#752/#753).

## The composition

`closedMemberAtDenote` (FT conclusion at empty context → closed membership of `Type@levelExpr`) then
`stronglyNormalizing_of_universeMemberAtDenote` (denote universe-member CR1, carrying `denote levelExpr env <
level`).  Both shipped; this is their direct one-line composition.

## Zero-axiom verification

A two-lemma composition (`closedMemberAtDenote` ∘ `stronglyNormalizing_of_universeMemberAtDenote`).  No
induction, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **Closed strong normalization for a universe-classified closed subject from the denote fundamental
conclusion.**  A closed `subject` classified by `Type@levelExpr` (decoded level strictly below the ambient
`level`) that satisfies `FundamentalConclusionAtDenote` at the empty context is strongly normalizing —
`closedMemberAtDenote` turns the conclusion into closed membership of `Type@levelExpr`, and the denote
universe-member CR1 `stronglyNormalizing_of_universeMemberAtDenote` (bound-packaged by `levelAbove`) extracts
strong normalization.  The SN-D6 type-code fragment, conditional on the FT conclusion: the subjects that ARE
types (where denote CR1 is threshold-free), closed WITHOUT the non-uniform genFormationPi residual. -/
theorem closedTypeCodeStronglyNormalizingFromFundamentalAtDenote {profile : PolyProfile}
    (env : Nat → Nat) (level : Nat) {subject : RawTerm 0}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (conclusion : FundamentalConclusionAtDenote env level
      (TypingContext.empty : TypingContext profile 0) subject (universeCodeCell levelExpr flag)) :
    IsStronglyNormalizing subject :=
  stronglyNormalizing_of_universeMemberAtDenote env level levelExpr flag subject levelAbove
    (closedMemberAtDenote env level conclusion)

end FX1Poly.Typed
