import FX1Poly.Typed.DenoteKeyedClosedMember
import FX1Poly.Typed.DenoteKeyedSigmaFromChildMembers

/-! Scratch probe: the SN-D6 closed-SN wire for the universe-classified (type-code) closed subject.

A closed subject classified by `Type@levelExpr` (decoded level below the ambient) that satisfies the denote
fundamental-theorem conclusion at the empty context is strongly normalizing — compose `closedMemberAtDenote`
(FT conclusion → closed membership) with the shipped denote universe-member CR1
`stronglyNormalizing_of_universeMemberAtDenote`. This is the type-code fragment of SN-D6, conditional on the FT
conclusion (the blocked-FT input), de-risking SN-D5/SN-D7. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

theorem closedTypeCodeStronglyNormalizingFromFundamentalAtDenote {profile : PolyProfile}
    (env : Nat → Nat) (level : Nat) {subject : RawTerm 0}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (conclusion : FundamentalConclusionAtDenote env level
      (TypingContext.empty : TypingContext profile 0) subject (universeCodeCell levelExpr flag)) :
    IsStronglyNormalizing subject :=
  stronglyNormalizing_of_universeMemberAtDenote env level levelExpr flag subject levelAbove
    (closedMemberAtDenote env level conclusion)

#print axioms closedTypeCodeStronglyNormalizingFromFundamentalAtDenote

end FX1Poly.Typed
