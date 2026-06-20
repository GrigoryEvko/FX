import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Canonicity.RecursiveDataIntroDataTaitMembers

/-! # FX1PolyAudit/AuditRecursiveDataIntroDataTaitMembers
    — zero-axiom gate for the COMPLETE recursive data-introduction arm of the fundamental theorem (FTGEN-9
    deeper)

The two generic reduction-under-a-constructor decompositions (`stepStar_under_unaryCell` /
`stepStar_under_binaryCell`) plus the six recursive data-intro arms over `dataTaitCandidate`:

  * `natSuccDataTaitMember`     — recursive Nat (predecessor member)
  * `optionSomeDataTaitMember`  — structural Option (payload SN)
  * `eitherInlDataTaitMember` / `eitherInrDataTaitMember` — structural Either (payload SN)
  * `pairDataTaitMember`        — structural Σ (both components SN)
  * `listConsDataTaitMember`    — recursive List (head SN, tail member)

With the nullary / already-normal intro arm (`inductiveSaturatedIntro`) and the closed-eliminator family
these close the data-introduction side of the FT.  Must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.stepStar_under_unaryCell
#assert_no_axioms FX1Poly.Core.stepStar_under_binaryCell
#assert_no_axioms FX1Poly.Core.natSuccDataTaitMember
#assert_no_axioms FX1Poly.Core.optionSomeDataTaitMember
#assert_no_axioms FX1Poly.Core.eitherInlDataTaitMember
#assert_no_axioms FX1Poly.Core.eitherInrDataTaitMember
#assert_no_axioms FX1Poly.Core.pairDataTaitMember
#assert_no_axioms FX1Poly.Core.listConsDataTaitMember

end FX1PolyAudit
