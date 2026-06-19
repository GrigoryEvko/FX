import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Denote.Universe.DenoteKeyedFlatFormerFromCarriers

/-! # FX1PolyAudit/AuditDenoteKeyedFlatFormerFromCarriers
    — zero-axiom gate for the flat-former formation FT closed to its carriers' SN (FTGEN-5, leaf-closed)

Each two-carrier flat former (equivCode / productCode / sumCode / eitherCode / arrowCode) is a denote-reducible
MEMBER of its classifying universe given ONLY its carriers' strong normalization under every closing
substitution — the former-SN premise of `flatFormerFundamentalAtDenote` discharged structurally by the shipped
congruence-only `*_isStronglyNormalizing_of_*` cell-SN lemmas (a flat code has no root redex, so its only steps
are congruence through its carriers), the substituted-former SN matching by the concrete-generator `subst`
reduction.  `equivCodeFundamentalFromCarriers` (the univalence carrier) is the headline.  Must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.equivCodeFundamentalFromCarriers
#assert_no_axioms FX1Poly.Typed.productCodeFundamentalFromCarriers
#assert_no_axioms FX1Poly.Typed.sumCodeFundamentalFromCarriers
#assert_no_axioms FX1Poly.Typed.eitherCodeFundamentalFromCarriers
#assert_no_axioms FX1Poly.Typed.arrowCodeFundamentalFromCarriers

end FX1PolyAudit
