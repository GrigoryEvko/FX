import FX1Poly.Typed.Metatheory.Canonicity.Forms.FormationCanonicalForms
import FX1Poly.Typed.Metatheory.Canonicity.Forms.GrownCanonicalForms
import FX1Poly.Typed.Engine.WfContext.WfContextDesc
import FX1Poly.Typed.Engine.WfContext.WfContextDescPi

/-! # FX1Poly/Typed/Metatheory/Canonicity/Forms/IntervalIsNotHostType
    — #1805 host-engine coherence: the interval is NON-FIBRANT in the host engines too

The #1805 union-engine work pins the interval's non-fibrancy into `WfContextUnion` (an explicit
`¬ Conv bindingType intervalTypeCell` cons-conjunct).  The host engines `HasTypeDesc` (formation) and
`HasTypeDescPi` (grown) are LIVE, and they enforce the SAME non-fibrancy AT NO COST — structurally, BY
CONSTRUCTION, because the interval is not a host type at all: `typingRuleDescOf gen_intervalCode = none`
(NativityCensus), so the `genFormation` arm can never produce `intervalTypeCell`, and neither can `var`
(head `gen_var`), `universeFormation` (head `gen_universeCode`), nor the grown Π-formers
(`lam`/`app`/`pathLam`/…).  No `cons`-arm change is needed (it would be redundant AND a large cascade across
the ~30 host `WfContextDesc(Pi).cons` construction sites that bind arbitrary domains).  Instead this file
HARVESTS the host non-fibrancy from the existing head-classification lemmas:

  * `hasTypeDesc_intervalTypeCell_false` / `isTypeDesc_intervalTypeCell_false` — the interval has no FORMATION
    typing (via `HasTypeDesc.subjectIsVariableOrFormerHead`: the head is neither a variable nor a former).
  * `hasTypeDescPi_intervalTypeCell_false` / `isTypeDescPi_intervalTypeCell_false` — the interval has no GROWN
    typing in a CLOSED context (via `HasTypeDescPi.closedNormalSubjectHead`: the closed normal head is one of
    the seven grown formers, never `gen_intervalCode`).
  * `wfContextDesc_intervalConsNotWellFormed` / `wfContextDescPi_intervalConsNotWellFormed` — the headline host
    witnesses: an ordinary `cons` of the interval is host-ILL-FORMED, the host duals of the union's
    `intervalConsNotWellFormed`.

## Zero-axiom verification

`HasTypeDesc.subjectIsVariableOrFormerHead` + `HasTypeDescPi.closedNormalSubjectHead` + `Generator.noConfusion`
on the `gen_intervalCode`-vs-former head distinctness + the `WfContextDesc(Pi).headIs*` projections.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax

/-- **The interval has no FORMATION typing.**  A host-typed subject's head is a variable or one of the six
formation formers (`HasTypeDesc.subjectIsVariableOrFormerHead`); the interval's head `gen_intervalCode` is
neither, so `HasTypeDesc context intervalTypeCell _` is impossible. -/
theorem hasTypeDesc_intervalTypeCell_false {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (typed : HasTypeDesc profile context (intervalTypeCell : RawTerm scope) classifier) : False := by
  rcases HasTypeDesc.subjectIsVariableOrFormerHead typed with ⟨index, subjectEq⟩ | hHead
  · exact Generator.noConfusion (congrArg RawTerm.headGenerator subjectEq)
  · rcases hHead with h | h | h | h | h | h <;> exact Generator.noConfusion h

/-- **The interval is not a FORMATION type.**  Immediate from `hasTypeDesc_intervalTypeCell_false`. -/
theorem isTypeDesc_intervalTypeCell_false {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (isType : IsTypeDesc profile context intervalTypeCell) : False :=
  let ⟨_levelExpr, _flag, typed⟩ := isType
  hasTypeDesc_intervalTypeCell_false typed

/-- **The interval has no GROWN typing in a closed context.**  A closed normal grown-typed subject's head is one
of the seven grown formers (`HasTypeDescPi.closedNormalSubjectHead`); the interval (closed, normal) has head
`gen_intervalCode`, none of them, so `HasTypeDescPi context intervalTypeCell _` is impossible. -/
theorem hasTypeDescPi_intervalTypeCell_false {profile : PolyProfile}
    {context : TypingContext profile 0} {classifier : RawTerm 0}
    (typed : HasTypeDescPi profile context (intervalTypeCell : RawTerm 0) classifier) : False := by
  rcases HasTypeDescPi.closedNormalSubjectHead typed rfl (fun index => index.elim0) with
    h | h | h | h | h | h | h <;> exact Generator.noConfusion h

/-- **The interval is not a GROWN type (closed context).**  Immediate from
`hasTypeDescPi_intervalTypeCell_false`. -/
theorem isTypeDescPi_intervalTypeCell_false {profile : PolyProfile}
    {context : TypingContext profile 0}
    (isType : IsTypeDescPi profile context intervalTypeCell) : False :=
  let ⟨_levelExpr, _flag, typed⟩ := isType
  hasTypeDescPi_intervalTypeCell_false typed

/-- **★ The interval is NON-FIBRANT in the FORMATION engine (#1805 host witness).**  An ordinary `cons` of the
interval is host-ILL-FORMED: `WfContextDesc.headIsTypeDesc` would make the interval a formation type, refuted by
`isTypeDesc_intervalTypeCell_false`.  The host dual of the union's `intervalConsNotWellFormed`. -/
theorem wfContextDesc_intervalConsNotWellFormed {profile : PolyProfile} :
    ¬ WfContextDesc ((TypingContext.empty : TypingContext profile 0).cons intervalTypeCell) :=
  fun wellFormed => isTypeDesc_intervalTypeCell_false (WfContextDesc.headIsTypeDesc wellFormed)

/-- **★ The interval is NON-FIBRANT in the GROWN engine (#1805 host witness).**  An ordinary `cons` of the
interval is grown-ILL-FORMED: `WfContextDescPi.headIsType` would make the interval a grown type, refuted by
`isTypeDescPi_intervalTypeCell_false`.  The grown dual of the union's `intervalConsNotWellFormed`. -/
theorem wfContextDescPi_intervalConsNotWellFormed {profile : PolyProfile} :
    ¬ WfContextDescPi ((TypingContext.empty : TypingContext profile 0).cons intervalTypeCell) :=
  fun wellFormed => isTypeDescPi_intervalTypeCell_false (WfContextDescPi.headIsType wellFormed)

end FX1Poly.Typed
