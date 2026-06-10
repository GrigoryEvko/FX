import FX1Poly.Typed.GrownCanonicalForms
import FX1Poly.Typed.HasTypeDescDataIntroInversion
import FX1Poly.Typed.HasTypeDescNatIntro
import FX1Poly.Typed.HasTypeDescListIntro
import FX1Poly.Typed.HasTypeDescPairIntro
import FX1Poly.Typed.HasTypeDescEitherIntro
import FX1Poly.Typed.HasTypeDescOptionIntro
import FX1Poly.Typed.HasTypeDescIdIntro

/-! # FX1Poly/Typed/CombinedClosedNormalValueHeads — the COMBINED closed-normal head
    characterization with CONSTRUCTOR heads (CAN-4, the #1048 head-extension).

`HasTypeDescPi.closedNormalSubjectHead` characterizes closed normal GROWN-typed subjects
(7 former/λ heads).  The kernel's data VALUES live in the standalone intro engines — by the
cascade-free architecture they are deliberately NOT grown-typable, so the grown theorem
cannot see constructor heads.  The canonicity assembly (#1048) needs the COMBINED statement:
a closed normal term typed by ANY value engine has a head in the combined former-or-constructor
set.

  * `TypedByValueEngine` — the 8-arm union of the value engines (grown + the 7 intro engines:
    bool data-intro, nat, list, pair, either, option, identity).  Eliminator judgments are
    deliberately EXCLUDED: their subjects are redexes or applications, not values — the
    closed-normal analysis of eliminator-typed subjects is the CAN-5 per-classifier step.
  * `IsCombinedValueHead` — the 19-head inductive predicate (the 7 grown heads + the 12
    constructor heads).  An inductive predicate rather than a Boolean table or a 19-way `Or`:
    no wildcard match (propext hygiene), and each arm closes by one constructor.
  * `closedNormalSubjectHeadCombined` (★) — the CAN-4 headline.  The grown arm consumes the
    shipped 7-head theorem; each intro arm consumes its engine's shipped subject-shape
    inversion (the subject IS a constructor cell), and the head computes by `rfl` after
    substitution.  Normality and closedness are consumed ONLY by the grown arm — constructor
    SHAPE is unconditional in the intro engines (their reducts are handled by the intro SR,
    `DataIntroSubjectReductionRecursive`).

## Zero-axiom

The union and the head predicate are plain inductives; the theorem is an 8-arm `cases` with
per-arm `rcases` + `subst` + predicate constructors.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The union of the kernel's VALUE engines: grown plus the 7 standalone intro engines. -/
inductive TypedByValueEngine (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (subject classifier : RawTerm scope) : Prop where
  | ofGrown (typed : HasTypeDescPi profile context subject classifier)
  | ofBoolIntro (typed : HasTypeDescDataIntro profile context subject classifier)
  | ofNatIntro (typed : HasTypeDescNatIntro profile context subject classifier)
  | ofListIntro (typed : HasTypeDescListIntro profile context subject classifier)
  | ofPairIntro (typed : HasTypeDescPairIntro profile context subject classifier)
  | ofEitherIntro (typed : HasTypeDescEitherIntro profile context subject classifier)
  | ofOptionIntro (typed : HasTypeDescOptionIntro profile context subject classifier)
  | ofIdIntro (typed : HasTypeDescIdIntro profile context subject classifier)

/-- The combined closed-normal VALUE head set: the 7 grown former/λ heads plus the 12 data
constructor heads. -/
inductive IsCombinedValueHead : Generator → Prop where
  | lam : IsCombinedValueHead .gen_lam
  | piTyCode : IsCombinedValueHead .gen_piTyCode
  | sigmaTyCode : IsCombinedValueHead .gen_sigmaTyCode
  | universeCode : IsCombinedValueHead .gen_universeCode
  | listCode : IsCombinedValueHead .gen_listCode
  | optionCode : IsCombinedValueHead .gen_optionCode
  | unitCode : IsCombinedValueHead .gen_unitCode
  | boolTrue : IsCombinedValueHead .gen_boolTrue
  | boolFalse : IsCombinedValueHead .gen_boolFalse
  | natZero : IsCombinedValueHead .gen_natZero
  | natSucc : IsCombinedValueHead .gen_natSucc
  | listNil : IsCombinedValueHead .gen_listNil
  | listCons : IsCombinedValueHead .gen_listCons
  | pair : IsCombinedValueHead .gen_pair
  | eitherInl : IsCombinedValueHead .gen_eitherInl
  | eitherInr : IsCombinedValueHead .gen_eitherInr
  | optionNone : IsCombinedValueHead .gen_optionNone
  | optionSome : IsCombinedValueHead .gen_optionSome
  | refl : IsCombinedValueHead .gen_refl
  | unit : IsCombinedValueHead .gen_unit

/-- **★ CAN-4: the combined closed-normal head characterization.**  A closed normal term typed
by ANY value engine has a combined former-or-constructor head.  The grown arm consumes the
shipped 7-head theorem; the intro arms consume their engines' subject-shape inversions (the
constructor shape is unconditional there — normality/closedness are only needed on the grown
side). -/
theorem closedNormalSubjectHeadCombined {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : TypedByValueEngine profile context subject classifier)
    (normal : RawTerm.isStepNormalForm subject)
    (closed : Fin scope → False) :
    IsCombinedValueHead (RawTerm.headGenerator subject) := by
  cases typed with
  | ofGrown grownTyped =>
      rcases HasTypeDescPi.closedNormalSubjectHead grownTyped normal closed with
        headEq | headEq | headEq | headEq | headEq | headEq | headEq
      · exact headEq ▸ IsCombinedValueHead.lam
      · exact headEq ▸ IsCombinedValueHead.piTyCode
      · exact headEq ▸ IsCombinedValueHead.sigmaTyCode
      · exact headEq ▸ IsCombinedValueHead.universeCode
      · exact headEq ▸ IsCombinedValueHead.listCode
      · exact headEq ▸ IsCombinedValueHead.optionCode
      · exact headEq ▸ IsCombinedValueHead.unitCode
  | ofBoolIntro boolTyped =>
      rcases HasTypeDescDataIntro.subjectIsNullaryValueCell boolTyped with
        subjectEq | subjectEq | subjectEq
      · exact subjectEq ▸ IsCombinedValueHead.boolTrue
      · exact subjectEq ▸ IsCombinedValueHead.boolFalse
      · exact subjectEq ▸ IsCombinedValueHead.unit
  | ofNatIntro natTyped =>
      rcases HasTypeDescNatIntro.subjectIsNatConstructor natTyped with
        subjectEq | ⟨predecessor, subjectEq⟩
      · exact subjectEq ▸ IsCombinedValueHead.natZero
      · exact subjectEq ▸ IsCombinedValueHead.natSucc
  | ofListIntro listTyped =>
      rcases HasTypeDescListIntro.subjectIsListConstructor listTyped with
        subjectEq | ⟨headValue, tailList, subjectEq⟩
      · exact subjectEq ▸ IsCombinedValueHead.listNil
      · exact subjectEq ▸ IsCombinedValueHead.listCons
  | ofPairIntro pairTyped =>
      obtain ⟨firstValue, secondValue, subjectEq⟩ := HasTypeDescPairIntro.subjectIsPair pairTyped
      exact subjectEq ▸ IsCombinedValueHead.pair
  | ofEitherIntro eitherTyped =>
      rcases HasTypeDescEitherIntro.subjectIsEitherInjection eitherTyped with
        ⟨value, subjectEq⟩ | ⟨value, subjectEq⟩
      · exact subjectEq ▸ IsCombinedValueHead.eitherInl
      · exact subjectEq ▸ IsCombinedValueHead.eitherInr
  | ofOptionIntro optionTyped =>
      rcases HasTypeDescOptionIntro.subjectIsOptionConstructor optionTyped with
        subjectEq | ⟨value, subjectEq⟩
      · exact subjectEq ▸ IsCombinedValueHead.optionNone
      · exact subjectEq ▸ IsCombinedValueHead.optionSome
  | ofIdIntro idTyped =>
      obtain ⟨witness, subjectEq⟩ := HasTypeDescIdIntro.subjectIsRefl idTyped
      exact subjectEq ▸ IsCombinedValueHead.refl

end FX1Poly.Typed
