import FX1Poly.Typed.TypedTypeValidityBoxedRelation
import FX1Poly.Typed.WfContextDescPi

/-! Probe: the WfContext-indexed typed-LR-validity predicate — each context entry's type is in the
    boxed typed LR (TypedTypeValidityBoxed) at its prefix context. Strengthens WfContextDescPi (which
    only says each entry IsTypeDescPi). The Abel-reflection well-formed-context the GrownCtxConv-5
    neutral arm needs. Now non-vacuous because the universe arm gives the LR closed inhabitants. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Each binding is LR-valid (in TypedTypeValidityBoxed at some candidate box) in its prefix context. -/
def WfContextTypedLrValid {profile : PolyProfile} :
    {scope : Nat} → TypingContext profile scope → Prop
  | _, .empty => True
  | _, .cons restContext bindingType =>
      WfContextTypedLrValid restContext ∧
        ∃ box : KripkeCandBox _, TypedTypeValidityBoxed profile restContext bindingType box

theorem WfContextTypedLrValid.emptyIsWellFormed {profile : PolyProfile} :
    WfContextTypedLrValid (profile := profile) .empty :=
  trivial

theorem WfContextTypedLrValid.tailValid {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (wellFormed : WfContextTypedLrValid (restContext.cons bindingType)) :
    WfContextTypedLrValid restContext :=
  wellFormed.1

theorem WfContextTypedLrValid.headLrValid {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (wellFormed : WfContextTypedLrValid (restContext.cons bindingType)) :
    ∃ box : KripkeCandBox scope, TypedTypeValidityBoxed profile restContext bindingType box :=
  wellFormed.2

theorem WfContextTypedLrValid.cons {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (restWellFormed : WfContextTypedLrValid restContext)
    (bindingLrValid :
      ∃ box : KripkeCandBox scope, TypedTypeValidityBoxed profile restContext bindingType box) :
    WfContextTypedLrValid (restContext.cons bindingType) :=
  ⟨restWellFormed, bindingLrValid⟩

/-- Soundness: LR-validity REFINES formation-validity. Each entry's LR-validity gives IsTypeDescPi via
toIsTypeDescPi, so a typed-LR-valid context is grown-well-formed (WfContextDescPi). -/
theorem WfContextTypedLrValid.toWfContextDescPi {profile : PolyProfile} :
    {scope : Nat} → {context : TypingContext profile scope} →
    WfContextTypedLrValid context → WfContextDescPi context
  | _, .empty, _ => trivial
  | _, .cons _restContext _bindingType, wellFormed =>
      ⟨WfContextTypedLrValid.toWfContextDescPi wellFormed.1,
       match wellFormed.2 with
       | ⟨_box, lrValid⟩ => lrValid.toIsTypeDescPi⟩

/-- Non-vacuity: a single universe-code binding is typed-LR-valid (using the closed universe inhabitant). -/
theorem wfContextTypedLrValid_universeBinding {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    WfContextTypedLrValid (profile := profile)
      ((TypingContext.empty : TypingContext profile 0).cons
        (universeCodeCell levelExpr flag)) :=
  ⟨trivial, ⟨KripkeCandBox.mk snKripkeCand,
    smoke_closedUniverseIsBoxedTypedValid levelExpr flag⟩⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.WfContextTypedLrValid.toWfContextDescPi
#print axioms FX1Poly.Typed.wfContextTypedLrValid_universeBinding
#print axioms FX1Poly.Typed.WfContextTypedLrValid.cons
#print axioms FX1Poly.Typed.WfContextTypedLrValid.headLrValid
