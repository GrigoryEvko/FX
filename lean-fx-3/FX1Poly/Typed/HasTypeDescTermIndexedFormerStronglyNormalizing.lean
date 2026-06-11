import FX1Poly.Typed.HasTypeDescTermIndexedFormerSubjectReduction
import FX1Poly.Typed.HasTypeDescSubjectStronglyNormalizingNative
import FX1Poly.Typed.OpenStronglyNormalizingUnconditional

/-! # FX1Poly/Typed/HasTypeDescTermIndexedFormerStronglyNormalizing — NATIVE-16: SN for the term-indexed former engine

`HasTypeDescTermIndexedFormer` (NATIVE-12) types `Id A a b` / `Bridge A a b` through ONE generic arm; NATIVE-13/14/15
gave its weakening/subst/inversion/uniqueness/context-conversion/SR.  This file lands the semantic-model piece —
strong normalization: every term-indexed-former-typed subject is strongly normalizing.

## The proof CONSUMES the grown reducibility (no new candidate)

The flat engine's SN (`HasTypeDescFlat.subjectStronglyNormalizing`) routes through the generic accessibility
substrate `formerCell_isStronglyNormalizing_of_accChildren` (a cell over a CONGRUENCE-ONLY generator is SN once
its child spine is accessible) keyed on the engine's no-root-redex inversion, plus
`accStepChildrenSuccessor_of_allStronglyNormalizing` (all-children-SN ⟹ accessibility).  The ONLY engine-specific
inputs are (1) the no-root-redex inversion — already shipped as `termIndexedFormerCellStepIsChildCongruence`
(NATIVE-15) — and (2) each child's SN.

The difference from flat: the flat telescope's children are FORMATION-typed (`HasTypeDesc`), whose SN is
unconditional (`HasTypeDesc.subjectStronglyNormalizingNative`).  The term-indexed children (carrier + endpoints)
are GROWN-typed (`HasTypeDescPi`), whose open SN is the shipped `HasTypeDescPi.stronglyNormalizingOfWfContextDesc`
(the SN-043 open generalization — itself the Tait/reducibility candidate machinery).  So the term-indexed former
SN does NOT introduce a bespoke `Id`/`Bridge` reducibility candidate; it is a former over grown-reducible children,
and CONSUMES the grown candidate — exactly the right architecture (the cell heads no redex, so its SN reduces to
its children's, which the grown logical relation already certifies).

`WfContextDesc Γ` is the genuinely-external hypothesis the grown open SN needs (since
`HasTypeDescPi Γ t T → WfContextDesc Γ` provably fails); the CLOSED corollary
(`…closedBridgeUniverseStronglyNormalizing`) discharges it with `WfContextDesc.emptyIsWellFormed`.

## Zero-axiom

The generic SN substrate is zero-axiom; `termIndexedFormerCellStronglyNormalizingOfChildren` is a direct
application keyed on the NATIVE-15 inversion; the telescope/endpoint children-SN helpers are structural
`match`-recursion calling the grown open SN on each child.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **A term-indexed former cell with all children strongly normalizing is strongly normalizing.**  The
term-indexed twin of `flatFormerCellStronglyNormalizingOfChildren`: an `Id`/`Bridge` former heads no root redex
(`termIndexedFormerCellStepIsChildCongruence`), so every `Step` out of the cell is a child congruence; the cell is
SN once its child spine is accessible, which all-children-SN supplies via the shipped
`accStepChildrenSuccessor_of_allStronglyNormalizing`.  Generic over the term-indexed former — a future table row
extends it with no change here. -/
theorem termIndexedFormerCellStronglyNormalizingOfChildren {scope : Nat} {generator : Generator}
    {rule : TermIndexedFormerDesc} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    (isTermIndexed : termIndexedFormerDescOf generator = some rule)
    (childrenSN : children.allStronglyNormalizing) :
    IsStronglyNormalizing (RawTerm.mkGen generator payload children) :=
  formerCell_isStronglyNormalizing_of_accChildren
    (fun cellStep => termIndexedFormerCellStepIsChildCongruence isTermIndexed cellStep)
    (accStepChildrenSuccessor_of_allStronglyNormalizing childrenSN)

/-- **Every endpoint of a term-indexed telescope is strongly normalizing.**  Structural `match`-recursion: each
endpoint is GROWN-typed at the carrier, so its SN is the shipped `HasTypeDescPi.stronglyNormalizingOfWfContextDesc`
(needing the external `WfContextDesc Γ`); the tail accumulates recursively. -/
theorem TermIndexedEndpoints.childrenStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {carrier : RawTerm scope}
    {shifts : List Nat} {rest : RawTermChildren shifts scope}
    (wellFormed : WfContextDesc context)
    (endpoints : TermIndexedEndpoints profile context carrier rest) :
    rest.allStronglyNormalizing :=
  match endpoints with
  | .nil => True.intro
  | .cons _endpoint _restChildren endpointTyped restTyped =>
      ⟨HasTypeDescPi.stronglyNormalizingOfWfContextDesc wellFormed endpointTyped,
        TermIndexedEndpoints.childrenStronglyNormalizing wellFormed restTyped⟩

/-- **Every child of a term-indexed former telescope is strongly normalizing.**  The carrier head is grown-typed
at a universe (SN via the grown open SN); the endpoint tail accumulates via the endpoint companion. -/
theorem TermIndexedFormerTelescope.childrenStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {shifts : List Nat}
    {children : RawTermChildren shifts scope} {carrier : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag}
    (wellFormed : WfContextDesc context)
    (telescope : TermIndexedFormerTelescope profile context children carrier level flag) :
    children.allStronglyNormalizing :=
  match telescope with
  | .mk _carrier _rest _level _flag carrierTyped endpointsTyped =>
      ⟨HasTypeDescPi.stronglyNormalizingOfWfContextDesc wellFormed carrierTyped,
        TermIndexedEndpoints.childrenStronglyNormalizing wellFormed endpointsTyped⟩

/-- **★ Term-indexed former subject strong normalization.**  Every term-indexed-former-typed subject is strongly
normalizing under a well-formed context — the SN piece for the `Id`/`Bridge` engine, consuming the grown
reducibility on its children.  The cell heads no root redex
(`termIndexedFormerCellStronglyNormalizingOfChildren`), and its telescope children are grown-SN
(`TermIndexedFormerTelescope.childrenStronglyNormalizing`). -/
theorem HasTypeDescTermIndexedFormer.subjectStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (wellFormed : WfContextDesc context)
    (derivation : HasTypeDescTermIndexedFormer profile context subject classifier) :
    IsStronglyNormalizing subject := by
  cases derivation with
  | genFormation generator payload children carrier level flag rule isTermIndexed premises =>
      exact termIndexedFormerCellStronglyNormalizingOfChildren isTermIndexed
        (TermIndexedFormerTelescope.childrenStronglyNormalizing wellFormed premises)

/-- **★ Closed corollary.**  Every CLOSED term-indexed-former-typed subject is strongly normalizing,
unconditionally — discharging the `WfContextDesc` hypothesis with `WfContextDesc.emptyIsWellFormed`.  The
canonicity-relevant SN statement (parity with the flat engine's unconditional closed SN). -/
theorem HasTypeDescTermIndexedFormer.closedSubjectStronglyNormalizing {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (derivation : HasTypeDescTermIndexedFormer profile (TypingContext.empty : TypingContext profile 0)
      subject classifier) :
    IsStronglyNormalizing subject :=
  HasTypeDescTermIndexedFormer.subjectStronglyNormalizing WfContextDesc.emptyIsWellFormed derivation

/-- **Closed non-vacuous witness.**  `Bridge(Type@1, Type@0, Type@0)` is strongly normalizing — the SN headline
at the NATIVE-12 bridge-universe smoke, demonstrating the engine types AND strongly normalizes a closed cell. -/
theorem closedBridgeUniverseStronglyNormalizing {profile : PolyProfile} (flag : UniverseFlag) :
    IsStronglyNormalizing
      ((bridgeTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
        (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag)) : RawTerm 0) :=
  HasTypeDescTermIndexedFormer.closedSubjectStronglyNormalizing
    (profile := profile) (termIndexedFormerGenFormation_bridgeUniverseSmoke flag)

end FX1Poly.Typed
