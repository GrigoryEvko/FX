import FX1Poly.Core.Rewriting.Reduction.Head.IotaHeadStep
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSubjectReduction
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionBetaRedexSubjectReduction
import FX1Poly.Typed.Engine.Classifier.UnionStaticTypingSoundness

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/HasTypeUnionIotaHeadStepSubjectReduction
    — subject reduction for a root-ι (`IotaHeadStep`) step (the `rootIota` base case of weak-head SR)

The native-union subject-reduction closer keyed on the root-ι relation `IotaHeadStep` directly (the
weak-head route's `rootIota` arm, consistency leg #1697/#1740).  `cases` on the seventeen `IotaHeadStep`
constructors routes each firing to its shipped per-row union SR closer — the same closers the root-step
dispatcher `unionRootStepSubjectReductionToTypedOrCongruence` calls, here exposed as one clean
`IotaHeadStep`-keyed interface so the weak-head single-step SR recursion can discharge its `rootIota`
constructor in a single `exact`.  The reserved `gen_idStrictRec` row carries no union typing rule, so its
ι-redex cannot be union-typed at all — refuted by `reservedHeadUntyped`.

Unlike the `Step`-keyed dispatcher this carries NO congruence disjunct: an `IotaHeadStep` is a genuine root
redex, so the reduct is ALWAYS union-typed at a `Conv`-equal classifier.  The only hypothesis is the
`WfContextUnion` presupposition (#1696), needed by the four app-chain ι rows (cons / some / inl / inr).

## Zero-axiom verification

`cases` on `IotaHeadStep`, the shipped per-row closers (each zero-axiom), and `reservedHeadUntyped` for the
reserved row.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **★ Subject reduction for a root-ι step.**  A union-typed ι-redex whose head fires (`IotaHeadStep term
reduct`) re-types its reduct at a `Conv`-equal classifier.  The seventeen-constructor `cases` routes each
firing to its shipped per-row SR closer; the reserved `gen_idStrictRec` row is refuted by
`reservedHeadUntyped` (no union eliminator typing rule). -/
theorem HasTypeUnion.iotaHeadStepSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {term reduct classifier : RawTerm scope}
    (typed : HasTypeUnion profile context term classifier)
    (wellFormed : WfContextUnion context)
    (iotaHead : IotaHeadStep term reduct) :
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context reduct pinnedClassifier ∧ Conv pinnedClassifier classifier := by
  cases iotaHead with
  | iotaBoolTrue =>
      obtain ⟨_, reductTyped, convLeg⟩ := unionSubjectReductionBoolElimTrue typed
      exact ⟨_, reductTyped, convLeg⟩
  | iotaBoolFalse =>
      obtain ⟨_, reductTyped, convLeg⟩ := unionSubjectReductionBoolElimFalse typed
      exact ⟨_, reductTyped, convLeg⟩
  | iotaFstPair => exact (unionSubjectReductionFstPair typed).2
  | iotaSndPair => exact (unionSubjectReductionSndPair typed).2
  | iotaNatElimZero =>
      obtain ⟨_, reductTyped, convLeg⟩ := unionSubjectReductionNatElimZero typed
      exact ⟨_, reductTyped, convLeg⟩
  | iotaNatRecZero =>
      obtain ⟨_, reductTyped, convLeg⟩ := unionSubjectReductionNatRecZero typed
      exact ⟨_, reductTyped, convLeg⟩
  | iotaListElimNil => exact (unionSubjectReductionListElimNil typed).2
  | iotaOptionMatchNone => exact (unionSubjectReductionOptionMatchNone typed).2
  | iotaOptionMatchSome => exact (unionSubjectReductionOptionMatchSome typed wellFormed).2
  | iotaEitherMatchInl => exact (unionSubjectReductionEitherMatchInl typed wellFormed).2
  | iotaEitherMatchInr => exact (unionSubjectReductionEitherMatchInr typed wellFormed).2
  | iotaNatElimSucc => exact unionSubjectReductionNatElimSuccFromRedex typed
  | iotaNatRecSucc => exact unionSubjectReductionNatRecSuccFromRedex typed
  | iotaListElimCons => exact (unionSubjectReductionListElimCons typed wellFormed).2
  | iotaIdJRefl => exact (unionSubjectReductionIdJRefl typed).2
  | iotaIdStrictRecRefl => exact (typed.reservedHeadUntyped rfl).elim

end FX1Poly.Typed
