import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionBetaRedexSubjectReduction

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/HasTypeUnionRootStepToTypedOrCongruence
    — the 2-way root-step dispatcher: typed-reduct ∨ congruence — TYTAB-2-FT gate-2 redex half DISCHARGED

This UPGRADES the 3-way `unionRootStepSubjectReduction` (typed ∨ congruence ∨ deferred-shape) to a 2-way
dispatcher: every single `Step` of a union-typed term either yields a reduct union-typed at a `Conv`-equal
classifier, or is a top-level child CONGRUENCE.  The "deferred-shape" disjunct is GONE — every root-redex
firing (`tableRedex`) is now typed inline by the shipped per-shape closers:

  * β: `unionSubjectReductionBetaFromRedex` (unconditional);
  * endpoint-β: `unionSubjectReductionEndpointBetaFromRedex` (unconditional);
  * natElim/natRec succ: `unionSubjectReductionNatElimSuccFromRedex` / `…NatRecSuccFromRedex` (unconditional);
  * fst/snd projection: `unionSubjectReductionFstPair` / `…SndPair` (unconditional);
  * option-some / either-inl/inr / list-cons app-chain: `unionSubjectReduction{OptionMatchSome,EitherMatchInl,
    EitherMatchInr,ListElimCons}` (over `WfContextUnion`);
  * the seven branch-selection ι (bool true/false, natElim/natRec zero, listElim nil, optionMatch none, idJ
    refl) — already typed inline in the source dispatcher;
  * `idStrictRecRefl` — `gen_idStrictRec` is RESERVED (no union typing rule), refuted by `reservedHeadUntyped`;
  * the four reserved heads (quotRec/quotElim/truncRec/ungel) — refuted by `reservedHeadUntyped`.

So the redex half of TYTAB-2-FT gate 2 is unconditionally discharged; the ONLY remaining single-step SR
residual is the congruence disjunct (the native mountain).  Consuming this in the single-step SR master leaves
exactly ONE closer (the congruence closer) instead of two.

## Zero-axiom verification

Faithful reproduction of `unionRootStepSubjectReduction`'s step inversion with each `tableRedex` leaf routed
to a shipped (zero-axiom) closer; no new axiom, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **endpoint-β row firing types its reduct.**  The path-twin bridge: at the `pathBeta` row leaf the reduct
is not pinned by a `…ToIotaHead` cases (the row decomposes through `pathBetaRowFiringDecompose`), so this
helper splits the `pathApp` spine, reads the path-lambda head + the reduct equation off the decomposition, and
applies the unconditional `unionSubjectReductionEndpointBetaFromRedex`. -/
private theorem pathBetaRowFiringSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (elimPayload : pathBetaIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren pathBetaIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (typed : HasTypeUnion profile context
      (RawTerm.mkGen pathBetaIotaRow.elimGenerator elimPayload spine) classifier)
    (fires : pathBetaIotaRow.firesOn? elimPayload spine = some reduct) :
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context reduct pinnedClassifier ∧ Conv pinnedClassifier classifier := by
  revert typed fires
  cases elimPayload
  cases spine with
  | childCons functionChild restSpine =>
    cases restSpine with
    | childCons argumentChild restNil =>
      cases restNil
      intro typed fires
      obtain ⟨pathBody, functionEq, reductEq⟩ := pathBetaRowFiringDecompose fires
      subst functionEq
      subst reductEq
      exact unionSubjectReductionEndpointBetaFromRedex typed

/-- **★ The 2-way root-step subject-reduction dispatcher (redex half of gate 2 discharged).**  For any single
`Step redex reduct` of a union-typed redex, EITHER the reduct is union-typed at a `Conv`-equal classifier (every
root-redex firing, typed by the shipped per-shape closers), OR the step is a top-level child congruence.  The
deferred-shape disjunct of `unionRootStepSubjectReduction` is eliminated.  Takes `WfContextUnion` (the
app-chain ι closers need it). -/
theorem unionRootStepSubjectReductionToTypedOrCongruence {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {redex reduct classifier : RawTerm scope}
    (typed : HasTypeUnion profile context redex classifier)
    (wellFormed : WfContextUnion context)
    (stepHyp : Step redex reduct) :
    (∃ pinnedClassifier : RawTerm scope,
        HasTypeUnion profile context reduct pinnedClassifier ∧
        Conv pinnedClassifier classifier)
    ∨ (∃ (generator : Generator) (payload : generator.payload scope)
         (childrenBefore childrenAfter : RawTermChildren generator.binderShifts scope),
        redex = .mkGen generator payload childrenBefore ∧
        reduct = .mkGen generator payload childrenAfter ∧
        StepChildren childrenBefore childrenAfter) := by
  cases stepOverTable_iff_step.mpr stepHyp with
  | cong generator payload childStep =>
      exact Or.inr ⟨generator, payload, _, _, rfl, rfl,
        StepOverTableChildren.toStepChildren childStep⟩
  | tableRedex isRow elimPayload fires =>
    cases isRow with
    | head =>
        cases betaRowFiringToHeadStep elimPayload fires with
        | beta => exact Or.inl (unionSubjectReductionBetaFromRedex typed)
        | appCongruence functionStep =>
            rename_i functionValue _functionReduct _argumentValue
            cases functionValue with
            | mkGen functionGen functionPayload functionChildren =>
              have isLamHead : functionGen = .gen_lam :=
                IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
              subst isLamHead
              cases functionChildren with
              | childCons domainAnn lamRest =>
                cases lamRest with
                | childCons lamBody lamNil =>
                  cases lamNil
                  exact absurd functionStep HeadStep.not_from_lam
    | tail _ isRow => cases isRow with
      | head =>
          cases boolTrueRowFiringToIotaHead elimPayload fires with
          | iotaBoolTrue =>
              exact Or.inl ⟨classifier,
                (unionSubjectReductionBoolElimTrue typed).2, Conv.refl classifier⟩
          | iotaBoolFalse =>
              exact Or.inl ⟨classifier,
                (unionSubjectReductionBoolElimFalse typed).2, Conv.refl classifier⟩
      | tail _ isRow => cases isRow with
        | head =>
            cases boolFalseRowFiringToIotaHead elimPayload fires with
            | iotaBoolTrue =>
                exact Or.inl ⟨classifier,
                  (unionSubjectReductionBoolElimTrue typed).2, Conv.refl classifier⟩
            | iotaBoolFalse =>
                exact Or.inl ⟨classifier,
                  (unionSubjectReductionBoolElimFalse typed).2, Conv.refl classifier⟩
        | tail _ isRow => cases isRow with
          | head =>
              cases fstPairRowFiringToIotaHead elimPayload fires with
              | iotaFstPair => exact Or.inl (unionSubjectReductionFstPair typed).2
          | tail _ isRow => cases isRow with
            | head =>
                cases sndPairRowFiringToIotaHead elimPayload fires with
                | iotaSndPair => exact Or.inl (unionSubjectReductionSndPair typed).2
            | tail _ isRow => cases isRow with
              | head =>
                  cases natElimZeroRowFiringToIotaHead elimPayload fires with
                  | iotaNatElimZero =>
                      exact Or.inl ⟨classifier,
                        (unionSubjectReductionNatElimZero typed).2, Conv.refl classifier⟩
                  | iotaNatElimSucc =>
                      exact Or.inl (unionSubjectReductionNatElimSuccFromRedex typed)
              | tail _ isRow => cases isRow with
                | head =>
                    cases natRecZeroRowFiringToIotaHead elimPayload fires with
                    | iotaNatRecZero =>
                        exact Or.inl ⟨classifier,
                          (unionSubjectReductionNatRecZero typed).2, Conv.refl classifier⟩
                    | iotaNatRecSucc =>
                        exact Or.inl (unionSubjectReductionNatRecSuccFromRedex typed)
                | tail _ isRow => cases isRow with
                  | head =>
                      cases natElimSuccRowFiringToIotaHead elimPayload fires with
                      | iotaNatElimZero =>
                          exact Or.inl ⟨classifier,
                            (unionSubjectReductionNatElimZero typed).2, Conv.refl classifier⟩
                      | iotaNatElimSucc =>
                          exact Or.inl (unionSubjectReductionNatElimSuccFromRedex typed)
                  | tail _ isRow => cases isRow with
                    | head =>
                        cases natRecSuccRowFiringToIotaHead elimPayload fires with
                        | iotaNatRecZero =>
                            exact Or.inl ⟨classifier,
                              (unionSubjectReductionNatRecZero typed).2, Conv.refl classifier⟩
                        | iotaNatRecSucc =>
                            exact Or.inl (unionSubjectReductionNatRecSuccFromRedex typed)
                    | tail _ isRow => cases isRow with
                      | head =>
                          cases listElimNilRowFiringToIotaHead elimPayload fires with
                          | iotaListElimNil =>
                              exact Or.inl (unionSubjectReductionListElimNil typed).2
                          | iotaListElimCons =>
                              exact Or.inl (unionSubjectReductionListElimCons typed wellFormed).2
                      | tail _ isRow => cases isRow with
                        | head =>
                            cases listElimConsRowFiringToIotaHead elimPayload fires with
                            | iotaListElimNil =>
                                exact Or.inl (unionSubjectReductionListElimNil typed).2
                            | iotaListElimCons =>
                                exact Or.inl (unionSubjectReductionListElimCons typed wellFormed).2
                        | tail _ isRow => cases isRow with
                          | head =>
                              cases optionMatchNoneRowFiringToIotaHead elimPayload fires with
                              | iotaOptionMatchNone =>
                                  exact Or.inl (unionSubjectReductionOptionMatchNone typed).2
                              | iotaOptionMatchSome =>
                                  exact Or.inl (unionSubjectReductionOptionMatchSome typed wellFormed).2
                          | tail _ isRow => cases isRow with
                            | head =>
                                cases optionMatchSomeRowFiringToIotaHead elimPayload fires with
                                | iotaOptionMatchNone =>
                                    exact Or.inl (unionSubjectReductionOptionMatchNone typed).2
                                | iotaOptionMatchSome =>
                                    exact Or.inl (unionSubjectReductionOptionMatchSome typed wellFormed).2
                            | tail _ isRow => cases isRow with
                              | head =>
                                  cases eitherMatchInlRowFiringToIotaHead elimPayload fires with
                                  | iotaEitherMatchInl =>
                                      exact Or.inl (unionSubjectReductionEitherMatchInl typed wellFormed).2
                                  | iotaEitherMatchInr =>
                                      exact Or.inl (unionSubjectReductionEitherMatchInr typed wellFormed).2
                              | tail _ isRow => cases isRow with
                                | head =>
                                    cases eitherMatchInrRowFiringToIotaHead elimPayload fires with
                                    | iotaEitherMatchInl =>
                                        exact Or.inl (unionSubjectReductionEitherMatchInl typed wellFormed).2
                                    | iotaEitherMatchInr =>
                                        exact Or.inl (unionSubjectReductionEitherMatchInr typed wellFormed).2
                                | tail _ isRow => cases isRow with
                                  | head =>
                                      cases idJReflRowFiringToIotaHead elimPayload fires with
                                      | iotaIdJRefl =>
                                          exact Or.inl ⟨classifier,
                                            (unionSubjectReductionIdJRefl typed).2, Conv.refl classifier⟩
                                  | tail _ isRow => cases isRow with
                                    | head =>
                                        cases idStrictRecReflRowFiringToIotaHead elimPayload fires with
                                        | iotaIdStrictRecRefl =>
                                            exact (typed.reservedHeadUntyped rfl).elim
                                    | tail _ isRow => cases isRow with
                                      | head =>
                                          exact Or.inl (pathBetaRowFiringSubjectReduction elimPayload typed fires)
                                      | tail _ isRow => cases isRow with
                                        | head =>
                                            exact (typed.reservedHeadUntyped rfl).elim
                                        | tail _ isRow => cases isRow with
                                          | head =>
                                              exact (typed.reservedHeadUntyped rfl).elim
                                          | tail _ isRow => cases isRow with
                                            | head =>
                                                exact (typed.reservedHeadUntyped rfl).elim
                                            | tail _ isRow => cases isRow with
                                              | head =>
                                                  exact (typed.reservedHeadUntyped rfl).elim
                                              | tail _ isRow => cases isRow

end FX1Poly.Typed
