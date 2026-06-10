import FX1Poly.Core.IotaHeadStep
import FX1Poly.Core.WeakHeadStep
import FX1Poly.Core.WeakHeadStepNormalForms
import FX1Poly.Core.HeadStep
import FX1Poly.Core.StepInversion
import FX1Poly.Core.StepSubst
import FX1Poly.Core.StepStar

/-! # Foundation/PolyCell/Core/WeakHeadStepCommute
    — the complete weak-head reduction commutes with arbitrary single-step reduction

`HeadStepCommute2` proved the β-only weak-head step (`HeadStep`) commutes with an arbitrary `Step`.
`ReducibleType` now dispatches on the COMPLETE weak-head reduction `WeakHeadStep` (β + root-ι +
scrutinee-congruence), so conversion-invariance needs the commutation diamond for `WeakHeadStep`:

```
        WeakHeadStep         Step
  term ──────────► reduct ,  term ──────────► other
```

Either the arbitrary step contracted the very weak-head redex (`other = reduct`), or the redex SURVIVES
— `other` weak-head steps to some `otherReduct` and the two contracta re-converge by a `StepStar` chain
(`reduct ↠ otherReduct`).  The chain (not a single step) is essential: a β-redex argument or an
eliminator branch can occur MORE THAN ONCE in the contractum (`natElim (natSucc p) z s ↝ app (app s p)
(natElim p z s)` has `p` twice, `s` twice), so replaying one source step replays it once per occurrence.

The diamond is assembled in two lemmas:

  * `IotaHeadStep.commuteWithStep` — the root-ι half: sixteen flat cases (one per ι rule).  The arbitrary
    step is inverted by raw `cases`; index unification auto-selects the matching ι (other = reduct),
    auto-discards the wrong-constructor ι, and the `cong` case splits on which child stepped.  A step in
    the constructor scrutinee or a branch leaves the ι redex intact, so `other` still ι-reduces and the
    contractum congruence (built from `StepStar.appFunction`/`appArgument` over the app spine and the
    generic one-hole lifter `StepStar.congAt` into the recursive eliminator) catches `reduct` up.

  * `WeakHeadStep.commuteWithStep` — the full relation, by induction on the `WeakHeadStep` derivation.  β
    and `appCongruence` mirror `HeadStep.commuteWithStep` (the β-redex / function-spine cases, with
    `Step.subst0Body`/`Step.subst0Argument` replaying argument reduction across the substitution); the
    `rootIota` case delegates to `IotaHeadStep.commuteWithStep` and re-wraps with `.rootIota`; each of the
    ten `scrutineeCong` cases inverts the arbitrary step with the eliminator's `Step.from_<elim>`, refutes
    the ι disjuncts via the `WeakHeadStep.not_from_<ctor>` normal-form lemmas (a reducible scrutinee is
    not yet a constructor), applies the induction hypothesis to a scrutinee step, and lifts a branch step
    by `StepStar.congAt`.

## Zero-axiom verification

The generic lifter `StepStar.congAt` is induction on the `StepStar` chain.  `IotaHeadStep.commuteWithStep`
is `cases` on the ι rule then `cases` inverting the `Step` and its `StepChildren` spine (the propext-clean
route the whole `Step`-inversion family uses); impossible spine tails close by `cases` on the empty
`StepChildren`.  `WeakHeadStep.commuteWithStep` is induction reusing the shipped `Step.from_<elim>`
inversions and `WeakHeadStep.not_from_<ctor>` refutes.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **One-hole-context chain lift.**  Replay a `StepStar` chain inside a single-hole context, given that
the context lifts ONE `Step` through its hole.  The general substrate the eliminator-child congruences
(scrutinee / branch positions) are built from: instantiate `oneHoleContext` with the eliminator wrapped
around its stepping child and `liftStepThroughHole` with the uniform `Step.cong` at that child. -/
theorem StepStar.congAt {scope : Nat} {subjectStart subjectEnd : RawTerm scope}
    (oneHoleContext : RawTerm scope → RawTerm scope)
    (liftStepThroughHole : ∀ {filledStart filledEnd : RawTerm scope},
      Step filledStart filledEnd → Step (oneHoleContext filledStart) (oneHoleContext filledEnd))
    (innerChain : StepStar subjectStart subjectEnd) :
    StepStar (oneHoleContext subjectStart) (oneHoleContext subjectEnd) := by
  induction innerChain with
  | refl _ => exact StepStar.refl _
  | trans headStep _restChain restCongruence =>
      exact StepStar.trans (liftStepThroughHole headStep) restCongruence

/-- **Root-iota reduction commutes with arbitrary single-step reduction.**  Given a root-ι step
`term ↝ᵢ reduct` and any step `term ↝ other`, either the arbitrary step contracted the same ι redex
(`other = reduct`), or the redex survives — `other` ι-reduces to some `otherReduct` and `reduct` catches
up by a `StepStar` chain (`reduct ↠ otherReduct`). -/
theorem IotaHeadStep.commuteWithStep {scope : Nat} {term reduct : RawTerm scope}
    (iotaStep : IotaHeadStep term reduct) :
    ∀ (other : RawTerm scope), Step term other →
      other = reduct ∨
        ∃ otherReduct : RawTerm scope, IotaHeadStep other otherReduct ∧ StepStar reduct otherReduct := by
  cases iotaStep with
  | @iotaBoolTrue motive thenBranch elseBranch =>
      -- Phase-Z spine: (motive, then, else, scrutinee=boolTrue).  The cong spine walks
      -- motive (here) → then → else → scrutinee.  Only a step in the then-branch changes
      -- the selected reduct; motive/else/scrutinee steps leave thenBranch intact.
      intro other step
      cases step with
      | iotaBoolTrue => exact Or.inl rfl
      | cong _generator _payload childStep =>
          cases childStep with
          | here _rest _motiveStep =>
              exact Or.inr ⟨_, IotaHeadStep.iotaBoolTrue, StepStar.refl _⟩
          | there _head tailStep =>
              cases tailStep with
              | here _rest thenStep =>
                  exact Or.inr ⟨_, IotaHeadStep.iotaBoolTrue, StepStar.single thenStep⟩
              | there _head2 restStep =>
                  cases restStep with
                  | here _rest _elseStep =>
                      exact Or.inr ⟨_, IotaHeadStep.iotaBoolTrue, StepStar.refl _⟩
                  | there _head3 scrutineeTailStep =>
                      cases scrutineeTailStep with
                      | here _rest scrutineeStep =>
                          cases scrutineeStep with | cong _g _p emptyChild => cases emptyChild
                      | there _head4 emptyStep => cases emptyStep
  | @iotaBoolFalse motive thenBranch elseBranch =>
      -- Phase-Z spine: (motive, then, else, scrutinee=boolFalse).  Only a step in the
      -- else-branch changes the selected reduct; motive/then/scrutinee steps leave
      -- elseBranch intact.
      intro other step
      cases step with
      | iotaBoolFalse => exact Or.inl rfl
      | cong _generator _payload childStep =>
          cases childStep with
          | here _rest _motiveStep =>
              exact Or.inr ⟨_, IotaHeadStep.iotaBoolFalse, StepStar.refl _⟩
          | there _head tailStep =>
              cases tailStep with
              | here _rest _thenStep =>
                  exact Or.inr ⟨_, IotaHeadStep.iotaBoolFalse, StepStar.refl _⟩
              | there _head2 restStep =>
                  cases restStep with
                  | here _rest elseStep =>
                      exact Or.inr ⟨_, IotaHeadStep.iotaBoolFalse, StepStar.single elseStep⟩
                  | there _head3 scrutineeTailStep =>
                      cases scrutineeTailStep with
                      | here _rest scrutineeStep =>
                          cases scrutineeStep with | cong _g _p emptyChild => cases emptyChild
                      | there _head4 emptyStep => cases emptyStep
  | @iotaFstPair firstValue secondValue =>
      intro other step
      cases step with
      | iotaFstPair => exact Or.inl rfl
      | cong _generator _payload childStep =>
          cases childStep with
          | here _rest scrutineeStep =>
              cases scrutineeStep with
              | cong _g _p pairChild =>
                  cases pairChild with
                  | here _rest firstStep =>
                      exact Or.inr ⟨_, IotaHeadStep.iotaFstPair, StepStar.single firstStep⟩
                  | there _head tailStep =>
                      cases tailStep with
                      | here _rest secondStep =>
                          exact Or.inr ⟨_, IotaHeadStep.iotaFstPair, StepStar.refl _⟩
                      | there _head2 emptyStep => cases emptyStep
          | there _head emptyStep => cases emptyStep
  | @iotaSndPair firstValue secondValue =>
      intro other step
      cases step with
      | iotaSndPair => exact Or.inl rfl
      | cong _generator _payload childStep =>
          cases childStep with
          | here _rest scrutineeStep =>
              cases scrutineeStep with
              | cong _g _p pairChild =>
                  cases pairChild with
                  | here _rest firstStep =>
                      exact Or.inr ⟨_, IotaHeadStep.iotaSndPair, StepStar.refl _⟩
                  | there _head tailStep =>
                      cases tailStep with
                      | here _rest secondStep =>
                          exact Or.inr ⟨_, IotaHeadStep.iotaSndPair, StepStar.single secondStep⟩
                      | there _head2 emptyStep => cases emptyStep
          | there _head emptyStep => cases emptyStep
  | @iotaNatElimZero zeroBranch succBranch =>
      intro other step
      cases step with
      | iotaNatElimZero => exact Or.inl rfl
      | cong _generator _payload childStep =>
          cases childStep with
          | here _rest scrutineeStep =>
              cases scrutineeStep with | cong _g _p emptyChild => cases emptyChild
          | there _head tailStep =>
              cases tailStep with
              | here _rest zeroStep =>
                  exact Or.inr ⟨_, IotaHeadStep.iotaNatElimZero, StepStar.single zeroStep⟩
              | there _head2 restStep =>
                  cases restStep with
                  | here _rest succStep =>
                      exact Or.inr ⟨_, IotaHeadStep.iotaNatElimZero, StepStar.refl _⟩
                  | there _head3 emptyStep => cases emptyStep
  | @iotaNatRecZero zeroBranch succBranch =>
      intro other step
      cases step with
      | iotaNatRecZero => exact Or.inl rfl
      | cong _generator _payload childStep =>
          cases childStep with
          | here _rest scrutineeStep =>
              cases scrutineeStep with | cong _g _p emptyChild => cases emptyChild
          | there _head tailStep =>
              cases tailStep with
              | here _rest zeroStep =>
                  exact Or.inr ⟨_, IotaHeadStep.iotaNatRecZero, StepStar.single zeroStep⟩
              | there _head2 restStep =>
                  cases restStep with
                  | here _rest succStep =>
                      exact Or.inr ⟨_, IotaHeadStep.iotaNatRecZero, StepStar.refl _⟩
                  | there _head3 emptyStep => cases emptyStep
  | @iotaListElimNil motive nilBranch consBranch =>
      -- Phase-Z spine: (motive, nil, cons, scrutinee=listNil).  The cong spine walks
      -- motive (here) → nil → cons → scrutinee.  Only a step in the nil-branch changes
      -- the selected reduct; motive/cons/scrutinee steps leave nilBranch intact.
      intro other step
      cases step with
      | iotaListElimNil => exact Or.inl rfl
      | cong _generator _payload childStep =>
          cases childStep with
          | here _rest _motiveStep =>
              exact Or.inr ⟨_, IotaHeadStep.iotaListElimNil, StepStar.refl _⟩
          | there _head tailStep =>
              cases tailStep with
              | here _rest nilStep =>
                  exact Or.inr ⟨_, IotaHeadStep.iotaListElimNil, StepStar.single nilStep⟩
              | there _head2 restStep =>
                  cases restStep with
                  | here _rest _consStep =>
                      exact Or.inr ⟨_, IotaHeadStep.iotaListElimNil, StepStar.refl _⟩
                  | there _head3 scrutineeTailStep =>
                      cases scrutineeTailStep with
                      | here _rest scrutineeStep =>
                          cases scrutineeStep with | cong _g _p emptyChild => cases emptyChild
                      | there _head4 emptyStep => cases emptyStep
  | @iotaOptionMatchNone noneBranch someBranch =>
      intro other step
      cases step with
      | iotaOptionMatchNone => exact Or.inl rfl
      | cong _generator _payload childStep =>
          cases childStep with
          | here _rest scrutineeStep =>
              cases scrutineeStep with | cong _g _p emptyChild => cases emptyChild
          | there _head tailStep =>
              cases tailStep with
              | here _rest noneStep =>
                  exact Or.inr ⟨_, IotaHeadStep.iotaOptionMatchNone, StepStar.single noneStep⟩
              | there _head2 restStep =>
                  cases restStep with
                  | here _rest someStep =>
                      exact Or.inr ⟨_, IotaHeadStep.iotaOptionMatchNone, StepStar.refl _⟩
                  | there _head3 emptyStep => cases emptyStep
  | @iotaOptionMatchSome value noneBranch someBranch =>
      intro other step
      cases step with
      | iotaOptionMatchSome => exact Or.inl rfl
      | cong _generator _payload childStep =>
          cases childStep with
          | here _rest scrutineeStep =>
              cases scrutineeStep with
              | cong _g _p valueChild =>
                  cases valueChild with
                  | here _rest valueStep =>
                      exact Or.inr ⟨_, IotaHeadStep.iotaOptionMatchSome,
                        StepStar.appArgument someBranch (StepStar.single valueStep)⟩
                  | there _head emptyStep => cases emptyStep
          | there _head tailStep =>
              cases tailStep with
              | here _rest noneStep =>
                  exact Or.inr ⟨_, IotaHeadStep.iotaOptionMatchSome, StepStar.refl _⟩
              | there _head2 restStep =>
                  cases restStep with
                  | here _rest someStep =>
                      exact Or.inr ⟨_, IotaHeadStep.iotaOptionMatchSome,
                        StepStar.appFunction (StepStar.single someStep)⟩
                  | there _head3 emptyStep => cases emptyStep
  | @iotaEitherMatchInl value leftBranch rightBranch =>
      intro other step
      cases step with
      | iotaEitherMatchInl => exact Or.inl rfl
      | cong _generator _payload childStep =>
          cases childStep with
          | here _rest scrutineeStep =>
              cases scrutineeStep with
              | cong _g _p valueChild =>
                  cases valueChild with
                  | here _rest valueStep =>
                      exact Or.inr ⟨_, IotaHeadStep.iotaEitherMatchInl,
                        StepStar.appArgument leftBranch (StepStar.single valueStep)⟩
                  | there _head emptyStep => cases emptyStep
          | there _head tailStep =>
              cases tailStep with
              | here _rest leftStep =>
                  exact Or.inr ⟨_, IotaHeadStep.iotaEitherMatchInl,
                    StepStar.appFunction (StepStar.single leftStep)⟩
              | there _head2 restStep =>
                  cases restStep with
                  | here _rest rightStep =>
                      exact Or.inr ⟨_, IotaHeadStep.iotaEitherMatchInl, StepStar.refl _⟩
                  | there _head3 emptyStep => cases emptyStep
  | @iotaEitherMatchInr value leftBranch rightBranch =>
      intro other step
      cases step with
      | iotaEitherMatchInr => exact Or.inl rfl
      | cong _generator _payload childStep =>
          cases childStep with
          | here _rest scrutineeStep =>
              cases scrutineeStep with
              | cong _g _p valueChild =>
                  cases valueChild with
                  | here _rest valueStep =>
                      exact Or.inr ⟨_, IotaHeadStep.iotaEitherMatchInr,
                        StepStar.appArgument rightBranch (StepStar.single valueStep)⟩
                  | there _head emptyStep => cases emptyStep
          | there _head tailStep =>
              cases tailStep with
              | here _rest leftStep =>
                  exact Or.inr ⟨_, IotaHeadStep.iotaEitherMatchInr, StepStar.refl _⟩
              | there _head2 restStep =>
                  cases restStep with
                  | here _rest rightStep =>
                      exact Or.inr ⟨_, IotaHeadStep.iotaEitherMatchInr,
                        StepStar.appFunction (StepStar.single rightStep)⟩
                  | there _head3 emptyStep => cases emptyStep
  | @iotaNatElimSucc predecessor zeroBranch succBranch =>
      intro other step
      cases step with
      | iotaNatElimSucc => exact Or.inl rfl
      | cong _generator _payload childStep =>
          cases childStep with
          | here _rest scrutineeStep =>
              cases scrutineeStep with
              | cong _g _p predChild =>
                  cases predChild with
                  | here _rest predStep =>
                      exact Or.inr ⟨_, IotaHeadStep.iotaNatElimSucc,
                        StepStar.trans_compose
                          (StepStar.appFunction
                            (StepStar.appArgument succBranch (StepStar.single predStep)))
                          (StepStar.appArgument _
                            (StepStar.congAt
                              (fun hole => .mkGen .gen_natElim ()
                                (.childCons hole (.childCons zeroBranch (.childCons succBranch .childNil))))
                              (fun childStep' => Step.cong .gen_natElim () (.here _ childStep'))
                              (StepStar.single predStep)))⟩
                  | there _head emptyStep => cases emptyStep
          | there _head tailStep =>
              cases tailStep with
              | here _rest zeroStep =>
                  exact Or.inr ⟨_, IotaHeadStep.iotaNatElimSucc,
                    StepStar.appArgument _
                      (StepStar.congAt
                        (fun hole => .mkGen .gen_natElim ()
                          (.childCons predecessor (.childCons hole (.childCons succBranch .childNil))))
                        (fun childStep' => Step.cong .gen_natElim () (.there _ (.here _ childStep')))
                        (StepStar.single zeroStep))⟩
              | there _head2 restStep =>
                  cases restStep with
                  | here _rest succStep =>
                      exact Or.inr ⟨_, IotaHeadStep.iotaNatElimSucc,
                        StepStar.trans_compose
                          (StepStar.appFunction (StepStar.appFunction (StepStar.single succStep)))
                          (StepStar.appArgument _
                            (StepStar.congAt
                              (fun hole => .mkGen .gen_natElim ()
                                (.childCons predecessor (.childCons zeroBranch (.childCons hole .childNil))))
                              (fun childStep' =>
                                Step.cong .gen_natElim () (.there _ (.there _ (.here _ childStep'))))
                              (StepStar.single succStep)))⟩
                  | there _head3 emptyStep => cases emptyStep
  | @iotaNatRecSucc predecessor zeroBranch succBranch =>
      intro other step
      cases step with
      | iotaNatRecSucc => exact Or.inl rfl
      | cong _generator _payload childStep =>
          cases childStep with
          | here _rest scrutineeStep =>
              cases scrutineeStep with
              | cong _g _p predChild =>
                  cases predChild with
                  | here _rest predStep =>
                      exact Or.inr ⟨_, IotaHeadStep.iotaNatRecSucc,
                        StepStar.trans_compose
                          (StepStar.appFunction
                            (StepStar.appArgument succBranch (StepStar.single predStep)))
                          (StepStar.appArgument _
                            (StepStar.congAt
                              (fun hole => .mkGen .gen_natRec ()
                                (.childCons hole (.childCons zeroBranch (.childCons succBranch .childNil))))
                              (fun childStep' => Step.cong .gen_natRec () (.here _ childStep'))
                              (StepStar.single predStep)))⟩
                  | there _head emptyStep => cases emptyStep
          | there _head tailStep =>
              cases tailStep with
              | here _rest zeroStep =>
                  exact Or.inr ⟨_, IotaHeadStep.iotaNatRecSucc,
                    StepStar.appArgument _
                      (StepStar.congAt
                        (fun hole => .mkGen .gen_natRec ()
                          (.childCons predecessor (.childCons hole (.childCons succBranch .childNil))))
                        (fun childStep' => Step.cong .gen_natRec () (.there _ (.here _ childStep')))
                        (StepStar.single zeroStep))⟩
              | there _head2 restStep =>
                  cases restStep with
                  | here _rest succStep =>
                      exact Or.inr ⟨_, IotaHeadStep.iotaNatRecSucc,
                        StepStar.trans_compose
                          (StepStar.appFunction (StepStar.appFunction (StepStar.single succStep)))
                          (StepStar.appArgument _
                            (StepStar.congAt
                              (fun hole => .mkGen .gen_natRec ()
                                (.childCons predecessor (.childCons zeroBranch (.childCons hole .childNil))))
                              (fun childStep' =>
                                Step.cong .gen_natRec () (.there _ (.there _ (.here _ childStep'))))
                              (StepStar.single succStep)))⟩
                  | there _head3 emptyStep => cases emptyStep
  | @iotaListElimCons motive headVal tailVal nilBranch consBranch =>
      -- Phase-Z spine: (motive, nil, cons, scrutinee=listCons headVal tailVal).  The reduct
      -- `app (app (app cons headVal) tailVal) (listElim motive nil cons tailVal)` THREADS the
      -- motive through the recursive call, so a motive step also catches up via the recursive
      -- eliminator.  The cong spine walks motive (here) → nil → cons → scrutinee; the scrutinee
      -- (`listCons`) splits into head / tail.
      intro other step
      cases step with
      | iotaListElimCons => exact Or.inl rfl
      | cong _generator _payload childStep =>
          cases childStep with
          | here _rest motiveStep =>
              -- The motive lives at scope + 1; lift its step into the recursive `listElim`'s
              -- motive child (`Step.cong … (.here _ motiveStep)`) as a single scope-level step,
              -- then replay it in the application argument.
              exact Or.inr ⟨_, IotaHeadStep.iotaListElimCons,
                StepStar.appArgument _
                  (StepStar.single (Step.cong .gen_listElim () (.here _ motiveStep)))⟩
          | there _head tailStep =>
              cases tailStep with
              | here _rest nilStep =>
                  exact Or.inr ⟨_, IotaHeadStep.iotaListElimCons,
                    StepStar.appArgument _
                      (StepStar.congAt
                        (fun hole => .mkGen .gen_listElim ()
                          (.childCons motive
                            (.childCons hole (.childCons consBranch (.childCons tailVal .childNil)))))
                        (fun childStep' => Step.cong .gen_listElim () (.there _ (.here _ childStep')))
                        (StepStar.single nilStep))⟩
              | there _head2 restStep =>
                  cases restStep with
                  | here _rest consStep =>
                      exact Or.inr ⟨_, IotaHeadStep.iotaListElimCons,
                        StepStar.trans_compose
                          (StepStar.appFunction
                            (StepStar.appFunction (StepStar.appFunction (StepStar.single consStep))))
                          (StepStar.appArgument _
                            (StepStar.congAt
                              (fun hole => .mkGen .gen_listElim ()
                                (.childCons motive
                                  (.childCons nilBranch (.childCons hole (.childCons tailVal .childNil)))))
                              (fun childStep' =>
                                Step.cong .gen_listElim () (.there _ (.there _ (.here _ childStep'))))
                              (StepStar.single consStep)))⟩
                  | there _head3 scrutineeTailStep =>
                      cases scrutineeTailStep with
                      | here _rest scrutineeStep =>
                          cases scrutineeStep with
                          | cong _g _p consChild =>
                              cases consChild with
                              | here _rest headStep =>
                                  exact Or.inr ⟨_, IotaHeadStep.iotaListElimCons,
                                    StepStar.appFunction
                                      (StepStar.appFunction
                                        (StepStar.appArgument consBranch (StepStar.single headStep)))⟩
                              | there _head4 tailChild =>
                                  cases tailChild with
                                  | here _rest tailValStep =>
                                      exact Or.inr ⟨_, IotaHeadStep.iotaListElimCons,
                                        StepStar.trans_compose
                                          (StepStar.appFunction
                                            (StepStar.appArgument _ (StepStar.single tailValStep)))
                                          (StepStar.appArgument _
                                            (StepStar.congAt
                                              (fun hole => .mkGen .gen_listElim ()
                                                (.childCons motive
                                                  (.childCons nilBranch
                                                    (.childCons consBranch (.childCons hole .childNil)))))
                                              (fun childStep' =>
                                                Step.cong .gen_listElim ()
                                                  (.there _ (.there _ (.there _ (.here _ childStep')))))
                                              (StepStar.single tailValStep)))⟩
                                  | there _head5 emptyStep => cases emptyStep
                      | there _head4 emptyStep => cases emptyStep
  | @iotaIdJRefl baseCase rawWitness =>
      intro other step
      cases step with
      | iotaIdJRefl => exact Or.inl rfl
      | cong _generator _payload childStep =>
          cases childStep with
          | here _rest baseStep =>
              exact Or.inr ⟨_, IotaHeadStep.iotaIdJRefl, StepStar.single baseStep⟩
          | there _head tailStep =>
              cases tailStep with
              | here _rest scrutineeStep =>
                  cases scrutineeStep with
                  | cong _g _p witnessChild =>
                      cases witnessChild with
                      | here _rest witnessStep =>
                          exact Or.inr ⟨_, IotaHeadStep.iotaIdJRefl, StepStar.refl _⟩
                      | there _head2 emptyStep => cases emptyStep
              | there _head2 emptyStep => cases emptyStep
  | @iotaIdStrictRecRefl baseCase rawWitness =>
      intro other step
      cases step with
      | iotaIdStrictRecRefl => exact Or.inl rfl
      | cong _generator _payload childStep =>
          cases childStep with
          | here _rest baseStep =>
              exact Or.inr ⟨_, IotaHeadStep.iotaIdStrictRecRefl, StepStar.single baseStep⟩
          | there _head tailStep =>
              cases tailStep with
              | here _rest scrutineeStep =>
                  cases scrutineeStep with
                  | cong _g _p witnessChild =>
                      cases witnessChild with
                      | here _rest witnessStep =>
                          exact Or.inr ⟨_, IotaHeadStep.iotaIdStrictRecRefl, StepStar.refl _⟩
                      | there _head2 emptyStep => cases emptyStep
              | there _head2 emptyStep => cases emptyStep

/-- **The complete weak-head reduction commutes with arbitrary single-step reduction.**  Given a weak-head
step `term ↝ʰ reduct` and any step `term ↝ other`, either the arbitrary step contracted the same weak-head
redex (`other = reduct`), or the redex survives — `other` weak-head steps to some `otherReduct` and
`reduct` catches up by a `StepStar` chain.  Induction on the `WeakHeadStep` derivation: `beta`/
`appCongruence` mirror `HeadStep.commuteWithStep` (β-redex argument/body substitution replays via
`Step.subst0Body`/`Step.subst0Argument`); `rootIota` delegates to `IotaHeadStep.commuteWithStep`; each
`scrutineeCong` case inverts by the eliminator's `Step.from_<elim>`, refutes the ι disjuncts via the
`WeakHeadStep.not_from_<ctor>` normal-form lemmas (a reducible scrutinee is not yet a constructor), recurses
on a scrutinee step, and lifts a branch step by `StepStar.congAt`. -/
theorem WeakHeadStep.commuteWithStep {scope : Nat} {term reduct : RawTerm scope}
    (weakHeadStep : WeakHeadStep term reduct) :
    ∀ (other : RawTerm scope), Step term other →
      other = reduct ∨
        ∃ otherReduct : RawTerm scope, WeakHeadStep other otherReduct ∧ StepStar reduct otherReduct := by
  induction weakHeadStep with
  | @beta domainAnn body argument =>
      intro other step
      cases step with
      | beta => exact Or.inl rfl
      | cong _generator _payload childStep =>
          cases childStep with
          | here _rest functionStep =>
              rcases Step.from_lam functionStep with
                ⟨domainAfter, functionEquation, _domainStep⟩ |
                ⟨bodyAfter, functionEquation, bodyStep⟩
              · subst functionEquation
                exact Or.inr ⟨_, WeakHeadStep.beta, StepStar.refl _⟩
              · subst functionEquation
                exact Or.inr ⟨_, WeakHeadStep.beta, Step.subst0Body argument bodyStep⟩
          | there _head tailStep =>
              cases tailStep with
              | here _rest argumentStep =>
                  exact Or.inr ⟨_, WeakHeadStep.beta, Step.subst0Argument body argumentStep⟩
              | there _head2 emptyStep => cases emptyStep
  | @appCongruence function functionReduct argument functionWeakHeadStep functionInductiveHypothesis =>
      intro other step
      rcases Step.from_app step with
        ⟨_betaDomainAnn, betaBody, functionEquation, _targetEquation⟩
        | ⟨functionAfter, targetEquation, functionStep⟩
        | ⟨argumentAfter, targetEquation, argumentStep⟩
      · rw [functionEquation] at functionWeakHeadStep
        exact absurd functionWeakHeadStep WeakHeadStep.not_from_lam
      · subst targetEquation
        rcases functionInductiveHypothesis _ functionStep with
          functionAfterEquation | ⟨functionReduct2, weakHeadStep2, starChain⟩
        · subst functionAfterEquation
          exact Or.inl rfl
        · exact Or.inr
            ⟨_, WeakHeadStep.appCongruence weakHeadStep2, StepStar.appFunction starChain⟩
      · subst targetEquation
        exact Or.inr
          ⟨_, WeakHeadStep.appCongruence functionWeakHeadStep,
            StepStar.appArgument functionReduct (StepStar.single argumentStep)⟩
  | @rootIota _innerTerm _innerReduct iotaStep =>
      intro other step
      rcases iotaStep.commuteWithStep other step with equation | ⟨otherReduct, iotaOther, starChain⟩
      · exact Or.inl equation
      · exact Or.inr ⟨otherReduct, WeakHeadStep.rootIota iotaOther, starChain⟩
  | @scrutineeBoolElim motive scrutinee scrutineeReduct thenBranch elseBranch
      scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      -- Phase-Z spine: (motive, then, else, scrutinee).  The WeakHeadStep reduces the LAST
      -- child (scrutinee).  `Step.from_boolElim` is a six-way disjunction in the order
      -- iotaTrue / iotaFalse / cong-motive / cong-then / cong-else / cong-scrutinee.  The two
      -- iota disjuncts are refuted (a reducible scrutinee is not yet a constructor); motive,
      -- then, and else steps leave the scrutinee reducible, so `other` still weak-head reduces
      -- there and `reduct` catches up by a single congruence at the stepped child; a scrutinee
      -- step recurses through the induction hypothesis.
      intro other step
      rcases Step.from_boolElim step with
        ⟨scrutEq, _⟩ | ⟨scrutEq, _⟩
        | ⟨_motiveAfter, otherEq, motiveStep⟩
        | ⟨_thenAfter, otherEq, thenStep⟩
        | ⟨_elseAfter, otherEq, elseStep⟩
        | ⟨_scrutAfter, otherEq, scrutStep⟩
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_boolTrue
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_boolFalse
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeBoolElim scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_boolElim () (.here _ motiveStep))⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeBoolElim scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_boolElim () (.there _ (.here _ thenStep)))⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeBoolElim scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_boolElim () (.there _ (.there _ (.here _ elseStep))))⟩
      · subst otherEq
        rcases scrutineeInductiveHypothesis _ scrutStep with
          scrutAfterEquation | ⟨_scrutReduct2, weakHeadStep2, starChain⟩
        · subst scrutAfterEquation; exact Or.inl rfl
        · exact Or.inr ⟨_, WeakHeadStep.scrutineeBoolElim weakHeadStep2,
            StepStar.congAt
              (fun hole => .mkGen .gen_boolElim ()
                (.childCons motive
                  (.childCons thenBranch (.childCons elseBranch (.childCons hole .childNil)))))
              (fun childStep' =>
                Step.cong .gen_boolElim ()
                  (.there _ (.there _ (.there _ (.here _ childStep'))))) starChain⟩
  | @scrutineeFst scrutinee scrutineeReduct scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      intro other step
      rcases Step.from_fst step with
        ⟨_firstValue, _secondValue, scrutEq, _⟩ | ⟨_scrutAfter, otherEq, scrutStep⟩
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_pair
      · subst otherEq
        rcases scrutineeInductiveHypothesis _ scrutStep with
          scrutAfterEquation | ⟨_scrutReduct2, weakHeadStep2, starChain⟩
        · subst scrutAfterEquation; exact Or.inl rfl
        · exact Or.inr ⟨_, WeakHeadStep.scrutineeFst weakHeadStep2,
            StepStar.congAt
              (fun hole => .mkGen .gen_fst () (.childCons hole .childNil))
              (fun childStep' => Step.cong .gen_fst () (.here _ childStep')) starChain⟩
  | @scrutineeSnd scrutinee scrutineeReduct scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      intro other step
      rcases Step.from_snd step with
        ⟨_firstValue, _secondValue, scrutEq, _⟩ | ⟨_scrutAfter, otherEq, scrutStep⟩
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_pair
      · subst otherEq
        rcases scrutineeInductiveHypothesis _ scrutStep with
          scrutAfterEquation | ⟨_scrutReduct2, weakHeadStep2, starChain⟩
        · subst scrutAfterEquation; exact Or.inl rfl
        · exact Or.inr ⟨_, WeakHeadStep.scrutineeSnd weakHeadStep2,
            StepStar.congAt
              (fun hole => .mkGen .gen_snd () (.childCons hole .childNil))
              (fun childStep' => Step.cong .gen_snd () (.here _ childStep')) starChain⟩
  | @scrutineeNatElim scrutinee scrutineeReduct zeroBranch succBranch
      scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      intro other step
      rcases Step.from_natElim step with
        ⟨scrutEq, _⟩ | ⟨_pred, scrutEq, _⟩
        | ⟨_scrutAfter, otherEq, scrutStep⟩
        | ⟨_zeroAfter, otherEq, zeroStep⟩
        | ⟨_succAfter, otherEq, succStep⟩
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_natZero
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_natSucc
      · subst otherEq
        rcases scrutineeInductiveHypothesis _ scrutStep with
          scrutAfterEquation | ⟨_scrutReduct2, weakHeadStep2, starChain⟩
        · subst scrutAfterEquation; exact Or.inl rfl
        · exact Or.inr ⟨_, WeakHeadStep.scrutineeNatElim weakHeadStep2,
            StepStar.congAt
              (fun hole => .mkGen .gen_natElim ()
                (.childCons hole (.childCons zeroBranch (.childCons succBranch .childNil))))
              (fun childStep' => Step.cong .gen_natElim () (.here _ childStep')) starChain⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeNatElim scrutineeWeakHeadStep,
          StepStar.congAt
            (fun hole => .mkGen .gen_natElim ()
              (.childCons scrutineeReduct (.childCons hole (.childCons succBranch .childNil))))
            (fun childStep' => Step.cong .gen_natElim () (.there _ (.here _ childStep')))
            (StepStar.single zeroStep)⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeNatElim scrutineeWeakHeadStep,
          StepStar.congAt
            (fun hole => .mkGen .gen_natElim ()
              (.childCons scrutineeReduct (.childCons zeroBranch (.childCons hole .childNil))))
            (fun childStep' => Step.cong .gen_natElim () (.there _ (.there _ (.here _ childStep'))))
            (StepStar.single succStep)⟩
  | @scrutineeNatRec scrutinee scrutineeReduct zeroBranch succBranch
      scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      intro other step
      rcases Step.from_natRec step with
        ⟨scrutEq, _⟩ | ⟨_pred, scrutEq, _⟩
        | ⟨_scrutAfter, otherEq, scrutStep⟩
        | ⟨_zeroAfter, otherEq, zeroStep⟩
        | ⟨_succAfter, otherEq, succStep⟩
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_natZero
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_natSucc
      · subst otherEq
        rcases scrutineeInductiveHypothesis _ scrutStep with
          scrutAfterEquation | ⟨_scrutReduct2, weakHeadStep2, starChain⟩
        · subst scrutAfterEquation; exact Or.inl rfl
        · exact Or.inr ⟨_, WeakHeadStep.scrutineeNatRec weakHeadStep2,
            StepStar.congAt
              (fun hole => .mkGen .gen_natRec ()
                (.childCons hole (.childCons zeroBranch (.childCons succBranch .childNil))))
              (fun childStep' => Step.cong .gen_natRec () (.here _ childStep')) starChain⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeNatRec scrutineeWeakHeadStep,
          StepStar.congAt
            (fun hole => .mkGen .gen_natRec ()
              (.childCons scrutineeReduct (.childCons hole (.childCons succBranch .childNil))))
            (fun childStep' => Step.cong .gen_natRec () (.there _ (.here _ childStep')))
            (StepStar.single zeroStep)⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeNatRec scrutineeWeakHeadStep,
          StepStar.congAt
            (fun hole => .mkGen .gen_natRec ()
              (.childCons scrutineeReduct (.childCons zeroBranch (.childCons hole .childNil))))
            (fun childStep' => Step.cong .gen_natRec () (.there _ (.there _ (.here _ childStep'))))
            (StepStar.single succStep)⟩
  | @scrutineeListElim motive scrutinee scrutineeReduct nilBranch consBranch
      scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      -- Phase-Z spine: (motive, nil, cons, scrutinee).  The WeakHeadStep reduces the LAST
      -- child (scrutinee).  `Step.from_listElim` is a six-way disjunction in the order
      -- iotaNil / iotaCons / cong-motive / cong-nil / cong-cons / cong-scrutinee.  The two
      -- iota disjuncts are refuted (a reducible scrutinee is not yet a constructor); motive,
      -- nil, and cons steps leave the scrutinee reducible, so `other` still weak-head reduces
      -- there and `reduct` catches up by a single congruence at the stepped child; a scrutinee
      -- step recurses through the induction hypothesis.
      intro other step
      rcases Step.from_listElim step with
        ⟨scrutEq, _⟩ | ⟨_headVal, _tailVal, scrutEq, _⟩
        | ⟨_motiveAfter, otherEq, motiveStep⟩
        | ⟨_nilAfter, otherEq, nilStep⟩
        | ⟨_consAfter, otherEq, consStep⟩
        | ⟨_scrutAfter, otherEq, scrutStep⟩
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_listNil
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_listCons
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeListElim scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_listElim () (.here _ motiveStep))⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeListElim scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_listElim () (.there _ (.here _ nilStep)))⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeListElim scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_listElim () (.there _ (.there _ (.here _ consStep))))⟩
      · subst otherEq
        rcases scrutineeInductiveHypothesis _ scrutStep with
          scrutAfterEquation | ⟨_scrutReduct2, weakHeadStep2, starChain⟩
        · subst scrutAfterEquation; exact Or.inl rfl
        · exact Or.inr ⟨_, WeakHeadStep.scrutineeListElim weakHeadStep2,
            StepStar.congAt
              (fun hole => .mkGen .gen_listElim ()
                (.childCons motive
                  (.childCons nilBranch (.childCons consBranch (.childCons hole .childNil)))))
              (fun childStep' =>
                Step.cong .gen_listElim ()
                  (.there _ (.there _ (.there _ (.here _ childStep'))))) starChain⟩
  | @scrutineeOptionMatch scrutinee scrutineeReduct noneBranch someBranch
      scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      intro other step
      rcases Step.from_optionMatch step with
        ⟨scrutEq, _⟩ | ⟨_value, scrutEq, _⟩
        | ⟨_scrutAfter, otherEq, scrutStep⟩
        | ⟨_noneAfter, otherEq, noneStep⟩
        | ⟨_someAfter, otherEq, someStep⟩
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_optionNone
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_optionSome
      · subst otherEq
        rcases scrutineeInductiveHypothesis _ scrutStep with
          scrutAfterEquation | ⟨_scrutReduct2, weakHeadStep2, starChain⟩
        · subst scrutAfterEquation; exact Or.inl rfl
        · exact Or.inr ⟨_, WeakHeadStep.scrutineeOptionMatch weakHeadStep2,
            StepStar.congAt
              (fun hole => .mkGen .gen_optionMatch ()
                (.childCons hole (.childCons noneBranch (.childCons someBranch .childNil))))
              (fun childStep' => Step.cong .gen_optionMatch () (.here _ childStep')) starChain⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeOptionMatch scrutineeWeakHeadStep,
          StepStar.congAt
            (fun hole => .mkGen .gen_optionMatch ()
              (.childCons scrutineeReduct (.childCons hole (.childCons someBranch .childNil))))
            (fun childStep' => Step.cong .gen_optionMatch () (.there _ (.here _ childStep')))
            (StepStar.single noneStep)⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeOptionMatch scrutineeWeakHeadStep,
          StepStar.congAt
            (fun hole => .mkGen .gen_optionMatch ()
              (.childCons scrutineeReduct (.childCons noneBranch (.childCons hole .childNil))))
            (fun childStep' => Step.cong .gen_optionMatch () (.there _ (.there _ (.here _ childStep'))))
            (StepStar.single someStep)⟩
  | @scrutineeEitherMatch scrutinee scrutineeReduct leftBranch rightBranch
      scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      intro other step
      rcases Step.from_eitherMatch step with
        ⟨_value, scrutEq, _⟩ | ⟨_value, scrutEq, _⟩
        | ⟨_scrutAfter, otherEq, scrutStep⟩
        | ⟨_leftAfter, otherEq, leftStep⟩
        | ⟨_rightAfter, otherEq, rightStep⟩
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_eitherInl
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_eitherInr
      · subst otherEq
        rcases scrutineeInductiveHypothesis _ scrutStep with
          scrutAfterEquation | ⟨_scrutReduct2, weakHeadStep2, starChain⟩
        · subst scrutAfterEquation; exact Or.inl rfl
        · exact Or.inr ⟨_, WeakHeadStep.scrutineeEitherMatch weakHeadStep2,
            StepStar.congAt
              (fun hole => .mkGen .gen_eitherMatch ()
                (.childCons hole (.childCons leftBranch (.childCons rightBranch .childNil))))
              (fun childStep' => Step.cong .gen_eitherMatch () (.here _ childStep')) starChain⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeEitherMatch scrutineeWeakHeadStep,
          StepStar.congAt
            (fun hole => .mkGen .gen_eitherMatch ()
              (.childCons scrutineeReduct (.childCons hole (.childCons rightBranch .childNil))))
            (fun childStep' => Step.cong .gen_eitherMatch () (.there _ (.here _ childStep')))
            (StepStar.single leftStep)⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeEitherMatch scrutineeWeakHeadStep,
          StepStar.congAt
            (fun hole => .mkGen .gen_eitherMatch ()
              (.childCons scrutineeReduct (.childCons leftBranch (.childCons hole .childNil))))
            (fun childStep' => Step.cong .gen_eitherMatch () (.there _ (.there _ (.here _ childStep'))))
            (StepStar.single rightStep)⟩
  | @scrutineeIdJ baseCase scrutinee scrutineeReduct
      scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      intro other step
      rcases Step.from_idJ step with
        ⟨_rawWitness, scrutEq, _⟩
        | ⟨_baseAfter, otherEq, baseStep⟩
        | ⟨_witnessAfter, otherEq, witnessStep⟩
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_refl
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeIdJ scrutineeWeakHeadStep,
          StepStar.congAt
            (fun hole => .mkGen .gen_idJ () (.childCons hole (.childCons scrutineeReduct .childNil)))
            (fun childStep' => Step.cong .gen_idJ () (.here _ childStep'))
            (StepStar.single baseStep)⟩
      · subst otherEq
        rcases scrutineeInductiveHypothesis _ witnessStep with
          scrutAfterEquation | ⟨_scrutReduct2, weakHeadStep2, starChain⟩
        · subst scrutAfterEquation; exact Or.inl rfl
        · exact Or.inr ⟨_, WeakHeadStep.scrutineeIdJ weakHeadStep2,
            StepStar.congAt
              (fun hole => .mkGen .gen_idJ () (.childCons baseCase (.childCons hole .childNil)))
              (fun childStep' => Step.cong .gen_idJ () (.there _ (.here _ childStep'))) starChain⟩
  | @scrutineeIdStrictRec baseCase scrutinee scrutineeReduct
      scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      intro other step
      rcases Step.from_idStrictRec step with
        ⟨_rawWitness, scrutEq, _⟩
        | ⟨_baseAfter, otherEq, baseStep⟩
        | ⟨_witnessAfter, otherEq, witnessStep⟩
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_refl
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeIdStrictRec scrutineeWeakHeadStep,
          StepStar.congAt
            (fun hole => .mkGen .gen_idStrictRec ()
              (.childCons hole (.childCons scrutineeReduct .childNil)))
            (fun childStep' => Step.cong .gen_idStrictRec () (.here _ childStep'))
            (StepStar.single baseStep)⟩
      · subst otherEq
        rcases scrutineeInductiveHypothesis _ witnessStep with
          scrutAfterEquation | ⟨_scrutReduct2, weakHeadStep2, starChain⟩
        · subst scrutAfterEquation; exact Or.inl rfl
        · exact Or.inr ⟨_, WeakHeadStep.scrutineeIdStrictRec weakHeadStep2,
            StepStar.congAt
              (fun hole => .mkGen .gen_idStrictRec ()
                (.childCons baseCase (.childCons hole .childNil)))
              (fun childStep' => Step.cong .gen_idStrictRec () (.there _ (.here _ childStep'))) starChain⟩

end FX1Poly.Core
