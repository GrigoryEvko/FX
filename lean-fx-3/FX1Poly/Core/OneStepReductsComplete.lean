import FX1Poly.Core.OneStepReducts

/-! # FX1Poly/Core/OneStepReductsComplete
    — enumeration COMPLETENESS: every kernel Step is listed (COST-3 brick 3)

The hard half of the reduct enumeration: every `Step` lands in
`oneStepReducts`.  By mutual induction on the `Step`/`StepChildren`
derivation:

  * the 17 ROOT arms (β + 16 ι) each close by ONE proof shape — the
    redex-shaped source makes `fireRootRedex` REDUCE DEFINITIONALLY to
    `some` of the constructor's reduct (the dite chain decides the
    literal generator tags; the children matches destructure the
    concrete constructor spine; symbolic leaves flow through), so the
    root part of the enumeration is the singleton and membership is
    `head` in the left append component;
  * the CONG arm maps the spine IH through the reassembly
    (`listMemMapOfMem`) into the right append component;
  * the spine arms (`here`/`there`) mirror into the head-map and
    tail-map components.

With brick 2's soundness this yields the CHARACTERIZATION
`step_iff_mem_oneStepReducts`: the computable enumeration decides
exactly the `Step` relation — the substrate the worst-case `costBound`
(next brick) folds over.

Forward membership lemmas (`listMemAppendLeft`/`Right`,
`listMemMapOfMem`) are hand-rolled generic, completing the inversion
trio from brick 2.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Core

open Foundation

/-! ## Generic forward membership (hand-rolled, explicit `List.Mem`) -/

/-- Left-component membership survives an append. -/
theorem listMemAppendLeft {alpha : Type} {element : alpha} :
    ∀ (firstList secondList : List alpha), element ∈ firstList →
      element ∈ firstList ++ secondList
  | [], _, memEmpty => nomatch memEmpty
  | listHead :: rest, secondList, memFirst => by
      cases memFirst with
      | head => exact List.Mem.head (rest ++ secondList)
      | tail _ memRest =>
          exact List.Mem.tail listHead (listMemAppendLeft rest secondList memRest)

/-- Right-component membership survives an append. -/
theorem listMemAppendRight {alpha : Type} {element : alpha} :
    ∀ (firstList secondList : List alpha), element ∈ secondList →
      element ∈ firstList ++ secondList
  | [], _, memSecond => memSecond
  | listHead :: rest, secondList, memSecond =>
      List.Mem.tail listHead (listMemAppendRight rest secondList memSecond)

/-- Membership maps forward through `List.map`. -/
theorem listMemMapOfMem {alpha beta : Type} (mapped : alpha → beta) {element : alpha} :
    ∀ (sourceList : List alpha), element ∈ sourceList →
      mapped element ∈ sourceList.map mapped
  | [], memEmpty => nomatch memEmpty
  | listHead :: rest, memSource => by
      cases memSource with
      | head => exact List.Mem.head (rest.map mapped)
      | tail _ memRest =>
          exact List.Mem.tail (mapped listHead) (listMemMapOfMem mapped rest memRest)

/-! ## ★ Completeness — every Step is listed -/

mutual
  /-- ★ **Enumeration completeness**: every `Step` reduct is listed.  The
  17 root arms share one proof shape — the redex-shaped source computes
  `fireRootRedex` to the constructor's reduct definitionally, so the
  reduct is the head of the left append component.  The cong arm maps
  the spine IH through the reassembly into the right component. -/
  theorem RawTerm.oneStepReducts_complete :
      ∀ {scope : Nat} {term reduct : RawTerm scope},
        Step term reduct → reduct ∈ RawTerm.oneStepReducts term
    | _, _, _, .beta .. => listMemAppendLeft _ _ (List.Mem.head _)
    | _, _, _, .cong _ _ childStep =>
        listMemAppendRight _ _
          (listMemMapOfMem _ _
            (RawTermChildren.oneStepChildrenReducts_complete childStep))
    | _, _, _, .iotaBoolTrue .. => listMemAppendLeft _ _ (List.Mem.head _)
    | _, _, _, .iotaBoolFalse .. => listMemAppendLeft _ _ (List.Mem.head _)
    | _, _, _, .iotaFstPair .. => listMemAppendLeft _ _ (List.Mem.head _)
    | _, _, _, .iotaSndPair .. => listMemAppendLeft _ _ (List.Mem.head _)
    | _, _, _, .iotaNatElimZero .. => listMemAppendLeft _ _ (List.Mem.head _)
    | _, _, _, .iotaNatRecZero .. => listMemAppendLeft _ _ (List.Mem.head _)
    | _, _, _, .iotaListElimNil .. => listMemAppendLeft _ _ (List.Mem.head _)
    | _, _, _, .iotaOptionMatchNone .. => listMemAppendLeft _ _ (List.Mem.head _)
    | _, _, _, .iotaOptionMatchSome .. => listMemAppendLeft _ _ (List.Mem.head _)
    | _, _, _, .iotaEitherMatchInl .. => listMemAppendLeft _ _ (List.Mem.head _)
    | _, _, _, .iotaEitherMatchInr .. => listMemAppendLeft _ _ (List.Mem.head _)
    | _, _, _, .iotaNatElimSucc .. => listMemAppendLeft _ _ (List.Mem.head _)
    | _, _, _, .iotaNatRecSucc .. => listMemAppendLeft _ _ (List.Mem.head _)
    | _, _, _, .iotaListElimCons .. => listMemAppendLeft _ _ (List.Mem.head _)
    | _, _, _, .iotaIdJRefl .. => listMemAppendLeft _ _ (List.Mem.head _)
    | _, _, _, .iotaIdStrictRecRefl .. => listMemAppendLeft _ _ (List.Mem.head _)

  /-- Spine completeness: a head step lands in the head-map component, a
  tail step in the tail-map component. -/
  theorem RawTermChildren.oneStepChildrenReducts_complete :
      ∀ {binderShifts : List Nat} {parentScope : Nat}
        {children steppedSpine : RawTermChildren binderShifts parentScope},
        StepChildren children steppedSpine →
        steppedSpine ∈ RawTermChildren.oneStepChildrenReducts children
    | _, _, _, _, .here rest childStep =>
        listMemAppendLeft _ _
          (listMemMapOfMem _ _ (RawTerm.oneStepReducts_complete childStep))
    | _, _, _, _, .there head restStep =>
        listMemAppendRight _ _
          (listMemMapOfMem _ _
            (RawTermChildren.oneStepChildrenReducts_complete restStep))
end

/-! ## ★ The characterization — the enumeration decides Step -/

/-- ★ **The enumeration characterizes one-step reduction**: a term steps
to exactly the members of its computable reduct list — soundness
(brick 2) and completeness in one biconditional.  This is the substrate
the worst-case `costBound` folds over: the fold's recursive calls are
justified by soundness, and its bound covers EVERY strategy by
completeness. -/
theorem RawTerm.step_iff_mem_oneStepReducts {scope : Nat}
    {term reduct : RawTerm scope} :
    Step term reduct ↔ reduct ∈ RawTerm.oneStepReducts term :=
  ⟨RawTerm.oneStepReducts_complete, RawTerm.oneStepReducts_sound term⟩

end FX1Poly.Core
