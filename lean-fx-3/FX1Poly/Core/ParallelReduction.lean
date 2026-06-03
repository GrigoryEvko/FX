import FX1Poly.Core.Step
import FX1Poly.Core.RawTermSubst0

/-! # FX1Poly/Core/ParallelReduction
    — the FX parallel reduction relation + reflexivity (toward the Takahashi diamond / raw confluence, #420)

`StepParallelConfluence.lean` reduces raw confluence to exhibiting a parallel reduction sandwiched
`Step ⊆ ParStep ⊆ StepStar` whose `DiamondProperty` holds, and `TakahashiTriangle.lean` reduces THAT
diamond to "every term has a maximal parallel reduct" (`Confluent.ofMaximalReduct`).  This file ships the
concrete parallel reduction itself — the relation that contracts ANY set of redexes simultaneously,
following Tait/Martin-Löf/Takahashi.

`ParStep` mirrors every `Step` rule but reduces the SURVIVING sub-terms in parallel:

* `beta` — contracts `app (lam body) arg` to `subst0 body' arg'` with `body`, `arg` reduced in parallel;
* `cong` — one uniform congruence over the children spine via the pointwise `ParStepChildren` (this is
  also the source of reflexivity: every `mkGen` cell parallel-reduces to itself by congruence over the
  reflexively-reduced children);
* the 16 ι arms — each fires the eliminator AND reduces the components that survive into the reduct in
  parallel (branch-selection ι reduce the selected branch; the app-chain ι reduce the branch + payload;
  the recursive `succ`/`cons` ι reduce predecessor/head/tail + branches and re-form the recursive
  eliminator on the reduced sub-terms).

`ParStepChildren` is the POINTWISE parallel reduction of a children spine (every child reduces at once) —
distinct from `StepChildren` (which picks ONE child).  That pointwise shape is exactly what the diamond
needs.

This tick ships the inductive + reflexivity (`ParStep.refl` / `ParStepChildren.refl`, by mutual structural
recursion).  The sandwiching (`Step ⊆ ParStep ⊆ StepStar`), the maximal-reduct existence, and the diamond
follow in subsequent increments — each feeding the shipped `Confluent.ofMaximalReduct` toward
UNCONDITIONAL raw confluence (the prize strong normalization cannot supply, since raw β+ι is not SN).

## Zero-axiom verification

Two mutual inductives plus a mutual reflexivity proof by term-mode pattern-matching (full-enumeration,
non-overlapping `mkGen` / `childNil` / `childCons` patterns — structural recursion, no `termination_by`,
avoiding the v4.29.1 well-founded substitution gap documented in `CertifyRawCellExact.lean`).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

mutual
  /-- **Parallel reduction** — contract any set of redexes simultaneously (Tait/Martin-Löf/Takahashi).
  Mirrors every `Step` rule but reduces the surviving sub-terms in parallel; the source of the
  `DiamondProperty` the raw-confluence proof needs. -/
  inductive ParStep : {scope : Nat} → RawTerm scope → RawTerm scope → Prop where
    | beta {scope : Nat} {body body' : RawTerm (scope + 1)} {arg arg' : RawTerm scope} :
        ParStep body body' → ParStep arg arg' →
        ParStep (.mkGen .gen_app () (.childCons (.mkGen .gen_lam () (.childCons body .childNil))
            (.childCons arg .childNil))) (RawTerm.subst0 body' arg')
    | cong {scope : Nat} (gen : Generator) (payload : gen.payload scope)
           {children children' : RawTermChildren gen.binderShifts scope} :
        ParStepChildren children children' →
        ParStep (.mkGen gen payload children) (.mkGen gen payload children')
    | iotaBoolTrue {scope : Nat} {thenBranch thenBranch' elseBranch : RawTerm scope} :
        ParStep thenBranch thenBranch' →
        ParStep (.mkGen .gen_boolElim () (.childCons (.mkGen .gen_boolTrue () .childNil)
            (.childCons thenBranch (.childCons elseBranch .childNil)))) thenBranch'
    | iotaBoolFalse {scope : Nat} {thenBranch elseBranch elseBranch' : RawTerm scope} :
        ParStep elseBranch elseBranch' →
        ParStep (.mkGen .gen_boolElim () (.childCons (.mkGen .gen_boolFalse () .childNil)
            (.childCons thenBranch (.childCons elseBranch .childNil)))) elseBranch'
    | iotaFstPair {scope : Nat} {firstValue firstValue' secondValue : RawTerm scope} :
        ParStep firstValue firstValue' →
        ParStep (.mkGen .gen_fst () (.childCons (.mkGen .gen_pair ()
            (.childCons firstValue (.childCons secondValue .childNil))) .childNil)) firstValue'
    | iotaSndPair {scope : Nat} {firstValue secondValue secondValue' : RawTerm scope} :
        ParStep secondValue secondValue' →
        ParStep (.mkGen .gen_snd () (.childCons (.mkGen .gen_pair ()
            (.childCons firstValue (.childCons secondValue .childNil))) .childNil)) secondValue'
    | iotaNatElimZero {scope : Nat} {zeroBranch zeroBranch' succBranch : RawTerm scope} :
        ParStep zeroBranch zeroBranch' →
        ParStep (.mkGen .gen_natElim () (.childCons (.mkGen .gen_natZero () .childNil)
            (.childCons zeroBranch (.childCons succBranch .childNil)))) zeroBranch'
    | iotaNatRecZero {scope : Nat} {zeroBranch zeroBranch' succBranch : RawTerm scope} :
        ParStep zeroBranch zeroBranch' →
        ParStep (.mkGen .gen_natRec () (.childCons (.mkGen .gen_natZero () .childNil)
            (.childCons zeroBranch (.childCons succBranch .childNil)))) zeroBranch'
    | iotaListElimNil {scope : Nat} {nilBranch nilBranch' consBranch : RawTerm scope} :
        ParStep nilBranch nilBranch' →
        ParStep (.mkGen .gen_listElim () (.childCons (.mkGen .gen_listNil () .childNil)
            (.childCons nilBranch (.childCons consBranch .childNil)))) nilBranch'
    | iotaOptionMatchNone {scope : Nat} {noneBranch noneBranch' someBranch : RawTerm scope} :
        ParStep noneBranch noneBranch' →
        ParStep (.mkGen .gen_optionMatch () (.childCons (.mkGen .gen_optionNone () .childNil)
            (.childCons noneBranch (.childCons someBranch .childNil)))) noneBranch'
    | iotaOptionMatchSome {scope : Nat} {value value' noneBranch someBranch someBranch' : RawTerm scope} :
        ParStep someBranch someBranch' → ParStep value value' →
        ParStep (.mkGen .gen_optionMatch () (.childCons
            (.mkGen .gen_optionSome () (.childCons value .childNil))
            (.childCons noneBranch (.childCons someBranch .childNil))))
          (.mkGen .gen_app () (.childCons someBranch' (.childCons value' .childNil)))
    | iotaEitherMatchInl {scope : Nat} {value value' leftBranch leftBranch' rightBranch : RawTerm scope} :
        ParStep leftBranch leftBranch' → ParStep value value' →
        ParStep (.mkGen .gen_eitherMatch () (.childCons
            (.mkGen .gen_eitherInl () (.childCons value .childNil))
            (.childCons leftBranch (.childCons rightBranch .childNil))))
          (.mkGen .gen_app () (.childCons leftBranch' (.childCons value' .childNil)))
    | iotaEitherMatchInr {scope : Nat} {value value' leftBranch rightBranch rightBranch' : RawTerm scope} :
        ParStep rightBranch rightBranch' → ParStep value value' →
        ParStep (.mkGen .gen_eitherMatch () (.childCons
            (.mkGen .gen_eitherInr () (.childCons value .childNil))
            (.childCons leftBranch (.childCons rightBranch .childNil))))
          (.mkGen .gen_app () (.childCons rightBranch' (.childCons value' .childNil)))
    | iotaNatElimSucc {scope : Nat}
        {predecessor predecessor' zeroBranch zeroBranch' succBranch succBranch' : RawTerm scope} :
        ParStep predecessor predecessor' → ParStep zeroBranch zeroBranch' → ParStep succBranch succBranch' →
        ParStep (.mkGen .gen_natElim () (.childCons
            (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
            (.childCons zeroBranch (.childCons succBranch .childNil))))
          (.mkGen .gen_app () (.childCons
            (.mkGen .gen_app () (.childCons succBranch' (.childCons predecessor' .childNil)))
            (.childCons (.mkGen .gen_natElim () (.childCons predecessor'
                (.childCons zeroBranch' (.childCons succBranch' .childNil)))) .childNil)))
    | iotaNatRecSucc {scope : Nat}
        {predecessor predecessor' zeroBranch zeroBranch' succBranch succBranch' : RawTerm scope} :
        ParStep predecessor predecessor' → ParStep zeroBranch zeroBranch' → ParStep succBranch succBranch' →
        ParStep (.mkGen .gen_natRec () (.childCons
            (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
            (.childCons zeroBranch (.childCons succBranch .childNil))))
          (.mkGen .gen_app () (.childCons
            (.mkGen .gen_app () (.childCons succBranch' (.childCons predecessor' .childNil)))
            (.childCons (.mkGen .gen_natRec () (.childCons predecessor'
                (.childCons zeroBranch' (.childCons succBranch' .childNil)))) .childNil)))
    | iotaListElimCons {scope : Nat}
        {headVal headVal' tailVal tailVal' nilBranch nilBranch' consBranch consBranch' : RawTerm scope} :
        ParStep headVal headVal' → ParStep tailVal tailVal' →
        ParStep nilBranch nilBranch' → ParStep consBranch consBranch' →
        ParStep (.mkGen .gen_listElim () (.childCons
            (.mkGen .gen_listCons () (.childCons headVal (.childCons tailVal .childNil)))
            (.childCons nilBranch (.childCons consBranch .childNil))))
          (.mkGen .gen_app () (.childCons
            (.mkGen .gen_app () (.childCons
              (.mkGen .gen_app () (.childCons consBranch' (.childCons headVal' .childNil)))
              (.childCons tailVal' .childNil)))
            (.childCons (.mkGen .gen_listElim () (.childCons tailVal'
                (.childCons nilBranch' (.childCons consBranch' .childNil)))) .childNil)))
    | iotaIdJRefl {scope : Nat} {baseCase baseCase' rawWitness : RawTerm scope} :
        ParStep baseCase baseCase' →
        ParStep (.mkGen .gen_idJ () (.childCons baseCase
            (.childCons (.mkGen .gen_refl () (.childCons rawWitness .childNil)) .childNil))) baseCase'
    | iotaIdStrictRecRefl {scope : Nat} {baseCase baseCase' rawWitness : RawTerm scope} :
        ParStep baseCase baseCase' →
        ParStep (.mkGen .gen_idStrictRec () (.childCons baseCase
            (.childCons (.mkGen .gen_refl () (.childCons rawWitness .childNil)) .childNil))) baseCase'
  /-- **Pointwise parallel reduction of a children spine** — every child reduces simultaneously (distinct
  from `StepChildren`, which steps ONE child).  The shape the diamond argument needs. -/
  inductive ParStepChildren :
      {binderShifts : List Nat} → {scope : Nat} →
      RawTermChildren binderShifts scope → RawTermChildren binderShifts scope → Prop where
    | nil {scope : Nat} : ParStepChildren (scope := scope) .childNil .childNil
    | cons {scope : Nat} {shift : Nat} {shifts : List Nat}
        {childHead childHead' : RawTerm (scope + shift)}
        {childTail childTail' : RawTermChildren shifts scope} :
        ParStep childHead childHead' → ParStepChildren childTail childTail' →
        ParStepChildren (.childCons childHead childTail) (.childCons childHead' childTail')
end

mutual
  /-- **Reflexivity of parallel reduction** — every term parallel-reduces to itself, by congruence over the
  reflexively-reduced children spine.  Proved by mutual structural recursion (term-mode match). -/
  theorem ParStep.refl {scope : Nat} : (term : RawTerm scope) → ParStep term term
    | .mkGen gen payload children => ParStep.cong gen payload (ParStepChildren.refl children)
  /-- **Reflexivity of pointwise children parallel reduction** — every spine parallel-reduces to itself. -/
  theorem ParStepChildren.refl {binderShifts : List Nat} {scope : Nat} :
      (children : RawTermChildren binderShifts scope) → ParStepChildren children children
    | .childNil => ParStepChildren.nil
    | .childCons head tail => ParStepChildren.cons (ParStep.refl head) (ParStepChildren.refl tail)
end

mutual
  /-- **`Step ⊆ ParStep`** (the lower sandwich bound, `stepToPar` for
  `StepStar.hasConfluence_of_parallelDiamond`): every single reduction is a parallel reduction firing ONLY
  that redex, leaving the sub-terms reflexive.  Each `Step` arm maps to the matching `ParStep` arm with
  `ParStep.refl` on every surviving component; `cong` maps the single-child `StepChildren` to a pointwise
  `ParStepChildren` (the stepping child via the recursive call, the rest reflexive). -/
  theorem Step.toParStep {scope : Nat} {a b : RawTerm scope} : Step a b → ParStep a b
    | .beta => ParStep.beta (ParStep.refl _) (ParStep.refl _)
    | .cong gen payload childStep => ParStep.cong gen payload (StepChildren.toParStepChildren childStep)
    | .iotaBoolTrue => ParStep.iotaBoolTrue (ParStep.refl _)
    | .iotaBoolFalse => ParStep.iotaBoolFalse (ParStep.refl _)
    | .iotaFstPair => ParStep.iotaFstPair (ParStep.refl _)
    | .iotaSndPair => ParStep.iotaSndPair (ParStep.refl _)
    | .iotaNatElimZero => ParStep.iotaNatElimZero (ParStep.refl _)
    | .iotaNatRecZero => ParStep.iotaNatRecZero (ParStep.refl _)
    | .iotaListElimNil => ParStep.iotaListElimNil (ParStep.refl _)
    | .iotaOptionMatchNone => ParStep.iotaOptionMatchNone (ParStep.refl _)
    | .iotaOptionMatchSome => ParStep.iotaOptionMatchSome (ParStep.refl _) (ParStep.refl _)
    | .iotaEitherMatchInl => ParStep.iotaEitherMatchInl (ParStep.refl _) (ParStep.refl _)
    | .iotaEitherMatchInr => ParStep.iotaEitherMatchInr (ParStep.refl _) (ParStep.refl _)
    | .iotaNatElimSucc => ParStep.iotaNatElimSucc (ParStep.refl _) (ParStep.refl _) (ParStep.refl _)
    | .iotaNatRecSucc => ParStep.iotaNatRecSucc (ParStep.refl _) (ParStep.refl _) (ParStep.refl _)
    | .iotaListElimCons =>
        ParStep.iotaListElimCons (ParStep.refl _) (ParStep.refl _) (ParStep.refl _) (ParStep.refl _)
    | .iotaIdJRefl => ParStep.iotaIdJRefl (ParStep.refl _)
    | .iotaIdStrictRecRefl => ParStep.iotaIdStrictRecRefl (ParStep.refl _)
  /-- **`StepChildren ⊆ ParStepChildren`** (the spine companion of `Step.toParStep`): a single-child step
  lifts to a pointwise parallel reduction — the stepping child parallel-reduces (recursive call), the
  other children stay reflexive. -/
  theorem StepChildren.toParStepChildren {parentScope : Nat} {binderShifts : List Nat}
      {children children' : RawTermChildren binderShifts parentScope} :
      StepChildren children children' → ParStepChildren children children'
    | .here rest childStep =>
        ParStepChildren.cons (Step.toParStep childStep) (ParStepChildren.refl rest)
    | .there head restStep =>
        ParStepChildren.cons (ParStep.refl head) (StepChildren.toParStepChildren restStep)
end

end FX1Poly.Core
