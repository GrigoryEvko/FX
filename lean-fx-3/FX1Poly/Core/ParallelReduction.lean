import FX1Poly.Core.Step
import FX1Poly.Core.RawTermSubst0
import FX1Poly.Core.StepSubst

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

mutual
  /-- **`ParStep ⊆ StepStar`** (the upper sandwich bound, `parToStepStar` for
  `StepStar.hasConfluence_of_parallelDiamond`): every parallel reduction is a finite sequence of single
  reductions.  Each arm reduces the redex's surviving sub-terms via `StepStar.ofChildrenStar` (the
  child-spine congruence lifter) — recursively through `ParStep.toStepStar` — then fires the matching root
  `Step`: `beta` reduces `body`/`arg` under `lam`/`app` then `Step.beta`; the branch-selection ι reduce
  the selected branch then fire; the app-chain ι (`some`/`inl`/`inr`) reduce the branch under the match,
  fire, then reduce the wrapped value under the resulting `app`; the recursive `succ`/`cons` ι reduce
  predecessor/head/tail + branches under the eliminator then fire (the reduct is exactly the fired
  all-reduced redex).  `cong` lifts the pointwise `ParStepChildren` to a `StepStar` through
  `ofChildrenStar`. -/
  theorem ParStep.toStepStar {scope : Nat} {a b : RawTerm scope} : ParStep a b → StepStar a b
    | .beta bodyPar argPar =>
        StepStar.transLast
          (StepStar.ofChildrenStar
            (StepChildrenStar.trans_compose
              (StepChildrenStar.here _
                (StepStar.ofChildrenStar (StepChildrenStar.here _ (ParStep.toStepStar bodyPar))))
              (StepChildrenStar.there _
                (StepChildrenStar.here _ (ParStep.toStepStar argPar)))))
          Step.beta
    | .cong _gen _payload childrenPar =>
        StepStar.ofChildrenStar (ParStepChildren.toStepChildrenStar childrenPar)
    | .iotaBoolTrue thenPar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.there _ (StepChildrenStar.here _ (ParStep.toStepStar thenPar))))
          Step.iotaBoolTrue
    | .iotaBoolFalse elsePar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.there _ (StepChildrenStar.there _
            (StepChildrenStar.here _ (ParStep.toStepStar elsePar)))))
          Step.iotaBoolFalse
    | .iotaFstPair firstPar =>
        StepStar.transLast (StepStar.ofChildrenStar (StepChildrenStar.here _
          (StepStar.ofChildrenStar (StepChildrenStar.here _ (ParStep.toStepStar firstPar)))))
          Step.iotaFstPair
    | .iotaSndPair secondPar =>
        StepStar.transLast (StepStar.ofChildrenStar (StepChildrenStar.here _
          (StepStar.ofChildrenStar (StepChildrenStar.there _
            (StepChildrenStar.here _ (ParStep.toStepStar secondPar))))))
          Step.iotaSndPair
    | .iotaNatElimZero zeroPar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.there _ (StepChildrenStar.here _ (ParStep.toStepStar zeroPar))))
          Step.iotaNatElimZero
    | .iotaNatRecZero zeroPar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.there _ (StepChildrenStar.here _ (ParStep.toStepStar zeroPar))))
          Step.iotaNatRecZero
    | .iotaListElimNil nilPar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.there _ (StepChildrenStar.here _ (ParStep.toStepStar nilPar))))
          Step.iotaListElimNil
    | .iotaOptionMatchNone nonePar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.there _ (StepChildrenStar.here _ (ParStep.toStepStar nonePar))))
          Step.iotaOptionMatchNone
    | .iotaOptionMatchSome somePar valuePar =>
        StepStar.trans_compose
          (StepStar.ofChildrenStar (StepChildrenStar.there _ (StepChildrenStar.there _
            (StepChildrenStar.here _ (ParStep.toStepStar somePar)))))
          (StepStar.trans Step.iotaOptionMatchSome
            (StepStar.ofChildrenStar (StepChildrenStar.there _
              (StepChildrenStar.here _ (ParStep.toStepStar valuePar)))))
    | .iotaEitherMatchInl leftPar valuePar =>
        StepStar.trans_compose
          (StepStar.ofChildrenStar (StepChildrenStar.there _ (StepChildrenStar.here _
            (ParStep.toStepStar leftPar))))
          (StepStar.trans Step.iotaEitherMatchInl
            (StepStar.ofChildrenStar (StepChildrenStar.there _
              (StepChildrenStar.here _ (ParStep.toStepStar valuePar)))))
    | .iotaEitherMatchInr rightPar valuePar =>
        StepStar.trans_compose
          (StepStar.ofChildrenStar (StepChildrenStar.there _ (StepChildrenStar.there _
            (StepChildrenStar.here _ (ParStep.toStepStar rightPar)))))
          (StepStar.trans Step.iotaEitherMatchInr
            (StepStar.ofChildrenStar (StepChildrenStar.there _
              (StepChildrenStar.here _ (ParStep.toStepStar valuePar)))))
    | .iotaNatElimSucc predPar zeroPar succPar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.trans_compose
            (StepChildrenStar.here _
              (StepStar.ofChildrenStar (StepChildrenStar.here _ (ParStep.toStepStar predPar))))
            (StepChildrenStar.trans_compose
              (StepChildrenStar.there _ (StepChildrenStar.here _ (ParStep.toStepStar zeroPar)))
              (StepChildrenStar.there _ (StepChildrenStar.there _
                (StepChildrenStar.here _ (ParStep.toStepStar succPar)))))))
          Step.iotaNatElimSucc
    | .iotaNatRecSucc predPar zeroPar succPar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.trans_compose
            (StepChildrenStar.here _
              (StepStar.ofChildrenStar (StepChildrenStar.here _ (ParStep.toStepStar predPar))))
            (StepChildrenStar.trans_compose
              (StepChildrenStar.there _ (StepChildrenStar.here _ (ParStep.toStepStar zeroPar)))
              (StepChildrenStar.there _ (StepChildrenStar.there _
                (StepChildrenStar.here _ (ParStep.toStepStar succPar)))))))
          Step.iotaNatRecSucc
    | .iotaListElimCons headPar tailPar nilPar consPar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.trans_compose
            (StepChildrenStar.here _
              (StepStar.ofChildrenStar (StepChildrenStar.here _ (ParStep.toStepStar headPar))))
            (StepChildrenStar.trans_compose
              (StepChildrenStar.here _
                (StepStar.ofChildrenStar (StepChildrenStar.there _
                  (StepChildrenStar.here _ (ParStep.toStepStar tailPar)))))
              (StepChildrenStar.trans_compose
                (StepChildrenStar.there _ (StepChildrenStar.here _ (ParStep.toStepStar nilPar)))
                (StepChildrenStar.there _ (StepChildrenStar.there _
                  (StepChildrenStar.here _ (ParStep.toStepStar consPar))))))))
          Step.iotaListElimCons
    | .iotaIdJRefl basePar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.here _ (ParStep.toStepStar basePar)))
          Step.iotaIdJRefl
    | .iotaIdStrictRecRefl basePar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.here _ (ParStep.toStepStar basePar)))
          Step.iotaIdStrictRecRefl
  /-- **`ParStepChildren ⊆ StepChildrenStar`** (the spine companion of `ParStep.toStepStar`): a pointwise
  parallel children reduction is a finite sequence of single child-spine steps — reduce the head (via
  `ParStep.toStepStar`), then the tail (recursive call), composing with `trans_compose`. -/
  theorem ParStepChildren.toStepChildrenStar {binderShifts : List Nat} {scope : Nat}
      {children children' : RawTermChildren binderShifts scope} :
      ParStepChildren children children' → StepChildrenStar children children'
    | .nil => StepChildrenStar.refl _
    | .cons headPar tailPar =>
        StepChildrenStar.trans_compose
          (StepChildrenStar.here _ (ParStep.toStepStar headPar))
          (StepChildrenStar.there _ (ParStepChildren.toStepChildrenStar tailPar))
end

end FX1Poly.Core
