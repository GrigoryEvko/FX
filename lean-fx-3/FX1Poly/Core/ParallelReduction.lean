import FX1Poly.Core.Step
import FX1Poly.Core.RawTermSubst0
import FX1Poly.Core.StepSubst
import FX1Poly.Core.RawTermSubstPair

/-! # FX1Poly/Core/ParallelReduction
    — the FX parallel reduction relation + reflexivity (toward the Takahashi diamond / raw confluence)

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
    | beta {scope : Nat} {domainAnn domainAnn' : RawTerm scope} {body body' : RawTerm (scope + 1)}
        {arg arg' : RawTerm scope} :
        ParStep domainAnn domainAnn' → ParStep body body' → ParStep arg arg' →
        ParStep (.mkGen .gen_app ()
            (.childCons (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
              (.childCons arg .childNil))) (RawTerm.subst0 body' arg')
    | cong {scope : Nat} (gen : Generator) (payload : gen.payload scope)
           {children children' : RawTermChildren gen.binderShifts scope} :
        ParStepChildren children children' →
        ParStep (.mkGen gen payload children) (.mkGen gen payload children')
    | iotaBoolTrue {scope : Nat} {motive motive' : RawTerm (scope + 1)}
        {thenBranch thenBranch' elseBranch : RawTerm scope} :
        ParStep motive motive' → ParStep thenBranch thenBranch' →
        ParStep (.mkGen .gen_boolElim () (.childCons motive
            (.childCons thenBranch (.childCons elseBranch
              (.childCons (.mkGen .gen_boolTrue () .childNil) .childNil))))) thenBranch'
    | iotaBoolFalse {scope : Nat} {motive motive' : RawTerm (scope + 1)}
        {thenBranch elseBranch elseBranch' : RawTerm scope} :
        ParStep motive motive' → ParStep elseBranch elseBranch' →
        ParStep (.mkGen .gen_boolElim () (.childCons motive
            (.childCons thenBranch (.childCons elseBranch
              (.childCons (.mkGen .gen_boolFalse () .childNil) .childNil))))) elseBranch'
    | iotaFstPair {scope : Nat} {firstValue firstValue' secondValue : RawTerm scope} :
        ParStep firstValue firstValue' →
        ParStep (.mkGen .gen_fst () (.childCons (.mkGen .gen_pair ()
            (.childCons firstValue (.childCons secondValue .childNil))) .childNil)) firstValue'
    | iotaSndPair {scope : Nat} {firstValue secondValue secondValue' : RawTerm scope} :
        ParStep secondValue secondValue' →
        ParStep (.mkGen .gen_snd () (.childCons (.mkGen .gen_pair ()
            (.childCons firstValue (.childCons secondValue .childNil))) .childNil)) secondValue'
    | iotaNatElimZero {scope : Nat} {motive motive' : RawTerm (scope + 1)}
        {zeroBranch zeroBranch' : RawTerm scope} {succBranch : RawTerm (scope + 2)} :
        ParStep motive motive' → ParStep zeroBranch zeroBranch' →
        ParStep (.mkGen .gen_natElim () (.childCons motive
            (.childCons zeroBranch (.childCons succBranch
              (.childCons (.mkGen .gen_natZero () .childNil) .childNil))))) zeroBranch'
    | iotaNatRecZero {scope : Nat} {motive motive' : RawTerm (scope + 1)}
        {zeroBranch zeroBranch' : RawTerm scope} {succBranch : RawTerm (scope + 2)} :
        ParStep motive motive' → ParStep zeroBranch zeroBranch' →
        ParStep (.mkGen .gen_natRec () (.childCons motive
            (.childCons zeroBranch (.childCons succBranch
              (.childCons (.mkGen .gen_natZero () .childNil) .childNil))))) zeroBranch'
    | iotaListElimNil {scope : Nat} {motive motive' : RawTerm (scope + 1)}
        {nilBranch nilBranch' consBranch : RawTerm scope} :
        ParStep motive motive' → ParStep nilBranch nilBranch' →
        ParStep (.mkGen .gen_listElim () (.childCons motive
            (.childCons nilBranch (.childCons consBranch
              (.childCons (.mkGen .gen_listNil () .childNil) .childNil))))) nilBranch'
    | iotaOptionMatchNone {scope : Nat} {motive motive' : RawTerm (scope + 1)}
        {noneBranch noneBranch' someBranch : RawTerm scope} :
        ParStep motive motive' → ParStep noneBranch noneBranch' →
        ParStep (.mkGen .gen_optionMatch () (.childCons motive
            (.childCons noneBranch (.childCons someBranch
              (.childCons (.mkGen .gen_optionNone () .childNil) .childNil))))) noneBranch'
    | iotaOptionMatchSome {scope : Nat} {motive motive' : RawTerm (scope + 1)}
        {value value' noneBranch someBranch someBranch' : RawTerm scope} :
        ParStep motive motive' → ParStep someBranch someBranch' → ParStep value value' →
        ParStep (.mkGen .gen_optionMatch () (.childCons motive
            (.childCons noneBranch (.childCons someBranch
              (.childCons (.mkGen .gen_optionSome () (.childCons value .childNil))
                .childNil)))))
          (.mkGen .gen_app () (.childCons someBranch' (.childCons value' .childNil)))
    | iotaEitherMatchInl {scope : Nat} {motive motive' : RawTerm (scope + 1)}
        {value value' leftBranch leftBranch' rightBranch : RawTerm scope} :
        ParStep motive motive' → ParStep leftBranch leftBranch' → ParStep value value' →
        ParStep (.mkGen .gen_eitherMatch () (.childCons motive
            (.childCons leftBranch (.childCons rightBranch
              (.childCons (.mkGen .gen_eitherInl () (.childCons value .childNil))
                .childNil)))))
          (.mkGen .gen_app () (.childCons leftBranch' (.childCons value' .childNil)))
    | iotaEitherMatchInr {scope : Nat} {motive motive' : RawTerm (scope + 1)}
        {value value' leftBranch rightBranch rightBranch' : RawTerm scope} :
        ParStep motive motive' → ParStep rightBranch rightBranch' → ParStep value value' →
        ParStep (.mkGen .gen_eitherMatch () (.childCons motive
            (.childCons leftBranch (.childCons rightBranch
              (.childCons (.mkGen .gen_eitherInr () (.childCons value .childNil))
                .childNil)))))
          (.mkGen .gen_app () (.childCons rightBranch' (.childCons value' .childNil)))
    | iotaNatElimSucc {scope : Nat}
        {motive motive' : RawTerm (scope + 1)}
        {predecessor predecessor' zeroBranch zeroBranch' : RawTerm scope}
        {succBranch succBranch' : RawTerm (scope + 2)} :
        ParStep motive motive' → ParStep predecessor predecessor' →
        ParStep zeroBranch zeroBranch' → ParStep succBranch succBranch' →
        ParStep (.mkGen .gen_natElim () (.childCons motive
            (.childCons zeroBranch (.childCons succBranch
              (.childCons (.mkGen .gen_natSucc () (.childCons predecessor .childNil)) .childNil)))))
          (RawTerm.substPair succBranch'
            (.mkGen .gen_natElim ()
              (.childCons motive' (.childCons zeroBranch' (.childCons succBranch'
                (.childCons predecessor' .childNil)))))
            predecessor')
    | iotaNatRecSucc {scope : Nat}
        {motive motive' : RawTerm (scope + 1)}
        {predecessor predecessor' zeroBranch zeroBranch' : RawTerm scope}
        {succBranch succBranch' : RawTerm (scope + 2)} :
        ParStep motive motive' → ParStep predecessor predecessor' →
        ParStep zeroBranch zeroBranch' → ParStep succBranch succBranch' →
        ParStep (.mkGen .gen_natRec () (.childCons motive
            (.childCons zeroBranch (.childCons succBranch
              (.childCons (.mkGen .gen_natSucc () (.childCons predecessor .childNil)) .childNil)))))
          (RawTerm.substPair succBranch'
            (.mkGen .gen_natRec ()
              (.childCons motive' (.childCons zeroBranch' (.childCons succBranch'
                (.childCons predecessor' .childNil)))))
            predecessor')
    | iotaListElimCons {scope : Nat} {motive motive' : RawTerm (scope + 1)}
        {headVal headVal' tailVal tailVal' nilBranch nilBranch' consBranch consBranch' : RawTerm scope} :
        ParStep motive motive' → ParStep headVal headVal' → ParStep tailVal tailVal' →
        ParStep nilBranch nilBranch' → ParStep consBranch consBranch' →
        ParStep (.mkGen .gen_listElim () (.childCons motive
            (.childCons nilBranch (.childCons consBranch
              (.childCons
                (.mkGen .gen_listCons () (.childCons headVal (.childCons tailVal .childNil)))
                .childNil)))))
          (.mkGen .gen_app () (.childCons
            (.mkGen .gen_app () (.childCons
              (.mkGen .gen_app () (.childCons consBranch' (.childCons headVal' .childNil)))
              (.childCons tailVal' .childNil)))
            (.childCons (.mkGen .gen_listElim () (.childCons motive'
                (.childCons nilBranch' (.childCons consBranch'
                  (.childCons tailVal' .childNil))))) .childNil)))
    | iotaIdJRefl {scope : Nat} {motive motive' : RawTerm (scope + 2)}
        {baseCase baseCase' rawWitness : RawTerm scope} :
        ParStep motive motive' → ParStep baseCase baseCase' →
        ParStep (.mkGen .gen_idJ () (.childCons motive
            (.childCons baseCase
              (.childCons (.mkGen .gen_refl () (.childCons rawWitness .childNil)) .childNil)))) baseCase'
    | iotaIdStrictRecRefl {scope : Nat} {motive motive' : RawTerm (scope + 2)}
        {baseCase baseCase' rawWitness : RawTerm scope} :
        ParStep motive motive' → ParStep baseCase baseCase' →
        ParStep (.mkGen .gen_idStrictRec () (.childCons motive
            (.childCons baseCase
              (.childCons (.mkGen .gen_refl () (.childCons rawWitness .childNil)) .childNil)))) baseCase'
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
    | .beta => ParStep.beta (ParStep.refl _) (ParStep.refl _) (ParStep.refl _)
    | .cong gen payload childStep => ParStep.cong gen payload (StepChildren.toParStepChildren childStep)
    | .iotaBoolTrue => ParStep.iotaBoolTrue (ParStep.refl _) (ParStep.refl _)
    | .iotaBoolFalse => ParStep.iotaBoolFalse (ParStep.refl _) (ParStep.refl _)
    | .iotaFstPair => ParStep.iotaFstPair (ParStep.refl _)
    | .iotaSndPair => ParStep.iotaSndPair (ParStep.refl _)
    | .iotaNatElimZero => ParStep.iotaNatElimZero (ParStep.refl _) (ParStep.refl _)
    | .iotaNatRecZero => ParStep.iotaNatRecZero (ParStep.refl _) (ParStep.refl _)
    | .iotaListElimNil => ParStep.iotaListElimNil (ParStep.refl _) (ParStep.refl _)
    | .iotaOptionMatchNone => ParStep.iotaOptionMatchNone (ParStep.refl _) (ParStep.refl _)
    | .iotaOptionMatchSome =>
        ParStep.iotaOptionMatchSome (ParStep.refl _) (ParStep.refl _) (ParStep.refl _)
    | .iotaEitherMatchInl =>
        ParStep.iotaEitherMatchInl (ParStep.refl _) (ParStep.refl _) (ParStep.refl _)
    | .iotaEitherMatchInr =>
        ParStep.iotaEitherMatchInr (ParStep.refl _) (ParStep.refl _) (ParStep.refl _)
    | .iotaNatElimSucc =>
        ParStep.iotaNatElimSucc (ParStep.refl _) (ParStep.refl _) (ParStep.refl _) (ParStep.refl _)
    | .iotaNatRecSucc =>
        ParStep.iotaNatRecSucc (ParStep.refl _) (ParStep.refl _) (ParStep.refl _) (ParStep.refl _)
    | .iotaListElimCons =>
        ParStep.iotaListElimCons (ParStep.refl _) (ParStep.refl _) (ParStep.refl _)
          (ParStep.refl _) (ParStep.refl _)
    | .iotaIdJRefl => ParStep.iotaIdJRefl (ParStep.refl _) (ParStep.refl _)
    | .iotaIdStrictRecRefl => ParStep.iotaIdStrictRecRefl (ParStep.refl _) (ParStep.refl _)
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
    | .beta domainPar bodyPar argPar =>
        StepStar.transLast
          (StepStar.ofChildrenStar
            (StepChildrenStar.trans_compose
              (StepChildrenStar.here _
                (StepStar.ofChildrenStar
                  (StepChildrenStar.trans_compose
                    (StepChildrenStar.here _ (ParStep.toStepStar domainPar))
                    (StepChildrenStar.there _
                      (StepChildrenStar.here _ (ParStep.toStepStar bodyPar))))))
              (StepChildrenStar.there _
                (StepChildrenStar.here _ (ParStep.toStepStar argPar)))))
          Step.beta
    | .cong _gen _payload childrenPar =>
        StepStar.ofChildrenStar (ParStepChildren.toStepChildrenStar childrenPar)
    | .iotaBoolTrue motivePar thenPar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.trans_compose
            (StepChildrenStar.here _ (ParStep.toStepStar motivePar))
            (StepChildrenStar.there _ (StepChildrenStar.here _ (ParStep.toStepStar thenPar)))))
          Step.iotaBoolTrue
    | .iotaBoolFalse motivePar elsePar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.trans_compose
            (StepChildrenStar.here _ (ParStep.toStepStar motivePar))
            (StepChildrenStar.there _ (StepChildrenStar.there _
              (StepChildrenStar.here _ (ParStep.toStepStar elsePar))))))
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
    | .iotaNatElimZero motivePar zeroPar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.trans_compose
            (StepChildrenStar.here _ (ParStep.toStepStar motivePar))
            (StepChildrenStar.there _ (StepChildrenStar.here _ (ParStep.toStepStar zeroPar)))))
          Step.iotaNatElimZero
    | .iotaNatRecZero motivePar zeroPar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.trans_compose
            (StepChildrenStar.here _ (ParStep.toStepStar motivePar))
            (StepChildrenStar.there _ (StepChildrenStar.here _ (ParStep.toStepStar zeroPar)))))
          Step.iotaNatRecZero
    | .iotaListElimNil motivePar nilPar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.trans_compose
            (StepChildrenStar.here _ (ParStep.toStepStar motivePar))
            (StepChildrenStar.there _ (StepChildrenStar.here _ (ParStep.toStepStar nilPar)))))
          Step.iotaListElimNil
    | .iotaOptionMatchNone motivePar nonePar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.trans_compose
            (StepChildrenStar.here _ (ParStep.toStepStar motivePar))
            (StepChildrenStar.there _ (StepChildrenStar.here _ (ParStep.toStepStar nonePar)))))
          Step.iotaOptionMatchNone
    | .iotaOptionMatchSome motivePar somePar valuePar =>
        StepStar.trans_compose
          (StepStar.ofChildrenStar
            (StepChildrenStar.trans_compose
              (StepChildrenStar.here _ (ParStep.toStepStar motivePar))
              (StepChildrenStar.there _ (StepChildrenStar.there _
                (StepChildrenStar.here _ (ParStep.toStepStar somePar))))))
          (StepStar.trans Step.iotaOptionMatchSome
            (StepStar.ofChildrenStar (StepChildrenStar.there _
              (StepChildrenStar.here _ (ParStep.toStepStar valuePar)))))
    | .iotaEitherMatchInl motivePar leftPar valuePar =>
        StepStar.trans_compose
          (StepStar.ofChildrenStar
            (StepChildrenStar.trans_compose
              (StepChildrenStar.here _ (ParStep.toStepStar motivePar))
              (StepChildrenStar.there _ (StepChildrenStar.here _
                (ParStep.toStepStar leftPar)))))
          (StepStar.trans Step.iotaEitherMatchInl
            (StepStar.ofChildrenStar (StepChildrenStar.there _
              (StepChildrenStar.here _ (ParStep.toStepStar valuePar)))))
    | .iotaEitherMatchInr motivePar rightPar valuePar =>
        StepStar.trans_compose
          (StepStar.ofChildrenStar
            (StepChildrenStar.trans_compose
              (StepChildrenStar.here _ (ParStep.toStepStar motivePar))
              (StepChildrenStar.there _ (StepChildrenStar.there _
                (StepChildrenStar.here _ (ParStep.toStepStar rightPar))))))
          (StepStar.trans Step.iotaEitherMatchInr
            (StepStar.ofChildrenStar (StepChildrenStar.there _
              (StepChildrenStar.here _ (ParStep.toStepStar valuePar)))))
    | .iotaNatElimSucc motivePar predPar zeroPar succPar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.trans_compose
            (StepChildrenStar.here _ (ParStep.toStepStar motivePar))
            (StepChildrenStar.trans_compose
              (StepChildrenStar.there _ (StepChildrenStar.here _ (ParStep.toStepStar zeroPar)))
              (StepChildrenStar.trans_compose
                (StepChildrenStar.there _ (StepChildrenStar.there _
                  (StepChildrenStar.here _ (ParStep.toStepStar succPar))))
                (StepChildrenStar.there _ (StepChildrenStar.there _ (StepChildrenStar.there _
                  (StepChildrenStar.here _
                    (StepStar.ofChildrenStar
                      (StepChildrenStar.here _ (ParStep.toStepStar predPar)))))))))))
          Step.iotaNatElimSucc
    | .iotaNatRecSucc motivePar predPar zeroPar succPar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.trans_compose
            (StepChildrenStar.here _ (ParStep.toStepStar motivePar))
            (StepChildrenStar.trans_compose
              (StepChildrenStar.there _ (StepChildrenStar.here _ (ParStep.toStepStar zeroPar)))
              (StepChildrenStar.trans_compose
                (StepChildrenStar.there _ (StepChildrenStar.there _
                  (StepChildrenStar.here _ (ParStep.toStepStar succPar))))
                (StepChildrenStar.there _ (StepChildrenStar.there _ (StepChildrenStar.there _
                  (StepChildrenStar.here _
                    (StepStar.ofChildrenStar
                      (StepChildrenStar.here _ (ParStep.toStepStar predPar)))))))))))
          Step.iotaNatRecSucc
    | .iotaListElimCons motivePar headPar tailPar nilPar consPar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.trans_compose
            (StepChildrenStar.here _ (ParStep.toStepStar motivePar))
            (StepChildrenStar.trans_compose
              (StepChildrenStar.there _ (StepChildrenStar.here _ (ParStep.toStepStar nilPar)))
              (StepChildrenStar.trans_compose
                (StepChildrenStar.there _ (StepChildrenStar.there _
                  (StepChildrenStar.here _ (ParStep.toStepStar consPar))))
                (StepChildrenStar.trans_compose
                  (StepChildrenStar.there _ (StepChildrenStar.there _ (StepChildrenStar.there _
                    (StepChildrenStar.here _
                      (StepStar.ofChildrenStar
                        (StepChildrenStar.here _ (ParStep.toStepStar headPar)))))))
                  (StepChildrenStar.there _ (StepChildrenStar.there _ (StepChildrenStar.there _
                    (StepChildrenStar.here _
                      (StepStar.ofChildrenStar (StepChildrenStar.there _
                        (StepChildrenStar.here _ (ParStep.toStepStar tailPar)))))))))))))
          Step.iotaListElimCons
    | .iotaIdJRefl motivePar basePar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.trans_compose
            (StepChildrenStar.here _ (ParStep.toStepStar motivePar))
            (StepChildrenStar.there _ (StepChildrenStar.here _ (ParStep.toStepStar basePar)))))
          Step.iotaIdJRefl
    | .iotaIdStrictRecRefl motivePar basePar =>
        StepStar.transLast (StepStar.ofChildrenStar
          (StepChildrenStar.trans_compose
            (StepChildrenStar.here _ (ParStep.toStepStar motivePar))
            (StepChildrenStar.there _ (StepChildrenStar.here _ (ParStep.toStepStar basePar)))))
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
