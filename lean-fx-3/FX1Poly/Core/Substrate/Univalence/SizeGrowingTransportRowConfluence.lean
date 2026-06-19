import FX1Poly.Core.Substrate.Univalence.SizeGrowingTransportRowSN
import FX1Poly.Core.Rewriting.Confluence.Newman

/-! # FX1Poly/Core/Substrate/Univalence/SizeGrowingTransportRowConfluence
    — Church-Rosser for the size-growing demo row via the GENUINE Newman route (SN + local confluence)

The univalence row was confluent the EASY way (no new redexes ⇒ a one-pass `univNF` is a sound complete
confluent normalizer, so confluence falls out of a preservation invariant with no Newman, no SN — see
`UnivalenceRowDecidableConv`).  The size-growing demo row
`glueElim(productCode A B) ↝ pair(glueElim A, glueElim B)` is the OPPOSITE case: it CREATES redexes (when
`A`/`B` are `productCode`-headed, the residual `glueElim A` fires again), so no single bottom-up pass
normalizes it.  This is exactly where Newman's lemma is the right tool: the row is strongly normalizing
(shipped: `sizeGrowingTransportDemo_wellFounded`, by the product-former measure) and LOCALLY confluent, and
SN + local confluence ⇒ confluence.

This file proves local confluence (`WeaklyConfluent`) by the standard critical-pair analysis and feeds it,
together with the shipped SN, to the GENERIC `FX1Poly.Core.newman` to obtain
`Confluent SizeGrowingTransportDemoStep`.  The demo rule is left-linear with a single rigid redex shape and
has NO critical pairs, so the analysis is small: `fire`-vs-`fire` is the same reduct; `fire`-vs-`cong`
(the redex's `productCode` argument steps) joins the fired pair against the residual fire (`demoFireCongJoin`);
`cong`-vs-`cong` recurses through the children; disjoint `here`-vs-`there` peaks commute in one step each.

## This file (Part 1: the scaffolding)

  * `demoReflTransClosure_cong`/`_here`/`_there` — lift a closure chain through a congruence position.
  * `joinableSymm`, `joinableChildrenToTerm`, `joinableHeadToChildren`, `joinableTailToChildren` — `Joinable`
    transported across congruence positions and swapped.
  * `demoStep_liftGlueElim`/`_liftPairHead`/`_liftPairTail` — single-step congruence lifts.
  * **`demoFireCongJoin` (★)** — the one non-trivial peak: a step inside the redex's `productCode` argument,
    joined against the residual fire.

## Zero-axiom verification

The congruence lifts are structural inductions on the closure; the `Joinable` lifts are `obtain`/repack;
`demoFireCongJoin` is `cases` on the (rigid-shaped) inner step.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open FX1Poly.Universe (LevelExpr UniverseFlag)

/-! ## Generic `Joinable` symmetry -/

/-- Joinability is symmetric: swap the two converging chains. -/
theorem joinableSymm {Carrier : Type} {rel : Carrier → Carrier → Prop} {leftValue rightValue : Carrier}
    (joined : Joinable rel leftValue rightValue) : Joinable rel rightValue leftValue := by
  obtain ⟨commonReduct, leftChain, rightChain⟩ := joined
  exact ⟨commonReduct, rightChain, leftChain⟩

/-! ## Closure-chain congruence lifts for the demo relation -/

/-- Lift a children-closure chain to a term-closure chain (congruence under a generator). -/
theorem demoReflTransClosure_cong {scope : Nat} (generator : Generator) (payload : generator.payload scope)
    {children children' : RawTermChildren generator.binderShifts scope}
    (chain : ReflTransClosure SizeGrowingTransportDemoStepChildren children children') :
    ReflTransClosure SizeGrowingTransportDemoStep (.mkGen generator payload children)
      (.mkGen generator payload children') := by
  induction chain with
  | refl _ => exact ReflTransClosure.refl _
  | head firstStep _rest inductionHypothesis =>
      exact ReflTransClosure.head (SizeGrowingTransportDemoStep.cong generator payload firstStep)
        inductionHypothesis

/-- Lift a head-closure chain to a children-closure chain (the `here` position). -/
theorem demoReflTransClosure_here {parentScope headShift : Nat} {restShifts : List Nat}
    {head head' : RawTerm (parentScope + headShift)} (rest : RawTermChildren restShifts parentScope)
    (chain : ReflTransClosure SizeGrowingTransportDemoStep head head') :
    ReflTransClosure SizeGrowingTransportDemoStepChildren
      (RawTermChildren.childCons head rest) (RawTermChildren.childCons head' rest) := by
  induction chain with
  | refl _ => exact ReflTransClosure.refl _
  | head firstStep _rest inductionHypothesis =>
      exact ReflTransClosure.head (SizeGrowingTransportDemoStepChildren.here rest firstStep)
        inductionHypothesis

/-- Lift a tail-closure chain to a children-closure chain (the `there` position). -/
theorem demoReflTransClosure_there {parentScope headShift : Nat} {restShifts : List Nat}
    (head : RawTerm (parentScope + headShift)) {rest rest' : RawTermChildren restShifts parentScope}
    (chain : ReflTransClosure SizeGrowingTransportDemoStepChildren rest rest') :
    ReflTransClosure SizeGrowingTransportDemoStepChildren
      (RawTermChildren.childCons head rest) (RawTermChildren.childCons head rest') := by
  induction chain with
  | refl _ => exact ReflTransClosure.refl _
  | head firstStep _rest inductionHypothesis =>
      exact ReflTransClosure.head (SizeGrowingTransportDemoStepChildren.there head firstStep)
        inductionHypothesis

/-! ## `Joinable` transported across congruence positions -/

/-- A children join lifts to a term join under a generator. -/
theorem joinableChildrenToTerm {scope : Nat} (generator : Generator) (payload : generator.payload scope)
    {children children' : RawTermChildren generator.binderShifts scope}
    (joined : Joinable SizeGrowingTransportDemoStepChildren children children') :
    Joinable SizeGrowingTransportDemoStep (.mkGen generator payload children)
      (.mkGen generator payload children') := by
  obtain ⟨commonReduct, leftChain, rightChain⟩ := joined
  exact ⟨.mkGen generator payload commonReduct,
    demoReflTransClosure_cong generator payload leftChain,
    demoReflTransClosure_cong generator payload rightChain⟩

/-- A head join lifts to a children join (the `here` position). -/
theorem joinableHeadToChildren {parentScope headShift : Nat} {restShifts : List Nat}
    {head head' : RawTerm (parentScope + headShift)} (rest : RawTermChildren restShifts parentScope)
    (joined : Joinable SizeGrowingTransportDemoStep head head') :
    Joinable SizeGrowingTransportDemoStepChildren
      (RawTermChildren.childCons head rest) (RawTermChildren.childCons head' rest) := by
  obtain ⟨commonReduct, leftChain, rightChain⟩ := joined
  exact ⟨RawTermChildren.childCons commonReduct rest,
    demoReflTransClosure_here rest leftChain, demoReflTransClosure_here rest rightChain⟩

/-- A tail join lifts to a children join (the `there` position). -/
theorem joinableTailToChildren {parentScope headShift : Nat} {restShifts : List Nat}
    (head : RawTerm (parentScope + headShift)) {rest rest' : RawTermChildren restShifts parentScope}
    (joined : Joinable SizeGrowingTransportDemoStepChildren rest rest') :
    Joinable SizeGrowingTransportDemoStepChildren
      (RawTermChildren.childCons head rest) (RawTermChildren.childCons head rest') := by
  obtain ⟨commonReduct, leftChain, rightChain⟩ := joined
  exact ⟨RawTermChildren.childCons head commonReduct,
    demoReflTransClosure_there head leftChain, demoReflTransClosure_there head rightChain⟩

/-! ## Single-step congruence lifts -/

/-- A step inside a `glueElim`'s argument. -/
theorem demoStep_liftGlueElim {scope : Nat} {argument argument' : RawTerm scope}
    (stepInside : SizeGrowingTransportDemoStep argument argument') :
    SizeGrowingTransportDemoStep
      (.mkGen .gen_glueElim () (.childCons argument .childNil))
      (.mkGen .gen_glueElim () (.childCons argument' .childNil)) := by
  refine SizeGrowingTransportDemoStep.cong .gen_glueElim () ?_
  exact SizeGrowingTransportDemoStepChildren.here _ stepInside

/-- A step inside a `pair`'s first component. -/
theorem demoStep_liftPairHead {scope : Nat} {leftComponent leftComponent' rightComponent : RawTerm scope}
    (stepInside : SizeGrowingTransportDemoStep leftComponent leftComponent') :
    SizeGrowingTransportDemoStep
      (.mkGen .gen_pair () (.childCons leftComponent (.childCons rightComponent .childNil)))
      (.mkGen .gen_pair () (.childCons leftComponent' (.childCons rightComponent .childNil))) := by
  refine SizeGrowingTransportDemoStep.cong .gen_pair () ?_
  exact SizeGrowingTransportDemoStepChildren.here _ stepInside

/-- A step inside a `pair`'s second component. -/
theorem demoStep_liftPairTail {scope : Nat} {leftComponent rightComponent rightComponent' : RawTerm scope}
    (stepInside : SizeGrowingTransportDemoStep rightComponent rightComponent') :
    SizeGrowingTransportDemoStep
      (.mkGen .gen_pair () (.childCons leftComponent (.childCons rightComponent .childNil)))
      (.mkGen .gen_pair () (.childCons leftComponent (.childCons rightComponent' .childNil))) := by
  refine SizeGrowingTransportDemoStep.cong .gen_pair () ?_
  exact SizeGrowingTransportDemoStepChildren.there _
    (SizeGrowingTransportDemoStepChildren.here _ stepInside)

/-! ## The crucial peak — `fire` versus a step inside the redex's `productCode` argument -/

/-- **★ The `fire`-vs-`cong` join.**  When one reduction fires the root redex
`glueElim(productCode A B) ↝ pair(glueElim A, glueElim B)` and the other steps INSIDE the `productCode`
argument (`productCode A B → reductInside`), the two results join: the fired pair pushes the same inner step
through `glueElim`, and the residual `glueElim(reductInside)` fires.  The inner step has a rigid shape
(`productCode`-headed, so never the root rule; its argument is `A` or `B`), giving exactly two sub-cases. -/
theorem demoFireCongJoin {scope : Nat} {leftCode rightCode reductInside : RawTerm scope}
    (stepInsideProduct : SizeGrowingTransportDemoStep
      (.mkGen .gen_productCode () (.childCons leftCode (.childCons rightCode .childNil)))
      reductInside) :
    Joinable SizeGrowingTransportDemoStep
      (.mkGen .gen_pair ()
        (.childCons (.mkGen .gen_glueElim () (.childCons leftCode .childNil))
          (.childCons (.mkGen .gen_glueElim () (.childCons rightCode .childNil)) .childNil)))
      (.mkGen .gen_glueElim () (.childCons reductInside .childNil)) := by
  cases stepInsideProduct with
  | cong _generator _payload childStep =>
      cases childStep with
      | here _rest leftInnerStep =>
          exact ⟨_,
            ReflTransClosure.single (demoStep_liftPairHead (demoStep_liftGlueElim leftInnerStep)),
            ReflTransClosure.single (SizeGrowingTransportDemoStep.fire _ rightCode)⟩
      | there _head restStep =>
          cases restStep with
          | here _rest rightInnerStep =>
              exact ⟨_,
                ReflTransClosure.single (demoStep_liftPairTail (demoStep_liftGlueElim rightInnerStep)),
                ReflTransClosure.single (SizeGrowingTransportDemoStep.fire leftCode _)⟩
          | there _head deeperStep => nomatch deeperStep

/-! ## Local confluence (the mutual critical-pair analysis) -/

/-- **★ Local confluence of the demo row.**  Two divergent single steps from the same term join.  Proved by
the explicit mutual recursor with a UNIVERSAL-CONCLUSION motive (`∀ other, step source other → Joinable
target other`), casing the second step inside each first-step arm: `fire`-vs-`fire` is the same reduct;
`fire`-vs-`cong` (the redex's `productCode` argument steps) is `demoFireCongJoin`; `cong`-vs-`cong` recurses
through the children; disjoint `here`-vs-`there` peaks commute in one step each. -/
theorem demoStep_localConfluent {scope : Nat} {source target : RawTerm scope}
    (leftStep : SizeGrowingTransportDemoStep source target) :
    ∀ (other : RawTerm scope), SizeGrowingTransportDemoStep source other →
      Joinable SizeGrowingTransportDemoStep target other := by
  let motiveStep : {scope : Nat} → (first second : RawTerm scope) →
      SizeGrowingTransportDemoStep first second → Prop :=
    fun {scope} first second _ =>
      ∀ (other : RawTerm scope), SizeGrowingTransportDemoStep first other →
        Joinable SizeGrowingTransportDemoStep second other
  let motiveChildren : {parentScope : Nat} → {binderShifts : List Nat} →
      (first second : RawTermChildren binderShifts parentScope) →
      SizeGrowingTransportDemoStepChildren first second → Prop :=
    fun {_} {_} first second _ =>
      ∀ (other : RawTermChildren _ _), SizeGrowingTransportDemoStepChildren first other →
        Joinable SizeGrowingTransportDemoStepChildren second other
  exact
    SizeGrowingTransportDemoStep.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      (fun {_} _leftCode _rightCode => by
        intro _other rightStep
        cases rightStep with
        | fire _ _ => exact ⟨_, ReflTransClosure.refl _, ReflTransClosure.refl _⟩
        | cong _generator _payload childStep =>
            cases childStep with
            | here _rest innerStep => exact demoFireCongJoin innerStep
            | there _head deeperStep => nomatch deeperStep)
      (fun {_} generator payload {_children} {_children'} childStep childIH => by
        intro _other rightStep
        cases rightStep with
        | fire _ _ =>
            cases childStep with
            | here _rest innerStep => exact joinableSymm (demoFireCongJoin innerStep)
            | there _head deeperStep => nomatch deeperStep
        | cong _generator2 _payload2 rightChildStep =>
            exact joinableChildrenToTerm generator payload (childIH _ rightChildStep))
      (fun {_} {_} {_} {_head} {_head'} rest headStep headIH => by
        intro _other rightChildStep
        cases rightChildStep with
        | here _rest2 rightHeadStep =>
            exact joinableHeadToChildren rest (headIH _ rightHeadStep)
        | there _head2 rightRestStep =>
            exact ⟨_,
              ReflTransClosure.single (SizeGrowingTransportDemoStepChildren.there _ rightRestStep),
              ReflTransClosure.single (SizeGrowingTransportDemoStepChildren.here _ headStep)⟩)
      (fun {_} {_} {_} head {_rest} {_rest'} restStep restIH => by
        intro _other rightChildStep
        cases rightChildStep with
        | here _rest2 rightHeadStep =>
            exact ⟨_,
              ReflTransClosure.single (SizeGrowingTransportDemoStepChildren.here _ rightHeadStep),
              ReflTransClosure.single (SizeGrowingTransportDemoStepChildren.there _ restStep)⟩
        | there _head2 rightRestStep =>
            exact joinableTailToChildren head (restIH _ rightRestStep))
      leftStep

/-! ## Weak confluence and Church-Rosser via the generic Newman -/

/-- The demo row is weakly (locally) confluent. -/
theorem sizeGrowingTransportDemo_weaklyConfluent {scope : Nat} :
    WeaklyConfluent (@SizeGrowingTransportDemoStep scope) := by
  intro _source _leftReduct _rightReduct leftStepProof rightStepProof
  exact demoStep_localConfluent leftStepProof _ rightStepProof

/-- **★ The size-growing demo row is confluent (Church-Rosser) — via the GENUINE Newman route.**  Unlike the
univalence row (no new redexes ⇒ a one-pass normalizer gives confluence directly), this row CREATES redexes,
so the only route to confluence is Newman's lemma: strong normalization (`sizeGrowingTransportDemo_wellFounded`,
by the product-former measure) plus local confluence (`sizeGrowingTransportDemo_weaklyConfluent`) imply global
confluence.  Rides the generic `FX1Poly.Core.newman`. -/
theorem sizeGrowingTransportDemo_confluent {scope : Nat} :
    Confluent (@SizeGrowingTransportDemoStep scope) :=
  newman sizeGrowingTransportDemo_wellFounded sizeGrowingTransportDemo_weaklyConfluent

end FX1Poly.Core
