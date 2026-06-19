import FX1Poly.Core.Substrate.Univalence.SizeGrowingTransportRowConfluence
import FX1Poly.Core.Substrate.Univalence.UnivalenceRowDecidableConv
import FX1Poly.Core.Substrate.Univalence.LexJointRowSN
import FX1Poly.Core.Rewriting.Confluence.DiamondConfluence

/-! # FX1Poly/Core/Substrate/Univalence/UnifiedDefinitionalRowConfluence
    — Church-Rosser for the JOINT definitional row (univalence ∪ size-growing demo) via the GENUINE Newman
    route, completing the modular-confluence picture for definitional univalence

The two component rows are each confluent for OPPOSITE reasons:

  * the univalence row `idCode(universeCode, A, B) ↝ equivCode(A, B)` creates NO redexes, so a one-pass
    `univNF` is a sound complete confluent normalizer (`univalenceRowStep_confluent`, no Newman, no SN); and
  * the size-growing demo row `glueElim(productCode A B) ↝ pair(glueElim A, glueElim B)` CREATES redexes, so
    its confluence goes through genuine Newman (`sizeGrowingTransportDemo_confluent`, SN + local confluence).

This file glues them.  The union `UnifiedDefinitionalRowStep` is strongly normalizing by the shipped
lexicographic type-complexity measure `lex(productFormerCount, size)` (`unifiedDefinitionalRow_wellFounded`),
so by Newman's lemma it is confluent once it is LOCALLY confluent.  Local confluence is a four-way peak
analysis: the like/like peaks fall to each row's own confluence, and the two MIXED peaks reduce to the
single observation that the two rules can never overlap — `gen_idCode` and `gen_glueElim` are distinct
generator heads, so a univalence redex and a demo redex from the same term sit at disjoint positions and
COMMUTE in one step each (`univStepDemoStepCommute`, zero critical pairs).

## What this ships

  * `univStep_liftGlueElim` / `univStep_liftPairHead` / `univStep_liftPairTail` — single univalence-step
    congruence lifts (mirrors the demo-side lifts), and `demoStep_liftEquivHead` / `demoStep_liftEquivTail`
    — single demo-step lifts into an `equivCode` child (the residual after a univalence `fire`).
  * **`univStepDemoStepCommute` (★)** — the cross-relation commuting diamond: a univalence step and a demo
    step from the same source reconverge in one demo step and one univalence step.  Explicit mutual recursor
    with a universal-conclusion motive over the demo step, casing it inside each univalence arm; the two
    `fire`-vs-`cong` cross-peaks (`fire` univalence inside an `idCode` whose argument demo-steps; `fire` demo
    on a `glueElim` whose `productCode` argument univalence-steps) are the only non-disjoint interactions,
    and even those are disjoint-by-head so they join immediately.
  * `joinableUnivToUnion` / `joinableDemoToUnion` — lift a single-row `Joinable` into the union via
    `ReflTransClosure.monotone`.
  * **`unifiedDefinitionalRow_weaklyConfluent` (★)** — the four-way local-confluence peak analysis.
  * **`unifiedDefinitionalRow_confluent` (★)** — the joint row is Church-Rosser, via the generic
    `FX1Poly.Core.newman` on the shipped joint SN.

## Zero-axiom verification

The cross-commutation is the same propext-clean indexed-`cases` analysis the demo local confluence used; the
union lifts are `ReflTransClosure.monotone` over the audited generic closure; the assembly is `rcases` over
the union `Or` plus the shipped `newman`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open FX1Poly.Universe (LevelExpr UniverseFlag)

/-! ## Single-step congruence lifts for the univalence relation -/

/-- A univalence step inside a `glueElim`'s argument. -/
theorem univStep_liftGlueElim {scope : Nat} {argument argument' : RawTerm scope}
    (stepInside : UnivalenceRowStep argument argument') :
    UnivalenceRowStep
      (.mkGen .gen_glueElim () (.childCons argument .childNil))
      (.mkGen .gen_glueElim () (.childCons argument' .childNil)) := by
  refine UnivalenceRowStep.cong .gen_glueElim () ?_
  exact UnivalenceRowStepChildren.here _ stepInside

/-- A univalence step inside a `pair`'s first component. -/
theorem univStep_liftPairHead {scope : Nat} {leftComponent leftComponent' rightComponent : RawTerm scope}
    (stepInside : UnivalenceRowStep leftComponent leftComponent') :
    UnivalenceRowStep
      (.mkGen .gen_pair () (.childCons leftComponent (.childCons rightComponent .childNil)))
      (.mkGen .gen_pair () (.childCons leftComponent' (.childCons rightComponent .childNil))) := by
  refine UnivalenceRowStep.cong .gen_pair () ?_
  exact UnivalenceRowStepChildren.here _ stepInside

/-- A univalence step inside a `pair`'s second component. -/
theorem univStep_liftPairTail {scope : Nat} {leftComponent rightComponent rightComponent' : RawTerm scope}
    (stepInside : UnivalenceRowStep rightComponent rightComponent') :
    UnivalenceRowStep
      (.mkGen .gen_pair () (.childCons leftComponent (.childCons rightComponent .childNil)))
      (.mkGen .gen_pair () (.childCons leftComponent (.childCons rightComponent' .childNil))) := by
  refine UnivalenceRowStep.cong .gen_pair () ?_
  exact UnivalenceRowStepChildren.there _
    (UnivalenceRowStepChildren.here _ stepInside)

/-! ## Single-step congruence lifts for the demo relation into an `equivCode` child

These are the residual of a univalence `fire`: after `idCode(universeCode, A, B) ↝ equivCode(A, B)`, a demo
step that diverged inside `A` (resp. `B`) lifts into the first (resp. second) `equivCode` component. -/

/-- A demo step inside an `equivCode`'s first component. -/
theorem demoStep_liftEquivHead {scope : Nat} {leftComponent leftComponent' rightComponent : RawTerm scope}
    (stepInside : SizeGrowingTransportDemoStep leftComponent leftComponent') :
    SizeGrowingTransportDemoStep
      (.mkGen .gen_equivCode () (.childCons leftComponent (.childCons rightComponent .childNil)))
      (.mkGen .gen_equivCode () (.childCons leftComponent' (.childCons rightComponent .childNil))) := by
  refine SizeGrowingTransportDemoStep.cong .gen_equivCode () ?_
  exact SizeGrowingTransportDemoStepChildren.here _ stepInside

/-- A demo step inside an `equivCode`'s second component. -/
theorem demoStep_liftEquivTail {scope : Nat} {leftComponent rightComponent rightComponent' : RawTerm scope}
    (stepInside : SizeGrowingTransportDemoStep rightComponent rightComponent') :
    SizeGrowingTransportDemoStep
      (.mkGen .gen_equivCode () (.childCons leftComponent (.childCons rightComponent .childNil)))
      (.mkGen .gen_equivCode () (.childCons leftComponent (.childCons rightComponent' .childNil))) := by
  refine SizeGrowingTransportDemoStep.cong .gen_equivCode () ?_
  exact SizeGrowingTransportDemoStepChildren.there _
    (SizeGrowingTransportDemoStepChildren.here _ stepInside)

/-! ## The cross-relation commuting diamond -/

/-- **★ A univalence step and a demo step from the same source commute** — in one demo step and one
univalence step.  The two rules can never overlap (`gen_idCode` vs `gen_glueElim` are distinct generator
heads), so the divergent redexes sit at disjoint positions: when one is nested inside the other, firing the
outer leaves the inner intact (and vice versa).  Proved by the explicit mutual recursor with a
universal-conclusion motive (`∀ demoReduct, demoStep source demoReduct → ∃ joinPoint, …`), casing the demo
step inside each univalence arm.  The two non-disjoint cross-peaks — a univalence `fire` whose `idCode`
argument demo-steps, and a univalence step inside the `productCode` argument of a demo `fire` — both join by
pushing the SAME surviving step through the other rule's residual. -/
theorem univStepDemoStepCommute {scope : Nat} {source univReduct : RawTerm scope}
    (univStep : UnivalenceRowStep source univReduct) :
    ∀ (demoReduct : RawTerm scope), SizeGrowingTransportDemoStep source demoReduct →
      ∃ joinPoint, SizeGrowingTransportDemoStep univReduct joinPoint
        ∧ UnivalenceRowStep demoReduct joinPoint := by
  let motiveStep : {scope : Nat} → (first second : RawTerm scope) →
      UnivalenceRowStep first second → Prop :=
    fun {scope} first second _ =>
      ∀ (demoReduct : RawTerm scope), SizeGrowingTransportDemoStep first demoReduct →
        ∃ joinPoint, SizeGrowingTransportDemoStep second joinPoint
          ∧ UnivalenceRowStep demoReduct joinPoint
  let motiveChildren : {parentScope : Nat} → {binderShifts : List Nat} →
      (first second : RawTermChildren binderShifts parentScope) →
      UnivalenceRowStepChildren first second → Prop :=
    fun {parentScope} {binderShifts} first second _ =>
      ∀ (demoReductChildren : RawTermChildren binderShifts parentScope),
        SizeGrowingTransportDemoStepChildren first demoReductChildren →
        ∃ joinPoint, SizeGrowingTransportDemoStepChildren second joinPoint
          ∧ UnivalenceRowStepChildren demoReductChildren joinPoint
  exact
    UnivalenceRowStep.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      -- univalence `fire`: source `idCode(universeCode, lhs, rhs)`.  The demo step cannot fire here
      -- (`idCode ≠ glueElim`), so it steps inside `lhs` or `rhs`; the univalence reduct `equivCode(lhs, rhs)`
      -- carries the same inner step into the corresponding `equivCode` child, and the demo reduct fires.
      (fun {_} _levelExpr _flag _lhsCode _rhsCode => by
        intro _demoReduct demoStep
        cases demoStep with
        | cong _gen _payload demoChildStep =>
            cases demoChildStep with
            | here _rest demoUniverseStep =>
                cases demoUniverseStep with
                | cong _g _p demoInner => nomatch demoInner
            | there _head demoRestStep =>
                cases demoRestStep with
                | here _rest2 demoLhsStep =>
                    exact ⟨_, demoStep_liftEquivHead demoLhsStep,
                      UnivalenceRowStep.fire _ _ _ _⟩
                | there _head2 demoRest2Step =>
                    cases demoRest2Step with
                    | here _rest3 demoRhsStep =>
                        exact ⟨_, demoStep_liftEquivTail demoRhsStep,
                          UnivalenceRowStep.fire _ _ _ _⟩
                    | there _head3 demoDeeper => nomatch demoDeeper)
      -- univalence `cong` at a generator node.  Either the demo step fires the root (forcing the node to be
      -- `glueElim` whose `productCode` argument the univalence step is rewriting — the disjoint cross-peak),
      -- or it `cong`s the same node and the children IH commutes them.
      (fun {_} gen payload {children} {children'} univChildStep childIH => by
        intro _demoReduct demoStep
        cases demoStep with
        | fire demoLeftCode demoRightCode =>
            cases univChildStep with
            | here _rest univInner =>
                cases univInner with
                | cong _g2 _p2 univProductChild =>
                    cases univProductChild with
                    | here _rest2 univLeftStep =>
                        exact ⟨_, SizeGrowingTransportDemoStep.fire _ _,
                          univStep_liftPairHead (univStep_liftGlueElim univLeftStep)⟩
                    | there _head2 univRightRest =>
                        cases univRightRest with
                        | here _rest3 univRightStep =>
                            exact ⟨_, SizeGrowingTransportDemoStep.fire _ _,
                              univStep_liftPairTail (univStep_liftGlueElim univRightStep)⟩
                        | there _head3 univDeeper => nomatch univDeeper
            | there _head univTailStep => nomatch univTailStep
        | cong _gen2 _payload2 demoChildStep =>
            obtain ⟨_joinChildren, demoChildJoin, univChildJoin⟩ := childIH _ demoChildStep
            exact ⟨_, SizeGrowingTransportDemoStep.cong gen payload demoChildJoin,
              UnivalenceRowStep.cong gen payload univChildJoin⟩)
      -- univalence step in the head child.  Demo in the head ⇒ recurse via the head IH; demo in the tail ⇒
      -- disjoint, commute in one step each.
      (fun {_} {_} {_} {_head} {_head'} rest _univHeadStep headIH => by
        intro _demoReductChildren demoChildStep
        cases demoChildStep with
        | here _rest2 demoHeadStep =>
            obtain ⟨_joinHead, demoHeadJoin, univHeadJoin⟩ := headIH _ demoHeadStep
            exact ⟨_, SizeGrowingTransportDemoStepChildren.here rest demoHeadJoin,
              UnivalenceRowStepChildren.here rest univHeadJoin⟩
        | there _head2 demoRestStep =>
            exact ⟨_, SizeGrowingTransportDemoStepChildren.there _ demoRestStep,
              UnivalenceRowStepChildren.here _ _univHeadStep⟩)
      -- univalence step in the tail children.  Demo in the head ⇒ disjoint; demo in the tail ⇒ recurse.
      (fun {_} {_} {_} head {_rest} {_rest'} _univRestStep restIH => by
        intro _demoReductChildren demoChildStep
        cases demoChildStep with
        | here _rest2 demoHeadStep =>
            exact ⟨_, SizeGrowingTransportDemoStepChildren.here _ demoHeadStep,
              UnivalenceRowStepChildren.there _ _univRestStep⟩
        | there _head2 demoRestStep =>
            obtain ⟨_joinRest, demoRestJoin, univRestJoin⟩ := restIH _ demoRestStep
            exact ⟨_, SizeGrowingTransportDemoStepChildren.there head demoRestJoin,
              UnivalenceRowStepChildren.there head univRestJoin⟩)
      univStep

/-! ## Lifting single-row joins into the union -/

/-- A univalence-row join is a union join (every univalence step is a union step). -/
theorem joinableUnivToUnion {scope : Nat} {leftValue rightValue : RawTerm scope}
    (joined : Joinable UnivalenceRowStep leftValue rightValue) :
    Joinable (@UnifiedDefinitionalRowStep scope) leftValue rightValue := by
  obtain ⟨commonReduct, leftChain, rightChain⟩ := joined
  exact ⟨commonReduct,
    ReflTransClosure.monotone (fun univStep => Or.inl univStep) leftChain,
    ReflTransClosure.monotone (fun univStep => Or.inl univStep) rightChain⟩

/-- A demo-row join is a union join (every demo step is a union step). -/
theorem joinableDemoToUnion {scope : Nat} {leftValue rightValue : RawTerm scope}
    (joined : Joinable SizeGrowingTransportDemoStep leftValue rightValue) :
    Joinable (@UnifiedDefinitionalRowStep scope) leftValue rightValue := by
  obtain ⟨commonReduct, leftChain, rightChain⟩ := joined
  exact ⟨commonReduct,
    ReflTransClosure.monotone (fun demoStep => Or.inr demoStep) leftChain,
    ReflTransClosure.monotone (fun demoStep => Or.inr demoStep) rightChain⟩

/-! ## Local confluence and Church-Rosser via the generic Newman -/

/-- **★ The joint definitional row is weakly (locally) confluent.**  Four-way peak analysis: univalence vs
univalence joins by `univalenceRowStep_confluent`; demo vs demo by `demoStep_localConfluent`; the two mixed
peaks by the cross-relation commuting diamond `univStepDemoStepCommute` (the divergent redexes are
disjoint-by-head, so each reconverges in one step of the other rule). -/
theorem unifiedDefinitionalRow_weaklyConfluent {scope : Nat} :
    WeaklyConfluent (@UnifiedDefinitionalRowStep scope) := by
  intro _source leftReduct rightReduct leftStep rightStep
  rcases leftStep with leftUniv | leftDemo
  · rcases rightStep with rightUniv | rightDemo
    · exact joinableUnivToUnion
        (univalenceRowStep_confluent (ReflTransClosure.single leftUniv)
          (ReflTransClosure.single rightUniv))
    · obtain ⟨joinPoint, demoFromLeft, univFromRight⟩ :=
        univStepDemoStepCommute leftUniv rightReduct rightDemo
      exact ⟨joinPoint, ReflTransClosure.single (Or.inr demoFromLeft),
        ReflTransClosure.single (Or.inl univFromRight)⟩
  · rcases rightStep with rightUniv | rightDemo
    · obtain ⟨joinPoint, demoFromRight, univFromLeft⟩ :=
        univStepDemoStepCommute rightUniv leftReduct leftDemo
      exact ⟨joinPoint, ReflTransClosure.single (Or.inl univFromLeft),
        ReflTransClosure.single (Or.inr demoFromRight)⟩
    · exact joinableDemoToUnion (demoStep_localConfluent leftDemo rightReduct rightDemo)

/-- **★ The joint definitional row (univalence ∪ size-growing demo) is confluent (Church-Rosser) — via the
GENUINE Newman route.**  Strong normalization is the shipped joint lexicographic type-complexity measure
`lex(productFormerCount, size)` (`unifiedDefinitionalRow_wellFounded`); local confluence is the four-way peak
analysis (`unifiedDefinitionalRow_weaklyConfluent`); Newman's lemma turns SN + local confluence into global
confluence.  This is the modular-confluence capstone for definitional univalence: the no-new-redexes
univalence row and the redex-creating demo row, each confluent for opposite reasons, glue into a confluent
union with no overlap to resolve. -/
theorem unifiedDefinitionalRow_confluent {scope : Nat} :
    Confluent (@UnifiedDefinitionalRowStep scope) :=
  newman unifiedDefinitionalRow_wellFounded unifiedDefinitionalRow_weaklyConfluent

/-! ## Honest rails -/

/-- **Honesty marker.**  The joint confluence rides the GENUINE Newman route (shipped joint SN + local
confluence), NOT the `univNF` one-pass shortcut — the demo row creates redexes, so no single bottom-up pass
normalizes the union.  `= true`. -/
def fxUnifiedDefinitionalRowConfluent_viaGenuineNewman : Bool := true

/-- **Honesty marker.**  This file ships CONFLUENCE of the joint row, not yet decidable Conv by computation:
a decision procedure needs a terminating normalizer FUNCTION for the union (the demo row needs real
normalization, unlike univalence's `univNF`), which is a separate construction on top of the shipped joint
SN.  `= false`. -/
def fxUnifiedDefinitionalRowConfluent_shipsDecidableConv : Bool := false

end FX1Poly.Core
