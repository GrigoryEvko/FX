import FX1Poly.Core.RawIotaRpoBridge
import FX1Poly.Core.IotaHeadStep

/-! # FX1Poly/Core/RawIotaRpoAssembly
    — the RPO-ORIENTED root-ι fragment of the real kernel (root ι MINUS the two Phase-Z
    substituting succ-iotas) is strongly normalizing by ONE recursive path order on
    `eraseToRose`, INDEPENDENT of β and typed-SN

`IotaNonRecursiveTermination` proved the NON-recursive ι arms terminate by `RawTerm.size`.  The recursive
arms defeat every flat measure (they duplicate the eliminator on a smaller scrutinee).  A generic inductive
recursive path order (RPO) over `RoseTerm Generator` was built, proved well-founded (Nipkow/Buchholz, no
size measure), and used to orient the recursive arms on the real kernel via
`eraseToRose : RawTerm scope → RoseTerm Generator`; the RPO is then a congruence (`rpo_congruence`).

This file is the UNIFICATION, over the CANONICAL relation: the shipped `FX1Poly.Core.IotaHeadStep` (the
16-arm deterministic root-ι reduction already consumed by Tait, the weak-head normalizer, and the Path-B
convergent presentation), restricted to its RPO-ORIENTABLE 14-arm fragment `IotaOrientedHeadStep`, is shown
SN by a single `Subrelation.wf ∘ InvImage.wf eraseToRose` — recursive AND non-recursive arms in ONE order,
rather than gluing two measures (size + RPO).  `IotaHeadStep` itself stays the full canonical relation
(it keeps `toStep` and `deterministic`); this file adds the strong-normalization leg for the oriented
fragment.

## Phase-Z RPO re-scope (EXECUTED orchestrator decision)

Under the Phase-Z motive migration the natElim/natRec **successor** iotas SUBSTITUTE
(`subst (cons recursiveCall (singleton predecessor)) succBranch`) — a substitution instance is NOT
orientable by erasure (the first-order RPO has no clause comparing a same-symbol node against an arbitrary
instance of a binder body; substitution duplicates `recursiveCall`, exactly β's situation —
`betaNotOrientableByErasure`).  So those two arms JOIN the β-imported boundary and DROP OUT of the
RPO-oriented ι set:

  * `RawTerm.isNatRecursorSuccRedex` — the propext-clean root-shape guard (a `gen_natElim`/`gen_natRec`
    cell with a `natSucc`-headed scrutinee), following the `fireRootRedex` decidable-equality recipe;
  * `IotaOrientedHeadStep` — `IotaHeadStep` conjoined with the guard being `false`: the 14 oriented arms
    (10 pure-subterm + 3 applied-branch + listElim-cons, which stays a pure app-chain reassembly and so
    stays oriented; the natElim/natRec ZERO projections are pure-subterm and also stay).

The full-relation claims (`rpoEmbeds` over all 16 arms / WF of all of root ι) are no longer stateable by
erasure and are NOT claimed; root-ι chains through the substituting arms are covered by the Tait-imported
typed-SN leg, exactly like β.

## The key observation (why one richer precedence suffices)

Only the recursive listElim-cons arm and the 3 applied-branch arms (optionMatchSome / eitherMatchInl /
eitherMatchInr, reduct `app(branch, value)` with head `gen_app`) need a precedence FACT.  The other arms
have pure-subterm reducts, oriented by the RPO's subterm clauses with NO precedence requirement.  So
`iotaGenRank` bumps the eliminators to rank 2 above `gen_app` (rank 1); everything else 0 (natElim/natRec
keep their rank-2 slot for uniformity even though their remaining oriented arms — the zero projections —
are pure-subterm and need no precedence).

## What this ships

  * `iotaGenRank` / `iotaGenPrecedence` (`@[reducible]`) / `iotaGenPrecedence_wellFounded` — the unified
    ι-fragment precedence (eliminators ≻ app ≻ rest).
  * `rpoOrientsAppliedFirst` / `rpoOrientsAppliedSecond` — the two generic applied-branch orientations
    (`elim (ctor value) … branch …` RPO-dominates `app branch value`); applied branch first / second child.
  * `iotaGenRpoWellFounded` — the generic RPO well-foundedness at `iotaGenPrecedence`.
  * `RawTerm.isNatRecursorSuccRedex` / `IotaOrientedHeadStep` — the substituting-redex guard and the
    oriented 14-arm sub-relation.
  * **`IotaHeadStep.rpoEmbeds` (★)** — every NON-substituting arm of the canonical relation RPO-decreases
    the erasure (the two substituting arms are excluded by the guard hypothesis and discharge by
    `Bool.noConfusion`).
  * **`iotaOrientedHeadStep_wellFounded` (★)** — the oriented root-ι fragment is SN by `Subrelation.wf` +
    `InvImage.wf eraseToRose`, the EXACT shape of the shipped η-SN / size-SN.  Tait-free.

## Honest scope

This is the oriented ROOT-ι fragment (the redex at the root — `IotaHeadStep` is root-only by design,
mirroring `HeadStep`).  Lifting root-SN to SN of full ι-REDUCTION (ι steps inside `StepChildren` contexts)
is `RawIotaFullStepSN` — it consumes `rpo_congruence` to lift a child RPO-decrease to a node RPO-decrease.
β AND the two substituting succ-iotas stay Tait-imported (raw β is non-SN, witnessed by the Ω combinator;
the substituting iotas share β's duplication shape) — the honest boundary; η-SN is shipped separately.

## Zero-axiom verification

`iotaGenRank` uses decidable-equality `if`s (no 203-constructor wildcard match, which would leak propext);
`iotaGenPrecedence` is `@[reducible]` so the precedence facts `decide` to `Nat.lt`; the orientations are
the propext-clean `Rpo` constructors + `List.Mem` `rcases`/`nomatch`; SN is `Subrelation.wf` +
`InvImage.wf`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core.RawIotaRpo
open FX1Poly.Core.RpoInductive

/-- Unified ι-fragment generator rank: every eliminator whose reduct is NOT a pure subterm — the recursive
ones (natElim/natRec/listElim) AND the applied-branch ones (optionMatch/eitherMatch, reduct `app(branch,
value)`) — outranks `gen_app`.  boolElim/fst/snd/idJ/idStrictRec need NO rank (pure-subterm reducts, the
subterm clauses handle them). -/
def iotaGenRank (gen : Generator) : Nat :=
  if gen = .gen_natElim ∨ gen = .gen_natRec ∨ gen = .gen_listElim
      ∨ gen = .gen_optionMatch ∨ gen = .gen_eitherMatch then 2
  else if gen = .gen_app then 1
  else 0

/-- The unified ι precedence: a smaller rank is `≺F`-below a bigger one.  Reducible so the precedence facts
(e.g. `gen_app ≺F gen_optionMatch`) decide through to `Nat.lt`. -/
@[reducible] def iotaGenPrecedence (small big : Generator) : Prop := iotaGenRank small < iotaGenRank big

theorem iotaGenPrecedence_wellFounded : WellFounded iotaGenPrecedence :=
  InvImage.wf iotaGenRank Nat.lt_wfRel.wf

/-- Applied-branch orientation, branch SECOND (optionMatchSome / eitherMatchInr): the Phase-Z
redex `elim motive otherBranch appliedBranch (ctor value)` (motive first, scrutinee LAST)
RPO-dominates `app appliedBranch value`, given `appGen ≺F elimGen`.  appliedBranch dominated as
a direct subterm (index 2); value through the `ctor` node (index 3). -/
theorem rpoOrientsAppliedSecond (prec : Generator → Generator → Prop)
    (elimGen appGen ctorGen : Generator) (hprec : prec appGen elimGen)
    (value motive otherBranch appliedBranch : RoseTerm Generator) :
    Rpo prec
      (.node elimGen [motive, otherBranch, appliedBranch, .node ctorGen [value]])
      (.node appGen [appliedBranch, value]) := by
  refine Rpo.precedence (bigSym := elimGen) (bigChildren := _) (smallSym := appGen)
    (smallChildren := _) hprec ?_
  intro smallChild membership
  rcases membership with _ | ⟨_, membershipRest⟩
  · exact Rpo.subtermEq elimGen _ appliedBranch
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  · rcases membershipRest with _ | ⟨_, membershipEmpty⟩
    · exact Rpo.subtermStrict elimGen _ value (.node ctorGen [value])
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        (Rpo.subtermEq ctorGen [value] value (List.Mem.head _))
    · nomatch membershipEmpty

/-- Applied-branch orientation, branch FIRST (eitherMatchInl).  Phase-Z layout: motive first,
scrutinee LAST; appliedBranch at index 1. -/
theorem rpoOrientsAppliedFirst (prec : Generator → Generator → Prop)
    (elimGen appGen ctorGen : Generator) (hprec : prec appGen elimGen)
    (value motive appliedBranch otherBranch : RoseTerm Generator) :
    Rpo prec
      (.node elimGen [motive, appliedBranch, otherBranch, .node ctorGen [value]])
      (.node appGen [appliedBranch, value]) := by
  refine Rpo.precedence (bigSym := elimGen) (bigChildren := _) (smallSym := appGen)
    (smallChildren := _) hprec ?_
  intro smallChild membership
  rcases membership with _ | ⟨_, membershipRest⟩
  · exact Rpo.subtermEq elimGen _ appliedBranch (List.Mem.tail _ (List.Mem.head _))
  · rcases membershipRest with _ | ⟨_, membershipEmpty⟩
    · exact Rpo.subtermStrict elimGen _ value (.node ctorGen [value])
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
        (Rpo.subtermEq ctorGen [value] value (List.Mem.head _))
    · nomatch membershipEmpty

/-- **★ The unified ι RPO is well-founded** (the generic RPO well-foundedness theorem at
`iotaGenPrecedence`). -/
theorem iotaGenRpoWellFounded : WellFounded (RpoBelow iotaGenPrecedence) :=
  rpoWellFounded iotaGenPrecedence_wellFounded

end FX1Poly.Core.RawIotaRpo

namespace FX1Poly.Core
open FX1Poly.Core.RpoInductive
open FX1Poly.Core.RawIotaRpo

/-- Root-shape guard for the two Phase-Z SUBSTITUTING succ-iota redexes: a `gen_natElim` or
`gen_natRec` cell whose scrutinee (4th child, LAST) is `natSucc`-headed.  These are exactly the
root-ι redexes whose reduct is a substitution instance (`betaNotOrientableByErasure`'s situation),
so they are EXCLUDED from the RPO-oriented ι fragment and join the β-imported boundary.  Follows
the `fireRootRedex` propext-clean recipe: decidable-equality `if`s + `▸`-cast children matches,
never a wildcard over the full `Generator` enum. -/
def RawTerm.isNatRecursorSuccRedex {scope : Nat} : RawTerm scope → Bool
  | .mkGen generator _payload children =>
    if hNatElim : generator = .gen_natElim then
      match (hNatElim ▸ children : RawTermChildren (Generator.gen_natElim.binderShifts) scope) with
      | .childCons _motive (.childCons _zeroBranch (.childCons _succBranch
          (.childCons scrutinee .childNil))) =>
        match scrutinee with
        | .mkGen scrutineeGenerator _scrutineePayload _scrutineeChildren =>
          decide (scrutineeGenerator = .gen_natSucc)
    else if hNatRec : generator = .gen_natRec then
      match (hNatRec ▸ children : RawTermChildren (Generator.gen_natRec.binderShifts) scope) with
      | .childCons _motive (.childCons _zeroBranch (.childCons _succBranch
          (.childCons scrutinee .childNil))) =>
        match scrutinee with
        | .mkGen scrutineeGenerator _scrutineePayload _scrutineeChildren =>
          decide (scrutineeGenerator = .gen_natSucc)
    else
      false

/-- The RPO-ORIENTED root-ι fragment: the canonical `IotaHeadStep` minus the two Phase-Z
substituting succ-iota arms (excluded by the `isNatRecursorSuccRedex` source guard).  14 arms:
10 pure-subterm + 3 applied-branch + the listElim-cons app-chain reassembly. -/
def IotaOrientedHeadStep {scope : Nat} (source target : RawTerm scope) : Prop :=
  IotaHeadStep source target ∧ source.isNatRecursorSuccRedex = false

/-- **★ Every NON-substituting root-ι arm of the canonical `IotaHeadStep` embeds into the unified
ι RPO** (under `iotaGenPrecedence`, via `eraseToRose`).  The unification of the size-decreasing
non-recursive leg and the RPO recursive leg: 10 subterm-reduct arms via `subtermEq`/`subtermStrict`;
3 applied-branch arms via `rpoOrientsAppliedFirst`/`Second`; the listElim-cons recursive arm via
`rpoOrientsElim3WithMotive`.  The two substituting succ-iota arms are excluded by the guard
hypothesis and discharge by `Bool.noConfusion` (the guard computes to `true` on their source shape). -/
theorem IotaHeadStep.rpoEmbeds {scope : Nat} {source target : RawTerm scope}
    (step : IotaHeadStep source target)
    (nonSubstituting : source.isNatRecursorSuccRedex = false) :
    Rpo iotaGenPrecedence (eraseToRose source) (eraseToRose target) := by
  cases step with
  | iotaBoolTrue =>
      dsimp only [eraseToRose, eraseChildren]
      exact Rpo.subtermEq Generator.gen_boolElim _ _ (List.Mem.tail _ (List.Mem.head _))
  | iotaBoolFalse =>
      dsimp only [eraseToRose, eraseChildren]
      exact Rpo.subtermEq Generator.gen_boolElim _ _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  | iotaFstPair =>
      dsimp only [eraseToRose, eraseChildren]
      exact Rpo.subtermStrict Generator.gen_fst _ _ (.node Generator.gen_pair [_, _])
        (List.Mem.head _) (Rpo.subtermEq Generator.gen_pair _ _ (List.Mem.head _))
  | iotaSndPair =>
      dsimp only [eraseToRose, eraseChildren]
      exact Rpo.subtermStrict Generator.gen_snd _ _ (.node Generator.gen_pair [_, _])
        (List.Mem.head _) (Rpo.subtermEq Generator.gen_pair _ _ (List.Mem.tail _ (List.Mem.head _)))
  | iotaNatElimZero =>
      dsimp only [eraseToRose, eraseChildren]
      exact Rpo.subtermEq Generator.gen_natElim _ _ (List.Mem.tail _ (List.Mem.head _))
  | iotaNatRecZero =>
      dsimp only [eraseToRose, eraseChildren]
      exact Rpo.subtermEq Generator.gen_natRec _ _ (List.Mem.tail _ (List.Mem.head _))
  | iotaListElimNil =>
      dsimp only [eraseToRose, eraseChildren]
      exact Rpo.subtermEq Generator.gen_listElim _ _ (List.Mem.tail _ (List.Mem.head _))
  | iotaOptionMatchNone =>
      dsimp only [eraseToRose, eraseChildren]
      exact Rpo.subtermEq Generator.gen_optionMatch _ _ (List.Mem.tail _ (List.Mem.head _))
  | iotaOptionMatchSome =>
      dsimp only [eraseToRose, eraseChildren]
      exact rpoOrientsAppliedSecond iotaGenPrecedence .gen_optionMatch .gen_app .gen_optionSome
        (by decide) _ _ _ _
  | iotaEitherMatchInl =>
      dsimp only [eraseToRose, eraseChildren]
      exact rpoOrientsAppliedFirst iotaGenPrecedence .gen_eitherMatch .gen_app .gen_eitherInl
        (by decide) _ _ _ _
  | iotaEitherMatchInr =>
      dsimp only [eraseToRose, eraseChildren]
      exact rpoOrientsAppliedSecond iotaGenPrecedence .gen_eitherMatch .gen_app .gen_eitherInr
        (by decide) _ _ _ _
  | iotaNatElimSucc =>
      exact Bool.noConfusion nonSubstituting
  | iotaNatRecSucc =>
      exact Bool.noConfusion nonSubstituting
  | iotaListElimCons =>
      dsimp only [eraseToRose, eraseChildren]
      exact rpoOrientsElim3WithMotive iotaGenPrecedence .gen_listElim .gen_app .gen_listCons
        (by decide) _ _ _ _ _
  | iotaIdJRefl =>
      dsimp only [eraseToRose, eraseChildren]
      exact Rpo.subtermEq Generator.gen_idJ _ _ (List.Mem.tail _ (List.Mem.head _))
  | iotaIdStrictRecRefl =>
      dsimp only [eraseToRose, eraseChildren]
      exact Rpo.subtermEq Generator.gen_idStrictRec _ _ (List.Mem.tail _ (List.Mem.head _))

/-- Accessibility successor: `laterTerm` is below `earlierTerm` when `earlierTerm` root-ι-contracts to it
(mirrors `Step.etaSuccessor` / `IotaNonRecursiveStep.successor`).  The FULL relation's successor;
kept for statement vocabulary — its well-foundedness is NOT claimed (the substituting succ-iota
arms are not erasure-orientable). -/
def IotaHeadStep.successor {scope : Nat} (laterTerm earlierTerm : RawTerm scope) : Prop :=
  IotaHeadStep earlierTerm laterTerm

/-- Accessibility successor for the ORIENTED fragment: `laterTerm` is below `earlierTerm` when
`earlierTerm` oriented-root-ι-contracts to it. -/
def IotaOrientedHeadStep.successor {scope : Nat} (laterTerm earlierTerm : RawTerm scope) : Prop :=
  IotaOrientedHeadStep earlierTerm laterTerm

/-- **★ The oriented root-ι fragment of the real kernel is strongly normalizing — by ONE RPO, Tait-free.**
`Subrelation.wf` (every oriented root-ι step RPO-decreases the erasure, `IotaHeadStep.rpoEmbeds`) +
`InvImage.wf eraseToRose` over the well-founded `iotaGenRpoWellFounded`.  All 14 oriented ι root arms —
recursive AND non-recursive — in a single order, INDEPENDENT of β and of typed-SN.  The two Phase-Z
substituting succ-iota arms sit at the β-imported boundary (typed-SN covers them through Tait). -/
theorem iotaOrientedHeadStep_wellFounded {scope : Nat} :
    WellFounded (IotaOrientedHeadStep.successor (scope := scope)) :=
  Subrelation.wf
    (r := InvImage (RpoBelow iotaGenPrecedence) eraseToRose)
    (fun orientedStep => IotaHeadStep.rpoEmbeds orientedStep.1 orientedStep.2)
    (InvImage.wf eraseToRose iotaGenRpoWellFounded)

/-- Every raw term is oriented-root-ι strongly normalizing (accessible). -/
theorem IotaOrientedHeadStep.isStronglyNormalizing {scope : Nat} (sourceTerm : RawTerm scope) :
    Acc IotaOrientedHeadStep.successor sourceTerm :=
  iotaOrientedHeadStep_wellFounded.apply sourceTerm

/-- Non-vacuity smoke: a concrete Phase-Z `listElim` cons-redex (arity 4, motive `var 0`, scrutinee
`listCons unit listNil` LAST) is oriented-root-ι accessible AND its cons-iota genuinely belongs to the
oriented fragment (the guard computes to `false` — listElim-cons stays an app-chain reassembly, not a
substitution).  The natElim/natRec succ redexes are NOT smoked here: they sit at the β-imported boundary. -/
theorem IotaOrientedHeadStep.isStronglyNormalizing.smoke :
    Acc (IotaOrientedHeadStep.successor (scope := 0))
      (.mkGen .gen_listElim ()
        (.childCons (.mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil)
          (.childCons (.mkGen .gen_unit () .childNil)
            (.childCons (.mkGen .gen_unit () .childNil)
              (.childCons
                (.mkGen .gen_listCons ()
                  (.childCons (.mkGen .gen_unit () .childNil)
                    (.childCons (.mkGen .gen_listNil () .childNil) .childNil)))
                .childNil))))) :=
  IotaOrientedHeadStep.isStronglyNormalizing _

/-- The listElim cons-iota is genuinely IN the oriented fragment (the smoke's step fires). -/
theorem IotaOrientedHeadStep.listElimConsSmoke :
    IotaOrientedHeadStep (scope := 0)
      (.mkGen .gen_listElim ()
        (.childCons (.mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil)
          (.childCons (.mkGen .gen_unit () .childNil)
            (.childCons (.mkGen .gen_unit () .childNil)
              (.childCons
                (.mkGen .gen_listCons ()
                  (.childCons (.mkGen .gen_unit () .childNil)
                    (.childCons (.mkGen .gen_listNil () .childNil) .childNil)))
                .childNil)))))
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons (.mkGen .gen_unit () .childNil)
                  (.childCons (.mkGen .gen_unit () .childNil) .childNil)))
              (.childCons (.mkGen .gen_listNil () .childNil) .childNil)))
          (.childCons
            (.mkGen .gen_listElim ()
              (.childCons (.mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil)
                (.childCons (.mkGen .gen_unit () .childNil)
                  (.childCons (.mkGen .gen_unit () .childNil)
                    (.childCons (.mkGen .gen_listNil () .childNil) .childNil)))))
            .childNil))) :=
  ⟨IotaHeadStep.iotaListElimCons, rfl⟩

end FX1Poly.Core
