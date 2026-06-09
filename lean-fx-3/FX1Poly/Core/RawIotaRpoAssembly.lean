import FX1Poly.Core.RawIotaRpoBridge
import FX1Poly.Core.IotaHeadStep

/-! # FX1Poly/Core/RawIotaRpoAssembly
    — #1139 (Leg 3): the canonical root-ι fragment (`IotaHeadStep`) of the real kernel is strongly
    normalizing by ONE recursive path order — unifying the size-decreasing non-recursive arms (firing-67)
    and the RPO-oriented recursive arms (firing-71) into a single well-founded order on `eraseToRose`,
    INDEPENDENT of β and typed-SN

Firing-67 (`IotaNonRecursiveTermination`) proved the 13 NON-recursive ι arms terminate by `RawTerm.size`.
Firing-68 found the 3 RECURSIVE arms (natElim/natRec on succ, listElim on cons) defeat every flat measure
(they duplicate the eliminator on a smaller scrutinee).  Firings 69-71 built a generic inductive recursive
path order (RPO), proved it well-founded (Nipkow/Buchholz, no size measure), and oriented those 3 recursive
arms by it on the real kernel via `eraseToRose : RawTerm scope → RoseTerm Generator`.  Firing-72 proved the
RPO is a congruence.

This file is the UNIFICATION, over the CANONICAL relation: the shipped `FX1Poly.Core.IotaHeadStep` (the
16-arm deterministic root-ι reduction already consumed by Tait, the weak-head normalizer, and the Path-B
convergent presentation) is shown SN by a single `Subrelation.wf ∘ InvImage.wf eraseToRose` — ALL 16 arms,
recursive AND non-recursive, in ONE order, rather than gluing two measures (size + RPO).  No new ι relation
is introduced; `IotaHeadStep` already carries `toStep` (soundness) and `deterministic`, so this adds exactly
the missing strong-normalization leg.

## The key observation (why one richer precedence suffices)

Only 5 of the 16 arms need a precedence FACT:

  * the 3 recursive arms (natElim/natRec/listElim ≻ app, as in firing-71), and
  * the 3 applied-branch arms (optionMatchSome / eitherMatchInl / eitherMatchInr), whose reduct
    `app(branch, value)` has head `gen_app` — which under firing-71's `realGenPrecedence` OUTRANKS the redex
    head optionMatch/eitherMatch (rank 0), the wrong direction.

The other 10 arms have pure-subterm reducts (a direct or nested child of the redex), oriented by the RPO's
subterm clauses with NO precedence requirement.  So `iotaGenRank` bumps optionMatch and eitherMatch to rank 2
(alongside the recursive eliminators), above `gen_app` (rank 1); everything else 0.  The firing-71
`rpoOrientsElim2`/`rpoOrientsElim3` are precedence-POLYMORPHIC, so the 3 recursive arms re-orient under the
new precedence for free.

## What this ships

  * `iotaGenRank` / `iotaGenPrecedence` (`@[reducible]`) / `iotaGenPrecedence_wellFounded` — the unified
    ι-fragment precedence (recursive + applied-branch eliminators ≻ app ≻ rest).
  * `rpoOrientsAppliedFirst` / `rpoOrientsAppliedSecond` — the two generic applied-branch orientations
    (`elim (ctor value) … branch …` RPO-dominates `app branch value`); applied branch first / second child.
  * `iotaGenRpoWellFounded` — firing-70's generic WF at `iotaGenPrecedence`.
  * **`IotaHeadStep.rpoEmbeds` (★)** — every one of the canonical relation's 16 arms RPO-decreases the
    erasure (10 subterm + 3 applied-branch + 3 recursive); the unification of firing-67 and firing-71.
  * **`iotaHeadStep_wellFounded` (★)** — the canonical root-ι fragment is SN by `Subrelation.wf` +
    `InvImage.wf eraseToRose`, the EXACT shape of the shipped η-SN / size-SN.  All 16 arms, one order,
    Tait-free.

## Honest scope

This is the full root-ι fragment (the redex at the root — `IotaHeadStep` is root-only by design, mirroring
`HeadStep`).  Lifting root-SN to SN of full ι-REDUCTION (ι steps inside `StepChildren` contexts) is the next
layer — it consumes firing-72's `rpo_congruence` to lift a child RPO-decrease to a node RPO-decrease.  β
stays Tait-imported (raw β non-SN, Ω, SN-NECESSITY #950) — #1139's honest boundary; η-SN is shipped (#357).

## Zero-axiom verification

`iotaGenRank` uses decidable-equality `if`s (no 194-constructor wildcard match, which would leak propext);
`iotaGenPrecedence` is `@[reducible]` so the precedence facts `decide` to `Nat.lt`; the orientations are
firing-69's propext-clean `Rpo` constructors + `List.Mem` `rcases`/`nomatch`; SN is `Subrelation.wf` +
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

/-- Applied-branch orientation, branch SECOND (optionMatchSome / eitherMatchInr): the redex
`elim (ctor value) otherBranch appliedBranch` RPO-dominates `app appliedBranch value`, given `appGen ≺F
elimGen`.  appliedBranch dominated as a direct subterm; value through the `ctor` node. -/
theorem rpoOrientsAppliedSecond (prec : Generator → Generator → Prop)
    (elimGen appGen ctorGen : Generator) (hprec : prec appGen elimGen)
    (value otherBranch appliedBranch : RoseTerm Generator) :
    Rpo prec
      (.node elimGen [.node ctorGen [value], otherBranch, appliedBranch])
      (.node appGen [appliedBranch, value]) := by
  refine Rpo.precedence (bigSym := elimGen) (bigChildren := _) (smallSym := appGen)
    (smallChildren := _) hprec ?_
  intro smallChild membership
  rcases membership with _ | ⟨_, membershipRest⟩
  · exact Rpo.subtermEq elimGen _ appliedBranch (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  · rcases membershipRest with _ | ⟨_, membershipEmpty⟩
    · exact Rpo.subtermStrict elimGen _ value (.node ctorGen [value]) (List.Mem.head _)
        (Rpo.subtermEq ctorGen [value] value (List.Mem.head _))
    · nomatch membershipEmpty

/-- Applied-branch orientation, branch FIRST (eitherMatchInl). -/
theorem rpoOrientsAppliedFirst (prec : Generator → Generator → Prop)
    (elimGen appGen ctorGen : Generator) (hprec : prec appGen elimGen)
    (value appliedBranch otherBranch : RoseTerm Generator) :
    Rpo prec
      (.node elimGen [.node ctorGen [value], appliedBranch, otherBranch])
      (.node appGen [appliedBranch, value]) := by
  refine Rpo.precedence (bigSym := elimGen) (bigChildren := _) (smallSym := appGen)
    (smallChildren := _) hprec ?_
  intro smallChild membership
  rcases membership with _ | ⟨_, membershipRest⟩
  · exact Rpo.subtermEq elimGen _ appliedBranch (List.Mem.tail _ (List.Mem.head _))
  · rcases membershipRest with _ | ⟨_, membershipEmpty⟩
    · exact Rpo.subtermStrict elimGen _ value (.node ctorGen [value]) (List.Mem.head _)
        (Rpo.subtermEq ctorGen [value] value (List.Mem.head _))
    · nomatch membershipEmpty

/-- **★ The unified ι RPO is well-founded** (firing-70's generic theorem at `iotaGenPrecedence`). -/
theorem iotaGenRpoWellFounded : WellFounded (RpoBelow iotaGenPrecedence) :=
  rpoWellFounded iotaGenPrecedence_wellFounded

end FX1Poly.Core.RawIotaRpo

namespace FX1Poly.Core
open FX1Poly.Core.RpoInductive
open FX1Poly.Core.RawIotaRpo

/-- **★ Every root-ι arm of the canonical `IotaHeadStep` embeds into the unified ι RPO** (under
`iotaGenPrecedence`, via `eraseToRose`).  The unification of firing-67 (size-decreasing non-recursive) and
firing-71 (RPO recursive): 10 subterm-reduct arms via `subtermEq`/`subtermStrict`; 3 applied-branch arms via
`rpoOrientsAppliedFirst`/`Second`; 3 recursive arms via the firing-71 `rpoOrientsElim2`/`rpoOrientsElim3`. -/
theorem IotaHeadStep.rpoEmbeds {scope : Nat} {source target : RawTerm scope}
    (step : IotaHeadStep source target) :
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
        (by decide) _ _ _
  | iotaEitherMatchInl =>
      dsimp only [eraseToRose, eraseChildren]
      exact rpoOrientsAppliedFirst iotaGenPrecedence .gen_eitherMatch .gen_app .gen_eitherInl
        (by decide) _ _ _
  | iotaEitherMatchInr =>
      dsimp only [eraseToRose, eraseChildren]
      exact rpoOrientsAppliedSecond iotaGenPrecedence .gen_eitherMatch .gen_app .gen_eitherInr
        (by decide) _ _ _
  | iotaNatElimSucc =>
      dsimp only [eraseToRose, eraseChildren]
      exact rpoOrientsElim2 iotaGenPrecedence .gen_natElim .gen_app .gen_natSucc (by decide) _ _ _
  | iotaNatRecSucc =>
      dsimp only [eraseToRose, eraseChildren]
      exact rpoOrientsElim2 iotaGenPrecedence .gen_natRec .gen_app .gen_natSucc (by decide) _ _ _
  | iotaListElimCons =>
      dsimp only [eraseToRose, eraseChildren]
      exact rpoOrientsElim3 iotaGenPrecedence .gen_listElim .gen_app .gen_listCons (by decide) _ _ _ _
  | iotaIdJRefl =>
      dsimp only [eraseToRose, eraseChildren]
      exact Rpo.subtermEq Generator.gen_idJ _ _ (List.Mem.head _)
  | iotaIdStrictRecRefl =>
      dsimp only [eraseToRose, eraseChildren]
      exact Rpo.subtermEq Generator.gen_idStrictRec _ _ (List.Mem.head _)

/-- Accessibility successor: `laterTerm` is below `earlierTerm` when `earlierTerm` root-ι-contracts to it
(mirrors `Step.etaSuccessor` / `IotaNonRecursiveStep.successor`). -/
def IotaHeadStep.successor {scope : Nat} (laterTerm earlierTerm : RawTerm scope) : Prop :=
  IotaHeadStep earlierTerm laterTerm

/-- **★ The canonical root-ι fragment of the real kernel is strongly normalizing — by ONE RPO, Tait-free.**
`Subrelation.wf` (every root-ι step RPO-decreases the erasure, `IotaHeadStep.rpoEmbeds`) + `InvImage.wf
eraseToRose` over the well-founded `iotaGenRpoWellFounded`.  All 16 ι root arms — recursive AND
non-recursive — in a single order, INDEPENDENT of β and of typed-SN.  This is the strong-normalization leg
the shipped `IotaHeadStep` (which already carries `toStep` and `deterministic`) was missing. -/
theorem iotaHeadStep_wellFounded {scope : Nat} :
    WellFounded (IotaHeadStep.successor (scope := scope)) :=
  Subrelation.wf
    (r := InvImage (RpoBelow iotaGenPrecedence) eraseToRose)
    (fun step => IotaHeadStep.rpoEmbeds step)
    (InvImage.wf eraseToRose iotaGenRpoWellFounded)

/-- Every raw term is root-ι strongly normalizing (accessible). -/
theorem IotaHeadStep.isStronglyNormalizing {scope : Nat} (sourceTerm : RawTerm scope) :
    Acc IotaHeadStep.successor sourceTerm :=
  iotaHeadStep_wellFounded.apply sourceTerm

/-- Non-vacuity smoke: a concrete recursive redex `natElim (succ unit) unit unit` (which `iotaNatElimSucc`
-steps to its app-chain reduct) is root-ι accessible — its root-ι reductions cannot go forever. -/
theorem IotaHeadStep.isStronglyNormalizing.smoke :
    Acc (IotaHeadStep.successor (scope := 0))
      (.mkGen .gen_natElim ()
        (.childCons (.mkGen .gen_natSucc () (.childCons (.mkGen .gen_unit () .childNil) .childNil))
          (.childCons (.mkGen .gen_unit () .childNil)
            (.childCons (.mkGen .gen_unit () .childNil) .childNil)))) :=
  IotaHeadStep.isStronglyNormalizing _

end FX1Poly.Core
