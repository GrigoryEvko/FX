import LeanFX2.Term
import LeanFX2.Term.Subst
import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.RawParInversion

/-! # LeanFX2.Reducibility — Tait reducibility candidates

K12.1-K12.5 pivot: `Reducible` is a `def`-by-recursion on Ty
covering all 25 Ty constructors.  The pivot resolves the
strict-positivity wall that blocked the K12.5 inductive arrow
clause — `Reducible` recursive references descend on Ty's
sub-components via Lean's structural recursion via `Ty.rec`
(no Acc dependency, no propext leak under full enum).

## Architectural history

K12.1+K12.2 originally shipped `Reducible` as an `inductive Prop`
with a `Reducible.nat` SN closure arm.  K12.3+K12.4 added five
more closed-leaf arms (bool / unit / empty / interval / universe)
identical in shape.

K12.5 (this commit) attempted to extend the inductive with the
standard Tait function-type closure:

```
| arrow ... (closesUnderApp :
      ∀ arg, Reducible domainType arg →
             Reducible codomainType (Term.app term arg)) :
    Reducible (Ty.arrow A B) term
```

Lean 4 v4.29.1 rejected with:

```
(kernel) arg #9 of 'LeanFX2.Reducible.arrow' has a
non positive occurrence of the datatypes being declared
```

The closure's hypothesis `Reducible domainType arg` sits LEFT
of an arrow inside the constructor argument — a non-positive
occurrence the kernel rejects.  Canonical mathlib pattern:
pivot from `inductive` to `def`-by-recursion on Ty.  This works
because recursive references descend on a structurally-smaller
Ty (`domainType` and `codomainType` are proper sub-terms of
`Ty.arrow domainType codomainType`).

## The Reducible predicate (Tait 1967 / Girard 1972)

Tait/Girard define reducibility by induction on type structure:
RC at a base type is SN, RC at a function type is "maps RC to
RC", etc.  Each Ty constructor specializes the closure.

This file ships:

* `RawStep.parProgress` — non-reflexive parallel reduction
  (par AND source ≠ target).  Sidesteps the `RawStep.par.refl`
  trivial loop in the SN encoding.
* `RawTerm.isStronglyNormalizing` — inductive Prop closure
  under non-trivial parallel reduction.  Same shape as Lean's
  `Acc` but emits its own recursor, no Acc dependency
  (satisfies `GatesCore.acc_dependent_budget` 0).
* `Term.isStronglyNormalizing` — typed SN as raw SN of the
  term's raw projection.
* `Reducible` — def-by-recursion on Ty with one arm per
  constructor (25 total).  Closed leaves use SN (Tait's
  base-type clause); arrow uses the corrected Wood/Atkey 2022
  closure under application bundled with SN.

## Arm-by-arm semantics

* **Closed leaves** (unit / bool / nat / empty / interval /
  universe / tyVar): `Term.isStronglyNormalizing term`.
  Matches Tait's base-type clause — no function structure
  forces recursion into sub-types.
* **arrow A B** (K12.5): `SN(term) ∧ ∀ arg, Reducible A arg →
  Reducible B (Term.app term arg)`.  Bundles SN with the
  closure for use by the fundamental lemma.
* **piTy A B** (K12.6, weak closure): `SN(term) ∧ ∀ arg,
  Reducible A arg → SN(Term.appPi term arg)`.  The full Tait
  clause `Reducible (B.subst0 A arg) (Term.appPi term arg)`
  fails structural recursion (substituted codomain is not a
  strict sub-term), so K12.6 ships the weak variant.  Stronger
  than SN-fallback (preserves SN under reducible application);
  weaker than the full Tait clause (no Reducible at the
  substituted codomain).  Full closure reserved for a future
  Kripke logical relation refactor.
* **sigmaTy A B** (K12.7, asymmetric closure): `SN(term) ∧
  Reducible A (Term.fst term) ∧ SN(Term.snd term)`.  Asymmetric
  because `firstType` IS a strict sub-term of `Ty.sigmaTy
  firstType secondType` (so full Reducible recurses), but the
  snd projection's type is `secondType.subst0 firstType ...`
  (substituted, same wall as K12.6 piTy codomain).  Full
  Reducible-snd closure reserved for the Kripke refactor.
* **listType A** / **optionType A** / **eitherType L R**
  (K12.8, weak elim closure per parametric inductive):
  `SN(term) ∧ ∀ motiveType branches, (Reducible-arg → SN-applied
  on each elimination branch) → SN(elimResult)`.  Each
  parametric type's element / left / right sub-Ty IS a strict
  sub-term, so full Reducible recurses through the branch
  hypothesis; the motiveType is arbitrary (NOT structural sub-Ty),
  so the conclusion demotes to SN of the eliminator result.
  Mirrors K12.6 piTy weak closure pattern.  Full Reducible-at-
  motiveType closure reserved for Kripke logical relation refactor.
* **id carrier left right** (K12.9, weak idJ closure):
  `SN(witness) ∧ ∀ motiveType baseCase, SN(baseCase) →
  SN(Term.idJ baseCase witness)`.  The id-eliminator's output
  type is arbitrary (motiveType), NOT a structural sub-Ty of
  `Ty.id _ _ _`, so the conclusion demotes to SN.  Carrier is a
  strict sub-Ty but doesn't appear directly in idJ's argument
  signature (only in the id-type's own structure).  Mirrors
  K12.6 piTy weak-closure pattern.  Full Reducible-motive
  closure reserved for the Kripke logical relation refactor.
* **oeq carrier left right** / **idStrict carrier left right**
  (K12.10, weak J closures): same shape as K12.9 RC.id — SN of
  witness + (SN baseCase → SN(Term.oeqJ baseCase witness)) for
  oeq, and analogously with `Term.idStrictRec` for idStrict.
  The idStrict arm additionally universally quantifies a
  `mode = Mode.strict` witness; when the ambient mode ≠ strict,
  this is uninhabited and the inner ∀ is vacuous.
* **equiv carrierA carrierB** (K12.11, FULL Reducible closure):
  `SN(equivTerm) ∧ ∀ arg, Reducible carrierA arg → Reducible
  carrierB (Term.equivApp equivTerm arg)`.  Both carrierA and
  carrierB are strict sub-Ty of `Ty.equiv carrierA carrierB`,
  so the closure recurses Reducible on BOTH sides — exact mirror
  of K12.5 RC.arrow, not the K12.6 weak shape.
* **path carrier left right** (K12.12, full-output closure):
  `SN(pathTerm) ∧ ∀ (modeIsUnivalent), ∀ intervalTerm, SN(interval)
  → Reducible carrier (Term.pathApp pathTerm intervalTerm)`.  The
  carrier IS strict sub-Ty so the output recurses Reducible.  The
  input intervalTerm uses SN rather than `Reducible Ty.interval` —
  `Ty.interval` is a sibling Ty constructor, NOT structural
  sub-Ty of `Ty.path _ _ _`, so the recursion checker rejects
  the recursive call.  Per K12.4, the demotion is propositionally
  equivalent.
* **glue baseType boundaryWitness** (K12.12, full glueElim
  closure): `SN(gluedValue) ∧ ∀ (modeIsUnivalent), Reducible
  baseType (Term.glueElim gluedValue)`.  baseType IS strict
  sub-Ty so full Reducible on the projection result.  Even
  simpler than path (no arg quantifier).
* **modal modalityTag carrierType** (K12.13, Layer-1 documented
  SN-fallback): SN-only closure.  Layer 1 kernel ships modal
  ctors (modIntro / modElim / subsume) as raw-side scaffolding —
  none currently produces `Ty.modal _ _`-typed values.  The
  modal type former exists but is uninhabited at the typed
  layer.  Layer 6 (#1716 + #1689-1691) will add typed
  `Term.modIntroCross` / `Term.modElimCross` producing
  `Ty.modal modality carrierType` values, plus 8-modality
  dispatch; K12.13.layer6 will then ship the per-modality Tait
  closure.
* **refine baseType predicate** (K12.14, full refineElim
  closure): `SN(refinedValue) ∧ Reducible baseType
  (Term.refineElim refinedValue)`.  Plain projection — no mode
  constraint, no quantifier.  Structurally identical to K12.12
  glue.  Decidable-predicate-discharge aspect is Layer 5
  (#1342 / #1344), orthogonal to RC closure.
* **record singleFieldType** (K12.15, full recordProj closure):
  `SN(recordValue) ∧ Reducible singleFieldType
  (Term.recordProj recordValue)`.  Plain projection — same shape
  as K12.14 refine / K12.12 glue.
* **codata stateType outputType** (K12.15, full codataDest
  closure): `SN(codataValue) ∧ Reducible outputType
  (Term.codataDest codataValue)`.  Plain projection to outputType
  (stateType doesn't appear in any current eliminator).
* **session protocolStep** (K12.15, Layer-1 SN-fallback):
  Layer-1 ships only type-preserving `sessionSend`/`sessionRecv`
  congruence ctors; protocol-state advancement awaits Sessions
  layer (#1268 K09).
* **effect carrierType effectTag** (K12.15, Layer-1 SN-fallback):
  Layer-1 ships only `effectPerform` introducer; handler
  destructor awaits Effects layer (#1345-#1346 D5.9/D5.10).

The pivot keeps K12.2-K12.4's six closed-leaf arms semantically
correct (SN IS the proper Tait clause for closed-leaf types).
K12.5 adds the proper arrow closure.  K12.6+ refines the
remaining ~17 weak-SN arms incrementally.

## K12.16 — universe-cumulativity-aware reducibility (no separate arm)

The K12.16 task description ("RC.cumulUp arm: universe-
cumulativity-aware reducibility") would naively suggest a
`| Ty.cumulUp ... =>` match arm.  **But there is no
`Ty.cumulUp` constructor** — per the lean-fx-2 architectural
commitment (CLAUDE.md §Architectural commitments):

> Cumulativity is a Conv rule (Layer 3+), not a Ty constructor.

Cumulativity at the kernel lives EXCLUSIVELY at the Term level
via `Term.cumulUp`:

```
| cumulUp ... (typeCode : Term context (Ty.universe lowerLevel
    levelLeLow) codeRaw) :
    Term context (Ty.universe higherLevel levelLeHigh)
                 (RawTerm.cumulUpMarker codeRaw)
```

`Term.cumulUp` consumes a Term at `Ty.universe lowerLevel` and
produces a Term at `Ty.universe higherLevel`.  Both source and
target Ty are matched by the K12.4 universe arm in this very
definition:

```
| Ty.universe _ _, _, term => Term.isStronglyNormalizing term
```

Since `Reducible` dispatches on `Ty` (not on `Term` shape), a
cumulated term `Term.cumulUp ... typeCode` of type
`Ty.universe higherLevel _` is treated identically to any other
typed code at that universe — its Reducible-ness reduces to
SN of the cumulated form.  Universe-cumulativity-awareness is
therefore INTRINSIC to the K12.4 universe arm under the
def-by-Ty-recursion design.

What this means for the fundamental lemma (K12.18-K12.26): the
**cumulUp case** (K12.26) doesn't need to invoke a separate
`Reducible.cumulUp` arm.  Instead, it uses the structural fact
that SN is preserved by `Term.cumulUp` (which is a single par-
step that doesn't introduce new redexes; verifiable from
`RawStep.par` rules at K12.1).  Specifically:

```
Reducible (Ty.universe lower) typeCode
  ⇔ Term.isStronglyNormalizing typeCode  (by K12.4)
  ⇒ Term.isStronglyNormalizing (Term.cumulUp lower higher ...
                                              typeCode)
  ⇔ Reducible (Ty.universe higher) (Term.cumulUp ...)  (by K12.4)
```

So the cumulativity-preservation lemma is `SN-preserved-under-
cumulUp` (a small Reduction/Compat-level lemma), not a separate
RC arm.  K12.16 ships **architectural documentation** locking
in this design and pointing the fundamental-lemma cumulUp case
at the right shipping mechanism (SN-preservation lemma at the
Reduction layer, not RC closure tightening).

This documented absence-of-arm is the honest atomic shipment
under the kernel-current architectural commitment.  No new
match arm; no docstring claiming progress that doesn't exist;
the K12.4 universe arm IS the cumulativity-aware closure.

## Wood/Atkey 2022 corrected Lam rule

Standard Tait reducibility (Tait 1967) uses the arrow closure
`∀ a, RC(A, a) → RC(B, f a)`.  Atkey 2018's original graded
Lam rule was unsound; Wood/Atkey 2022 corrected it via context
division (§6.2 of fx_design.md).  At the reducibility layer,
the closure formula is unchanged; the correction lives in the
Lam typing rule itself (`Term.lam`), not in `Reducible`.

## What ships

* `RawStep.parProgress` (def, K12.1)
* `RawTerm.isStronglyNormalizing` (inductive Prop, K12.1)
* `Term.isStronglyNormalizing` (def, K12.1)
* `Reducible` (def by recursion on 25 Ty ctors, K12.1-K12.5)

## Root status

Layer 3 metatheory (top-level `LeanFX2.Reducibility` module).
Provides foundation for the Tait SN theorem (M04 / K12.27).
K12.6-K12.16 tighten remaining weak-SN arms.  K12.18-K12.26
ship the fundamental lemma threading Reducible through Term
typing derivations.

## Task anchors

K12.1 (#1758), K12.2 (#1759), K12.3 (#1760), K12.4 (#1761),
K12.5 (#1762) in the FX task tracker.  Pairs with K12.6-K12.30
filling remaining Ty arm closures + fundamental-lemma cascade.
-/

namespace LeanFX2

/-- Non-reflexive parallel-progress reduction: a `RawStep.par`
step that fires at least one redex (source and target distinct).
Distinguishing source from target sidesteps the `RawStep.par.refl`
trivial loop. -/
def RawStep.parProgress {scope : Nat} (source target : RawTerm scope) : Prop :=
  RawStep.par source target ∧ source ≠ target

/-- Strong normalization of a raw term: inductively-defined
closure under non-trivial parallel reduction.

`isStronglyNormalizing raw` holds iff every parallel-progress
reduction `raw → target` leads to a target that is itself SN.
Equivalent to `Acc (inverse parProgress) raw` but emits its
own recursor — no Acc dependency, satisfies the kernel-tier
no-Acc discipline. -/
inductive RawTerm.isStronglyNormalizing : ∀ {scope : Nat},
    RawTerm scope → Prop
  /-- Constructor closes SN over the non-trivial reduction
  successors.  Smallest fixed point — inhabits exactly the
  well-founded part of inverse `parProgress`. -/
  | intro {scope : Nat} (raw : RawTerm scope)
      (closure : ∀ (target : RawTerm scope),
                   RawStep.parProgress raw target →
                   RawTerm.isStronglyNormalizing target) :
      RawTerm.isStronglyNormalizing raw

/-- Strong normalization of a typed term: SN of its raw
projection.  Lifts through `Term.toRaw` definitionally (the
typed `Term` carries the raw form as a structural index). -/
def Term.isStronglyNormalizing {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (_term : Term context sourceType sourceRaw) : Prop :=
  RawTerm.isStronglyNormalizing sourceRaw

/-- The Tait reducibility-candidate predicate, defined by
structural recursion on Ty.

Closed-leaf arms (unit / bool / nat / empty / interval /
universe / tyVar) use plain SN per Tait's base-type clause.
The arrow arm bundles SN with the closure under application
per Wood/Atkey 2022's corrected Lam rule.  Remaining arms
(piTy / sigmaTy / id / list / option / either / path / glue /
oeq / idStrict / equiv / refine / record / codata / session /
effect / modal) ship the SN-fallback closure; K12.6-K12.16
tighten each to its type-former-specific shape. -/
def Reducible {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    : ∀ (ty : Ty level scope) {raw : RawTerm scope},
        Term context ty raw → Prop
  -- Closed leaves (K12.2-K12.4): SN base-type clause
  | Ty.unit, _, term => Term.isStronglyNormalizing term
  | Ty.bool, _, term => Term.isStronglyNormalizing term
  | Ty.nat, _, term => Term.isStronglyNormalizing term
  | Ty.empty, _, term => Term.isStronglyNormalizing term
  | Ty.interval, _, term => Term.isStronglyNormalizing term
  | Ty.universe _ _, _, term => Term.isStronglyNormalizing term
  | Ty.tyVar _, _, term => Term.isStronglyNormalizing term
  -- Function type (K12.5): SN + closure under application
  | Ty.arrow domainType codomainType, _, functionTerm =>
      Term.isStronglyNormalizing functionTerm ∧
      ∀ {argumentRaw : RawTerm scope}
        (argumentTerm : Term context domainType argumentRaw),
        Reducible domainType argumentTerm →
        Reducible codomainType (Term.app functionTerm argumentTerm)
  -- Dependent Π type (K12.6, weak closure): SN + SN-after-app.
  -- The full Tait dep-Π closure (`Reducible (B.subst0 A arg)
  -- (Term.appPi f arg)`) recurses on the substituted codomain
  -- `B.subst0 domainType argumentRaw` — NOT a structural
  -- sub-term of `Ty.piTy A B`, so the structural-recursion
  -- checker rejects it (probed 2026-05-11: "Please use
  -- `termination_by` to specify a decreasing measure",
  -- requires WellFounded.fix → Acc, banned by GatesCore
  -- line 51).  The weak closure recurses only on `domainType`
  -- (strict sub-term) and demands SN of the result.  Stronger
  -- than pure SN-fallback (the function preserves SN under
  -- reducible argument application) but weaker than the full
  -- Tait clause.  The full closure ships in a future Kripke
  -- logical relation refactor (reserve K12.6.full for that).
  | Ty.piTy domainType _, _, functionTerm =>
      Term.isStronglyNormalizing functionTerm ∧
      ∀ {argumentRaw : RawTerm scope}
        (argumentTerm : Term context domainType argumentRaw),
        Reducible domainType argumentTerm →
        Term.isStronglyNormalizing (Term.appPi functionTerm argumentTerm)
  -- Dependent Σ type (K12.7, asymmetric closure): SN + full
  -- Reducible on fst projection (firstType IS a strict sub-term
  -- of `Ty.sigmaTy firstType secondType`, so structural recursion
  -- works) + weak SN on snd projection (its type is
  -- `secondType.subst0 firstType (RawTerm.fst pairRaw)` — same
  -- substituted-sub-term wall as K12.6's piTy codomain).  Full
  -- Reducible-snd closure ships in the future Kripke logical
  -- relation refactor.
  | Ty.sigmaTy firstType _, _, pairTerm =>
      Term.isStronglyNormalizing pairTerm ∧
      Reducible firstType (Term.fst pairTerm) ∧
      Term.isStronglyNormalizing (Term.snd pairTerm)
  -- Remaining type formers (K12.11-K12.16 TODO): SN-fallback
  -- HoTT propositional identity type (K12.9, weak idJ closure).
  -- The id-eliminator `Term.idJ` consumes a witness at
  -- `Ty.id carrier leftEndpoint rightEndpoint` and a baseCase at an
  -- arbitrary motiveType, producing `motiveType`.  motiveType is NOT
  -- a structural sub-Ty of `Ty.id _ _ _` (eliminator-output types
  -- never are), so Reducible at motiveType is banned by the
  -- structural-recursion-on-Ty checker.  Carrier IS a strict sub-Ty,
  -- but doesn't appear in idJ's argument signature directly — only in
  -- the id-type's own structure.  The weak closure: SN(witness) +
  -- (baseCase SN → SN(idJ baseCase witness)).  Mirrors K12.6 piTy
  -- weak-closure pattern.  Full Reducible-motive closure reserved for
  -- the Kripke logical relation refactor (Abel-Öhman-Vezzosi POPL'18
  -- style — paired-environment recursion sidesteps the sub-Ty wall).
  | Ty.id _ _ _, _, witness =>
      Term.isStronglyNormalizing witness ∧
      ∀ {motiveType : Ty level scope}
        {baseRaw : RawTerm scope}
        (baseCase : Term context motiveType baseRaw),
        Term.isStronglyNormalizing baseCase →
        Term.isStronglyNormalizing (Term.idJ baseCase witness)
  -- Parametric inductive: list (K12.8, weak elim closure).  Mirrors
  -- K12.6 piTy's "Reducible-arg → SN result" weak-Tait pattern.
  -- The eliminator `Term.listElim` returns at an arbitrary motiveType
  -- (NOT a strict sub-Ty of `Ty.listType elementType`), so the
  -- structural-recursion-on-Ty checker rejects a full
  -- Reducible-at-motiveType conclusion (would need same-or-arbitrary-Ty
  -- recursion).  The weak closure recurses on `elementType` only
  -- (strict sub-Ty, full Reducible works) for the head-element witness,
  -- demotes the tail to SN (its type is `Ty.listType elementType` —
  -- SAME Ty, recursion banned), demands SN of branches and SN of the
  -- elim result.  Full Reducible-tail closure reserved for the future
  -- Kripke logical relation refactor.
  | Ty.listType elementType, _, listTerm =>
      Term.isStronglyNormalizing listTerm ∧
      ∀ {motiveType : Ty level scope}
        {nilRaw consRaw : RawTerm scope}
        (nilBranch : Term context motiveType nilRaw)
        (consBranch : Term context (Ty.arrow elementType
                                      (Ty.arrow (Ty.listType elementType) motiveType)) consRaw),
        Term.isStronglyNormalizing nilBranch →
        (∀ {headRaw tailRaw : RawTerm scope}
           (headTerm : Term context elementType headRaw)
           (tailTerm : Term context (Ty.listType elementType) tailRaw),
           Reducible elementType headTerm →
           Term.isStronglyNormalizing tailTerm →
           Term.isStronglyNormalizing
             (Term.app (Term.app consBranch headTerm) tailTerm)) →
        Term.isStronglyNormalizing (Term.listElim listTerm nilBranch consBranch)
  -- Parametric inductive: option (K12.8, weak elim closure).  Cleanest
  -- of the three K12.8 arms: someBranch's type `Ty.arrow elementType
  -- motiveType` matches K12.6 piTy weak closure shape exactly when
  -- restricted to elementType (strict sub-Ty).  Demands SN of noneBranch
  -- and Reducible-arg → SN-applied of someBranch, yields SN of the
  -- optionMatch result.
  | Ty.optionType elementType, _, optionTerm =>
      Term.isStronglyNormalizing optionTerm ∧
      ∀ {motiveType : Ty level scope}
        {noneRaw someRaw : RawTerm scope}
        (noneBranch : Term context motiveType noneRaw)
        (someBranch : Term context (Ty.arrow elementType motiveType) someRaw),
        Term.isStronglyNormalizing noneBranch →
        (∀ {valueRaw : RawTerm scope}
           (valueTerm : Term context elementType valueRaw),
           Reducible elementType valueTerm →
           Term.isStronglyNormalizing (Term.app someBranch valueTerm)) →
        Term.isStronglyNormalizing
          (Term.optionMatch optionTerm noneBranch someBranch)
  -- Parametric inductive: either (K12.8, symmetric weak elim closure).
  -- Symmetric in leftType / rightType (both strict sub-Ty of
  -- `Ty.eitherType leftType rightType`); each branch is
  -- `Ty.arrow leftType motiveType` / `Ty.arrow rightType motiveType`
  -- matching the K12.6 piTy weak shape per branch.  Demands
  -- Reducible-arg → SN-applied on each side, yields SN of the
  -- eitherMatch result.
  | Ty.eitherType leftType rightType, _, eitherTerm =>
      Term.isStronglyNormalizing eitherTerm ∧
      ∀ {motiveType : Ty level scope}
        {leftRaw rightRaw : RawTerm scope}
        (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
        (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw),
        (∀ {valueRaw : RawTerm scope}
           (valueTerm : Term context leftType valueRaw),
           Reducible leftType valueTerm →
           Term.isStronglyNormalizing (Term.app leftBranch valueTerm)) →
        (∀ {valueRaw : RawTerm scope}
           (valueTerm : Term context rightType valueRaw),
           Reducible rightType valueTerm →
           Term.isStronglyNormalizing (Term.app rightBranch valueTerm)) →
        Term.isStronglyNormalizing
          (Term.eitherMatch eitherTerm leftBranch rightBranch)
  -- Cubical path (K12.12, full-output pathApp closure).
  -- `Ty.path carrier left right` has carrier as strict sub-Ty and
  -- endpoints as RawTerm.  The eliminator `Term.pathApp` consumes
  -- the path + an interval term, produces a result at carrier
  -- (strict sub-Ty).  The closure recurses Reducible on carrier
  -- (strict sub-Ty ✓), but demands only SN on intervalTerm rather
  -- than Reducible at Ty.interval — Ty.interval is a sibling
  -- constructor of Ty, NOT a structural sub-Ty of Ty.path, so the
  -- structural-recursion-on-Ty checker rejects a `Reducible
  -- Ty.interval` call here.  Per K12.4's closed-leaf arm,
  -- `Reducible Ty.interval _ = Term.isStronglyNormalizing _`, so the
  -- SN demotion is propositionally equivalent to the full Tait
  -- form.  `modeIsUnivalent : mode = Mode.univalent` is universally
  -- quantified — vacuous in non-univalent modes.
  | Ty.path carrier _ _, _, pathTerm =>
      Term.isStronglyNormalizing pathTerm ∧
      ∀ (modeIsUnivalent : mode = Mode.univalent)
        {intervalRaw : RawTerm scope}
        (intervalTerm : Term context Ty.interval intervalRaw),
        Term.isStronglyNormalizing intervalTerm →
        Reducible carrier
          (Term.pathApp modeIsUnivalent pathTerm intervalTerm)
  -- CCHM Glue (K12.12, full glueElim closure).  `Ty.glue baseType
  -- boundaryWitness` has baseType as strict sub-Ty.  The eliminator
  -- `Term.glueElim` is a simple projection: consumes the glued value,
  -- produces a result at baseType.  Even simpler closure than path
  -- (no quantifier over argument): SN(gluedValue) + Reducible at
  -- baseType for the projection result.  Mode-univalent constraint
  -- universally quantified per the K12.10 idStrict pattern.
  | Ty.glue baseType _, _, gluedValue =>
      Term.isStronglyNormalizing gluedValue ∧
      ∀ (modeIsUnivalent : mode = Mode.univalent),
        Reducible baseType
          (Term.glueElim modeIsUnivalent gluedValue)
  -- HoTT observational equality (K12.10, weak oeqJ closure).
  -- Ty.oeq mirrors Ty.id's shape exactly: carrier (strict sub-Ty) +
  -- two RawTerm endpoints.  The oeq-eliminator `Term.oeqJ` has the
  -- same shape as `Term.idJ` — consumes a witness and a baseCase at
  -- an arbitrary motiveType, produces motiveType.  Same K12.6 / K12.9
  -- weak closure pattern: SN(witness) + (SN baseCase → SN(oeqJ
  -- baseCase witness)).
  | Ty.oeq _ _ _, _, witness =>
      Term.isStronglyNormalizing witness ∧
      ∀ {motiveType : Ty level scope}
        {baseRaw : RawTerm scope}
        (baseCase : Term context motiveType baseRaw),
        Term.isStronglyNormalizing baseCase →
        Term.isStronglyNormalizing (Term.oeqJ baseCase witness)
  -- Strict identity type (K12.10, weak idStrictRec closure).
  -- Ty.idStrict mirrors Ty.id's shape but the eliminator
  -- `Term.idStrictRec` requires a `mode = Mode.strict` witness.  The
  -- closure quantifies that witness universally — when the ambient
  -- mode ≠ Mode.strict, the equation is uninhabited and the inner
  -- ∀ is vacuous (closure reduces to SN(witness) alone).  Same
  -- K12.6 / K12.9 weak-J pattern in the strict-mode branch.
  | Ty.idStrict _ _ _, _, witness =>
      Term.isStronglyNormalizing witness ∧
      ∀ (modeIsStrict : mode = Mode.strict)
        {motiveType : Ty level scope}
        {baseRaw : RawTerm scope}
        (baseCase : Term context motiveType baseRaw),
        Term.isStronglyNormalizing baseCase →
        Term.isStronglyNormalizing
          (Term.idStrictRec modeIsStrict baseCase witness)
  -- Type equivalence (K12.11, full Reducible closure via equivApp).
  -- `Ty.equiv carrierA carrierB` has BOTH carrierA and carrierB as
  -- strict sub-Ty, and `Term.equivApp` mirrors `Term.app` exactly:
  -- takes the equivalence + an argument at carrierA, produces a
  -- result at carrierB.  Both Reducible recursions descend on strict
  -- sub-Ty, so the closure can demand FULL Reducible on both sides
  -- (no SN-fallback needed — same shape as K12.5 RC.arrow).
  -- Heterogeneous equivalence laws (left/right inverse) live INSIDE
  -- equivIntroHet's construction and are not exposed as eliminators;
  -- so the equivApp-driven closure captures the full computational
  -- content available at the kernel layer.
  | Ty.equiv carrierA carrierB, _, equivTerm =>
      Term.isStronglyNormalizing equivTerm ∧
      ∀ {argumentRaw : RawTerm scope}
        (argumentTerm : Term context carrierA argumentRaw),
        Reducible carrierA argumentTerm →
        Reducible carrierB (Term.equivApp equivTerm argumentTerm)
  -- Refinement type (K12.14, full refineElim closure).
  -- `Ty.refine baseType predicate` has baseType as strict sub-Ty
  -- and predicate as a RawTerm-binder (no typed dependency at the
  -- Reducible layer).  `Term.refineElim` is a pure projection from
  -- `Ty.refine _ _` to baseType — no mode constraint, no
  -- quantifier overhead.  Structurally identical to K12.12
  -- Ty.glue's full-output closure: SN(refinedValue) + Reducible
  -- baseType (Term.refineElim refinedValue).  The "Decidable
  -- predicate discharge" aspect of K12.14 lives at Layer 5 SMT-
  -- recheck (#1342 D5.6, #1344 D5.8 SMTCert) — orthogonal to the
  -- Reducibility-candidate closure shipped here.
  | Ty.refine baseType _, _, refinedValue =>
      Term.isStronglyNormalizing refinedValue ∧
      Reducible baseType (Term.refineElim refinedValue)
  -- Single-field record (K12.15, full recordProj closure).
  -- `Ty.record singleFieldType` has singleFieldType as strict sub-Ty.
  -- `Term.recordProj` projects to singleFieldType — same structure
  -- as K12.14 refine / K12.12 glue.  Multi-field records compose
  -- via nested single-field records (per Term.lean docstring),
  -- preserving this closure shape under nesting.
  | Ty.record singleFieldType, _, recordValue =>
      Term.isStronglyNormalizing recordValue ∧
      Reducible singleFieldType (Term.recordProj recordValue)
  -- Codata (K12.15, full codataDest closure).  `Ty.codata stateType
  -- outputType` has BOTH stateType and outputType as strict sub-Ty.
  -- `Term.codataDest` projects to outputType (the observation type).
  -- The stateType doesn't appear in any current eliminator (it's
  -- packed into the unfold/initial-state), so the closure recurses
  -- only on outputType.  Productivity-checking at higher
  -- observation depths lives at the codata-corecursion Layer
  -- (#1267 K08), orthogonal to this RC closure.
  | Ty.codata _ outputType, _, codataValue =>
      Term.isStronglyNormalizing codataValue ∧
      Reducible outputType (Term.codataDest codataValue)
  -- Session protocol (K12.15, Layer-1 documented SN-fallback).
  -- `Ty.session protocolStep` has protocolStep as a RawTerm — no
  -- typed sub-Ty exposed at the Ty layer.  Layer 1 ships
  -- `Term.sessionSend` / `Term.sessionRecv` as type-PRESERVING
  -- congruence-only ctors: both produce `Term ctx (Ty.session
  -- protocolStep) _` from inputs at the same session type, not a
  -- strict sub-Ty.  No projection eliminator at Layer 1 — the
  -- session protocol-state advancement (send → recv → end via
  -- duality) lives at the Sessions layer (#1268 K09 - implement
  -- session types at kernel).  K12.15.layer-sessions will then
  -- ship per-step closures via the Sessions.advance eliminator.
  | Ty.session _, _, sessionTerm =>
      Term.isStronglyNormalizing sessionTerm
  -- Effectful type (K12.15, Layer-1 documented SN-fallback).
  -- `Ty.effect carrierType effectTag` has carrierType as a strict
  -- sub-Ty in principle, but Layer 1 ships ONLY the
  -- `Term.effectPerform` introducer — no `Term.effectHandle`
  -- destructor projecting to carrierType exists yet.  The effect-
  -- handler / row-discharge semantics belong to the Effects layer
  -- (#1345 D5.9 Effects/Foundation.lean Op+EffectRow+effectPerform+
  -- effectHandle infrastructure, #1346 D5.10 Effects/Step.lean
  -- handler reduction theorems).  When Layer 5 Effects lands,
  -- K12.15.layer-effects will tighten this arm to
  -- `SN(term) ∧ ∀ handlerImpl, Reducible carrierType
  -- (Term.effectHandle term handlerImpl)`.
  | Ty.effect _ _, _, effectTerm =>
      Term.isStronglyNormalizing effectTerm
  -- Modal type (K12.13, Layer-1 SN-fallback with Layer-6 deferral).
  -- `Ty.modal modalityTag carrierType` has carrierType as a strict
  -- sub-Ty, so structural recursion would admit a `Reducible
  -- carrierType _` call in principle.  HOWEVER, the current kernel
  -- (Layer 1) ships modal ctors as RAW-SIDE SCAFFOLDING ONLY:
  -- `Term.modIntro innerTerm : Term ctx innerType (RawTerm.modIntro
  -- innerRaw)` preserves innerType rather than producing
  -- `Ty.modal _ innerType`.  Consequently, NO Term ctor at the
  -- typed layer currently inhabits `Ty.modal _ _` — the type
  -- former exists, but the typed kernel has zero inhabitants of
  -- modal type.  Any putative `Reducible Ty.modal _ _ term`
  -- application is therefore vacuous at Layer 1, and SN-fallback
  -- is the maximally-meaningful closure available without new
  -- ctors.  Layer 6 (#1716 Modal/Foundation.lean +
  -- CUMUL-7.1.{1,2,3} #1689-1691) will add typed
  -- `Term.modIntroCross` / `Term.modElimCross` producing
  -- `Ty.modal modality carrierType`-typed values plus the
  -- 8-modality dispatch (♭ ⊣ ◇ ⊣ □ ⊣ ♯ chain + ghost/cap/
  -- later/clock).  K12.13.layer6 will then tighten this arm to
  -- the per-modality Tait closure (e.g. `Reducible (modal ◇ A)
  -- term := SN(term) ∧ Reducible A (Term.modElimCross term)` for
  -- positive modalities, with mode-quantified eliminators per the
  -- K12.10 idStrict pattern).
  | Ty.modal _ _, _, term => Term.isStronglyNormalizing term

/-- **K12.17 universal extraction**: every reducible term is
strongly normalizing.  Holds uniformly across all 25 Ty arms —
every Reducible body either IS `Term.isStronglyNormalizing` (for
closed-leaf arms K12.2-K12.4, SN-fallback arms K12.13/15-modal-
session-effect) or starts with it as the first conjunct (for all
type-former-specific arms K12.5-K12.15).

This is the foundational extraction lemma the fundamental-lemma
cascade (K12.18-K12.26) will invoke on every Term typing
derivation to conclude SN from the Reducible witness. -/
theorem Reducible.isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    : ∀ {ty : Ty level scope} {raw : RawTerm scope}
        {term : Term context ty raw},
        Reducible ty term → Term.isStronglyNormalizing term
  | Ty.unit, _, _, witness => witness
  | Ty.bool, _, _, witness => witness
  | Ty.nat, _, _, witness => witness
  | Ty.empty, _, _, witness => witness
  | Ty.interval, _, _, witness => witness
  | Ty.universe _ _, _, _, witness => witness
  | Ty.tyVar _, _, _, witness => witness
  | Ty.arrow _ _, _, _, witness => witness.1
  | Ty.piTy _ _, _, _, witness => witness.1
  | Ty.sigmaTy _ _, _, _, witness => witness.1
  | Ty.id _ _ _, _, _, witness => witness.1
  | Ty.listType _, _, _, witness => witness.1
  | Ty.optionType _, _, _, witness => witness.1
  | Ty.eitherType _ _, _, _, witness => witness.1
  | Ty.path _ _ _, _, _, witness => witness.1
  | Ty.glue _ _, _, _, witness => witness.1
  | Ty.oeq _ _ _, _, _, witness => witness.1
  | Ty.idStrict _ _ _, _, _, witness => witness.1
  | Ty.equiv _ _, _, _, witness => witness.1
  | Ty.refine _ _, _, _, witness => witness.1
  | Ty.record _, _, _, witness => witness.1
  | Ty.codata _ _, _, _, witness => witness.1
  | Ty.session _, _, _, witness => witness
  | Ty.effect _ _, _, _, witness => witness
  | Ty.modal _ _, _, _, witness => witness

/-- **K12.18/K12.19 substitution-reducibility predicate**: the
universal quantification target of the fundamental lemma cascade
(K12.19-K12.26).

A typed substitution `termSubst : TermSubst sourceCtx targetCtx sigma`
is *reducible* when every per-position typed term it supplies is
`Reducible` at the substituted-source-type / matched-raw view.

## Design (K12.19 refactor of K12.18)

K12.18's first cut packaged the typed witness existentially —
`∀ position, ∃ (term : Term ...), Reducible _ term`.  K12.19's audit
(2026-05-11) revealed the shape is wrong: the fundamental-lemma var
case proves `Reducible _ (Term.subst termSubst (Term.var position))`,
which definitionally reduces to `Reducible _ (termSubst position)`
because `Term.subst termSubst (.var position) = termSubst position`
by the var equation of `Term.subst` (LeanFX2/Term/Subst.lean:192).
But an existential `∃ w, Reducible _ w` cannot supply reducibility
of THAT specific term — eliminating the existential yields SOME
reducible `w`, not the canonical `termSubst position`.

K12.19 therefore reshapes the predicate to take a `TermSubst`
directly.  Now the canonical witness at each position IS
`termSubst position`, and `ReducibleSubst termSubst position`
states reducibility of that exact term.  The fundamental lemma's
var case becomes `substReducible position` (no rewriting, no
existential elimination).

The K12.18 commit's body is replaced — same predicate name, same
audit pin, same zero-axiom discipline, corrected shape.

## Fundamental lemma statement (K12.19-K12.26)

```
theorem Reducible.fundamental
    (term : Term sourceCtx ty raw)
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (substReducible : ReducibleSubst termSubst) :
    Reducible (ty.subst sigma) (Term.subst termSubst term)
```

Induction proceeds on `term`; each arm consumes `substReducible`'s
per-position witnesses to discharge IHs on sub-terms.  K12.19 ships
the var case (and base-leaf cases via "introducer is SN" lemmas);
K12.20-K12.26 ship the remaining arms.

## Constructors (forward-referenced, K12.20+)

* `ReducibleSubst.identity` — the identity TermSubst is reducible
  when "every variable is reducible at its declared type" holds.
  K12.20 ships the prerequisite once the per-Ty neutral-reducibility
  fact is in place.
* `ReducibleSubst.consSingleton` — extending a reducible TermSubst
  with a fresh Reducible argument (for β-reduction) yields a
  reducible TermSubst at the extended context.  Ships in K12.20
  alongside the Lam case (where it's first needed).
-/
def ReducibleSubst {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma) : Prop :=
  ∀ (position : Fin scope),
    Reducible ((varType sourceCtx position).subst sigma) (termSubst position)

/-- **K12.19 fundamental-lemma var case**: applying a reducible
typed substitution to a variable term yields a reducible term at
the substituted type.

Direct unpacking of `ReducibleSubst`'s universal quantification at
the given position.  The kernel-definitional reduction
`Term.subst termSubst (.var position) ⇝ termSubst position`
(`LeanFX2/Term/Subst.lean:192`) makes the body literally
`substReducible position`.

This is the foundational base case the cascade builds on; every
later K12.20-K12.26 arm threads `substReducible` through Term-ctor
recursion, ultimately bottoming out here at variable leaves. -/
theorem Reducible.fundamental_var
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substReducible : ReducibleSubst termSubst)
    (position : Fin scope) :
    Reducible ((varType sourceCtx position).subst sigma)
              (Term.subst termSubst (Term.var position)) :=
  substReducible position

/-! ## K12.19.B introducer-SN cases

For nullary introducers (unit / boolTrue / boolFalse / natZero), the
fundamental-lemma arm reduces to "the introducer is strongly
normalizing".  Each introducer is canonical: no β/ι rule fires on
it because there's no destructor chain through a nullary head, so
`RawStep.par` reduces only via `refl` (target = source).  The
`*_inv` lemmas already shipped in `Reduction/RawParInversion.lean`
make this trivial: any step is reflexive, and `parProgress`'s
source-≠-target requirement contradicts the inversion.
-/

/-- `RawTerm.unit` is strongly normalizing.  No β/ι rule has unit
as a source, so any parallel step is `refl`; `parProgress` rules
that out. -/
theorem RawTerm.unit_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.unit : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro RawTerm.unit
    (fun _ parStep =>
      (parStep.2 (RawStep.par.unit_inv parStep.1).symm).elim)

/-- `RawTerm.boolTrue` is strongly normalizing. -/
theorem RawTerm.boolTrue_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.boolTrue : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro RawTerm.boolTrue
    (fun _ parStep =>
      (parStep.2 (RawStep.par.boolTrue_inv parStep.1).symm).elim)

/-- `RawTerm.boolFalse` is strongly normalizing. -/
theorem RawTerm.boolFalse_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.boolFalse : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro RawTerm.boolFalse
    (fun _ parStep =>
      (parStep.2 (RawStep.par.boolFalse_inv parStep.1).symm).elim)

/-- `RawTerm.natZero` is strongly normalizing. -/
theorem RawTerm.natZero_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.natZero : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro RawTerm.natZero
    (fun _ parStep =>
      (parStep.2 (RawStep.par.natZero_inv parStep.1).symm).elim)

/-- **K12.19.B unit case**: substituting through `Term.unit` yields
a reducible term at `Ty.unit`.  `Term.subst termSubst Term.unit =
Term.unit` (by Term.subst's unit equation); `Reducible Ty.unit
Term.unit` unfolds to `Term.isStronglyNormalizing Term.unit`, which
is `RawTerm.unit_isStronglyNormalizing`. -/
theorem Reducible.fundamental_unit
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    Reducible ((Ty.unit : Ty level scope).subst sigma)
              (Term.subst termSubst
                (Term.unit (context := sourceCtx))) :=
  RawTerm.unit_isStronglyNormalizing

/-- **K12.19.B boolTrue case**: same shape as `fundamental_unit`. -/
theorem Reducible.fundamental_boolTrue
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    Reducible ((Ty.bool : Ty level scope).subst sigma)
              (Term.subst termSubst
                (Term.boolTrue (context := sourceCtx))) :=
  RawTerm.boolTrue_isStronglyNormalizing

/-- **K12.19.B boolFalse case**. -/
theorem Reducible.fundamental_boolFalse
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    Reducible ((Ty.bool : Ty level scope).subst sigma)
              (Term.subst termSubst
                (Term.boolFalse (context := sourceCtx))) :=
  RawTerm.boolFalse_isStronglyNormalizing

/-- **K12.19.B natZero case**. -/
theorem Reducible.fundamental_natZero
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    Reducible ((Ty.nat : Ty level scope).subst sigma)
              (Term.subst termSubst
                (Term.natZero (context := sourceCtx))) :=
  RawTerm.natZero_isStronglyNormalizing

end LeanFX2
