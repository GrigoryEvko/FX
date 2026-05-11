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

/-! ## K12.20.A unary-introducer SN preservation

K12.20 (Term.lam case of the fundamental lemma) needs three
ingredients per the standard Tait/Girard cascade:

1. **SN preservation under lam** — if body is SN then `lam body`
   is SN.  Proved here as `RawTerm.lam_isStronglyNormalizing`.
2. **ReducibleSubst.singleton + lift** — extending a reducible
   TermSubst with a fresh reducible witness (for β-redex unfolding
   `(lam body) arg ⇝ body.subst0 arg`).  Blocked on CR3
   ("neutral terms are reducible at every type") — variables in
   the lifted TermSubst's positions need to be Reducible.
3. **Closure under reduction (CR2)** — Reducible closed under
   parProgress steps.  Per-Ty case split (25 arms).

K12.20.A ships ingredient (1).  K12.20.B/C ship (2)/(3) once the
neutral-reducibility chain is set up.  The full Term.lam case
follows by combining all three.
-/

/-- `RawTerm.lam body` is strongly normalizing whenever `body` is.
Proof: every `RawStep.par` from `lam body` lands at `lam bodyTarget`
with `par body bodyTarget` (`RawStep.par.lam_inv`); the `parProgress`
disequality `lam body ≠ lam bodyTarget` forces `body ≠ bodyTarget`
(by `RawTerm.lam` injectivity), so the recursive IH on `body`'s SN
witness handles the bodyTarget case. -/
theorem RawTerm.lam_isStronglyNormalizing {scope : Nat}
    {body : RawTerm (scope + 1)}
    (bodyIsSN : RawTerm.isStronglyNormalizing body) :
    RawTerm.isStronglyNormalizing (RawTerm.lam body) := by
  induction bodyIsSN with
  | intro currentBody _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro (RawTerm.lam currentBody) ?_
    intro target progressStep
    obtain ⟨bodyTarget, targetEq, bodyStep⟩ :=
      RawStep.par.lam_inv progressStep.1
    subst targetEq
    have bodyDistinct : currentBody ≠ bodyTarget := fun bodyEq =>
      progressStep.2 (congrArg RawTerm.lam bodyEq)
    exact inductiveHypothesis bodyTarget ⟨bodyStep, bodyDistinct⟩

/-! ## K12.20.B raw-level CR2 (closure under reduction)

CR2 of Tait's three reducibility-candidate conditions: Reducible
closed under reduction.  At the raw level, this is one step removed
from SN's inductive definition — given SN of source and a progress
step source → target, the SN constructor's closure directly gives
SN of target.

CR2 at typed Reducible reduces to this raw fact for SN-direct arms
(unit / bool / nat / empty / interval / universe / tyVar / session /
effect / modal) because `Reducible Ty.X term = Term.isStronglyNormalizing
term = RawTerm.isStronglyNormalizing term.toRaw`.  The compound
arms (arrow / piTy / Σ / id / list / option / either / path / glue /
oeq / idStrict / equiv / refine / record / codata) need per-Ty
case analysis on the closure structure — those land in K12.20.B
follow-ups.
-/

/-- **K12.20.B raw CR2**: SN is preserved under parallel-progress
reduction.  Direct destructuring of the SN constructor's closure —
the closure says exactly "every progress step lands at SN target",
so we apply it to the given step. -/
theorem RawTerm.isStronglyNormalizing.step_preserves {scope : Nat}
    {source target : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source)
    (progressStep : RawStep.parProgress source target) :
    RawTerm.isStronglyNormalizing target := by
  cases sourceIsSN with
  | intro _ closure => exact closure target progressStep

/-! ## K12.20.C neutral & natSucc SN preservation

Two more raw-level SN lemmas continuing the K12.19.B/K12.20.A
pattern:

* `RawTerm.var_isStronglyNormalizing` — every variable is SN.
  Variables have no β/ι rules (no destructor fires on a variable
  head); the only `RawStep.par` from `RawTerm.var position` is
  `refl` (per `var_inv` in `RawParInversion`), so the parProgress
  disequality contradiction discharges the SN closure.  Foundational
  for CR3: variables are neutral terms with no progress steps, so
  CR3's premise is vacuously satisfied → variables are reducible at
  every SN-direct Ty arm.

* `RawTerm.natSucc_isStronglyNormalizing` — `natSucc predecessor`
  is SN whenever the predecessor is.  Same single-subterm structural
  induction as `lam_isStronglyNormalizing`: `natSucc_inv` step
  inversion + `RawTerm.natSucc` ctor-injectivity.
-/

/-- Variables are strongly normalizing.  No `RawStep.par` ctor has
a variable as source other than `refl`, so any `parProgress` step
contradicts. -/
theorem RawTerm.var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope) :
    RawTerm.isStronglyNormalizing (RawTerm.var position) :=
  RawTerm.isStronglyNormalizing.intro (RawTerm.var position)
    (fun _ progressStep =>
      (progressStep.2 (RawStep.par.var_inv progressStep.1).symm).elim)

/-- `RawTerm.natSucc predecessor` is SN when predecessor is.  Same
proof pattern as `lam_isStronglyNormalizing`: structural induction
on predecessor's SN witness + step inversion via `natSucc_inv` +
ctor-injectivity for the disequality.  `natSucc` is also a unary
cong-only ctor at parallel reduction. -/
theorem RawTerm.natSucc_isStronglyNormalizing {scope : Nat}
    {predecessor : RawTerm scope}
    (predecessorIsSN : RawTerm.isStronglyNormalizing predecessor) :
    RawTerm.isStronglyNormalizing (RawTerm.natSucc predecessor) := by
  induction predecessorIsSN with
  | intro currentPredecessor _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.natSucc currentPredecessor) ?_
    intro target progressStep
    obtain ⟨predecessorTarget, targetEq, predecessorStep⟩ :=
      RawStep.par.natSucc_inv progressStep.1
    subst targetEq
    have predecessorDistinct :
        currentPredecessor ≠ predecessorTarget := fun predecessorEq =>
      progressStep.2 (congrArg RawTerm.natSucc predecessorEq)
    exact inductiveHypothesis predecessorTarget
      ⟨predecessorStep, predecessorDistinct⟩

/-- **K12.20.W optionSome SN preservation**.  Sister to
`natSucc_isStronglyNormalizing` — unary cong-only ctor with
`optionSome_inv` for step inversion + `RawTerm.optionSome`
injectivity for the parProgress disequality. -/
theorem RawTerm.optionSome_isStronglyNormalizing {scope : Nat}
    {valueTerm : RawTerm scope}
    (valueIsSN : RawTerm.isStronglyNormalizing valueTerm) :
    RawTerm.isStronglyNormalizing (RawTerm.optionSome valueTerm) := by
  induction valueIsSN with
  | intro currentValue _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.optionSome currentValue) ?_
    intro target progressStep
    obtain ⟨valueTarget, targetEq, valueStep⟩ :=
      RawStep.par.optionSome_inv progressStep.1
    subst targetEq
    have valueDistinct :
        currentValue ≠ valueTarget := fun valueEq =>
      progressStep.2 (congrArg RawTerm.optionSome valueEq)
    exact inductiveHypothesis valueTarget
      ⟨valueStep, valueDistinct⟩

/-- **K12.20.X.1 eitherInl SN preservation**.  Sister to optionSome
helper — unary cong-only ctor at the left injection of Ty.eitherType. -/
theorem RawTerm.eitherInl_isStronglyNormalizing {scope : Nat}
    {valueTerm : RawTerm scope}
    (valueIsSN : RawTerm.isStronglyNormalizing valueTerm) :
    RawTerm.isStronglyNormalizing (RawTerm.eitherInl valueTerm) := by
  induction valueIsSN with
  | intro currentValue _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.eitherInl currentValue) ?_
    intro target progressStep
    obtain ⟨valueTarget, targetEq, valueStep⟩ :=
      RawStep.par.eitherInl_inv progressStep.1
    subst targetEq
    have valueDistinct :
        currentValue ≠ valueTarget := fun valueEq =>
      progressStep.2 (congrArg RawTerm.eitherInl valueEq)
    exact inductiveHypothesis valueTarget
      ⟨valueStep, valueDistinct⟩

/-- **K12.20.X.2 eitherInr SN preservation**.  Mirror of
`eitherInl_isStronglyNormalizing` — same template, right injection. -/
theorem RawTerm.eitherInr_isStronglyNormalizing {scope : Nat}
    {valueTerm : RawTerm scope}
    (valueIsSN : RawTerm.isStronglyNormalizing valueTerm) :
    RawTerm.isStronglyNormalizing (RawTerm.eitherInr valueTerm) := by
  induction valueIsSN with
  | intro currentValue _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.eitherInr currentValue) ?_
    intro target progressStep
    obtain ⟨valueTarget, targetEq, valueStep⟩ :=
      RawStep.par.eitherInr_inv progressStep.1
    subst targetEq
    have valueDistinct :
        currentValue ≠ valueTarget := fun valueEq =>
      progressStep.2 (congrArg RawTerm.eitherInr valueEq)
    exact inductiveHypothesis valueTarget
      ⟨valueStep, valueDistinct⟩

/-- **K12.20.Y modIntro SN preservation**.  Sister to the
optionSome / eitherInl / eitherInr helpers — unary cong-only ctor at
the modal-introduction ctor.  Powers future fundamental_modIntro at
parametric Ty.modal closures. -/
theorem RawTerm.modIntro_isStronglyNormalizing {scope : Nat}
    {innerTerm : RawTerm scope}
    (innerIsSN : RawTerm.isStronglyNormalizing innerTerm) :
    RawTerm.isStronglyNormalizing (RawTerm.modIntro innerTerm) := by
  induction innerIsSN with
  | intro currentInner _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.modIntro currentInner) ?_
    intro target progressStep
    obtain ⟨innerTarget, targetEq, innerStep⟩ :=
      RawStep.par.modIntro_inv progressStep.1
    subst targetEq
    have innerDistinct :
        currentInner ≠ innerTarget := fun innerEq =>
      progressStep.2 (congrArg RawTerm.modIntro innerEq)
    exact inductiveHypothesis innerTarget
      ⟨innerStep, innerDistinct⟩

/-- **K12.20.Z pair SN preservation** — first binary cong-only SN
helper.  Pair has two parallel subterms; the SN proof needs nested
induction (outer on firstIsSN with `generalizing` to expose
second's SN as IH input, inner on secondIsSN) plus a per-side
disequality split.  When `pair currentFirst currentSecond` steps
to `pair firstTarget secondTarget` with the pair distinct, at
least one side must have advanced; case-split on which to discharge
via the outer or inner IH. -/
theorem RawTerm.pair_isStronglyNormalizing {scope : Nat}
    {firstValue : RawTerm scope}
    (firstIsSN : RawTerm.isStronglyNormalizing firstValue) :
    ∀ {secondValue : RawTerm scope},
      RawTerm.isStronglyNormalizing secondValue →
      RawTerm.isStronglyNormalizing
        (RawTerm.pair firstValue secondValue) := by
  induction firstIsSN with
  | intro currentFirst _ firstIH =>
    intro secondValue secondIsSN
    induction secondIsSN with
    | intro currentSecond secondClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.pair currentFirst currentSecond) ?_
      intro target progressStep
      obtain ⟨firstTarget, secondTarget, targetEq, firstStep, secondStep⟩ :=
        RawStep.par.pair_inv progressStep.1
      subst targetEq
      by_cases firstEq : currentFirst = firstTarget
      · subst firstEq
        have secondDistinct : currentSecond ≠ secondTarget := fun secondEq =>
          progressStep.2 (congrArg (RawTerm.pair currentFirst) secondEq)
        exact innerIH secondTarget ⟨secondStep, secondDistinct⟩
      · have firstProgress : RawStep.parProgress currentFirst firstTarget :=
          ⟨firstStep, firstEq⟩
        by_cases secondEq : currentSecond = secondTarget
        · subst secondEq
          exact firstIH firstTarget firstProgress
            (RawTerm.isStronglyNormalizing.intro currentSecond secondClosure)
        · exact firstIH firstTarget firstProgress
            (secondClosure secondTarget ⟨secondStep, secondEq⟩)

/-- **K12.20.AA listCons SN preservation** — second binary SN
helper.  Same nested-induction + decidable-injectivity-split template
as `pair_isStronglyNormalizing`, applied to the cons-cell at the
head + tail positions of `Ty.listType`. -/
theorem RawTerm.listCons_isStronglyNormalizing {scope : Nat}
    {headTerm : RawTerm scope}
    (headIsSN : RawTerm.isStronglyNormalizing headTerm) :
    ∀ {tailTerm : RawTerm scope},
      RawTerm.isStronglyNormalizing tailTerm →
      RawTerm.isStronglyNormalizing
        (RawTerm.listCons headTerm tailTerm) := by
  induction headIsSN with
  | intro currentHead _ headIH =>
    intro tailTerm tailIsSN
    induction tailIsSN with
    | intro currentTail tailClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.listCons currentHead currentTail) ?_
      intro target progressStep
      obtain ⟨headTarget, tailTarget, targetEq, headStep, tailStep⟩ :=
        RawStep.par.listCons_inv progressStep.1
      subst targetEq
      by_cases headEq : currentHead = headTarget
      · subst headEq
        have tailDistinct : currentTail ≠ tailTarget := fun tailEq =>
          progressStep.2 (congrArg (RawTerm.listCons currentHead) tailEq)
        exact innerIH tailTarget ⟨tailStep, tailDistinct⟩
      · have headProgress : RawStep.parProgress currentHead headTarget :=
          ⟨headStep, headEq⟩
        by_cases tailEq : currentTail = tailTarget
        · subst tailEq
          exact headIH headTarget headProgress
            (RawTerm.isStronglyNormalizing.intro currentTail tailClosure)
        · exact headIH headTarget headProgress
            (tailClosure tailTarget ⟨tailStep, tailEq⟩)

/-- **K12.20.AB subsume SN preservation** — modal cumulativity cong.
Sister to `modIntro_isStronglyNormalizing` — unary cong-only ctor at
the modal-cumul-coercion position; no β rule at the raw level.
Powers future fundamental_subsume under the K12.16 Ty.cumulUp closure
chain. -/
theorem RawTerm.subsume_isStronglyNormalizing {scope : Nat}
    {innerTerm : RawTerm scope}
    (innerIsSN : RawTerm.isStronglyNormalizing innerTerm) :
    RawTerm.isStronglyNormalizing (RawTerm.subsume innerTerm) := by
  induction innerIsSN with
  | intro currentInner _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.subsume currentInner) ?_
    intro target progressStep
    obtain ⟨innerTarget, targetEq, innerStep⟩ :=
      RawStep.par.subsume_inv progressStep.1
    subst targetEq
    have innerDistinct :
        currentInner ≠ innerTarget := fun innerEq =>
      progressStep.2 (congrArg RawTerm.subsume innerEq)
    exact inductiveHypothesis innerTarget
      ⟨innerStep, innerDistinct⟩

/-- **K12.20.AC.1 listNil SN preservation** — nullary value at
parametric Ty.listType.  Sister to natZero / unit / boolTrue —
atomic ctor, only refl reduces, parProgress disequality contradicts
trivially. -/
theorem RawTerm.listNil_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.listNil : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro
    (RawTerm.listNil : RawTerm scope)
    (fun _ progressStep =>
      (progressStep.2 (RawStep.par.listNil_inv progressStep.1).symm).elim)

/-- **K12.20.AC.2 optionNone SN preservation** — nullary value at
parametric Ty.optionType.  Same atomic shape as listNil. -/
theorem RawTerm.optionNone_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing
      (RawTerm.optionNone : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro
    (RawTerm.optionNone : RawTerm scope)
    (fun _ progressStep =>
      (progressStep.2 (RawStep.par.optionNone_inv progressStep.1).symm).elim)

/-- **K12.20.AD.1 refl SN preservation** — HoTT identity-type
introduction.  Unary cong over the path witness; refl_inv discharges
each par step. -/
theorem RawTerm.refl_isStronglyNormalizing {scope : Nat}
    {rawWitness : RawTerm scope}
    (witnessIsSN : RawTerm.isStronglyNormalizing rawWitness) :
    RawTerm.isStronglyNormalizing (RawTerm.refl rawWitness) := by
  induction witnessIsSN with
  | intro currentWitness _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.refl currentWitness) ?_
    intro target progressStep
    obtain ⟨witnessTarget, targetEq, witnessStep⟩ :=
      RawStep.par.refl_inv progressStep.1
    subst targetEq
    have witnessDistinct :
        currentWitness ≠ witnessTarget := fun witnessEq =>
      progressStep.2 (congrArg RawTerm.refl witnessEq)
    exact inductiveHypothesis witnessTarget
      ⟨witnessStep, witnessDistinct⟩

/-- **K12.20.AD.2 oeqRefl SN preservation** — observational-equality
reflexivity intro.  Sister to refl helper; oeqRefl_inv discharges. -/
theorem RawTerm.oeqRefl_isStronglyNormalizing {scope : Nat}
    {witness : RawTerm scope}
    (witnessIsSN : RawTerm.isStronglyNormalizing witness) :
    RawTerm.isStronglyNormalizing (RawTerm.oeqRefl witness) := by
  induction witnessIsSN with
  | intro currentWitness _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.oeqRefl currentWitness) ?_
    intro target progressStep
    obtain ⟨witnessTarget, targetEq, witnessStep⟩ :=
      RawStep.par.oeqRefl_inv progressStep.1
    subst targetEq
    have witnessDistinct :
        currentWitness ≠ witnessTarget := fun witnessEq =>
      progressStep.2 (congrArg RawTerm.oeqRefl witnessEq)
    exact inductiveHypothesis witnessTarget
      ⟨witnessStep, witnessDistinct⟩

/-- **K12.20.AD.3 idStrictRefl SN preservation** — strict-id
reflexivity intro.  Same unary shape as refl / oeqRefl. -/
theorem RawTerm.idStrictRefl_isStronglyNormalizing {scope : Nat}
    {witness : RawTerm scope}
    (witnessIsSN : RawTerm.isStronglyNormalizing witness) :
    RawTerm.isStronglyNormalizing (RawTerm.idStrictRefl witness) := by
  induction witnessIsSN with
  | intro currentWitness _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.idStrictRefl currentWitness) ?_
    intro target progressStep
    obtain ⟨witnessTarget, targetEq, witnessStep⟩ :=
      RawStep.par.idStrictRefl_inv progressStep.1
    subst targetEq
    have witnessDistinct :
        currentWitness ≠ witnessTarget := fun witnessEq =>
      progressStep.2 (congrArg RawTerm.idStrictRefl witnessEq)
    exact inductiveHypothesis witnessTarget
      ⟨witnessStep, witnessDistinct⟩

/-- **K12.20.AE.1 interval0 SN preservation** — cubical interval
endpoint 0.  Atomic nullary, only-refl reduces, parProgress
disequality contradicts the .symm of interval0_inv. -/
theorem RawTerm.interval0_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.interval0 : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro
    (RawTerm.interval0 : RawTerm scope)
    (fun _ progressStep =>
      (progressStep.2 (RawStep.par.interval0_inv progressStep.1).symm).elim)

/-- **K12.20.AE.2 interval1 SN preservation** — cubical interval
endpoint 1.  Sister to interval0; same atomic nullary shape. -/
theorem RawTerm.interval1_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.interval1 : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro
    (RawTerm.interval1 : RawTerm scope)
    (fun _ progressStep =>
      (progressStep.2 (RawStep.par.interval1_inv progressStep.1).symm).elim)

/-- **K12.20.AN.1 interval0 fundamental case** — cubical interval
zero endpoint.  `Ty.interval` is closed (no scope dependence) so
`Ty.interval.subst sigma = Ty.interval`; `Term.subst` on the
nullary intro reduces to itself
(`LeanFX2/Term/Subst.lean:306`); `Reducible Ty.interval _`
unfolds to `Term.isStronglyNormalizing _`
(`LeanFX2/Reducibility.lean:329`).  Closes the nullary-intro
quartet alongside K12.19.B unit / boolTrue / boolFalse / natZero
with the same one-liner template. -/
theorem Reducible.fundamental_interval0
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    Reducible ((Ty.interval : Ty level scope).subst sigma)
              (Term.subst termSubst
                (Term.interval0 (context := sourceCtx))) :=
  RawTerm.interval0_isStronglyNormalizing

/-- **K12.20.AN.2 interval1 fundamental case** — cubical interval
one endpoint.  Same closed-leaf intro shape as `interval0`. -/
theorem Reducible.fundamental_interval1
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    Reducible ((Ty.interval : Ty level scope).subst sigma)
              (Term.subst termSubst
                (Term.interval1 (context := sourceCtx))) :=
  RawTerm.interval1_isStronglyNormalizing

/-- **K12.20.AF.1 intervalOpp SN preservation** — cubical interval
negation.  Unary cong over the interval term; intervalOpp_inv
discharges each par step. -/
theorem RawTerm.intervalOpp_isStronglyNormalizing {scope : Nat}
    {intervalTerm : RawTerm scope}
    (intervalIsSN : RawTerm.isStronglyNormalizing intervalTerm) :
    RawTerm.isStronglyNormalizing (RawTerm.intervalOpp intervalTerm) := by
  induction intervalIsSN with
  | intro currentInterval _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.intervalOpp currentInterval) ?_
    intro target progressStep
    obtain ⟨intervalTarget, targetEq, intervalStep⟩ :=
      RawStep.par.intervalOpp_inv progressStep.1
    subst targetEq
    have intervalDistinct :
        currentInterval ≠ intervalTarget := fun intervalEq =>
      progressStep.2 (congrArg RawTerm.intervalOpp intervalEq)
    exact inductiveHypothesis intervalTarget
      ⟨intervalStep, intervalDistinct⟩

/-- **K12.20.AF.2 intervalMeet SN preservation** — cubical interval
meet (∧).  Binary cong; uses the universal-in-conclusion trick
to keep the second-argument IH universal during induction on the
first SN witness. -/
theorem RawTerm.intervalMeet_isStronglyNormalizing {scope : Nat}
    {leftInterval : RawTerm scope}
    (leftIsSN : RawTerm.isStronglyNormalizing leftInterval) :
    ∀ {rightInterval : RawTerm scope},
      RawTerm.isStronglyNormalizing rightInterval →
      RawTerm.isStronglyNormalizing
        (RawTerm.intervalMeet leftInterval rightInterval) := by
  induction leftIsSN with
  | intro currentLeft _ leftIH =>
    intro rightInterval rightIsSN
    induction rightIsSN with
    | intro currentRight rightClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.intervalMeet currentLeft currentRight) ?_
      intro target progressStep
      obtain ⟨leftTarget, rightTarget, targetEq, leftStep, rightStep⟩ :=
        RawStep.par.intervalMeet_inv progressStep.1
      subst targetEq
      by_cases leftEq : currentLeft = leftTarget
      · subst leftEq
        have rightDistinct : currentRight ≠ rightTarget := fun rightEq =>
          progressStep.2 (congrArg (RawTerm.intervalMeet currentLeft) rightEq)
        exact innerIH rightTarget ⟨rightStep, rightDistinct⟩
      · have leftProgress : RawStep.parProgress currentLeft leftTarget :=
          ⟨leftStep, leftEq⟩
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact leftIH leftTarget leftProgress
            (RawTerm.isStronglyNormalizing.intro currentRight rightClosure)
        · exact leftIH leftTarget leftProgress
            (rightClosure rightTarget ⟨rightStep, rightEq⟩)

/-- **K12.20.AF.3 intervalJoin SN preservation** — cubical interval
join (∨).  Sister to intervalMeet; same binary cong shape. -/
theorem RawTerm.intervalJoin_isStronglyNormalizing {scope : Nat}
    {leftInterval : RawTerm scope}
    (leftIsSN : RawTerm.isStronglyNormalizing leftInterval) :
    ∀ {rightInterval : RawTerm scope},
      RawTerm.isStronglyNormalizing rightInterval →
      RawTerm.isStronglyNormalizing
        (RawTerm.intervalJoin leftInterval rightInterval) := by
  induction leftIsSN with
  | intro currentLeft _ leftIH =>
    intro rightInterval rightIsSN
    induction rightIsSN with
    | intro currentRight rightClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.intervalJoin currentLeft currentRight) ?_
      intro target progressStep
      obtain ⟨leftTarget, rightTarget, targetEq, leftStep, rightStep⟩ :=
        RawStep.par.intervalJoin_inv progressStep.1
      subst targetEq
      by_cases leftEq : currentLeft = leftTarget
      · subst leftEq
        have rightDistinct : currentRight ≠ rightTarget := fun rightEq =>
          progressStep.2 (congrArg (RawTerm.intervalJoin currentLeft) rightEq)
        exact innerIH rightTarget ⟨rightStep, rightDistinct⟩
      · have leftProgress : RawStep.parProgress currentLeft leftTarget :=
          ⟨leftStep, leftEq⟩
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact leftIH leftTarget leftProgress
            (RawTerm.isStronglyNormalizing.intro currentRight rightClosure)
        · exact leftIH leftTarget leftProgress
            (rightClosure rightTarget ⟨rightStep, rightEq⟩)

/-- **K12.20.AG pathLam SN preservation** — cubical path lambda
binder.  Sister to lam helper — body lives in `RawTerm (scope+1)`,
induction on body's SN witness discharges each par step via
pathLam_inv + congrArg-based parProgress disequality. -/
theorem RawTerm.pathLam_isStronglyNormalizing {scope : Nat}
    {body : RawTerm (scope + 1)}
    (bodyIsSN : RawTerm.isStronglyNormalizing body) :
    RawTerm.isStronglyNormalizing (RawTerm.pathLam body) := by
  induction bodyIsSN with
  | intro currentBody _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.pathLam currentBody) ?_
    intro target progressStep
    obtain ⟨bodyTarget, targetEq, bodyStep⟩ :=
      RawStep.par.pathLam_inv progressStep.1
    subst targetEq
    have bodyDistinct : currentBody ≠ bodyTarget := fun bodyEq =>
      progressStep.2 (congrArg RawTerm.pathLam bodyEq)
    exact inductiveHypothesis bodyTarget ⟨bodyStep, bodyDistinct⟩

/-- **K12.20.AI.1 uaToEquiv SN preservation** — univalence-to-
equivalence converter (D3.6 ua_β infrastructure).  Pure unary
cong over its proof witness; uaToEquiv_inv discharges. -/
theorem RawTerm.uaToEquiv_isStronglyNormalizing {scope : Nat}
    {proof : RawTerm scope}
    (proofIsSN : RawTerm.isStronglyNormalizing proof) :
    RawTerm.isStronglyNormalizing (RawTerm.uaToEquiv proof) := by
  induction proofIsSN with
  | intro currentProof _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.uaToEquiv currentProof) ?_
    intro target progressStep
    obtain ⟨proofTarget, targetEq, proofStep⟩ :=
      RawStep.par.uaToEquiv_inv progressStep.1
    subst targetEq
    have proofDistinct :
        currentProof ≠ proofTarget := fun proofEq =>
      progressStep.2 (congrArg RawTerm.uaToEquiv proofEq)
    exact inductiveHypothesis proofTarget
      ⟨proofStep, proofDistinct⟩

/-- **K12.20.AI.2 oeqFunext SN preservation** — observational
equality functional extensionality intro.  Pure unary cong over
the pointwise-equality witness. -/
theorem RawTerm.oeqFunext_isStronglyNormalizing {scope : Nat}
    {pointwiseEquality : RawTerm scope}
    (pointwiseIsSN : RawTerm.isStronglyNormalizing pointwiseEquality) :
    RawTerm.isStronglyNormalizing
      (RawTerm.oeqFunext pointwiseEquality) := by
  induction pointwiseIsSN with
  | intro currentPointwise _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.oeqFunext currentPointwise) ?_
    intro target progressStep
    obtain ⟨pointwiseTarget, targetEq, pointwiseStep⟩ :=
      RawStep.par.oeqFunext_inv progressStep.1
    subst targetEq
    have pointwiseDistinct :
        currentPointwise ≠ pointwiseTarget := fun pointwiseEq =>
      progressStep.2 (congrArg RawTerm.oeqFunext pointwiseEq)
    exact inductiveHypothesis pointwiseTarget
      ⟨pointwiseStep, pointwiseDistinct⟩

/-- **K12.20.AJ.1 recordIntro SN preservation** — record value
introduction (currently single-field representative; multi-field
records desugar to nested pairs).  Pure unary cong over the
first-field witness. -/
theorem RawTerm.recordIntro_isStronglyNormalizing {scope : Nat}
    {firstField : RawTerm scope}
    (firstFieldIsSN : RawTerm.isStronglyNormalizing firstField) :
    RawTerm.isStronglyNormalizing (RawTerm.recordIntro firstField) := by
  induction firstFieldIsSN with
  | intro currentField _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.recordIntro currentField) ?_
    intro target progressStep
    obtain ⟨firstTarget, targetEq, firstStep⟩ :=
      RawStep.par.recordIntro_inv progressStep.1
    subst targetEq
    have firstDistinct :
        currentField ≠ firstTarget := fun firstEq =>
      progressStep.2 (congrArg RawTerm.recordIntro firstEq)
    exact inductiveHypothesis firstTarget
      ⟨firstStep, firstDistinct⟩

/-- **K12.20.AJ.2 refineIntro SN preservation** — refinement-type
intro packs a value with a proof of its refinement predicate.
Binary cong; uses the pair-style universal-in-conclusion pattern. -/
theorem RawTerm.refineIntro_isStronglyNormalizing {scope : Nat}
    {rawValue : RawTerm scope}
    (valueIsSN : RawTerm.isStronglyNormalizing rawValue) :
    ∀ {predicateProof : RawTerm scope},
      RawTerm.isStronglyNormalizing predicateProof →
      RawTerm.isStronglyNormalizing
        (RawTerm.refineIntro rawValue predicateProof) := by
  induction valueIsSN with
  | intro currentValue _ valueIH =>
    intro predicateProof proofIsSN
    induction proofIsSN with
    | intro currentProof proofClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.refineIntro currentValue currentProof) ?_
      intro target progressStep
      obtain ⟨valueTarget, proofTarget, targetEq,
              valueStep, proofStep⟩ :=
        RawStep.par.refineIntro_inv progressStep.1
      subst targetEq
      by_cases valueEq : currentValue = valueTarget
      · subst valueEq
        have proofDistinct :
            currentProof ≠ proofTarget := fun proofEq =>
          progressStep.2
            (congrArg (RawTerm.refineIntro currentValue) proofEq)
        exact innerIH proofTarget ⟨proofStep, proofDistinct⟩
      · have valueProgress :
            RawStep.parProgress currentValue valueTarget :=
          ⟨valueStep, valueEq⟩
        by_cases proofEq : currentProof = proofTarget
        · subst proofEq
          exact valueIH valueTarget valueProgress
            (RawTerm.isStronglyNormalizing.intro currentProof
              proofClosure)
        · exact valueIH valueTarget valueProgress
            (proofClosure proofTarget ⟨proofStep, proofEq⟩)

/-- **K12.20.AJ.3 codataUnfold SN preservation** — codata
corecursive unfold bundles an initial state with a transition
function.  Binary cong; pair-style universal-in-conclusion. -/
theorem RawTerm.codataUnfold_isStronglyNormalizing {scope : Nat}
    {initialState : RawTerm scope}
    (stateIsSN : RawTerm.isStronglyNormalizing initialState) :
    ∀ {transition : RawTerm scope},
      RawTerm.isStronglyNormalizing transition →
      RawTerm.isStronglyNormalizing
        (RawTerm.codataUnfold initialState transition) := by
  induction stateIsSN with
  | intro currentState _ stateIH =>
    intro transition transitionIsSN
    induction transitionIsSN with
    | intro currentTransition transitionClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.codataUnfold currentState currentTransition) ?_
      intro target progressStep
      obtain ⟨stateTarget, transitionTarget, targetEq,
              stateStep, transitionStep⟩ :=
        RawStep.par.codataUnfold_inv progressStep.1
      subst targetEq
      by_cases stateEq : currentState = stateTarget
      · subst stateEq
        have transitionDistinct :
            currentTransition ≠ transitionTarget :=
          fun transitionEq =>
            progressStep.2
              (congrArg (RawTerm.codataUnfold currentState)
                transitionEq)
        exact innerIH transitionTarget
          ⟨transitionStep, transitionDistinct⟩
      · have stateProgress :
            RawStep.parProgress currentState stateTarget :=
          ⟨stateStep, stateEq⟩
        by_cases transitionEq : currentTransition = transitionTarget
        · subst transitionEq
          exact stateIH stateTarget stateProgress
            (RawTerm.isStronglyNormalizing.intro currentTransition
              transitionClosure)
        · exact stateIH stateTarget stateProgress
            (transitionClosure transitionTarget
              ⟨transitionStep, transitionEq⟩)

/-- **K12.20.AK.1 pathCompose SN preservation** — cubical path
composition.  Pure binary cong over two path witnesses;
pair-style universal-in-conclusion. -/
theorem RawTerm.pathCompose_isStronglyNormalizing {scope : Nat}
    {leftPath : RawTerm scope}
    (leftIsSN : RawTerm.isStronglyNormalizing leftPath) :
    ∀ {rightPath : RawTerm scope},
      RawTerm.isStronglyNormalizing rightPath →
      RawTerm.isStronglyNormalizing
        (RawTerm.pathCompose leftPath rightPath) := by
  induction leftIsSN with
  | intro currentLeft _ leftIH =>
    intro rightPath rightIsSN
    induction rightIsSN with
    | intro currentRight rightClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.pathCompose currentLeft currentRight) ?_
      intro target progressStep
      obtain ⟨leftTarget, rightTarget, targetEq,
              leftStep, rightStep⟩ :=
        RawStep.par.pathCompose_inv progressStep.1
      subst targetEq
      by_cases leftEq : currentLeft = leftTarget
      · subst leftEq
        have rightDistinct :
            currentRight ≠ rightTarget := fun rightEq =>
          progressStep.2
            (congrArg (RawTerm.pathCompose currentLeft) rightEq)
        exact innerIH rightTarget ⟨rightStep, rightDistinct⟩
      · have leftProgress :
            RawStep.parProgress currentLeft leftTarget :=
          ⟨leftStep, leftEq⟩
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact leftIH leftTarget leftProgress
            (RawTerm.isStronglyNormalizing.intro currentRight
              rightClosure)
        · exact leftIH leftTarget leftProgress
            (rightClosure rightTarget ⟨rightStep, rightEq⟩)

/-- **K12.20.AK.2 oeqTrans SN preservation** — observational
equality transitivity.  Pure binary cong over two proof
witnesses. -/
theorem RawTerm.oeqTrans_isStronglyNormalizing {scope : Nat}
    {firstProof : RawTerm scope}
    (firstIsSN : RawTerm.isStronglyNormalizing firstProof) :
    ∀ {secondProof : RawTerm scope},
      RawTerm.isStronglyNormalizing secondProof →
      RawTerm.isStronglyNormalizing
        (RawTerm.oeqTrans firstProof secondProof) := by
  induction firstIsSN with
  | intro currentFirst _ firstIH =>
    intro secondProof secondIsSN
    induction secondIsSN with
    | intro currentSecond secondClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.oeqTrans currentFirst currentSecond) ?_
      intro target progressStep
      obtain ⟨firstTarget, secondTarget, targetEq,
              firstStep, secondStep⟩ :=
        RawStep.par.oeqTrans_inv progressStep.1
      subst targetEq
      by_cases firstEq : currentFirst = firstTarget
      · subst firstEq
        have secondDistinct :
            currentSecond ≠ secondTarget := fun secondEq =>
          progressStep.2
            (congrArg (RawTerm.oeqTrans currentFirst) secondEq)
        exact innerIH secondTarget ⟨secondStep, secondDistinct⟩
      · have firstProgress :
            RawStep.parProgress currentFirst firstTarget :=
          ⟨firstStep, firstEq⟩
        by_cases secondEq : currentSecond = secondTarget
        · subst secondEq
          exact firstIH firstTarget firstProgress
            (RawTerm.isStronglyNormalizing.intro currentSecond
              secondClosure)
        · exact firstIH firstTarget firstProgress
            (secondClosure secondTarget ⟨secondStep, secondEq⟩)

/-- **K12.20.AK.3 equivCompose SN preservation** — equivalence
composition.  Pure binary cong over two equivalence witnesses. -/
theorem RawTerm.equivCompose_isStronglyNormalizing {scope : Nat}
    {firstEquiv : RawTerm scope}
    (firstIsSN : RawTerm.isStronglyNormalizing firstEquiv) :
    ∀ {secondEquiv : RawTerm scope},
      RawTerm.isStronglyNormalizing secondEquiv →
      RawTerm.isStronglyNormalizing
        (RawTerm.equivCompose firstEquiv secondEquiv) := by
  induction firstIsSN with
  | intro currentFirst _ firstIH =>
    intro secondEquiv secondIsSN
    induction secondIsSN with
    | intro currentSecond secondClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.equivCompose currentFirst currentSecond) ?_
      intro target progressStep
      obtain ⟨firstTarget, secondTarget, targetEq,
              firstStep, secondStep⟩ :=
        RawStep.par.equivCompose_inv progressStep.1
      subst targetEq
      by_cases firstEq : currentFirst = firstTarget
      · subst firstEq
        have secondDistinct :
            currentSecond ≠ secondTarget := fun secondEq =>
          progressStep.2
            (congrArg (RawTerm.equivCompose currentFirst) secondEq)
        exact innerIH secondTarget ⟨secondStep, secondDistinct⟩
      · have firstProgress :
            RawStep.parProgress currentFirst firstTarget :=
          ⟨firstStep, firstEq⟩
        by_cases secondEq : currentSecond = secondTarget
        · subst secondEq
          exact firstIH firstTarget firstProgress
            (RawTerm.isStronglyNormalizing.intro currentSecond
              secondClosure)
        · exact firstIH firstTarget firstProgress
            (secondClosure secondTarget ⟨secondStep, secondEq⟩)

/-- **K12.20.AL.1 sessionRecv SN preservation** — session-type
receive operation.  Pure unary cong over the channel witness. -/
theorem RawTerm.sessionRecv_isStronglyNormalizing {scope : Nat}
    {channel : RawTerm scope}
    (channelIsSN : RawTerm.isStronglyNormalizing channel) :
    RawTerm.isStronglyNormalizing (RawTerm.sessionRecv channel) := by
  induction channelIsSN with
  | intro currentChannel _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.sessionRecv currentChannel) ?_
    intro target progressStep
    obtain ⟨channelTarget, targetEq, channelStep⟩ :=
      RawStep.par.sessionRecv_inv progressStep.1
    subst targetEq
    have channelDistinct :
        currentChannel ≠ channelTarget := fun channelEq =>
      progressStep.2 (congrArg RawTerm.sessionRecv channelEq)
    exact inductiveHypothesis channelTarget
      ⟨channelStep, channelDistinct⟩

/-- **K12.20.AL.2 sessionSend SN preservation** — session-type
send operation bundles a channel with a payload.  Pure binary
cong; pair-style universal-in-conclusion. -/
theorem RawTerm.sessionSend_isStronglyNormalizing {scope : Nat}
    {channel : RawTerm scope}
    (channelIsSN : RawTerm.isStronglyNormalizing channel) :
    ∀ {payload : RawTerm scope},
      RawTerm.isStronglyNormalizing payload →
      RawTerm.isStronglyNormalizing
        (RawTerm.sessionSend channel payload) := by
  induction channelIsSN with
  | intro currentChannel _ channelIH =>
    intro payload payloadIsSN
    induction payloadIsSN with
    | intro currentPayload payloadClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.sessionSend currentChannel currentPayload) ?_
      intro target progressStep
      obtain ⟨channelTarget, payloadTarget, targetEq,
              channelStep, payloadStep⟩ :=
        RawStep.par.sessionSend_inv progressStep.1
      subst targetEq
      by_cases channelEq : currentChannel = channelTarget
      · subst channelEq
        have payloadDistinct :
            currentPayload ≠ payloadTarget := fun payloadEq =>
          progressStep.2
            (congrArg (RawTerm.sessionSend currentChannel) payloadEq)
        exact innerIH payloadTarget ⟨payloadStep, payloadDistinct⟩
      · have channelProgress :
            RawStep.parProgress currentChannel channelTarget :=
          ⟨channelStep, channelEq⟩
        by_cases payloadEq : currentPayload = payloadTarget
        · subst payloadEq
          exact channelIH channelTarget channelProgress
            (RawTerm.isStronglyNormalizing.intro currentPayload
              payloadClosure)
        · exact channelIH channelTarget channelProgress
            (payloadClosure payloadTarget
              ⟨payloadStep, payloadEq⟩)

/-- **K12.20.AL.3 effectPerform SN preservation** — algebraic
effect operation invocation bundles an operation tag with its
arguments.  Pure binary cong; pair-style universal-in-conclusion. -/
theorem RawTerm.effectPerform_isStronglyNormalizing {scope : Nat}
    {operationTag : RawTerm scope}
    (operationIsSN : RawTerm.isStronglyNormalizing operationTag) :
    ∀ {arguments : RawTerm scope},
      RawTerm.isStronglyNormalizing arguments →
      RawTerm.isStronglyNormalizing
        (RawTerm.effectPerform operationTag arguments) := by
  induction operationIsSN with
  | intro currentOperation _ operationIH =>
    intro arguments argumentsIsSN
    induction argumentsIsSN with
    | intro currentArguments argumentsClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.effectPerform currentOperation currentArguments) ?_
      intro target progressStep
      obtain ⟨operationTarget, argumentsTarget, targetEq,
              operationStep, argumentsStep⟩ :=
        RawStep.par.effectPerform_inv progressStep.1
      subst targetEq
      by_cases operationEq : currentOperation = operationTarget
      · subst operationEq
        have argumentsDistinct :
            currentArguments ≠ argumentsTarget := fun argumentsEq =>
          progressStep.2
            (congrArg (RawTerm.effectPerform currentOperation)
              argumentsEq)
        exact innerIH argumentsTarget
          ⟨argumentsStep, argumentsDistinct⟩
      · have operationProgress :
            RawStep.parProgress currentOperation operationTarget :=
          ⟨operationStep, operationEq⟩
        by_cases argumentsEq : currentArguments = argumentsTarget
        · subst argumentsEq
          exact operationIH operationTarget operationProgress
            (RawTerm.isStronglyNormalizing.intro currentArguments
              argumentsClosure)
        · exact operationIH operationTarget operationProgress
            (argumentsClosure argumentsTarget
              ⟨argumentsStep, argumentsEq⟩)

/-- **K12.20.AM glueIntro SN preservation** — cubical Glue
introduction bundles a base value with a partial-element witness.
Pure binary cong; pair-style universal-in-conclusion.  Closes
the cubical/HoTT intro slice of the SN-helper rail. -/
theorem RawTerm.glueIntro_isStronglyNormalizing {scope : Nat}
    {baseValue : RawTerm scope}
    (baseIsSN : RawTerm.isStronglyNormalizing baseValue) :
    ∀ {partialValue : RawTerm scope},
      RawTerm.isStronglyNormalizing partialValue →
      RawTerm.isStronglyNormalizing
        (RawTerm.glueIntro baseValue partialValue) := by
  induction baseIsSN with
  | intro currentBase _ baseIH =>
    intro partialValue partialIsSN
    induction partialIsSN with
    | intro currentPartial partialClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.glueIntro currentBase currentPartial) ?_
      intro target progressStep
      obtain ⟨baseTarget, partialTarget, targetEq,
              baseStep, partialStep⟩ :=
        RawStep.par.glueIntro_inv progressStep.1
      subst targetEq
      by_cases baseEq : currentBase = baseTarget
      · subst baseEq
        have partialDistinct :
            currentPartial ≠ partialTarget := fun partialEq =>
          progressStep.2
            (congrArg (RawTerm.glueIntro currentBase) partialEq)
        exact innerIH partialTarget ⟨partialStep, partialDistinct⟩
      · have baseProgress :
            RawStep.parProgress currentBase baseTarget :=
          ⟨baseStep, baseEq⟩
        by_cases partialEq : currentPartial = partialTarget
        · subst partialEq
          exact baseIH baseTarget baseProgress
            (RawTerm.isStronglyNormalizing.intro currentPartial
              partialClosure)
        · exact baseIH baseTarget baseProgress
            (partialClosure partialTarget
              ⟨partialStep, partialEq⟩)

/-- **K12.20.AH equivIntro SN preservation** — equivalence intro
bundles a forward and backward function.  Binary cong; uses the
pair-style universal-in-conclusion pattern to keep the backward
IH universal under outer induction on the forward SN witness. -/
theorem RawTerm.equivIntro_isStronglyNormalizing {scope : Nat}
    {forwardFn : RawTerm scope}
    (forwardIsSN : RawTerm.isStronglyNormalizing forwardFn) :
    ∀ {backwardFn : RawTerm scope},
      RawTerm.isStronglyNormalizing backwardFn →
      RawTerm.isStronglyNormalizing
        (RawTerm.equivIntro forwardFn backwardFn) := by
  induction forwardIsSN with
  | intro currentForward _ forwardIH =>
    intro backwardFn backwardIsSN
    induction backwardIsSN with
    | intro currentBackward backwardClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.equivIntro currentForward currentBackward) ?_
      intro target progressStep
      obtain ⟨forwardTarget, backwardTarget, targetEq,
              forwardStep, backwardStep⟩ :=
        RawStep.par.equivIntro_inv progressStep.1
      subst targetEq
      by_cases forwardEq : currentForward = forwardTarget
      · subst forwardEq
        have backwardDistinct :
            currentBackward ≠ backwardTarget := fun backwardEq =>
          progressStep.2
            (congrArg (RawTerm.equivIntro currentForward) backwardEq)
        exact innerIH backwardTarget ⟨backwardStep, backwardDistinct⟩
      · have forwardProgress :
            RawStep.parProgress currentForward forwardTarget :=
          ⟨forwardStep, forwardEq⟩
        by_cases backwardEq : currentBackward = backwardTarget
        · subst backwardEq
          exact forwardIH forwardTarget forwardProgress
            (RawTerm.isStronglyNormalizing.intro currentBackward
              backwardClosure)
        · exact forwardIH forwardTarget forwardProgress
            (backwardClosure backwardTarget ⟨backwardStep, backwardEq⟩)

/-! ## K12.20.D typed CR2 lift for SN-direct Reducible arms

CR2 at the typed `Reducible` level for the ten SN-direct arms.  Each
arm's `Reducible Ty.X _ = Term.isStronglyNormalizing _` unfolds
definitionally to `RawTerm.isStronglyNormalizing _.toRaw`, so the
typed-level CR2 statement reduces — definitionally, no rewriting —
to K12.20.B's raw `step_preserves`.  Each theorem body is a single
application of `RawTerm.isStronglyNormalizing.step_preserves`.

These 10 lemmas cover the SN-direct closures shipped in K12.2-K12.4
(closed leaves: unit / bool / nat / empty / interval / universe /
tyVar) plus K12.13/K12.15 (Layer-1 SN-fallback for session / effect /
modal — no destructor available at Layer 1, so closure cannot enrich
beyond SN).  The remaining 15 compound arms (arrow / piTy / Σ / id /
list / option / either / path / glue / oeq / idStrict / equiv /
refine / record / codata) need per-Ty case analysis on the closure
structure (preserving both SN AND the eliminator closures); those
land in K12.20.G.

Note: these typed CR2 lemmas use the raw step `RawStep.parProgress
sourceRaw targetRaw` directly rather than a typed-Step relation,
because (1) Reducible's SN-direct unfolding bypasses the typed step
entirely — only `sourceRaw` and `targetRaw` are needed; (2) any
typed Step at the relevant ctors projects down to a parProgress on
the raw forms via the typed→raw bridge (which downstream cascade
steps invoke); (3) keeping the K12.20.D signature raw-only means
zero dependency on the typed Step relation, so the lemmas compose
freely with K12.20.A/B/C in the K12.20.H Term.lam case.
-/

/-- **K12.20.D unit arm**: Reducible at Ty.unit is closed under raw
parallel-progress reduction. -/
theorem Reducible.step_preserves_unit
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context Ty.unit sourceRaw}
    {target : Term context Ty.unit targetRaw}
    (sourceReducible : Reducible Ty.unit source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible Ty.unit target :=
  RawTerm.isStronglyNormalizing.step_preserves sourceReducible rawStep

/-- **K12.20.D bool arm**. -/
theorem Reducible.step_preserves_bool
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context Ty.bool sourceRaw}
    {target : Term context Ty.bool targetRaw}
    (sourceReducible : Reducible Ty.bool source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible Ty.bool target :=
  RawTerm.isStronglyNormalizing.step_preserves sourceReducible rawStep

/-- **K12.20.D nat arm**. -/
theorem Reducible.step_preserves_nat
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context Ty.nat sourceRaw}
    {target : Term context Ty.nat targetRaw}
    (sourceReducible : Reducible Ty.nat source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible Ty.nat target :=
  RawTerm.isStronglyNormalizing.step_preserves sourceReducible rawStep

/-- **K12.20.D empty arm**.  Vacuous in practice (no Term inhabits
`Ty.empty` at the typed layer), but the closure ships uniformly with
the other SN-direct arms for cascade symmetry. -/
theorem Reducible.step_preserves_empty
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context Ty.empty sourceRaw}
    {target : Term context Ty.empty targetRaw}
    (sourceReducible : Reducible Ty.empty source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible Ty.empty target :=
  RawTerm.isStronglyNormalizing.step_preserves sourceReducible rawStep

/-- **K12.20.D interval arm**.  Cubical-mode-only interval terms;
the closure preserves SN under reduction.  Per K12.4, Ty.interval is
a closed leaf shipping SN directly. -/
theorem Reducible.step_preserves_interval
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context Ty.interval sourceRaw}
    {target : Term context Ty.interval targetRaw}
    (sourceReducible : Reducible Ty.interval source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible Ty.interval target :=
  RawTerm.isStronglyNormalizing.step_preserves sourceReducible rawStep

/-- **K12.20.D universe arm**.  Universe-coded types ship SN directly
per K12.4; the closure preserves SN through type-code reductions
(e.g. `Step.eqType` reducing identity-of-universe to equiv). -/
theorem Reducible.step_preserves_universe
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {universeLevel : UniverseLevel}
    {levelLe : universeLevel.toNat + 1 ≤ level}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.universe universeLevel levelLe) sourceRaw}
    {target : Term context (Ty.universe universeLevel levelLe) targetRaw}
    (sourceReducible :
        Reducible (Ty.universe universeLevel levelLe) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.universe universeLevel levelLe) target :=
  RawTerm.isStronglyNormalizing.step_preserves sourceReducible rawStep

/-- **K12.20.D tyVar arm**.  Abstract type-variable inhabitants ship
SN directly; the closure preserves SN under reduction.  Used by the
fundamental lemma when threading through polymorphic type
parameters. -/
theorem Reducible.step_preserves_tyVar
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {position : Fin scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.tyVar position) sourceRaw}
    {target : Term context (Ty.tyVar position) targetRaw}
    (sourceReducible : Reducible (Ty.tyVar position) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.tyVar position) target :=
  RawTerm.isStronglyNormalizing.step_preserves sourceReducible rawStep

/-- **K12.20.D session arm**.  Layer-1 SN-fallback per K12.15 (no
projection eliminator exists at Layer 1).  Session protocol-state
reductions preserve SN — the typed Sessions layer (#1268 K09) will
ship per-step closures requiring per-step CR2 case analysis. -/
theorem Reducible.step_preserves_session
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {protocolStep : RawTerm scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.session protocolStep) sourceRaw}
    {target : Term context (Ty.session protocolStep) targetRaw}
    (sourceReducible : Reducible (Ty.session protocolStep) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.session protocolStep) target :=
  RawTerm.isStronglyNormalizing.step_preserves sourceReducible rawStep

/-- **K12.20.D effect arm**.  Layer-1 SN-fallback per K12.15 (no
`Term.effectHandle` destructor exists at Layer 1).  Effectful-term
reductions preserve SN — the Effects layer (#1345 D5.9, #1346 D5.10)
will ship handler-discharge closures requiring per-handler CR2. -/
theorem Reducible.step_preserves_effect
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {effectTag : RawTerm scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.effect carrierType effectTag) sourceRaw}
    {target : Term context (Ty.effect carrierType effectTag) targetRaw}
    (sourceReducible :
        Reducible (Ty.effect carrierType effectTag) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.effect carrierType effectTag) target :=
  RawTerm.isStronglyNormalizing.step_preserves sourceReducible rawStep

/-- **K12.20.D modal arm**.  Layer-1 SN-fallback per K12.13 (no
typed `Term` ctor inhabits `Ty.modal _ _` at Layer 1 — the type
former is structurally uninhabited until Layer 6's modIntroCross /
modElimCross land).  The closure remains uniformly statable for
cascade symmetry — vacuous in practice at Layer 1, real once
Layer 6 ships. -/
theorem Reducible.step_preserves_modal
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {modalityTag : Nat}
    {carrierType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.modal modalityTag carrierType) sourceRaw}
    {target : Term context (Ty.modal modalityTag carrierType) targetRaw}
    (sourceReducible :
        Reducible (Ty.modal modalityTag carrierType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.modal modalityTag carrierType) target :=
  RawTerm.isStronglyNormalizing.step_preserves sourceReducible rawStep

/-! ## K12.20.E typed neutral-var reducibility at SN-direct arms

Variables-as-reducible: every typed `Term` whose raw projection is
`RawTerm.var position` is reducible at any SN-direct Reducible arm.
Foundational for the K12.20.F `ReducibleSubst.singleton` /
`ReducibleSubst.lift` constructors, where var-shaped Terms (cast
through `Ty.weaken_subst_singleton` / `Ty.weaken_subst_commute`
equalities) need to be exhibited reducible at the substituted-out
type.

Generic over the Term's type-level index — the lemmas accept ANY
`Term context ty (RawTerm.var position)` (i.e. anything whose raw
form is a var), not specifically `Term.var position`.  This covers:
* The canonical `Term.var position` form when `ty = varType context
  position` matches by definition.
* `▸`-cast forms `h ▸ Term.var position` used in TermSubst.lift /
  .singleton, where `h : varType context position = ty`.  The `▸`
  preserves the raw index, so the casted term still has raw form
  `RawTerm.var position`.

Body across all 10 arms is identical: `RawTerm.var_isStronglyNormalizing
position`.  Works by Reducible's definitional unfolding:
`Reducible Ty.X term = Term.isStronglyNormalizing term = RawTerm.
isStronglyNormalizing term.toRaw = RawTerm.isStronglyNormalizing
(RawTerm.var position)` — exactly the type of
`var_isStronglyNormalizing`.

The compound Reducible arms (arrow / piTy / Σ / id / list / option /
either / path / glue / oeq / idStrict / equiv / refine / record /
codata) need full CR3-style neutral-reducibility (a variable applied
to reducible arguments must be reducible at the result type),
provable only by outer induction on Ty.  Those land in K12.20.G
alongside compound-arm CR2.
-/

/-- **K12.20.E foundation**: any Term whose raw projection is
`RawTerm.var position` is strongly normalizing, regardless of its
declared type.  Body uses raw `var_isStronglyNormalizing` directly;
`Term.isStronglyNormalizing` definitionally unfolds to the raw SN
at the term's raw index, which is `RawTerm.var position` by the
type-level index discipline. -/
theorem Term.isStronglyNormalizing_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {ty : Ty level scope}
    {position : Fin scope}
    (_term : Term context ty (RawTerm.var position)) :
    Term.isStronglyNormalizing _term :=
  RawTerm.var_isStronglyNormalizing position

/-- **K12.20.E unit arm**: variables are reducible at Ty.unit. -/
theorem Reducible.unit_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {position : Fin scope}
    (term : Term context Ty.unit (RawTerm.var position)) :
    Reducible Ty.unit term :=
  Term.isStronglyNormalizing_of_varShape term

/-- **K12.20.E bool arm**. -/
theorem Reducible.bool_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {position : Fin scope}
    (term : Term context Ty.bool (RawTerm.var position)) :
    Reducible Ty.bool term :=
  Term.isStronglyNormalizing_of_varShape term

/-- **K12.20.E nat arm**. -/
theorem Reducible.nat_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {position : Fin scope}
    (term : Term context Ty.nat (RawTerm.var position)) :
    Reducible Ty.nat term :=
  Term.isStronglyNormalizing_of_varShape term

/-- **K12.20.E empty arm**. -/
theorem Reducible.empty_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {position : Fin scope}
    (term : Term context Ty.empty (RawTerm.var position)) :
    Reducible Ty.empty term :=
  Term.isStronglyNormalizing_of_varShape term

/-- **K12.20.E interval arm**. -/
theorem Reducible.interval_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {position : Fin scope}
    (term : Term context Ty.interval (RawTerm.var position)) :
    Reducible Ty.interval term :=
  Term.isStronglyNormalizing_of_varShape term

/-- **K12.20.E universe arm**. -/
theorem Reducible.universe_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {universeLevel : UniverseLevel}
    {levelLe : universeLevel.toNat + 1 ≤ level}
    {position : Fin scope}
    (term :
        Term context (Ty.universe universeLevel levelLe)
          (RawTerm.var position)) :
    Reducible (Ty.universe universeLevel levelLe) term :=
  Term.isStronglyNormalizing_of_varShape term

/-- **K12.20.E tyVar arm**. -/
theorem Reducible.tyVar_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {tyVarPosition : Fin scope}
    {position : Fin scope}
    (term :
        Term context (Ty.tyVar tyVarPosition) (RawTerm.var position)) :
    Reducible (Ty.tyVar tyVarPosition) term :=
  Term.isStronglyNormalizing_of_varShape term

/-- **K12.20.E session arm**. -/
theorem Reducible.session_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {protocolStep : RawTerm scope}
    {position : Fin scope}
    (term :
        Term context (Ty.session protocolStep) (RawTerm.var position)) :
    Reducible (Ty.session protocolStep) term :=
  Term.isStronglyNormalizing_of_varShape term

/-- **K12.20.E effect arm**. -/
theorem Reducible.effect_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {effectTag : RawTerm scope}
    {position : Fin scope}
    (term :
        Term context (Ty.effect carrierType effectTag)
          (RawTerm.var position)) :
    Reducible (Ty.effect carrierType effectTag) term :=
  Term.isStronglyNormalizing_of_varShape term

/-- **K12.20.E modal arm**. -/
theorem Reducible.modal_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {modalityTag : Nat}
    {carrierType : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.modal modalityTag carrierType)
          (RawTerm.var position)) :
    Reducible (Ty.modal modalityTag carrierType) term :=
  Term.isStronglyNormalizing_of_varShape term

/-! ## K12.20.F typed CR2 lift for compound Reducible arms — Ty.arrow

The first of 15 compound-arm CR2 lemmas.  Unlike the 10 SN-direct
arms (K12.20.D), compound arms have closure structure beyond pure SN
that must also be preserved under reduction.

For `Ty.arrow A B`, `Reducible` says: SN(f) ∧ (∀ arg, Reducible A arg
→ Reducible B (app f arg)).  Preserving this under f → f' requires:
1. SN(f'), via K12.20.B's raw `step_preserves` on the SN conjunct.
2. ∀ arg, Reducible A arg → Reducible B (app f' arg).  Given
   `Reducible B (app f arg)` (from source's closure), and step
   `app f arg → app f' arg` (via RawStep.par.app + refl on arg),
   the new closure conclusion follows from CR2 at codomain — the
   recursive ingredient supplied as `codomainCR2`.

Per the warrior-mentality discipline of CLAUDE.md, K12.20.F ships
the arrow case taking `codomainCR2` as an explicit hypothesis rather
than wiring up structural recursion on Ty here.  This keeps the
proof atomic and one-shot.  K12.20.G+ ship the remaining 14
compound arms, each with the same shape (recursion-hypothesis
taken as argument).  The final combined `Reducible.step_preserves`
will be a structurally-recursive bundle wiring all 25 arms together;
its body will invoke each per-arm helper at the right recursive
position.
-/

/-- **K12.20.F arrow arm**: Reducible at `Ty.arrow domain codomain`
is preserved under raw `parProgress` reduction.  Body: SN preserved
via K12.20.B, closure preserved via codomainCR2 + raw app-cong. -/
theorem Reducible.step_preserves_arrow
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.arrow domainType codomainType) sourceRaw}
    {target : Term context (Ty.arrow domainType codomainType) targetRaw}
    (sourceReducible : Reducible (Ty.arrow domainType codomainType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw)
    (codomainCR2 :
        ∀ {sourceRaw' targetRaw' : RawTerm scope}
          {source' : Term context codomainType sourceRaw'}
          {target' : Term context codomainType targetRaw'},
          Reducible codomainType source' →
          RawStep.parProgress sourceRaw' targetRaw' →
          Reducible codomainType target') :
    Reducible (Ty.arrow domainType codomainType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro argRaw argTerm argReducible
    have appStep : RawStep.parProgress
        (RawTerm.app sourceRaw argRaw) (RawTerm.app targetRaw argRaw) := by
      refine ⟨RawStep.par.app rawStep.1 (RawStep.par.refl argRaw), ?_⟩
      intro appEq
      apply rawStep.2
      injection appEq
    exact codomainCR2 (sourceReducible.2 argTerm argReducible) appStep

/-! ## K12.20.G typed CR2 lift — Ty.piTy weak-closure compound arm

Second compound-arm CR2 lemma.  `Ty.piTy` ships a **weak closure**
in K12.6 (full Tait dep-Π closure is reserved for the future Kripke
logical-relation refactor):

```
Reducible (Ty.piTy A B) f =
  SN(f) ∧ ∀ arg, Reducible A arg → SN(Term.appPi f arg)
```

The eliminator output is `SN(appPi f arg)` not `Reducible
codomain (appPi f arg)`.  Consequently, CR2 for piTy needs NO
recursive codomainCR2 hypothesis — both SN preservation (the SN
conjunct) and the eliminator-output closure are pure-SN
preservation, both discharged by K12.20.B's raw `step_preserves`.
This is the simplest compound-arm CR2 of the 15.

Term.appPi's raw projection IS `RawTerm.app` (per Term.lean:127,
`Term.appPi : Term ctx (cod.subst0 dom arg) (RawTerm.app f a)`),
not a separate `RawTerm.appPi`.  So the same `RawStep.par.app`
cong rule we used in K12.20.F applies here.
-/

/-- **K12.20.G piTy arm**: weak-closure CR2 for `Ty.piTy`.  Both
SN-of-functionTerm and SN-of-appPi-result are preserved by the same
raw `step_preserves`.  Distinctness on app via ctor injectivity, same
as K12.20.F. -/
theorem Reducible.step_preserves_piTy
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.piTy domainType codomainType) sourceRaw}
    {target : Term context (Ty.piTy domainType codomainType) targetRaw}
    (sourceReducible :
        Reducible (Ty.piTy domainType codomainType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.piTy domainType codomainType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro argRaw argTerm argReducible
    have appStep : RawStep.parProgress
        (RawTerm.app sourceRaw argRaw) (RawTerm.app targetRaw argRaw) := by
      refine ⟨RawStep.par.app rawStep.1 (RawStep.par.refl argRaw), ?_⟩
      intro appEq
      apply rawStep.2
      injection appEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 argTerm argReducible) appStep

/-! ## K12.20.H typed CR2 lift — Ty.sigmaTy asymmetric-closure compound arm

Third compound-arm CR2 lemma.  `Ty.sigmaTy` ships an **asymmetric
closure** in K12.7 (the second conjunct is full Reducible on the
fst projection because `firstType` IS a strict sub-Ty of
`Ty.sigmaTy firstType secondType` and structural recursion on
Ty admits it; the third conjunct is weak SN on snd, because
`secondType.subst0 firstType (RawTerm.fst pairRaw)` is a
substituted Ty — same substituted-codomain wall as K12.6
piTy):

```
Reducible (Ty.sigmaTy A B) p =
  SN(p) ∧ Reducible A (Term.fst p) ∧ SN(Term.snd p)
```

The three-conjunct shape demands three independent preservation
discharges under one raw-progress step:

* **SN(p)**: pure-SN preservation, K12.20.B's raw
  `step_preserves` handles it directly.
* **Reducible A (fst p)**: needs `firstTypeCR2` hypothesis
  threaded through (the structural-recursion-on-Ty bundling
  comes later when all 15 compound CR2 arms ship as one
  bundle).  The fst-cong step lifts `rawStep` via
  `RawStep.par.fst`; distinctness via `injection` on
  `RawTerm.fst.injEq` (ctor injectivity, propext-free).
* **SN(snd p)**: pure-SN preservation again; snd-cong step
  via `RawStep.par.snd`, distinctness via `injection` on
  `RawTerm.snd.injEq`.

Term.fst's raw projection IS `RawTerm.fst` (per Term.lean:140),
Term.snd's IS `RawTerm.snd` (per Term.lean:145).  So the cong
rules `RawStep.par.fst` and `RawStep.par.snd` apply directly to
typed projections.
-/

/-- **K12.20.H sigmaTy arm**: asymmetric-closure CR2 for
`Ty.sigmaTy`.  Takes `firstTypeCR2` as explicit hypothesis (the
recursive Reducible-preservation witness on the smaller `firstType`
sub-Ty — supplied externally per the per-arm decomposition; the
unified structurally-recursive bundling ships after all 15
compound-arm lemmas land).  Both SN conjuncts (pair + snd) are
pure-SN preservation; the middle full-Reducible conjunct uses
firstTypeCR2 with fst-cong. -/
theorem Reducible.step_preserves_sigmaTy
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.sigmaTy firstType secondType) sourceRaw}
    {target : Term context (Ty.sigmaTy firstType secondType) targetRaw}
    (firstTypeCR2 :
        ∀ {fstSourceRaw fstTargetRaw : RawTerm scope}
          {fstSource : Term context firstType fstSourceRaw}
          {fstTarget : Term context firstType fstTargetRaw},
          Reducible firstType fstSource →
          RawStep.parProgress fstSourceRaw fstTargetRaw →
          Reducible firstType fstTarget)
    (sourceReducible :
        Reducible (Ty.sigmaTy firstType secondType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.sigmaTy firstType secondType) target := by
  refine ⟨?_, ?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · have fstStep : RawStep.parProgress
        (RawTerm.fst sourceRaw) (RawTerm.fst targetRaw) := by
      refine ⟨RawStep.par.fst rawStep.1, ?_⟩
      intro fstEq
      apply rawStep.2
      injection fstEq
    exact firstTypeCR2 sourceReducible.2.1 fstStep
  · have sndStep : RawStep.parProgress
        (RawTerm.snd sourceRaw) (RawTerm.snd targetRaw) := by
      refine ⟨RawStep.par.snd rawStep.1, ?_⟩
      intro sndEq
      apply rawStep.2
      injection sndEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.2.2 sndStep

/-! ## K12.20.I typed CR2 lift — Ty.id weak-idJ-closure compound arm

Fourth compound-arm CR2 lemma.  `Ty.id` ships a **weak idJ
closure** in K12.9 (motive-Reducible closure is reserved for
the future Kripke logical-relation refactor — paired-environment
recursion sidesteps the eliminator-output sub-Ty wall):

```
Reducible (Ty.id A x y) w =
  SN(w) ∧ ∀ {M : Ty} {br} (bc : Term ctx M br),
            SN(bc) → SN(Term.idJ bc w)
```

The eliminator output is `SN(Term.idJ bc w)` not full
`Reducible motiveType (Term.idJ bc w)`.  Consequently, CR2 for
`Ty.id` needs NO recursive motiveTypeCR2 hypothesis — both
SN-of-witness and SN-of-idJ-result are pure-SN preservation,
both discharged by K12.20.B's raw `step_preserves`.  Same
weak-closure pattern as K12.20.G piTy.

Term.idJ's raw projection IS `RawTerm.idJ baseRaw witnessRaw`
(per Term.lean:245), and `RawStep.par.idJ` takes paired par
steps on baseRaw + witnessRaw (per RawPar.lean:179).  For the
CR2 step, baseCase is unchanged across source/target, so the
baseRaw side gets `RawStep.par.refl baseRaw` while the witness
side gets `rawStep.1`.
-/

/-- **K12.20.I id arm**: weak-idJ-closure CR2 for `Ty.id`.  Both
SN-of-witness and SN-of-idJ-result are preserved by the same
raw `step_preserves`.  Distinctness on idJ via ctor injectivity
(injection extracts witness-side raw equality, contradicts
rawStep.2). -/
theorem Reducible.step_preserves_id
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context
        (Ty.id carrierType leftEndpoint rightEndpoint) sourceRaw}
    {target : Term context
        (Ty.id carrierType leftEndpoint rightEndpoint) targetRaw}
    (sourceReducible :
        Reducible (Ty.id carrierType leftEndpoint rightEndpoint) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.id carrierType leftEndpoint rightEndpoint) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro motiveType baseRaw baseCase baseSN
    have idJStep : RawStep.parProgress
        (RawTerm.idJ baseRaw sourceRaw)
        (RawTerm.idJ baseRaw targetRaw) := by
      refine ⟨RawStep.par.idJ (RawStep.par.refl baseRaw) rawStep.1, ?_⟩
      intro idJEq
      apply rawStep.2
      injection idJEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 baseCase baseSN) idJStep

/-! ## K12.20.J typed CR2 lift — Ty.listType weak-elim-closure compound arm

Fifth compound-arm CR2 lemma.  `Ty.listType` ships a **weak elim
closure** in K12.8: the eliminator output is plain SN, not full
Reducible (motive-Reducible closure reserved for Kripke logical-
relation refactor — paired-environment recursion sidesteps the
arbitrary-motiveType sub-Ty wall).  Closure shape (per
Reducibility.lean:404):

```
Reducible (Ty.listType A) xs =
  SN(xs) ∧ ∀ {M} {nilRaw consRaw} (nilBranch consBranch),
    SN(nilBranch) →
    (∀ head tail, Reducible A head → SN(tail) →
                  SN(consBranch head tail)) →
    SN(listElim xs nilBranch consBranch)
```

The hypothesis chain (`Reducible A head` + `SN(tail)` for the
cons branch) is propagated unchanged by sourceReducible.2 — CR2
needs NO recursive elementTypeCR2 hypothesis because the
eliminator output is plain SN, not Reducible.  Same weak-closure
pattern as K12.20.G piTy and K12.20.I id.

Term.listElim shares raw form `RawTerm.listElim scrutineeRaw
nilRaw consRaw` (per Term.lean:200); `RawStep.par.listElim`
takes paired par steps on all three components (per RawPar.lean:
120).  For CR2, branches are fixed across source/target, so the
nilRaw/consRaw sides get `par.refl` while scrutinee gets
`rawStep.1`.
-/

/-- **K12.20.J listType arm**: weak-elim-closure CR2 for
`Ty.listType`.  Both SN-of-listTerm and SN-of-listElim-result are
preserved by the same raw `step_preserves`.  Distinctness on
listElim via ctor injectivity (injection extracts scrutinee-side
raw equality, contradicts rawStep.2). -/
theorem Reducible.step_preserves_listType
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.listType elementType) sourceRaw}
    {target : Term context (Ty.listType elementType) targetRaw}
    (sourceReducible :
        Reducible (Ty.listType elementType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.listType elementType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro motiveType nilRaw consRaw nilBranch consBranch nilSN consApplied
    have listElimStep : RawStep.parProgress
        (RawTerm.listElim sourceRaw nilRaw consRaw)
        (RawTerm.listElim targetRaw nilRaw consRaw) := by
      refine ⟨RawStep.par.listElim rawStep.1
          (RawStep.par.refl nilRaw) (RawStep.par.refl consRaw), ?_⟩
      intro listElimEq
      apply rawStep.2
      injection listElimEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 nilBranch consBranch nilSN consApplied) listElimStep

/-! ## K12.20.K typed CR2 lift — Ty.optionType weak-elim-closure compound arm

Sixth compound-arm CR2 lemma.  `Ty.optionType` ships a **weak
elim closure** in K12.8, cleanest of the three K12.8 parametric
arms: someBranch's type matches K12.6 piTy weak shape exactly
when restricted to elementType.  Closure shape (per
Reducibility.lean:426):

```
Reducible (Ty.optionType A) o =
  SN(o) ∧ ∀ {M} {noneRaw someRaw} (noneBranch someBranch),
    SN(noneBranch) →
    (∀ v, Reducible A v → SN(Term.app someBranch v)) →
    SN(optionMatch o noneBranch someBranch)
```

Same mechanical shape as K12.20.J listType — eliminator output
is plain SN, NO recursive elementTypeCR2 hypothesis needed.
Term.optionMatch raw form is `RawTerm.optionMatch scrutineeRaw
noneRaw someRaw` (per Term.lean:216); `RawStep.par.optionMatch`
takes triple par steps (per RawPar.lean:136).  For CR2 the
branches use `par.refl` while scrutinee gets `rawStep.1`.
-/

/-- **K12.20.K optionType arm**: weak-elim-closure CR2 for
`Ty.optionType`.  Both SN-of-optionTerm and SN-of-optionMatch-
result are preserved by the same raw `step_preserves`.
Distinctness on optionMatch via ctor injectivity. -/
theorem Reducible.step_preserves_optionType
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.optionType elementType) sourceRaw}
    {target : Term context (Ty.optionType elementType) targetRaw}
    (sourceReducible :
        Reducible (Ty.optionType elementType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.optionType elementType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro motiveType noneRaw someRaw noneBranch someBranch noneSN someApplied
    have optionMatchStep : RawStep.parProgress
        (RawTerm.optionMatch sourceRaw noneRaw someRaw)
        (RawTerm.optionMatch targetRaw noneRaw someRaw) := by
      refine ⟨RawStep.par.optionMatch rawStep.1
          (RawStep.par.refl noneRaw) (RawStep.par.refl someRaw), ?_⟩
      intro optionMatchEq
      apply rawStep.2
      injection optionMatchEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 noneBranch someBranch noneSN someApplied) optionMatchStep

/-! ## K12.20.L typed CR2 lift — Ty.eitherType symmetric-weak-elim-closure compound arm

Seventh compound-arm CR2 lemma.  `Ty.eitherType` ships a
**symmetric weak elim closure** in K12.8: both `leftType` and
`rightType` are strict sub-Ty of `Ty.eitherType leftType
rightType`, so each branch's arrow shape matches K12.6 piTy weak
closure per side.  Closure shape (per Reducibility.lean:446):

```
Reducible (Ty.eitherType A B) e =
  SN(e) ∧ ∀ {M} {leftRaw rightRaw} (leftBranch rightBranch),
    (∀ v, Reducible A v → SN(Term.app leftBranch v)) →
    (∀ v, Reducible B v → SN(Term.app rightBranch v)) →
    SN(eitherMatch e leftBranch rightBranch)
```

Same mechanical shape as K12.20.J listType / K12.20.K
optionType — eliminator output is plain SN, NO recursive
leftTypeCR2 / rightTypeCR2 hypothesis needed.  Term.eitherMatch
raw form is `RawTerm.eitherMatch scrutineeRaw leftRaw rightRaw`
(per Term.lean:234); `RawStep.par.eitherMatch` takes triple par
steps (per RawPar.lean:159).  For CR2 the branches use
`par.refl` while scrutinee gets `rawStep.1`.
-/

/-- **K12.20.L eitherType arm**: symmetric-weak-elim-closure CR2
for `Ty.eitherType`.  Both SN-of-eitherTerm and SN-of-eitherMatch-
result are preserved by the same raw `step_preserves`.
Distinctness on eitherMatch via ctor injectivity. -/
theorem Reducible.step_preserves_eitherType
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.eitherType leftType rightType) sourceRaw}
    {target : Term context (Ty.eitherType leftType rightType) targetRaw}
    (sourceReducible :
        Reducible (Ty.eitherType leftType rightType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.eitherType leftType rightType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro motiveType leftRaw rightRaw leftBranch rightBranch leftApplied rightApplied
    have eitherMatchStep : RawStep.parProgress
        (RawTerm.eitherMatch sourceRaw leftRaw rightRaw)
        (RawTerm.eitherMatch targetRaw leftRaw rightRaw) := by
      refine ⟨RawStep.par.eitherMatch rawStep.1
          (RawStep.par.refl leftRaw) (RawStep.par.refl rightRaw), ?_⟩
      intro eitherMatchEq
      apply rawStep.2
      injection eitherMatchEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 leftBranch rightBranch leftApplied rightApplied)
      eitherMatchStep

/-! ## K12.20.M typed CR2 lift — Ty.path strong-pathApp-closure compound arm

Eighth compound-arm CR2 lemma.  `Ty.path` ships a **strong
pathApp closure** in K12.12: the eliminator produces a full
`Reducible carrier _` verdict (NOT plain SN), because `carrier`
is a strict sub-Ty of `Ty.path carrier left right` and the
structural-recursion-on-Ty checker admits `Reducible carrier`
recursion.  Closure shape (per Reducibility.lean:476):

```
Reducible (Ty.path A x y) p =
  SN(p) ∧ ∀ (modeIsUnivalent : mode = Mode.univalent)
            {intervalRaw} (intervalTerm : Term context Ty.interval intervalRaw),
    SN(intervalTerm) →
    Reducible A (Term.pathApp modeIsUnivalent p intervalTerm)
```

This is the **strong** pattern from K12.20.F arrow: full
Reducible eliminator output forces an explicit `carrierCR2`
hypothesis to lift Reducible across the cong step.  The interval
side stays SN-only (Ty.interval is a sibling Ty constructor, not
a strict sub-Ty of Ty.path — K12.4's closed-leaf arm gives
`Reducible Ty.interval _ = Term.isStronglyNormalizing _`
propositionally, so SN demotion preserves Tait semantics).

Term.pathApp raw form is `RawTerm.pathApp pathRaw intervalRaw`
(per Term.lean:355); `RawStep.par.pathAppCong` takes paired par
steps (per RawPar.lean:558).  For CR2, interval side gets
`par.refl` while path side gets `rawStep.1`.  Distinctness via
`injection` on RawTerm.pathApp.injEq.
-/

/-- **K12.20.M path arm**: strong-pathApp-closure CR2 for
`Ty.path`.  Takes `carrierCR2` as explicit hypothesis (the
recursive Reducible-preservation witness on the strict sub-Ty
`carrierType`).  SN-of-pathTerm preserved by raw `step_preserves`;
the full-Reducible pathApp conjunct lifted via carrierCR2 over
the pathAppCong step. -/
theorem Reducible.step_preserves_path
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context
        (Ty.path carrierType leftEndpoint rightEndpoint) sourceRaw}
    {target : Term context
        (Ty.path carrierType leftEndpoint rightEndpoint) targetRaw}
    (carrierCR2 :
        ∀ {pathAppSourceRaw pathAppTargetRaw : RawTerm scope}
          {pathAppSource : Term context carrierType pathAppSourceRaw}
          {pathAppTarget : Term context carrierType pathAppTargetRaw},
          Reducible carrierType pathAppSource →
          RawStep.parProgress pathAppSourceRaw pathAppTargetRaw →
          Reducible carrierType pathAppTarget)
    (sourceReducible :
        Reducible (Ty.path carrierType leftEndpoint rightEndpoint) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.path carrierType leftEndpoint rightEndpoint) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro modeIsUnivalent intervalRaw intervalTerm intervalSN
    have pathAppStep : RawStep.parProgress
        (RawTerm.pathApp sourceRaw intervalRaw)
        (RawTerm.pathApp targetRaw intervalRaw) := by
      refine ⟨RawStep.par.pathAppCong rawStep.1 (RawStep.par.refl intervalRaw), ?_⟩
      intro pathAppEq
      apply rawStep.2
      injection pathAppEq
    exact carrierCR2
      (sourceReducible.2 modeIsUnivalent intervalTerm intervalSN) pathAppStep

/-! ## K12.20.N typed CR2 lift — Ty.glue strong-glueElim-closure compound arm

Ninth compound-arm CR2 lemma.  `Ty.glue` ships a **strong
glueElim closure** in K12.12: the eliminator produces a full
`Reducible baseType _` verdict (NOT plain SN), because
`baseType` is a strict sub-Ty of `Ty.glue baseType
boundaryWitness` and the structural-recursion-on-Ty checker
admits `Reducible baseType` recursion.  Closure shape (per
Reducibility.lean:491):

```
Reducible (Ty.glue baseType _) gluedValue =
  SN(gluedValue) ∧
  ∀ (modeIsUnivalent : mode = Mode.univalent),
    Reducible baseType
      (Term.glueElim modeIsUnivalent gluedValue)
```

This is the **strong** pattern (mirror of K12.20.F arrow and
K12.20.M path), but **even simpler than path** — no quantifier
over an interval argument, no SN-on-arg conjunct.  Just the
mode-univalent witness binder.  The proof carries an explicit
`baseTypeCR2` hypothesis to lift Reducible across the cong step.

Term.glueElim raw form is `RawTerm.glueElim gluedRaw` (per
Term.lean:373); `RawStep.par.glueElimCong` is a 1-arg cong rule
taking just `gluedRawStep` (per RawPar.lean:633-638).  No paired
substituent: glueElim has only one argument.  Distinctness via
`injection` on `RawTerm.glueElim.injEq`.
-/

/-- **K12.20.N glue arm**: strong-glueElim-closure CR2 for
`Ty.glue`.  Takes `baseTypeCR2` as explicit hypothesis (the
recursive Reducible-preservation witness on the strict sub-Ty
`baseType`).  SN-of-gluedTerm preserved by raw `step_preserves`;
the full-Reducible glueElim conjunct lifted via baseTypeCR2 over
the glueElimCong step.  Simpler than K12.20.M path — single-
ctor cong rule, no interval binder. -/
theorem Reducible.step_preserves_glue
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.glue baseType boundaryWitness) sourceRaw}
    {target : Term context (Ty.glue baseType boundaryWitness) targetRaw}
    (baseTypeCR2 :
        ∀ {glueElimSourceRaw glueElimTargetRaw : RawTerm scope}
          {glueElimSource : Term context baseType glueElimSourceRaw}
          {glueElimTarget : Term context baseType glueElimTargetRaw},
          Reducible baseType glueElimSource →
          RawStep.parProgress glueElimSourceRaw glueElimTargetRaw →
          Reducible baseType glueElimTarget)
    (sourceReducible :
        Reducible (Ty.glue baseType boundaryWitness) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.glue baseType boundaryWitness) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro modeIsUnivalent
    have glueElimStep : RawStep.parProgress
        (RawTerm.glueElim sourceRaw)
        (RawTerm.glueElim targetRaw) := by
      refine ⟨RawStep.par.glueElimCong rawStep.1, ?_⟩
      intro glueElimEq
      apply rawStep.2
      injection glueElimEq
    exact baseTypeCR2
      (sourceReducible.2 modeIsUnivalent) glueElimStep

/-! ## K12.20.O typed CR2 lift — Ty.oeq weak-oeqJ-closure compound arm

Tenth compound-arm CR2 lemma.  `Ty.oeq` (HoTT observational
equality) ships a **weak oeqJ closure** in K12.10: the
eliminator output is plain SN, not full `Reducible motiveType _`.
The arbitrary `motiveType` is NOT a strict sub-Ty of
`Ty.oeq carrier left right` — structural-recursion-on-Ty would
not admit a `Reducible motiveType` recursive call (K12.6 / K12.9
weak-J pattern, identical to K12.20.I for Ty.id and the parametric
inductive weak elim arms K12.20.J/K/L).  Closure shape (per
Reducibility.lean:503-509):

```
Reducible (Ty.oeq _ _ _) witness =
  SN(witness) ∧
  ∀ {motiveType : Ty level scope}
    {baseRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw),
    SN baseCase →
    SN (Term.oeqJ baseCase witness)
```

Weak closure → **no recursive hypothesis needed**.  Eliminator
output is SN, so the cong lift goes via
`RawTerm.isStronglyNormalizing.step_preserves` directly.

Term.oeqJ raw form is `RawTerm.oeqJ baseRaw witnessRaw` (per
Term.lean:261); `RawStep.par.oeqJCong` takes paired par steps
on baseCase + witness (per RawPar.lean:705-710).  For CR2 the
baseCase rides `par.refl` (not progressing); witness rides
`rawStep.1`.  Distinctness via `injection` on
`RawTerm.oeqJ.injEq`.
-/

/-- **K12.20.O oeq arm**: weak-oeqJ-closure CR2 for `Ty.oeq`.
No recursive hypothesis needed (weak elim closure produces SN,
not Reducible).  SN-of-witnessTerm preserved by raw
`step_preserves`; SN-of-oeqJ-applied lifted via raw
`step_preserves` over the oeqJCong step.  Mirror of K12.20.I id
arm; differs only in the raw cong rule name (`oeqJCong` rather
than `idJ`). -/
theorem Reducible.step_preserves_oeq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context
        (Ty.oeq carrierType leftEndpoint rightEndpoint) sourceRaw}
    {target : Term context
        (Ty.oeq carrierType leftEndpoint rightEndpoint) targetRaw}
    (sourceReducible :
        Reducible (Ty.oeq carrierType leftEndpoint rightEndpoint) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.oeq carrierType leftEndpoint rightEndpoint) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro motiveType baseRaw baseCase baseSN
    have oeqJStep : RawStep.parProgress
        (RawTerm.oeqJ baseRaw sourceRaw)
        (RawTerm.oeqJ baseRaw targetRaw) := by
      refine ⟨RawStep.par.oeqJCong (RawStep.par.refl baseRaw) rawStep.1, ?_⟩
      intro oeqJEq
      apply rawStep.2
      injection oeqJEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 baseCase baseSN) oeqJStep

/-! ## K12.20.P typed CR2 lift — Ty.idStrict weak-idStrictRec-closure compound arm

Eleventh compound-arm CR2 lemma.  `Ty.idStrict` (strict identity
type) ships a **weak idStrictRec closure** in K12.10: the
eliminator output is plain SN, not full `Reducible motiveType _`.
The arbitrary `motiveType` is NOT a strict sub-Ty of
`Ty.idStrict carrier left right` — structural-recursion-on-Ty
cannot recurse `Reducible motiveType`.  Same K12.6 / K12.9 weak-J
pattern as K12.20.I (id) and K12.20.O (oeq).

Closure shape (per Reducibility.lean:517-525):

```
Reducible (Ty.idStrict _ _ _) witness =
  SN(witness) ∧
  ∀ (modeIsStrict : mode = Mode.strict)
    {motiveType : Ty level scope}
    {baseRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw),
    SN baseCase →
    SN (Term.idStrictRec modeIsStrict baseCase witness)
```

When `mode ≠ Mode.strict` the binder is uninhabited and the
inner ∀ is vacuous (closure reduces to SN(witness) alone) —
matches the conditional-elim K12.10 idStrict pattern.

Weak closure → **no recursive hypothesis needed**.  Eliminator
output is SN, so the cong lift goes via
`RawTerm.isStronglyNormalizing.step_preserves` directly.

Term.idStrictRec raw form is `RawTerm.idStrictRec baseRaw
witnessRaw` (per Term.lean:294) — the `modeIsStrict` proof lives
at the typed level only.  `RawStep.par.idStrictRecCong` takes
paired par steps on baseCase + witness (per RawPar.lean:724-729).
For CR2 the baseCase rides `par.refl`; witness rides `rawStep.1`.
Distinctness via `injection` on `RawTerm.idStrictRec.injEq`.
-/

/-- **K12.20.P idStrict arm**: weak-idStrictRec-closure CR2 for
`Ty.idStrict`.  No recursive hypothesis needed (weak elim
closure produces SN, not Reducible).  Identical structure to
K12.20.O oeq, with extra `modeIsStrict` binder threaded through
the per-mode quantifier in the closure body. -/
theorem Reducible.step_preserves_idStrict
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context
        (Ty.idStrict carrierType leftEndpoint rightEndpoint) sourceRaw}
    {target : Term context
        (Ty.idStrict carrierType leftEndpoint rightEndpoint) targetRaw}
    (sourceReducible :
        Reducible (Ty.idStrict carrierType leftEndpoint rightEndpoint) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.idStrict carrierType leftEndpoint rightEndpoint) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro modeIsStrict motiveType baseRaw baseCase baseSN
    have idStrictRecStep : RawStep.parProgress
        (RawTerm.idStrictRec baseRaw sourceRaw)
        (RawTerm.idStrictRec baseRaw targetRaw) := by
      refine ⟨RawStep.par.idStrictRecCong
        (RawStep.par.refl baseRaw) rawStep.1, ?_⟩
      intro idStrictRecEq
      apply rawStep.2
      injection idStrictRecEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 modeIsStrict baseCase baseSN) idStrictRecStep

/-! ## K12.20.Q typed CR2 lift — Ty.equiv strong-equivApp-closure compound arm

Twelfth compound-arm CR2 lemma.  `Ty.equiv carrierA carrierB`
(type equivalence) ships a **strong equivApp closure** in K12.11:
the eliminator produces full `Reducible carrierB (Term.equivApp
equivTerm argumentTerm)`.  BOTH `carrierA` and `carrierB` are
strict sub-Ty of `Ty.equiv carrierA carrierB` — structural-
recursion-on-Ty admits `Reducible carrierA` AND `Reducible
carrierB` recursive calls (K12.5 RC.arrow shape).

Closure shape (per Reducibility.lean:537-542):

```
Reducible (Ty.equiv carrierA carrierB) equivTerm =
  SN(equivTerm) ∧
  ∀ {argumentRaw : RawTerm scope}
    (argumentTerm : Term context carrierA argumentRaw),
    Reducible carrierA argumentTerm →
    Reducible carrierB
      (Term.equivApp equivTerm argumentTerm)
```

Structurally identical to K12.20.F arrow: `SN(f) ∧ ∀ arg,
Reducible A arg → Reducible B (Term.app f arg)`.  The argument
side stays at carrierA — it rides `par.refl` through the cong
step and does NOT progress.  Only `equivTerm` progresses; the
eliminator output is at carrierB, so the proof carries an
explicit `carrierBCR2` hypothesis to lift Reducible over the
equivAppCong step.  No `carrierACR2` is needed — that side never
moves in this cong step.

Term.equivApp raw form is `RawTerm.equivApp equivRaw argumentRaw`
(per Term.lean:727); `RawStep.par.equivAppCong` takes paired par
steps on equiv + argument (per RawPar.lean:738-743).  For CR2
the equiv side rides `rawStep.1`; argument side rides
`par.refl`.  Distinctness via `injection` on
`RawTerm.equivApp.injEq`.
-/

/-- **K12.20.Q equiv arm**: strong-equivApp-closure CR2 for
`Ty.equiv`.  Takes `carrierBCR2` as explicit hypothesis (the
recursive Reducible-preservation witness on the strict sub-Ty
`carrierB`).  SN-of-equivTerm preserved by raw `step_preserves`;
the full-Reducible equivApp conjunct lifted via carrierBCR2 over
the equivAppCong step.  Structurally identical to K12.20.F arrow;
differs only in raw cong rule name (`equivAppCong` vs `app`) and
ctor (`equivApp` vs `app`). -/
theorem Reducible.step_preserves_equiv
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.equiv carrierA carrierB) sourceRaw}
    {target : Term context (Ty.equiv carrierA carrierB) targetRaw}
    (carrierBCR2 :
        ∀ {equivAppSourceRaw equivAppTargetRaw : RawTerm scope}
          {equivAppSource : Term context carrierB equivAppSourceRaw}
          {equivAppTarget : Term context carrierB equivAppTargetRaw},
          Reducible carrierB equivAppSource →
          RawStep.parProgress equivAppSourceRaw equivAppTargetRaw →
          Reducible carrierB equivAppTarget)
    (sourceReducible :
        Reducible (Ty.equiv carrierA carrierB) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.equiv carrierA carrierB) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro argumentRaw argumentTerm argumentReducible
    have equivAppStep : RawStep.parProgress
        (RawTerm.equivApp sourceRaw argumentRaw)
        (RawTerm.equivApp targetRaw argumentRaw) := by
      refine ⟨RawStep.par.equivAppCong rawStep.1
        (RawStep.par.refl argumentRaw), ?_⟩
      intro equivAppEq
      apply rawStep.2
      injection equivAppEq
    exact carrierBCR2
      (sourceReducible.2 argumentTerm argumentReducible) equivAppStep

/-! ## K12.20.R typed CR2 lift — Ty.refine strong-refineElim-closure compound arm

Thirteenth compound-arm CR2 lemma.  `Ty.refine baseType
predicate` ships a **strong refineElim closure** in K12.14:
the eliminator produces full `Reducible baseType (Term.refineElim
refinedValue)` from the simple projection.  `baseType` is a
strict sub-Ty of `Ty.refine baseType predicate` — structural-
recursion-on-Ty admits `Reducible baseType` recursive call.
The `predicate : RawTerm (scope+1)` is a RawTerm-binder with no
typed dependency at the Reducible layer; the "Decidable
predicate discharge" aspect of K12.14 lives at Layer 5 SMT-
recheck (#1342 D5.6, #1344 D5.8) and is orthogonal to the
Reducibility-candidate closure shipped here.

Closure shape (per Reducibility.lean:554-556):

```
Reducible (Ty.refine baseType _) refinedValue =
  SN(refinedValue) ∧
  Reducible baseType (Term.refineElim refinedValue)
```

This is the **simplest** strong compound arm of the 15.  No
quantifier overhead, no mode-univalent / mode-strict witness,
no interval / motive binder.  Pure projection — directly
analogous to K12.20.N glue but stripped down further (no
modeIsUnivalent binder).

Term.refineElim raw form is `RawTerm.refineElim refinedRaw`
(per Term.lean:446); `RawStep.par.refineElimCong` is a 1-arg
cong rule taking just `refinedRawStep` (per RawPar.lean:766-771).
Single-substituent ctor → no `par.refl` companion needed.
Distinctness via `injection` on `RawTerm.refineElim.injEq`.
-/

/-- **K12.20.R refine arm**: strong-refineElim-closure CR2 for
`Ty.refine`.  Takes `baseTypeCR2` as explicit hypothesis (the
recursive Reducible-preservation witness on the strict sub-Ty
`baseType`).  SN-of-refinedValue preserved by raw
`step_preserves`; the full-Reducible refineElim conjunct lifted
via baseTypeCR2 over the refineElimCong step.  Simplest strong
compound arm — no quantifier, no mode binder. -/
theorem Reducible.step_preserves_refine
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.refine baseType predicate) sourceRaw}
    {target : Term context (Ty.refine baseType predicate) targetRaw}
    (baseTypeCR2 :
        ∀ {refineElimSourceRaw refineElimTargetRaw : RawTerm scope}
          {refineElimSource : Term context baseType refineElimSourceRaw}
          {refineElimTarget : Term context baseType refineElimTargetRaw},
          Reducible baseType refineElimSource →
          RawStep.parProgress refineElimSourceRaw refineElimTargetRaw →
          Reducible baseType refineElimTarget)
    (sourceReducible :
        Reducible (Ty.refine baseType predicate) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.refine baseType predicate) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · have refineElimStep : RawStep.parProgress
        (RawTerm.refineElim sourceRaw)
        (RawTerm.refineElim targetRaw) := by
      refine ⟨RawStep.par.refineElimCong rawStep.1, ?_⟩
      intro refineElimEq
      apply rawStep.2
      injection refineElimEq
    exact baseTypeCR2 sourceReducible.2 refineElimStep

/-! ## K12.20.S typed CR2 lift — Ty.record strong-recordProj-closure compound arm

Fourteenth compound-arm CR2 lemma.  `Ty.record singleFieldType`
ships a **strong recordProj closure** in K12.15: the eliminator
produces full `Reducible singleFieldType (Term.recordProj
recordValue)` from the simple projection.  `singleFieldType` is
a strict sub-Ty of `Ty.record singleFieldType` — structural-
recursion-on-Ty admits `Reducible singleFieldType` recursive
call.  Multi-field records compose via nested single-field
records (per Term.lean docstring), preserving this closure
shape under nesting.

Closure shape (per Reducibility.lean:563-565):

```
Reducible (Ty.record singleFieldType) recordValue =
  SN(recordValue) ∧
  Reducible singleFieldType (Term.recordProj recordValue)
```

Structurally identical to K12.20.R refine: pure projection,
single-substituent cong rule, no quantifier overhead.  Only
differences: ctor name (`Ty.record` vs `Ty.refine`), eliminator
(`recordProj` vs `refineElim`), strict-sub-Ty field name
(`singleFieldType` vs `baseType`).  No predicate binder (record
has no SMT-recheck axis — purely structural).

Term.recordProj raw form is `RawTerm.recordProj recordRaw` (per
Term.lean:425); `RawStep.par.recordProjCong` is a 1-arg cong
rule (per RawPar.lean:790-795).  Distinctness via `injection`
on `RawTerm.recordProj.injEq`.
-/

/-- **K12.20.S record arm**: strong-recordProj-closure CR2 for
`Ty.record`.  Takes `singleFieldTypeCR2` as explicit hypothesis
(the recursive Reducible-preservation witness on the strict
sub-Ty `singleFieldType`).  SN-of-recordValue preserved by raw
`step_preserves`; the full-Reducible recordProj conjunct lifted
via singleFieldTypeCR2 over the recordProjCong step.  Mirror of
K12.20.R refine. -/
theorem Reducible.step_preserves_record
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.record singleFieldType) sourceRaw}
    {target : Term context (Ty.record singleFieldType) targetRaw}
    (singleFieldTypeCR2 :
        ∀ {recordProjSourceRaw recordProjTargetRaw : RawTerm scope}
          {recordProjSource :
              Term context singleFieldType recordProjSourceRaw}
          {recordProjTarget :
              Term context singleFieldType recordProjTargetRaw},
          Reducible singleFieldType recordProjSource →
          RawStep.parProgress recordProjSourceRaw recordProjTargetRaw →
          Reducible singleFieldType recordProjTarget)
    (sourceReducible : Reducible (Ty.record singleFieldType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.record singleFieldType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · have recordProjStep : RawStep.parProgress
        (RawTerm.recordProj sourceRaw)
        (RawTerm.recordProj targetRaw) := by
      refine ⟨RawStep.par.recordProjCong rawStep.1, ?_⟩
      intro recordProjEq
      apply rawStep.2
      injection recordProjEq
    exact singleFieldTypeCR2 sourceReducible.2 recordProjStep

/-! ## K12.20.T typed CR2 lift — Ty.codata strong-codataDest-closure compound arm

Fifteenth (and final) compound-arm CR2 lemma.  `Ty.codata
stateType outputType` ships a **strong codataDest closure** in
K12.15: the eliminator produces full `Reducible outputType
(Term.codataDest codataValue)` from the observation projection.
`outputType` is a strict sub-Ty of `Ty.codata stateType
outputType` — structural-recursion-on-Ty admits the recursive
`Reducible outputType` call.

Closure shape (per Reducibility.lean:574-576):

```
Reducible (Ty.codata _ outputType) codataValue =
  SN(codataValue) ∧
  Reducible outputType (Term.codataDest codataValue)
```

Note: `stateType` is also a strict sub-Ty of `Ty.codata
stateType outputType`, but the closure does NOT recurse on it
— the stateType is packed into the unfold/initial-state and is
never exposed by an eliminator.  Productivity-checking at higher
observation depths lives at the codata-corecursion Layer (#1267
K08), orthogonal to this RC closure.  So this lemma needs only
ONE recursive-CR2 hypothesis (`outputTypeCR2`).

Structurally identical to K12.20.{R refine, S record}: pure
projection, single-substituent cong rule, no quantifier
overhead.  Only differences: ctor name (`Ty.codata` takes two
Ty args — `stateType` carried implicit, only `outputType`
appears in the recursive hypothesis), eliminator
(`codataDest` vs `recordProj`).

Term.codataDest raw form is `RawTerm.codataDest codataRaw` (per
Term.lean:460-465); `RawStep.par.codataDestCong` is a 1-arg
cong rule (per RawPar.lean:820-825).  Distinctness via
`injection` on `RawTerm.codataDest.injEq`.

**Compound-arm CR2 sweep COMPLETE** with this lemma: all 15
compound-arm closures shipped (arrow / piTy / sigmaTy / id /
listType / optionType / eitherType / path / glue / oeq /
idStrict / equiv / refine / record / codata).  Next: K12.20
wrap-up combining all 25 arms (10 SN-direct + 15 compound) into
a single structurally-recursive `Reducible.step_preserves`.
-/

/-- **K12.20.T codata arm**: strong-codataDest-closure CR2 for
`Ty.codata`.  Takes `outputTypeCR2` as explicit hypothesis (the
recursive Reducible-preservation witness on the strict sub-Ty
`outputType` — the projection target).  SN-of-codataValue
preserved by raw `step_preserves`; the full-Reducible
codataDest conjunct lifted via outputTypeCR2 over the
codataDestCong step.  Mirror of K12.20.{R refine, S record}.
The `stateType` index is carried implicit and never reached —
codata's state is packed into the unfold/initial-state, not
exposed by any current eliminator. -/
theorem Reducible.step_preserves_codata
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.codata stateType outputType) sourceRaw}
    {target : Term context (Ty.codata stateType outputType) targetRaw}
    (outputTypeCR2 :
        ∀ {codataDestSourceRaw codataDestTargetRaw : RawTerm scope}
          {codataDestSource :
              Term context outputType codataDestSourceRaw}
          {codataDestTarget :
              Term context outputType codataDestTargetRaw},
          Reducible outputType codataDestSource →
          RawStep.parProgress codataDestSourceRaw codataDestTargetRaw →
          Reducible outputType codataDestTarget)
    (sourceReducible :
        Reducible (Ty.codata stateType outputType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.codata stateType outputType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · have codataDestStep : RawStep.parProgress
        (RawTerm.codataDest sourceRaw)
        (RawTerm.codataDest targetRaw) := by
      refine ⟨RawStep.par.codataDestCong rawStep.1, ?_⟩
      intro codataDestEq
      apply rawStep.2
      injection codataDestEq
    exact outputTypeCR2 sourceReducible.2 codataDestStep

/-! ## K12.20.U typed CR2 wrap-up — unified `Reducible.step_preserves`

Combined headline lemma bundling all 25 per-arm CR2 helpers
(K12.20.{C-T}) into a single structurally-recursive theorem on
Ty.  Each Ty constructor's arm dispatches to the matching per-
arm helper; the eight **strong-compound** arms (arrow / sigmaTy
/ path / glue / equiv / refine / record / codata) receive their
`subTyCR2` hypothesis as a recursive `Reducible.step_preserves`
call at the strict sub-Ty position.  This is the canonical CR2
lemma downstream fundamental-theorem cases (K12.21-K12.26) will
consume — no manual per-arm dispatch needed at each call site.

**Termination**: structural recursion on `ty : Ty level scope`.
Recursive calls land on strict sub-Ty positions ONLY, all at
the SAME scope as the parent ctor:

* `Ty.arrow _ codomain`: recurses on `codomain`
* `Ty.sigmaTy first _`: recurses on `first` (secondType lives
  at scope+1 — sigmaTy's CR2 closure only needs firstType)
* `Ty.path carrier _ _`: recurses on `carrier` (left/right are
  RawTerm endpoints, not Ty)
* `Ty.glue base _`: recurses on `base` (boundary is RawTerm)
* `Ty.equiv _ carrierB`: recurses on `carrierB`
* `Ty.refine base _`: recurses on `base` (predicate is RawTerm)
* `Ty.record single`: recurses on `single`
* `Ty.codata _ output`: recurses on `output` (stateType is
  packed into unfold/initial-state, not exposed)

Every recursive call lands at the SAME (level, scope) as the
parent ctor — this sidesteps the **sibling-Ty wall** and the
**substituted-codomain wall** (per
`feedback_lean_reducible_sibling_ty_block.md`).  The 7 weak-
compound arms (piTy / id / idStrict / oeq / listType /
optionType / eitherType) and the 10 SN-direct arms (unit /
bool / nat / empty / interval / universe / tyVar / session /
effect / modal) make NO recursive call — they just dispatch.

**Compound-arm CR2 sweep COMPLETE** with this wrap-up: 15
strong/weak compound + 10 SN-direct = all 25 Ty constructors
covered.  Next: K12.20.V — `ReducibleSubst.singleton` / `lift`
infrastructure for the Term.lam fundamental-theorem case
proper, plus K12.21-K12.26 fundamental theorem cases. -/
theorem Reducible.step_preserves
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    ∀ (ty : Ty level scope)
      {sourceRaw targetRaw : RawTerm scope}
      {source : Term context ty sourceRaw}
      {target : Term context ty targetRaw},
      Reducible ty source →
      RawStep.parProgress sourceRaw targetRaw →
      Reducible ty target
  -- SN-direct arms (10): plain SN preservation.
  | Ty.unit, _, _, _, _ => Reducible.step_preserves_unit
  | Ty.bool, _, _, _, _ => Reducible.step_preserves_bool
  | Ty.nat,  _, _, _, _ => Reducible.step_preserves_nat
  | Ty.empty, _, _, _, _ => Reducible.step_preserves_empty
  | Ty.interval, _, _, _, _ => Reducible.step_preserves_interval
  | Ty.universe _ _, _, _, _, _ => Reducible.step_preserves_universe
  | Ty.tyVar _, _, _, _, _ => Reducible.step_preserves_tyVar
  | Ty.session _, _, _, _, _ => Reducible.step_preserves_session
  | Ty.effect _ _, _, _, _, _ => Reducible.step_preserves_effect
  | Ty.modal _ _, _, _, _, _ => Reducible.step_preserves_modal
  -- Weak-compound arms (7): SN-only closure, no subTyCR2 hypothesis.
  | Ty.piTy _ _, _, _, _, _ => Reducible.step_preserves_piTy
  | Ty.id _ _ _, _, _, _, _ => Reducible.step_preserves_id
  | Ty.idStrict _ _ _, _, _, _, _ => Reducible.step_preserves_idStrict
  | Ty.oeq _ _ _, _, _, _, _ => Reducible.step_preserves_oeq
  | Ty.listType _, _, _, _, _ => Reducible.step_preserves_listType
  | Ty.optionType _, _, _, _, _ => Reducible.step_preserves_optionType
  | Ty.eitherType _ _, _, _, _, _ => Reducible.step_preserves_eitherType
  -- Strong-compound arms (8): subTyCR2 dispatched via recursive
  -- `Reducible.step_preserves` at the strict sub-Ty position.
  | Ty.arrow _ codomain, _, _, _, _ =>
      fun reducible rawStep =>
        Reducible.step_preserves_arrow reducible rawStep
          (Reducible.step_preserves codomain)
  | Ty.sigmaTy first _, _, _, _, _ =>
      fun reducible rawStep =>
        Reducible.step_preserves_sigmaTy
          (Reducible.step_preserves first) reducible rawStep
  | Ty.path carrier _ _, _, _, _, _ =>
      fun reducible rawStep =>
        Reducible.step_preserves_path
          (Reducible.step_preserves carrier) reducible rawStep
  | Ty.glue base _, _, _, _, _ =>
      fun reducible rawStep =>
        Reducible.step_preserves_glue
          (Reducible.step_preserves base) reducible rawStep
  | Ty.equiv _ carrierB, _, _, _, _ =>
      fun reducible rawStep =>
        Reducible.step_preserves_equiv
          (Reducible.step_preserves carrierB) reducible rawStep
  | Ty.refine base _, _, _, _, _ =>
      fun reducible rawStep =>
        Reducible.step_preserves_refine
          (Reducible.step_preserves base) reducible rawStep
  | Ty.record single, _, _, _, _ =>
      fun reducible rawStep =>
        Reducible.step_preserves_record
          (Reducible.step_preserves single) reducible rawStep
  | Ty.codata _ output, _, _, _, _ =>
      fun reducible rawStep =>
        Reducible.step_preserves_codata
          (Reducible.step_preserves output) reducible rawStep

/-- **K12.20.V natSucc case** — first unary recursive introducer.
Reducible at Ty.nat unfolds to SN; subst commutes with natSucc
definitionally; raw lift via `RawTerm.natSucc_isStronglyNormalizing`. -/
theorem Reducible.fundamental_natSucc
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {predRaw : RawTerm scope}
    {predecessor : Term sourceCtx Ty.nat predRaw}
    (predIH : Reducible ((Ty.nat : Ty level scope).subst sigma)
                        (Term.subst termSubst predecessor)) :
    Reducible ((Ty.nat : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.natSucc predecessor)) :=
  RawTerm.natSucc_isStronglyNormalizing predIH

/-- **K12.20.AO.1 intervalOpp fundamental case** — cubical interval
negation.  Unary intro to the closed-leaf `Ty.interval`; identical
single-line pattern as `fundamental_natSucc`. -/
theorem Reducible.fundamental_intervalOpp
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerValue : Term sourceCtx Ty.interval innerRaw}
    (innerIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                         (Term.subst termSubst innerValue)) :
    Reducible ((Ty.interval : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.intervalOpp innerValue)) :=
  RawTerm.intervalOpp_isStronglyNormalizing innerIH

/-- **K12.20.AO.2 intervalMeet fundamental case** — cubical interval
meet (∧).  Binary intro to `Ty.interval`; both subterms substitute
componentwise and the binary SN helper closes both arguments. -/
theorem Reducible.fundamental_intervalMeet
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                        (Term.subst termSubst leftValue))
    (rightIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                         (Term.subst termSubst rightValue)) :
    Reducible ((Ty.interval : Ty level scope).subst sigma)
              (Term.subst termSubst
                (Term.intervalMeet leftValue rightValue)) :=
  RawTerm.intervalMeet_isStronglyNormalizing leftIH rightIH

/-- **K12.20.AO.3 intervalJoin fundamental case** — cubical interval
join (∨).  Sister to intervalMeet; same binary shape. -/
theorem Reducible.fundamental_intervalJoin
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                        (Term.subst termSubst leftValue))
    (rightIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                         (Term.subst termSubst rightValue)) :
    Reducible ((Ty.interval : Ty level scope).subst sigma)
              (Term.subst termSubst
                (Term.intervalJoin leftValue rightValue)) :=
  RawTerm.intervalJoin_isStronglyNormalizing leftIH rightIH

/-- **K12.20.AP.1 sessionRecv fundamental case** — session-type
receive operation.  Result type `Ty.session protocolStep` is
SN-direct (`Reducibility.lean:667`); `Term.subst` distributes
componentwise over `sessionRecv`
(`LeanFX2/Term/Subst.lean:363-364`); the unary K12.20.AL.1 SN
helper closes the proof in one line. -/
theorem Reducible.fundamental_sessionRecv
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    (channelIH : Reducible ((Ty.session protocolStep).subst sigma)
                           (Term.subst termSubst channel)) :
    Reducible ((Ty.session protocolStep).subst sigma)
              (Term.subst termSubst (Term.sessionRecv channel)) :=
  RawTerm.sessionRecv_isStronglyNormalizing channelIH

/-- **K12.20.AP.2 sessionSend fundamental case** — session-type
send operation bundles a channel with an arbitrary-typed payload.
Channel lives at `Ty.session protocolStep` (SN-direct) so `channelIH`
IS SN; payload lives at arbitrary `payloadType`, so its SN witness
is extracted via the K12.18 closure-elimination lemma
`Reducible.isStronglyNormalizing` (lines 639-669) before feeding
the K12.20.AL.2 binary helper. -/
theorem Reducible.fundamental_sessionSend
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {protocolStep : RawTerm scope}
    {payloadType : Ty level scope}
    {channelRaw payloadRaw : RawTerm scope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    {payload : Term sourceCtx payloadType payloadRaw}
    (channelIH : Reducible ((Ty.session protocolStep).subst sigma)
                           (Term.subst termSubst channel))
    (payloadIH : Reducible (payloadType.subst sigma)
                           (Term.subst termSubst payload)) :
    Reducible ((Ty.session protocolStep).subst sigma)
              (Term.subst termSubst
                (Term.sessionSend protocolStep channel payload)) :=
  RawTerm.sessionSend_isStronglyNormalizing channelIH
    (Reducible.isStronglyNormalizing payloadIH)

end LeanFX2
