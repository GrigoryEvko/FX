import LeanFX2.Term
import LeanFX2.Term.Subst
import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Reduction.RawParCompatible

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

/-! ## K12.20.U2 neutral vocabulary

CR3 needs a syntactic class of neutral terms: variables and terms
stuck on an eliminator whose principal scrutinee is neutral.  This
predicate deliberately excludes introduction forms (`lam`, `pair`,
constructors, records, refinements, codes) because those either are
values or have their own beta/iota head rule.

The predicate carries only neutrality, not strong-normalization of
side arguments.  Later CR3 lemmas combine this neutral shape with the
CR3 premise "every reduct is reducible" and the existing neutral-head
SN helper family below. -/
inductive RawTerm.IsNeutral : ∀ {scope : Nat}, RawTerm scope → Prop
  | var {scope : Nat} (position : Fin scope) :
      RawTerm.IsNeutral (RawTerm.var position)
  | app {scope : Nat} {functionTerm argumentTerm : RawTerm scope}
      (functionIsNeutral : RawTerm.IsNeutral functionTerm) :
      RawTerm.IsNeutral (RawTerm.app functionTerm argumentTerm)
  | fst {scope : Nat} {pairTerm : RawTerm scope}
      (pairIsNeutral : RawTerm.IsNeutral pairTerm) :
      RawTerm.IsNeutral (RawTerm.fst pairTerm)
  | snd {scope : Nat} {pairTerm : RawTerm scope}
      (pairIsNeutral : RawTerm.IsNeutral pairTerm) :
      RawTerm.IsNeutral (RawTerm.snd pairTerm)
  | boolElim {scope : Nat}
      {scrutinee thenBranch elseBranch : RawTerm scope}
      (scrutineeIsNeutral : RawTerm.IsNeutral scrutinee) :
      RawTerm.IsNeutral
        (RawTerm.boolElim scrutinee thenBranch elseBranch)
  | natElim {scope : Nat}
      {scrutinee zeroBranch succBranch : RawTerm scope}
      (scrutineeIsNeutral : RawTerm.IsNeutral scrutinee) :
      RawTerm.IsNeutral
        (RawTerm.natElim scrutinee zeroBranch succBranch)
  | natRec {scope : Nat}
      {scrutinee zeroBranch succBranch : RawTerm scope}
      (scrutineeIsNeutral : RawTerm.IsNeutral scrutinee) :
      RawTerm.IsNeutral
        (RawTerm.natRec scrutinee zeroBranch succBranch)
  | listElim {scope : Nat}
      {scrutinee nilBranch consBranch : RawTerm scope}
      (scrutineeIsNeutral : RawTerm.IsNeutral scrutinee) :
      RawTerm.IsNeutral
        (RawTerm.listElim scrutinee nilBranch consBranch)
  | optionMatch {scope : Nat}
      {scrutinee noneBranch someBranch : RawTerm scope}
      (scrutineeIsNeutral : RawTerm.IsNeutral scrutinee) :
      RawTerm.IsNeutral
        (RawTerm.optionMatch scrutinee noneBranch someBranch)
  | eitherMatch {scope : Nat}
      {scrutinee leftBranch rightBranch : RawTerm scope}
      (scrutineeIsNeutral : RawTerm.IsNeutral scrutinee) :
      RawTerm.IsNeutral
        (RawTerm.eitherMatch scrutinee leftBranch rightBranch)
  | pathApp {scope : Nat}
      {pathTerm intervalArg : RawTerm scope}
      (pathIsNeutral : RawTerm.IsNeutral pathTerm) :
      RawTerm.IsNeutral (RawTerm.pathApp pathTerm intervalArg)
  | glueElim {scope : Nat} {gluedValue : RawTerm scope}
      (gluedValueIsNeutral : RawTerm.IsNeutral gluedValue) :
      RawTerm.IsNeutral (RawTerm.glueElim gluedValue)
  | transp {scope : Nat} {path source : RawTerm scope}
      (pathIsNeutral : RawTerm.IsNeutral path) :
      RawTerm.IsNeutral (RawTerm.transp path source)
  | hcomp {scope : Nat} {sides cap : RawTerm scope}
      (sidesIsNeutral : RawTerm.IsNeutral sides) :
      RawTerm.IsNeutral (RawTerm.hcomp sides cap)
  | idJ {scope : Nat} {baseCase witness : RawTerm scope}
      (witnessIsNeutral : RawTerm.IsNeutral witness) :
      RawTerm.IsNeutral (RawTerm.idJ baseCase witness)
  | oeqJ {scope : Nat} {baseCase witness : RawTerm scope}
      (witnessIsNeutral : RawTerm.IsNeutral witness) :
      RawTerm.IsNeutral (RawTerm.oeqJ baseCase witness)
  | idStrictRec {scope : Nat} {baseCase witness : RawTerm scope}
      (witnessIsNeutral : RawTerm.IsNeutral witness) :
      RawTerm.IsNeutral (RawTerm.idStrictRec baseCase witness)
  | equivApp {scope : Nat} {equivTerm argument : RawTerm scope}
      (equivIsNeutral : RawTerm.IsNeutral equivTerm) :
      RawTerm.IsNeutral (RawTerm.equivApp equivTerm argument)
  | equivApply {scope : Nat} {equivRaw argRaw : RawTerm scope}
      (equivIsNeutral : RawTerm.IsNeutral equivRaw) :
      RawTerm.IsNeutral (RawTerm.equivApply equivRaw argRaw)
  | modElim {scope : Nat} {raw : RawTerm scope}
      (rawIsNeutral : RawTerm.IsNeutral raw) :
      RawTerm.IsNeutral (RawTerm.modElim raw)
  | subsume {scope : Nat} {raw : RawTerm scope}
      (rawIsNeutral : RawTerm.IsNeutral raw) :
      RawTerm.IsNeutral (RawTerm.subsume raw)
  | refineElim {scope : Nat} {refinedValue : RawTerm scope}
      (refinedValueIsNeutral : RawTerm.IsNeutral refinedValue) :
      RawTerm.IsNeutral (RawTerm.refineElim refinedValue)
  | recordProj {scope : Nat} {recordValue : RawTerm scope}
      (recordValueIsNeutral : RawTerm.IsNeutral recordValue) :
      RawTerm.IsNeutral (RawTerm.recordProj recordValue)
  | codataDest {scope : Nat} {codataValue : RawTerm scope}
      (codataValueIsNeutral : RawTerm.IsNeutral codataValue) :
      RawTerm.IsNeutral (RawTerm.codataDest codataValue)
  | sessionSend {scope : Nat} {channel payload : RawTerm scope}
      (channelIsNeutral : RawTerm.IsNeutral channel) :
      RawTerm.IsNeutral (RawTerm.sessionSend channel payload)
  | sessionRecv {scope : Nat} {channel : RawTerm scope}
      (channelIsNeutral : RawTerm.IsNeutral channel) :
      RawTerm.IsNeutral (RawTerm.sessionRecv channel)
  | effectPerform {scope : Nat}
      {operationTag arguments : RawTerm scope}
      (operationIsNeutral : RawTerm.IsNeutral operationTag) :
      RawTerm.IsNeutral
        (RawTerm.effectPerform operationTag arguments)

/-- Neutral raw terms are never lambda-shaped. -/
theorem RawTerm.IsNeutral.not_lam {scope : Nat}
    {source : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source)
    {bodyRaw : RawTerm (scope + 1)} :
    source ≠ RawTerm.lam bodyRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never pair-shaped. -/
theorem RawTerm.IsNeutral.not_pair {scope : Nat}
    {source firstRaw secondRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.pair firstRaw secondRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never `true`. -/
theorem RawTerm.IsNeutral.not_boolTrue {scope : Nat}
    {source : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.boolTrue := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never `false`. -/
theorem RawTerm.IsNeutral.not_boolFalse {scope : Nat}
    {source : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.boolFalse := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never `natZero`. -/
theorem RawTerm.IsNeutral.not_natZero {scope : Nat}
    {source : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.natZero := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never successor-shaped. -/
theorem RawTerm.IsNeutral.not_natSucc {scope : Nat}
    {source predecessorRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.natSucc predecessorRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never empty-list-shaped. -/
theorem RawTerm.IsNeutral.not_listNil {scope : Nat}
    {source : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.listNil := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never list-cons-shaped. -/
theorem RawTerm.IsNeutral.not_listCons {scope : Nat}
    {source headRaw tailRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.listCons headRaw tailRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never option-none-shaped. -/
theorem RawTerm.IsNeutral.not_optionNone {scope : Nat}
    {source : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.optionNone := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never option-some-shaped. -/
theorem RawTerm.IsNeutral.not_optionSome {scope : Nat}
    {source valueRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.optionSome valueRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never either-left-shaped. -/
theorem RawTerm.IsNeutral.not_eitherInl {scope : Nat}
    {source valueRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.eitherInl valueRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never either-right-shaped. -/
theorem RawTerm.IsNeutral.not_eitherInr {scope : Nat}
    {source valueRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.eitherInr valueRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never cubical-path-lambda-shaped. -/
theorem RawTerm.IsNeutral.not_pathLam {scope : Nat}
    {source : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source)
    {bodyRaw : RawTerm (scope + 1)} :
    source ≠ RawTerm.pathLam bodyRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never glue-intro-shaped. -/
theorem RawTerm.IsNeutral.not_glueIntro {scope : Nat}
    {source baseRaw partialRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.glueIntro baseRaw partialRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never identity-refl-shaped. -/
theorem RawTerm.IsNeutral.not_refl {scope : Nat}
    {source witnessRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.refl witnessRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never observational-refl-shaped. -/
theorem RawTerm.IsNeutral.not_oeqRefl {scope : Nat}
    {source witnessRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.oeqRefl witnessRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never strict-identity-refl-shaped. -/
theorem RawTerm.IsNeutral.not_idStrictRefl {scope : Nat}
    {source witnessRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.idStrictRefl witnessRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never equivalence-intro-shaped. -/
theorem RawTerm.IsNeutral.not_equivIntro {scope : Nat}
    {source forwardRaw backwardRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.equivIntro forwardRaw backwardRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never univalence-to-equivalence shaped. -/
theorem RawTerm.IsNeutral.not_uaToEquiv {scope : Nat}
    {source proofRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.uaToEquiv proofRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never path-composition shaped. -/
theorem RawTerm.IsNeutral.not_pathCompose {scope : Nat}
    {source leftRaw rightRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.pathCompose leftRaw rightRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never modal-intro-shaped. -/
theorem RawTerm.IsNeutral.not_modIntro {scope : Nat}
    {source valueRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.modIntro valueRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never refinement-intro-shaped. -/
theorem RawTerm.IsNeutral.not_refineIntro {scope : Nat}
    {source valueRaw proofRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.refineIntro valueRaw proofRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never record-intro-shaped. -/
theorem RawTerm.IsNeutral.not_recordIntro {scope : Nat}
    {source fieldRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.recordIntro fieldRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never codata-unfold-shaped. -/
theorem RawTerm.IsNeutral.not_codataUnfold {scope : Nat}
    {source initialRaw transitionRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.codataUnfold initialRaw transitionRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-! ### K12.20.U2 neutral preservation under raw parallel development

These higher-order one-step preservation lemmas are the local shape
facts needed by compound CR3.  Each lemma assumes preservation for the
principal neutral subterm and proves preservation for one eliminator
wrapper.  Keeping the lemmas higher-order mirrors the `varShape` and
`step_preserves` architecture: the later global CR3/par-preservation
dispatcher supplies the recursive hook, while these atoms discharge the
constructor-specific beta/iota-impossible cases exactly once.
-/

/-- A variable can only parallel-develop to itself, so neutrality is
preserved by one raw parallel step from a variable. -/
theorem RawTerm.IsNeutral.var_par_preserves {scope : Nat}
    {position : Fin scope} {targetRaw : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.var position) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  have targetEq : targetRaw = RawTerm.var position :=
    RawStep.par.var_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.var position

/-- Neutrality is preserved by one raw parallel step from a neutral
application, assuming preservation for the function head. -/
theorem RawTerm.IsNeutral.app_par_preserves {scope : Nat}
    {functionRaw argumentRaw targetRaw : RawTerm scope}
    (functionParPreserves :
      ∀ {functionTarget : RawTerm scope},
        RawStep.par functionRaw functionTarget →
        RawTerm.IsNeutral functionTarget)
    (parallelStep :
      RawStep.par (RawTerm.app functionRaw argumentRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.app_inv parallelStep with
    ⟨functionTarget, argumentTarget, targetEq,
      functionStep, _argumentStep⟩
    | ⟨bodyTarget, _argumentTarget, _targetEq,
        functionStep, _argumentStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.app (functionParPreserves functionStep)
  · exact (RawTerm.IsNeutral.not_lam
      (functionParPreserves functionStep) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `fst` of a
neutral pair scrutinee. -/
theorem RawTerm.IsNeutral.fst_par_preserves {scope : Nat}
    {pairRaw targetRaw : RawTerm scope}
    (pairParPreserves :
      ∀ {pairTarget : RawTerm scope},
        RawStep.par pairRaw pairTarget →
        RawTerm.IsNeutral pairTarget)
    (parallelStep : RawStep.par (RawTerm.fst pairRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.fst_inv parallelStep with
    ⟨pairTarget, targetEq, pairStep⟩
    | ⟨firstTarget, secondTarget, _targetEq, pairStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.fst (pairParPreserves pairStep)
  · exact (RawTerm.IsNeutral.not_pair
      (pairParPreserves pairStep)
      (firstRaw := firstTarget) (secondRaw := secondTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `snd` of a
neutral pair scrutinee. -/
theorem RawTerm.IsNeutral.snd_par_preserves {scope : Nat}
    {pairRaw targetRaw : RawTerm scope}
    (pairParPreserves :
      ∀ {pairTarget : RawTerm scope},
        RawStep.par pairRaw pairTarget →
        RawTerm.IsNeutral pairTarget)
    (parallelStep : RawStep.par (RawTerm.snd pairRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.snd_inv parallelStep with
    ⟨pairTarget, targetEq, pairStep⟩
    | ⟨firstTarget, secondTarget, _targetEq, pairStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.snd (pairParPreserves pairStep)
  · exact (RawTerm.IsNeutral.not_pair
      (pairParPreserves pairStep)
      (firstRaw := firstTarget) (secondRaw := secondTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `boolElim`
with a neutral scrutinee. -/
theorem RawTerm.IsNeutral.boolElim_par_preserves {scope : Nat}
    {scrutineeRaw thenRaw elseRaw targetRaw : RawTerm scope}
    (scrutineeParPreserves :
      ∀ {scrutineeTarget : RawTerm scope},
        RawStep.par scrutineeRaw scrutineeTarget →
        RawTerm.IsNeutral scrutineeTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.boolElim scrutineeRaw thenRaw elseRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.boolElim_inv parallelStep with
    ⟨scrutineeTarget, thenTarget, elseTarget, targetEq,
      scrutineeStep, _thenStep, _elseStep⟩
    | ⟨_thenTarget, _targetEq, scrutineeStep, _thenStep⟩
    | ⟨_elseTarget, _targetEq, scrutineeStep, _elseStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.boolElim
      (scrutineeParPreserves scrutineeStep)
  · exact (RawTerm.IsNeutral.not_boolTrue
      (scrutineeParPreserves scrutineeStep) rfl).elim
  · exact (RawTerm.IsNeutral.not_boolFalse
      (scrutineeParPreserves scrutineeStep) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `natElim`
with a neutral scrutinee. -/
theorem RawTerm.IsNeutral.natElim_par_preserves {scope : Nat}
    {scrutineeRaw zeroRaw succRaw targetRaw : RawTerm scope}
    (scrutineeParPreserves :
      ∀ {scrutineeTarget : RawTerm scope},
        RawStep.par scrutineeRaw scrutineeTarget →
        RawTerm.IsNeutral scrutineeTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.natElim scrutineeRaw zeroRaw succRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.natElim_inv parallelStep with
    ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
      scrutineeStep, _zeroStep, _succStep⟩
    | ⟨_zeroTarget, _targetEq, scrutineeStep, _zeroStep⟩
    | ⟨predecessorRaw, _succTarget, _targetEq,
        scrutineeStep, _succStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.natElim
      (scrutineeParPreserves scrutineeStep)
  · exact (RawTerm.IsNeutral.not_natZero
      (scrutineeParPreserves scrutineeStep) rfl).elim
  · exact (RawTerm.IsNeutral.not_natSucc
      (scrutineeParPreserves scrutineeStep)
      (predecessorRaw := predecessorRaw) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `natRec`
with a neutral scrutinee. -/
theorem RawTerm.IsNeutral.natRec_par_preserves {scope : Nat}
    {scrutineeRaw zeroRaw succRaw targetRaw : RawTerm scope}
    (scrutineeParPreserves :
      ∀ {scrutineeTarget : RawTerm scope},
        RawStep.par scrutineeRaw scrutineeTarget →
        RawTerm.IsNeutral scrutineeTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.natRec scrutineeRaw zeroRaw succRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.natRec_inv parallelStep with
    ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
      scrutineeStep, _zeroStep, _succStep⟩
    | ⟨_zeroTarget, _targetEq, scrutineeStep, _zeroStep⟩
    | ⟨predecessorRaw, _zeroTarget, _succTarget, _targetEq,
        scrutineeStep, _zeroStep, _succStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.natRec
      (scrutineeParPreserves scrutineeStep)
  · exact (RawTerm.IsNeutral.not_natZero
      (scrutineeParPreserves scrutineeStep) rfl).elim
  · exact (RawTerm.IsNeutral.not_natSucc
      (scrutineeParPreserves scrutineeStep)
      (predecessorRaw := predecessorRaw) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `listElim`
with a neutral scrutinee. -/
theorem RawTerm.IsNeutral.listElim_par_preserves {scope : Nat}
    {scrutineeRaw nilRaw consRaw targetRaw : RawTerm scope}
    (scrutineeParPreserves :
      ∀ {scrutineeTarget : RawTerm scope},
        RawStep.par scrutineeRaw scrutineeTarget →
        RawTerm.IsNeutral scrutineeTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.listElim scrutineeRaw nilRaw consRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.listElim_inv parallelStep with
    ⟨scrutineeTarget, nilTarget, consTarget, targetEq,
      scrutineeStep, _nilStep, _consStep⟩
    | ⟨_nilTarget, _targetEq, scrutineeStep, _nilStep⟩
    | ⟨headRaw, tailRaw, _consTarget, _targetEq,
        scrutineeStep, _consStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.listElim
      (scrutineeParPreserves scrutineeStep)
  · exact (RawTerm.IsNeutral.not_listNil
      (scrutineeParPreserves scrutineeStep) rfl).elim
  · exact (RawTerm.IsNeutral.not_listCons
      (scrutineeParPreserves scrutineeStep)
      (headRaw := headRaw) (tailRaw := tailRaw) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `optionMatch`
with a neutral scrutinee. -/
theorem RawTerm.IsNeutral.optionMatch_par_preserves {scope : Nat}
    {scrutineeRaw noneRaw someRaw targetRaw : RawTerm scope}
    (scrutineeParPreserves :
      ∀ {scrutineeTarget : RawTerm scope},
        RawStep.par scrutineeRaw scrutineeTarget →
        RawTerm.IsNeutral scrutineeTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.optionMatch scrutineeRaw noneRaw someRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.optionMatch_inv parallelStep with
    ⟨scrutineeTarget, noneTarget, someTarget, targetEq,
      scrutineeStep, _noneStep, _someStep⟩
    | ⟨_noneTarget, _targetEq, scrutineeStep, _noneStep⟩
    | ⟨valueRaw, _someTarget, _targetEq, scrutineeStep, _someStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.optionMatch
      (scrutineeParPreserves scrutineeStep)
  · exact (RawTerm.IsNeutral.not_optionNone
      (scrutineeParPreserves scrutineeStep) rfl).elim
  · exact (RawTerm.IsNeutral.not_optionSome
      (scrutineeParPreserves scrutineeStep)
      (valueRaw := valueRaw) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `eitherMatch`
with a neutral scrutinee. -/
theorem RawTerm.IsNeutral.eitherMatch_par_preserves {scope : Nat}
    {scrutineeRaw leftRaw rightRaw targetRaw : RawTerm scope}
    (scrutineeParPreserves :
      ∀ {scrutineeTarget : RawTerm scope},
        RawStep.par scrutineeRaw scrutineeTarget →
        RawTerm.IsNeutral scrutineeTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.eitherMatch scrutineeRaw leftRaw rightRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.eitherMatch_inv parallelStep with
    ⟨scrutineeTarget, leftTarget, rightTarget, targetEq,
      scrutineeStep, _leftStep, _rightStep⟩
    | ⟨valueRaw, _leftTarget, _targetEq,
        scrutineeStep, _leftStep⟩
    | ⟨valueRaw, _rightTarget, _targetEq,
        scrutineeStep, _rightStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.eitherMatch
      (scrutineeParPreserves scrutineeStep)
  · exact (RawTerm.IsNeutral.not_eitherInl
      (scrutineeParPreserves scrutineeStep)
      (valueRaw := valueRaw) rfl).elim
  · exact (RawTerm.IsNeutral.not_eitherInr
      (scrutineeParPreserves scrutineeStep)
      (valueRaw := valueRaw) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `pathApp`
with a neutral path head. -/
theorem RawTerm.IsNeutral.pathApp_par_preserves {scope : Nat}
    {pathRaw intervalRaw targetRaw : RawTerm scope}
    (pathParPreserves :
      ∀ {pathTarget : RawTerm scope},
        RawStep.par pathRaw pathTarget →
        RawTerm.IsNeutral pathTarget)
    (parallelStep :
      RawStep.par (RawTerm.pathApp pathRaw intervalRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.pathApp_inv parallelStep with
    ⟨pathTarget, intervalTarget, targetEq,
      pathStep, _intervalStep⟩
    | ⟨bodyTarget, _intervalTarget, _targetEq,
        pathStep, _intervalStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.pathApp (pathParPreserves pathStep)
  · exact (RawTerm.IsNeutral.not_pathLam
      (pathParPreserves pathStep)
      (bodyRaw := bodyTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `glueElim`
with a neutral glued value. -/
theorem RawTerm.IsNeutral.glueElim_par_preserves {scope : Nat}
    {gluedRaw targetRaw : RawTerm scope}
    (gluedParPreserves :
      ∀ {gluedTarget : RawTerm scope},
        RawStep.par gluedRaw gluedTarget →
        RawTerm.IsNeutral gluedTarget)
    (parallelStep : RawStep.par (RawTerm.glueElim gluedRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.glueElim_inv parallelStep with
    ⟨gluedTarget, targetEq, gluedStep⟩
    | ⟨baseTarget, partialTarget, _targetEq, gluedStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.glueElim (gluedParPreserves gluedStep)
  · exact (RawTerm.IsNeutral.not_glueIntro
      (gluedParPreserves gluedStep)
      (baseRaw := baseTarget) (partialRaw := partialTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `hcomp`
with neutral sides. -/
theorem RawTerm.IsNeutral.hcomp_par_preserves {scope : Nat}
    {sidesRaw capRaw targetRaw : RawTerm scope}
    (sidesParPreserves :
      ∀ {sidesTarget : RawTerm scope},
        RawStep.par sidesRaw sidesTarget →
        RawTerm.IsNeutral sidesTarget)
    (parallelStep : RawStep.par (RawTerm.hcomp sidesRaw capRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨sidesTarget, capTarget, targetEq,
      sidesStep, _capStep⟩ :=
    RawStep.par.hcomp_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.hcomp (sidesParPreserves sidesStep)

/-- Neutrality is preserved by one raw parallel step from `transp`
with a neutral path line.  The non-congruent D3.6 arms are impossible
because the path source or path target would have to be canonical. -/
theorem RawTerm.IsNeutral.transp_par_preserves {scope : Nat}
    {pathRaw sourceRaw targetRaw : RawTerm scope}
    (pathIsNeutral : RawTerm.IsNeutral pathRaw)
    (pathParPreserves :
      ∀ {pathTarget : RawTerm scope},
        RawStep.par pathRaw pathTarget →
        RawTerm.IsNeutral pathTarget)
    (parallelStep : RawStep.par (RawTerm.transp pathRaw sourceRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.transp_inv parallelStep with
    ⟨pathTarget, sourceTarget, targetEq,
      pathStep, _sourceStep⟩
    | ⟨typeRawSource, _sourceTarget, pathEq,
        _targetEq, _sourceStep⟩
    | ⟨typeRawTarget, _sourceTarget, _targetEq,
        pathStep, _sourceStep⟩
    | ⟨proofRawSource, _proofRawTarget, _sourceTarget,
        pathEq, _targetEq, _proofStep, _sourceStep⟩
    | ⟨proofRawTarget, _sourceTarget, _targetEq,
        pathStep, _sourceStep⟩
    | ⟨leftRawSource, _leftRawTarget, rightRawSource,
        _rightRawTarget, _sourceTarget, pathEq,
        _targetEq, _leftStep, _rightStep, _sourceStep⟩
    | ⟨leftRawTarget, rightRawTarget, _sourceTarget, _targetEq,
        pathStep, _sourceStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.transp (pathParPreserves pathStep)
  · exact (RawTerm.IsNeutral.not_pathLam pathIsNeutral
      (bodyRaw := typeRawSource.weaken) pathEq).elim
  · exact (RawTerm.IsNeutral.not_pathLam
      (pathParPreserves pathStep)
      (bodyRaw := typeRawTarget.weaken) rfl).elim
  · exact (RawTerm.IsNeutral.not_uaToEquiv pathIsNeutral
      (proofRaw := proofRawSource) pathEq).elim
  · exact (RawTerm.IsNeutral.not_uaToEquiv
      (pathParPreserves pathStep)
      (proofRaw := proofRawTarget) rfl).elim
  · exact (RawTerm.IsNeutral.not_pathCompose pathIsNeutral
      (leftRaw := leftRawSource) (rightRaw := rightRawSource)
      pathEq).elim
  · exact (RawTerm.IsNeutral.not_pathCompose
      (pathParPreserves pathStep)
      (leftRaw := leftRawTarget) (rightRaw := rightRawTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `idJ`
with a neutral equality witness. -/
theorem RawTerm.IsNeutral.idJ_par_preserves {scope : Nat}
    {baseRaw witnessRaw targetRaw : RawTerm scope}
    (witnessParPreserves :
      ∀ {witnessTarget : RawTerm scope},
        RawStep.par witnessRaw witnessTarget →
        RawTerm.IsNeutral witnessTarget)
    (parallelStep : RawStep.par (RawTerm.idJ baseRaw witnessRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.idJ_inv parallelStep with
    ⟨baseTarget, witnessTarget, targetEq,
      _baseStep, witnessStep⟩
    | ⟨witnessTarget, _baseTarget, _targetEq,
        witnessStep, _baseStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.idJ (witnessParPreserves witnessStep)
  · exact (RawTerm.IsNeutral.not_refl
      (witnessParPreserves witnessStep)
      (witnessRaw := witnessTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `oeqJ`
with a neutral observational-equality witness. -/
theorem RawTerm.IsNeutral.oeqJ_par_preserves {scope : Nat}
    {baseRaw witnessRaw targetRaw : RawTerm scope}
    (witnessParPreserves :
      ∀ {witnessTarget : RawTerm scope},
        RawStep.par witnessRaw witnessTarget →
        RawTerm.IsNeutral witnessTarget)
    (parallelStep : RawStep.par (RawTerm.oeqJ baseRaw witnessRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨baseTarget, witnessTarget, targetEq,
      _baseStep, witnessStep⟩ :=
    RawStep.par.oeqJ_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.oeqJ (witnessParPreserves witnessStep)

/-- Neutrality is preserved by one raw parallel step from `idStrictRec`
with a neutral strict-identity witness. -/
theorem RawTerm.IsNeutral.idStrictRec_par_preserves {scope : Nat}
    {baseRaw witnessRaw targetRaw : RawTerm scope}
    (witnessParPreserves :
      ∀ {witnessTarget : RawTerm scope},
        RawStep.par witnessRaw witnessTarget →
        RawTerm.IsNeutral witnessTarget)
    (parallelStep :
      RawStep.par (RawTerm.idStrictRec baseRaw witnessRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.idStrictRec_inv parallelStep with
    ⟨baseTarget, witnessTarget, targetEq,
      _baseStep, witnessStep⟩
    | ⟨witnessTarget, _baseTarget, _targetEq,
        witnessStep, _baseStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.idStrictRec
      (witnessParPreserves witnessStep)
  · exact (RawTerm.IsNeutral.not_idStrictRefl
      (witnessParPreserves witnessStep)
      (witnessRaw := witnessTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `equivApp`
with a neutral equivalence head. -/
theorem RawTerm.IsNeutral.equivApp_par_preserves {scope : Nat}
    {equivRaw argumentRaw targetRaw : RawTerm scope}
    (equivParPreserves :
      ∀ {equivTarget : RawTerm scope},
        RawStep.par equivRaw equivTarget →
        RawTerm.IsNeutral equivTarget)
    (parallelStep :
      RawStep.par (RawTerm.equivApp equivRaw argumentRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨equivTarget, argumentTarget, targetEq,
      equivStep, _argumentStep⟩ :=
    RawStep.par.equivApp_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.equivApp (equivParPreserves equivStep)

/-- Neutrality is preserved by one raw parallel step from `equivApply`
with a neutral equivalence head.  The univalence-reflexivity β arms are
impossible because the equivalence source or target would have to be
`uaToEquiv _`. -/
theorem RawTerm.IsNeutral.equivApply_par_preserves {scope : Nat}
    {equivRaw argumentRaw targetRaw : RawTerm scope}
    (equivIsNeutral : RawTerm.IsNeutral equivRaw)
    (equivParPreserves :
      ∀ {equivTarget : RawTerm scope},
        RawStep.par equivRaw equivTarget →
        RawTerm.IsNeutral equivTarget)
    (parallelStep :
      RawStep.par (RawTerm.equivApply equivRaw argumentRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.equivApply_inv parallelStep with
    ⟨equivTarget, argumentTarget, targetEq,
      equivStep, _argumentStep⟩
    | ⟨witnessSource, _witnessTarget, _sourceTarget,
        equivEq, _targetEq, _witnessStep, _argumentStep⟩
    | ⟨witnessTarget, _sourceTarget, _targetEq,
        equivStep, _argumentStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.equivApply
      (equivParPreserves equivStep)
  · exact (RawTerm.IsNeutral.not_uaToEquiv equivIsNeutral
      (proofRaw := RawTerm.oeqRefl witnessSource) equivEq).elim
  · exact (RawTerm.IsNeutral.not_uaToEquiv
      (equivParPreserves equivStep)
      (proofRaw := RawTerm.oeqRefl witnessTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `modElim`
with a neutral modal value. -/
theorem RawTerm.IsNeutral.modElim_par_preserves {scope : Nat}
    {modalRaw targetRaw : RawTerm scope}
    (modalParPreserves :
      ∀ {modalTarget : RawTerm scope},
        RawStep.par modalRaw modalTarget →
        RawTerm.IsNeutral modalTarget)
    (parallelStep : RawStep.par (RawTerm.modElim modalRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.modElim_inv parallelStep with
    ⟨modalTarget, targetEq, modalStep⟩
    | ⟨payloadTarget, _targetEq, modalStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.modElim (modalParPreserves modalStep)
  · exact (RawTerm.IsNeutral.not_modIntro
      (modalParPreserves modalStep)
      (valueRaw := payloadTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `subsume`
with a neutral inner term. -/
theorem RawTerm.IsNeutral.subsume_par_preserves {scope : Nat}
    {innerRaw targetRaw : RawTerm scope}
    (innerParPreserves :
      ∀ {innerTarget : RawTerm scope},
        RawStep.par innerRaw innerTarget →
        RawTerm.IsNeutral innerTarget)
    (parallelStep : RawStep.par (RawTerm.subsume innerRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨innerTarget, targetEq, innerStep⟩ :=
    RawStep.par.subsume_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.subsume (innerParPreserves innerStep)

/-- Neutrality is preserved by one raw parallel step from `refineElim`
with a neutral refined value. -/
theorem RawTerm.IsNeutral.refineElim_par_preserves {scope : Nat}
    {refinedRaw targetRaw : RawTerm scope}
    (refinedParPreserves :
      ∀ {refinedTarget : RawTerm scope},
        RawStep.par refinedRaw refinedTarget →
        RawTerm.IsNeutral refinedTarget)
    (parallelStep : RawStep.par (RawTerm.refineElim refinedRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.refineElim_inv parallelStep with
    ⟨refinedTarget, targetEq, refinedStep⟩
    | ⟨valueTarget, proofTarget, _targetEq, refinedStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.refineElim
      (refinedParPreserves refinedStep)
  · exact (RawTerm.IsNeutral.not_refineIntro
      (refinedParPreserves refinedStep)
      (valueRaw := valueTarget) (proofRaw := proofTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `recordProj`
with a neutral record value. -/
theorem RawTerm.IsNeutral.recordProj_par_preserves {scope : Nat}
    {recordRaw targetRaw : RawTerm scope}
    (recordParPreserves :
      ∀ {recordTarget : RawTerm scope},
        RawStep.par recordRaw recordTarget →
        RawTerm.IsNeutral recordTarget)
    (parallelStep : RawStep.par (RawTerm.recordProj recordRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.recordProj_inv parallelStep with
    ⟨recordTarget, targetEq, recordStep⟩
    | ⟨fieldTarget, _targetEq, recordStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.recordProj
      (recordParPreserves recordStep)
  · exact (RawTerm.IsNeutral.not_recordIntro
      (recordParPreserves recordStep)
      (fieldRaw := fieldTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `codataDest`
with a neutral codata value. -/
theorem RawTerm.IsNeutral.codataDest_par_preserves {scope : Nat}
    {codataRaw targetRaw : RawTerm scope}
    (codataParPreserves :
      ∀ {codataTarget : RawTerm scope},
        RawStep.par codataRaw codataTarget →
        RawTerm.IsNeutral codataTarget)
    (parallelStep : RawStep.par (RawTerm.codataDest codataRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.codataDest_inv parallelStep with
    ⟨codataTarget, targetEq, codataStep⟩
    | ⟨stateTarget, transitionTarget, _targetEq, codataStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.codataDest
      (codataParPreserves codataStep)
  · exact (RawTerm.IsNeutral.not_codataUnfold
      (codataParPreserves codataStep)
      (initialRaw := stateTarget) (transitionRaw := transitionTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `sessionSend`
with a neutral channel. -/
theorem RawTerm.IsNeutral.sessionSend_par_preserves {scope : Nat}
    {channelRaw payloadRaw targetRaw : RawTerm scope}
    (channelParPreserves :
      ∀ {channelTarget : RawTerm scope},
        RawStep.par channelRaw channelTarget →
        RawTerm.IsNeutral channelTarget)
    (parallelStep :
      RawStep.par (RawTerm.sessionSend channelRaw payloadRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨channelTarget, payloadTarget, targetEq,
      channelStep, _payloadStep⟩ :=
    RawStep.par.sessionSend_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.sessionSend
    (channelParPreserves channelStep)

/-- Neutrality is preserved by one raw parallel step from `sessionRecv`
with a neutral channel. -/
theorem RawTerm.IsNeutral.sessionRecv_par_preserves {scope : Nat}
    {channelRaw targetRaw : RawTerm scope}
    (channelParPreserves :
      ∀ {channelTarget : RawTerm scope},
        RawStep.par channelRaw channelTarget →
        RawTerm.IsNeutral channelTarget)
    (parallelStep : RawStep.par (RawTerm.sessionRecv channelRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨channelTarget, targetEq, channelStep⟩ :=
    RawStep.par.sessionRecv_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.sessionRecv
    (channelParPreserves channelStep)

/-- Neutrality is preserved by one raw parallel step from `effectPerform`
with a neutral operation tag. -/
theorem RawTerm.IsNeutral.effectPerform_par_preserves {scope : Nat}
    {operationRaw argumentsRaw targetRaw : RawTerm scope}
    (operationParPreserves :
      ∀ {operationTarget : RawTerm scope},
        RawStep.par operationRaw operationTarget →
        RawTerm.IsNeutral operationTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.effectPerform operationRaw argumentsRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨operationTarget, argumentsTarget, targetEq,
      operationStep, _argumentsStep⟩ :=
    RawStep.par.effectPerform_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.effectPerform
    (operationParPreserves operationStep)

/-- One raw parallel step preserves neutral shape.

This is the global dispatcher over the `RawTerm.IsNeutral` syntax class.
Each eliminator case delegates to its local preservation atom, and the
recursive hypothesis supplies preservation for the principal neutral
subterm. -/
theorem RawTerm.IsNeutral.par_preserves {scope : Nat}
    {sourceRaw targetRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (parallelStep : RawStep.par sourceRaw targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  induction sourceIsNeutral generalizing targetRaw with
  | var position =>
      exact RawTerm.IsNeutral.var_par_preserves parallelStep
  | app functionIsNeutral functionParPreserves =>
      exact RawTerm.IsNeutral.app_par_preserves
        (fun functionStep => functionParPreserves functionStep)
        parallelStep
  | fst pairIsNeutral pairParPreserves =>
      exact RawTerm.IsNeutral.fst_par_preserves
        (fun pairStep => pairParPreserves pairStep)
        parallelStep
  | snd pairIsNeutral pairParPreserves =>
      exact RawTerm.IsNeutral.snd_par_preserves
        (fun pairStep => pairParPreserves pairStep)
        parallelStep
  | boolElim scrutineeIsNeutral scrutineeParPreserves =>
      exact RawTerm.IsNeutral.boolElim_par_preserves
        (fun scrutineeStep => scrutineeParPreserves scrutineeStep)
        parallelStep
  | natElim scrutineeIsNeutral scrutineeParPreserves =>
      exact RawTerm.IsNeutral.natElim_par_preserves
        (fun scrutineeStep => scrutineeParPreserves scrutineeStep)
        parallelStep
  | natRec scrutineeIsNeutral scrutineeParPreserves =>
      exact RawTerm.IsNeutral.natRec_par_preserves
        (fun scrutineeStep => scrutineeParPreserves scrutineeStep)
        parallelStep
  | listElim scrutineeIsNeutral scrutineeParPreserves =>
      exact RawTerm.IsNeutral.listElim_par_preserves
        (fun scrutineeStep => scrutineeParPreserves scrutineeStep)
        parallelStep
  | optionMatch scrutineeIsNeutral scrutineeParPreserves =>
      exact RawTerm.IsNeutral.optionMatch_par_preserves
        (fun scrutineeStep => scrutineeParPreserves scrutineeStep)
        parallelStep
  | eitherMatch scrutineeIsNeutral scrutineeParPreserves =>
      exact RawTerm.IsNeutral.eitherMatch_par_preserves
        (fun scrutineeStep => scrutineeParPreserves scrutineeStep)
        parallelStep
  | pathApp pathIsNeutral pathParPreserves =>
      exact RawTerm.IsNeutral.pathApp_par_preserves
        (fun pathStep => pathParPreserves pathStep)
        parallelStep
  | glueElim gluedValueIsNeutral gluedParPreserves =>
      exact RawTerm.IsNeutral.glueElim_par_preserves
        (fun gluedStep => gluedParPreserves gluedStep)
        parallelStep
  | transp pathIsNeutral pathParPreserves =>
      exact RawTerm.IsNeutral.transp_par_preserves
        pathIsNeutral
        (fun pathStep => pathParPreserves pathStep)
        parallelStep
  | hcomp sidesIsNeutral sidesParPreserves =>
      exact RawTerm.IsNeutral.hcomp_par_preserves
        (fun sidesStep => sidesParPreserves sidesStep)
        parallelStep
  | idJ witnessIsNeutral witnessParPreserves =>
      exact RawTerm.IsNeutral.idJ_par_preserves
        (fun witnessStep => witnessParPreserves witnessStep)
        parallelStep
  | oeqJ witnessIsNeutral witnessParPreserves =>
      exact RawTerm.IsNeutral.oeqJ_par_preserves
        (fun witnessStep => witnessParPreserves witnessStep)
        parallelStep
  | idStrictRec witnessIsNeutral witnessParPreserves =>
      exact RawTerm.IsNeutral.idStrictRec_par_preserves
        (fun witnessStep => witnessParPreserves witnessStep)
        parallelStep
  | equivApp equivIsNeutral equivParPreserves =>
      exact RawTerm.IsNeutral.equivApp_par_preserves
        (fun equivStep => equivParPreserves equivStep)
        parallelStep
  | equivApply equivIsNeutral equivParPreserves =>
      exact RawTerm.IsNeutral.equivApply_par_preserves
        equivIsNeutral
        (fun equivStep => equivParPreserves equivStep)
        parallelStep
  | modElim rawIsNeutral rawParPreserves =>
      exact RawTerm.IsNeutral.modElim_par_preserves
        (fun rawStep => rawParPreserves rawStep)
        parallelStep
  | subsume rawIsNeutral rawParPreserves =>
      exact RawTerm.IsNeutral.subsume_par_preserves
        (fun rawStep => rawParPreserves rawStep)
        parallelStep
  | refineElim refinedValueIsNeutral refinedParPreserves =>
      exact RawTerm.IsNeutral.refineElim_par_preserves
        (fun refinedStep => refinedParPreserves refinedStep)
        parallelStep
  | recordProj recordValueIsNeutral recordParPreserves =>
      exact RawTerm.IsNeutral.recordProj_par_preserves
        (fun recordStep => recordParPreserves recordStep)
        parallelStep
  | codataDest codataValueIsNeutral codataParPreserves =>
      exact RawTerm.IsNeutral.codataDest_par_preserves
        (fun codataStep => codataParPreserves codataStep)
        parallelStep
  | sessionSend channelIsNeutral channelParPreserves =>
      exact RawTerm.IsNeutral.sessionSend_par_preserves
        (fun channelStep => channelParPreserves channelStep)
        parallelStep
  | sessionRecv channelIsNeutral channelParPreserves =>
      exact RawTerm.IsNeutral.sessionRecv_par_preserves
        (fun channelStep => channelParPreserves channelStep)
        parallelStep
  | effectPerform operationIsNeutral operationParPreserves =>
      exact RawTerm.IsNeutral.effectPerform_par_preserves
        (fun operationStep => operationParPreserves operationStep)
        parallelStep

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
  -- elim result.  The explicit branch-SN premises are load-bearing:
  -- raw congruence reduces branches even when the scrutinee is stuck,
  -- so neutral/list-variable CR3 cannot be sound without them.  Full
  -- Reducible-tail closure is reserved for the future Kripke logical
  -- relation refactor.
  | Ty.listType elementType, _, listTerm =>
      Term.isStronglyNormalizing listTerm ∧
      ∀ {motiveType : Ty level scope}
        {nilRaw consRaw : RawTerm scope}
        (nilBranch : Term context motiveType nilRaw)
        (consBranch : Term context (Ty.arrow elementType
                                      (Ty.arrow (Ty.listType elementType) motiveType)) consRaw),
        Term.isStronglyNormalizing nilBranch →
        Term.isStronglyNormalizing consBranch →
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
  -- restricted to elementType (strict sub-Ty).  Demands SN of both
  -- branches and Reducible-arg → SN-applied of someBranch, yielding SN
  -- of the optionMatch result.  The some-branch SN premise is necessary
  -- because optionMatch congruence can reduce it even under a stuck
  -- neutral scrutinee.
  | Ty.optionType elementType, _, optionTerm =>
      Term.isStronglyNormalizing optionTerm ∧
      ∀ {motiveType : Ty level scope}
        {noneRaw someRaw : RawTerm scope}
        (noneBranch : Term context motiveType noneRaw)
        (someBranch : Term context (Ty.arrow elementType motiveType) someRaw),
        Term.isStronglyNormalizing noneBranch →
        Term.isStronglyNormalizing someBranch →
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
  -- matching the K12.6 piTy weak shape per branch.  Demands branch SN
  -- plus Reducible-arg → SN-applied on each side, yielding SN of the
  -- eitherMatch result.  Branch SN is required for neutral scrutinees
  -- because eitherMatch congruence reduces both branches independently
  -- of which ι-rule may later fire.
  | Ty.eitherType leftType rightType, _, eitherTerm =>
      Term.isStronglyNormalizing eitherTerm ∧
      ∀ {motiveType : Ty level scope}
        {leftRaw rightRaw : RawTerm scope}
        (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
        (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw),
        Term.isStronglyNormalizing leftBranch →
        Term.isStronglyNormalizing rightBranch →
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

/-- Head-β SN expansion for non-dependent application.

If the lambda body, argument, and β-contractum are all strongly
normalizing, then the whole redex `app (lam body) argument` is strongly
normalizing.  Congruence reducts recurse through body/argument SN.
The β arm is not dismissed syntactically: `RawStep.par.app_inv` may
produce a deep β target after the function side parallel-reduces to a
lambda, so the proof uses `RawStep.par.subst0_par` to relate the
original contractum to that β target and then applies raw CR2. -/
theorem RawTerm.app_lam_isStronglyNormalizing {scope : Nat}
    {body : RawTerm (scope + 1)}
    (bodyIsSN : RawTerm.isStronglyNormalizing body) :
    ∀ {argument : RawTerm scope},
      RawTerm.isStronglyNormalizing argument →
      RawTerm.isStronglyNormalizing (body.subst0 argument) →
      RawTerm.isStronglyNormalizing
        (RawTerm.app (RawTerm.lam body) argument) := by
  induction bodyIsSN with
  | intro currentBody bodyClosure bodyIH =>
    intro argument argumentIsSN betaContractumIsSN
    induction argumentIsSN with
    | intro currentArgument argumentClosure argumentIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.app (RawTerm.lam currentBody) currentArgument) ?_
      intro target progressStep
      rcases RawStep.par.app_inv progressStep.1 with
        ⟨functionTarget, argumentTarget, targetEq,
          functionStep, argumentStep⟩
        | ⟨bodyTarget, argumentTarget, targetEq,
            functionStep, argumentStep⟩
      · obtain ⟨bodyTarget, functionTargetEq, bodyStep⟩ :=
          RawStep.par.lam_inv functionStep
        subst functionTargetEq
        subst targetEq
        by_cases bodyEq : currentBody = bodyTarget
        · subst bodyEq
          by_cases argumentEq : currentArgument = argumentTarget
          · subst argumentEq
            exact False.elim (progressStep.2 rfl)
          · have argumentContractumIsSN :
                RawTerm.isStronglyNormalizing
                  (currentBody.subst0 argumentTarget) := by
              by_cases contractumEq :
                  currentBody.subst0 currentArgument =
                    currentBody.subst0 argumentTarget
              · rw [← contractumEq]
                exact betaContractumIsSN
              · exact RawTerm.isStronglyNormalizing.step_preserves
                  betaContractumIsSN
                  ⟨RawStep.par.subst0_par (RawStep.par.refl currentBody)
                    argumentStep, contractumEq⟩
            exact argumentIH argumentTarget ⟨argumentStep, argumentEq⟩
              argumentContractumIsSN
        · have bodyProgress :
              RawStep.parProgress currentBody bodyTarget :=
            ⟨bodyStep, bodyEq⟩
          have argumentTargetIsSN :
              RawTerm.isStronglyNormalizing argumentTarget := by
            by_cases argumentEq : currentArgument = argumentTarget
            · subst argumentEq
              exact RawTerm.isStronglyNormalizing.intro
                currentArgument argumentClosure
            · exact argumentClosure argumentTarget ⟨argumentStep, argumentEq⟩
          have bodyTargetContractumIsSN :
              RawTerm.isStronglyNormalizing
                (bodyTarget.subst0 argumentTarget) := by
            by_cases contractumEq :
                currentBody.subst0 currentArgument =
                  bodyTarget.subst0 argumentTarget
            · rw [← contractumEq]
              exact betaContractumIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                betaContractumIsSN
                ⟨RawStep.par.subst0_par bodyStep argumentStep,
                  contractumEq⟩
          exact bodyIH bodyTarget bodyProgress argumentTargetIsSN
            bodyTargetContractumIsSN
      · obtain ⟨bodyTargetFromLam, lamTargetEq, bodyStep⟩ :=
          RawStep.par.lam_inv functionStep
        cases lamTargetEq
        subst targetEq
        by_cases contractumEq :
            currentBody.subst0 currentArgument =
              bodyTarget.subst0 argumentTarget
        · rw [← contractumEq]
          exact betaContractumIsSN
        · exact RawTerm.isStronglyNormalizing.step_preserves
            betaContractumIsSN
            ⟨RawStep.par.subst0_par bodyStep argumentStep, contractumEq⟩

/-- Shape-specialized inversion for application SN.  The induction is
over an arbitrary SN source and receives the application shape as an
equality, which keeps Lean's indexed-inductive eliminator in the
structural fragment. -/
theorem RawTerm.app_function_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {functionRaw argumentRaw : RawTerm scope},
      source = RawTerm.app functionRaw argumentRaw →
      RawTerm.isStronglyNormalizing functionRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro functionRaw argumentRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro functionRaw ?_
    intro functionTarget functionProgress
    have appProgress :
        RawStep.parProgress
          (RawTerm.app functionRaw argumentRaw)
          (RawTerm.app functionTarget argumentRaw) := by
      refine ⟨RawStep.par.app functionProgress.1
        (RawStep.par.refl argumentRaw), ?_⟩
      intro appEq
      apply functionProgress.2
      injection appEq
    exact inductiveHypothesis
      (RawTerm.app functionTarget argumentRaw) appProgress rfl

/-- If an application is strongly normalizing, its function subterm is
strongly normalizing.  This is used by weak eliminator CR3: branch
closures often expose SN only after applying a branch, while neutral
eliminator congruence needs SN of the branch term itself. -/
theorem RawTerm.app_function_isStronglyNormalizing {scope : Nat}
    {functionRaw argumentRaw : RawTerm scope}
    (appIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.app functionRaw argumentRaw)) :
    RawTerm.isStronglyNormalizing functionRaw :=
  RawTerm.app_function_isStronglyNormalizing_aux appIsSN rfl

/-- Shape-specialized inversion for application-argument SN.  This is
the argument-position sibling of `app_function_isStronglyNormalizing_aux`:
the induction is over an arbitrary SN source and receives the application
shape as an equality. -/
theorem RawTerm.app_argument_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {functionRaw argumentRaw : RawTerm scope},
      source = RawTerm.app functionRaw argumentRaw →
      RawTerm.isStronglyNormalizing argumentRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro functionRaw argumentRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro argumentRaw ?_
    intro argumentTarget argumentProgress
    have appProgress :
        RawStep.parProgress
          (RawTerm.app functionRaw argumentRaw)
          (RawTerm.app functionRaw argumentTarget) := by
      refine ⟨RawStep.par.app (RawStep.par.refl functionRaw)
        argumentProgress.1, ?_⟩
      intro appEq
      apply argumentProgress.2
      injection appEq
    exact inductiveHypothesis
      (RawTerm.app functionRaw argumentTarget) appProgress rfl

/-- If an application is strongly normalizing, its argument subterm is
strongly normalizing.  Used alongside function-position inversion when
head-β and eliminator proofs need to recover SN of raw subterms from an
already-normalizing application. -/
theorem RawTerm.app_argument_isStronglyNormalizing {scope : Nat}
    {functionRaw argumentRaw : RawTerm scope}
    (appIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.app functionRaw argumentRaw)) :
    RawTerm.isStronglyNormalizing argumentRaw :=
  RawTerm.app_argument_isStronglyNormalizing_aux appIsSN rfl

/-- Shape-specialized inversion for first component SN from pair SN. -/
theorem RawTerm.pair_first_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {firstRaw secondRaw : RawTerm scope},
      source = RawTerm.pair firstRaw secondRaw →
      RawTerm.isStronglyNormalizing firstRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro firstRaw secondRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro firstRaw ?_
    intro firstTarget firstProgress
    have pairProgress :
        RawStep.parProgress
          (RawTerm.pair firstRaw secondRaw)
          (RawTerm.pair firstTarget secondRaw) := by
      refine ⟨RawStep.par.pair firstProgress.1
        (RawStep.par.refl secondRaw), ?_⟩
      intro pairEq
      apply firstProgress.2
      injection pairEq
    exact inductiveHypothesis
      (RawTerm.pair firstTarget secondRaw) pairProgress rfl

/-- If a pair is strongly normalizing, its first component is strongly
normalizing. -/
theorem RawTerm.pair_first_isStronglyNormalizing {scope : Nat}
    {firstRaw secondRaw : RawTerm scope}
    (pairIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.pair firstRaw secondRaw)) :
    RawTerm.isStronglyNormalizing firstRaw :=
  RawTerm.pair_first_isStronglyNormalizing_aux pairIsSN rfl

/-- Shape-specialized inversion for second component SN from pair SN. -/
theorem RawTerm.pair_second_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {firstRaw secondRaw : RawTerm scope},
      source = RawTerm.pair firstRaw secondRaw →
      RawTerm.isStronglyNormalizing secondRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro firstRaw secondRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro secondRaw ?_
    intro secondTarget secondProgress
    have pairProgress :
        RawStep.parProgress
          (RawTerm.pair firstRaw secondRaw)
          (RawTerm.pair firstRaw secondTarget) := by
      refine ⟨RawStep.par.pair (RawStep.par.refl firstRaw)
        secondProgress.1, ?_⟩
      intro pairEq
      apply secondProgress.2
      injection pairEq
    exact inductiveHypothesis
      (RawTerm.pair firstRaw secondTarget) pairProgress rfl

/-- If a pair is strongly normalizing, its second component is strongly
normalizing. -/
theorem RawTerm.pair_second_isStronglyNormalizing {scope : Nat}
    {firstRaw secondRaw : RawTerm scope}
    (pairIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.pair firstRaw secondRaw)) :
    RawTerm.isStronglyNormalizing secondRaw :=
  RawTerm.pair_second_isStronglyNormalizing_aux pairIsSN rfl

/-- Shape-specialized inversion for option payload SN. -/
theorem RawTerm.optionSome_value_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {valueRaw : RawTerm scope},
      source = RawTerm.optionSome valueRaw →
      RawTerm.isStronglyNormalizing valueRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro valueRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro valueRaw ?_
    intro valueTarget valueProgress
    have optionProgress :
        RawStep.parProgress
          (RawTerm.optionSome valueRaw)
          (RawTerm.optionSome valueTarget) := by
      refine ⟨RawStep.par.optionSome valueProgress.1, ?_⟩
      intro optionEq
      apply valueProgress.2
      injection optionEq
    exact inductiveHypothesis
      (RawTerm.optionSome valueTarget) optionProgress rfl

/-- If `optionSome value` is strongly normalizing, then `value` is
strongly normalizing. -/
theorem RawTerm.optionSome_value_isStronglyNormalizing {scope : Nat}
    {valueRaw : RawTerm scope}
    (optionIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.optionSome valueRaw)) :
    RawTerm.isStronglyNormalizing valueRaw :=
  RawTerm.optionSome_value_isStronglyNormalizing_aux optionIsSN rfl

/-- Shape-specialized inversion for either-left payload SN. -/
theorem RawTerm.eitherInl_value_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {valueRaw : RawTerm scope},
      source = RawTerm.eitherInl valueRaw →
      RawTerm.isStronglyNormalizing valueRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro valueRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro valueRaw ?_
    intro valueTarget valueProgress
    have eitherProgress :
        RawStep.parProgress
          (RawTerm.eitherInl valueRaw)
          (RawTerm.eitherInl valueTarget) := by
      refine ⟨RawStep.par.eitherInl valueProgress.1, ?_⟩
      intro eitherEq
      apply valueProgress.2
      injection eitherEq
    exact inductiveHypothesis
      (RawTerm.eitherInl valueTarget) eitherProgress rfl

/-- If `eitherInl value` is strongly normalizing, then `value` is
strongly normalizing. -/
theorem RawTerm.eitherInl_value_isStronglyNormalizing {scope : Nat}
    {valueRaw : RawTerm scope}
    (eitherIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.eitherInl valueRaw)) :
    RawTerm.isStronglyNormalizing valueRaw :=
  RawTerm.eitherInl_value_isStronglyNormalizing_aux eitherIsSN rfl

/-- Shape-specialized inversion for either-right payload SN. -/
theorem RawTerm.eitherInr_value_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {valueRaw : RawTerm scope},
      source = RawTerm.eitherInr valueRaw →
      RawTerm.isStronglyNormalizing valueRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro valueRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro valueRaw ?_
    intro valueTarget valueProgress
    have eitherProgress :
        RawStep.parProgress
          (RawTerm.eitherInr valueRaw)
          (RawTerm.eitherInr valueTarget) := by
      refine ⟨RawStep.par.eitherInr valueProgress.1, ?_⟩
      intro eitherEq
      apply valueProgress.2
      injection eitherEq
    exact inductiveHypothesis
      (RawTerm.eitherInr valueTarget) eitherProgress rfl

/-- If `eitherInr value` is strongly normalizing, then `value` is
strongly normalizing. -/
theorem RawTerm.eitherInr_value_isStronglyNormalizing {scope : Nat}
    {valueRaw : RawTerm scope}
    (eitherIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.eitherInr valueRaw)) :
    RawTerm.isStronglyNormalizing valueRaw :=
  RawTerm.eitherInr_value_isStronglyNormalizing_aux eitherIsSN rfl

/-- Shape-specialized inversion for list-cons head SN. -/
theorem RawTerm.listCons_head_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {headRaw tailRaw : RawTerm scope},
      source = RawTerm.listCons headRaw tailRaw →
      RawTerm.isStronglyNormalizing headRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro headRaw tailRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro headRaw ?_
    intro headTarget headProgress
    have consProgress :
        RawStep.parProgress
          (RawTerm.listCons headRaw tailRaw)
          (RawTerm.listCons headTarget tailRaw) := by
      refine ⟨RawStep.par.listCons headProgress.1
        (RawStep.par.refl tailRaw), ?_⟩
      intro consEq
      apply headProgress.2
      injection consEq
    exact inductiveHypothesis
      (RawTerm.listCons headTarget tailRaw) consProgress rfl

/-- If `listCons head tail` is strongly normalizing, then `head` is
strongly normalizing. -/
theorem RawTerm.listCons_head_isStronglyNormalizing {scope : Nat}
    {headRaw tailRaw : RawTerm scope}
    (consIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.listCons headRaw tailRaw)) :
    RawTerm.isStronglyNormalizing headRaw :=
  RawTerm.listCons_head_isStronglyNormalizing_aux consIsSN rfl

/-- Shape-specialized inversion for list-cons tail SN. -/
theorem RawTerm.listCons_tail_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {headRaw tailRaw : RawTerm scope},
      source = RawTerm.listCons headRaw tailRaw →
      RawTerm.isStronglyNormalizing tailRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro headRaw tailRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro tailRaw ?_
    intro tailTarget tailProgress
    have consProgress :
        RawStep.parProgress
          (RawTerm.listCons headRaw tailRaw)
          (RawTerm.listCons headRaw tailTarget) := by
      refine ⟨RawStep.par.listCons (RawStep.par.refl headRaw)
        tailProgress.1, ?_⟩
      intro consEq
      apply tailProgress.2
      injection consEq
    exact inductiveHypothesis
      (RawTerm.listCons headRaw tailTarget) consProgress rfl

/-- If `listCons head tail` is strongly normalizing, then `tail` is
strongly normalizing. -/
theorem RawTerm.listCons_tail_isStronglyNormalizing {scope : Nat}
    {headRaw tailRaw : RawTerm scope}
    (consIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.listCons headRaw tailRaw)) :
    RawTerm.isStronglyNormalizing tailRaw :=
  RawTerm.listCons_tail_isStronglyNormalizing_aux consIsSN rfl

/-- **K12.20.U2 raw CR3 skeleton**: a raw term is strongly
normalizing when every non-trivial parallel-progress reduct is
strongly normalizing.

This is the constructor direction of the SN definition, named because
the typed CR3 proof repeatedly reduces its SN-direct arms to exactly
this shape.  Neutrality is intentionally not required here: neutrality
is what makes the premise provable for variables and stuck eliminators;
the raw SN constructor itself only needs the reduct closure. -/
theorem RawTerm.isStronglyNormalizing.of_progress_closure {scope : Nat}
    {source : RawTerm scope}
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress source target →
        RawTerm.isStronglyNormalizing target) :
    RawTerm.isStronglyNormalizing source :=
  RawTerm.isStronglyNormalizing.intro source closure

/-- Typed wrapper around `RawTerm.isStronglyNormalizing.of_progress_closure`.
The term's type is irrelevant because typed SN is raw SN of the term's
structural raw index. -/
theorem Term.isStronglyNormalizing.of_raw_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context sourceType sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Term.isStronglyNormalizing sourceTerm :=
  RawTerm.isStronglyNormalizing.of_progress_closure closure

/-- **K12.20.U2 raw CR3, neutral form**: a neutral raw term is SN
when all of its non-trivial progress reducts are SN.

The neutral witness is not computationally needed by the SN
constructor; it records the Tait CR3 contract at the call site.  In
later compound arms the neutral witness is what makes the reduct
closure available, while this lemma performs the final SN packaging. -/
theorem RawTerm.IsNeutral.isStronglyNormalizing_of_progress_closure
    {scope : Nat}
    {source : RawTerm scope}
    (_sourceIsNeutral : RawTerm.IsNeutral source)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress source target →
        RawTerm.isStronglyNormalizing target) :
    RawTerm.isStronglyNormalizing source :=
  RawTerm.isStronglyNormalizing.of_progress_closure closure

/-- Typed wrapper for the neutral raw CR3 form. -/
theorem Term.isStronglyNormalizing_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context sourceType sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Term.isStronglyNormalizing sourceTerm :=
  RawTerm.IsNeutral.isStronglyNormalizing_of_progress_closure
    sourceIsNeutral closure

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

/-- Variables have no non-trivial parallel-progress reducts.  This is
the vacuous CR3 base fact for `RawTerm.IsNeutral.var`: once the CR3
proof recurses over types, the premise `∀ target, var → target →
Reducible target` is never queried for an actual target. -/
theorem RawTerm.var_has_no_progress {scope : Nat}
    (position : Fin scope) :
    ∀ target : RawTerm scope,
      ¬ RawStep.parProgress (RawTerm.var position) target := by
  intro target progressStep
  exact progressStep.2 (RawStep.par.var_inv progressStep.1).symm

/-- Application with a neutral function head is strongly normalizing
when both the head and argument are strongly normalizing.

The beta arm is impossible because `RawTerm.IsNeutral.par_preserves`
keeps every parallel reduct of the function head neutral, and neutral
terms are never lambda-shaped.  The congruence arm recurses on the
function progress when the head changes, otherwise on the argument
progress. -/
theorem RawTerm.app_neutral_isStronglyNormalizing {scope : Nat}
    {functionRaw argumentRaw : RawTerm scope}
    (functionIsNeutral : RawTerm.IsNeutral functionRaw)
    (functionIsSN : RawTerm.isStronglyNormalizing functionRaw)
    (argumentIsSN : RawTerm.isStronglyNormalizing argumentRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.app functionRaw argumentRaw) := by
  induction functionIsSN generalizing argumentRaw with
  | intro currentFunction _ functionInduction =>
    induction argumentIsSN with
    | intro currentArgument argumentClosure argumentInduction =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.app currentFunction currentArgument) ?_
      intro target progressStep
      rcases RawStep.par.app_inv progressStep.1 with
        ⟨functionTarget, argumentTarget, targetEq,
          functionStep, argumentStep⟩
        | ⟨bodyTarget, _argumentTarget, _targetEq,
            functionStep, _argumentStep⟩
      · subst targetEq
        have functionTargetIsNeutral :
            RawTerm.IsNeutral functionTarget :=
          RawTerm.IsNeutral.par_preserves functionIsNeutral functionStep
        have argumentTargetIsSN :
            RawTerm.isStronglyNormalizing argumentTarget := by
          by_cases argumentEq : currentArgument = argumentTarget
          · subst argumentEq
            exact RawTerm.isStronglyNormalizing.intro
              currentArgument argumentClosure
          · exact argumentClosure argumentTarget
              ⟨argumentStep, argumentEq⟩
        by_cases functionEq : currentFunction = functionTarget
        · subst functionEq
          by_cases argumentEq : currentArgument = argumentTarget
          · subst argumentEq
            exact (progressStep.2 rfl).elim
          · exact argumentInduction argumentTarget
              ⟨argumentStep, argumentEq⟩
        · exact functionInduction functionTarget
            ⟨functionStep, functionEq⟩
            functionTargetIsNeutral
            argumentTargetIsSN
      · exact (RawTerm.IsNeutral.not_lam
          (RawTerm.IsNeutral.par_preserves functionIsNeutral functionStep)
          (bodyRaw := bodyTarget) rfl).elim

/-- First projection with a neutral pair head is strongly normalizing
when the head is strongly normalizing.

The pair beta arm is impossible because any parallel reduct of a
neutral head stays neutral, and neutral terms are never pair-shaped.
The congruence arm recurses on head progress. -/
theorem RawTerm.fst_neutral_isStronglyNormalizing {scope : Nat}
    {pairRaw : RawTerm scope}
    (pairIsNeutral : RawTerm.IsNeutral pairRaw)
    (pairIsSN : RawTerm.isStronglyNormalizing pairRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.fst pairRaw) := by
  induction pairIsSN with
  | intro currentPair _ pairInduction =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.fst currentPair) ?_
    intro target progressStep
    rcases RawStep.par.fst_inv progressStep.1 with
      ⟨pairTarget, targetEq, pairStep⟩
      | ⟨firstTarget, secondTarget, _targetEq, pairStep⟩
    · have pairTargetIsNeutral : RawTerm.IsNeutral pairTarget :=
        RawTerm.IsNeutral.par_preserves pairIsNeutral pairStep
      by_cases pairEq : currentPair = pairTarget
      · subst pairEq
        subst targetEq
        exact (progressStep.2 rfl).elim
      · subst targetEq
        exact pairInduction pairTarget
          ⟨pairStep, pairEq⟩ pairTargetIsNeutral
    · exact (RawTerm.IsNeutral.not_pair
        (RawTerm.IsNeutral.par_preserves pairIsNeutral pairStep)
        (firstRaw := firstTarget) (secondRaw := secondTarget) rfl).elim

/-- Second projection with a neutral pair head is strongly normalizing
when the head is strongly normalizing. -/
theorem RawTerm.snd_neutral_isStronglyNormalizing {scope : Nat}
    {pairRaw : RawTerm scope}
    (pairIsNeutral : RawTerm.IsNeutral pairRaw)
    (pairIsSN : RawTerm.isStronglyNormalizing pairRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.snd pairRaw) := by
  induction pairIsSN with
  | intro currentPair _ pairInduction =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.snd currentPair) ?_
    intro target progressStep
    rcases RawStep.par.snd_inv progressStep.1 with
      ⟨pairTarget, targetEq, pairStep⟩
      | ⟨firstTarget, secondTarget, _targetEq, pairStep⟩
    · have pairTargetIsNeutral : RawTerm.IsNeutral pairTarget :=
        RawTerm.IsNeutral.par_preserves pairIsNeutral pairStep
      by_cases pairEq : currentPair = pairTarget
      · subst pairEq
        subst targetEq
        exact (progressStep.2 rfl).elim
      · subst targetEq
        exact pairInduction pairTarget
          ⟨pairStep, pairEq⟩ pairTargetIsNeutral
    · exact (RawTerm.IsNeutral.not_pair
        (RawTerm.IsNeutral.par_preserves pairIsNeutral pairStep)
        (firstRaw := firstTarget) (secondRaw := secondTarget) rfl).elim

/-- **K12.20.AS neutral-app SN preservation**.  `RawTerm.app (var pos)
arg` is strongly normalizing whenever `arg` is.

This is the first **neutral-head application** SN helper — the
foundational building block for compound-Ty CR3 (variables are
Reducible at every type), which is in turn the prerequisite for
`ReducibleSubst.lift` / `.singleton` and the K12.20-head fundamental
theorem case for `Term.lam` proper.

Proof: induction on `arg`'s SN witness.  Step inversion of
`RawStep.par (app (var pos) currentArg) target` via `app_inv` gives
two arms: (1) cong on both subterms — `var pos` only par-reduces to
itself via `var_inv`, so the function position is rigid; the
argument-position cong is discharged by the inductive hypothesis on
the SN-progress of `currentArg`.  (2) shallow/deep β — would require
`var pos` par-reducing to a `lam` form, which `var_inv` rules out
via `RawTerm.noConfusion` on the resulting `var = lam` equation. -/
theorem RawTerm.app_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {argRaw : RawTerm scope}
    (argIsSN : RawTerm.isStronglyNormalizing argRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.app (RawTerm.var position) argRaw) := by
  induction argIsSN with
  | intro currentArg _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.app (RawTerm.var position) currentArg) ?_
    intro target progressStep
    rcases RawStep.par.app_inv progressStep.1 with
      ⟨functionTarget, argumentTarget, targetEq, functionStep, argumentStep⟩
      | ⟨bodyTarget, argumentTarget, _targetEq, functionStep, _argumentStep⟩
    · have functionEq : functionTarget = RawTerm.var position :=
        (RawStep.par.var_inv functionStep)
      subst functionEq
      subst targetEq
      have argumentDistinct :
          currentArg ≠ argumentTarget := fun argumentEq =>
        progressStep.2
          (congrArg (RawTerm.app (RawTerm.var position)) argumentEq)
      exact inductiveHypothesis argumentTarget
        ⟨argumentStep, argumentDistinct⟩
    · exact (by
        have varEqLam :
            RawTerm.lam bodyTarget = RawTerm.var position :=
          (RawStep.par.var_inv functionStep)
        nomatch varEqLam)

/-- **K12.20.AT.1 neutral fst SN preservation**.  `RawTerm.fst
(var pos)` is strongly normalizing.  Sister to `app_var`; `fst` is
a unary destructor for Σ pairs, β fires only when the inner term
par-reduces to `pair _ _`.  For variable inner, `var_inv` rules
that out — `var pos` only par-reduces to itself, never to a pair.
The cong arm is vacuous: the scrutinee is fixed, so no progress
step exists; `parProgress`'s source-≠-target requirement contradicts
`var_inv`. -/
theorem RawTerm.fst_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope) :
    RawTerm.isStronglyNormalizing
      (RawTerm.fst (RawTerm.var position)) := by
  refine RawTerm.isStronglyNormalizing.intro
    (RawTerm.fst (RawTerm.var position)) ?_
  intro target progressStep
  rcases RawStep.par.fst_inv progressStep.1 with
    ⟨pairTarget, targetEq, pairStep⟩
    | ⟨firstTarget, secondTarget, _targetEq, pairStep⟩
  · have pairEq : pairTarget = RawTerm.var position :=
      (RawStep.par.var_inv pairStep)
    subst pairEq
    subst targetEq
    exact (progressStep.2 rfl).elim
  · exact (by
      have varEqPair :
          RawTerm.pair firstTarget secondTarget = RawTerm.var position :=
        (RawStep.par.var_inv pairStep)
      nomatch varEqPair)

/-- **K12.20.AT.2 neutral snd SN preservation**.  Sister to
`fst_var`; same proof shape, dual Σ projection. -/
theorem RawTerm.snd_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope) :
    RawTerm.isStronglyNormalizing
      (RawTerm.snd (RawTerm.var position)) := by
  refine RawTerm.isStronglyNormalizing.intro
    (RawTerm.snd (RawTerm.var position)) ?_
  intro target progressStep
  rcases RawStep.par.snd_inv progressStep.1 with
    ⟨pairTarget, targetEq, pairStep⟩
    | ⟨firstTarget, secondTarget, _targetEq, pairStep⟩
  · have pairEq : pairTarget = RawTerm.var position :=
      (RawStep.par.var_inv pairStep)
    subst pairEq
    subst targetEq
    exact (progressStep.2 rfl).elim
  · exact (by
      have varEqPair :
          RawTerm.pair firstTarget secondTarget = RawTerm.var position :=
        (RawStep.par.var_inv pairStep)
      nomatch varEqPair)

/-- **K12.20.AU neutral boolElim SN preservation**.  `RawTerm.boolElim
(var pos) thenBranch elseBranch` is SN when both branches are SN.

First ternary neutral-head SN helper.  boolElim has three subterms
plus two ι rules (`iotaBoolElimTrue` / `False` for true/false
scrutinees).  Variable scrutinee blocks both ι rules via `var_inv`
(var doesn't par-reduce to `boolTrue` or `boolFalse`).  Cong arm
has all three subterms moving in parallel; with the scrutinee
rigid, the effective movement is binary on (thenBranch, elseBranch)
— nested induction like `pair_isStronglyNormalizing`.

Per `feedback_lean_induction_universal_motive.md`: state the
`elseBranch`-side universal in the conclusion to keep the IH wide
across nested induction on the two branches. -/
theorem RawTerm.boolElim_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {thenBranch : RawTerm scope}
    (thenIsSN : RawTerm.isStronglyNormalizing thenBranch) :
    ∀ {elseBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing elseBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.boolElim (RawTerm.var position) thenBranch elseBranch) := by
  induction thenIsSN with
  | intro currentThen _ thenIH =>
    intro elseBranch elseIsSN
    induction elseIsSN with
    | intro currentElse elseClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.boolElim (RawTerm.var position) currentThen currentElse) ?_
      intro target progressStep
      rcases RawStep.par.boolElim_inv progressStep.1 with
        ⟨scrutineeTarget, thenTarget, elseTarget, targetEq,
          scrutineeStep, thenStep, elseStep⟩
        | (⟨thenTarget, _targetEq, scrutineeStep, _thenStep⟩
          | ⟨elseTarget, _targetEq, scrutineeStep, _elseStep⟩)
      · have scrutineeEq :
            scrutineeTarget = RawTerm.var position :=
          (RawStep.par.var_inv scrutineeStep)
        subst scrutineeEq
        subst targetEq
        by_cases thenEq : currentThen = thenTarget
        · subst thenEq
          have elseDistinct :
              currentElse ≠ elseTarget := fun elseEq =>
            progressStep.2 (congrArg
              (RawTerm.boolElim (RawTerm.var position) currentThen) elseEq)
          exact innerIH elseTarget ⟨elseStep, elseDistinct⟩
        · have thenProgress :
              RawStep.parProgress currentThen thenTarget :=
            ⟨thenStep, thenEq⟩
          by_cases elseEq : currentElse = elseTarget
          · subst elseEq
            exact thenIH thenTarget thenProgress
              (RawTerm.isStronglyNormalizing.intro currentElse elseClosure)
          · exact thenIH thenTarget thenProgress
              (elseClosure elseTarget ⟨elseStep, elseEq⟩)
      · exact (by
          have varEqTrue :
              RawTerm.var position = RawTerm.boolTrue :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqTrue)
      · exact (by
          have varEqFalse :
              RawTerm.var position = RawTerm.boolFalse :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqFalse)

/-- Boolean eliminator SN preservation.  This is the generic version
behind the neutral `boolElim_var` helper: congruence arms recurse through
the three SN subterms, while true/false ι arms return the corresponding
branch target. -/
theorem RawTerm.boolElim_isStronglyNormalizing {scope : Nat}
    {thenBranch : RawTerm scope}
    (thenIsSN : RawTerm.isStronglyNormalizing thenBranch) :
    ∀ {elseBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing elseBranch →
    ∀ {scrutinee : RawTerm scope},
      RawTerm.isStronglyNormalizing scrutinee →
      RawTerm.isStronglyNormalizing
        (RawTerm.boolElim scrutinee thenBranch elseBranch) := by
  induction thenIsSN with
  | intro currentThen thenClosure thenIH =>
    intro elseBranch elseIsSN
    induction elseIsSN with
    | intro currentElse elseClosure elseIH =>
      intro scrutinee scrutineeIsSN
      induction scrutineeIsSN with
      | intro currentScrutinee scrutineeClosure scrutineeIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.boolElim currentScrutinee currentThen currentElse) ?_
        intro target progressStep
        cases RawStep.par.boolElim_inv progressStep.1 with
        | inl congruentStep =>
          rcases congruentStep with
            ⟨scrutineeTarget, thenTarget, elseTarget, targetEq,
              scrutineeStep, thenStep, elseStep⟩
          subst targetEq
          by_cases thenEq : currentThen = thenTarget
          · subst thenEq
            by_cases elseEq : currentElse = elseTarget
            · subst elseEq
              by_cases scrutineeEq : currentScrutinee = scrutineeTarget
              · subst scrutineeEq
                exact (progressStep.2 rfl).elim
              · exact scrutineeIH scrutineeTarget
                  ⟨scrutineeStep, scrutineeEq⟩
            · have scrutineeTargetIsSN :
                  RawTerm.isStronglyNormalizing scrutineeTarget := by
                by_cases scrutineeEq : currentScrutinee = scrutineeTarget
                · subst scrutineeEq
                  exact RawTerm.isStronglyNormalizing.intro currentScrutinee
                    scrutineeClosure
                · exact scrutineeClosure scrutineeTarget
                    ⟨scrutineeStep, scrutineeEq⟩
              exact elseIH elseTarget ⟨elseStep, elseEq⟩
                scrutineeTargetIsSN
          · have elseTargetIsSN :
                RawTerm.isStronglyNormalizing elseTarget := by
              by_cases elseEq : currentElse = elseTarget
              · subst elseEq
                exact RawTerm.isStronglyNormalizing.intro currentElse
                  elseClosure
              · exact elseClosure elseTarget ⟨elseStep, elseEq⟩
            have scrutineeTargetIsSN :
                RawTerm.isStronglyNormalizing scrutineeTarget := by
              by_cases scrutineeEq : currentScrutinee = scrutineeTarget
              · subst scrutineeEq
                exact RawTerm.isStronglyNormalizing.intro currentScrutinee
                  scrutineeClosure
              · exact scrutineeClosure scrutineeTarget
                  ⟨scrutineeStep, scrutineeEq⟩
            exact thenIH thenTarget ⟨thenStep, thenEq⟩
              elseTargetIsSN scrutineeTargetIsSN
        | inr iotaStep =>
          cases iotaStep with
          | inl trueStep =>
            rcases trueStep with
              ⟨thenTarget, targetEq, _scrutineeStep, thenStep⟩
            rw [targetEq]
            by_cases thenEq : currentThen = thenTarget
            · subst thenEq
              exact RawTerm.isStronglyNormalizing.intro currentThen
                thenClosure
            · exact thenClosure thenTarget ⟨thenStep, thenEq⟩
          | inr falseStep =>
            rcases falseStep with
              ⟨elseTarget, targetEq, _scrutineeStep, elseStep⟩
            rw [targetEq]
            by_cases elseEq : currentElse = elseTarget
            · subst elseEq
              exact RawTerm.isStronglyNormalizing.intro currentElse
                elseClosure
            · exact elseClosure elseTarget ⟨elseStep, elseEq⟩

/-- **K12.20.AV.1 neutral natElim SN preservation**.  Sister to
`boolElim_var`; nat-recursor with variable scrutinee.

Same nested-induction template as `boolElim_var`: variable
scrutinee blocks both ι rules (`iotaNatElimZero` requires
`var → natZero`, `iotaNatElimSucc` requires `var → natSucc _`),
the cong arm collapses to binary movement on (zeroBranch,
succBranch). -/
theorem RawTerm.natElim_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {zeroBranch : RawTerm scope}
    (zeroIsSN : RawTerm.isStronglyNormalizing zeroBranch) :
    ∀ {succBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing succBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.natElim (RawTerm.var position) zeroBranch succBranch) := by
  induction zeroIsSN with
  | intro currentZero _ zeroIH =>
    intro succBranch succIsSN
    induction succIsSN with
    | intro currentSucc succClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.natElim (RawTerm.var position) currentZero currentSucc) ?_
      intro target progressStep
      rcases RawStep.par.natElim_inv progressStep.1 with
        ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
          scrutineeStep, zeroStep, succStep⟩
        | (⟨zeroTarget, _targetEq, scrutineeStep, _zeroStep⟩
          | ⟨predRaw, succTarget, _targetEq, scrutineeStep, _succStep⟩)
      · have scrutineeEq :
            scrutineeTarget = RawTerm.var position :=
          (RawStep.par.var_inv scrutineeStep)
        subst scrutineeEq
        subst targetEq
        by_cases zeroEq : currentZero = zeroTarget
        · subst zeroEq
          have succDistinct :
              currentSucc ≠ succTarget := fun succEq =>
            progressStep.2 (congrArg
              (RawTerm.natElim (RawTerm.var position) currentZero) succEq)
          exact innerIH succTarget ⟨succStep, succDistinct⟩
        · have zeroProgress :
              RawStep.parProgress currentZero zeroTarget :=
            ⟨zeroStep, zeroEq⟩
          by_cases succEq : currentSucc = succTarget
          · subst succEq
            exact zeroIH zeroTarget zeroProgress
              (RawTerm.isStronglyNormalizing.intro currentSucc succClosure)
          · exact zeroIH zeroTarget zeroProgress
              (succClosure succTarget ⟨succStep, succEq⟩)
      · exact (by
          have varEqZero :
              RawTerm.var position = RawTerm.natZero :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqZero)
      · exact (by
          have varEqSucc :
              RawTerm.var position = RawTerm.natSucc predRaw :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqSucc)

/-- **K12.20.AV.2 neutral natRec SN preservation**.  Sister to
`natElim_var`; nat recursor (motive-dependent) with variable
scrutinee.  Same proof shape; the succ-ι rule rebuilds the
target into `app (app succ predRaw) (natRec predRaw zero succ)`
but inversion still requires `scrutinee → natSucc predRaw`,
which `var_inv` rules out. -/
theorem RawTerm.natRec_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {zeroBranch : RawTerm scope}
    (zeroIsSN : RawTerm.isStronglyNormalizing zeroBranch) :
    ∀ {succBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing succBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.natRec (RawTerm.var position) zeroBranch succBranch) := by
  induction zeroIsSN with
  | intro currentZero _ zeroIH =>
    intro succBranch succIsSN
    induction succIsSN with
    | intro currentSucc succClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.natRec (RawTerm.var position) currentZero currentSucc) ?_
      intro target progressStep
      rcases RawStep.par.natRec_inv progressStep.1 with
        ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
          scrutineeStep, zeroStep, succStep⟩
        | (⟨zeroTarget, _targetEq, scrutineeStep, _zeroStep⟩
          | ⟨predRaw, zeroTarget, succTarget,
              _targetEq, scrutineeStep, _zeroStep, _succStep⟩)
      · have scrutineeEq :
            scrutineeTarget = RawTerm.var position :=
          (RawStep.par.var_inv scrutineeStep)
        subst scrutineeEq
        subst targetEq
        by_cases zeroEq : currentZero = zeroTarget
        · subst zeroEq
          have succDistinct :
              currentSucc ≠ succTarget := fun succEq =>
            progressStep.2 (congrArg
              (RawTerm.natRec (RawTerm.var position) currentZero) succEq)
          exact innerIH succTarget ⟨succStep, succDistinct⟩
        · have zeroProgress :
              RawStep.parProgress currentZero zeroTarget :=
            ⟨zeroStep, zeroEq⟩
          by_cases succEq : currentSucc = succTarget
          · subst succEq
            exact zeroIH zeroTarget zeroProgress
              (RawTerm.isStronglyNormalizing.intro currentSucc succClosure)
          · exact zeroIH zeroTarget zeroProgress
              (succClosure succTarget ⟨succStep, succEq⟩)
      · exact (by
          have varEqZero :
              RawTerm.var position = RawTerm.natZero :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqZero)
      · exact (by
          have varEqSucc :
              RawTerm.var position = RawTerm.natSucc predRaw :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqSucc)

/-- **K12.20.AW.1 neutral listElim SN preservation**.  Sister to
the K12.20.AU/AV eliminator family; parametric-list recursor.

Variable scrutinee blocks both ι rules — `iotaListElimNil` needs
`var → listNil`, `iotaListElimCons` needs `var → listCons _ _` —
discharged via `var_inv` on each ι arm. -/
theorem RawTerm.listElim_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {nilBranch : RawTerm scope}
    (nilIsSN : RawTerm.isStronglyNormalizing nilBranch) :
    ∀ {consBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing consBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.listElim (RawTerm.var position) nilBranch consBranch) := by
  induction nilIsSN with
  | intro currentNil _ nilIH =>
    intro consBranch consIsSN
    induction consIsSN with
    | intro currentCons consClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.listElim (RawTerm.var position) currentNil currentCons) ?_
      intro target progressStep
      rcases RawStep.par.listElim_inv progressStep.1 with
        ⟨scrutineeTarget, nilTarget, consTarget, targetEq,
          scrutineeStep, nilStep, consStep⟩
        | (⟨nilTarget, _targetEq, scrutineeStep, _nilStep⟩
          | ⟨headRaw, tailRaw, consTarget,
              _targetEq, scrutineeStep, _consStep⟩)
      · have scrutineeEq :
            scrutineeTarget = RawTerm.var position :=
          (RawStep.par.var_inv scrutineeStep)
        subst scrutineeEq
        subst targetEq
        by_cases nilEq : currentNil = nilTarget
        · subst nilEq
          have consDistinct :
              currentCons ≠ consTarget := fun consEq =>
            progressStep.2 (congrArg
              (RawTerm.listElim (RawTerm.var position) currentNil) consEq)
          exact innerIH consTarget ⟨consStep, consDistinct⟩
        · have nilProgress :
              RawStep.parProgress currentNil nilTarget :=
            ⟨nilStep, nilEq⟩
          by_cases consEq : currentCons = consTarget
          · subst consEq
            exact nilIH nilTarget nilProgress
              (RawTerm.isStronglyNormalizing.intro currentCons consClosure)
          · exact nilIH nilTarget nilProgress
              (consClosure consTarget ⟨consStep, consEq⟩)
      · exact (by
          have varEqNil :
              RawTerm.var position = RawTerm.listNil :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqNil)
      · exact (by
          have varEqCons :
              RawTerm.var position = RawTerm.listCons headRaw tailRaw :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqCons)

/-- **K12.20.AW.2 neutral optionMatch SN preservation**.  Sister
to `listElim_var`; option-eliminator with variable scrutinee.
Same proof shape; ι rules need `var → optionNone` and
`var → optionSome _`. -/
theorem RawTerm.optionMatch_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {noneBranch : RawTerm scope}
    (noneIsSN : RawTerm.isStronglyNormalizing noneBranch) :
    ∀ {someBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing someBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.optionMatch (RawTerm.var position) noneBranch someBranch) := by
  induction noneIsSN with
  | intro currentNone _ noneIH =>
    intro someBranch someIsSN
    induction someIsSN with
    | intro currentSome someClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.optionMatch (RawTerm.var position) currentNone currentSome) ?_
      intro target progressStep
      rcases RawStep.par.optionMatch_inv progressStep.1 with
        ⟨scrutineeTarget, noneTarget, someTarget, targetEq,
          scrutineeStep, noneStep, someStep⟩
        | (⟨noneTarget, _targetEq, scrutineeStep, _noneStep⟩
          | ⟨valueRaw, someTarget, _targetEq, scrutineeStep, _someStep⟩)
      · have scrutineeEq :
            scrutineeTarget = RawTerm.var position :=
          (RawStep.par.var_inv scrutineeStep)
        subst scrutineeEq
        subst targetEq
        by_cases noneEq : currentNone = noneTarget
        · subst noneEq
          have someDistinct :
              currentSome ≠ someTarget := fun someEq =>
            progressStep.2 (congrArg
              (RawTerm.optionMatch (RawTerm.var position) currentNone) someEq)
          exact innerIH someTarget ⟨someStep, someDistinct⟩
        · have noneProgress :
              RawStep.parProgress currentNone noneTarget :=
            ⟨noneStep, noneEq⟩
          by_cases someEq : currentSome = someTarget
          · subst someEq
            exact noneIH noneTarget noneProgress
              (RawTerm.isStronglyNormalizing.intro currentSome someClosure)
          · exact noneIH noneTarget noneProgress
              (someClosure someTarget ⟨someStep, someEq⟩)
      · exact (by
          have varEqNone :
              RawTerm.var position = RawTerm.optionNone :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqNone)
      · exact (by
          have varEqSome :
              RawTerm.var position = RawTerm.optionSome valueRaw :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqSome)

/-- **K12.20.AW.3 neutral eitherMatch SN preservation**.  Sister
to `listElim_var` / `optionMatch_var`; either-eliminator with
variable scrutinee.  Both ι rules carry a payload value (no
nullary constructor on either side), so both demand
`var → eitherInl _` / `var → eitherInr _` — both blocked by
`var_inv`. -/
theorem RawTerm.eitherMatch_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {leftBranch : RawTerm scope}
    (leftIsSN : RawTerm.isStronglyNormalizing leftBranch) :
    ∀ {rightBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing rightBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.eitherMatch (RawTerm.var position) leftBranch rightBranch) := by
  induction leftIsSN with
  | intro currentLeft _ leftIH =>
    intro rightBranch rightIsSN
    induction rightIsSN with
    | intro currentRight rightClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.eitherMatch (RawTerm.var position)
          currentLeft currentRight) ?_
      intro target progressStep
      rcases RawStep.par.eitherMatch_inv progressStep.1 with
        ⟨scrutineeTarget, leftTarget, rightTarget, targetEq,
          scrutineeStep, leftStep, rightStep⟩
        | (⟨valueRaw, leftTarget, _targetEq, scrutineeStep, _leftStep⟩
          | ⟨valueRaw, rightTarget, _targetEq, scrutineeStep, _rightStep⟩)
      · have scrutineeEq :
            scrutineeTarget = RawTerm.var position :=
          (RawStep.par.var_inv scrutineeStep)
        subst scrutineeEq
        subst targetEq
        by_cases leftEq : currentLeft = leftTarget
        · subst leftEq
          have rightDistinct :
              currentRight ≠ rightTarget := fun rightEq =>
            progressStep.2 (congrArg
              (RawTerm.eitherMatch (RawTerm.var position) currentLeft) rightEq)
          exact innerIH rightTarget ⟨rightStep, rightDistinct⟩
        · have leftProgress :
              RawStep.parProgress currentLeft leftTarget :=
            ⟨leftStep, leftEq⟩
          by_cases rightEq : currentRight = rightTarget
          · subst rightEq
            exact leftIH leftTarget leftProgress
              (RawTerm.isStronglyNormalizing.intro currentRight rightClosure)
          · exact leftIH leftTarget leftProgress
              (rightClosure rightTarget ⟨rightStep, rightEq⟩)
      · exact (by
          have varEqInl :
              RawTerm.var position = RawTerm.eitherInl valueRaw :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqInl)
      · exact (by
          have varEqInr :
              RawTerm.var position = RawTerm.eitherInr valueRaw :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqInr)

/-- **K12.20.AX.1 neutral pathApp SN preservation**.  Direct analogue
of `app_var`: var sits in the path-term slot, interval argument is
SN witness.  `pathApp_inv` gives 2 arms (cong + β); β arm requires
`pathTerm → pathLam _`, defeated by `var_inv` + nomatch on the
resulting `var = pathLam _` equation. -/
theorem RawTerm.pathApp_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {intervalArgRaw : RawTerm scope}
    (intervalIsSN : RawTerm.isStronglyNormalizing intervalArgRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.pathApp (RawTerm.var position) intervalArgRaw) := by
  induction intervalIsSN with
  | intro currentInterval _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.pathApp (RawTerm.var position) currentInterval) ?_
    intro target progressStep
    rcases RawStep.par.pathApp_inv progressStep.1 with
      ⟨pathTarget, intervalTarget, targetEq, pathStep, intervalStep⟩
      | ⟨bodyTarget, _intervalTarget, _targetEq, pathStep, _intervalStep⟩
    · have pathEq : pathTarget = RawTerm.var position :=
        (RawStep.par.var_inv pathStep)
      subst pathEq
      subst targetEq
      have intervalDistinct :
          currentInterval ≠ intervalTarget := fun intervalEq =>
        progressStep.2
          (congrArg (RawTerm.pathApp (RawTerm.var position)) intervalEq)
      exact inductiveHypothesis intervalTarget
        ⟨intervalStep, intervalDistinct⟩
    · exact (by
        have varEqPathLam :
            RawTerm.pathLam bodyTarget = RawTerm.var position :=
          (RawStep.par.var_inv pathStep)
        nomatch varEqPathLam)

/-- Path application with a neutral path head is strongly normalizing
when both the path head and interval argument are strongly normalizing.

The path beta arms are impossible because every parallel reduct of the
neutral head stays neutral, and neutral terms are never `pathLam`-
shaped.  The congruence arm recurses on head progress or interval
progress. -/
theorem RawTerm.pathApp_neutral_isStronglyNormalizing {scope : Nat}
    {pathRaw intervalArgRaw : RawTerm scope}
    (pathIsNeutral : RawTerm.IsNeutral pathRaw)
    (pathIsSN : RawTerm.isStronglyNormalizing pathRaw)
    (intervalIsSN : RawTerm.isStronglyNormalizing intervalArgRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.pathApp pathRaw intervalArgRaw) := by
  induction pathIsSN generalizing intervalArgRaw with
  | intro currentPath _ pathInduction =>
    induction intervalIsSN with
    | intro currentInterval intervalClosure intervalInduction =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.pathApp currentPath currentInterval) ?_
      intro target progressStep
      rcases RawStep.par.pathApp_inv progressStep.1 with
        ⟨pathTarget, intervalTarget, targetEq, pathStep, intervalStep⟩
        | ⟨bodyTarget, _intervalTarget, _targetEq,
            pathStep, _intervalStep⟩
      · subst targetEq
        have pathTargetIsNeutral : RawTerm.IsNeutral pathTarget :=
          RawTerm.IsNeutral.par_preserves pathIsNeutral pathStep
        have intervalTargetIsSN :
            RawTerm.isStronglyNormalizing intervalTarget := by
          by_cases intervalEq : currentInterval = intervalTarget
          · subst intervalEq
            exact RawTerm.isStronglyNormalizing.intro
              currentInterval intervalClosure
          · exact intervalClosure intervalTarget
              ⟨intervalStep, intervalEq⟩
        by_cases pathEq : currentPath = pathTarget
        · subst pathEq
          by_cases intervalEq : currentInterval = intervalTarget
          · subst intervalEq
            exact (progressStep.2 rfl).elim
          · exact intervalInduction intervalTarget
              ⟨intervalStep, intervalEq⟩
        · exact pathInduction pathTarget
            ⟨pathStep, pathEq⟩
            pathTargetIsNeutral
            intervalTargetIsSN
      · exact (RawTerm.IsNeutral.not_pathLam
          (RawTerm.IsNeutral.par_preserves pathIsNeutral pathStep)
          (bodyRaw := bodyTarget) rfl).elim

/-- Glue elimination with a neutral glued value is strongly normalizing
when the glued value is strongly normalizing.

The Glue beta arms are impossible because every parallel reduct of the
neutral glued value stays neutral, and neutral terms are never
`glueIntro`-shaped.  The congruence arm recurses on glued-value
progress. -/
theorem RawTerm.glueElim_neutral_isStronglyNormalizing {scope : Nat}
    {gluedRaw : RawTerm scope}
    (gluedIsNeutral : RawTerm.IsNeutral gluedRaw)
    (gluedIsSN : RawTerm.isStronglyNormalizing gluedRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.glueElim gluedRaw) := by
  induction gluedIsSN with
  | intro currentGlued _ gluedInduction =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.glueElim currentGlued) ?_
    intro target progressStep
    rcases RawStep.par.glueElim_inv progressStep.1 with
      ⟨gluedTarget, targetEq, gluedStep⟩
      | ⟨baseTarget, partialTarget, _targetEq, gluedStep⟩
    · have gluedTargetIsNeutral : RawTerm.IsNeutral gluedTarget :=
        RawTerm.IsNeutral.par_preserves gluedIsNeutral gluedStep
      by_cases gluedEq : currentGlued = gluedTarget
      · subst gluedEq
        subst targetEq
        exact (progressStep.2 rfl).elim
      · subst targetEq
        exact gluedInduction gluedTarget
          ⟨gluedStep, gluedEq⟩ gluedTargetIsNeutral
    · exact (RawTerm.IsNeutral.not_glueIntro
        (RawTerm.IsNeutral.par_preserves gluedIsNeutral gluedStep)
        (baseRaw := baseTarget) (partialRaw := partialTarget) rfl).elim

/-- **K12.20.AX.2 neutral equivApp SN preservation**.  Sister to
`pathApp_var`; var sits in the equiv-term slot, argument is the SN
witness.  `equivApp_inv` is cong-only (no β rule at raw layer yet),
so no nomatch defense needed — the cong arm alone preserves SN
via inductive hypothesis. -/
theorem RawTerm.equivApp_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {argumentRaw : RawTerm scope}
    (argumentIsSN : RawTerm.isStronglyNormalizing argumentRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.equivApp (RawTerm.var position) argumentRaw) := by
  induction argumentIsSN with
  | intro currentArgument _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.equivApp (RawTerm.var position) currentArgument) ?_
    intro target progressStep
    obtain ⟨equivTarget, argumentTarget, targetEq, equivStep, argumentStep⟩ :=
      RawStep.par.equivApp_inv progressStep.1
    have equivEq : equivTarget = RawTerm.var position :=
      (RawStep.par.var_inv equivStep)
    subst equivEq
    subst targetEq
    have argumentDistinct :
        currentArgument ≠ argumentTarget := fun argumentEq =>
      progressStep.2
        (congrArg (RawTerm.equivApp (RawTerm.var position)) argumentEq)
    exact inductiveHypothesis argumentTarget
      ⟨argumentStep, argumentDistinct⟩

/-- **K12.20.AX.3 neutral idJ SN preservation**.  HOTT J eliminator
with variable witness (the equality being eliminated).  `idJ_inv`
gives 2 arms (cong + iotaIdJRefl); ι arm requires
`witness → refl _`, defeated by `var_inv` + nomatch on
`var = refl _`.  Variable sits in the SECOND slot since
`Term.idJ baseCase witness` destructs `witness`. -/
theorem RawTerm.idJ_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {baseCaseRaw : RawTerm scope}
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.idJ baseCaseRaw (RawTerm.var position)) := by
  induction baseCaseIsSN with
  | intro currentBase _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.idJ currentBase (RawTerm.var position)) ?_
    intro target progressStep
    rcases RawStep.par.idJ_inv progressStep.1 with
      ⟨baseTarget, witnessTarget, targetEq, baseStep, witnessStep⟩
      | ⟨witnessRaw, _baseTarget, _targetEq, witnessStep, _baseStep⟩
    · have witnessEq : witnessTarget = RawTerm.var position :=
        (RawStep.par.var_inv witnessStep)
      subst witnessEq
      subst targetEq
      have baseDistinct :
          currentBase ≠ baseTarget := fun baseEq =>
        progressStep.2
          (congrArg (fun base => RawTerm.idJ base (RawTerm.var position))
            baseEq)
      exact inductiveHypothesis baseTarget
        ⟨baseStep, baseDistinct⟩
    · exact (by
        have varEqRefl :
            RawTerm.var position = RawTerm.refl witnessRaw :=
          (RawStep.par.var_inv witnessStep).symm
        nomatch varEqRefl)

/-- **K12.20.AX.4 neutral oeqJ SN preservation**.  Observational
equality J eliminator with variable witness.  `oeqJ_inv` is
cong-only (no ι rule at raw layer yet; oeq-style witness elimination
deferred), so no nomatch defense needed.  Same proof pattern as
`equivApp_var` but with var in the SECOND slot. -/
theorem RawTerm.oeqJ_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {baseCaseRaw : RawTerm scope}
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.oeqJ baseCaseRaw (RawTerm.var position)) := by
  induction baseCaseIsSN with
  | intro currentBase _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.oeqJ currentBase (RawTerm.var position)) ?_
    intro target progressStep
    obtain ⟨baseTarget, witnessTarget, targetEq, baseStep, witnessStep⟩ :=
      RawStep.par.oeqJ_inv progressStep.1
    have witnessEq : witnessTarget = RawTerm.var position :=
      (RawStep.par.var_inv witnessStep)
    subst witnessEq
    subst targetEq
    have baseDistinct :
        currentBase ≠ baseTarget := fun baseEq =>
      progressStep.2
        (congrArg (fun base => RawTerm.oeqJ base (RawTerm.var position))
          baseEq)
    exact inductiveHypothesis baseTarget
      ⟨baseStep, baseDistinct⟩

/-- Observational-equality eliminator SN preservation.  Unlike
`idJ` and `idStrictRec`, the current raw `oeqJ` fragment has no
refl-ι firing rule; `RawStep.par.oeqJ_inv` is pure congruence over
the base case and witness. -/
theorem RawTerm.oeqJ_isStronglyNormalizing {scope : Nat}
    {baseCaseRaw : RawTerm scope}
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    ∀ {witnessRaw : RawTerm scope},
      RawTerm.isStronglyNormalizing witnessRaw →
      RawTerm.isStronglyNormalizing
        (RawTerm.oeqJ baseCaseRaw witnessRaw) := by
  induction baseCaseIsSN with
  | intro currentBase _ baseIH =>
    intro witnessRaw witnessIsSN
    induction witnessIsSN with
    | intro currentWitness witnessClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.oeqJ currentBase currentWitness) ?_
      intro target progressStep
      obtain ⟨baseTarget, witnessTarget, targetEq,
              baseStep, witnessStep⟩ :=
        RawStep.par.oeqJ_inv progressStep.1
      subst targetEq
      by_cases baseEq : currentBase = baseTarget
      · subst baseEq
        have witnessDistinct :
            currentWitness ≠ witnessTarget := fun witnessEq =>
          progressStep.2
            (congrArg (RawTerm.oeqJ currentBase) witnessEq)
        exact innerIH witnessTarget ⟨witnessStep, witnessDistinct⟩
      · have baseProgress :
            RawStep.parProgress currentBase baseTarget :=
          ⟨baseStep, baseEq⟩
        by_cases witnessEq : currentWitness = witnessTarget
        · subst witnessEq
          exact baseIH baseTarget baseProgress
            (RawTerm.isStronglyNormalizing.intro currentWitness
              witnessClosure)
        · exact baseIH baseTarget baseProgress
            (witnessClosure witnessTarget ⟨witnessStep, witnessEq⟩)

/-- Identity eliminator SN preservation.  Unlike `oeqJ`, `idJ` has
refl-ι rules, so the iota arm returns the reduced base case directly.
The congruence arm follows the same nested-SN induction pattern as
`RawTerm.oeqJ_isStronglyNormalizing`. -/
theorem RawTerm.idJ_isStronglyNormalizing {scope : Nat}
    {baseCaseRaw : RawTerm scope}
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    ∀ {witnessRaw : RawTerm scope},
      RawTerm.isStronglyNormalizing witnessRaw →
      RawTerm.isStronglyNormalizing
        (RawTerm.idJ baseCaseRaw witnessRaw) := by
  induction baseCaseIsSN with
  | intro currentBase baseClosure baseIH =>
    intro witnessRaw witnessIsSN
    induction witnessIsSN with
    | intro currentWitness witnessClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.idJ currentBase currentWitness) ?_
      intro target progressStep
      cases RawStep.par.idJ_inv progressStep.1 with
      | inl congruentStep =>
        rcases congruentStep with
          ⟨baseTarget, witnessTarget, targetEq, baseStep, witnessStep⟩
        subst targetEq
        by_cases baseEq : currentBase = baseTarget
        · subst baseEq
          have witnessDistinct :
              currentWitness ≠ witnessTarget := fun witnessEq =>
            progressStep.2
              (congrArg (RawTerm.idJ currentBase) witnessEq)
          exact innerIH witnessTarget ⟨witnessStep, witnessDistinct⟩
        · have baseProgress :
              RawStep.parProgress currentBase baseTarget :=
            ⟨baseStep, baseEq⟩
          by_cases witnessEq : currentWitness = witnessTarget
          · subst witnessEq
            exact baseIH baseTarget baseProgress
              (RawTerm.isStronglyNormalizing.intro currentWitness
                witnessClosure)
          · exact baseIH baseTarget baseProgress
              (witnessClosure witnessTarget ⟨witnessStep, witnessEq⟩)
      | inr iotaStep =>
        rcases iotaStep with
          ⟨_witnessRaw, baseTarget, targetEq, _witnessStep, baseStep⟩
        rw [targetEq]
        by_cases baseEq : currentBase = baseTarget
        · subst baseEq
          exact RawTerm.isStronglyNormalizing.intro currentBase baseClosure
        · exact baseClosure baseTarget ⟨baseStep, baseEq⟩

/-- **K12.20.AX.5 neutral idStrictRec SN preservation**.  Strict-id
recursor with variable witness.  `idStrictRec_inv` gives 2 arms
(cong + iotaIdStrictRecRefl); ι arm requires
`witness → idStrictRefl _`, defeated by `var_inv` + nomatch on
`var = idStrictRefl _`. -/
theorem RawTerm.idStrictRec_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {baseCaseRaw : RawTerm scope}
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.idStrictRec baseCaseRaw (RawTerm.var position)) := by
  induction baseCaseIsSN with
  | intro currentBase _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.idStrictRec currentBase (RawTerm.var position)) ?_
    intro target progressStep
    rcases RawStep.par.idStrictRec_inv progressStep.1 with
      ⟨baseTarget, witnessTarget, targetEq, baseStep, witnessStep⟩
      | ⟨reflRawArgument, _baseTarget, _targetEq, witnessStep, _baseStep⟩
    · have witnessEq : witnessTarget = RawTerm.var position :=
        (RawStep.par.var_inv witnessStep)
      subst witnessEq
      subst targetEq
      have baseDistinct :
          currentBase ≠ baseTarget := fun baseEq =>
        progressStep.2
          (congrArg
            (fun base => RawTerm.idStrictRec base (RawTerm.var position))
            baseEq)
      exact inductiveHypothesis baseTarget
        ⟨baseStep, baseDistinct⟩
    · exact (by
        have varEqIdStrictRefl :
            RawTerm.var position = RawTerm.idStrictRefl reflRawArgument :=
          (RawStep.par.var_inv witnessStep).symm
        nomatch varEqIdStrictRefl)

/-- Strict identity recursor SN preservation.  This mirrors
`RawTerm.idJ_isStronglyNormalizing`, with the strict reflexivity
constructor in the iota arm. -/
theorem RawTerm.idStrictRec_isStronglyNormalizing {scope : Nat}
    {baseCaseRaw : RawTerm scope}
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    ∀ {witnessRaw : RawTerm scope},
      RawTerm.isStronglyNormalizing witnessRaw →
      RawTerm.isStronglyNormalizing
        (RawTerm.idStrictRec baseCaseRaw witnessRaw) := by
  induction baseCaseIsSN with
  | intro currentBase baseClosure baseIH =>
    intro witnessRaw witnessIsSN
    induction witnessIsSN with
    | intro currentWitness witnessClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.idStrictRec currentBase currentWitness) ?_
      intro target progressStep
      cases RawStep.par.idStrictRec_inv progressStep.1 with
      | inl congruentStep =>
        rcases congruentStep with
          ⟨baseTarget, witnessTarget, targetEq, baseStep, witnessStep⟩
        subst targetEq
        by_cases baseEq : currentBase = baseTarget
        · subst baseEq
          have witnessDistinct :
              currentWitness ≠ witnessTarget := fun witnessEq =>
            progressStep.2
              (congrArg (RawTerm.idStrictRec currentBase) witnessEq)
          exact innerIH witnessTarget ⟨witnessStep, witnessDistinct⟩
        · have baseProgress :
              RawStep.parProgress currentBase baseTarget :=
            ⟨baseStep, baseEq⟩
          by_cases witnessEq : currentWitness = witnessTarget
          · subst witnessEq
            exact baseIH baseTarget baseProgress
              (RawTerm.isStronglyNormalizing.intro currentWitness
                witnessClosure)
          · exact baseIH baseTarget baseProgress
              (witnessClosure witnessTarget ⟨witnessStep, witnessEq⟩)
      | inr iotaStep =>
        rcases iotaStep with
          ⟨_reflRawArgument, baseTarget, targetEq, _witnessStep, baseStep⟩
        rw [targetEq]
        by_cases baseEq : currentBase = baseTarget
        · subst baseEq
          exact RawTerm.isStronglyNormalizing.intro currentBase baseClosure
        · exact baseClosure baseTarget ⟨baseStep, baseEq⟩

/-- **K12.20.AY.1 neutral modElim SN preservation**.  Unary modal
destructor with variable inner term.  `modElim_inv` gives 2 arms:
cong (innerTerm → innerTarget) and βModElimIntro (innerTerm →
modIntro payloadTarget).  Variable inner: cong arm yields
`innerTarget = var position` via var_inv, then refl on the source
contradicts progressStep.2; β arm needs `var → modIntro _`,
defeated by var_inv + nomatch on `var = modIntro _`. -/
theorem RawTerm.modElim_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope) :
    RawTerm.isStronglyNormalizing
      (RawTerm.modElim (RawTerm.var position)) := by
  refine RawTerm.isStronglyNormalizing.intro
    (RawTerm.modElim (RawTerm.var position)) ?_
  intro target progressStep
  rcases RawStep.par.modElim_inv progressStep.1 with
    ⟨innerTarget, targetEq, innerStep⟩
    | ⟨payloadTarget, _targetEq, innerStep⟩
  · have innerEq : innerTarget = RawTerm.var position :=
      (RawStep.par.var_inv innerStep)
    subst innerEq
    subst targetEq
    exact (progressStep.2 rfl).elim
  · exact (by
      have varEqModIntro :
          RawTerm.modIntro payloadTarget = RawTerm.var position :=
        (RawStep.par.var_inv innerStep)
      nomatch varEqModIntro)

/-- **K12.20.AY.2 neutral glueElim SN preservation**.  Unary cubical
destructor with variable glued value.  `glueElim_inv` gives 2 arms:
cong and βGlueElimIntro (gluedValue → glueIntro baseTarget
partialTarget).  Variable glued: cong arm contradicts
progressStep.2 via refl-on-source; β arm defeated by var_inv +
nomatch on `var = glueIntro _ _`. -/
theorem RawTerm.glueElim_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope) :
    RawTerm.isStronglyNormalizing
      (RawTerm.glueElim (RawTerm.var position)) := by
  refine RawTerm.isStronglyNormalizing.intro
    (RawTerm.glueElim (RawTerm.var position)) ?_
  intro target progressStep
  rcases RawStep.par.glueElim_inv progressStep.1 with
    ⟨gluedTarget, targetEq, gluedStep⟩
    | ⟨baseTarget, partialTarget, _targetEq, gluedStep⟩
  · have gluedEq : gluedTarget = RawTerm.var position :=
      (RawStep.par.var_inv gluedStep)
    subst gluedEq
    subst targetEq
    exact (progressStep.2 rfl).elim
  · exact (by
      have varEqGlueIntro :
          RawTerm.glueIntro baseTarget partialTarget =
            RawTerm.var position :=
        (RawStep.par.var_inv gluedStep)
      nomatch varEqGlueIntro)

/-- **K12.20.AY.3 neutral hcomp SN preservation**.  Binary cubical
homogeneous-composition operator with variable in sides slot.
`hcomp_inv` is cong-only (no face-firing β at raw layer yet; full
Kan-op β reserved for cubical extension), so single-arm nested
induction on cap term's SN witness — directly analogous to
`equivApp_var`. -/
theorem RawTerm.hcomp_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {capTermRaw : RawTerm scope}
    (capIsSN : RawTerm.isStronglyNormalizing capTermRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.hcomp (RawTerm.var position) capTermRaw) := by
  induction capIsSN with
  | intro currentCap _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.hcomp (RawTerm.var position) currentCap) ?_
    intro target progressStep
    obtain ⟨sidesTarget, capTarget, targetEq, sidesStep, capStep⟩ :=
      RawStep.par.hcomp_inv progressStep.1
    have sidesEq : sidesTarget = RawTerm.var position :=
      (RawStep.par.var_inv sidesStep)
    subst sidesEq
    subst targetEq
    have capDistinct :
        currentCap ≠ capTarget := fun capEq =>
      progressStep.2 (congrArg (RawTerm.hcomp (RawTerm.var position)) capEq)
    exact inductiveHypothesis capTarget ⟨capStep, capDistinct⟩

/-- **K12.20.AY.4 neutral transp SN preservation**.  Binary cubical
transport with variable in path slot.  `transp_inv` is the heaviest
inversion in the kernel: 7 arms covering cong + 3 shape-equality β
rules (transpReflBeta on constant `pathLam _.weaken`, uaBeta on
`uaToEquiv _`, transpCompose on `pathCompose _ _`) + 3 deep β
counterparts where `pathTerm` par-steps to those ctors.  Variable
pathTerm: shape-equality arms defeated by direct nomatch on
`var = pathLam _ | uaToEquiv _ | pathCompose _ _`; deep arms
defeated by var_inv + nomatch on the resulting `ctor _ = var`. -/
theorem RawTerm.transp_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {sourceTermRaw : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing sourceTermRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.transp (RawTerm.var position) sourceTermRaw) := by
  induction sourceIsSN with
  | intro currentSource _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.transp (RawTerm.var position) currentSource) ?_
    intro target progressStep
    rcases RawStep.par.transp_inv progressStep.1 with
      ⟨pathTarget, sourceTarget, targetEq, pathStep, sourceStep⟩
      | ⟨_typeRawSource, _sourceTarget, pathEqRefl, _targetEq, _sourceStep⟩
      | ⟨_typeRawTarget, _sourceTarget, _targetEq, pathStepRefl, _sourceStep⟩
      | ⟨_proofRawSource, _proofRawTarget, _sourceTarget, pathEqUa,
          _targetEq, _proofStep, _sourceStep⟩
      | ⟨_proofRawTarget, _sourceTarget, _targetEq, pathStepUa,
          _sourceStep⟩
      | ⟨_leftRawSource, _leftRawTarget, _rightRawSource,
          _rightRawTarget, _sourceTarget, pathEqCompose, _targetEq,
          _leftStep, _rightStep, _sourceStep⟩
      | ⟨_leftRawTarget, _rightRawTarget, _sourceTarget, _targetEq,
          pathStepCompose, _sourceStep⟩
    · have pathEq : pathTarget = RawTerm.var position :=
        (RawStep.par.var_inv pathStep)
      subst pathEq
      subst targetEq
      have sourceDistinct :
          currentSource ≠ sourceTarget := fun sourceEq =>
        progressStep.2
          (congrArg (RawTerm.transp (RawTerm.var position)) sourceEq)
      exact inductiveHypothesis sourceTarget
        ⟨sourceStep, sourceDistinct⟩
    · exact (by nomatch pathEqRefl)
    · exact (by
        have varEqPathLam := (RawStep.par.var_inv pathStepRefl)
        nomatch varEqPathLam)
    · exact (by nomatch pathEqUa)
    · exact (by
        have varEqUaToEquiv := (RawStep.par.var_inv pathStepUa)
        nomatch varEqUaToEquiv)
    · exact (by nomatch pathEqCompose)
    · exact (by
        have varEqPathCompose := (RawStep.par.var_inv pathStepCompose)
        nomatch varEqPathCompose)

/-- **K12.20.BA.1 neutral refineElim SN preservation**.  Stage 1
completion (overlooked in K12.20.AY's "18/18" close-out — the
kernel has 20 unary/binary destructors with fireable β/ι rules at
the raw layer, including refineElim and recordProj which are
needed for K12.20.BC+ compound refine/record varShape work).
Unary refinement destructor with variable refined value;
refineElim_inv gives 2 arms: cong and βRefineElimIntro
(refinedValue → refineIntro valueTarget proofTarget).  Direct
`fst_var`-style template — cong arm contradicts progressStep.2
via refl-on-source; β arm defeated by `var_inv` + nomatch on
`var = refineIntro _ _`. -/
theorem RawTerm.refineElim_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope) :
    RawTerm.isStronglyNormalizing
      (RawTerm.refineElim (RawTerm.var position)) := by
  refine RawTerm.isStronglyNormalizing.intro
    (RawTerm.refineElim (RawTerm.var position)) ?_
  intro target progressStep
  rcases RawStep.par.refineElim_inv progressStep.1 with
    ⟨refinedTarget, targetEq, refinedStep⟩
    | ⟨valueTarget, proofTarget, _targetEq, refinedStep⟩
  · have refinedEq : refinedTarget = RawTerm.var position :=
      (RawStep.par.var_inv refinedStep)
    subst refinedEq
    subst targetEq
    exact (progressStep.2 rfl).elim
  · exact (by
      have varEqRefineIntro :
          RawTerm.refineIntro valueTarget proofTarget =
            RawTerm.var position :=
        (RawStep.par.var_inv refinedStep)
      nomatch varEqRefineIntro)

/-- **K12.20.BA.2 neutral recordProj SN preservation**.  Sister to
`refineElim_var`; unary record-field projection with variable
record value.  `recordProj_inv` gives 2 arms: cong and
βRecordProjIntro (recordValue → recordIntro firstTarget).  Same
fst_var-style proof.  Closes Stage 1 honestly at 20/20 kernel
destructors. -/
theorem RawTerm.recordProj_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope) :
    RawTerm.isStronglyNormalizing
      (RawTerm.recordProj (RawTerm.var position)) := by
  refine RawTerm.isStronglyNormalizing.intro
    (RawTerm.recordProj (RawTerm.var position)) ?_
  intro target progressStep
  rcases RawStep.par.recordProj_inv progressStep.1 with
    ⟨recordTarget, targetEq, recordStep⟩
    | ⟨firstTarget, _targetEq, recordStep⟩
  · have recordEq : recordTarget = RawTerm.var position :=
      (RawStep.par.var_inv recordStep)
    subst recordEq
    subst targetEq
    exact (progressStep.2 rfl).elim
  · exact (by
      have varEqRecordIntro :
          RawTerm.recordIntro firstTarget = RawTerm.var position :=
        (RawStep.par.var_inv recordStep)
      nomatch varEqRecordIntro)

/-- **K12.20.BA.3 neutral codataDest SN preservation**.  Unary
codata observation with variable codata value.  `codataDest_inv`
gives 2 arms: congruent observation and codata β after the codata
value develops to `codataUnfold`.  The congruent arm is reflexive
after `var_inv`; the β arm is impossible because a variable cannot
parallel-develop to `codataUnfold _ _`. -/
theorem RawTerm.codataDest_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope) :
    RawTerm.isStronglyNormalizing
      (RawTerm.codataDest (RawTerm.var position)) := by
  refine RawTerm.isStronglyNormalizing.intro
    (RawTerm.codataDest (RawTerm.var position)) ?_
  intro target progressStep
  rcases RawStep.par.codataDest_inv progressStep.1 with
    ⟨codataTarget, targetEq, codataStep⟩
    | ⟨stateTarget, transitionTarget, _targetEq, codataStep⟩
  · have codataEq : codataTarget = RawTerm.var position :=
      (RawStep.par.var_inv codataStep)
    subst codataEq
    subst targetEq
    exact (progressStep.2 rfl).elim
  · exact (by
      have varEqCodataUnfold :
          RawTerm.codataUnfold stateTarget transitionTarget =
            RawTerm.var position :=
        (RawStep.par.var_inv codataStep)
      nomatch varEqCodataUnfold)

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

/-- Head-β SN expansion for first projection over a pair.

If both components are strongly normalizing, then `fst (pair first second)`
is strongly normalizing.  Congruence reducts recurse through the pair
components; β reducts land on a reduct of the first component. -/
theorem RawTerm.fst_pair_isStronglyNormalizing {scope : Nat}
    {firstValue : RawTerm scope}
    (firstIsSN : RawTerm.isStronglyNormalizing firstValue) :
    ∀ {secondValue : RawTerm scope},
      RawTerm.isStronglyNormalizing secondValue →
      RawTerm.isStronglyNormalizing
        (RawTerm.fst (RawTerm.pair firstValue secondValue)) := by
  induction firstIsSN with
  | intro currentFirst firstClosure firstIH =>
    intro secondValue secondIsSN
    induction secondIsSN with
    | intro currentSecond secondClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.fst (RawTerm.pair currentFirst currentSecond)) ?_
      intro target progressStep
      rcases RawStep.par.fst_inv progressStep.1 with
        ⟨pairTarget, targetEq, pairStep⟩
        | ⟨firstTarget, secondTarget, targetEq, pairStep⟩
      · obtain ⟨firstTarget, secondTarget, pairTargetEq,
            firstStep, secondStep⟩ :=
          RawStep.par.pair_inv pairStep
        subst pairTargetEq
        subst targetEq
        by_cases firstEq : currentFirst = firstTarget
        · subst firstEq
          by_cases secondEq : currentSecond = secondTarget
          · subst secondEq
            exact False.elim (progressStep.2 rfl)
          · exact innerIH secondTarget ⟨secondStep, secondEq⟩
        · have firstProgress :
              RawStep.parProgress currentFirst firstTarget :=
            ⟨firstStep, firstEq⟩
          by_cases secondEq : currentSecond = secondTarget
          · subst secondEq
            exact firstIH firstTarget firstProgress
              (RawTerm.isStronglyNormalizing.intro currentSecond secondClosure)
          · exact firstIH firstTarget firstProgress
              (secondClosure secondTarget ⟨secondStep, secondEq⟩)
      · obtain ⟨firstPairTarget, _secondPairTarget, pairTargetEq,
            firstStep, _secondStep⟩ :=
          RawStep.par.pair_inv pairStep
        injection pairTargetEq with _scopeEq firstTargetEq _secondTargetEq
        rw [targetEq]
        have firstStepToTarget : RawStep.par currentFirst firstTarget := by
          rw [firstTargetEq]
          exact firstStep
        by_cases firstEq : currentFirst = firstTarget
        · subst firstEq
          exact RawTerm.isStronglyNormalizing.intro
            currentFirst firstClosure
        · exact firstClosure firstTarget ⟨firstStepToTarget, firstEq⟩

/-- Head-β SN expansion for second projection over a pair.

If both components are strongly normalizing, then `snd (pair first second)`
is strongly normalizing.  Congruence reducts recurse through the pair
components; β reducts land on a reduct of the second component. -/
theorem RawTerm.snd_pair_isStronglyNormalizing {scope : Nat}
    {firstValue : RawTerm scope}
    (firstIsSN : RawTerm.isStronglyNormalizing firstValue) :
    ∀ {secondValue : RawTerm scope},
      RawTerm.isStronglyNormalizing secondValue →
      RawTerm.isStronglyNormalizing
        (RawTerm.snd (RawTerm.pair firstValue secondValue)) := by
  induction firstIsSN with
  | intro currentFirst firstClosure firstIH =>
    intro secondValue secondIsSN
    induction secondIsSN with
    | intro currentSecond secondClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.snd (RawTerm.pair currentFirst currentSecond)) ?_
      intro target progressStep
      rcases RawStep.par.snd_inv progressStep.1 with
        ⟨pairTarget, targetEq, pairStep⟩
        | ⟨firstTarget, secondTarget, targetEq, pairStep⟩
      · obtain ⟨firstTarget, secondTarget, pairTargetEq,
            firstStep, secondStep⟩ :=
          RawStep.par.pair_inv pairStep
        subst pairTargetEq
        subst targetEq
        by_cases firstEq : currentFirst = firstTarget
        · subst firstEq
          by_cases secondEq : currentSecond = secondTarget
          · subst secondEq
            exact False.elim (progressStep.2 rfl)
          · exact innerIH secondTarget ⟨secondStep, secondEq⟩
        · have firstProgress :
              RawStep.parProgress currentFirst firstTarget :=
            ⟨firstStep, firstEq⟩
          by_cases secondEq : currentSecond = secondTarget
          · subst secondEq
            exact firstIH firstTarget firstProgress
              (RawTerm.isStronglyNormalizing.intro currentSecond secondClosure)
          · exact firstIH firstTarget firstProgress
              (secondClosure secondTarget ⟨secondStep, secondEq⟩)
      · obtain ⟨_firstPairTarget, secondPairTarget, pairTargetEq,
            _firstStep, secondStep⟩ :=
          RawStep.par.pair_inv pairStep
        injection pairTargetEq with _scopeEq _firstTargetEq secondTargetEq
        rw [targetEq]
        have secondStepToTarget : RawStep.par currentSecond secondTarget := by
          rw [secondTargetEq]
          exact secondStep
        by_cases secondEq : currentSecond = secondTarget
        · subst secondEq
          exact RawTerm.isStronglyNormalizing.intro
            currentSecond secondClosure
        · exact secondClosure secondTarget ⟨secondStepToTarget, secondEq⟩

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

/-- **K12.20.AR.2 universeCode SN preservation** — universe code
intro at outer level.  `RawTerm.universeCode innerLevel` has no
β/ι rules; only `RawStep.par.refl` applies (per
`RawStep.par.universeCode_inv` in
`Reduction/RawParInversion.lean`), so `parProgress`'s
source-≠-target requirement contradicts the inversion's
.symm. -/
theorem RawTerm.universeCode_isStronglyNormalizing {scope : Nat}
    (innerLevel : Nat) :
    RawTerm.isStronglyNormalizing
      (RawTerm.universeCode innerLevel : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro
    (RawTerm.universeCode innerLevel : RawTerm scope)
    (fun _ progressStep =>
      (progressStep.2
        (RawStep.par.universeCode_inv progressStep.1).symm).elim)

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

Compound Reducible arms split into two families.  Weak/SN-output
arms whose closures only ask for SN of eliminator results can be
closed directly from the raw neutral-eliminator SN helpers once their
branch-SN premises are explicit.  Strong-output arms (arrow, sigmaTy,
path, glue, equiv, refine, record, codata) use the higher-order
varShape pattern: each arm takes the CR3 hook for its strict sub-Ty
as an explicit parameter, mirroring `Reducible.step_preserves`'
higher-order CR2 structure without pretending that arbitrary neutral
CR3 has already shipped.
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

/-! ### K12.20.U2 SN-direct CR3 arms

For SN-direct Reducible arms, typed CR3 reduces to the raw SN
constructor direction: if every non-trivial raw reduct is SN, then
the source term is SN, hence Reducible at that type.  These lemmas
do not claim the compound-Ty CR3 theorem; they establish exactly the
ten arms whose Reducible definition has no additional closure field. -/

/-- **K12.20.U2 unit arm**: CR3 for the unit SN-direct arm. -/
theorem Reducible.unit_of_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context Ty.unit sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Reducible Ty.unit sourceTerm :=
  Term.isStronglyNormalizing.of_raw_progress_closure sourceTerm closure

/-- **K12.20.U2 bool arm**. -/
theorem Reducible.bool_of_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context Ty.bool sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Reducible Ty.bool sourceTerm :=
  Term.isStronglyNormalizing.of_raw_progress_closure sourceTerm closure

/-- **K12.20.U2 nat arm**. -/
theorem Reducible.nat_of_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context Ty.nat sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Reducible Ty.nat sourceTerm :=
  Term.isStronglyNormalizing.of_raw_progress_closure sourceTerm closure

/-- **K12.20.U2 empty arm**. -/
theorem Reducible.empty_of_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context Ty.empty sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Reducible Ty.empty sourceTerm :=
  Term.isStronglyNormalizing.of_raw_progress_closure sourceTerm closure

/-- **K12.20.U2 interval arm**. -/
theorem Reducible.interval_of_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context Ty.interval sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Reducible Ty.interval sourceTerm :=
  Term.isStronglyNormalizing.of_raw_progress_closure sourceTerm closure

/-- **K12.20.U2 universe arm**. -/
theorem Reducible.universe_of_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {universeLevel : UniverseLevel}
    {levelLe : universeLevel.toNat + 1 ≤ level}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.universe universeLevel levelLe) sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Reducible (Ty.universe universeLevel levelLe) sourceTerm :=
  Term.isStronglyNormalizing.of_raw_progress_closure sourceTerm closure

/-- **K12.20.U2 tyVar arm**. -/
theorem Reducible.tyVar_of_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {tyVarPosition : Fin scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context (Ty.tyVar tyVarPosition) sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Reducible (Ty.tyVar tyVarPosition) sourceTerm :=
  Term.isStronglyNormalizing.of_raw_progress_closure sourceTerm closure

/-- **K12.20.U2 session arm**. -/
theorem Reducible.session_of_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {protocolStep : RawTerm scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context (Ty.session protocolStep) sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Reducible (Ty.session protocolStep) sourceTerm :=
  Term.isStronglyNormalizing.of_raw_progress_closure sourceTerm closure

/-- **K12.20.U2 effect arm**. -/
theorem Reducible.effect_of_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {effectTag : RawTerm scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context (Ty.effect carrierType effectTag) sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Reducible (Ty.effect carrierType effectTag) sourceTerm :=
  Term.isStronglyNormalizing.of_raw_progress_closure sourceTerm closure

/-- **K12.20.U2 modal arm**. -/
theorem Reducible.modal_of_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {modalityTag : Nat}
    {carrierType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context (Ty.modal modalityTag carrierType) sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Reducible (Ty.modal modalityTag carrierType) sourceTerm :=
  Term.isStronglyNormalizing.of_raw_progress_closure sourceTerm closure

/-! ### K12.20.AZ compound varShape — SN-only-closure compound types

Four compound-Ty `_of_varShape` lemmas where Reducible's closure
clause demands only SN of the eliminator result (not full
Reducible).  These extend K12.20.E's SN-direct batch with the
SN-only-closure compound arms — dependent Π, HoTT identity,
observational equality, strict identity — each discharged by ONE
Stage 1 neutral-head SN helper.  Compound arms with
Reducible-on-sub-Ty closures (arrow / sigmaTy / listType /
optionType / eitherType / path / glue / equiv / refine / record)
require induction-on-Ty and ship later in K12.20.BA+. -/

/-- **K12.20.U2 arrow varShape arm**: variables are reducible at
function type once the codomain CR3 step is available.

This is the binder-lift entry point for the arrow candidate.  The
function variable itself is SN by `Term.isStronglyNormalizing_of_varShape`.
For the application closure, `app (var position) argumentRaw` is neutral;
the raw Stage-1 lemma `RawTerm.app_var_isStronglyNormalizing` supplies the
progress-closure needed by the codomain CR3 hook. -/
theorem Reducible.arrow_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.arrow domainType codomainType)
          (RawTerm.var position))
    (codomainCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context codomainType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible codomainType sourceTerm) :
    Reducible (Ty.arrow domainType codomainType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun {_argumentRaw} argumentTerm argumentIsReducible =>
     codomainCR3 (Term.app term argumentTerm)
       (RawTerm.IsNeutral.app (RawTerm.IsNeutral.var position))
       (fun _targetRaw progressStep =>
         RawTerm.isStronglyNormalizing.step_preserves
           (RawTerm.app_var_isStronglyNormalizing position
             (Reducible.isStronglyNormalizing argumentIsReducible))
           progressStep)⟩

/-- **K12.20.U2 arrow CR3 arm**: a neutral function is reducible at
`Ty.arrow domain codomain` when every raw progress reduct is SN and
the codomain CR3 hook is available.

The function itself is SN by the neutral progress-closure wrapper.
For an argument, `app neutral argument` is neutral and strongly
normalizing by `RawTerm.app_neutral_isStronglyNormalizing`; that SN
witness supplies the codomain CR3 hook's progress-closure premise. -/
theorem Reducible.arrow_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.arrow domainType codomainType) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw)
    (codomainCR3 :
      ∀ {codomainRaw : RawTerm scope}
        (codomainTerm : Term context codomainType codomainRaw),
        RawTerm.IsNeutral codomainRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress codomainRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible codomainType codomainTerm) :
    Reducible (Ty.arrow domainType codomainType) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro argumentRaw argumentTerm argumentIsReducible
  have appIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.app sourceRaw argumentRaw) :=
    RawTerm.app_neutral_isStronglyNormalizing
      sourceIsNeutral
      sourceIsSN
      (Reducible.isStronglyNormalizing argumentIsReducible)
  exact codomainCR3 (Term.app sourceTerm argumentTerm)
    (RawTerm.IsNeutral.app sourceIsNeutral)
    (fun _targetRaw progressStep =>
      RawTerm.isStronglyNormalizing.step_preserves appIsSN progressStep)

/-- **K12.20.U2 sigmaTy varShape arm**: variables are reducible at
dependent-pair type once the first-projection CR3 step is available.

The sigma candidate demands SN of the pair-shaped term, full Reducible
for `fst`, and SN for `snd`.  The raw `fst_var` / `snd_var` lemmas
provide the neutral projection SN closures; the full first projection
is delegated to the recursive CR3 hook for `firstType`. -/
theorem Reducible.sigmaTy_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {position : Fin scope}
    (term :
        Term context (Ty.sigmaTy firstType secondType)
          (RawTerm.var position))
    (firstTypeCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context firstType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible firstType sourceTerm) :
    Reducible (Ty.sigmaTy firstType secondType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   firstTypeCR3 (Term.fst term)
     (RawTerm.IsNeutral.fst (RawTerm.IsNeutral.var position))
     (fun _targetRaw progressStep =>
       RawTerm.isStronglyNormalizing.step_preserves
         (RawTerm.fst_var_isStronglyNormalizing position) progressStep),
   RawTerm.snd_var_isStronglyNormalizing position⟩

/-- **K12.20.U2 sigmaTy CR3 arm**: a neutral dependent pair is
reducible at `Ty.sigmaTy firstType secondType` when every raw
progress reduct is SN and the first-projection CR3 hook is available.

This matches the asymmetric sigma candidate: SN for the pair itself,
full Reducible for `fst`, and SN for `snd`.  The second projection
remains SN-only by the current K12.7 closure shape. -/
theorem Reducible.sigmaTy_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.sigmaTy firstType secondType) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw)
    (firstTypeCR3 :
      ∀ {firstRaw : RawTerm scope}
        (firstTerm : Term context firstType firstRaw),
        RawTerm.IsNeutral firstRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress firstRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible firstType firstTerm) :
    Reducible (Ty.sigmaTy firstType secondType) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_, ?_⟩
  · have fstIsSN :
        RawTerm.isStronglyNormalizing (RawTerm.fst sourceRaw) :=
      RawTerm.fst_neutral_isStronglyNormalizing
        sourceIsNeutral sourceIsSN
    exact firstTypeCR3 (Term.fst sourceTerm)
      (RawTerm.IsNeutral.fst sourceIsNeutral)
      (fun _targetRaw progressStep =>
        RawTerm.isStronglyNormalizing.step_preserves fstIsSN progressStep)
  · exact RawTerm.snd_neutral_isStronglyNormalizing
      sourceIsNeutral sourceIsSN

/-- **K12.20.U2 path varShape arm**: variables are reducible at cubical
path type once carrier CR3 is available.

The path candidate's eliminator closure returns full Reducible at the
carrier type.  `pathApp (var position) interval` is neutral, and the
existing raw helper supplies the progress-closure SN needed by the
carrier CR3 hook. -/
theorem Reducible.path_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {position : Fin scope}
    (term :
        Term context (Ty.path carrierType leftEndpoint rightEndpoint)
          (RawTerm.var position))
    (carrierCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context carrierType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible carrierType sourceTerm) :
    Reducible (Ty.path carrierType leftEndpoint rightEndpoint) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun modeIsUnivalent {_intervalRaw} intervalTerm intervalIsSN =>
     carrierCR3 (Term.pathApp modeIsUnivalent term intervalTerm)
       (RawTerm.IsNeutral.pathApp (RawTerm.IsNeutral.var position))
       (fun _targetRaw progressStep =>
         RawTerm.isStronglyNormalizing.step_preserves
           (RawTerm.pathApp_var_isStronglyNormalizing position intervalIsSN)
           progressStep)⟩

/-- **K12.20.U2 path CR3 arm**: a neutral path is reducible at
`Ty.path carrierType leftEndpoint rightEndpoint` when every raw
progress reduct is SN and the carrier CR3 hook is available.

The path candidate's output closure is full Reducible at the carrier
type.  The interval argument remains SN-only, matching the current
K12.12 closure where `Ty.interval` is a closed leaf rather than a
structural sub-Ty of the path type. -/
theorem Reducible.path_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw)
    (carrierCR3 :
      ∀ {carrierRaw : RawTerm scope}
        (carrierTerm : Term context carrierType carrierRaw),
        RawTerm.IsNeutral carrierRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress carrierRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible carrierType carrierTerm) :
    Reducible
      (Ty.path carrierType leftEndpoint rightEndpoint) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro modeIsUnivalent intervalRaw intervalTerm intervalIsSN
  have pathAppIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.pathApp sourceRaw intervalRaw) :=
    RawTerm.pathApp_neutral_isStronglyNormalizing
      sourceIsNeutral sourceIsSN intervalIsSN
  exact carrierCR3
    (Term.pathApp modeIsUnivalent sourceTerm intervalTerm)
    (RawTerm.IsNeutral.pathApp sourceIsNeutral)
    (fun _targetRaw progressStep =>
      RawTerm.isStronglyNormalizing.step_preserves pathAppIsSN progressStep)

/-- **K12.20.U2 glue CR3 arm**: a neutral glued value is reducible at
`Ty.glue baseType boundaryWitness` when every raw progress reduct is
SN and the base-type CR3 hook is available.

The Glue candidate demands full Reducible at the base type for
`glueElim`.  Since `baseType` is a strict sub-Ty of the Glue type,
the proof delegates that projection result to the recursive CR3 hook;
`RawTerm.glueElim_neutral_isStronglyNormalizing` supplies the raw
progress-closure SN premise for the neutral projection. -/
theorem Reducible.glue_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.glue baseType boundaryWitness) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw)
    (baseTypeCR3 :
      ∀ {baseRaw : RawTerm scope}
        (baseTerm : Term context baseType baseRaw),
        RawTerm.IsNeutral baseRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress baseRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible baseType baseTerm) :
    Reducible (Ty.glue baseType boundaryWitness) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro modeIsUnivalent
  have glueElimIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.glueElim sourceRaw) :=
    RawTerm.glueElim_neutral_isStronglyNormalizing
      sourceIsNeutral sourceIsSN
  exact baseTypeCR3
    (Term.glueElim modeIsUnivalent sourceTerm)
    (RawTerm.IsNeutral.glueElim sourceIsNeutral)
    (fun _targetRaw progressStep =>
      RawTerm.isStronglyNormalizing.step_preserves glueElimIsSN progressStep)

/-- **K12.20.U2 glue varShape arm**: variables are reducible at Glue
type once base-type CR3 is available. -/
theorem Reducible.glue_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {position : Fin scope}
    (term :
        Term context (Ty.glue baseType boundaryWitness)
          (RawTerm.var position))
    (baseTypeCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context baseType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible baseType sourceTerm) :
    Reducible (Ty.glue baseType boundaryWitness) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun modeIsUnivalent =>
     baseTypeCR3 (Term.glueElim modeIsUnivalent term)
       (RawTerm.IsNeutral.glueElim (RawTerm.IsNeutral.var position))
       (fun _targetRaw progressStep =>
         RawTerm.isStronglyNormalizing.step_preserves
           (RawTerm.glueElim_var_isStronglyNormalizing position)
           progressStep)⟩

/-- **K12.20.U2 equiv varShape arm**: variables are reducible at
equivalence type once codomain CR3 is available. -/
theorem Reducible.equiv_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.equiv carrierA carrierB)
          (RawTerm.var position))
    (carrierBCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context carrierB sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible carrierB sourceTerm) :
    Reducible (Ty.equiv carrierA carrierB) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun {_argumentRaw} argumentTerm argumentIsReducible =>
     carrierBCR3 (Term.equivApp term argumentTerm)
       (RawTerm.IsNeutral.equivApp (RawTerm.IsNeutral.var position))
       (fun _targetRaw progressStep =>
         RawTerm.isStronglyNormalizing.step_preserves
           (RawTerm.equivApp_var_isStronglyNormalizing position
             (Reducible.isStronglyNormalizing argumentIsReducible))
           progressStep)⟩

/-- **K12.20.U2 refine varShape arm**: variables are reducible at
refinement type once base-type CR3 is available. -/
theorem Reducible.refine_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {position : Fin scope}
    (term :
        Term context (Ty.refine baseType predicate)
          (RawTerm.var position))
    (baseTypeCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context baseType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible baseType sourceTerm) :
    Reducible (Ty.refine baseType predicate) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   baseTypeCR3 (Term.refineElim term)
     (RawTerm.IsNeutral.refineElim (RawTerm.IsNeutral.var position))
     (fun _targetRaw progressStep =>
       RawTerm.isStronglyNormalizing.step_preserves
         (RawTerm.refineElim_var_isStronglyNormalizing position)
         progressStep)⟩

/-- **K12.20.U2 record varShape arm**: variables are reducible at
single-field record type once field-type CR3 is available. -/
theorem Reducible.record_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.record singleFieldType)
          (RawTerm.var position))
    (singleFieldTypeCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context singleFieldType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible singleFieldType sourceTerm) :
    Reducible (Ty.record singleFieldType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   singleFieldTypeCR3 (Term.recordProj term)
     (RawTerm.IsNeutral.recordProj (RawTerm.IsNeutral.var position))
     (fun _targetRaw progressStep =>
       RawTerm.isStronglyNormalizing.step_preserves
         (RawTerm.recordProj_var_isStronglyNormalizing position)
         progressStep)⟩

/-- **K12.20.U2 codata varShape arm**: variables are reducible at
codata type once output-type CR3 is available. -/
theorem Reducible.codata_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.codata stateType outputType)
          (RawTerm.var position))
    (outputTypeCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context outputType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible outputType sourceTerm) :
    Reducible (Ty.codata stateType outputType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   outputTypeCR3 (Term.codataDest term)
     (RawTerm.IsNeutral.codataDest (RawTerm.IsNeutral.var position))
     (fun _targetRaw progressStep =>
       RawTerm.isStronglyNormalizing.step_preserves
         (RawTerm.codataDest_var_isStronglyNormalizing position)
         progressStep)⟩

/-- **K12.20.U2 listType varShape arm**: variables are reducible at
list type.

The strengthened K12.8 list closure includes SN for both eliminator
branches.  That is exactly what the raw neutral-list eliminator helper
needs for `listElim (var position) nilBranch consBranch`; the branch
application hypothesis remains available for canonical cons ι-cases but
is not needed for the stuck-variable case. -/
theorem Reducible.listType_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.listType elementType)
          (RawTerm.var position)) :
    Reducible (Ty.listType elementType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun {_motiveType} {_nilRaw} {_consRaw}
       _nilBranch _consBranch nilIsSN consIsSN _consApplied =>
     RawTerm.listElim_var_isStronglyNormalizing position nilIsSN consIsSN⟩

/-- **K12.20.U2 optionType varShape arm**: variables are reducible at
option type.

The some-branch SN premise is load-bearing for neutral scrutinees:
`optionMatch` can reduce the some branch by congruence even when the
scrutinee is stuck at a variable. -/
theorem Reducible.optionType_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.optionType elementType)
          (RawTerm.var position)) :
    Reducible (Ty.optionType elementType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun {_motiveType} {_noneRaw} {_someRaw}
       _noneBranch _someBranch noneIsSN someIsSN _someApplied =>
     RawTerm.optionMatch_var_isStronglyNormalizing position noneIsSN someIsSN⟩

/-- **K12.20.U2 eitherType varShape arm**: variables are reducible at
either type.

Both branches must be SN because `eitherMatch` reduces both branch
positions by congruence under a stuck variable scrutinee. -/
theorem Reducible.eitherType_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.eitherType leftType rightType)
          (RawTerm.var position)) :
    Reducible (Ty.eitherType leftType rightType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun {_motiveType} {_leftRaw} {_rightRaw}
       _leftBranch _rightBranch leftIsSN rightIsSN
       _leftApplied _rightApplied =>
     RawTerm.eitherMatch_var_isStronglyNormalizing position
       leftIsSN rightIsSN⟩

/-- **K12.20.AZ.1 piTy arm**: variables are reducible at the
dependent-Π type.  Closure: SN(var) + ∀ argTerm, Reducible
domainType argTerm → SN(Term.appPi (var) argTerm).  The second
clause reduces (via Reducible.isStronglyNormalizing CR1) to
SN(argRaw), then Stage 1's `RawTerm.app_var_isStronglyNormalizing`
closes — Term.appPi's raw form is `RawTerm.app functionRaw
argumentRaw`, matching app_var's signature. -/
theorem Reducible.piTy_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {position : Fin scope}
    (term :
        Term context (Ty.piTy domainType codomainType)
          (RawTerm.var position)) :
    Reducible (Ty.piTy domainType codomainType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun {_argRaw} _argTerm argIsReducible =>
     RawTerm.app_var_isStronglyNormalizing position
       (Reducible.isStronglyNormalizing argIsReducible)⟩

/-- **K12.20.AZ.2 id arm**: variables are reducible at the HoTT
propositional identity type.  Closure: SN(var) + ∀ baseCase,
SN(baseCase) → SN(Term.idJ baseCase var).  Stage 1's
`RawTerm.idJ_var_isStronglyNormalizing` discharges directly —
Term.idJ's raw form is `RawTerm.idJ baseRaw witnessRaw` with var
in the witness slot. -/
theorem Reducible.id_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {position : Fin scope}
    (witness :
        Term context (Ty.id carrier leftEndpoint rightEndpoint)
          (RawTerm.var position)) :
    Reducible (Ty.id carrier leftEndpoint rightEndpoint) witness :=
  ⟨Term.isStronglyNormalizing_of_varShape witness,
   fun {_motiveType} {_baseRaw} _baseCase baseIsSN =>
     RawTerm.idJ_var_isStronglyNormalizing position baseIsSN⟩

/-- **K12.20.AZ.3 oeq arm**: variables are reducible at the
observational equality type.  Closure: SN(var) + ∀ baseCase,
SN(baseCase) → SN(Term.oeqJ baseCase var).  Discharged by Stage 1's
`RawTerm.oeqJ_var_isStronglyNormalizing` (cong-only inversion;
oeq-ι deferred at raw layer).  Same shape as `id_of_varShape`. -/
theorem Reducible.oeq_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {position : Fin scope}
    (witness :
        Term context (Ty.oeq carrier leftEndpoint rightEndpoint)
          (RawTerm.var position)) :
    Reducible (Ty.oeq carrier leftEndpoint rightEndpoint) witness :=
  ⟨Term.isStronglyNormalizing_of_varShape witness,
   fun {_motiveType} {_baseRaw} _baseCase baseIsSN =>
     RawTerm.oeqJ_var_isStronglyNormalizing position baseIsSN⟩

/-- **K12.20.AZ.4 idStrict arm**: variables are reducible at the
strict identity type.  Closure: SN(var) + ∀ (modeIsStrict : mode =
Mode.strict) baseCase, SN(baseCase) → SN(Term.idStrictRec
modeIsStrict baseCase var).  Discharged by Stage 1's
`RawTerm.idStrictRec_var_isStronglyNormalizing`; the typed mode
witness is universally quantified and consumed silently — the raw
form drops it. -/
theorem Reducible.idStrict_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {position : Fin scope}
    (witness :
        Term context (Ty.idStrict carrier leftEndpoint rightEndpoint)
          (RawTerm.var position)) :
    Reducible (Ty.idStrict carrier leftEndpoint rightEndpoint) witness :=
  ⟨Term.isStronglyNormalizing_of_varShape witness,
   fun (_modeIsStrict : mode = Mode.strict)
       {_motiveType} {_baseRaw} _baseCase baseIsSN =>
     RawTerm.idStrictRec_var_isStronglyNormalizing position baseIsSN⟩

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
    SN(nilBranch) → SN(consBranch) →
    (∀ head tail, Reducible A head → SN(tail) →
                  SN(consBranch head tail)) →
    SN(listElim xs nilBranch consBranch)
```

The branch-SN and application-closure hypotheses are propagated
unchanged by sourceReducible.2 — CR2 needs NO recursive
elementTypeCR2 hypothesis because the eliminator output is plain SN,
not Reducible.  Same weak-closure pattern as K12.20.G piTy and
K12.20.I id.

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
  · intro motiveType nilRaw consRaw nilBranch consBranch nilSN consSN consApplied
    have listElimStep : RawStep.parProgress
        (RawTerm.listElim sourceRaw nilRaw consRaw)
        (RawTerm.listElim targetRaw nilRaw consRaw) := by
      refine ⟨RawStep.par.listElim rawStep.1
          (RawStep.par.refl nilRaw) (RawStep.par.refl consRaw), ?_⟩
      intro listElimEq
      apply rawStep.2
      injection listElimEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 nilBranch consBranch nilSN consSN consApplied)
      listElimStep

/-! ## K12.20.K typed CR2 lift — Ty.optionType weak-elim-closure compound arm

Sixth compound-arm CR2 lemma.  `Ty.optionType` ships a **weak
elim closure** in K12.8, cleanest of the three K12.8 parametric
arms: someBranch's type matches K12.6 piTy weak shape exactly
when restricted to elementType.  Closure shape (per
Reducibility.lean:426):

```
Reducible (Ty.optionType A) o =
  SN(o) ∧ ∀ {M} {noneRaw someRaw} (noneBranch someBranch),
    SN(noneBranch) → SN(someBranch) →
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
  · intro motiveType noneRaw someRaw noneBranch someBranch noneSN someSN someApplied
    have optionMatchStep : RawStep.parProgress
        (RawTerm.optionMatch sourceRaw noneRaw someRaw)
        (RawTerm.optionMatch targetRaw noneRaw someRaw) := by
      refine ⟨RawStep.par.optionMatch rawStep.1
          (RawStep.par.refl noneRaw) (RawStep.par.refl someRaw), ?_⟩
      intro optionMatchEq
      apply rawStep.2
      injection optionMatchEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 noneBranch someBranch noneSN someSN someApplied)
      optionMatchStep

/-! ## K12.20.L typed CR2 lift — Ty.eitherType symmetric-weak-elim-closure compound arm

Seventh compound-arm CR2 lemma.  `Ty.eitherType` ships a
**symmetric weak elim closure** in K12.8: both `leftType` and
`rightType` are strict sub-Ty of `Ty.eitherType leftType
rightType`, so each branch's arrow shape matches K12.6 piTy weak
closure per side.  Closure shape (per Reducibility.lean:446):

```
Reducible (Ty.eitherType A B) e =
  SN(e) ∧ ∀ {M} {leftRaw rightRaw} (leftBranch rightBranch),
    SN(leftBranch) → SN(rightBranch) →
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
  · intro motiveType leftRaw rightRaw leftBranch rightBranch
      leftSN rightSN leftApplied rightApplied
    have eitherMatchStep : RawStep.parProgress
        (RawTerm.eitherMatch sourceRaw leftRaw rightRaw)
        (RawTerm.eitherMatch targetRaw leftRaw rightRaw) := by
      refine ⟨RawStep.par.eitherMatch rawStep.1
          (RawStep.par.refl leftRaw) (RawStep.par.refl rightRaw), ?_⟩
      intro eitherMatchEq
      apply rawStep.2
      injection eitherMatchEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 leftBranch rightBranch leftSN rightSN
        leftApplied rightApplied)
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

/-- **K12.20.AQ effectPerform fundamental case** — algebraic effect
operation invocation bundles an operation tag with arguments.
Both subterms have arbitrary-Ty payloads — operationTag at
`Ty.effect operationSignature.argumentCarrier effectTag` (SN-direct
per Reducibility.lean:668 so operationIH IS SN); arguments at
the arbitrary `operationSignature.argumentCarrier` (needs SN
extraction via `Reducible.isStronglyNormalizing` per K12.20.AP.2).
Result type `Ty.effect resultCarrier effectTag` after subst is
also SN-direct.  The K12.20.AL.3 binary SN helper closes the
proof in one line. -/
theorem Reducible.fundamental_effectPerform
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (effectTag : RawTerm scope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level scope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm scope}
    {operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw}
    {arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw}
    (operationIH :
      Reducible
        ((Ty.effect operationSignature.argumentCarrier effectTag).subst sigma)
        (Term.subst termSubst operationTag))
    (argumentsIH :
      Reducible (operationSignature.argumentCarrier.subst sigma)
                (Term.subst termSubst arguments)) :
    Reducible
      ((Ty.effect operationSignature.resultCarrier effectTag).subst sigma)
      (Term.subst termSubst
        (Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationTag arguments)) :=
  RawTerm.effectPerform_isStronglyNormalizing operationIH
    (Reducible.isStronglyNormalizing argumentsIH)

/-- **K12.20.AR.3 universeCode fundamental case** — universe-code
nullary intro at outer level.  Output `Ty.universe outerLevel
levelLe` is SN-direct (Reducibility.lean:330); `Term.subst` on
universeCode is identity (`LeanFX2/Term/Subst.lean:379-380`);
`Reducible Ty.universe _` unfolds to `Term.isStronglyNormalizing
_`.  Direct lift via the K12.20.AR.2 SN helper. -/
theorem Reducible.fundamental_universeCode
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.universeCode (context := sourceCtx)
                  innerLevel outerLevel cumulOk levelLe)) :=
  RawTerm.universeCode_isStronglyNormalizing innerLevel.toNat

/-- **K12.20.BB.1 cumulUpMarker SN preservation** — CUMUL-2.6 cong
helper at the raw layer.  Sister to `subsume_isStronglyNormalizing`
(K12.20.AB) and `modIntro_isStronglyNormalizing` (K12.20.Y) — unary
cong-only ctor; `RawStep.par.cumulUpMarkerCong` is the only non-refl
rule with `cumulUpMarker _` as source.  Powers `fundamental_cumulUp`
at the typed cross-universe cumulativity ctor. -/
theorem RawTerm.cumulUpMarker_isStronglyNormalizing {scope : Nat}
    {innerCodeRaw : RawTerm scope}
    (innerIsSN : RawTerm.isStronglyNormalizing innerCodeRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.cumulUpMarker innerCodeRaw) := by
  induction innerIsSN with
  | intro currentInner _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.cumulUpMarker currentInner) ?_
    intro target progressStep
    obtain ⟨innerTarget, targetEq, innerStep⟩ :=
      RawStep.par.cumulUpMarker_inv progressStep.1
    subst targetEq
    have innerDistinct :
        currentInner ≠ innerTarget := fun innerEq =>
      progressStep.2 (congrArg RawTerm.cumulUpMarker innerEq)
    exact inductiveHypothesis innerTarget
      ⟨innerStep, innerDistinct⟩

/-- **K12.20.BB.2 cumulUp fundamental case** — REAL cross-universe
cumulativity at the typed Term level (Phase CUMUL-2.6 Design D).
Source `Ty.universe lowerLevel levelLeLow` is SN-direct; output
`Ty.universe higherLevel levelLeHigh` is also SN-direct (per
`Reducibility.lean:330`).  `Term.subst` on `Term.cumulUp` reconstructs
the cumulUp ctor at the target scope with the recursively-substituted
inner typeCode (per `LeanFX2/Term/Subst.lean:388-393`); the typed
raw form is `RawTerm.cumulUpMarker (codeRaw.subst sigma.forRaw)`.
The `innerIH` is SN of the substituted inner; the K12.20.BB.1
cumulUpMarker SN helper closes the proof. -/
theorem Reducible.fundamental_cumulUp
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    {typeCode :
        Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw}
    (innerIH :
        Reducible ((Ty.universe lowerLevel levelLeLow).subst sigma)
                  (Term.subst termSubst typeCode)) :
    Reducible ((Ty.universe higherLevel levelLeHigh).subst sigma)
              (Term.subst termSubst
                (Term.cumulUp lowerLevel higherLevel
                              cumulMonotone levelLeLow levelLeHigh
                              typeCode)) :=
  RawTerm.cumulUpMarker_isStronglyNormalizing innerIH

/-! ## K12.20.BC SN-direct fundamental cases for `Term.subsume`

`Term.subsume` is the Layer 1 modal-cumulativity coercion: a
type-preserving wrapper `Term ctx innerType innerRaw → Term ctx
innerType (RawTerm.subsume innerRaw)`.  Its `Term.subst` commute
is definitional (`LeanFX2/Term/Subst.lean:303-304` — substitution
distributes componentwise over the wrapper).

For SN-direct `innerType` arms — those where `Reducible ty term`
unfolds to `Term.isStronglyNormalizing term` (i.e. unit / bool /
nat / empty / interval / universe / session / effect / modal —
all closed-leaf or raw-payload-shaped) — the fundamental case
ships as a one-line composition of the K12.20.AB raw SN helper
with the `innerIH`.  No per-Ty case analysis is needed because
the substituted innerType retains its SN-direct shape under
`Ty.subst`.

This batch covers four representative SN-direct arms (unit,
universe, session, modal) spanning closed-leaf / level-
parameterized / raw-payload-carrying / K12.25-modal targets.
The remaining SN-direct arms (bool / nat / empty / interval /
effect) follow the identical 1-line pattern and ship in a
future K12.20.BD tick when the modIntro companion cases land.

Compound-Ty `innerType` arms (arrow / sigmaTy / listType / etc.)
are NOT covered here — those require the full
`Reducible.subsume_intro` framework with case analysis on the
substituted Ty and step-closure under elimination forms.  Such
arms ship at K12.25 alongside the full modal-cases milestone. -/

/-- **K12.20.BC.1 subsume fundamental case at `Ty.unit`** —
canonical SN-direct closed-leaf coverage.  Layer 1
type-preserving wrapper at the unit type.  `(Ty.unit).subst
sigma = Ty.unit` (`Foundation/Subst.lean:102` — definitional);
`Reducible Ty.unit term = Term.isStronglyNormalizing term`
(`Reducibility.lean:325`); `Term.subst termSubst (Term.subsume
inner) = Term.subsume (Term.subst termSubst inner)`
(`Term/Subst.lean:303-304` — definitional).  The K12.20.AB
`RawTerm.subsume_isStronglyNormalizing` lifts SN of the inner
to SN of the wrapped form in one composition. -/
theorem Reducible.fundamental_subsume_at_unit
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.unit innerRaw}
    (innerIH : Reducible ((Ty.unit : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.unit : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- **K12.20.BC.2 subsume fundamental case at `Ty.universe`** —
SN-direct level-parameterized coverage.  `(Ty.universe lvl
levelLe).subst sigma = Ty.universe lvl levelLe`
(`Foundation/Subst.lean:123` — definitional, sigma doesn't see
the level parameter); the SN-direct invariant carries through
the level parameter identically to the closed-leaf case.  Same
single-line composition as the unit case. -/
theorem Reducible.fundamental_subsume_at_universe
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.universe outerLevel levelLe) innerRaw}
    (innerIH :
        Reducible ((Ty.universe outerLevel levelLe).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- **K12.20.BC.3 subsume fundamental case at `Ty.session`** —
SN-direct raw-payload coverage.  `(Ty.session protocolStep).subst
sigma = Ty.session (protocolStep.subst sigma.forRaw)`
(`Foundation/Subst.lean:150-151`) — substitution recurses on
the raw payload via `sigma.forRaw`, but the outer `Ty.session`
constructor is preserved, so the resulting Ty is still
SN-direct (`Reducibility.lean:588-589`).  Same one-line
composition as the closed-leaf case; the raw-payload
substitution lives transparently inside `innerIH`'s type. -/
theorem Reducible.fundamental_subsume_at_session
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {protocolStep : RawTerm scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx (Ty.session protocolStep) innerRaw}
    (innerIH :
        Reducible ((Ty.session protocolStep).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.session protocolStep).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- **K12.20.BC.4 subsume fundamental case at `Ty.modal`** —
SN-direct modal coverage (K12.25 milestone target).
`(Ty.modal modalityTag carrierType).subst sigma = Ty.modal
modalityTag (carrierType.subst sigma)`
(`Foundation/Subst.lean:154-155`) — substitution recurses on
the carrier Ty but preserves the outer `Ty.modal` constructor,
keeping the SN-direct invariant.  Per Layer 1 modal scaffolding
(`Reducibility.lean:604-627`), no Term ctor currently inhabits
`Ty.modal _ _`, but the `Reducible` arm is shipped for
forward-compat with Layer 6 typed `modIntroCross` / `modElimCross`
(CUMUL-7.1.{1,2}, #1689-1691); when those land,
`fundamental_subsume_at_modal` is the unchanged single-line
modal-subsume case. -/
theorem Reducible.fundamental_subsume_at_modal
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modalityTag : Nat) {carrierType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.modal modalityTag carrierType) innerRaw}
    (innerIH :
        Reducible ((Ty.modal modalityTag carrierType).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.modal modalityTag carrierType).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-! ## K12.20.BD SN-direct fundamental cases for `Term.modIntro`

`Term.modIntro` is the Layer 1 modal-introduction wrapper —
sister to `Term.subsume`, with identical type-preserving
structure: `Term ctx innerType innerRaw → Term ctx innerType
(RawTerm.modIntro innerRaw)`.  `Term.subst` commute is
definitional (`LeanFX2/Term/Subst.lean:299-300`).

Per Layer 1 modal scaffolding (`Reducibility.lean:604-627` +
`Term.lean:295-300`), modIntro preserves innerType rather than
producing `Ty.modal _ innerType`; Layer 6 will refactor to take
a Modality and produce `Ty.modal modality innerType` via the
CUMUL-7.1.{1,2} `modIntroCross` / `modElimCross` ctors
(#1689-1691).  This batch covers the Layer 1 SN-direct
fragment; the per-modality Tait closure ships at K12.25
alongside Layer 6's typed modIntroCross.

Four representative SN-direct arms mirroring K12.20.BC's
subsume quartet (unit / universe / session / modal — closed-
leaf / level-parameterized / raw-payload-carrying / K12.25
modal target).  Each ships as a 1-line composition of the
K12.20.Y `RawTerm.modIntro_isStronglyNormalizing` helper with
the `innerIH`. -/

/-- **K12.20.BD.1 modIntro fundamental case at `Ty.unit`** —
Layer 1 modal-introduction wrapper at the unit type.
`(Ty.unit).subst sigma = Ty.unit` (definitional); `Reducible
Ty.unit term = Term.isStronglyNormalizing term` (def-unfold);
`Term.subst termSubst (Term.modIntro inner) = Term.modIntro
(Term.subst termSubst inner)` (`Term/Subst.lean:299-300` —
definitional).  K12.20.Y `RawTerm.modIntro_isStronglyNormalizing`
lifts SN of the inner to SN of the wrapped form. -/
theorem Reducible.fundamental_modIntro_at_unit
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.unit innerRaw}
    (innerIH : Reducible ((Ty.unit : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.unit : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- **K12.20.BD.2 modIntro fundamental case at `Ty.universe`** —
SN-direct level-parameterized.  `(Ty.universe outerLevel
levelLe).subst sigma = Ty.universe outerLevel levelLe`
(`Foundation/Subst.lean:123`) — substitution doesn't touch the
level parameter.  Same 1-line composition as the unit case. -/
theorem Reducible.fundamental_modIntro_at_universe
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.universe outerLevel levelLe) innerRaw}
    (innerIH :
        Reducible ((Ty.universe outerLevel levelLe).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- **K12.20.BD.3 modIntro fundamental case at `Ty.session`** —
SN-direct raw-payload-carrying.  `(Ty.session protocolStep).subst
sigma = Ty.session (protocolStep.subst sigma.forRaw)`
(`Foundation/Subst.lean:150-151`) — the outer `Ty.session`
constructor is preserved under subst, keeping the SN-direct
invariant.  The raw-payload substitution lives inside
innerIH's type. -/
theorem Reducible.fundamental_modIntro_at_session
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {protocolStep : RawTerm scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx (Ty.session protocolStep) innerRaw}
    (innerIH :
        Reducible ((Ty.session protocolStep).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.session protocolStep).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- **K12.20.BD.4 modIntro fundamental case at `Ty.modal`** —
SN-direct modal (K12.25 milestone target).  `(Ty.modal
modalityTag carrierType).subst sigma = Ty.modal modalityTag
(carrierType.subst sigma)` (`Foundation/Subst.lean:154-155`)
— the outer `Ty.modal` constructor is preserved, keeping the
SN-direct invariant.  Per Layer 1 scaffolding, no Term ctor
currently inhabits `Ty.modal _ _`; this case is shipped for
forward-compat with Layer 6's typed modIntroCross / modElimCross
(CUMUL-7.1.{1,2}, #1689-1691).  When those ctors land, this
single-line modal-modIntro case carries through unchanged. -/
theorem Reducible.fundamental_modIntro_at_modal
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modalityTag : Nat) {carrierType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.modal modalityTag carrierType) innerRaw}
    (innerIH :
        Reducible ((Ty.modal modalityTag carrierType).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.modal modalityTag carrierType).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-! ## K12.20.BE Remaining SN-direct fundamental cases — subsume / modIntro

Five additional SN-direct arms covering the closed-leaf and
raw-payload-carrying types not in K12.20.BC/BD's
representative quartet: `Ty.bool`, `Ty.nat`, `Ty.empty`,
`Ty.interval`, and `Ty.effect`.  All five preserve their outer
Ty constructor under substitution (`Foundation/Subst.lean:103,
104, 126, 127, 152-153` respectively), keeping the SN-direct
invariant per `Reducibility.lean:326-329, 602-603`.

Ten total cases (5 subsume + 5 modIntro) closing the SN-direct
fragment of `Reducible.fundamental_subsume` and
`fundamental_modIntro` at Layer 1.  Same single-line composition
pattern as K12.20.BC/BD: `RawTerm.{subsume,modIntro}_isStronglyNormalizing
innerIH`.

After K12.20.BE, the full SN-direct coverage matrix is:

| Ty           | subsume | modIntro |
| ------------ | ------- | -------- |
| unit         | BC.1    | BD.1     |
| bool         | BE.1    | BE.6     |
| nat          | BE.2    | BE.7     |
| empty        | BE.3    | BE.8     |
| interval     | BE.4    | BE.9     |
| universe     | BC.2    | BD.2     |
| session      | BC.3    | BD.3     |
| effect       | BE.5    | BE.10    |
| modal        | BC.4    | BD.4     |

`Ty.tyVar` is intentionally excluded: substitution maps
`tyVar position → sigma.forTy position` (`Foundation/Subst.lean:111-112`)
to an arbitrary Ty, breaking the SN-direct invariant.  The
tyVar case ships at K12.25 alongside the compound-Ty machinery.

Compound-Ty innerType arms (arrow / sigmaTy / listType /
optionType / eitherType / id / oeq / idStrict / path / glue /
equiv / refine / record / codata / piTy) require the full
`Reducible.subsume_intro` / `Reducible.modIntro_intro`
framework with case analysis on the substituted Ty and step-
closure under elimination forms — those ship at K12.25. -/

/-- **K12.20.BE.1 subsume at `Ty.bool`** — SN-direct closed-leaf.
`(Ty.bool).subst sigma = .bool` (`Foundation/Subst.lean:103`). -/
theorem Reducible.fundamental_subsume_at_bool
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.bool innerRaw}
    (innerIH : Reducible ((Ty.bool : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.bool : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- **K12.20.BE.2 subsume at `Ty.nat`** — SN-direct closed-leaf.
`(Ty.nat).subst sigma = .nat` (`Foundation/Subst.lean:104`). -/
theorem Reducible.fundamental_subsume_at_nat
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.nat innerRaw}
    (innerIH : Reducible ((Ty.nat : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.nat : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- **K12.20.BE.3 subsume at `Ty.empty`** — SN-direct closed-leaf.
`(Ty.empty).subst sigma = .empty` (`Foundation/Subst.lean:126`). -/
theorem Reducible.fundamental_subsume_at_empty
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.empty innerRaw}
    (innerIH : Reducible ((Ty.empty : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.empty : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- **K12.20.BE.4 subsume at `Ty.interval`** — SN-direct cubical
closed-leaf.  `(Ty.interval).subst sigma = .interval`
(`Foundation/Subst.lean:127`). -/
theorem Reducible.fundamental_subsume_at_interval
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.interval innerRaw}
    (innerIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.interval : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- **K12.20.BE.5 subsume at `Ty.effect`** — SN-direct
raw-payload-carrying.  `(Ty.effect carrier tag).subst sigma =
.effect (carrier.subst sigma) (tag.subst sigma.forRaw)`
(`Foundation/Subst.lean:152-153`) — the outer `Ty.effect`
constructor is preserved.  Sister to K12.20.BC.3 session. -/
theorem Reducible.fundamental_subsume_at_effect
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierType : Ty level scope}
    {effectTag : RawTerm scope}
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.effect carrierType effectTag) innerRaw}
    (innerIH :
        Reducible ((Ty.effect carrierType effectTag).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.effect carrierType effectTag).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- **K12.20.BE.6 modIntro at `Ty.bool`** — sister to BE.1 via
K12.20.Y `RawTerm.modIntro_isStronglyNormalizing`. -/
theorem Reducible.fundamental_modIntro_at_bool
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.bool innerRaw}
    (innerIH : Reducible ((Ty.bool : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.bool : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- **K12.20.BE.7 modIntro at `Ty.nat`** — sister to BE.2. -/
theorem Reducible.fundamental_modIntro_at_nat
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.nat innerRaw}
    (innerIH : Reducible ((Ty.nat : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.nat : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- **K12.20.BE.8 modIntro at `Ty.empty`** — sister to BE.3. -/
theorem Reducible.fundamental_modIntro_at_empty
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.empty innerRaw}
    (innerIH : Reducible ((Ty.empty : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.empty : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- **K12.20.BE.9 modIntro at `Ty.interval`** — sister to BE.4. -/
theorem Reducible.fundamental_modIntro_at_interval
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.interval innerRaw}
    (innerIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.interval : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- **K12.20.BE.10 modIntro at `Ty.effect`** — sister to BE.5. -/
theorem Reducible.fundamental_modIntro_at_effect
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierType : Ty level scope}
    {effectTag : RawTerm scope}
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.effect carrierType effectTag) innerRaw}
    (innerIH :
        Reducible ((Ty.effect carrierType effectTag).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.effect carrierType effectTag).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-! ## K12.21.A fundamental_app at `Ty.arrow` — β-redex elimination
case at the homogeneous (non-dependent) arrow type

First entry of the K12.21 β-redex fundamental-case batch (#1778).
`Term.app : Term ctx (Ty.arrow A B) fnRaw → Term ctx A argRaw →
Term ctx B (RawTerm.app fnRaw argRaw)` is the non-dependent
function-application elimination form.

The proof is a single composition of three definitional facts:

1.  `(Ty.arrow A B).subst sigma = Ty.arrow (A.subst sigma)
    (B.subst sigma)`  (`Foundation/Subst.lean:105-106`)
2.  `Reducible (Ty.arrow A' B') f = SN(f) ∧ ∀ argTerm, Reducible
    A' argTerm → Reducible B' (Term.app f argTerm)`  (K12.5, see
    `Reducibility.lean:333-338`)
3.  `Term.subst termSubst (Term.app fn arg) = Term.app
    (Term.subst termSubst fn) (Term.subst termSubst arg)`
    (`Term/Subst.lean:199-200`)

Composing: `functionIH.2 (Term.subst termSubst argumentTerm)
argumentIH` projects the second component of the arrow-closure
witness from the function's IH, applied to the substituted
argument and its argument-IH.  The result has the goal type
modulo the three definitional reductions above. -/

/-- **K12.21.A fundamental_app at `Ty.arrow`** — non-dependent
β-redex elimination.  Direct projection of the arrow's
Reducible-closure (K12.5 second conjunct) applied to the
substituted argument.

This is the strongest fundamental case shipped so far: it
exercises the FULL Tait reducibility framework (not just SN
preservation), proving that the codomain Reducible witness
follows by composing the function's arrow-closure with the
argument's reducibility witness. -/
theorem Reducible.fundamental_app_at_arrow
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm :
        Term sourceCtx (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionIH :
        Reducible ((Ty.arrow domainType codomainType).subst sigma)
                  (Term.subst termSubst functionTerm))
    (argumentIH :
        Reducible (domainType.subst sigma)
                  (Term.subst termSubst argumentTerm)) :
    Reducible (codomainType.subst sigma)
              (Term.subst termSubst
                (Term.app functionTerm argumentTerm)) :=
  functionIH.2 (Term.subst termSubst argumentTerm) argumentIH

/-! ## K12.21.B fundamental_fst at `Ty.sigmaTy` — Σ first-projection
elimination

Second entry of the K12.21 β-redex fundamental-case batch (#1778).
`Term.fst : Term ctx (Ty.sigmaTy A B) pairRaw → Term ctx A
(RawTerm.fst pairRaw)` projects the first component out of a
dependent pair.

The proof is a single triple-projection on the pair's reducibility
witness.  Three definitional facts compose:

1.  `(Ty.sigmaTy A B).subst sigma = Ty.sigmaTy (A.subst sigma)
    (B.subst sigma.lift)`  (`Foundation/Subst.lean:109-110`)
2.  `Reducible (Ty.sigmaTy A' B') pair = SN(pair) ∧ Reducible A'
    (Term.fst pair) ∧ SN(Term.snd pair)`  (K12.7 asymmetric
    closure, see `Reducibility.lean:367-370`)
3.  `Term.subst termSubst (Term.fst pairTerm) = Term.fst
    (Term.subst termSubst pairTerm)`  (`Term/Subst.lean:215`)

Body: `pairIH.2.1` extracts the middle conjunct (full Reducible
on the substituted firstType applied to the substituted pair's
first projection).

The sibling `fundamental_snd_at_sigmaTy` would extract `.2.2`
(SN of `Term.snd pair`) — but its goal type involves the
substituted-codomain wall `secondType.subst0 firstType
(RawTerm.fst pairRaw)`, which is not a strict sub-Ty of
`Ty.sigmaTy firstType secondType`.  Per K12.7's design, the
snd-projection closure is reserved for the Kripke logical-
relation refactor; the second projection ships at K12.21.snd
with the weak SN target rather than full Reducible. -/

/-- **K12.21.B fundamental_fst at `Ty.sigmaTy`** — Σ
first-projection elimination.  Direct extraction of the middle
conjunct from K12.7's asymmetric sigmaTy closure. -/
theorem Reducible.fundamental_fst_at_sigmaTy
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm :
        Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIH :
        Reducible ((Ty.sigmaTy firstType secondType).subst sigma)
                  (Term.subst termSubst pairTerm)) :
    Reducible (firstType.subst sigma)
              (Term.subst termSubst (Term.fst pairTerm)) :=
  pairIH.2.1

/-! ## K12.21.C fundamental_snd at `Ty.sigmaTy` — Σ second-projection
weak-SN case

Third entry of the K12.21 β-redex fundamental-case batch (#1778).
`Term.snd : Term ctx (Ty.sigmaTy A B) pairRaw → Term ctx (B.subst0
A (RawTerm.fst pairRaw)) (RawTerm.snd pairRaw)` projects the
second component of a dependent pair.

Asymmetry with K12.21.B: the sigmaTy second-projection target type
`secondType.subst0 firstType (RawTerm.fst pairRaw)` is NOT a
strict sub-Ty of `Ty.sigmaTy firstType secondType` — structural
recursion on Ty cannot inspect it without the Kripke logical-
relation refactor.  Per K12.7's asymmetric closure design
(`Reducibility.lean:367-370`), the snd-projection closure ships
only as **SN of the snd term**, not full Reducible:

  Reducible (Ty.sigmaTy A' B') pair = SN(pair)
                                    ∧ Reducible A' (Term.fst pair)
                                    ∧ SN(Term.snd pair)

This fundamental case ships at the weak-SN level matching K12.7.
Three definitional facts compose:

1.  `(Ty.sigmaTy A B).subst sigma = Ty.sigmaTy (A.subst sigma)
    (B.subst sigma.lift)`  (`Foundation/Subst.lean:109-110`)
2.  K12.7's third conjunct gives SN of Term.snd directly
3.  `Term.isStronglyNormalizing` reads only the raw index
    (`Reducibility.lean:303-307`) — the Ty.subst0_subst_commute
    cast on `Term.subst termSubst (Term.snd ...)` (`Term/Subst.lean:
    217-221`) is irrelevant because both cast and un-cast forms
    share the same RawTerm.snd raw projection.

Body: `pairIH.2.2` extracts the third conjunct (the SN witness on
the snd projection).

When secondType.subst0 is itself SN-direct (e.g. when secondType
is a non-dependent variant `B.weaken` of a closed-leaf type), the
weak SN result IS the full Reducible result.  When secondType is
compound, the lift to full Reducible waits for K12.25's modal
framework or the Kripke refactor. -/

/-- **K12.21.C fundamental_snd at `Ty.sigmaTy`** — weak-SN
case.  Direct extraction of the third conjunct from K12.7's
asymmetric sigmaTy closure; the substituted-codomain wall blocks
full-Reducible until the Kripke refactor.

The goal is **SN of the substituted Term.snd**, not Reducible —
matching K12.6/K12.7's documented design (`Reducibility.lean:339-352`).  -/
theorem Reducible.fundamental_snd_at_sigmaTy_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm :
        Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIH :
        Reducible ((Ty.sigmaTy firstType secondType).subst sigma)
                  (Term.subst termSubst pairTerm)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst (Term.snd pairTerm)) :=
  pairIH.2.2

/-! ## K12.21.D fundamental_appPi at `Ty.piTy` — Π weak-SN
elimination

Fourth entry of the K12.21 β-redex fundamental-case batch (#1778).
`Term.appPi : Term ctx (Ty.piTy A B) fnRaw → Term ctx A argRaw →
Term ctx (B.subst0 A argRaw) (RawTerm.app fnRaw argRaw)` is the
dependent function-application elimination form.

Asymmetry with K12.21.A: the target type `B.subst0 A argRaw` is
NOT a strict sub-Ty of `Ty.piTy A B` — same structural-recursion
wall as K12.21.C's `B.subst0` codomain on Σ.snd.  Per K12.6's
weak closure design (`Reducibility.lean:353-358`), the dep-Π
eliminator closure ships only as SN of the application
(not full Reducible):

  Reducible (Ty.piTy A' B') f = SN(f)
                              ∧ ∀ arg, Reducible A' arg
                                       → SN(Term.appPi f arg)

Cast-invariance: `Term.subst termSubst (Term.appPi fn arg)`
applies a `Ty.subst0_subst_commute.symm ▸` cast (`Term/Subst.lean:
205-208`), but `Term.isStronglyNormalizing` reads only the raw
index (`Reducibility.lean:303-307`) — the cast preserves the
underlying `RawTerm.app (fnRaw.subst sigma.forRaw) (argRaw.subst
sigma.forRaw)` projection.

Body: `functionIH.2 (Term.subst termSubst argumentTerm)
argumentIH` — same composition shape as K12.21.A's
fundamental_app_at_arrow, but the second conjunct of K12.6's
piTy closure returns SN, not Reducible (K12.6's weak closure).

The full-Reducible upgrade waits for the Kripke logical-relation
refactor that defeats the structural-recursion barrier on
substituted codomains. -/

/-- **K12.21.D fundamental_appPi at `Ty.piTy`** — Π weak-SN
elimination.  Dependent function application composes the
function's weak-piTy closure with the argument's reducibility
witness; the substituted-codomain wall blocks full-Reducible
until the Kripke refactor.

The goal is **SN of the substituted Term.appPi**, not Reducible —
matching K12.6's documented weak closure design (`Reducibility.
lean:339-352`). -/
theorem Reducible.fundamental_appPi_at_piTy_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm :
        Term sourceCtx (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionIH :
        Reducible ((Ty.piTy domainType codomainType).subst sigma)
                  (Term.subst termSubst functionTerm))
    (argumentIH :
        Reducible (domainType.subst sigma)
                  (Term.subst termSubst argumentTerm)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst (Term.appPi functionTerm argumentTerm)) :=
  functionIH.2 (Term.subst termSubst argumentTerm) argumentIH

/-! ## K12.21.E fundamental_recordProj at `Ty.record` —
single-field record projection

Fifth entry of the K12.21 β-redex fundamental-case batch (#1778).
`Term.recordProj : Term ctx (Ty.record A) recordRaw → Term ctx A
(RawTerm.recordProj recordRaw)` projects out the single field
of a record.

The proof is a direct second-conjunct extraction.  Three
definitional facts compose:

1.  `(Ty.record A).subst sigma = Ty.record (A.subst sigma)`
    (`Foundation/Subst.lean:146-147`)
2.  `Reducible (Ty.record A') record = SN(record) ∧ Reducible
    A' (Term.recordProj record)`  (K12.15 closure, see
    `Reducibility.lean:563-565`)
3.  `Term.subst termSubst (Term.recordProj rec) = Term.recordProj
    (Term.subst termSubst rec)`  (`Term/Subst.lean:346-347`)

Body: `recordIH.2` — unary projection.  Closure shape parallels
K12.21.B's `fundamental_fst_at_sigmaTy` (K12.7 first conjunct);
record's single-field design means the eliminator target is
exactly the strict sub-Ty `singleFieldType` with no
substituted-codomain wall, so full Reducible (not weak SN). -/

/-- **K12.21.E fundamental_recordProj at `Ty.record`** — record
field projection.  Direct extraction of the second conjunct from
K12.15's record closure.

Multi-field records compose via nested single-field records (see
`Term.lean:420`+ docstring), preserving this closure shape under
nesting; no separate fundamental case needed for multi-field
projection. -/
theorem Reducible.fundamental_recordProj_at_record
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    {recordValue :
        Term sourceCtx (Ty.record singleFieldType) recordRaw}
    (recordIH :
        Reducible ((Ty.record singleFieldType).subst sigma)
                  (Term.subst termSubst recordValue)) :
    Reducible (singleFieldType.subst sigma)
              (Term.subst termSubst (Term.recordProj recordValue)) :=
  recordIH.2

/-- Fundamental case: `Term.refineElim` at `Ty.refine` (K12.21.F).

`Term.refineElim` projects from a refinement-typed value to the
underlying base type — `Term ctx (Ty.refine baseType predicate)
refinedRaw → Term ctx baseType (RawTerm.refineElim refinedRaw)`.
`Term.subst` commutes definitionally over `.refineElim` (no
cast, since Ty.refine.subst keeps baseType intact under sigma:
`(Ty.refine baseType predicate).subst sigma = Ty.refine
(baseType.subst sigma) (predicate.subst sigma.forRaw.lift)`).

K12.14's refine closure carries the full eliminator-output
witness: `Reducible (Ty.refine baseType _) refinedValue =
SN(refinedValue) ∧ Reducible baseType (Term.refineElim
refinedValue)`.  The fundamental case extracts the second
conjunct — `refineIH.2` — and Lean unifies it with the goal
via the definitional Term.subst commute on `.refineElim`.

Same unary-projection pattern as K12.21.E recordProj and K12.21.B
fst-at-sigmaTy.  The Decidable-predicate discharge aspect of
refinements (the `predicate` argument carrying an SMT obligation)
lives at Layer 5 SMTCert (#1342 D5.6, #1344 D5.8) — orthogonal to
this Reducibility-candidate projection, which only consults the
base-type carrier. -/
theorem Reducible.fundamental_refineElim_at_refine
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    {refinedValue :
        Term sourceCtx (Ty.refine baseType predicate) refinedRaw}
    (refineIH :
        Reducible ((Ty.refine baseType predicate).subst sigma)
                  (Term.subst termSubst refinedValue)) :
    Reducible (baseType.subst sigma)
              (Term.subst termSubst (Term.refineElim refinedValue)) :=
  refineIH.2

/-! ## K12.22 fundamental ι-eliminator cases -/

/-- Fundamental case: `Term.boolElim` at `Ty.bool` (K12.22.A,
weak-SN).

The current bool arm is an SN-direct closed-type clause.  Since the motive
type is arbitrary rather than a structural sub-type of `Ty.bool`, this case
returns SN of the eliminator result.  Full `Reducible motiveType` is deferred
to the same Kripke/refined-candidate infrastructure as the other dependent
eliminators.
-/
theorem Reducible.fundamental_boolElim_at_bool_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    {thenBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw}
    {elseBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw}
    (scrutineeIH :
      Reducible ((Ty.bool : Ty level scope).subst sigma)
        (Term.subst termSubst scrutinee))
    (thenIH :
      Reducible ((motiveType.subst0 Ty.bool RawTerm.boolTrue).subst sigma)
        (Term.subst termSubst thenBranch))
    (elseIH :
      Reducible ((motiveType.subst0 Ty.bool RawTerm.boolFalse).subst sigma)
        (Term.subst termSubst elseBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.boolElim scrutinee thenBranch elseBranch)) :=
  RawTerm.boolElim_isStronglyNormalizing
    (Reducible.isStronglyNormalizing thenIH)
    (Reducible.isStronglyNormalizing elseIH)
    scrutineeIH

/-- Fundamental case: `Term.optionMatch` at `Ty.optionType` (K12.22.B,
weak-SN).

The `Ty.optionType` reducibility arm stores an eliminator closure:
SN of the scrutinee plus SN of the none branch plus SN of each
some-branch application at a reducible element.  The branch-application
premise is supplied by the arrow reducibility of `someBranch`, then
demoted to SN because the current closure returns only weak-SN at the
arbitrary motive type.
-/
theorem Reducible.fundamental_optionMatch_at_option_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term sourceCtx motiveType noneRaw}
    {someBranch :
      Term sourceCtx (Ty.arrow elementType motiveType) someRaw}
    (scrutineeIH :
      Reducible ((Ty.optionType elementType).subst sigma)
        (Term.subst termSubst scrutinee))
    (noneIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst noneBranch))
    (someIH :
      Reducible ((Ty.arrow elementType motiveType).subst sigma)
        (Term.subst termSubst someBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.optionMatch scrutinee noneBranch someBranch)) :=
  scrutineeIH.2
    (Term.subst termSubst noneBranch)
    (Term.subst termSubst someBranch)
    (Reducible.isStronglyNormalizing noneIH)
    (Reducible.isStronglyNormalizing someIH)
    (fun valueTerm valueIH =>
      Reducible.isStronglyNormalizing (someIH.2 valueTerm valueIH))

/-- Fundamental case: `Term.eitherMatch` at `Ty.eitherType` (K12.22.C,
weak-SN).

Same weak eliminator pattern as `optionMatch`, with one arrow-typed
branch for each side.  The current candidate can prove SN of the
eliminator result, while full `Reducible motiveType` remains deferred
to the Kripke/refined-candidate upgrade.
-/
theorem Reducible.fundamental_eitherMatch_at_either_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch :
      Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch :
      Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    (scrutineeIH :
      Reducible ((Ty.eitherType leftType rightType).subst sigma)
        (Term.subst termSubst scrutinee))
    (leftIH :
      Reducible ((Ty.arrow leftType motiveType).subst sigma)
        (Term.subst termSubst leftBranch))
    (rightIH :
      Reducible ((Ty.arrow rightType motiveType).subst sigma)
        (Term.subst termSubst rightBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.eitherMatch scrutinee leftBranch rightBranch)) :=
  scrutineeIH.2
    (Term.subst termSubst leftBranch)
    (Term.subst termSubst rightBranch)
    (Reducible.isStronglyNormalizing leftIH)
    (Reducible.isStronglyNormalizing rightIH)
    (fun valueTerm valueIH =>
      Reducible.isStronglyNormalizing (leftIH.2 valueTerm valueIH))
    (fun valueTerm valueIH =>
      Reducible.isStronglyNormalizing (rightIH.2 valueTerm valueIH))

/-! ## K12.23 fundamental HOTT-eliminator cases -/

/-- Fundamental case: `Term.idJ` at `Ty.id` (K12.23.B, weak-SN).

The current `Ty.id` reducibility arm is intentionally weak: it stores
SN of the equality witness plus an eliminator closure from any SN
base case to SN of `Term.idJ baseCase witness`.  The motive type is
arbitrary, not a structural sub-type of `Ty.id carrier left right`, so
the conclusion here is exactly `Term.isStronglyNormalizing`, not full
`Reducible motiveType`.
-/
theorem Reducible.fundamental_idJ_at_id_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIH :
        Reducible (motiveType.subst sigma)
                  (Term.subst termSubst baseCase))
    (witnessIH :
        Reducible ((Ty.id carrier leftEndpoint rightEndpoint).subst sigma)
                  (Term.subst termSubst witness)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst (Term.idJ baseCase witness)) :=
  witnessIH.2 (Term.subst termSubst baseCase)
    (Reducible.isStronglyNormalizing baseIH)

/-- Fundamental case: `Term.oeqJ` at `Ty.oeq` (K12.23.C, weak-SN).

Observational equality has the same weak eliminator closure shape as
`Ty.id`: SN of the witness plus SN preservation through `oeqJ` for any
SN base case.  The arbitrary motive wall again prevents a full
`Reducible motiveType` conclusion in the current structural-on-`Ty`
candidate.
-/
theorem Reducible.fundamental_oeqJ_at_oeq_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIH :
        Reducible (motiveType.subst sigma)
                  (Term.subst termSubst baseCase))
    (witnessIH :
        Reducible ((Ty.oeq carrier leftEndpoint rightEndpoint).subst sigma)
                  (Term.subst termSubst witness)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst (Term.oeqJ baseCase witness)) :=
  witnessIH.2 (Term.subst termSubst baseCase)
    (Reducible.isStronglyNormalizing baseIH)

/-- Fundamental case: `Term.idStrictRec` at `Ty.idStrict`
(K12.23.D, weak-SN).

Strict identity adds the ambient `mode = Mode.strict` witness to the
same weak eliminator closure used by `Ty.id` and `Ty.oeq`.  The result
is SN of the substituted strict recursor, matching the closure stored in
`Reducible (Ty.idStrict ...)`.
-/
theorem Reducible.fundamental_idStrictRec_at_idStrict_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx
          (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIH :
        Reducible (motiveType.subst sigma)
                  (Term.subst termSubst baseCase))
    (witnessIH :
        Reducible
          ((Ty.idStrict carrier leftEndpoint rightEndpoint).subst sigma)
          (Term.subst termSubst witness)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.idStrictRec modeIsStrict baseCase witness)) :=
  witnessIH.2 modeIsStrict (Term.subst termSubst baseCase)
    (Reducible.isStronglyNormalizing baseIH)

/-! ## K12.26 reflexivity-intro fundamentals with explicit endpoint SN -/

/-- Fundamental case: `Term.refl` at `Ty.id` with an explicit endpoint
SN premise.

`Term.refl` carries a raw endpoint rather than a typed endpoint subterm, so
this lemma does not pretend to be the full structural fundamental-theorem
case.  The caller must provide SN of the substituted endpoint; from there the
weak `Ty.id` closure is discharged by raw refl SN plus generic `idJ` SN.
-/
theorem Reducible.fundamental_refl_at_id_of_endpoint_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (endpointIsSN :
      RawTerm.isStronglyNormalizing (rawWitness.subst sigma.forRaw)) :
    Reducible
      ((Ty.id carrier rawWitness rawWitness).subst sigma)
      (Term.subst termSubst (Term.refl carrier rawWitness)) := by
  let witnessIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.refl (rawWitness.subst sigma.forRaw)) :=
    RawTerm.refl_isStronglyNormalizing endpointIsSN
  exact ⟨witnessIsSN,
    fun {_motiveType} {_baseRaw} _baseCase baseIsSN =>
      RawTerm.idJ_isStronglyNormalizing baseIsSN witnessIsSN⟩

/-- Fundamental case: `Term.oeqRefl` at `Ty.oeq` with an explicit
endpoint SN premise.  Observational equality has the same weak-J closure
shape as `Ty.id`. -/
theorem Reducible.fundamental_oeqRefl_at_oeq_of_endpoint_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (endpointIsSN :
      RawTerm.isStronglyNormalizing (rawWitness.subst sigma.forRaw)) :
    Reducible
      ((Ty.oeq carrier rawWitness rawWitness).subst sigma)
      (Term.subst termSubst (Term.oeqRefl carrier rawWitness)) := by
  let witnessIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.oeqRefl (rawWitness.subst sigma.forRaw)) :=
    RawTerm.oeqRefl_isStronglyNormalizing endpointIsSN
  exact ⟨witnessIsSN,
    fun {_motiveType} {_baseRaw} _baseCase baseIsSN =>
      RawTerm.oeqJ_isStronglyNormalizing baseIsSN witnessIsSN⟩

/-- Fundamental case: `Term.idStrictRefl` at `Ty.idStrict` with an
explicit endpoint SN premise.  The strict-mode eliminator closure keeps its
mode equality parameter explicit and otherwise mirrors `Term.refl`. -/
theorem Reducible.fundamental_idStrictRefl_at_idStrict_of_endpoint_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (endpointIsSN :
      RawTerm.isStronglyNormalizing (rawWitness.subst sigma.forRaw)) :
    Reducible
      ((Ty.idStrict carrier rawWitness rawWitness).subst sigma)
      (Term.subst termSubst
        (Term.idStrictRefl modeIsStrict carrier rawWitness)) := by
  let witnessIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.idStrictRefl (rawWitness.subst sigma.forRaw)) :=
    RawTerm.idStrictRefl_isStronglyNormalizing endpointIsSN
  exact ⟨witnessIsSN,
    fun modeIsStrict' {_motiveType} {_baseRaw} _baseCase baseIsSN =>
      RawTerm.idStrictRec_isStronglyNormalizing baseIsSN witnessIsSN⟩

/-- Fundamental case: `Term.equivApp` at `Ty.equiv` (K12.23.A).

First fundamental atomic over HOTT-adjacent eliminators.  Same
binary Reducible-composition pattern as K12.21.A
`fundamental_app_at_arrow` — `Term.equivApp` is the kernel-
internal application form for type equivalences (per K11.B8 docs
in `Term.lean:1029`+), mirroring `Term.app`'s shape exactly:
takes the equivalence + an argument at carrierA, produces a
result at carrierB.

K12.11's equiv closure ships the FULL Reducible (not SN-fallback)
on the output side, because both carriers (carrierA, carrierB)
are strict sub-Ty of `Ty.equiv carrierA carrierB` — the closure
can recurse on both via def-by-recursion on Ty:

    Reducible (Ty.equiv carrierA carrierB) equivTerm =
      SN(equivTerm) ∧ ∀ argumentTerm,
        Reducible carrierA argumentTerm →
        Reducible carrierB (Term.equivApp equivTerm argumentTerm)

The fundamental atomic projects the second conjunct and applies
to the substituted argument:

    equivIH.2 (Term.subst termSubst argumentTerm) argumentIH

`Term.subst` commutes over `.equivApp` definitionally
(`Term/Subst.lean:414` — no cast, since `Ty.equiv.subst` is
also definitional per `Foundation/Subst.lean:142`).  Same audit
gate as the existing K12.21 cluster.

Note: `Term.equivApply` (the D3.6-P4 univalence-target ctor at
`Term.lean:990`+) is a SEPARATE constructor projecting to a
different raw form; its fundamental case will ship as K12.23.B
once we audit which closure governs it. -/
theorem Reducible.fundamental_equivApp_at_equiv
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm :
        Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (equivIH :
        Reducible ((Ty.equiv carrierA carrierB).subst sigma)
                  (Term.subst termSubst equivTerm))
    (argumentIH :
        Reducible (carrierA.subst sigma)
                  (Term.subst termSubst argumentTerm)) :
    Reducible (carrierB.subst sigma)
              (Term.subst termSubst (Term.equivApp equivTerm argumentTerm)) :=
  equivIH.2 (Term.subst termSubst argumentTerm) argumentIH

/-- Fundamental case: `Term.oeqFunext` at `Ty.oeq` (K12.23.B).

The current `Ty.oeq` reducibility arm is weak-J shaped: SN of the
witness plus SN preservation for `Term.oeqJ` over every SN base case.
`Term.oeqFunext` has a typed pointwise proof subterm, so its SN follows
from that subterm's reducibility by `RawTerm.oeqFunext_isStronglyNormalizing`.
The `oeqJ` closure is pure congruence in the present raw reduction
fragment, discharged by `RawTerm.oeqJ_isStronglyNormalizing`. -/
theorem Reducible.fundamental_oeqFunext_at_oeq
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {leftFunctionRaw rightFunctionRaw pointwiseRaw : RawTerm scope}
    {pointwiseProof :
        Term sourceCtx
          (oeqFunextPointwiseType domainType codomainType
            leftFunctionRaw rightFunctionRaw)
          pointwiseRaw}
    (pointwiseIH :
        Reducible
          ((oeqFunextPointwiseType domainType codomainType
            leftFunctionRaw rightFunctionRaw).subst sigma)
          (Term.subst termSubst pointwiseProof)) :
    Reducible
      ((Ty.oeq (Ty.arrow domainType codomainType)
          leftFunctionRaw rightFunctionRaw).subst sigma)
      (Term.subst termSubst
        (Term.oeqFunext domainType codomainType
          leftFunctionRaw rightFunctionRaw pointwiseProof)) := by
  let witnessIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.oeqFunext (pointwiseRaw.subst sigma.forRaw)) :=
    RawTerm.oeqFunext_isStronglyNormalizing
      (Reducible.isStronglyNormalizing pointwiseIH)
  exact ⟨witnessIsSN,
    fun {_motiveType} {_baseRaw} _baseCase baseIsSN =>
      RawTerm.oeqJ_isStronglyNormalizing baseIsSN witnessIsSN⟩

/-! ## K12.24 fundamental cubical-eliminator cases -/

/-- Fundamental case: `Term.pathApp` at `Ty.path` (K12.24.A).

Cubical path application — `Term.pathApp` consumes a path
witness at `Ty.path carrierType leftEndpoint rightEndpoint` plus
an interval point and produces a value at carrierType.  The
`modeIsUnivalent : mode = Mode.univalent` data parameter on the
ctor (`Term.lean:348`) is the univalent-mode gate that protects
the cubical β rule from firing in non-univalent modes.

K12.12's path closure (`Reducibility.lean:476-483`) carries a
quantified eliminator-output Reducible witness, threading the
SAME mode gate plus an interval-SN argument hypothesis:

    Reducible (Ty.path carrier _ _) pathTerm =
      SN(pathTerm) ∧
      ∀ (modeIsUnivalent : mode = Mode.univalent) intervalTerm,
        SN(intervalTerm) →
        Reducible carrier (Term.pathApp modeIsUnivalent pathTerm intervalTerm)

The fundamental atomic projects the second conjunct and supplies
all three pieces from the IHs:

* `modeIsUnivalent` comes directly from the ctor parameter
  (threaded as `modeIsUnivalent` here).
* `Term.subst termSubst intervalTerm` is the post-substitution
  interval point.
* `intervalIH` is `Reducible (Ty.interval.subst sigma)
  (subst intervalTerm)`; Ty.interval is a closed type so
  `Ty.interval.subst sigma = Ty.interval` definitionally
  (`Foundation/Subst.lean:127`), and K12.4's interval closure
  (`Reducibility.lean:329`) is literally `SN(...)`, so intervalIH
  IS the SN witness K12.12 demands.

Term.subst commutes definitionally over `.pathApp`
(`Term/Subst.lean:322` — no cast); Ty.path.subst is also
definitional (`Foundation/Subst.lean:128-131`), so the substituted
goal `(Ty.path c l r).subst sigma` unifies with the closure's
LHS without rewriting.

Same projection pattern as K12.23.A equivApp.  The interval-SN
demand sets this atomic apart from K12.23.A's Reducible-argument
demand — path's argument lives at the closed type Ty.interval
where Reducible degenerates to SN. -/
theorem Reducible.fundamental_pathApp_at_path
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw intervalRaw : RawTerm scope}
    {pathTerm :
        Term sourceCtx
             (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    {intervalTerm : Term sourceCtx Ty.interval intervalRaw}
    (pathIH :
        Reducible
          ((Ty.path carrierType leftEndpoint rightEndpoint).subst sigma)
          (Term.subst termSubst pathTerm))
    (intervalIH :
        Reducible (Ty.interval.subst sigma)
                  (Term.subst termSubst intervalTerm)) :
    Reducible (carrierType.subst sigma)
              (Term.subst termSubst
                 (Term.pathApp modeIsUnivalent pathTerm intervalTerm)) :=
  pathIH.2 modeIsUnivalent (Term.subst termSubst intervalTerm) intervalIH

/-- Fundamental case: `Term.glueElim` at `Ty.glue` (K12.24.B).

`Ty.glue` carries a full eliminator-output closure in K12.12:
reducibility of a glued value includes reducibility of
`Term.glueElim` at the strict sub-type `baseType`, gated by the
same univalent-mode witness.  The fundamental case is therefore a
direct projection of that closure after substitution. -/
theorem Reducible.fundamental_glueElim_at_glue
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    {gluedValue :
        Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw}
    (glueIH :
        Reducible ((Ty.glue baseType boundaryWitness).subst sigma)
                  (Term.subst termSubst gluedValue)) :
    Reducible (baseType.subst sigma)
              (Term.subst termSubst
                (Term.glueElim modeIsUnivalent gluedValue)) :=
  glueIH.2 modeIsUnivalent

/-- Fundamental case: `Term.codataDest` at `Ty.codata` (K12.26.A).

The codata reducibility arm stores the full observation closure at
the strict sub-type `outputType`; `stateType` is carried by the
codata value but is not exposed by the current one-observation
destructor.  This fundamental case is the direct projection of that
closure after `Term.subst` distributes over `codataDest`. -/
theorem Reducible.fundamental_codataDest_at_codata
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    {codataValue :
        Term sourceCtx (Ty.codata stateType outputType) codataRaw}
    (codataIH :
        Reducible ((Ty.codata stateType outputType).subst sigma)
                  (Term.subst termSubst codataValue)) :
    Reducible (outputType.subst sigma)
              (Term.subst termSubst (Term.codataDest codataValue)) :=
  codataIH.2

end LeanFX2
