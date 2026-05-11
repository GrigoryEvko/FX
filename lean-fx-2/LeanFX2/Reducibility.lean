import LeanFX2.Term
import LeanFX2.Reduction.RawPar

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
* **All remaining constructors** (~6 type formers: refine, record,
  codata, session, effect, modal): SN-fallback (admissible but
  weak — every reducible term is at least SN).  K12.13-K12.16
  tighten each to its type-former-specific closure.

The pivot keeps K12.2-K12.4's six closed-leaf arms semantically
correct (SN IS the proper Tait clause for closed-leaf types).
K12.5 adds the proper arrow closure.  K12.6+ refines the
remaining ~17 weak-SN arms incrementally.

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
  | Ty.refine _ _, _, term => Term.isStronglyNormalizing term
  | Ty.record _, _, term => Term.isStronglyNormalizing term
  | Ty.codata _ _, _, term => Term.isStronglyNormalizing term
  | Ty.session _, _, term => Term.isStronglyNormalizing term
  | Ty.effect _ _, _, term => Term.isStronglyNormalizing term
  | Ty.modal _ _, _, term => Term.isStronglyNormalizing term

end LeanFX2
