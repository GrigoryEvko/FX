import FX1Poly.Typed.BetaEtaConvDecidable
import FX1Poly.Typed.HasTypeDescDataIntroMetatheory
import FX1Poly.Typed.RawTermHeadGenerator

/-! # FX1Poly/Typed/UnitEtaJudgmentalEquality
   — ★ typed unit-η: the judgmental equality βη-conversion CANNOT express, decidable (#362 core)

The first genuinely TYPE-DIRECTED judgmental-equality extension: `DefEqUnitEta` is βη-conversion
(`BetaEtaConv`, decided by #1202's normalize-and-compare) extended by the unit-η rule — ANY two
terms typed at `unitTypeCell` are equal.  Raw rewriting can never have this rule: an unconditional
raw unit-η is unsound (deliberately excluded from `Step.eta`), because whether the collapse is
justified depends on the TYPE, not the term's shape.  This module ships the relation, its
equivalence package, the strictness witness, and the decider:

  * `DefEqUnitEta` — two arms, presupposition-carrying: `ofBetaEtaConv` (wf context + both subjects
    grown-typed at the classifier + `BetaEtaConv`) and `unitEta` (both subjects typed at
    `unitTypeCell` by the data-intro or the grown engine — no reduction, no well-formedness: the
    one-value collapse is type-directed).
  * `refl` / `sym` / `trans` — `trans` is UNCONDITIONAL given the derivations (the βη-βη peak is
    discharged by `BetaEtaConv.transAtTypedMiddle` with the wf + middle-typing the first arm
    CARRIES; every unit-involving case re-fires `unitEta`).
  * ★ `strictlyExtendsBetaEtaConv` — the textbook witness: a unit-typed VARIABLE vs the unit value
    `unitCell`, in the raw context binding `unitTypeCell`.  Both are βη-normal and distinct, so NOT
    `BetaEtaConv`; both are typed at `unitTypeCell` (the grown var rule needs no well-formedness),
    so `DefEqUnitEta`.  This is inexpressible at the raw layer and was inexpressible before UNIT-1
    landed the unit type.
  * `dataIntroUnitPairsCollapseToRefl` — the honest degeneracy boundary: on the DATA-INTRO fragment
    the `unitEta` arm is refl-degenerate (closed unit canonicity already collapses both sides to
    `unitCell`); the strictness genuinely lives at open unit-typed NEUTRALS.
  * ★ `decidableOfWfTyped` — the decider: compare the classifier with `unitTypeCell` (structural
    `DecidableEq`); at unit type the answer is always YES (`unitEta`); off unit type the `unitEta`
    arm is impossible (`betaEtaConvOfNotUnit` inversion) and the decision is exactly #1202's
    `BetaEtaConv.decidableOfWfTyped`.

## Honest boundaries

(1) NOT congruent: `DefEqUnitEta` does not collapse unit-typed SUBTERMS (a pair of unit-typed
components is not equated to a pair of `unitCell`s); the congruent closure is the η-long
type-directed readback (#481 / the #364 remainder), the named follow-on.  (2) `WfContextDesc`
cannot currently bind `unitTypeCell` (the formation engine has no `unitCode` row — the nullary
flag-uniqueness obstruction that parked bool/empty/nat in the standalone `HasTypeDescBaseType`
engine), so the strictness witness lives in a RAW context; giving unit-typed variables the full wf
metatheory needs the formation-row follow-on.  (3) SProp/modal η kin (η-M15e) remain open.

## Zero-axiom verification

Structural `cases` on the two-arm relation, the shipped #1202 decider + typed-middle transitivity,
`reduceOnceBetaEta_complete` at `rfl`-computing leaves, and `Generator.noConfusion ∘ congrArg
headGenerator` discrimination.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **The typed unit-η judgmental equality**: βη-conversion of grown-typed terms, extended by the
type-directed one-value collapse at `unitTypeCell`.  Presupposition-carrying: each arm carries the
typings (and, for the βη arm, the context well-formedness) its metatheory needs, so the equivalence
package below is unconditional given derivations. -/
inductive DefEqUnitEta (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) :
    RawTerm scope → RawTerm scope → RawTerm scope → Prop where
  /-- The βη embedding: well-typed βη-convertible terms are judgmentally equal (the #1202-decided
  relation, conservative base). -/
  | ofBetaEtaConv {leftTerm rightTerm classifier : RawTerm scope}
      (contextWellFormed : WfContextDesc context)
      (leftTyped : HasTypeDescPi profile context leftTerm classifier)
      (rightTyped : HasTypeDescPi profile context rightTerm classifier)
      (convertible : BetaEtaConv leftTerm rightTerm) :
      DefEqUnitEta profile context leftTerm rightTerm classifier
  /-- **Unit-η**: ANY two terms typed at `unitTypeCell` (by the data-intro engine — the unit value —
  or the grown engine — variables/neutrals) are judgmentally equal.  Type-directed: no reduction
  relates them; the TYPE alone justifies the collapse. -/
  | unitEta {leftTerm rightTerm : RawTerm scope}
      (leftTypedAtUnit :
        HasTypeDescDataIntro profile context leftTerm unitTypeCell ∨
          HasTypeDescPi profile context leftTerm unitTypeCell)
      (rightTypedAtUnit :
        HasTypeDescDataIntro profile context rightTerm unitTypeCell ∨
          HasTypeDescPi profile context rightTerm unitTypeCell) :
      DefEqUnitEta profile context leftTerm rightTerm unitTypeCell

namespace DefEqUnitEta

/-- Reflexivity at any grown typing (via the reflexive βη join). -/
theorem reflOfGrownTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {term classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context term classifier) :
    DefEqUnitEta profile context term term classifier :=
  .ofBetaEtaConv contextWellFormed typed typed (BetaEtaConv.refl term)

/-- Symmetry (both arms are symmetric in their premises). -/
theorem sym {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {leftTerm rightTerm classifier : RawTerm scope}
    (defEq : DefEqUnitEta profile context leftTerm rightTerm classifier) :
    DefEqUnitEta profile context rightTerm leftTerm classifier := by
  cases defEq with
  | ofBetaEtaConv contextWellFormed leftTyped rightTyped convertible =>
      exact .ofBetaEtaConv contextWellFormed rightTyped leftTyped (BetaEtaConv.sym convertible)
  | unitEta leftTypedAtUnit rightTypedAtUnit =>
      exact .unitEta rightTypedAtUnit leftTypedAtUnit

/-- **Transitivity — unconditional given the derivations.**  The βη-βη peak is discharged by typed
βη Church-Rosser through the middle term (whose well-formedness + typing the FIRST derivation
carries); every case touching `unitEta` re-fires `unitEta` (the endpoints' unit typings come from
the arms' own premises — the grown typing at the now-pinned `unitTypeCell` classifier supplies the
missing side). -/
theorem trans {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {leftTerm middleTerm rightTerm classifier : RawTerm scope}
    (leftToMiddle : DefEqUnitEta profile context leftTerm middleTerm classifier)
    (middleToRight : DefEqUnitEta profile context middleTerm rightTerm classifier) :
    DefEqUnitEta profile context leftTerm rightTerm classifier := by
  cases leftToMiddle with
  | ofBetaEtaConv contextWellFormed leftTyped middleTypedFirst convertibleFirst =>
      cases middleToRight with
      | ofBetaEtaConv _ _ rightTyped convertibleSecond =>
          exact .ofBetaEtaConv contextWellFormed leftTyped rightTyped
            (BetaEtaConv.transAtTypedMiddle contextWellFormed middleTypedFirst
              convertibleFirst convertibleSecond)
      | unitEta _ rightTypedAtUnit =>
          exact .unitEta (Or.inr leftTyped) rightTypedAtUnit
  | unitEta leftTypedAtUnit _ =>
      cases middleToRight with
      | ofBetaEtaConv _ _ rightTyped _ =>
          exact .unitEta leftTypedAtUnit (Or.inr rightTyped)
      | unitEta _ rightTypedAtUnit =>
          exact .unitEta leftTypedAtUnit rightTypedAtUnit

end DefEqUnitEta

/-- The raw context binding `unitTypeCell` — the home of the unit-typed VARIABLE.  Raw, not
`WfContextDesc`-well-formed: the formation engine has no `unitCode` row (the nullary
flag-uniqueness obstruction), but the var TYPING rule needs no well-formedness. -/
def unitVariableContext (profile : PolyProfile) : TypingContext profile 1 :=
  (TypingContext.empty : TypingContext profile 0).cons unitTypeCell

/-- The variable bound at `unitTypeCell` IS grown-typed at `unitTypeCell` — the formation var rule
fires in ANY context, and looking up the newest binding weakens the closed leaf `unitTypeCell` to
itself. -/
theorem unitVariableTyped (profile : PolyProfile) :
    HasTypeDescPi profile (unitVariableContext profile)
      (variableCell ⟨0, Nat.zero_lt_one⟩) unitTypeCell :=
  HasTypeDescPi.ofFormation
    (HasTypeDesc.var (unitVariableContext profile) ⟨0, Nat.zero_lt_one⟩)

/-- **★ Unit-η is STRICTLY beyond βη-conversion**: the unit-typed variable and the unit value are
judgmentally equal (`unitEta` — both typed at `unitTypeCell`) but provably NOT `BetaEtaConv` (both
are βη-normal leaves, so a join forces them syntactically equal — distinct head generators).  The
textbook motivation for type-directed η, machine-checked: no rewriting relation can close this
pair, only the type can. -/
theorem DefEqUnitEta.strictlyExtendsBetaEtaConv (profile : PolyProfile) :
    ∃ (context : TypingContext profile 1) (leftTerm rightTerm : RawTerm 1),
      DefEqUnitEta profile context leftTerm rightTerm unitTypeCell ∧
        ¬ BetaEtaConv leftTerm rightTerm := by
  refine ⟨unitVariableContext profile, variableCell ⟨0, Nat.zero_lt_one⟩, unitCell,
    .unitEta (Or.inr (unitVariableTyped profile))
      (Or.inl (HasTypeDescDataIntro.unitValueTyped (unitVariableContext profile))),
    fun convertible => ?_⟩
  obtain ⟨commonTerm, variableChain, unitChain⟩ := convertible
  have variableIsCommon :=
    Step.betaEtaStar.eq_of_noBetaEtaStep
      (RawTerm.reduceOnceBetaEta_complete (rfl :
        (variableCell ⟨0, Nat.zero_lt_one⟩ : RawTerm 1).reduceOnceBetaEta = none))
      variableChain
  have unitIsCommon :=
    Step.betaEtaStar.eq_of_noBetaEtaStep
      (RawTerm.reduceOnceBetaEta_complete (rfl :
        (unitCell : RawTerm 1).reduceOnceBetaEta = none))
      unitChain
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator (variableIsCommon.trans unitIsCommon.symm))

/-- **The honest degeneracy boundary**: on the DATA-INTRO fragment the `unitEta` arm is
refl-degenerate — closed unit canonicity (`subjectIsUnitOfUnitClassifier`) already collapses both
sides to `unitCell`, so the two terms are EQUAL, not merely judgmentally equal.  The strict content
of unit-η lives exactly at open unit-typed NEUTRALS (the variable witness above). -/
theorem DefEqUnitEta.dataIntroUnitPairsCollapseToRefl {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {leftTerm rightTerm : RawTerm scope}
    (leftTyped : HasTypeDescDataIntro profile context leftTerm unitTypeCell)
    (rightTyped : HasTypeDescDataIntro profile context rightTerm unitTypeCell) :
    leftTerm = rightTerm :=
  (HasTypeDescDataIntro.subjectIsUnitOfUnitClassifier leftTyped).trans
    (HasTypeDescDataIntro.subjectIsUnitOfUnitClassifier rightTyped).symm

/-- **Inversion off the unit type**: at a classifier that is NOT `unitTypeCell`, only the βη arm
can have fired — the `unitEta` arm pins its classifier index. -/
theorem DefEqUnitEta.betaEtaConvOfNotUnit {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {leftTerm rightTerm classifier : RawTerm scope}
    (defEq : DefEqUnitEta profile context leftTerm rightTerm classifier)
    (notUnitClassifier : classifier ≠ unitTypeCell) :
    BetaEtaConv leftTerm rightTerm := by
  cases defEq with
  | ofBetaEtaConv _ _ _ convertible => exact convertible
  | unitEta _ _ => exact absurd rfl notUnitClassifier

/-- **★ The decider** — typed unit-η judgmental equality is decidable for grown-typed terms over a
well-formed context: compare the classifier with `unitTypeCell` structurally; at unit type the
answer is always YES (the one-value collapse), off unit type the decision is exactly the #1202
βη decider. -/
def DefEqUnitEta.decidableOfWfTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {leftTerm rightTerm classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (leftTyped : HasTypeDescPi profile context leftTerm classifier)
    (rightTyped : HasTypeDescPi profile context rightTerm classifier) :
    Decidable (DefEqUnitEta profile context leftTerm rightTerm classifier) :=
  if isUnitClassifier : classifier = unitTypeCell then
    .isTrue (by
      subst isUnitClassifier
      exact .unitEta (Or.inr leftTyped) (Or.inr rightTyped))
  else
    match BetaEtaConv.decidableOfWfTyped contextWellFormed leftTyped rightTyped with
    | .isTrue convertible =>
        .isTrue (.ofBetaEtaConv contextWellFormed leftTyped rightTyped convertible)
    | .isFalse notConvertible =>
        .isFalse (fun defEq => notConvertible (defEq.betaEtaConvOfNotUnit isUnitClassifier))

end FX1Poly.Typed
