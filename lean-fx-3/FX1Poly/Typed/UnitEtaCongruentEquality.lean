import FX1Poly.Typed.UnitEtaCongruenceGap

/-! # FX1Poly/Typed/UnitEtaCongruentEquality
   — the congruent unit-η judgmental equality SPEC + the gap pair related (ULC-1 verdict)

## The ULC-1 spike verdict: SPEC FIRST, decider second

ULC-1 asked how the unit-collapse FUNCTION should supply per-subterm classifiers.  The spike's
finding inverts the question: the collapse's SOUNDNESS statement ("collapsed term is congruently
unit-η-equal to the source") had no relation to be stated against — `DefEqUnitEta` is provably
not congruent (`DefEqUnitEta.isNotCongruent`).  So the first brick is the congruent relation
itself, as a SPEC object whose leaves carry typing PREMISES (presupposition style) — the spec
needs no classifier computation at all.  The classifier-supply question moves wholly to the
DECIDER (the collapse, the named follow-on), where the committed candidate is CHECK-mode against
the fixed target `unitTypeCell` via the whnf-directed grown checker on the route-H wf fragment
(the STR-5 refutation bars the raw relation).

## What this module ships

  * `DefEqUnitEtaCong` / `ChildrenUnitEtaCong` — the mutual congruent closure: `ofDefEq` embeds
    every `DefEqUnitEta` instance (so βη-conversion and top-level unit-η are included);
    `congGen` descends ONE generator with pointwise-related children.  The children relation
    relates shift-0 children by the full congruent relation (`consZero`) and keeps binder
    children syntactically equal (`consEqual`, any shift) — the zero-shift congruent fragment.
  * `refl` / `sym` — unconditional (unlike `DefEqUnitEta.reflOfGrownTyped`, congruent refl needs
    NO typing: every term is `mkGen`-rooted, so structural descent with `consEqual` everywhere
    closes it).
  * ★ `gapPairCongruentlyEqual` — NON-VACUITY at exactly the machine-checked gap:
    `pair(x,x)` is congruently unit-η-equal to `pair(unit,unit)` (congruence + the components'
    `unitEta`), the pair `DefEqUnitEta.isNotCongruent` proves unreachable for `DefEqUnitEta`.
  * ★ `strictlyExtendsDefEqUnitEta` — the strictness theorem: the congruent relation relates a
    pair that `DefEqUnitEta` relates at NO classifier.  Composed with UNIT-2's
    `strictlyExtendsBetaEtaConv`, the chain is now machine-checked at every link:
    `BetaEtaConv ⊊ DefEqUnitEta ⊊ DefEqUnitEtaCong`.

## Honest boundaries

(1) NO transitivity here: congruent transitivity composes leaf equations across DIFFERENT
positions and needs the collapse-normalizer (collapse-then-βη-compare) or a CR-style argument —
that is the decider brick, not this one.  (2) Binder-crossing congruence is NOT included:
`consEqual` keeps binder children equal; relating UNDER a binder requires extending the context
by the binder's domain, which generic `mkGen` children do not carry (per-generator binder-domain
info; `gen_lam`'s T2 domain child makes the lam case doable later).  (3) `congGen` itself carries
no typing — the congruence skeleton is raw, and only the `ofDefEq` leaves are typed; soundness
and decidability claims live on the wf fragment, exactly as for raw `Conv`.

## Zero-axiom verification

Mutual structural recursion on the derivation (refl/sym) and on raw terms (refl), constructor
applications for the witnesses.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

mutual

/-- **The congruent unit-η judgmental equality (zero-shift fragment)**: the congruent closure of
`DefEqUnitEta` — `ofDefEq` embeds the βη + top-level-unit-η relation; `congGen` descends one
generator with pointwise-related children.  The spec object the unit-collapse decider is sound
against. -/
inductive DefEqUnitEtaCong (profile : PolyProfile) : {scope : Nat} →
    TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  /-- Every `DefEqUnitEta` instance (βη-conversion of wf-typed terms; top-level unit-η) is
  congruently equal. -/
  | ofDefEq {scope : Nat} {context : TypingContext profile scope}
      {leftTerm rightTerm classifier : RawTerm scope}
      (defEq : DefEqUnitEta profile context leftTerm rightTerm classifier) :
      DefEqUnitEtaCong profile context leftTerm rightTerm
  /-- Congruence: cells rooted at the SAME generator with the SAME payload and pointwise-related
  children are congruently equal. -/
  | congGen {scope : Nat} {context : TypingContext profile scope}
      {generator : Generator} (payload : generator.payload scope)
      {leftChildren rightChildren : RawTermChildren generator.binderShifts scope}
      (childrenRelated :
        ChildrenUnitEtaCong profile context generator.binderShifts
          leftChildren rightChildren) :
      DefEqUnitEtaCong profile context
        (.mkGen generator payload leftChildren) (.mkGen generator payload rightChildren)

/-- Pointwise congruent equality of children spines: shift-0 children relate by the full
congruent relation (`consZero`); binder children are kept syntactically EQUAL (`consEqual` —
relating UNDER a binder needs the binder-domain context extension, the named follow-on). -/
inductive ChildrenUnitEtaCong (profile : PolyProfile) : {scope : Nat} →
    TypingContext profile scope → (shifts : List Nat) →
    RawTermChildren shifts scope → RawTermChildren shifts scope → Prop where
  | nil {scope : Nat} {context : TypingContext profile scope} :
      ChildrenUnitEtaCong profile context [] .childNil .childNil
  /-- A shift-0 head child relates by the full congruent relation in the SAME context. -/
  | consZero {scope : Nat} {context : TypingContext profile scope} {restShifts : List Nat}
      {leftChild rightChild : RawTerm scope}
      {leftRest rightRest : RawTermChildren restShifts scope}
      (headRelated : DefEqUnitEtaCong profile context leftChild rightChild)
      (restRelated : ChildrenUnitEtaCong profile context restShifts leftRest rightRest) :
      ChildrenUnitEtaCong profile context (0 :: restShifts)
        (.childCons leftChild leftRest) (.childCons rightChild rightRest)
  /-- A head child kept syntactically equal on both sides (any shift — in particular every
  binder child).  This is also what makes `refl` unconditional. -/
  | consEqual {scope : Nat} {context : TypingContext profile scope}
      {headShift : Nat} {restShifts : List Nat}
      {sharedChild : RawTerm (scope + headShift)}
      {leftRest rightRest : RawTermChildren restShifts scope}
      (restRelated : ChildrenUnitEtaCong profile context restShifts leftRest rightRest) :
      ChildrenUnitEtaCong profile context (headShift :: restShifts)
        (.childCons sharedChild leftRest) (.childCons sharedChild rightRest)

end

mutual

/-- Reflexivity — UNCONDITIONAL (no typing, no well-formedness): every term is `mkGen`-rooted,
so structural descent with `consEqual` at every child closes it. -/
theorem DefEqUnitEtaCong.refl {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} :
    (term : RawTerm scope) → DefEqUnitEtaCong profile context term term
  | .mkGen _generator payload children =>
      .congGen payload (ChildrenUnitEtaCong.refl children)

/-- Children reflexivity: `consEqual` at every position. -/
theorem ChildrenUnitEtaCong.refl {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {shifts : List Nat} :
    (children : RawTermChildren shifts scope) →
      ChildrenUnitEtaCong profile context shifts children children
  | .childNil => .nil
  | .childCons _headChild restChildren =>
      .consEqual (ChildrenUnitEtaCong.refl restChildren)

end

mutual

/-- Symmetry (every arm is symmetric in its premises). -/
theorem DefEqUnitEtaCong.sym {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {leftTerm rightTerm : RawTerm scope}
    (related : DefEqUnitEtaCong profile context leftTerm rightTerm) :
    DefEqUnitEtaCong profile context rightTerm leftTerm :=
  match related with
  | .ofDefEq defEq => .ofDefEq defEq.sym
  | .congGen payload childrenRelated =>
      .congGen payload (ChildrenUnitEtaCong.sym childrenRelated)

/-- Children symmetry. -/
theorem ChildrenUnitEtaCong.sym {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {shifts : List Nat}
    {leftChildren rightChildren : RawTermChildren shifts scope}
    (related : ChildrenUnitEtaCong profile context shifts leftChildren rightChildren) :
    ChildrenUnitEtaCong profile context shifts rightChildren leftChildren :=
  match related with
  | .nil => .nil
  | .consZero headRelated restRelated =>
      .consZero (DefEqUnitEtaCong.sym headRelated) (ChildrenUnitEtaCong.sym restRelated)
  | .consEqual restRelated => .consEqual (ChildrenUnitEtaCong.sym restRelated)

end

/-- **★ Non-vacuity at exactly the machine-checked gap**: the pairs `pair(x,x)` /
`pair(unit,unit)` — which `DefEqUnitEta.isNotCongruent` proves `DefEqUnitEta` relates at NO
classifier — ARE congruently unit-η-equal: one `congGen` descent, then the components'
`unitEta`. -/
theorem DefEqUnitEtaCong.gapPairCongruentlyEqual (profile : PolyProfile) :
    DefEqUnitEtaCong profile (unitVariableContext profile)
      pairOfUnitVariables pairOfUnitValues :=
  DefEqUnitEtaCong.congGen (generator := Generator.gen_pair) ()
    (.consZero
      (.ofDefEq (.unitEta (Or.inr (unitVariableTyped profile))
        (Or.inl (HasTypeDescDataIntro.unitValueTyped (unitVariableContext profile)))))
      (.consZero
        (.ofDefEq (.unitEta (Or.inr (unitVariableTyped profile))
          (Or.inl (HasTypeDescDataIntro.unitValueTyped (unitVariableContext profile)))))
        .nil))

/-- **★ The congruent relation STRICTLY extends `DefEqUnitEta`** — completing the
machine-checked strictness chain `BetaEtaConv ⊊ DefEqUnitEta ⊊ DefEqUnitEtaCong`: the gap pair
is congruently equal yet `DefEqUnitEta`-related at no classifier. -/
theorem DefEqUnitEtaCong.strictlyExtendsDefEqUnitEta (profile : PolyProfile) :
    ∃ (leftTerm rightTerm : RawTerm 1),
      DefEqUnitEtaCong profile (unitVariableContext profile) leftTerm rightTerm ∧
        ∀ classifier : RawTerm 1,
          ¬ DefEqUnitEta profile (unitVariableContext profile)
              leftTerm rightTerm classifier :=
  ⟨pairOfUnitVariables, pairOfUnitValues,
    DefEqUnitEtaCong.gapPairCongruentlyEqual profile,
    (DefEqUnitEta.isNotCongruent profile).2⟩

end FX1Poly.Typed
