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

(1) Transitivity is a RULE (`trans` constructor — standard for a declarative judgmental
equality), NOT an admissibility theorem: whether the trans-FREE algorithmic presentation
(congruence + leaves only) derives the same relation is exactly the canonicalizer COMPLETENESS
question of the collapse-decider campaign; the spec takes the rule, the decider must earn it.
(2) Binder-crossing congruence is NOT included:
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
  children are congruently equal.  The children relation starts with no shared preceding
  sibling. -/
  | congGen {scope : Nat} {context : TypingContext profile scope}
      {generator : Generator} (payload : generator.payload scope)
      {leftChildren rightChildren : RawTermChildren generator.binderShifts scope}
      (childrenRelated :
        ChildrenUnitEtaCong profile context none generator.binderShifts
          leftChildren rightChildren) :
      DefEqUnitEtaCong profile context
        (.mkGen generator payload leftChildren) (.mkGen generator payload rightChildren)
  /-- Transitivity — a RULE of the declarative equality (standard for judgmental equality).
  Its ADMISSIBILITY in the trans-free algorithmic presentation is exactly the canonicalizer
  completeness question (the collapse-decider campaign); as a spec rule it lets the decision
  procedure's soundness compose through the collapsed middle. -/
  | trans {scope : Nat} {context : TypingContext profile scope}
      {leftTerm middleTerm rightTerm : RawTerm scope}
      (leftToMiddle : DefEqUnitEtaCong profile context leftTerm middleTerm)
      (middleToRight : DefEqUnitEtaCong profile context middleTerm rightTerm) :
      DefEqUnitEtaCong profile context leftTerm rightTerm

/-- Pointwise congruent equality of children spines, threading the SHARED preceding sibling (the
binder-domain candidate per the telescope discipline): shift-0 children relate by the full
congruent relation (`consZero` — heads may differ, so no shared domain flows downstream); a
SHARED shift-0 head flows to the next position (`consEqualZero`); a binder child relates UNDER
the shared preceding sibling's context extension (`consBinder` — the binder-crossing arm the
binder-fence refutation forces); shared heads at positive shifts are kept by `consEqualHigher`. -/
inductive ChildrenUnitEtaCong (profile : PolyProfile) : {scope : Nat} →
    TypingContext profile scope → Option (RawTerm scope) → (shifts : List Nat) →
    RawTermChildren shifts scope → RawTermChildren shifts scope → Prop where
  | nil {scope : Nat} {context : TypingContext profile scope}
      {previousShared : Option (RawTerm scope)} :
      ChildrenUnitEtaCong profile context previousShared [] .childNil .childNil
  /-- A shift-0 head child relates by the full congruent relation in the SAME context.  The heads
  may DIFFER, so no shared domain flows to the next position. -/
  | consZero {scope : Nat} {context : TypingContext profile scope}
      {previousShared : Option (RawTerm scope)} {restShifts : List Nat}
      {leftChild rightChild : RawTerm scope}
      {leftRest rightRest : RawTermChildren restShifts scope}
      (headRelated : DefEqUnitEtaCong profile context leftChild rightChild)
      (restRelated : ChildrenUnitEtaCong profile context none restShifts leftRest rightRest) :
      ChildrenUnitEtaCong profile context previousShared (0 :: restShifts)
        (.childCons leftChild leftRest) (.childCons rightChild rightRest)
  /-- A SHARED shift-0 head child — it becomes the next position's binder-domain candidate. -/
  | consEqualZero {scope : Nat} {context : TypingContext profile scope}
      {previousShared : Option (RawTerm scope)} {restShifts : List Nat}
      {sharedChild : RawTerm scope}
      {leftRest rightRest : RawTermChildren restShifts scope}
      (restRelated : ChildrenUnitEtaCong profile context (some sharedChild) restShifts
        leftRest rightRest) :
      ChildrenUnitEtaCong profile context previousShared (0 :: restShifts)
        (.childCons sharedChild leftRest) (.childCons sharedChild rightRest)
  /-- **The binder-crossing arm**: with a SHARED preceding sibling available as the binder
  domain, shift-1 head children relate by the full congruent relation in the EXTENDED context.
  Symmetric because the domain is shared. -/
  | consBinder {scope : Nat} {context : TypingContext profile scope}
      {domainSibling : RawTerm scope} {restShifts : List Nat}
      {leftBody rightBody : RawTerm (scope + 1)}
      {leftRest rightRest : RawTermChildren restShifts scope}
      (bodiesRelated : DefEqUnitEtaCong profile (context.cons domainSibling)
        leftBody rightBody)
      (restRelated : ChildrenUnitEtaCong profile context none restShifts leftRest rightRest) :
      ChildrenUnitEtaCong profile context (some domainSibling) (1 :: restShifts)
        (.childCons leftBody leftRest) (.childCons rightBody rightRest)
  /-- A head child kept syntactically equal on both sides at ANY positive shift (binder children
  without an available shared domain stay fenced; this also keeps `refl` unconditional). -/
  | consEqualHigher {scope : Nat} {context : TypingContext profile scope}
      {previousShared : Option (RawTerm scope)}
      {headShift : Nat} {restShifts : List Nat}
      {sharedChild : RawTerm (scope + (headShift + 1))}
      {leftRest rightRest : RawTermChildren restShifts scope}
      (restRelated : ChildrenUnitEtaCong profile context none restShifts leftRest rightRest) :
      ChildrenUnitEtaCong profile context previousShared ((headShift + 1) :: restShifts)
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

/-- Children reflexivity: shared-head arms at every position, at ANY threading. -/
theorem ChildrenUnitEtaCong.refl {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {previousShared : Option (RawTerm scope)} :
    {shifts : List Nat} → (children : RawTermChildren shifts scope) →
      ChildrenUnitEtaCong profile context previousShared shifts children children
  | _, .childNil => .nil
  | _, @RawTermChildren.childCons _ 0 _ _headChild restChildren =>
      .consEqualZero (ChildrenUnitEtaCong.refl restChildren)
  | _, @RawTermChildren.childCons _ (_ + 1) _ _headChild restChildren =>
      .consEqualHigher (ChildrenUnitEtaCong.refl restChildren)

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
  | .trans leftToMiddle middleToRight =>
      .trans (DefEqUnitEtaCong.sym middleToRight) (DefEqUnitEtaCong.sym leftToMiddle)

/-- Children symmetry — every arm is symmetric at its own threading (the binder arm because the
domain is SHARED; a left-threading convention would break exactly here). -/
theorem ChildrenUnitEtaCong.sym {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {previousShared : Option (RawTerm scope)}
    {shifts : List Nat}
    {leftChildren rightChildren : RawTermChildren shifts scope}
    (related : ChildrenUnitEtaCong profile context previousShared shifts
      leftChildren rightChildren) :
    ChildrenUnitEtaCong profile context previousShared shifts rightChildren leftChildren :=
  match related with
  | .nil => .nil
  | .consZero headRelated restRelated =>
      .consZero (DefEqUnitEtaCong.sym headRelated) (ChildrenUnitEtaCong.sym restRelated)
  | .consEqualZero restRelated => .consEqualZero (ChildrenUnitEtaCong.sym restRelated)
  | .consBinder bodiesRelated restRelated =>
      .consBinder (DefEqUnitEtaCong.sym bodiesRelated) (ChildrenUnitEtaCong.sym restRelated)
  | .consEqualHigher restRelated => .consEqualHigher (ChildrenUnitEtaCong.sym restRelated)

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
        (Or.inl (NullaryDataValueTyped.unitValueTyped (unitVariableContext profile)))))
      (.consZero
        (.ofDefEq (.unitEta (Or.inr (unitVariableTyped profile))
          (Or.inl (NullaryDataValueTyped.unitValueTyped (unitVariableContext profile)))))
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
