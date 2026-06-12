import FX1Poly.Core.RawTermSubst0
import FX1Poly.Core.RawTermSubstPair
import FX1Poly.Core.RawTermWeaken

/-! # FX1Poly/Core/IotaRuleTable — reduction rules as DATA (the ι-rule table)

The operational twin of the typing rule tables (`typingRuleDescOf` /
`introRuleDescOf` / `elimRuleDescOf`): every β/ι reduction rule of the
kernel becomes one `IotaRuleDesc` VALUE — a two-level left-linear
pattern (eliminator head + firing constructor head in one child slot)
plus a reduct template drawn from a CLOSED template DSL.  Adding a new
ι-rule to the kernel becomes adding a row, not threading constructors
through every Step consumer.

## Maximal dependent wiring

The schema wires the DEPENDENT structure of every rule even where the
current kernel's reducts do not consume it, so future rows (W-types,
indexed families, observational identity, copatterns) fit without a
schema change:

  * **Motive**: every dependent-eliminator row declares `motiveSlot?`
    (the spine slot holding the motive); the binder arity of the motive
    is DERIVED from the generator table (`motiveBinderArity?`), never
    duplicated.  The template nodes `motiveInstantiatedWith` /
    `motiveInstantiatedWithPair` build `motive[arg]` / `motive[a, b]` —
    the dependent-elimination output shapes (`ElimRuleDesc.outputType`'s
    operational twin) — usable inside any reduct, including under fresh
    binders (instantiate at `boundVarAt`).
  * **Scrutinee**: derived FROM the spine (`scrutineeTermOf?`), never
    passed separately — incoherent inputs are unrepresentable.  The
    whole firing constructor is mentionable (`theScrutinee`), its
    children projectable (`scrutineeChildAt`), and its binder children
    substitutable (`substOneIntoScrutineeChild` /
    `substPairIntoScrutineeChild`).
  * **Binders in reducts**: interpretation is graded by a binder DEPTH;
    `underBinder` / `underPathBinder` wrap reducts in fresh λ / path-λ
    binders and `boundVarAt` references them, with all projections
    weakened on demand.  This is exactly the W-type-recursor shape
    `wRec (sup a f) ↝ step a f (λ x. wRec (f x))` — see the
    `wStyleRecursiveBinderDemoRule` adequacy equation.
  * **n-ary reassembly**: `reassembledReplacing` re-applies the row's
    own eliminator with ANY set of spine slots replaced — the recursion
    of `natElim`/`listElim` (scrutinee slot only) and the
    indexed-family shape (index slots change in recursive calls) in one
    node.  The eliminator payload is transported across binder depth by
    the fold engine's scope-invariance
    (`Generator.payload_scope_invariant_of_not_var`).

## The closed reduct-template DSL

Every reduct of every shipped rule (β, the 16 data/identity iotas, and
endpoint-β at `gen_pathApp`/`gen_pathLam`) is built from these nodes,
and the node set is closed under the known future row shapes:
projection, application chains, motive instantiation, n-ary eliminator
reassembly, one- and two-binder substitution from either the spine or
the scrutinee, and fresh-binder wrapping.

## Shift-erased child view

The interpreter walks a shift-tagged list view of children
(`ScopedChild`) instead of the shift-indexed spine, so slot access is
plain `Nat` indexing with shift checks done by full-enumeration `Nat`
matches — no `Eq.rec` casts anywhere, and everything reduces by iota on
concrete spines (the adequacy equations below close by `rfl`).  All
depth-weakening helpers return their input UNCHANGED at depth 0 (first
match arm), so the 18 shipped rows reduce exactly as written.

## The 18 rows + the GO gate

`iotaRuleTable` lists all 18 rules.  Rows 1–17 mirror the bespoke
`Step` constructors; row 18 (`pathBetaIotaRow`, endpoint-β) is the
first TABLE-NATIVE rule — it has NO bespoke `Step` constructor and goes
operationally live at the canonicality flip (IOTA-T9).  The per-row
adequacy theorems (`interpretTarget? = some <the rule's reduct>`, all
`rfl`) are this spike's GO gate, and every NEW node carries its own
demo adequacy equation (motive instantiation, whole-scrutinee echo,
two-binder scrutinee substitution, multi-slot reassembly, the W-style
under-binder recursion, path-binder wrapping, firing positive +
negative).

## Tier discipline (forward note)

Rows using only projection/application/substitution inherit the full
Tier-1 metatheory (SR / equivariance / firing / confluence) from the
generic template theorems (IOTA-T2..T6).  Rows whose reducts recurse
under `underBinder` or reassemble with grown arguments face the
DECIDABLE subterm-recursion SN check separately (IOTA-T8, Tier 2) — the
table never promises SN generically.

## Zero-axiom verification

Plain structural definitions (full-enumeration `Nat`/list matches, the
`Option` monad on concrete values), `cast` only through the
by-`cases`-`rfl` payload scope-invariance lemma (which vanishes on
every concrete row), and `rfl` equations throughout.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Gated per declaration in
`FX1PolyAudit/AuditIotaRuleTable.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## The shift-erased child view -/

/-- A spine child packaged with its binder shift — the shift-erased view
the template interpreter walks.  `childTerm` lives `binderShift` binders
below the parent scope. -/
structure ScopedChild (scope : Nat) where
  binderShift : Nat
  childTerm : RawTerm (scope + binderShift)

/-- Erase a shift-indexed children spine to its shift-tagged list view. -/
def RawTermChildren.toScopedChildren :
    {binderShifts : List Nat} → {scope : Nat} →
    RawTermChildren binderShifts scope → List (ScopedChild scope)
  | _, _, .childNil => []
  | _, _, .childCons childHead childTail =>
      ⟨_, childHead⟩ :: childTail.toScopedChildren

namespace ScopedChild

/-- Project the child as a parent-scope term — succeeds exactly when the
child sits at binder shift 0. -/
def atShiftZero? {scope : Nat} : ScopedChild scope → Option (RawTerm scope)
  | ⟨0, childTerm⟩ => some childTerm
  | ⟨_ + 1, _⟩ => none

/-- Project the child as a one-binder body — succeeds exactly at shift 1. -/
def atShiftOne? {scope : Nat} :
    ScopedChild scope → Option (RawTerm (scope + 1))
  | ⟨1, childTerm⟩ => some childTerm
  | ⟨0, _⟩ => none
  | ⟨_ + 2, _⟩ => none

/-- Project the child as a two-binder body — succeeds exactly at shift 2. -/
def atShiftTwo? {scope : Nat} :
    ScopedChild scope → Option (RawTerm (scope + 2))
  | ⟨2, childTerm⟩ => some childTerm
  | ⟨0, _⟩ => none
  | ⟨1, _⟩ => none
  | ⟨_ + 3, _⟩ => none

end ScopedChild

/-- Positional lookup in a scoped-children list (hand-rolled, Init-only). -/
def scopedChildAt? {scope : Nat} :
    List (ScopedChild scope) → Nat → Option (ScopedChild scope)
  | [], _ => none
  | headChild :: _, 0 => some headChild
  | _ :: restChildren, slot + 1 => scopedChildAt? restChildren slot

/-- The shift-erased children view of a cell term (total — every
`RawTerm` is a `mkGen` cell). -/
def RawTerm.scopedChildrenView {scope : Nat} :
    RawTerm scope → List (ScopedChild scope)
  | .mkGen _ _ children => children.toScopedChildren

/-- Positional lookup in a plain `Nat` list (hand-rolled, Init-only) —
used to DERIVE per-slot binder arities from the generator table instead
of duplicating them on rows. -/
def natListLookup? : List Nat → Nat → Option Nat
  | [], _ => none
  | shiftHead :: _, 0 => some shiftHead
  | _ :: restShifts, slot + 1 => natListLookup? restShifts slot

/-! ## Depth weakening — projections under template binders

Interpretation is graded by a binder DEPTH (how many fresh binders the
reduct template has introduced).  Every projection from the spine or
the scrutinee must be weakened by that depth.  Each helper returns its
input UNCHANGED at depth 0 (the first match arm fires by iota even on
symbolic terms), so the depth-0 rows reduce exactly as written. -/

/-- Weaken a parent-scope term under `depth` fresh template binders
(the new variables become indices `0 … depth-1`). -/
def RawTerm.weakenBy {scope : Nat} :
    (depth : Nat) → RawTerm scope → RawTerm (scope + depth)
  | 0, term => term
  | innerDepth + 1, term => RawTerm.weaken (RawTerm.weakenBy innerDepth term)

/-- Weaken a one-binder body under `depth` fresh template binders,
keeping the body's own binder innermost: the fresh variables are
inserted BETWEEN the body's binder and the original scope. -/
def RawTerm.weakenBodyUnderOneBinderBy {scope : Nat} :
    (depth : Nat) → RawTerm (scope + 1) → RawTerm (scope + depth + 1)
  | 0, body => body
  | innerDepth + 1, body =>
      RawTerm.rename (RawRenaming.lift RawRenaming.weaken)
        (RawTerm.weakenBodyUnderOneBinderBy innerDepth body)

/-- Weaken a two-binder body under `depth` fresh template binders,
keeping both of the body's own binders innermost. -/
def RawTerm.weakenBodyUnderTwoBindersBy {scope : Nat} :
    (depth : Nat) → RawTerm (scope + 2) → RawTerm (scope + depth + 2)
  | 0, body => body
  | innerDepth + 1, body =>
      RawTerm.rename (RawRenaming.lift (RawRenaming.lift RawRenaming.weaken))
        (RawTerm.weakenBodyUnderTwoBindersBy innerDepth body)

/-- Weaken a whole children spine under `depth` fresh template binders.
Each child is weakened UNDER its own binder shift — `RawTermChildren.weaken`
already lifts the weakening renaming through per-child shifts, so one
step is one shipped call. -/
def RawTermChildren.weakenSpineBy {binderShifts : List Nat} {scope : Nat} :
    (depth : Nat) → RawTermChildren binderShifts scope →
    RawTermChildren binderShifts (scope + depth)
  | 0, spine => spine
  | innerDepth + 1, spine =>
      RawTermChildren.weaken (RawTermChildren.weakenSpineBy innerDepth spine)

/-! ## Cast-free slot replacement on the typed spine -/

/-- Admit a parent-scope replacement into a slot of binder shift
`slotShift` — succeeds exactly when the shift is 0.  Taking the shift
EXPLICITLY keeps the definition cast-free: the `0` arm's return type
`RawTerm (scope + 0)` is definitionally `RawTerm scope`. -/
def replacementIntoShift? {scope : Nat} :
    (slotShift : Nat) → RawTerm scope → Option (RawTerm (scope + slotShift))
  | 0, replacement => some replacement
  | _ + 1, _ => none

/-- Replace the child at `slot` with a parent-scope term — succeeds
exactly when that slot's binder shift is 0 (every replaceable slot in
the table is shift-0).  Cast-free via `replacementIntoShift?`. -/
def RawTermChildren.replaceChildAt? :
    {binderShifts : List Nat} → {scope : Nat} →
    RawTermChildren binderShifts scope → Nat → RawTerm scope →
    Option (RawTermChildren binderShifts scope)
  | _, _, .childNil, _, _ => none
  | _, _, .childCons _ childTail, 0, replacement =>
      (replacementIntoShift? _ replacement).map (.childCons · childTail)
  | _, _, .childCons childHead childTail, slot + 1, replacement =>
      (childTail.replaceChildAt? slot replacement).map (.childCons childHead ·)

/-! ## The closed reduct-template DSL -/

mutual

/-- The CLOSED reduct-template DSL — every shipped β/ι reduct is built
from these node shapes, and the node set covers the known future row
shapes (see the module docstring).  Slot numbers refer to the
ELIMINATOR spine (`spine…`) or to the firing CONSTRUCTOR's own children
(`scrutinee…`).  Interpretation is graded by a binder DEPTH;
`underBinder`/`underPathBinder` increase it and `boundVarAt` references
the template-introduced binders (innermost = 0). -/
inductive ReductTemplate : Type where
  /-- A template-introduced binder (innermost = 0; must be < the current
      depth). -/
  | boundVarAt (binderIndex : Nat)
  /-- The eliminator-spine child at `slot` (must sit at binder shift 0),
      weakened to the current depth. -/
  | spineChildAt (slot : Nat)
  /-- The firing constructor's child at `slot` (must sit at shift 0),
      weakened to the current depth. -/
  | scrutineeChildAt (slot : Nat)
  /-- The whole firing scrutinee term, weakened to the current depth. -/
  | theScrutinee
  /-- The row's declared motive (a one-binder spine child at
      `motiveSlot?`) instantiated at the interpreted argument —
      `motive[arg]`, the dependent-elimination output shape. -/
  | motiveInstantiatedWith (argTemplate : ReductTemplate)
  /-- The row's declared TWO-binder motive (`idJ`-family) instantiated
      at the interpreted pair — `motive[inner, outer]` with `var 0`
      receiving the inner template. -/
  | motiveInstantiatedWithPair (innerTemplate outerTemplate : ReductTemplate)
  /-- Application `gen_app(fnTemplate, argTemplate)` — the applied-branch
      iotas (`optionMatch`/`eitherMatch` firing cases, `listElim` cons). -/
  | applicationOf (fnTemplate argTemplate : ReductTemplate)
  /-- The row's own eliminator re-applied with the listed spine slots
      replaced by interpreted templates — the recursion of the
      `natElim`/`natRec`/`listElim` step cases (scrutinee slot only) AND
      the indexed-family shape (index slots change too) in one node.
      The whole spine is weakened to the current depth; the payload is
      transported by scope invariance. -/
  | reassembledReplacing (replacements : SpineReplacements)
  /-- `subst0` of the one-binder SPINE child at `bodySlot` by the
      interpreted argument. -/
  | substOneIntoSpineChild (bodySlot : Nat) (argTemplate : ReductTemplate)
  /-- `subst0` of the one-binder SCRUTINEE child at `bodySlot` by the
      interpreted argument — β (`gen_lam` body) and endpoint-β
      (`gen_pathLam` body). -/
  | substOneIntoScrutineeChild (bodySlot : Nat) (argTemplate : ReductTemplate)
  /-- `substPair` of the two-binder SPINE child at `bodySlot`: `var 0`
      gets the inner template (the recursive call / IH), `var 1` the
      outer template (the predecessor) — the Nat recursor step cases. -/
  | substPairIntoSpineChild (bodySlot : Nat)
      (innerTemplate outerTemplate : ReductTemplate)
  /-- `substPair` of the two-binder SCRUTINEE child at `bodySlot` — the
      symmetric closure (future constructor heads with binder
      children). -/
  | substPairIntoScrutineeChild (bodySlot : Nat)
      (innerTemplate outerTemplate : ReductTemplate)
  /-- Wrap the body template in a fresh `gen_lam` binder (the domain
      annotation interprets OUTSIDE the new binder, the body one depth
      deeper) — the W-type-recursor reduct shape. -/
  | underBinder (domainTemplate bodyTemplate : ReductTemplate)
  /-- Wrap the body template in a fresh `gen_pathLam` interval binder. -/
  | underPathBinder (bodyTemplate : ReductTemplate)

/-- A list of (spine slot, replacement template) pairs for
`reassembledReplacing` — hand-rolled as a mutual sibling (not a nested
`List`) to keep recursion plainly structural and propext-clean. -/
inductive SpineReplacements : Type where
  | replaceNil
  | replaceCons (slot : Nat) (replacementTemplate : ReductTemplate)
      (restReplacements : SpineReplacements)

end

/-! ## The rule descriptor -/

/-- One β/ι rewrite rule as DATA: a two-level left-linear pattern — the
eliminator head, which spine slot fires, the constructor head that fires
it — plus the DEPENDENT wiring (which spine slot is the motive) and the
reduct template.  The orthogonality discipline (eliminator heads
disjoint from constructor heads, keys pairwise distinct) is what makes
the whole table confluent generically. -/
structure IotaRuleDesc where
  elimGenerator : Generator
  scrutineeSlot : Nat
  scrutineeHead : Generator
  /-- The spine slot holding the dependent motive, when the eliminator
      has one (`none` for β / endpoint-β, whose redexes carry no
      motive).  Its binder arity is DERIVED from the generator table —
      see `motiveBinderArity?` — never duplicated here. -/
  motiveSlot? : Option Nat := none
  target : ReductTemplate

namespace IotaRuleDesc

/-- The binder arity of the row's motive, read off the generator
table — `some 1` for the unary-motive eliminators, `some 2` for the
`idJ` family, `none` when the row has no motive.  Single source of
truth: rows never restate what `Generator.binderShifts` already says. -/
def motiveBinderArity? (rule : IotaRuleDesc) : Option Nat :=
  rule.motiveSlot?.bind (natListLookup? rule.elimGenerator.binderShifts)

/-- The binder shift of the row's scrutinee slot per the generator
table (every shipped row sits at shift 0 — the orthogonality
certificate re-decides this per row at IOTA-T5). -/
def scrutineeSlotShift? (rule : IotaRuleDesc) : Option Nat :=
  natListLookup? rule.elimGenerator.binderShifts rule.scrutineeSlot

/-- The firing scrutinee term, DERIVED from the spine (slot lookup at
shift 0) — never passed separately, so interpreter inputs cannot
disagree with the spine. -/
def scrutineeTermOf? (rule : IotaRuleDesc) {scope : Nat}
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    Option (RawTerm scope) :=
  (scopedChildAt? spine.toScopedChildren rule.scrutineeSlot).bind
    ScopedChild.atShiftZero?

/-- The firing scrutinee's shift-erased children view, derived from the
spine. -/
def scrutineeChildrenOf? (rule : IotaRuleDesc) {scope : Nat}
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    Option (List (ScopedChild scope)) :=
  (rule.scrutineeTermOf? spine).map RawTerm.scopedChildrenView

/-- Transport the matched eliminator payload to the current binder
depth.  Non-`gen_var` payload types are scope-invariant
(`Generator.payload_scope_invariant_of_not_var`, by-`cases`-`rfl`), so
the `cast` vanishes on every concrete row; a `gen_var`-headed rule (no
such row exists — variables eliminate nothing) reassembles to `none`. -/
def elimPayloadAtDepth? (rule : IotaRuleDesc) {scope : Nat} (depth : Nat)
    (elimPayload : rule.elimGenerator.payload scope) :
    Option (rule.elimGenerator.payload (scope + depth)) :=
  if isVarHead : rule.elimGenerator = .gen_var then none
  else
    some (cast
      (Generator.payload_scope_invariant_of_not_var isVarHead
        scope (scope + depth))
      elimPayload)

end IotaRuleDesc

/-! ## The template interpreter -/

mutual

/-- Interpret a reduct template against a rule's eliminator spine (with
its matched payload) at a binder depth.  The scrutinee and its children
are DERIVED from the spine at every scrutinee leaf.  Total on the
table's rows; `none` on shape mismatches.  All arms reduce by iota on
concrete spines — the adequacy equations below are `rfl`. -/
def IotaRuleDesc.interpretTemplate? (rule : IotaRuleDesc) {scope : Nat}
    (elimPayload : rule.elimGenerator.payload scope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    (depth : Nat) → ReductTemplate → Option (RawTerm (scope + depth))
  | depth, .boundVarAt binderIndex =>
      if isTemplateBound : binderIndex < depth then
        some (.mkGen .gen_var
          ⟨binderIndex,
            Nat.lt_of_lt_of_le isTemplateBound (Nat.le_add_left depth scope)⟩
          .childNil)
      else none
  | depth, .spineChildAt slot => do
      let spineChild ← scopedChildAt? spine.toScopedChildren slot
      let childTerm ← spineChild.atShiftZero?
      some (RawTerm.weakenBy depth childTerm)
  | depth, .scrutineeChildAt slot => do
      let scrutineeChildren ← rule.scrutineeChildrenOf? spine
      let scrutineeChild ← scopedChildAt? scrutineeChildren slot
      let childTerm ← scrutineeChild.atShiftZero?
      some (RawTerm.weakenBy depth childTerm)
  | depth, .theScrutinee => do
      let scrutineeTerm ← rule.scrutineeTermOf? spine
      some (RawTerm.weakenBy depth scrutineeTerm)
  | depth, .motiveInstantiatedWith argTemplate => do
      let motiveSlot ← rule.motiveSlot?
      let argTerm ← rule.interpretTemplate? elimPayload spine depth argTemplate
      let motiveChild ← scopedChildAt? spine.toScopedChildren motiveSlot
      let motiveBody ← motiveChild.atShiftOne?
      some (RawTerm.subst0
        (RawTerm.weakenBodyUnderOneBinderBy depth motiveBody) argTerm)
  | depth, .motiveInstantiatedWithPair innerTemplate outerTemplate => do
      let motiveSlot ← rule.motiveSlot?
      let innerTerm ←
        rule.interpretTemplate? elimPayload spine depth innerTemplate
      let outerTerm ←
        rule.interpretTemplate? elimPayload spine depth outerTemplate
      let motiveChild ← scopedChildAt? spine.toScopedChildren motiveSlot
      let motiveBody ← motiveChild.atShiftTwo?
      some (RawTerm.substPair
        (RawTerm.weakenBodyUnderTwoBindersBy depth motiveBody)
        innerTerm outerTerm)
  | depth, .applicationOf fnTemplate argTemplate => do
      let fnTerm ← rule.interpretTemplate? elimPayload spine depth fnTemplate
      let argTerm ← rule.interpretTemplate? elimPayload spine depth argTemplate
      some (.mkGen .gen_app ()
        (.childCons fnTerm (.childCons argTerm .childNil)))
  | depth, .reassembledReplacing replacements => do
      let payloadAtDepth ← rule.elimPayloadAtDepth? depth elimPayload
      let replacedSpine ←
        rule.interpretReplacements? elimPayload spine depth replacements
          (RawTermChildren.weakenSpineBy depth spine)
      some (.mkGen rule.elimGenerator payloadAtDepth replacedSpine)
  | depth, .substOneIntoSpineChild bodySlot argTemplate => do
      let argTerm ← rule.interpretTemplate? elimPayload spine depth argTemplate
      let bodyChild ← scopedChildAt? spine.toScopedChildren bodySlot
      let bodyTerm ← bodyChild.atShiftOne?
      some (RawTerm.subst0
        (RawTerm.weakenBodyUnderOneBinderBy depth bodyTerm) argTerm)
  | depth, .substOneIntoScrutineeChild bodySlot argTemplate => do
      let argTerm ← rule.interpretTemplate? elimPayload spine depth argTemplate
      let scrutineeChildren ← rule.scrutineeChildrenOf? spine
      let bodyChild ← scopedChildAt? scrutineeChildren bodySlot
      let bodyTerm ← bodyChild.atShiftOne?
      some (RawTerm.subst0
        (RawTerm.weakenBodyUnderOneBinderBy depth bodyTerm) argTerm)
  | depth, .substPairIntoSpineChild bodySlot innerTemplate outerTemplate => do
      let innerTerm ←
        rule.interpretTemplate? elimPayload spine depth innerTemplate
      let outerTerm ←
        rule.interpretTemplate? elimPayload spine depth outerTemplate
      let bodyChild ← scopedChildAt? spine.toScopedChildren bodySlot
      let bodyTerm ← bodyChild.atShiftTwo?
      some (RawTerm.substPair
        (RawTerm.weakenBodyUnderTwoBindersBy depth bodyTerm)
        innerTerm outerTerm)
  | depth, .substPairIntoScrutineeChild bodySlot innerTemplate outerTemplate => do
      let innerTerm ←
        rule.interpretTemplate? elimPayload spine depth innerTemplate
      let outerTerm ←
        rule.interpretTemplate? elimPayload spine depth outerTemplate
      let scrutineeChildren ← rule.scrutineeChildrenOf? spine
      let bodyChild ← scopedChildAt? scrutineeChildren bodySlot
      let bodyTerm ← bodyChild.atShiftTwo?
      some (RawTerm.substPair
        (RawTerm.weakenBodyUnderTwoBindersBy depth bodyTerm)
        innerTerm outerTerm)
  | depth, .underBinder domainTemplate bodyTemplate => do
      let domainTerm ←
        rule.interpretTemplate? elimPayload spine depth domainTemplate
      let bodyTerm ←
        rule.interpretTemplate? elimPayload spine (depth + 1) bodyTemplate
      some (.mkGen .gen_lam ()
        (.childCons domainTerm (.childCons bodyTerm .childNil)))
  | depth, .underPathBinder bodyTemplate => do
      let bodyTerm ←
        rule.interpretTemplate? elimPayload spine (depth + 1) bodyTemplate
      some (.mkGen .gen_pathLam () (.childCons bodyTerm .childNil))

/-- Interpret a replacement list left-to-right into the (already
depth-weakened) reassembly spine. -/
def IotaRuleDesc.interpretReplacements? (rule : IotaRuleDesc) {scope : Nat}
    (elimPayload : rule.elimGenerator.payload scope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    (depth : Nat) → SpineReplacements →
    RawTermChildren rule.elimGenerator.binderShifts (scope + depth) →
    Option (RawTermChildren rule.elimGenerator.binderShifts (scope + depth))
  | _, .replaceNil, reassemblySpine => some reassemblySpine
  | depth, .replaceCons slot replacementTemplate restReplacements,
      reassemblySpine => do
      let replacement ←
        rule.interpretTemplate? elimPayload spine depth replacementTemplate
      let replacedSpine ← reassemblySpine.replaceChildAt? slot replacement
      rule.interpretReplacements? elimPayload spine depth restReplacements
        replacedSpine

end

/-- The top-level row interpreter: interpret the row's own target at
depth 0. -/
def IotaRuleDesc.interpretTarget? (rule : IotaRuleDesc) {scope : Nat}
    (elimPayload : rule.elimGenerator.payload scope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    Option (RawTerm scope) :=
  rule.interpretTemplate? elimPayload spine 0 rule.target

/-- The firing dispatcher: interpret the row's reduct exactly when the
derived scrutinee's head generator is the row's declared firing head —
the two-level left-linear pattern test.  The IOTA-T4 generic firing
soundness/completeness theorems are stated against THIS function. -/
def IotaRuleDesc.firesOn? (rule : IotaRuleDesc) {scope : Nat}
    (elimPayload : rule.elimGenerator.payload scope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    Option (RawTerm scope) := do
  let scrutineeTerm ← rule.scrutineeTermOf? spine
  match scrutineeTerm with
  | .mkGen scrutineeGenerator _ _ =>
    if scrutineeGenerator = rule.scrutineeHead then
      rule.interpretTarget? elimPayload spine
    else none

/-! ## The 18 rows -/

/-- β: `app(lam(domainAnn, body), arg) ↝ subst0 body arg`. -/
def betaIotaRow : IotaRuleDesc where
  elimGenerator := .gen_app
  scrutineeSlot := 0
  scrutineeHead := .gen_lam
  motiveSlot? := none
  target := .substOneIntoScrutineeChild 1 (.spineChildAt 1)

/-- `boolElim … boolTrue ↝ thenBranch` (spine slot 1). -/
def boolTrueIotaRow : IotaRuleDesc where
  elimGenerator := .gen_boolElim
  scrutineeSlot := 3
  scrutineeHead := .gen_boolTrue
  motiveSlot? := some 0
  target := .spineChildAt 1

/-- `boolElim … boolFalse ↝ elseBranch` (spine slot 2). -/
def boolFalseIotaRow : IotaRuleDesc where
  elimGenerator := .gen_boolElim
  scrutineeSlot := 3
  scrutineeHead := .gen_boolFalse
  motiveSlot? := some 0
  target := .spineChildAt 2

/-- `fst(pair(a, b)) ↝ a` (non-dependent projection — no motive slot in
the current generator table). -/
def fstPairIotaRow : IotaRuleDesc where
  elimGenerator := .gen_fst
  scrutineeSlot := 0
  scrutineeHead := .gen_pair
  motiveSlot? := none
  target := .scrutineeChildAt 0

/-- `snd(pair(a, b)) ↝ b`. -/
def sndPairIotaRow : IotaRuleDesc where
  elimGenerator := .gen_snd
  scrutineeSlot := 0
  scrutineeHead := .gen_pair
  motiveSlot? := none
  target := .scrutineeChildAt 1

/-- `natElim … natZero ↝ zeroBranch`. -/
def natElimZeroIotaRow : IotaRuleDesc where
  elimGenerator := .gen_natElim
  scrutineeSlot := 3
  scrutineeHead := .gen_natZero
  motiveSlot? := some 0
  target := .spineChildAt 1

/-- `natRec … natZero ↝ zeroBranch`. -/
def natRecZeroIotaRow : IotaRuleDesc where
  elimGenerator := .gen_natRec
  scrutineeSlot := 3
  scrutineeHead := .gen_natZero
  motiveSlot? := some 0
  target := .spineChildAt 1

/-- `natElim … natSucc(pred) ↝ substPair succBranch (natElim … pred) pred`
— the recursive step case: `var 0` gets the recursive call (reassembly
of the eliminator with the scrutinee slot replaced by the predecessor),
`var 1` the predecessor. -/
def natElimSuccIotaRow : IotaRuleDesc where
  elimGenerator := .gen_natElim
  scrutineeSlot := 3
  scrutineeHead := .gen_natSucc
  motiveSlot? := some 0
  target := .substPairIntoSpineChild 2
    (.reassembledReplacing (.replaceCons 3 (.scrutineeChildAt 0) .replaceNil))
    (.scrutineeChildAt 0)

/-- `natRec … natSucc(pred)` — the dependent-recursor twin. -/
def natRecSuccIotaRow : IotaRuleDesc where
  elimGenerator := .gen_natRec
  scrutineeSlot := 3
  scrutineeHead := .gen_natSucc
  motiveSlot? := some 0
  target := .substPairIntoSpineChild 2
    (.reassembledReplacing (.replaceCons 3 (.scrutineeChildAt 0) .replaceNil))
    (.scrutineeChildAt 0)

/-- `listElim … listNil ↝ nilBranch`. -/
def listElimNilIotaRow : IotaRuleDesc where
  elimGenerator := .gen_listElim
  scrutineeSlot := 3
  scrutineeHead := .gen_listNil
  motiveSlot? := some 0
  target := .spineChildAt 1

/-- `listElim … listCons(h, t) ↝ consBranch h t (listElim … t)` — the
applied-branch + reassembly step case. -/
def listElimConsIotaRow : IotaRuleDesc where
  elimGenerator := .gen_listElim
  scrutineeSlot := 3
  scrutineeHead := .gen_listCons
  motiveSlot? := some 0
  target := .applicationOf
    (.applicationOf
      (.applicationOf (.spineChildAt 2) (.scrutineeChildAt 0))
      (.scrutineeChildAt 1))
    (.reassembledReplacing (.replaceCons 3 (.scrutineeChildAt 1) .replaceNil))

/-- `optionMatch … optionNone ↝ noneBranch`. -/
def optionMatchNoneIotaRow : IotaRuleDesc where
  elimGenerator := .gen_optionMatch
  scrutineeSlot := 3
  scrutineeHead := .gen_optionNone
  motiveSlot? := some 0
  target := .spineChildAt 1

/-- `optionMatch … optionSome(v) ↝ someBranch v`. -/
def optionMatchSomeIotaRow : IotaRuleDesc where
  elimGenerator := .gen_optionMatch
  scrutineeSlot := 3
  scrutineeHead := .gen_optionSome
  motiveSlot? := some 0
  target := .applicationOf (.spineChildAt 2) (.scrutineeChildAt 0)

/-- `eitherMatch … eitherInl(v) ↝ leftBranch v`. -/
def eitherMatchInlIotaRow : IotaRuleDesc where
  elimGenerator := .gen_eitherMatch
  scrutineeSlot := 3
  scrutineeHead := .gen_eitherInl
  motiveSlot? := some 0
  target := .applicationOf (.spineChildAt 1) (.scrutineeChildAt 0)

/-- `eitherMatch … eitherInr(v) ↝ rightBranch v`. -/
def eitherMatchInrIotaRow : IotaRuleDesc where
  elimGenerator := .gen_eitherMatch
  scrutineeSlot := 3
  scrutineeHead := .gen_eitherInr
  motiveSlot? := some 0
  target := .applicationOf (.spineChildAt 2) (.scrutineeChildAt 0)

/-- `idJ … refl ↝ baseCase` (two-binder motive at slot 0). -/
def idJReflIotaRow : IotaRuleDesc where
  elimGenerator := .gen_idJ
  scrutineeSlot := 2
  scrutineeHead := .gen_refl
  motiveSlot? := some 0
  target := .spineChildAt 1

/-- `idStrictRec … refl ↝ baseCase`. -/
def idStrictRecReflIotaRow : IotaRuleDesc where
  elimGenerator := .gen_idStrictRec
  scrutineeSlot := 2
  scrutineeHead := .gen_refl
  motiveSlot? := some 0
  target := .spineChildAt 1

/-- Endpoint β: `pathApp(pathLam(body), arg) ↝ subst0 body arg` — the
FIRST TABLE-NATIVE rule (no bespoke `Step` constructor; goes
operationally live at the canonicality flip).  `gen_pathLam` carries no
domain annotation, so the body is its scrutinee child 0. -/
def pathBetaIotaRow : IotaRuleDesc where
  elimGenerator := .gen_pathApp
  scrutineeSlot := 0
  scrutineeHead := .gen_pathLam
  motiveSlot? := none
  target := .substOneIntoScrutineeChild 0 (.spineChildAt 1)

/-- The full ι-rule table: β + the 16 legacy data/identity iotas + the
table-native endpoint-β.  Key discipline (decided generically at
IOTA-T5): `(elimGenerator, scrutineeHead)` pairs are pairwise distinct,
and no scrutinee head is an eliminator root — the orthogonality
certificate. -/
def iotaRuleTable : List IotaRuleDesc :=
  [ betaIotaRow
  , boolTrueIotaRow, boolFalseIotaRow
  , fstPairIotaRow, sndPairIotaRow
  , natElimZeroIotaRow, natRecZeroIotaRow
  , natElimSuccIotaRow, natRecSuccIotaRow
  , listElimNilIotaRow, listElimConsIotaRow
  , optionMatchNoneIotaRow, optionMatchSomeIotaRow
  , eitherMatchInlIotaRow, eitherMatchInrIotaRow
  , idJReflIotaRow, idStrictRecReflIotaRow
  , pathBetaIotaRow ]

/-! ## Adequacy — the GO gate: every row interprets to the rule's exact
reduct, definitionally.  Statements use the SAME reduct expressions as
the bespoke `Step` constructors (where those exist), so the IOTA-T1
adequacy against `Step` is substitution into these equations.  The
scrutinee is DERIVED from the spine — no second argument. -/

theorem betaIotaRow_interpretsTarget {scope : Nat}
    (domainAnn : RawTerm scope) (body : RawTerm (scope + 1))
    (arg : RawTerm scope) :
    betaIotaRow.interpretTarget? ()
      (.childCons
        (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
        (.childCons arg .childNil))
    = some (RawTerm.subst0 body arg) := rfl

theorem boolTrueIotaRow_interpretsTarget {scope : Nat}
    (motive : RawTerm (scope + 1)) (thenBranch elseBranch : RawTerm scope) :
    boolTrueIotaRow.interpretTarget? ()
      (.childCons motive
        (.childCons thenBranch
          (.childCons elseBranch
            (.childCons (.mkGen .gen_boolTrue () .childNil) .childNil))))
    = some thenBranch := rfl

theorem boolFalseIotaRow_interpretsTarget {scope : Nat}
    (motive : RawTerm (scope + 1)) (thenBranch elseBranch : RawTerm scope) :
    boolFalseIotaRow.interpretTarget? ()
      (.childCons motive
        (.childCons thenBranch
          (.childCons elseBranch
            (.childCons (.mkGen .gen_boolFalse () .childNil) .childNil))))
    = some elseBranch := rfl

theorem fstPairIotaRow_interpretsTarget {scope : Nat}
    (firstValue secondValue : RawTerm scope) :
    fstPairIotaRow.interpretTarget? ()
      (.childCons
        (.mkGen .gen_pair ()
          (.childCons firstValue (.childCons secondValue .childNil)))
        .childNil)
    = some firstValue := rfl

theorem sndPairIotaRow_interpretsTarget {scope : Nat}
    (firstValue secondValue : RawTerm scope) :
    sndPairIotaRow.interpretTarget? ()
      (.childCons
        (.mkGen .gen_pair ()
          (.childCons firstValue (.childCons secondValue .childNil)))
        .childNil)
    = some secondValue := rfl

theorem natElimZeroIotaRow_interpretsTarget {scope : Nat}
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) :
    natElimZeroIotaRow.interpretTarget? ()
      (.childCons motive
        (.childCons zeroBranch
          (.childCons succBranch
            (.childCons (.mkGen .gen_natZero () .childNil) .childNil))))
    = some zeroBranch := rfl

theorem natRecZeroIotaRow_interpretsTarget {scope : Nat}
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) :
    natRecZeroIotaRow.interpretTarget? ()
      (.childCons motive
        (.childCons zeroBranch
          (.childCons succBranch
            (.childCons (.mkGen .gen_natZero () .childNil) .childNil))))
    = some zeroBranch := rfl

theorem natElimSuccIotaRow_interpretsTarget {scope : Nat}
    (motive : RawTerm (scope + 1))
    (zeroBranch predecessor : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) :
    natElimSuccIotaRow.interpretTarget? ()
      (.childCons motive
        (.childCons zeroBranch
          (.childCons succBranch
            (.childCons
              (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
              .childNil))))
    = some (RawTerm.subst
        (RawTermSubst.cons
          (.mkGen .gen_natElim ()
            (.childCons motive
              (.childCons zeroBranch
                (.childCons succBranch
                  (.childCons predecessor .childNil)))))
          (RawTermSubst.singleton predecessor))
        succBranch) := rfl

theorem natRecSuccIotaRow_interpretsTarget {scope : Nat}
    (motive : RawTerm (scope + 1))
    (zeroBranch predecessor : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) :
    natRecSuccIotaRow.interpretTarget? ()
      (.childCons motive
        (.childCons zeroBranch
          (.childCons succBranch
            (.childCons
              (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
              .childNil))))
    = some (RawTerm.subst
        (RawTermSubst.cons
          (.mkGen .gen_natRec ()
            (.childCons motive
              (.childCons zeroBranch
                (.childCons succBranch
                  (.childCons predecessor .childNil)))))
          (RawTermSubst.singleton predecessor))
        succBranch) := rfl

theorem listElimNilIotaRow_interpretsTarget {scope : Nat}
    (motive : RawTerm (scope + 1)) (nilBranch consBranch : RawTerm scope) :
    listElimNilIotaRow.interpretTarget? ()
      (.childCons motive
        (.childCons nilBranch
          (.childCons consBranch
            (.childCons (.mkGen .gen_listNil () .childNil) .childNil))))
    = some nilBranch := rfl

theorem listElimConsIotaRow_interpretsTarget {scope : Nat}
    (motive : RawTerm (scope + 1))
    (nilBranch consBranch headValue tailValue : RawTerm scope) :
    listElimConsIotaRow.interpretTarget? ()
      (.childCons motive
        (.childCons nilBranch
          (.childCons consBranch
            (.childCons
              (.mkGen .gen_listCons ()
                (.childCons headValue (.childCons tailValue .childNil)))
              .childNil))))
    = some (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons consBranch (.childCons headValue .childNil)))
              (.childCons tailValue .childNil)))
          (.childCons
            (.mkGen .gen_listElim ()
              (.childCons motive
                (.childCons nilBranch
                  (.childCons consBranch
                    (.childCons tailValue .childNil)))))
            .childNil))) := rfl

theorem optionMatchNoneIotaRow_interpretsTarget {scope : Nat}
    (motive : RawTerm (scope + 1)) (noneBranch someBranch : RawTerm scope) :
    optionMatchNoneIotaRow.interpretTarget? ()
      (.childCons motive
        (.childCons noneBranch
          (.childCons someBranch
            (.childCons (.mkGen .gen_optionNone () .childNil) .childNil))))
    = some noneBranch := rfl

theorem optionMatchSomeIotaRow_interpretsTarget {scope : Nat}
    (motive : RawTerm (scope + 1))
    (noneBranch someBranch value : RawTerm scope) :
    optionMatchSomeIotaRow.interpretTarget? ()
      (.childCons motive
        (.childCons noneBranch
          (.childCons someBranch
            (.childCons
              (.mkGen .gen_optionSome () (.childCons value .childNil))
              .childNil))))
    = some (.mkGen .gen_app ()
        (.childCons someBranch (.childCons value .childNil))) := rfl

theorem eitherMatchInlIotaRow_interpretsTarget {scope : Nat}
    (motive : RawTerm (scope + 1))
    (leftBranch rightBranch value : RawTerm scope) :
    eitherMatchInlIotaRow.interpretTarget? ()
      (.childCons motive
        (.childCons leftBranch
          (.childCons rightBranch
            (.childCons
              (.mkGen .gen_eitherInl () (.childCons value .childNil))
              .childNil))))
    = some (.mkGen .gen_app ()
        (.childCons leftBranch (.childCons value .childNil))) := rfl

theorem eitherMatchInrIotaRow_interpretsTarget {scope : Nat}
    (motive : RawTerm (scope + 1))
    (leftBranch rightBranch value : RawTerm scope) :
    eitherMatchInrIotaRow.interpretTarget? ()
      (.childCons motive
        (.childCons leftBranch
          (.childCons rightBranch
            (.childCons
              (.mkGen .gen_eitherInr () (.childCons value .childNil))
              .childNil))))
    = some (.mkGen .gen_app ()
        (.childCons rightBranch (.childCons value .childNil))) := rfl

theorem idJReflIotaRow_interpretsTarget {scope : Nat}
    (motive : RawTerm (scope + 2))
    (baseCase rawWitness : RawTerm scope) :
    idJReflIotaRow.interpretTarget? ()
      (.childCons motive
        (.childCons baseCase
          (.childCons
            (.mkGen .gen_refl () (.childCons rawWitness .childNil))
            .childNil)))
    = some baseCase := rfl

theorem idStrictRecReflIotaRow_interpretsTarget {scope : Nat}
    (motive : RawTerm (scope + 2))
    (baseCase rawWitness : RawTerm scope) :
    idStrictRecReflIotaRow.interpretTarget? ()
      (.childCons motive
        (.childCons baseCase
          (.childCons
            (.mkGen .gen_refl () (.childCons rawWitness .childNil))
            .childNil)))
    = some baseCase := rfl

/-- The TABLE-NATIVE row's adequacy: endpoint-β interprets to exactly the
substitution reduct — proved without any bespoke `Step` constructor. -/
theorem pathBetaIotaRow_interpretsTarget {scope : Nat}
    (body : RawTerm (scope + 1)) (arg : RawTerm scope) :
    pathBetaIotaRow.interpretTarget? ()
      (.childCons
        (.mkGen .gen_pathLam () (.childCons body .childNil))
        (.childCons arg .childNil))
    = some (RawTerm.subst0 body arg) := rfl

/-- Table size pin: 18 rows (β + 16 legacy iotas + table-native
endpoint-β).  A permanent stale-count guard in the HON-9 style. -/
theorem iotaRuleTable_length : iotaRuleTable.length = 18 := rfl

/-! ## Dependent-wiring pins — the motive metadata is DERIVED, not
restated: arity 1 for the unary-motive eliminators, arity 2 for the
`idJ` family, `none` for β / endpoint-β / the non-dependent
projections.  Every shipped scrutinee slot sits at binder shift 0. -/

theorem boolTrueIotaRow_motiveArity :
    boolTrueIotaRow.motiveBinderArity? = some 1 := rfl

theorem natElimSuccIotaRow_motiveArity :
    natElimSuccIotaRow.motiveBinderArity? = some 1 := rfl

theorem listElimConsIotaRow_motiveArity :
    listElimConsIotaRow.motiveBinderArity? = some 1 := rfl

theorem idJReflIotaRow_motiveArity :
    idJReflIotaRow.motiveBinderArity? = some 2 := rfl

theorem idStrictRecReflIotaRow_motiveArity :
    idStrictRecReflIotaRow.motiveBinderArity? = some 2 := rfl

theorem betaIotaRow_motiveArity :
    betaIotaRow.motiveBinderArity? = none := rfl

theorem pathBetaIotaRow_motiveArity :
    pathBetaIotaRow.motiveBinderArity? = none := rfl

theorem betaIotaRow_scrutineeShift :
    betaIotaRow.scrutineeSlotShift? = some 0 := rfl

theorem natElimSuccIotaRow_scrutineeShift :
    natElimSuccIotaRow.scrutineeSlotShift? = some 0 := rfl

theorem idJReflIotaRow_scrutineeShift :
    idJReflIotaRow.scrutineeSlotShift? = some 0 := rfl

/-! ## New-node demo adequacy — each maximal-wiring node proves its
expressiveness with an `rfl` equation on a synthetic rule (these rules
are NOT table rows; they witness that the DSL already expresses the
future row shapes). -/

/-- Demo rule: the whole-scrutinee echo (`theScrutinee`). -/
def scrutineeEchoDemoRule : IotaRuleDesc where
  elimGenerator := .gen_fst
  scrutineeSlot := 0
  scrutineeHead := .gen_pair
  motiveSlot? := none
  target := .theScrutinee

/-- `theScrutinee` interprets to the firing constructor itself. -/
theorem scrutineeEchoDemoRule_interpretsTarget {scope : Nat}
    (firstValue secondValue : RawTerm scope) :
    scrutineeEchoDemoRule.interpretTarget? ()
      (.childCons
        (.mkGen .gen_pair ()
          (.childCons firstValue (.childCons secondValue .childNil)))
        .childNil)
    = some (.mkGen .gen_pair ()
        (.childCons firstValue (.childCons secondValue .childNil))) := rfl

/-- Demo rule: unary-motive instantiation at the scrutinee —
`motive[natZero]`, the dependent-elimination OUTPUT TYPE shape of the
`natElim` zero case (the operational twin of `ElimRuleDesc.outputType`,
the IOTA-T7 pairing readiness witness). -/
def natElimMotiveAtScrutineeDemoRule : IotaRuleDesc where
  elimGenerator := .gen_natElim
  scrutineeSlot := 3
  scrutineeHead := .gen_natZero
  motiveSlot? := some 0
  target := .motiveInstantiatedWith .theScrutinee

/-- `motiveInstantiatedWith` builds `subst0 motive scrutinee`. -/
theorem natElimMotiveAtScrutineeDemoRule_interpretsTarget {scope : Nat}
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) :
    natElimMotiveAtScrutineeDemoRule.interpretTarget? ()
      (.childCons motive
        (.childCons zeroBranch
          (.childCons succBranch
            (.childCons (.mkGen .gen_natZero () .childNil) .childNil))))
    = some (RawTerm.subst0 motive (.mkGen .gen_natZero () .childNil)) := rfl

/-- Demo rule: TWO-binder motive instantiation — `motive[refl(a), a]`,
the `idJ` dependent output shape (`var 0` receives the path, `var 1`
the endpoint). -/
def idJMotivePairDemoRule : IotaRuleDesc where
  elimGenerator := .gen_idJ
  scrutineeSlot := 2
  scrutineeHead := .gen_refl
  motiveSlot? := some 0
  target := .motiveInstantiatedWithPair .theScrutinee (.scrutineeChildAt 0)

/-- `motiveInstantiatedWithPair` builds `substPair motive path endpoint`. -/
theorem idJMotivePairDemoRule_interpretsTarget {scope : Nat}
    (motive : RawTerm (scope + 2))
    (baseCase rawWitness : RawTerm scope) :
    idJMotivePairDemoRule.interpretTarget? ()
      (.childCons motive
        (.childCons baseCase
          (.childCons
            (.mkGen .gen_refl () (.childCons rawWitness .childNil))
            .childNil)))
    = some (RawTerm.substPair motive
        (.mkGen .gen_refl () (.childCons rawWitness .childNil))
        rawWitness) := rfl

/-- Demo rule: two-binder substitution into a SCRUTINEE child — the
symmetric closure node, exercised with a `natElim`-headed scrutinee
(its slot-2 child is the only shipped two-binder child shape). -/
def scrutineeTwoBinderSubstDemoRule : IotaRuleDesc where
  elimGenerator := .gen_fst
  scrutineeSlot := 0
  scrutineeHead := .gen_natElim
  motiveSlot? := none
  target := .substPairIntoScrutineeChild 2
    (.scrutineeChildAt 1) (.scrutineeChildAt 1)

/-- `substPairIntoScrutineeChild` builds `substPair` of the scrutinee's
two-binder child. -/
theorem scrutineeTwoBinderSubstDemoRule_interpretsTarget {scope : Nat}
    (motive : RawTerm (scope + 1)) (zeroBranch scrutinee : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) :
    scrutineeTwoBinderSubstDemoRule.interpretTarget? ()
      (.childCons
        (.mkGen .gen_natElim ()
          (.childCons motive
            (.childCons zeroBranch
              (.childCons succBranch
                (.childCons scrutinee .childNil)))))
        .childNil)
    = some (RawTerm.substPair succBranch zeroBranch zeroBranch) := rfl

/-- Demo rule: MULTI-slot reassembly — the indexed-family recursion
shape, where a recursive call rewrites an index slot (here slot 1) AND
the scrutinee slot (slot 3) in one reassembly. -/
def natElimMultiSlotReassemblyDemoRule : IotaRuleDesc where
  elimGenerator := .gen_natElim
  scrutineeSlot := 3
  scrutineeHead := .gen_natSucc
  motiveSlot? := some 0
  target := .reassembledReplacing
    (.replaceCons 1 (.scrutineeChildAt 0)
      (.replaceCons 3 (.scrutineeChildAt 0) .replaceNil))

/-- `reassembledReplacing` rewrites BOTH listed slots in the
re-applied eliminator. -/
theorem natElimMultiSlotReassemblyDemoRule_interpretsTarget {scope : Nat}
    (motive : RawTerm (scope + 1))
    (zeroBranch predecessor : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) :
    natElimMultiSlotReassemblyDemoRule.interpretTarget? ()
      (.childCons motive
        (.childCons zeroBranch
          (.childCons succBranch
            (.childCons
              (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
              .childNil))))
    = some (.mkGen .gen_natElim ()
        (.childCons motive
          (.childCons predecessor
            (.childCons succBranch
              (.childCons predecessor .childNil))))) := rfl

/-- Demo rule: the W-TYPE-RECURSOR reduct shape — a fresh λ binder whose
body applies a (weakened) scrutinee child to the bound variable:
`… ↝ lam(zeroBranch, app(pred↑, var 0))`.  This is exactly the
`wRec (sup a f) ↝ step a f (λ x. wRec … (f x))` skeleton (EXT-1
readiness): projections weaken on demand and `boundVarAt 0` references
the fresh binder. -/
def wStyleRecursiveBinderDemoRule : IotaRuleDesc where
  elimGenerator := .gen_natElim
  scrutineeSlot := 3
  scrutineeHead := .gen_natSucc
  motiveSlot? := some 0
  target := .underBinder (.spineChildAt 1)
    (.applicationOf (.scrutineeChildAt 0) (.boundVarAt 0))

/-- `underBinder`/`boundVarAt` build a fresh-binder reduct with
on-demand weakening of the projections. -/
theorem wStyleRecursiveBinderDemoRule_interpretsTarget {scope : Nat}
    (motive : RawTerm (scope + 1))
    (zeroBranch predecessor : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) :
    wStyleRecursiveBinderDemoRule.interpretTarget? ()
      (.childCons motive
        (.childCons zeroBranch
          (.childCons succBranch
            (.childCons
              (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
              .childNil))))
    = some (.mkGen .gen_lam ()
        (.childCons zeroBranch
          (.childCons
            (.mkGen .gen_app ()
              (.childCons (RawTerm.weaken predecessor)
                (.childCons
                  (.mkGen .gen_var
                    ⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0)
                      (Nat.le_add_left 1 scope)⟩
                    .childNil)
                  .childNil)))
            .childNil))) := rfl

/-- Demo rule: fresh path-binder wrapping (`underPathBinder`). -/
def pathBinderEchoDemoRule : IotaRuleDesc where
  elimGenerator := .gen_fst
  scrutineeSlot := 0
  scrutineeHead := .gen_pair
  motiveSlot? := none
  target := .underPathBinder (.boundVarAt 0)

/-- `underPathBinder` builds `pathLam(var 0)`. -/
theorem pathBinderEchoDemoRule_interpretsTarget {scope : Nat}
    (firstValue secondValue : RawTerm scope) :
    pathBinderEchoDemoRule.interpretTarget? ()
      (.childCons
        (.mkGen .gen_pair ()
          (.childCons firstValue (.childCons secondValue .childNil)))
        .childNil)
    = some (.mkGen .gen_pathLam ()
        (.childCons
          (.mkGen .gen_var
            ⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0)
              (Nat.le_add_left 1 scope)⟩
            .childNil)
          .childNil)) := rfl

/-! ## Firing dispatcher smoke — the head test fires exactly on the
declared constructor head. -/

/-- Positive: β fires on a λ-headed function position. -/
theorem betaIotaRow_firesOnLamHeaded {scope : Nat}
    (domainAnn : RawTerm scope) (body : RawTerm (scope + 1))
    (arg : RawTerm scope) :
    betaIotaRow.firesOn? ()
      (.childCons
        (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
        (.childCons arg .childNil))
    = some (RawTerm.subst0 body arg) := rfl

/-- Negative: β does NOT fire on a non-λ-headed function position. -/
theorem betaIotaRow_rejectsUnitHeaded {scope : Nat} (arg : RawTerm scope) :
    betaIotaRow.firesOn? ()
      (.childCons (.mkGen .gen_unit () .childNil)
        (.childCons arg .childNil))
    = none := rfl

end FX1Poly.Core
