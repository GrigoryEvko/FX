import FX1Poly.Core.RawTermSubst0
import FX1Poly.Core.RawTermSubstPair
import FX1Poly.Core.RawTermWeaken

/-! # FX1Poly/Core/IotaRuleTable — reduction rules as DATA (the ι-rule table)

The operational twin of the typing rule tables (`typingRuleDescOf` /
`introRuleDescOf` / `elimRuleDescOf`): every β/ι reduction rule of the
kernel becomes one `IotaRuleDesc` VALUE — a left-linear pattern
(eliminator head + firing constructor heads in declared child slots)
plus a reduct template drawn from a CLOSED template DSL.  Adding a new
ι-rule to the kernel becomes adding a row, not threading constructors
through every Step consumer.

## Maximal dependent wiring (ALL tiers shipped)

The schema wires the FULL dependent structure of every rule even where
the current kernel's reducts do not consume it, so future rows
(W-types, indexed families, observational identity, definitional
univalence, literal/level arithmetic, copatterns) fit without a schema
change:

  * **Motive**: every dependent-eliminator row declares `motiveSlot?`;
    the binder arity is DERIVED from the generator table
    (`motiveBinderArity?`), never duplicated.  The template nodes
    `motiveInstantiatedWith` / `motiveInstantiatedWithPair` build
    `motive[arg]` / `motive[a, b]` — usable inside any reduct,
    including under fresh binders.
  * **Typed output ON the row** (`typedOutputTemplate?`): every
    motive-carrying row also states the TYPE of its reduct as a
    template (`motive[scrutinee]`, the `ElimRuleDesc.outputType`
    operational twin).  A row is thus a complete semantic unit —
    pattern, reduct, AND the dependent classifier of the reduct — and
    generic typed iota-SR plus the static-operational coherence
    certificate quantify over rows.  Rows whose reduct type is not
    syntactically present in the redex (β, endpoint-β, the
    non-dependent projections) honestly carry `none`.
  * **Multi-scrutinee patterns** (`scrutinees : List ScrutineeSpec`):
    a row may require constructor heads at SEVERAL slots
    simultaneously — the observational data-identity shape
    (`Id boolCode boolTrue boolFalse ↝ emptyCode` matches three heads;
    see `multiScrutineeBoolIdDemoRule`) and binary primitives.  All 21
    shipped rows are singleton patterns.  Template scrutinee accessors
    take the scrutinee INDEX (into the row's list).
  * **Payload guards + payload flow**: each scrutinee spec may carry a
    decidable `payloadGuard?` over the matched head's payload (the
    side-condition hook for level/flag-sensitive rows), and the
    `builtGen` node's `PayloadSource` either supplies a constant
    payload family or TRANSFORMS the matched scrutinee payload into
    the built generator's payload — the definitional-univalence and
    literal-arithmetic seam (see `univalenceShapedDemoRule` /
    `rebuildUniversePayloadDemoRule`).  A future binary payload
    transform (two literal operands) is ONE more `PayloadSource`
    constructor, not a template change.
  * **Generic cell construction** (`builtGen`): build ANY generator's
    cell in a reduct — target generator + payload source + a child
    template spine evaluated per-child at the target's OWN binder
    shifts (shift-1/2 children interpret one/two depths deeper, so
    fresh-binder wrapping is the shift-1 special case).  Subsumes
    application chains (`gen_app`), λ/path-λ wrapping, and former
    construction (the observational `Id`-at-Π funext reduct builds a
    `piTyCode` with a binder child).
  * **Scrutinee**: derived FROM the spine (`scrutineeTermAt?`), never
    passed separately — incoherent inputs are unrepresentable.  Whole
    scrutinees are mentionable (`theScrutineeAt`), their children
    projectable (`scrutineeChildAt`), their binder children
    substitutable (`substOneIntoScrutineeChild` /
    `substPairIntoScrutineeChild`).
  * **Binders in reducts**: interpretation is graded by a binder
    DEPTH; `boundVarAt` references template-introduced binders, with
    all projections weakened on demand — the W-type-recursor shape
    `wRec (sup a f) ↝ step a f (λ x. wRec (f x))` (see
    `wStyleRecursiveBinderDemoRule`).
  * **n-ary reassembly** (`reassembledReplacing`): re-apply the row's
    own eliminator with ANY set of spine slots replaced — `natElim` /
    `listElim` recursion AND the indexed-family shape (index slots
    change in recursive calls) in one node; the matched eliminator
    payload is transported across binder depth by the fold engine's
    scope-invariance (`Generator.payload_scope_invariant_of_not_var`).
  * **Decidable Tier-2 classifier** (`isStructurallyRecursive`): a
    computable check that every reassembly replaces scrutinee slots
    with IMMEDIATE scrutinee-child projections — the syntactic
    subterm-recursion condition the generic SN argument (IOTA-T8)
    keys on.  `natElimSuccIotaRow` passes; a reassembly feeding the
    WHOLE scrutinee back in fails (see
    `nonStructuralReassemblyDemoRule`).

## Shift-erased child view

The interpreter walks a shift-tagged list view of children
(`ScopedChild`); slot access is plain `Nat` indexing with shift checks
by full-enumeration `Nat` matches — no `Eq.rec` casts in the data path
(the two payload transports reduce away on every concrete row), and
everything reduces by iota on concrete spines: the adequacy equations
below close by `rfl`.  All depth-weakening helpers return their input
UNCHANGED at depth 0 (first match arm), so the 21 shipped rows reduce
exactly as written.

## The 21 rows + the GO gate

`iotaRuleTable` lists all 21 rules.  Rows 1–17 mirror the bespoke
`Step` constructors; row 18 (`pathBetaIotaRow`, endpoint-β) is the
first TABLE-NATIVE rule — no bespoke `Step` constructor; goes
operationally live at the canonicality flip (IOTA-T9).  Rows 19–21
(`quotRecMkIotaRow`, `quotElimMkIotaRow`, `truncRecIntroIotaRow`) are
the quotient/truncation TABLE-NATIVE rules.  The per-row
adequacy theorems (all `rfl`) are the GO gate, and every schema tier
carries its own demo adequacy equation (typed outputs, multi-scrutinee
firing, payload guard accept and reject, payload flow,
univalence-shaped row, W-style under-binder recursion, structural and
non-structural reassembly classification).

## Tier discipline (forward note)

Singleton-pattern guard-free rows form the orthogonal fragment and
inherit the full Tier-1 metatheory (SR / equivariance / firing /
confluence) from the generic template theorems (IOTA-T2..T6).
Multi-scrutinee rows stay left-linear (keys become slot-to-head maps);
guarded rows additionally owe the orthogonality certificate
guard-exclusivity on overlapping keys; reducts recursing under
`builtGen` binders or reassembling non-structurally face the decidable
Tier-2 SN check (IOTA-T8).  The table never promises SN generically.

## Zero-axiom verification

Plain structural definitions (full-enumeration matches, the `Option`
monad on concrete values), payload transports only through the
by-`cases`-`rfl` scope-invariance lemma and `Eq.rec` on
decidable-equality witnesses (both vanish on every concrete row), and
`rfl` equations throughout.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated per
declaration in `FX1PolyAudit/AuditIotaRuleTable.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation
open FX1Poly.Universe (LevelExpr UniverseFlag)

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

/-- Positional lookup in any list (hand-rolled, Init-only) — the one
lookup all slot/index accessors delegate to. -/
def listEntryAt? {entryType : Type} : List entryType → Nat → Option entryType
  | [], _ => none
  | headEntry :: _, 0 => some headEntry
  | _ :: restEntries, position + 1 => listEntryAt? restEntries position

/-- Positional lookup in a scoped-children list. -/
def scopedChildAt? {scope : Nat}
    (children : List (ScopedChild scope)) (slot : Nat) :
    Option (ScopedChild scope) :=
  listEntryAt? children slot

/-- Positional lookup in a plain `Nat` list — used to DERIVE per-slot
binder arities from the generator table instead of duplicating them on
rows. -/
def natListLookup? (entries : List Nat) (position : Nat) : Option Nat :=
  listEntryAt? entries position

/-- Membership test in a plain `Nat` list via the structural `Nat.beq`
(reduces by `rfl` on concrete slot lists) — used by the Tier-2
structural-recursion classifier. -/
def natListContains : List Nat → Nat → Bool
  | [], _ => false
  | slotHead :: restSlots, slot =>
      Nat.beq slotHead slot || natListContains restSlots slot

/-- The shift-erased children view of a cell term (total — every
`RawTerm` is a `mkGen` cell). -/
def RawTerm.scopedChildrenView {scope : Nat} :
    RawTerm scope → List (ScopedChild scope)
  | .mkGen _ _ children => children.toScopedChildren

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

/-! ## Pattern side: scrutinee specs with payload guards -/

/-- One scrutinee requirement of a row's left-linear pattern: the spine
slot, the constructor head that must sit there, and an optional
DECIDABLE guard over the matched head's payload (the side-condition
hook for level/flag-sensitive rows).  A guard-free spec fires on the
head test alone. -/
structure ScrutineeSpec where
  slot : Nat
  head : Generator
  payloadGuard? : Option ((atScope : Nat) → head.payload atScope → Bool) := none

/-! ## Reduct side: payload sources for built cells -/

/-- Where a `builtGen` reduct cell's payload comes from:

  * `constantFamily` — a scope-uniform payload value (every `Unit`
    payload, plus scope-independent data payloads like
    `gen_universeCode`'s level pair);
  * `transformedFromScrutinee` — the MATCHED payload of the scrutinee
    at `scrutineeIndex` (whose head must be the declared `sourceHead`),
    pushed through a row-supplied transform — the payload-flow seam for
    definitional univalence and future literal/level arithmetic rows.

A binary transform (two scrutinee payloads) is one more constructor
HERE when a concrete rule demands it — never a template change. -/
inductive PayloadSource : Generator → Type where
  | constantFamily {builtHead : Generator}
      (payloadFamily : (anyScope : Nat) → builtHead.payload anyScope) :
      PayloadSource builtHead
  | transformedFromScrutinee {builtHead : Generator}
      (scrutineeIndex : Nat) (sourceHead : Generator)
      (payloadTransform : (sourceScope targetScope : Nat) →
        sourceHead.payload sourceScope → builtHead.payload targetScope) :
      PayloadSource builtHead

/-! ## The closed reduct-template DSL -/

mutual

/-- The CLOSED reduct-template DSL — every shipped β/ι reduct is built
from these node shapes, and the node set covers the known future row
shapes (see the module docstring).  Slot numbers refer to the
ELIMINATOR spine (`spine…`) or to a firing CONSTRUCTOR's own children
(`scrutinee…`, addressed by the scrutinee's INDEX in the row's
`scrutinees` list, then the child slot).  Interpretation is graded by a
binder DEPTH; `builtGen` evaluates shift-1/2 children one/two depths
deeper and `boundVarAt` references the template-introduced binders
(innermost = 0). -/
inductive ReductTemplate : Type where
  /-- A template-introduced binder (innermost = 0; must be < the current
      depth). -/
  | boundVarAt (binderIndex : Nat)
  /-- The eliminator-spine child at `slot` (must sit at binder shift 0),
      weakened to the current depth. -/
  | spineChildAt (slot : Nat)
  /-- The child at `slot` of the firing constructor at `scrutineeIndex`
      (must sit at shift 0), weakened to the current depth. -/
  | scrutineeChildAt (scrutineeIndex slot : Nat)
  /-- The whole firing scrutinee at `scrutineeIndex`, weakened to the
      current depth. -/
  | theScrutineeAt (scrutineeIndex : Nat)
  /-- The row's declared motive (a one-binder spine child at
      `motiveSlot?`) instantiated at the interpreted argument —
      `motive[arg]`, the dependent-elimination output shape. -/
  | motiveInstantiatedWith (argTemplate : ReductTemplate)
  /-- The row's declared TWO-binder motive (`idJ`-family) instantiated
      at the interpreted pair — `motive[inner, outer]` with `var 0`
      receiving the inner template. -/
  | motiveInstantiatedWithPair (innerTemplate outerTemplate : ReductTemplate)
  /-- Build a cell of ANY generator: payload from a `PayloadSource`,
      children from a template spine evaluated per-child at the
      generator's own binder shifts (a shift-1 child interprets one
      depth deeper — fresh-binder wrapping; shift-2 two deeper).
      Subsumes application chains (`gen_app`), λ / path-λ wrapping, and
      former construction in type-level reducts. -/
  | builtGen (builtHead : Generator) (payloadSource : PayloadSource builtHead)
      (childTemplates : ReductTemplateSpine)
  /-- The row's own eliminator re-applied with the listed spine slots
      replaced by interpreted templates — the recursion of the
      `natElim`/`natRec`/`listElim` step cases (scrutinee slot only) AND
      the indexed-family shape (index slots change too) in one node.
      The whole spine is weakened to the current depth; the matched
      payload is transported by scope invariance. -/
  | reassembledReplacing (replacements : SpineReplacements)
  /-- `subst0` of the one-binder SPINE child at `bodySlot` by the
      interpreted argument. -/
  | substOneIntoSpineChild (bodySlot : Nat) (argTemplate : ReductTemplate)
  /-- `subst0` of the one-binder child at `bodySlot` of the scrutinee at
      `scrutineeIndex` by the interpreted argument — β (`gen_lam` body)
      and endpoint-β (`gen_pathLam` body). -/
  | substOneIntoScrutineeChild (scrutineeIndex bodySlot : Nat)
      (argTemplate : ReductTemplate)
  /-- `substPair` of the two-binder SPINE child at `bodySlot`: `var 0`
      gets the inner template (the recursive call / IH), `var 1` the
      outer template (the predecessor) — the Nat recursor step cases. -/
  | substPairIntoSpineChild (bodySlot : Nat)
      (innerTemplate outerTemplate : ReductTemplate)
  /-- `substPair` of the two-binder child at `bodySlot` of the scrutinee
      at `scrutineeIndex` — the symmetric closure (future constructor
      heads with binder children). -/
  | substPairIntoScrutineeChild (scrutineeIndex bodySlot : Nat)
      (innerTemplate outerTemplate : ReductTemplate)

/-- The child templates of a `builtGen` node — hand-rolled as a mutual
sibling (not a nested `List`) to keep recursion plainly structural and
propext-clean. -/
inductive ReductTemplateSpine : Type where
  | spineNil
  | spineCons (childTemplate : ReductTemplate) (restTemplates : ReductTemplateSpine)

/-- A list of (spine slot, replacement template) pairs for
`reassembledReplacing` — mutual sibling for the same reason. -/
inductive SpineReplacements : Type where
  | replaceNil
  | replaceCons (slot : Nat) (replacementTemplate : ReductTemplate)
      (restReplacements : SpineReplacements)

end

/-! ## The rule descriptor -/

/-- One β/ι rewrite rule as DATA: a left-linear pattern — the eliminator
head plus the constructor heads (with optional payload guards) required
at the declared spine slots — together with the DEPENDENT wiring (which
spine slot is the motive, what the reduct's TYPE is) and the reduct
template.  The orthogonality discipline (eliminator heads disjoint from
constructor heads, slot-to-head keys pairwise distinct, guards on
overlapping keys mutually exclusive) is what makes the table confluent
generically. -/
structure IotaRuleDesc where
  elimGenerator : Generator
  /-- The left-linear pattern's scrutinee requirements.  All 21 shipped
      rows are singletons; multi-scrutinee rows are the observational
      data-identity / binary-primitive shape. -/
  scrutinees : List ScrutineeSpec
  /-- The spine slot holding the dependent motive, when the eliminator
      has one (`none` for β / endpoint-β / the non-dependent
      projections).  Its binder arity is DERIVED from the generator
      table — see `motiveBinderArity?` — never duplicated here. -/
  motiveSlot? : Option Nat := none
  /-- The TYPE of the reduct as a template — `motive[scrutinee]` for
      every motive-carrying eliminator (the `ElimRuleDesc.outputType`
      operational twin; the generic typed iota-SR statement target).
      `none` exactly when the reduct's type is not syntactically
      present in the redex (β and endpoint-β: the codomain lives only
      in the typing derivation; fst/snd: the component types live only
      in the pair's classifier). -/
  typedOutputTemplate? : Option ReductTemplate := none
  target : ReductTemplate

namespace IotaRuleDesc

/-- The scrutinee spec at `scrutineeIndex` in the row's pattern. -/
def scrutineeSpecAt? (rule : IotaRuleDesc) (scrutineeIndex : Nat) :
    Option ScrutineeSpec :=
  listEntryAt? rule.scrutinees scrutineeIndex

/-- The slots of all scrutinee specs (the Tier-2 classifier's
"recursion positions"). -/
def scrutineeSlots (rule : IotaRuleDesc) : List Nat :=
  rule.scrutinees.map ScrutineeSpec.slot

/-- The binder arity of the row's motive, read off the generator
table — `some 1` for the unary-motive eliminators, `some 2` for the
`idJ` family, `none` when the row has no motive.  Single source of
truth: rows never restate what `Generator.binderShifts` already says. -/
def motiveBinderArity? (rule : IotaRuleDesc) : Option Nat :=
  rule.motiveSlot?.bind (natListLookup? rule.elimGenerator.binderShifts)

/-- The binder shift of the row's PRIMARY (index-0) scrutinee slot per
the generator table (every shipped row sits at shift 0 — the
orthogonality certificate re-decides this per row at IOTA-T5). -/
def scrutineeSlotShift? (rule : IotaRuleDesc) : Option Nat :=
  (rule.scrutineeSpecAt? 0).bind fun primarySpec =>
    natListLookup? rule.elimGenerator.binderShifts primarySpec.slot

/-- The firing scrutinee term at `scrutineeIndex`, DERIVED from the
spine (slot lookup at shift 0) — never passed separately, so
interpreter inputs cannot disagree with the spine. -/
def scrutineeTermAt? (rule : IotaRuleDesc) {scope : Nat}
    (scrutineeIndex : Nat)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    Option (RawTerm scope) :=
  (rule.scrutineeSpecAt? scrutineeIndex).bind fun spec =>
    (scopedChildAt? spine.toScopedChildren spec.slot).bind
      ScopedChild.atShiftZero?

/-- The shift-erased children view of the scrutinee at
`scrutineeIndex`, derived from the spine. -/
def scrutineeChildrenAt? (rule : IotaRuleDesc) {scope : Nat}
    (scrutineeIndex : Nat)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    Option (List (ScopedChild scope)) :=
  (rule.scrutineeTermAt? scrutineeIndex spine).map RawTerm.scopedChildrenView

/-- The PRIMARY (index-0) scrutinee term — the single-scrutinee rows'
canonical accessor. -/
def scrutineeTermOf? (rule : IotaRuleDesc) {scope : Nat}
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    Option (RawTerm scope) :=
  rule.scrutineeTermAt? 0 spine

/-- The PRIMARY scrutinee's children view. -/
def scrutineeChildrenOf? (rule : IotaRuleDesc) {scope : Nat}
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    Option (List (ScopedChild scope)) :=
  rule.scrutineeChildrenAt? 0 spine

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

/-- Resolve a `builtGen` payload source at the current depth: a
constant family applies at the built scope; a scrutinee transform reads
the MATCHED payload (checking the matched head is the declared source
head — the `Eq.rec` transport reduces away on concrete rows) and pushes
it through the row-supplied transform. -/
def resolvePayloadSource? (rule : IotaRuleDesc) {scope : Nat}
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope)
    (depth : Nat) {builtHead : Generator} :
    PayloadSource builtHead → Option (builtHead.payload (scope + depth))
  | .constantFamily payloadFamily => some (payloadFamily (scope + depth))
  | .transformedFromScrutinee scrutineeIndex sourceHead payloadTransform => do
      let scrutineeTerm ← rule.scrutineeTermAt? scrutineeIndex spine
      match scrutineeTerm with
      | .mkGen scrutineeGenerator scrutineePayload _ =>
        if isDeclaredHead : scrutineeGenerator = sourceHead then
          some (payloadTransform scope (scope + depth)
            (Eq.rec (motive := fun matchedHead _ => matchedHead.payload scope)
              scrutineePayload isDeclaredHead))
        else none

end IotaRuleDesc

/-! ## The template interpreter -/

mutual

/-- Interpret a reduct template against a rule's eliminator spine (with
its matched payload) at a binder depth.  Scrutinees and their children
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
  | depth, .scrutineeChildAt scrutineeIndex slot => do
      let scrutineeChildren ← rule.scrutineeChildrenAt? scrutineeIndex spine
      let scrutineeChild ← scopedChildAt? scrutineeChildren slot
      let childTerm ← scrutineeChild.atShiftZero?
      some (RawTerm.weakenBy depth childTerm)
  | depth, .theScrutineeAt scrutineeIndex => do
      let scrutineeTerm ← rule.scrutineeTermAt? scrutineeIndex spine
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
  | depth, .builtGen builtHead payloadSource childTemplates => do
      let builtPayload ← rule.resolvePayloadSource? spine depth payloadSource
      let builtChildren ←
        rule.interpretBuiltChildren? elimPayload spine depth
          builtHead.binderShifts childTemplates
      some (.mkGen builtHead builtPayload builtChildren)
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
  | depth, .substOneIntoScrutineeChild scrutineeIndex bodySlot argTemplate => do
      let argTerm ← rule.interpretTemplate? elimPayload spine depth argTemplate
      let scrutineeChildren ← rule.scrutineeChildrenAt? scrutineeIndex spine
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
  | depth, .substPairIntoScrutineeChild scrutineeIndex bodySlot
      innerTemplate outerTemplate => do
      let innerTerm ←
        rule.interpretTemplate? elimPayload spine depth innerTemplate
      let outerTerm ←
        rule.interpretTemplate? elimPayload spine depth outerTemplate
      let scrutineeChildren ← rule.scrutineeChildrenAt? scrutineeIndex spine
      let bodyChild ← scopedChildAt? scrutineeChildren bodySlot
      let bodyTerm ← bodyChild.atShiftTwo?
      some (RawTerm.substPair
        (RawTerm.weakenBodyUnderTwoBindersBy depth bodyTerm)
        innerTerm outerTerm)

/-- Assemble a `builtGen` node's children: each child template is
interpreted at the built generator's OWN binder shift on top of the
current depth (shift-0 at `depth`, shift-1 at `depth + 1`, shift-2 at
`depth + 2` — full-enumeration arms keep every scope index
definitional; no generator carries a shift above 2, and a future one
extends the enumeration by one arm).  Fails when the template spine's
length disagrees with the generator's arity. -/
def IotaRuleDesc.interpretBuiltChildren? (rule : IotaRuleDesc) {scope : Nat}
    (elimPayload : rule.elimGenerator.payload scope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope)
    (depth : Nat) :
    (childShifts : List Nat) → ReductTemplateSpine →
    Option (RawTermChildren childShifts (scope + depth))
  | [], .spineNil => some .childNil
  | [], .spineCons _ _ => none
  | _ :: _, .spineNil => none
  | 0 :: restShifts, .spineCons childTemplate restTemplates => do
      let childTerm ← rule.interpretTemplate? elimPayload spine depth childTemplate
      let restChildren ←
        rule.interpretBuiltChildren? elimPayload spine depth
          restShifts restTemplates
      some (.childCons childTerm restChildren)
  | 1 :: restShifts, .spineCons childTemplate restTemplates => do
      let childTerm ←
        rule.interpretTemplate? elimPayload spine (depth + 1) childTemplate
      let restChildren ←
        rule.interpretBuiltChildren? elimPayload spine depth
          restShifts restTemplates
      some (.childCons childTerm restChildren)
  | 2 :: restShifts, .spineCons childTemplate restTemplates => do
      let childTerm ←
        rule.interpretTemplate? elimPayload spine (depth + 2) childTemplate
      let restChildren ←
        rule.interpretBuiltChildren? elimPayload spine depth
          restShifts restTemplates
      some (.childCons childTerm restChildren)
  | (_ + 3) :: _, .spineCons _ _ => none

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

/-- Interpret the row's declared TYPED OUTPUT (the reduct's type) at
depth 0 — `motive[scrutinee]` for the motive-carrying eliminators; the
generic typed iota-SR statement target (IOTA-T7). -/
def IotaRuleDesc.interpretTypedOutput? (rule : IotaRuleDesc) {scope : Nat}
    (elimPayload : rule.elimGenerator.payload scope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    Option (RawTerm scope) :=
  rule.typedOutputTemplate?.bind (rule.interpretTemplate? elimPayload spine 0)

/-! ## The firing dispatcher -/

/-- Does ONE scrutinee spec fire on this spine?  The declared slot must
hold (at shift 0) a cell with the declared head whose payload passes
the optional guard.  The `Eq.rec` payload transport reduces away on
concrete heads. -/
def IotaRuleDesc.scrutineeSpecFires (rule : IotaRuleDesc) {scope : Nat}
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope)
    (spec : ScrutineeSpec) : Bool :=
  match (scopedChildAt? spine.toScopedChildren spec.slot).bind
      ScopedChild.atShiftZero? with
  | none => false
  | some (.mkGen scrutineeGenerator scrutineePayload _) =>
    if isDeclaredHead : scrutineeGenerator = spec.head then
      match spec.payloadGuard? with
      | none => true
      | some payloadGuard =>
          payloadGuard scope
            (Eq.rec (motive := fun matchedHead _ => matchedHead.payload scope)
              scrutineePayload isDeclaredHead)
    else false

/-- Do ALL scrutinee specs in a list fire? -/
def IotaRuleDesc.scrutineesFire (rule : IotaRuleDesc) {scope : Nat}
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    List ScrutineeSpec → Bool
  | [] => true
  | spec :: restSpecs =>
      rule.scrutineeSpecFires spine spec && rule.scrutineesFire spine restSpecs

/-- The firing dispatcher: interpret the row's reduct exactly when
EVERY declared scrutinee slot holds its declared (guard-passing)
constructor head — the left-linear pattern test.  The IOTA-T4 generic
firing soundness/completeness theorems are stated against THIS
function. -/
def IotaRuleDesc.firesOn? (rule : IotaRuleDesc) {scope : Nat}
    (elimPayload : rule.elimGenerator.payload scope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    Option (RawTerm scope) :=
  if rule.scrutineesFire spine rule.scrutinees then
    rule.interpretTarget? elimPayload spine
  else none

/-! ## The Tier-2 structural-recursion classifier

A row is STRUCTURALLY RECURSIVE when every `reassembledReplacing`
anywhere in its reduct replaces each SCRUTINEE slot with an immediate
scrutinee-child projection (`scrutineeChildAt`) — the decidable
syntactic condition the generic SN argument (IOTA-T8) keys on.  A
fixpoint-style row (feeding the whole scrutinee, or a built term, back
into the scrutinee slot) computably FAILS the check. -/

/-- Is this template literally an immediate scrutinee-child
projection?  (Full enumeration — no wildcard.) -/
def ReductTemplate.isScrutineeChildProjection : ReductTemplate → Bool
  | .scrutineeChildAt _ _ => true
  | .boundVarAt _ => false
  | .spineChildAt _ => false
  | .theScrutineeAt _ => false
  | .motiveInstantiatedWith _ => false
  | .motiveInstantiatedWithPair _ _ => false
  | .builtGen _ _ _ => false
  | .reassembledReplacing _ => false
  | .substOneIntoSpineChild _ _ => false
  | .substOneIntoScrutineeChild _ _ _ => false
  | .substPairIntoSpineChild _ _ _ => false
  | .substPairIntoScrutineeChild _ _ _ _ => false

mutual

/-- Every reassembly in this template replaces scrutinee slots only
with immediate scrutinee-child projections. -/
def ReductTemplate.hasOnlyStructuralReassemblies
    (scrutineeSlots : List Nat) : ReductTemplate → Bool
  | .boundVarAt _ => true
  | .spineChildAt _ => true
  | .scrutineeChildAt _ _ => true
  | .theScrutineeAt _ => true
  | .motiveInstantiatedWith argTemplate =>
      argTemplate.hasOnlyStructuralReassemblies scrutineeSlots
  | .motiveInstantiatedWithPair innerTemplate outerTemplate =>
      innerTemplate.hasOnlyStructuralReassemblies scrutineeSlots
        && outerTemplate.hasOnlyStructuralReassemblies scrutineeSlots
  | .builtGen _ _ childTemplates =>
      childTemplates.hasOnlyStructuralReassemblies scrutineeSlots
  | .reassembledReplacing replacements =>
      replacements.areStructuralOver scrutineeSlots
  | .substOneIntoSpineChild _ argTemplate =>
      argTemplate.hasOnlyStructuralReassemblies scrutineeSlots
  | .substOneIntoScrutineeChild _ _ argTemplate =>
      argTemplate.hasOnlyStructuralReassemblies scrutineeSlots
  | .substPairIntoSpineChild _ innerTemplate outerTemplate =>
      innerTemplate.hasOnlyStructuralReassemblies scrutineeSlots
        && outerTemplate.hasOnlyStructuralReassemblies scrutineeSlots
  | .substPairIntoScrutineeChild _ _ innerTemplate outerTemplate =>
      innerTemplate.hasOnlyStructuralReassemblies scrutineeSlots
        && outerTemplate.hasOnlyStructuralReassemblies scrutineeSlots

/-- Spine-wise conjunction of the structural-reassembly check. -/
def ReductTemplateSpine.hasOnlyStructuralReassemblies
    (scrutineeSlots : List Nat) : ReductTemplateSpine → Bool
  | .spineNil => true
  | .spineCons childTemplate restTemplates =>
      childTemplate.hasOnlyStructuralReassemblies scrutineeSlots
        && restTemplates.hasOnlyStructuralReassemblies scrutineeSlots

/-- Each replacement at a SCRUTINEE slot is an immediate scrutinee-child
projection (non-scrutinee slots are unconstrained — index slots may be
rewritten arbitrarily), and every replacement template is itself
recursively structural. -/
def SpineReplacements.areStructuralOver
    (scrutineeSlots : List Nat) : SpineReplacements → Bool
  | .replaceNil => true
  | .replaceCons slot replacementTemplate restReplacements =>
      (if natListContains scrutineeSlots slot then
        replacementTemplate.isScrutineeChildProjection
      else true)
        && replacementTemplate.hasOnlyStructuralReassemblies scrutineeSlots
        && restReplacements.areStructuralOver scrutineeSlots

end

/-- The row-level Tier-2 classifier: every recursive reassembly in the
reduct is structural (immediate-subterm) on the row's scrutinee slots. -/
def IotaRuleDesc.isStructurallyRecursive (rule : IotaRuleDesc) : Bool :=
  rule.target.hasOnlyStructuralReassemblies rule.scrutineeSlots

/-! ## The 21 rows -/

/-- β: `app(lam(domainAnn, body), arg) ↝ subst0 body arg`.  No motive,
and the codomain (the reduct's type) lives only in the typing
derivation — `typedOutputTemplate? := none`, honestly. -/
def betaIotaRow : IotaRuleDesc where
  elimGenerator := .gen_app
  scrutinees := [{ slot := 0, head := .gen_lam }]
  motiveSlot? := none
  typedOutputTemplate? := none
  target := .substOneIntoScrutineeChild 0 1 (.spineChildAt 1)

/-- `boolElim … boolTrue ↝ thenBranch` (spine slot 1); reduct type
`motive[boolTrue]`. -/
def boolTrueIotaRow : IotaRuleDesc where
  elimGenerator := .gen_boolElim
  scrutinees := [{ slot := 3, head := .gen_boolTrue }]
  motiveSlot? := some 0
  typedOutputTemplate? := some (.motiveInstantiatedWith (.theScrutineeAt 0))
  target := .spineChildAt 1

/-- `boolElim … boolFalse ↝ elseBranch` (spine slot 2); reduct type
`motive[boolFalse]`. -/
def boolFalseIotaRow : IotaRuleDesc where
  elimGenerator := .gen_boolElim
  scrutinees := [{ slot := 3, head := .gen_boolFalse }]
  motiveSlot? := some 0
  typedOutputTemplate? := some (.motiveInstantiatedWith (.theScrutineeAt 0))
  target := .spineChildAt 2

/-- `fst(pair(a, b)) ↝ a` (non-dependent projection — no motive slot in
the current generator table, so no syntactic typed output either). -/
def fstPairIotaRow : IotaRuleDesc where
  elimGenerator := .gen_fst
  scrutinees := [{ slot := 0, head := .gen_pair }]
  motiveSlot? := none
  typedOutputTemplate? := none
  target := .scrutineeChildAt 0 0

/-- `snd(pair(a, b)) ↝ b`. -/
def sndPairIotaRow : IotaRuleDesc where
  elimGenerator := .gen_snd
  scrutinees := [{ slot := 0, head := .gen_pair }]
  motiveSlot? := none
  typedOutputTemplate? := none
  target := .scrutineeChildAt 0 1

/-- `natElim … natZero ↝ zeroBranch`; reduct type `motive[natZero]`. -/
def natElimZeroIotaRow : IotaRuleDesc where
  elimGenerator := .gen_natElim
  scrutinees := [{ slot := 3, head := .gen_natZero }]
  motiveSlot? := some 0
  typedOutputTemplate? := some (.motiveInstantiatedWith (.theScrutineeAt 0))
  target := .spineChildAt 1

/-- `natRec … natZero ↝ zeroBranch`. -/
def natRecZeroIotaRow : IotaRuleDesc where
  elimGenerator := .gen_natRec
  scrutinees := [{ slot := 3, head := .gen_natZero }]
  motiveSlot? := some 0
  typedOutputTemplate? := some (.motiveInstantiatedWith (.theScrutineeAt 0))
  target := .spineChildAt 1

/-- `natElim … natSucc(pred) ↝ substPair succBranch (natElim … pred) pred`
— the recursive step case: `var 0` gets the recursive call (reassembly
of the eliminator with the scrutinee slot replaced by the predecessor),
`var 1` the predecessor.  Reduct type `motive[natSucc pred]`. -/
def natElimSuccIotaRow : IotaRuleDesc where
  elimGenerator := .gen_natElim
  scrutinees := [{ slot := 3, head := .gen_natSucc }]
  motiveSlot? := some 0
  typedOutputTemplate? := some (.motiveInstantiatedWith (.theScrutineeAt 0))
  target := .substPairIntoSpineChild 2
    (.reassembledReplacing
      (.replaceCons 3 (.scrutineeChildAt 0 0) .replaceNil))
    (.scrutineeChildAt 0 0)

/-- `natRec … natSucc(pred)` — the dependent-recursor twin. -/
def natRecSuccIotaRow : IotaRuleDesc where
  elimGenerator := .gen_natRec
  scrutinees := [{ slot := 3, head := .gen_natSucc }]
  motiveSlot? := some 0
  typedOutputTemplate? := some (.motiveInstantiatedWith (.theScrutineeAt 0))
  target := .substPairIntoSpineChild 2
    (.reassembledReplacing
      (.replaceCons 3 (.scrutineeChildAt 0 0) .replaceNil))
    (.scrutineeChildAt 0 0)

/-- `listElim … listNil ↝ nilBranch`; reduct type `motive[listNil]`. -/
def listElimNilIotaRow : IotaRuleDesc where
  elimGenerator := .gen_listElim
  scrutinees := [{ slot := 3, head := .gen_listNil }]
  motiveSlot? := some 0
  typedOutputTemplate? := some (.motiveInstantiatedWith (.theScrutineeAt 0))
  target := .spineChildAt 1

/-- `listElim … listCons(h, t) ↝ consBranch h t (listElim … t)` — the
applied-branch + reassembly step case; reduct type
`motive[listCons h t]`. -/
def listElimConsIotaRow : IotaRuleDesc where
  elimGenerator := .gen_listElim
  scrutinees := [{ slot := 3, head := .gen_listCons }]
  motiveSlot? := some 0
  typedOutputTemplate? := some (.motiveInstantiatedWith (.theScrutineeAt 0))
  target := .builtGen .gen_app (.constantFamily fun _ => ())
    (.spineCons
      (.builtGen .gen_app (.constantFamily fun _ => ())
        (.spineCons
          (.builtGen .gen_app (.constantFamily fun _ => ())
            (.spineCons (.spineChildAt 2)
              (.spineCons (.scrutineeChildAt 0 0) .spineNil)))
          (.spineCons (.scrutineeChildAt 0 1) .spineNil)))
      (.spineCons
        (.reassembledReplacing
          (.replaceCons 3 (.scrutineeChildAt 0 1) .replaceNil))
        .spineNil))

/-- `optionMatch … optionNone ↝ noneBranch`; reduct type
`motive[optionNone]`. -/
def optionMatchNoneIotaRow : IotaRuleDesc where
  elimGenerator := .gen_optionMatch
  scrutinees := [{ slot := 3, head := .gen_optionNone }]
  motiveSlot? := some 0
  typedOutputTemplate? := some (.motiveInstantiatedWith (.theScrutineeAt 0))
  target := .spineChildAt 1

/-- `optionMatch … optionSome(v) ↝ someBranch v`; reduct type
`motive[optionSome v]`. -/
def optionMatchSomeIotaRow : IotaRuleDesc where
  elimGenerator := .gen_optionMatch
  scrutinees := [{ slot := 3, head := .gen_optionSome }]
  motiveSlot? := some 0
  typedOutputTemplate? := some (.motiveInstantiatedWith (.theScrutineeAt 0))
  target := .builtGen .gen_app (.constantFamily fun _ => ())
    (.spineCons (.spineChildAt 2)
      (.spineCons (.scrutineeChildAt 0 0) .spineNil))

/-- `eitherMatch … eitherInl(v) ↝ leftBranch v`; reduct type
`motive[eitherInl v]`. -/
def eitherMatchInlIotaRow : IotaRuleDesc where
  elimGenerator := .gen_eitherMatch
  scrutinees := [{ slot := 3, head := .gen_eitherInl }]
  motiveSlot? := some 0
  typedOutputTemplate? := some (.motiveInstantiatedWith (.theScrutineeAt 0))
  target := .builtGen .gen_app (.constantFamily fun _ => ())
    (.spineCons (.spineChildAt 1)
      (.spineCons (.scrutineeChildAt 0 0) .spineNil))

/-- `eitherMatch … eitherInr(v) ↝ rightBranch v`; reduct type
`motive[eitherInr v]`. -/
def eitherMatchInrIotaRow : IotaRuleDesc where
  elimGenerator := .gen_eitherMatch
  scrutinees := [{ slot := 3, head := .gen_eitherInr }]
  motiveSlot? := some 0
  typedOutputTemplate? := some (.motiveInstantiatedWith (.theScrutineeAt 0))
  target := .builtGen .gen_app (.constantFamily fun _ => ())
    (.spineCons (.spineChildAt 2)
      (.spineCons (.scrutineeChildAt 0 0) .spineNil))

/-- `idJ … refl ↝ baseCase` (two-binder motive at slot 0); reduct type
`motive[refl(a), a]` (`var 0` = the path, `var 1` = the endpoint). -/
def idJReflIotaRow : IotaRuleDesc where
  elimGenerator := .gen_idJ
  scrutinees := [{ slot := 2, head := .gen_refl }]
  motiveSlot? := some 0
  typedOutputTemplate? := some
    (.motiveInstantiatedWithPair (.theScrutineeAt 0) (.scrutineeChildAt 0 0))
  target := .spineChildAt 1

/-- `idStrictRec … refl ↝ baseCase`. -/
def idStrictRecReflIotaRow : IotaRuleDesc where
  elimGenerator := .gen_idStrictRec
  scrutinees := [{ slot := 2, head := .gen_refl }]
  motiveSlot? := some 0
  typedOutputTemplate? := some
    (.motiveInstantiatedWithPair (.theScrutineeAt 0) (.scrutineeChildAt 0 0))
  target := .spineChildAt 1

/-- Endpoint β: `pathApp(pathLam(body), arg) ↝ subst0 body arg` — the
FIRST TABLE-NATIVE rule (no bespoke `Step` constructor; goes
operationally live at the canonicality flip).  `gen_pathLam` carries no
domain annotation, so the body is its scrutinee child 0. -/
def pathBetaIotaRow : IotaRuleDesc where
  elimGenerator := .gen_pathApp
  scrutinees := [{ slot := 0, head := .gen_pathLam }]
  motiveSlot? := none
  typedOutputTemplate? := none
  target := .substOneIntoScrutineeChild 0 0 (.spineChildAt 1)

/-! ## The IOTA-T10 demo rows — NEW iotas landed purely as data

Three reserved eliminators go operationally live as rows ONLY (the
TG-5-style cascade-death demonstration): the quotient lift
computation (fx_design §3.7, the EXT-2 substrate), its dependent
twin, and the truncation recursor.  Every Tier-1 metatheorem
(equivariance, SR, confluence, firing determinism, the normalizer)
holds by instantiation; the certificates re-decide. -/

/-- `quotRec(kernelFn, respectsRel, quotMk(v)) ↝ app(kernelFn, v)` —
the quotient lift computes on the constructor (the `respectsRel`
witness is consumed by typing, not by the reduct). -/
def quotRecMkIotaRow : IotaRuleDesc where
  elimGenerator := .gen_quotRec
  scrutinees := [{ slot := 2, head := .gen_quotMk }]
  motiveSlot? := none
  typedOutputTemplate? := none
  target := .builtGen .gen_app (.constantFamily fun _ => ())
    (.spineCons (.spineChildAt 0)
      (.spineCons (.scrutineeChildAt 0 0) .spineNil))

/-- `quotElim(depMotive, depKernel, quotMk(v)) ↝ app(depKernel, v)` —
the dependent quotient eliminator; the reduct TYPE is the motive
family applied to the scrutinee (the motive is a function child at
shift 0, so the typed output is a built application, not a
binder-motive instantiation). -/
def quotElimMkIotaRow : IotaRuleDesc where
  elimGenerator := .gen_quotElim
  scrutinees := [{ slot := 2, head := .gen_quotMk }]
  motiveSlot? := none
  typedOutputTemplate? := some
    (.builtGen .gen_app (.constantFamily fun _ => ())
      (.spineCons (.spineChildAt 0)
        (.spineCons (.theScrutineeAt 0) .spineNil)))
  target := .builtGen .gen_app (.constantFamily fun _ => ())
    (.spineCons (.spineChildAt 1)
      (.spineCons (.scrutineeChildAt 0 0) .spineNil))

/-- `truncRec(kernelFn, truncIntro(v)) ↝ app(kernelFn, v)` — the
truncation recursor computes on the constructor (the level payloads
are coherence data for typing; the reduct reads neither). -/
def truncRecIntroIotaRow : IotaRuleDesc where
  elimGenerator := .gen_truncRec
  scrutinees := [{ slot := 1, head := .gen_truncIntro }]
  motiveSlot? := none
  typedOutputTemplate? := none
  target := .builtGen .gen_app (.constantFamily fun _ => ())
    (.spineCons (.spineChildAt 0)
      (.spineCons (.scrutineeChildAt 0 0) .spineNil))

/-- The full ι-rule table: β + the 16 legacy data/identity iotas + the
table-native endpoint-β + the three IOTA-T10 demo rows (quotient
lift, dependent quotient eliminator, truncation recursor — landed as
data with zero new arms).  Key discipline (decided generically at
IOTA-T5): the slot-to-head maps are pairwise distinct per eliminator,
no scrutinee head is an eliminator root, and guards on overlapping keys
are mutually exclusive — the orthogonality certificate. -/
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
  , pathBetaIotaRow
  , quotRecMkIotaRow, quotElimMkIotaRow, truncRecIntroIotaRow ]

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

/-- IOTA-T10 GO gate: the quotient lift computes on the constructor. -/
theorem quotRecMkIotaRow_interpretsTarget {scope : Nat}
    (kernelFn respectsRel value : RawTerm scope) :
    quotRecMkIotaRow.interpretTarget? ()
      (.childCons kernelFn
        (.childCons respectsRel
          (.childCons
            (.mkGen .gen_quotMk () (.childCons value .childNil))
            .childNil)))
    = some (.mkGen .gen_app ()
        (.childCons kernelFn (.childCons value .childNil))) := rfl

/-- IOTA-T10 GO gate: the dependent quotient eliminator computes. -/
theorem quotElimMkIotaRow_interpretsTarget {scope : Nat}
    (depMotive depKernel value : RawTerm scope) :
    quotElimMkIotaRow.interpretTarget? ()
      (.childCons depMotive
        (.childCons depKernel
          (.childCons
            (.mkGen .gen_quotMk () (.childCons value .childNil))
            .childNil)))
    = some (.mkGen .gen_app ()
        (.childCons depKernel (.childCons value .childNil))) := rfl

/-- IOTA-T10 GO gate: the truncation recursor computes (any intro
level — coherence is typing's job). -/
theorem truncRecIntroIotaRow_interpretsTarget {scope : Nat}
    (kernelFn value : RawTerm scope) (elimLevel introLevel : Nat) :
    truncRecIntroIotaRow.interpretTarget? elimLevel
      (.childCons kernelFn
        (.childCons
          (.mkGen .gen_truncIntro introLevel (.childCons value .childNil))
          .childNil))
    = some (.mkGen .gen_app ()
        (.childCons kernelFn (.childCons value .childNil))) := rfl

/-- Table size pin: 21 rows (β + 16 legacy iotas + table-native
endpoint-β + the 3 IOTA-T10 demo rows).  A permanent stale-count
guard in the HON-9 style. -/
theorem iotaRuleTable_length : iotaRuleTable.length = 21 := rfl

/-! ## Dependent-wiring pins — the motive metadata is DERIVED, not
restated: arity 1 for the unary-motive eliminators, arity 2 for the
`idJ` family, `none` for β / endpoint-β / the non-dependent
projections.  Every shipped primary scrutinee slot sits at shift 0. -/

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

/-! ## Typed-output pins — each motive-carrying row's declared reduct
TYPE interprets to exactly `motive[scrutinee]` (the dependent
elimination classifier), definitionally.  The generic typed iota-SR
(IOTA-T7) is stated against `interpretTypedOutput?`. -/

theorem boolTrueIotaRow_typedOutputInterprets {scope : Nat}
    (motive : RawTerm (scope + 1)) (thenBranch elseBranch : RawTerm scope) :
    boolTrueIotaRow.interpretTypedOutput? ()
      (.childCons motive
        (.childCons thenBranch
          (.childCons elseBranch
            (.childCons (.mkGen .gen_boolTrue () .childNil) .childNil))))
    = some (RawTerm.subst0 motive (.mkGen .gen_boolTrue () .childNil)) := rfl

theorem natElimSuccIotaRow_typedOutputInterprets {scope : Nat}
    (motive : RawTerm (scope + 1))
    (zeroBranch predecessor : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) :
    natElimSuccIotaRow.interpretTypedOutput? ()
      (.childCons motive
        (.childCons zeroBranch
          (.childCons succBranch
            (.childCons
              (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
              .childNil))))
    = some (RawTerm.subst0 motive
        (.mkGen .gen_natSucc () (.childCons predecessor .childNil))) := rfl

theorem idJReflIotaRow_typedOutputInterprets {scope : Nat}
    (motive : RawTerm (scope + 2))
    (baseCase rawWitness : RawTerm scope) :
    idJReflIotaRow.interpretTypedOutput? ()
      (.childCons motive
        (.childCons baseCase
          (.childCons
            (.mkGen .gen_refl () (.childCons rawWitness .childNil))
            .childNil)))
    = some (RawTerm.substPair motive
        (.mkGen .gen_refl () (.childCons rawWitness .childNil))
        rawWitness) := rfl

/-- β honestly declares NO syntactic typed output. -/
theorem betaIotaRow_typedOutputAbsent :
    betaIotaRow.typedOutputTemplate? = none := rfl

/-! ## New-node demo adequacy — each schema tier proves its
expressiveness with an `rfl` equation on a synthetic rule (these rules
are NOT table rows; they witness that the DSL already expresses the
future row shapes). -/

/-- Demo rule: the whole-scrutinee echo (`theScrutineeAt`). -/
def scrutineeEchoDemoRule : IotaRuleDesc where
  elimGenerator := .gen_fst
  scrutinees := [{ slot := 0, head := .gen_pair }]
  target := .theScrutineeAt 0

/-- `theScrutineeAt` interprets to the firing constructor itself. -/
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
`natElim` zero case. -/
def natElimMotiveAtScrutineeDemoRule : IotaRuleDesc where
  elimGenerator := .gen_natElim
  scrutinees := [{ slot := 3, head := .gen_natZero }]
  motiveSlot? := some 0
  target := .motiveInstantiatedWith (.theScrutineeAt 0)

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
  scrutinees := [{ slot := 2, head := .gen_refl }]
  motiveSlot? := some 0
  target := .motiveInstantiatedWithPair (.theScrutineeAt 0)
    (.scrutineeChildAt 0 0)

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
  scrutinees := [{ slot := 0, head := .gen_natElim }]
  target := .substPairIntoScrutineeChild 0 2
    (.scrutineeChildAt 0 1) (.scrutineeChildAt 0 1)

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
  scrutinees := [{ slot := 3, head := .gen_natSucc }]
  motiveSlot? := some 0
  target := .reassembledReplacing
    (.replaceCons 1 (.scrutineeChildAt 0 0)
      (.replaceCons 3 (.scrutineeChildAt 0 0) .replaceNil))

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

/-- Demo rule: the W-TYPE-RECURSOR reduct shape — a fresh λ binder
(`builtGen .gen_lam` with its shift-1 body child one depth deeper)
whose body applies a (weakened) scrutinee child to the bound variable:
`… ↝ lam(zeroBranch, app(pred↑, var 0))`.  This is exactly the
`wRec (sup a f) ↝ step a f (λ x. wRec … (f x))` skeleton (EXT-1
readiness): projections weaken on demand and `boundVarAt 0` references
the fresh binder. -/
def wStyleRecursiveBinderDemoRule : IotaRuleDesc where
  elimGenerator := .gen_natElim
  scrutinees := [{ slot := 3, head := .gen_natSucc }]
  motiveSlot? := some 0
  target := .builtGen .gen_lam (.constantFamily fun _ => ())
    (.spineCons (.spineChildAt 1)
      (.spineCons
        (.builtGen .gen_app (.constantFamily fun _ => ())
          (.spineCons (.scrutineeChildAt 0 0)
            (.spineCons (.boundVarAt 0) .spineNil)))
        .spineNil))

/-- `builtGen` at a shift-1 child + `boundVarAt` build a fresh-binder
reduct with on-demand weakening of the projections. -/
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

/-- Demo rule: fresh path-binder wrapping via `builtGen .gen_pathLam`
(shift-1 child). -/
def pathBinderEchoDemoRule : IotaRuleDesc where
  elimGenerator := .gen_fst
  scrutinees := [{ slot := 0, head := .gen_pair }]
  target := .builtGen .gen_pathLam (.constantFamily fun _ => ())
    (.spineCons (.boundVarAt 0) .spineNil)

/-- `builtGen .gen_pathLam` builds `pathLam(var 0)`. -/
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

/-- Demo rule: MULTI-SCRUTINEE pattern — the observational
data-identity shape `Id boolCode boolTrue boolFalse ↝ emptyCode`
(HOTT-3 / EXT-3 readiness): THREE constructor heads matched
simultaneously (the type child and both endpoints), reduct built by
`builtGen` at a nullary former. -/
def multiScrutineeBoolIdDemoRule : IotaRuleDesc where
  elimGenerator := .gen_idCode
  scrutinees :=
    [ { slot := 0, head := .gen_boolCode }
    , { slot := 1, head := .gen_boolTrue }
    , { slot := 2, head := .gen_boolFalse } ]
  target := .builtGen .gen_emptyCode (.constantFamily fun _ => ()) .spineNil

/-- The three-head pattern fires on distinct boolean endpoints and
computes the empty code. -/
theorem multiScrutineeBoolIdDemoRule_firesOnDistinctBools {scope : Nat} :
    multiScrutineeBoolIdDemoRule.firesOn? ()
      ((.childCons (.mkGen .gen_boolCode () .childNil)
        (.childCons (.mkGen .gen_boolTrue () .childNil)
          (.childCons (.mkGen .gen_boolFalse () .childNil) .childNil)))
        : RawTermChildren _ scope)
    = some (.mkGen .gen_emptyCode () .childNil) := rfl

/-- The three-head pattern REJECTS matching endpoints (slot 2 holds
`boolTrue`, not the declared `boolFalse`). -/
theorem multiScrutineeBoolIdDemoRule_rejectsMatchingBools {scope : Nat} :
    multiScrutineeBoolIdDemoRule.firesOn? ()
      ((.childCons (.mkGen .gen_boolCode () .childNil)
        (.childCons (.mkGen .gen_boolTrue () .childNil)
          (.childCons (.mkGen .gen_boolTrue () .childNil) .childNil)))
        : RawTermChildren _ scope)
    = none := rfl

/-- Demo rule: the DEFINITIONAL-UNIVALENCE shape (EXT-4 readiness) —
`Id (Type@l) lhs rhs ↝ Equiv lhs rhs`: a payload-carrying TYPE head
(`gen_universeCode`) as scrutinee, reduct built at `gen_equivCode`
from the spine endpoints. -/
def univalenceShapedDemoRule : IotaRuleDesc where
  elimGenerator := .gen_idCode
  scrutinees := [{ slot := 0, head := .gen_universeCode }]
  target := .builtGen .gen_equivCode (.constantFamily fun _ => ())
    (.spineCons (.spineChildAt 1) (.spineCons (.spineChildAt 2) .spineNil))

/-- The univalence-shaped row fires on a universe-headed type child
(any level payload) and computes the equivalence code. -/
theorem univalenceShapedDemoRule_firesOnUniverse {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (lhsCode rhsCode : RawTerm scope) :
    univalenceShapedDemoRule.firesOn? ()
      (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (.childCons lhsCode (.childCons rhsCode .childNil)))
    = some (.mkGen .gen_equivCode ()
        (.childCons lhsCode (.childCons rhsCode .childNil))) := rfl

/-- Demo rule: PAYLOAD GUARD rejection — same shape as the univalence
row but with an always-false guard on the universe payload; the
pattern's head matches yet the row does not fire. -/
def guardedRejectDemoRule : IotaRuleDesc where
  elimGenerator := .gen_idCode
  scrutinees :=
    [{ slot := 0, head := .gen_universeCode
     , payloadGuard? := some fun _ _ => false }]
  target := .builtGen .gen_equivCode (.constantFamily fun _ => ())
    (.spineCons (.spineChildAt 1) (.spineCons (.spineChildAt 2) .spineNil))

/-- The always-false payload guard blocks firing despite the matching
head. -/
theorem guardedRejectDemoRule_rejects {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (lhsCode rhsCode : RawTerm scope) :
    guardedRejectDemoRule.firesOn? ()
      (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (.childCons lhsCode (.childCons rhsCode .childNil)))
    = none := rfl

/-- Demo rule: PAYLOAD FLOW — rebuild a universe code carrying the
MATCHED scrutinee payload through `PayloadSource.transformedFromScrutinee`
(the literal/level-arithmetic seam). -/
def rebuildUniversePayloadDemoRule : IotaRuleDesc where
  elimGenerator := .gen_fst
  scrutinees := [{ slot := 0, head := .gen_universeCode }]
  target := .builtGen .gen_universeCode
    (.transformedFromScrutinee 0 .gen_universeCode fun _ _ payload => payload)
    .spineNil

/-- The matched universe payload flows verbatim into the rebuilt cell. -/
theorem rebuildUniversePayloadDemoRule_interpretsTarget {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    rebuildUniversePayloadDemoRule.interpretTarget? ()
      ((.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        .childNil) : RawTermChildren _ scope)
    = some (.mkGen .gen_universeCode (levelExpr, flag) .childNil) := rfl

/-- Demo rule: a NON-STRUCTURAL reassembly — the recursive call feeds
the WHOLE scrutinee (not a child) back into the scrutinee slot; the
Tier-2 classifier computably rejects it. -/
def nonStructuralReassemblyDemoRule : IotaRuleDesc where
  elimGenerator := .gen_natElim
  scrutinees := [{ slot := 3, head := .gen_natSucc }]
  motiveSlot? := some 0
  target := .reassembledReplacing
    (.replaceCons 3 (.theScrutineeAt 0) .replaceNil)

/-! ## Tier-2 classifier pins -/

theorem natElimSuccIotaRow_isStructurallyRecursive :
    natElimSuccIotaRow.isStructurallyRecursive = true := rfl

theorem listElimConsIotaRow_isStructurallyRecursive :
    listElimConsIotaRow.isStructurallyRecursive = true := rfl

/-- Reassembly-free rows pass vacuously. -/
theorem boolTrueIotaRow_isStructurallyRecursive :
    boolTrueIotaRow.isStructurallyRecursive = true := rfl

/-- The whole-scrutinee feedback loop computably FAILS the structural
check — the table never promises SN for such a row. -/
theorem nonStructuralReassemblyDemoRule_isNotStructurallyRecursive :
    nonStructuralReassemblyDemoRule.isStructurallyRecursive = false := rfl

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
