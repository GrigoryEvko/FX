import LeanFX2.Foundation.PolyCell.Core.PolyProfile
import LeanFX2.Foundation.PolyCell.Core.CellSort
import LeanFX2.Foundation.PolyCell.Core.RawCell
import LeanFX2.Foundation.PolyCell.Core.CellBoundary
import LeanFX2.Foundation.PolyCell.Core.GeneratorMetadata
import LeanFX2.Foundation.PolyCell.Core.GeneratorAdmission
import LeanFX2.Foundation.PolyCell.Core.GenPayloadEvidence
import LeanFX2.Foundation.PolyCell.Core.HasEqualDim
import LeanFX2.Foundation.PolyCell.Core.RuleSpec

/-! # Foundation/PolyCell/Core/PolyCell — the certified inductive

This file ships the v2 certified-cell inductive `PolyCell` together
with its spec-aligned spine `CertifiedTermSpine` in a single mutual
block.  This is the architectural headline of the v2 re-foundation:
ONE generic `gen` constructor admits every dim-0 term-former
(subsuming the 5 per-fixture ctors of v1), with the cascade tax
collapsed into 9 metadata-table lines per feature instead of
600-1000 LoC per ctor.

## The mutual block — tying the knot

`PolyCell.gen` takes a `CertifiedTermSpine` parameter (its
children).  `CertifiedTermSpine.cons` produces a `PolyCell` value
at its head position.  This cyclic dependency requires a Lean 4
`mutual ... end` block — but the mutual-index rule [feedback memory
`feedback_lean_mutual_index_rule`] is satisfied because neither
inductive's INDICES reference the other:

* `PolyCell` indices: `(sort : CellSort, dim : Nat, scope : Nat,
  boundary : CellBoundary ..., rawCell : RawCell scope)` — no
  sibling refs.

* `CertifiedTermSpine` indices: `(childSpecs : List ChildSpec,
  binderShifts : List Nat, children : RawTermChildren
  binderShifts parentScope)` — `RawTermChildren` is from a
  separate (raw-layer) mutual block, not a sibling.

So the mutual block compiles cleanly.

## The 4 PolyCell constructors

### `gen` — the cascade-killing headline

Subsumes v1's `lambdaUnitTypeBodyVarZero` /
`applicationVarZeroVarOne` / `piTypeUnitCodomainUnit` /
`contextConsEmptyUnitLinear` etc. (5+ per-fixture ctors).  ONE generic
ctor admits any term-former whose `Generator` is admitted and whose
payload passes evidence:

```
gen : (admissionWitness : SupportedGenerator generator) →
      (payloadEvidence : GenPayloadEvidence generator scope payload) →
      (childSpine : CertifiedTermSpine profile scope ...) →
      PolyCell profile generator.cellSort 0 scope ()
        (.termBase (.mkGen generator payload children))
```

Adding a feature = adding ONE `SupportedGenerator` arm — NO new
PolyCell constructor needed.  This is the load-bearing payoff of
the v2 architecture: the 9-lines-per-feature discipline at L1
translates here into ZERO new ctors at L1c.

### `generatingCell` — dim-(n+1) rules

Certifies a generating cell at `source.dim + 1`, with source and
target endpoints certified at `source.dim` (reconciled via
`HasEqualDim source target`).  Gated by SPIKE-1's value-level dim
transport pattern.

### `verticalComposite` — same-dim composition

Two dim-(n+1) cells sharing a middle endpoint compose into a dim-
(n+1) cell from source to target.  No `horizontalComposite` ctor
(reserved for future Gray-tensor work; raw `RawCell.compH` rejects
as `unsupportedCompH` per `polycell.md` §4).

### `identityCell` — degeneracy

Every certified cell has a certified identity at one higher dim,
preserving the same base.

## The CertifiedTermSpine design — 5 indices, no transports

The spine is indexed by FIVE things:

1. `profile : PolyProfile` (parameter, not index)
2. `parentScope : Nat` (parameter, not index)
3. `childSpecs : List ChildSpec` (index — what specs?)
4. `binderShifts : List Nat` (index — what scope shifts?)
5. `children : RawTermChildren binderShifts parentScope` (index —
   what raws?)

The `binderShifts` index is redundant with `childSpecs` (it equals
`childSpecs.map (·.scopeShift)`) but tracking it as a SEPARATE
type index avoids needing the coherence equation
`childSpecs.map (·.scopeShift) = generator.binderShifts` to hold
definitionally (it doesn't — the coherence lemma is propositional,
not definitional).

The `cons` constructor maintains both `childSpecs` and `binderShifts`
in lockstep — `headSpec :: restSpecs` is paired with
`headSpec.scopeShift :: restShifts`.  So at the gen ctor's use site,
passing `generator.childSpecs` as childSpecs and `generator.binderShifts`
as binderShifts both type-check directly; the spine is constructible
iff the coherence holds at the value level (which it does, by the
shipped coherence lemma).

This is the **Allais-style "track parallel indices"** pattern from
the Indexed Functors universe-of-syntaxes paper (Allais et al.,
ICFP'18): two related indices, maintained in lockstep at constructor
time, with no transports at use time.

## Why all CertifiedTermSpine cons heads are termBase-wrapped

The cons head's rawCell is `.termBase headRaw` where `headRaw :
RawTerm (parentScope + headSpec.scopeShift)`.  This commits all
child cells to be at dim 0 (since `RawCell.dim (.termBase _) = 0`).

For fxProfile, this is correct: every `ChildSpec` in every
`Generator.childSpecs` has `cellDimension = 0`.  All children are
terms.  Future profiles with dim-1 children would require a different
spine ctor admitting non-termBase heads.

## Zero-axiom verification

All declarations use propext-free structural patterns: no
match-wildcard, no auto-derived DecEq on indexed inductives, no
type-level reasoning on Nat indices via equation compiler.  The
SPIKE-1 transport from `HasEqualDim` is the only `▸` used (and it's
in the `generatingCell` ctor's signature, propext-clean by
construction since `HasEqualDim` is decided by `Nat.decEq`).

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean` per the V2-L1c.3
section.

This file CLOSES tasks #148-#152 (V2-L1c.3 through V2-L1c.7) in one
atomic commit, since Lean 4 mutual inductives must be declared
together and incremental ctor extension isn't possible.
-/

namespace LeanFX2.Foundation.PolyCell.Core

mutual

/-- The v2 certified-cell inductive.  Indexed by sort, dim, scope,
boundary, and raw erasure.  Four constructors:

* `gen` admits any term-former with proper admission + payload evidence
* `generatingCell` admits dim-(n+1) rewrite rules between certified endpoints
* `verticalComposite` composes two dim-(n+1) cells via a shared middle
* `identityCell` builds a degenerate dim-(n+1) cell from a dim-n base

There is deliberately no `horizontalComposite` constructor; raw
`RawCell.horizontalComposite` is rejected by the certifier as
`unsupportedCompH` until Gray-tensor semantics are mechanized. -/
inductive PolyCell (profile : PolyProfile) :
    (sort : CellSort) → (dim : Nat) → (scope : Nat) →
    CellBoundary profile sort dim scope →
    RawCell scope →
    Type where
  /-- ONE generic certified term-former constructor.  Subsumes v1's
  5+ per-fixture term ctors.  Adding a feature = adding ONE
  `SupportedGenerator` arm; ZERO new PolyCell ctors. -/
  | gen :
      {scope : Nat} → {generator : Generator} →
      {payload : generator.payload scope} →
      {children : RawTermChildren generator.binderShifts scope} →
      SupportedGenerator generator →
      GenPayloadEvidence generator scope payload →
      CertifiedTermSpine profile generator.childSpecs scope
        generator.binderShifts children →
      PolyCell profile generator.cellSort 0 scope
        CellBoundary.trivial
        (.termBase (.mkGen generator payload children))

  /-- Certified dim-(n+1) generating cell over two certified endpoints
  of EQUAL computed dimension, reconciled by `HasEqualDim` against a
  supported rule.  Gated by SPIKE-1's value-level dim transport. -/
  | generatingCell :
      {scope : Nat} → (rule : RuleSpec) →
      SupportedRuleSpec rule →
      {source target : RawCell scope} →
      {sourceBoundary targetBoundary :
        CellBoundary profile rule.cellSort source.dim scope} →
      HasEqualDim source target →
      PolyCell profile rule.cellSort source.dim scope
        sourceBoundary source →
      PolyCell profile rule.cellSort source.dim scope
        targetBoundary target →
      PolyCell profile rule.cellSort (source.dim + 1) scope
        (CellBoundary.endpoints source target)
        (.generatingCell rule.ruleId source target)

  /-- Certified vertical composition.  Two dim-(n+1) cells sharing a
  middle endpoint (decided by the propext-free
  `DecidableEq (RawCell)`) compose into a dim-(n+1) cell from source
  to target. -/
  | verticalComposite :
      {sort : CellSort} → {dim scope : Nat} →
      {source middle target : RawCell scope} →
      {firstRaw secondRaw : RawCell scope} →
      PolyCell profile sort (dim + 1) scope
        (CellBoundary.endpoints source middle) firstRaw →
      PolyCell profile sort (dim + 1) scope
        (CellBoundary.endpoints middle target) secondRaw →
      PolyCell profile sort (dim + 1) scope
        (CellBoundary.endpoints source target)
        (.verticalComposite firstRaw secondRaw)

  /-- Certified identity (degenerate) cell over any certified base.
  Produces a dim-(n+1) cell at boundary (base, base) from a dim-n
  base. -/
  | identityCell :
      {sort : CellSort} → {dim scope : Nat} →
      {boundary : CellBoundary profile sort dim scope} →
      {baseRaw : RawCell scope} →
      PolyCell profile sort dim scope boundary baseRaw →
      PolyCell profile sort (dim + 1) scope
        (CellBoundary.endpoints baseRaw baseRaw)
        (.identityCell baseRaw)

/-- Concrete certified-child spine consumed by `PolyCell.gen`.

PARALLEL TYPE INDICES: `childSpecs : List ChildSpec` AND
`binderShifts : List Nat`.  Each `cons` extends both in lockstep
(`headSpec :: rest` paired with `headSpec.scopeShift :: restShifts`),
so a constructible spine maintains the coherence
`binderShifts = childSpecs.map (·.scopeShift)` at the value level
(propositional, not definitional — but the type accepts both
indices independently, so no transports are needed at use sites).

Each `cons` head is a `PolyCell` cell at the head spec's
`cellSort`, `cellDimension`, and `parentScope + scopeShift`, with
raw erasure `.termBase headRaw`.  This commits the spine to dim-0
children only — correct for all fxProfile generators (whose
`cellDimension` is 0 everywhere). -/
inductive CertifiedTermSpine (profile : PolyProfile) :
    (childSpecs : List ChildSpec) →
    (parentScope : Nat) →
    (binderShifts : List Nat) →
    RawTermChildren binderShifts parentScope →
    Type where
  /-- Empty spine for a nullary generator (zero children). -/
  | nil {parentScope : Nat} :
      CertifiedTermSpine profile [] parentScope [] .childNil
  /-- Cons a head certified cell whose indices match the head spec.
  Both `childSpecs` and `binderShifts` extend in lockstep —
  `headSpec :: restSpecs` paired with `headSpec.scopeShift ::
  restShifts`.  The cons head MUST be a dim-`headSpec.cellDimension`
  cell with rawCell `.termBase headRaw` — under fxProfile this means
  dim 0 (every ChildSpec in every Generator.childSpecs has
  cellDimension = 0). -/
  | cons {parentScope : Nat}
         {headSpec : ChildSpec}
         {restSpecs : List ChildSpec}
         {restShifts : List Nat}
         {headRaw : RawTerm (parentScope + headSpec.scopeShift)}
         {restRaws : RawTermChildren restShifts parentScope}
         {headBoundary :
           CellBoundary profile headSpec.cellSort
             headSpec.cellDimension
             (parentScope + headSpec.scopeShift)} :
      PolyCell profile headSpec.cellSort headSpec.cellDimension
        (parentScope + headSpec.scopeShift) headBoundary
        (.termBase headRaw) →
      CertifiedTermSpine profile restSpecs parentScope restShifts
        restRaws →
      CertifiedTermSpine profile
        (headSpec :: restSpecs)
        parentScope
        (headSpec.scopeShift :: restShifts)
        (.childCons headRaw restRaws)

end

end LeanFX2.Foundation.PolyCell.Core
