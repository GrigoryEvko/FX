import FX1Poly.Core.PolyCell

/-! # Foundation/PolyCell/Core/CertifiedTermSpineProjections — head / tail

V2-L3.1 phase D step 2 (2026-05-27).  Ships structural projections on
`CertifiedTermSpine`: given a spine whose `RawTermChildren` index
is `.childCons headRaw restRaws`, extract:

  * the head cell `PolyCell ... (.termBase headRaw)`, together with
    its (existentially-bound) boundary, as a sigma pair, and
  * the tail spine `CertifiedTermSpine ... restRaws`.

## Why this matters for SR

The termBase shape pin shipped in V2-L3.1 phase D step 1 yields a
spine success witness: `∃ spine, certifyChildrenInlineFueled? ...
= .ok spine`.  But the spine itself is an opaque inductive over the
parent's children — to feed the SR proof's cong + iota arms, we need
to **destructure** the spine into per-child certificates.

For a composite generator like `lam body` (children =
`.childCons body .childNil`), destructuring gives:

  * head cell: `PolyCell profile lamSpec.cellSort 0 (scope+1) ()
                  (.termBase body)`
  * tail spine: empty (`.nil`)

The head cell IS the certificate of body — at dim 0 with trivial
boundary (since every fxProfile ChildSpec has dim 0).

## Structural-projection discipline

The spine type `CertifiedTermSpine profile (headSpec :: restSpecs)
parentScope (headSpec.scopeShift :: restShifts) (.childCons headRaw
restRaws)` has indices that FORCE the constructor to be `.cons` —
the `.nil` constructor requires `[]` for the spec list, so it
mismatches `headSpec :: restSpecs`.  Lean's pattern matcher derives
this via `List.cons.injEq` and produces a single-arm match without
a `.nil` impossible case.

This is the zero-axiom destructor pattern: pattern-match through
the spine constructor, return the carried head + tail as a sigma
pair (head's boundary is existentially bound by the cons
constructor, so it must surface in the destructor's return type).

## Dim-0 boundary uniqueness (now shipped via `generalize` + `subst`)

For fxProfile (every ChildSpec has `cellDimension = 0`), the
existential boundary collapses: `CellBoundary profile sort 0 scope
= Unit` is a singleton, so the boundary is uniquely `()` =
`CellBoundary.trivial`.  The dedicated `headAtDim0` helper performs
the dim-cast in one step.

The implementation pattern: `subst` cannot directly dispatch
`hDim : headSpec.cellDimension = 0` because the LHS is a field
projection (not a free variable).  Workaround:

  1. Destructure the spine via `headWithBoundary` to expose
     `boundary` and `headCell`, both indexed by
     `headSpec.cellDimension`.
  2. `generalize hCellDim : headSpec.cellDimension = cellDim at *`
     introduces `cellDim` as a fresh variable, rewriting it
     everywhere (including in `hDim`).  Now `hDim : cellDim = 0`.
  3. `subst hDim` substitutes `cellDim := 0` everywhere.  After
     subst, `boundary : CellBoundary profile sort 0 scope`,
     whose type reduces to `Unit` (definitional unfolding of the
     `_, 0, _` arm of `CellBoundary`).
  4. `Subsingleton.elim boundary CellBoundary.trivial` produces
     the boundary equation, since `Unit` has a `Subsingleton`
     instance and Lean sees through the `def`-reduction to apply
     it.  Cast the cell via this equation.

## What this does NOT do

This file ships PURE STRUCTURAL projections — no fuel reasoning, no
soundness lifting, no Certified-level wrapping.  Those higher
operations come later in the phase D progression.  The projections
here are the **substrate**: given an actual spine value, expose its
head and tail components.

## Zero-axiom verification

All declarations are direct pattern matches on the inductive's
non-nil constructor.  No `simp`, no `omega`, no propext-touching
tactics.  Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- **Spine head projection (existential boundary).**

Given a `CertifiedTermSpine` whose `RawTermChildren` index is
`.childCons headRaw restRaws` and whose `childSpecs` index is
`headSpec :: restSpecs`, extract the head's certified cell as a
sigma pair `(boundary, headCell)`.

The boundary is existentially bound because the `cons` constructor
chose it at construction time; the destructor surfaces it as data.
For dim-0 head cells (every fxProfile ChildSpec), the boundary is
trivially `()` (unique inhabitant of `Unit`), but the general
sigma form is dim-agnostic. -/
def CertifiedTermSpine.headWithBoundary
    {profile : PolyProfile} {headSpec : ChildSpec}
    {restSpecs : List ChildSpec} {parentScope : Nat}
    {restShifts : List Nat}
    {headRaw : RawTerm (parentScope + headSpec.scopeShift)}
    {restRaws : RawTermChildren restShifts parentScope}
    (spine :
      CertifiedTermSpine profile (headSpec :: restSpecs) parentScope
        (headSpec.scopeShift :: restShifts) (.childCons headRaw restRaws)) :
    Σ' (headBoundary :
          CellBoundary profile headSpec.cellSort
            headSpec.cellDimension
            (parentScope + headSpec.scopeShift)),
      PolyCell profile headSpec.cellSort headSpec.cellDimension
        (parentScope + headSpec.scopeShift) headBoundary
        (.termBase headRaw) :=
  match spine with
  | .cons (headBoundary := boundary) headCell _ => ⟨boundary, headCell⟩

/-- **Spine tail projection.**

Given a `CertifiedTermSpine` whose `RawTermChildren` index is
`.childCons headRaw restRaws`, extract the tail spine over
`restRaws`. -/
def CertifiedTermSpine.tail
    {profile : PolyProfile} {headSpec : ChildSpec}
    {restSpecs : List ChildSpec} {parentScope : Nat}
    {restShifts : List Nat}
    {headRaw : RawTerm (parentScope + headSpec.scopeShift)}
    {restRaws : RawTermChildren restShifts parentScope}
    (spine :
      CertifiedTermSpine profile (headSpec :: restSpecs) parentScope
        (headSpec.scopeShift :: restShifts) (.childCons headRaw restRaws)) :
    CertifiedTermSpine profile restSpecs parentScope restShifts
      restRaws :=
  match spine with
  | .cons _ restSpine => restSpine

/-- **Spine nil-uniqueness (no information loss on an empty spine).**

When the spine's children index is `.childNil`, the spec list must be
`[]` and the shift list must be `[]` (by `RawTermChildren`'s typing),
so the spine must be `.nil`.  This lemma surfaces that fact for
downstream callers needing to derive `spine = .nil` propositionally
(e.g., when discharging tail-is-nil after destructuring the head).

Closes by pattern matching: the `.nil` arm produces `rfl`; the
`.cons` arm is impossible because its index pattern (`headSpec ::
restSpecs`) cannot match `[]`. -/
theorem CertifiedTermSpine.eq_nil_of_childNil
    {profile : PolyProfile} {parentScope : Nat}
    (spine :
      CertifiedTermSpine profile [] parentScope []
        (.childNil : RawTermChildren [] parentScope)) :
    spine = .nil :=
  match spine with
  | .nil => rfl

/-! ## Dim-0 head extraction (the SR projection one-liner)

The `headAtDim0` helper collapses the sigma-wrapped boundary from
`headWithBoundary` into a plain `PolyCell` at dim 0 with
`CellBoundary.trivial` boundary, given a hypothesis that the
head spec's dim is 0.

This is the SR projection's load-bearing helper: combined with the
termBase shape pin (phase D step 1) and `headWithBoundary` /
`tail` (this file's other projections), the chain reads as

  `Certified (lam body)`
  → spine success (via shape pin)
  → `⟨boundary, headCell⟩` (via `headWithBoundary`)
  → `PolyCell profile .term 0 (scope+1) trivial (.termBase body)`
    (via `headAtDim0 rfl`)

The final cell IS the structural certificate of `body`.
-/

/-- **Dim-0 spine head extraction.**

When the head spec's dim is 0 (every fxProfile ChildSpec), the
boundary collapses to `Unit` via `CellBoundary_zero`.  This helper
returns just the head cell at dim 0 with the canonical trivial
boundary, hiding the sigma when callers statically know the dim.

The dim-0 hypothesis `headSpec.cellDimension = 0` is passed
explicitly; at every fxProfile call site it discharges by `rfl`
(since `gen_lam.childSpecs.head.cellDimension = 0` etc are all
definitional).

Implementation pattern: destructure the spine, generalize
`headSpec.cellDimension` to a fresh variable, `subst` through
`hDim`, then use `Subsingleton.elim` to identify the boundary
with `CellBoundary.trivial`. -/
def CertifiedTermSpine.headAtDim0
    {profile : PolyProfile} {headSpec : ChildSpec}
    {restSpecs : List ChildSpec} {parentScope : Nat}
    {restShifts : List Nat}
    {headRaw : RawTerm (parentScope + headSpec.scopeShift)}
    {restRaws : RawTermChildren restShifts parentScope}
    (hDim : headSpec.cellDimension = 0)
    (spine :
      CertifiedTermSpine profile (headSpec :: restSpecs) parentScope
        (headSpec.scopeShift :: restShifts) (.childCons headRaw restRaws)) :
    PolyCell profile headSpec.cellSort 0
      (parentScope + headSpec.scopeShift) CellBoundary.trivial
      (.termBase headRaw) := by
  obtain ⟨boundary, headCell⟩ := spine.headWithBoundary
  -- After destructuring, `boundary : CellBoundary profile
  -- headSpec.cellSort headSpec.cellDimension (...)` and `headCell :
  -- PolyCell profile headSpec.cellSort headSpec.cellDimension (...)
  -- boundary (.termBase headRaw)`.
  --
  -- `subst` cannot operate on `hDim` directly because the LHS
  -- (`headSpec.cellDimension`) is a field projection.  Generalize it
  -- to a fresh variable first.
  generalize hCellDim : headSpec.cellDimension = cellDim at boundary headCell hDim
  -- After generalize: `cellDim` is fresh, `hDim : cellDim = 0`,
  -- `boundary` and `headCell` are indexed by `cellDim`.
  subst hDim
  -- `cellDim` substituted to `0` everywhere.  Now `boundary :
  -- CellBoundary profile sort 0 scope`, which is `Unit` by
  -- definitional reduction of `CellBoundary`'s `_, 0, _` arm.
  --
  -- Lean's TC inference doesn't see through the `def` to find
  -- `Subsingleton Unit`, so we provide the instance explicitly via
  -- `inferInstanceAs (Subsingleton Unit)`, which Lean accepts at
  -- the equivalent (definitionally reduced) type.
  haveI : Subsingleton (CellBoundary profile headSpec.cellSort 0
                          (parentScope + headSpec.scopeShift)) :=
    inferInstanceAs (Subsingleton Unit)
  have boundaryEq : boundary = CellBoundary.trivial :=
    Subsingleton.elim _ _
  exact boundaryEq ▸ headCell

/-! ## Smokes on the structural projections

Concrete fixtures demonstrating the destructors work on real spine
values.  Each smoke uses pattern matching internally and exercises
both the destructor and Lean's matcher's ability to derive `.nil`
impossibility from index mismatch.
-/

/-- **Smoke: project the head from a lam-shaped spine via the dim-0
helper.**

Exercises `headAtDim0` on the spine produced by certifying a lambda's
body: `lam body` has child spec `[lamSpec]` with `lamSpec.cellDimension
= 0` and `lamSpec.scopeShift = 1`.  The destructor extracts the body's
certified cell at scope `parentScope + 1`. -/
example {profile : PolyProfile} {parentScope : Nat}
    {body : RawTerm (parentScope + 1)}
    (spine :
      CertifiedTermSpine profile
        [{cellSort := .term, cellDimension := 0, scopeShift := 1}]
        parentScope [1] (.childCons body .childNil)) :
    PolyCell profile .term 0 (parentScope + 1)
      CellBoundary.trivial (.termBase body) :=
  CertifiedTermSpine.headAtDim0 rfl spine


/-- **Smoke: extract head from a single-child spine via pattern match.**

For a `[headSpec]` spine over `.childCons body .childNil`, pattern
matching with `.cons` exposes the head cell.  Demonstrates Lean's
matcher correctly derives that `.nil` is impossible for this index
configuration (single-spec + cons-children). -/
example {profile : PolyProfile} {headSpec : ChildSpec}
    {parentScope : Nat}
    {body : RawTerm (parentScope + headSpec.scopeShift)}
    (spine :
      CertifiedTermSpine profile [headSpec] parentScope
        [headSpec.scopeShift] (.childCons body .childNil)) :
    Σ' (headBoundary :
          CellBoundary profile headSpec.cellSort
            headSpec.cellDimension
            (parentScope + headSpec.scopeShift)),
      PolyCell profile headSpec.cellSort headSpec.cellDimension
        (parentScope + headSpec.scopeShift) headBoundary
        (.termBase body) :=
  spine.headWithBoundary

/-- **Smoke: extract tail from a single-child spine.**

The tail of a `[headSpec]` spine over `.childCons body .childNil`
is a `.nil` spine — type-forced by the index mismatch on the spec
list (`[]` vs `[headSpec]` ruled out by injectivity). -/
example {profile : PolyProfile} {headSpec : ChildSpec}
    {parentScope : Nat}
    {body : RawTerm (parentScope + headSpec.scopeShift)}
    (spine :
      CertifiedTermSpine profile [headSpec] parentScope
        [headSpec.scopeShift] (.childCons body .childNil)) :
    CertifiedTermSpine profile [] parentScope []
      (.childNil : RawTermChildren [] parentScope) :=
  spine.tail

end FX1Poly.Core
