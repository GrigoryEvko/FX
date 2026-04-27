import FX.KernelMTT.Term
import FX.KernelMTT.Mode
import FX.KernelMTT.Modality
import FX.KernelMTT.TwoCells

/-!
# Modality operations: smart constructors and admissibility

Helpers around the modality-related `Term` constructors
(`modIntro`, `modElim`, `coerceCell`) plus admissibility
predicates that decide whether a given modality applies at a
given mode.  The V1.5 MTT checker consumes this module — it's
the operational layer between the bare `Term` AST (V1.3 + W2)
and the typing rules.

## W2 update — context-size threading + TermArgs

After W2 (well-scoped Term : Nat → Type), every Term operation
threads the context-size index `n` through.  Smart constructors
that build a binder (`modElim`) take the body at `Term (n+1)`;
those that wrap a value (`modIntro`, `coerceCell`) keep it at
`Term n`.

Variable-arity arg lists became `TermArgs n` (a custom mutual
inductive paired with Term, since `List (Term n)` is forbidden
by Lean 4's nested-inductive rules).  `eraseCoercions` recurses
through binders with the correct `n+1` and over args via
`eraseCoercionsArgs`.

## What's here

  * `Modality.isAdmissibleAt` — does the modality apply at the
    given mode?  Consults `Mode.config`'s `modalityNames`
    list per mode.  Companion to the existing
    `Modality.admissibleAt : Mode → List Modality` (lookup by
    mode); this predicate is the boolean-valued reverse query.
  * `Term.modIntroAt` / `Term.modElimAt` — smart constructors
    for the modality intro / elim Term forms.  Pure wrappers;
    admissibility checks live at the V1.5 typing boundary.
  * `Term.coerceVia` — build a `coerceCell` Term applying a
    `SubsumptionCell` to a term.
  * `Modality.canSubsume?` — wraps `SubsumptionCell.subsumes`'s
    fuel-bounded BFS.
  * `Term.eraseCoercions` — strip every `coerceCell`
    constructor recursively, descending into binders + args.

## Trust layer

`FX/KernelMTT/**` is UNTRUSTED scaffold.  Same zero-`sorry` /
no-axiom-outside-AXIOMS.md discipline as Term.lean.
`canSubsume?` wraps `SubsumptionCell.subsumes`, which is itself
fuel-bounded BFS; same boundary as legacy reduction's `whnf`.
`eraseCoercions` is `partial def` mutual with
`eraseCoercionsArgs`.

## Cross-references

  * `fx_modecat.md` §3 — modalities and per-mode admissibility
  * `fx_modecat.md` §5 — subsumption 2-cells
  * `fx_modecat.md` §6 — collision rules (missing 2-cells)
  * `FX/KernelMTT/Term.lean` — the AST these operations build
  * `FX/KernelMTT/TwoCells.lean` — the 2-cell registry
  * `FX/KernelMTT/Mode.lean` — per-mode admissibility data
-/

namespace FX.KernelMTT

-- `Modality.isAdmissibleAt : Modality → Mode → Bool` and
-- `Modality.admissibleAt   : Mode → List Modality` already live
-- in `FX/KernelMTT/Modality.lean` (R0.3).  This module re-uses
-- those rather than redefining; downstream callers get them via
-- the standard `import FX.KernelMTT.Modality` chain.

namespace Term

/-- Smart constructor for modality intro: lift `term` from
    `sourceMode` across `modality` into `targetMode`.  Pure
    wrapper around `Term.modIntro`; admissibility is checked
    at the V1.5 typing boundary, not here. -/
@[inline]
def modIntroAt {n : Nat} (sourceMode targetMode : Mode)
    (modality : Modality) (term : Term n) : Term n :=
  .modIntro sourceMode targetMode modality term

/-- Smart constructor for modality elim: unwrap a modal value
    `modalTerm` from `sourceMode` and continue with `body` at
    `targetMode`.  Body lives in the context extended by the
    unwrapped binding (Term (n+1)) — Lean enforces this at the
    type level. -/
@[inline]
def modElimAt {n : Nat} (sourceMode targetMode : Mode)
    (modality : Modality)
    (modalTerm : Term n) (body : Term (n+1)) : Term n :=
  .modElim sourceMode targetMode modality modalTerm body

/-- Apply a 2-cell coercion to `term`.  The cell's modality is
    extracted from the `SubsumptionCell` record, eliminating the
    chance of pairing a cell from one modality with a term
    intended for another. -/
@[inline]
def coerceVia {n : Nat} (cell : SubsumptionCell)
    (term : Term n) : Term n :=
  .coerceCell cell.modality cell.fromGrade cell.toGrade term

-- `eraseCoercions` strips every `coerceCell` constructor from
-- a term recursively.  Useful for test assertions that compare
-- two terms "modulo subsumption coercions" — when the V1.5
-- checker inserts `coerceCell` nodes during inference, the
-- underlying term should structurally match the input modulo
-- those wrappers.
--
-- Recurses through binders at the correct `n+1` extended
-- context — Lean's type checker enforces the threading; an
-- incorrect `n` would not type-check.  Mutual with
-- `eraseCoercionsArgs` over `TermArgs n` for the variable-
-- arity arg lists.  Marked `partial` for the same reason
-- `Term.structEq` does.
mutual

/-- Strip every `coerceCell` constructor from `term`, descending
    recursively into binders and arg lists. -/
partial def eraseCoercions {n : Nat} : Term n → Term n
  | .coerceCell _ _ _ inner => eraseCoercions inner
  | .var m i => .var m i
  | .app m f a => .app m (eraseCoercions f) (eraseCoercions a)
  | .lam m g d b =>
    .lam m g (eraseCoercions d) (eraseCoercions b)
  | .pi m g d b e =>
    .pi m g (eraseCoercions d) (eraseCoercions b) e
  | .sigma m g d b =>
    .sigma m g (eraseCoercions d) (eraseCoercions b)
  | .type m l => .type m l
  | .forallLevel m b => .forallLevel m (eraseCoercions b)
  | .const m name => .const m name
  | .ind m name args =>
    .ind m name (eraseCoercionsArgs args)
  | .ctor m name i ts vs =>
    .ctor m name i (eraseCoercionsArgs ts) (eraseCoercionsArgs vs)
  | .indRec m name mot ms tgt =>
    .indRec m name (eraseCoercions mot)
      (eraseCoercionsArgs ms) (eraseCoercions tgt)
  | .coind m name args =>
    .coind m name (eraseCoercionsArgs args)
  | .coindUnfold m name ts arms =>
    .coindUnfold m name
      (eraseCoercionsArgs ts) (eraseCoercionsArgs arms)
  | .coindDestruct m name i tgt =>
    .coindDestruct m name i (eraseCoercions tgt)
  | .id m ty l r =>
    .id m (eraseCoercions ty)
      (eraseCoercions l) (eraseCoercions r)
  | .refl m w => .refl m (eraseCoercions w)
  | .idJ m mot base eq =>
    .idJ m (eraseCoercions mot)
      (eraseCoercions base) (eraseCoercions eq)
  | .hit m name args =>
    .hit m name (eraseCoercionsArgs args)
  | .hitMk m name i ts vs =>
    .hitMk m name i (eraseCoercionsArgs ts) (eraseCoercionsArgs vs)
  | .hitRec m name mot dms pps tgt =>
    .hitRec m name (eraseCoercions mot)
      (eraseCoercionsArgs dms) (eraseCoercionsArgs pps)
      (eraseCoercions tgt)
  | .modIntro src tgt mod inner =>
    .modIntro src tgt mod (eraseCoercions inner)
  | .modElim src tgt mod modT body =>
    .modElim src tgt mod
      (eraseCoercions modT) (eraseCoercions body)
  | .transport ep src =>
    .transport (eraseCoercions ep) (eraseCoercions src)

partial def eraseCoercionsArgs {n : Nat} :
    TermArgs n → TermArgs n
  | .nil       => .nil
  | .cons t ts => .cons (eraseCoercions t) (eraseCoercionsArgs ts)

end

end Term

namespace Modality

/-- Find whether a chain of subsumption 2-cells witnesses
    `fromGrade ⇒ toGrade` on `modality`, or `false` if no chain
    exists in the registry.  Wraps `SubsumptionCell.subsumes`'s
    fuel-bounded BFS.

    The V1.6 checker calls this at every coercion site; on
    `false`, surfaces `T_subsume` with the modality + grade pair
    so callers see a structured "subsumption unreachable"
    diagnostic rather than a hung typecheck.

    Returns boolean reachability (true ⇔ a chain exists).
    Witness-extraction (returning the cell list itself) belongs
    to V1.6 where the checker also wants the cell list for
    proof-cache keys.  Kept Bool here to match the existing
    TwoCells API surface; V1.6 will extend. -/
def canSubsume? (modality : Modality)
    (fromGrade toGrade : String) : Bool :=
  SubsumptionCell.subsumes modality fromGrade toGrade

/-- Lookup the per-mode modality config for `mode`.  Re-export
    from `Mode.config` with a name that reads naturally at call
    sites in the V1.5 checker. -/
@[inline]
def admittedAt (mode : Mode) : List String :=
  (Mode.config mode).modalityNames

end Modality

end FX.KernelMTT
