import FX1Poly.Core.DataCanonicityViaSconing
import FX1Poly.Core.BoolElimCanonicalComputation
import FX1Poly.Core.SigmaProjectionCanonicalComputation

/-! # FX1Poly/Core/DataEliminatorProgressViaSconing
    — operational PROGRESS for the non-recursive data eliminators via the sconing fundamental (SN-058/063)

The canonicity files answer "what value does a closed well-typed data term reduce TO".  Their operational
COMPLEMENT is progress: a closed well-typed eliminator does not get STUCK — it reduces to a result.  This
file composes the two `#672`-free halves already shipped:

* the sconing FUNDAMENTAL (closed well-typed term ⟹ data-candidate member) — the explicit hypothesis,
  the Path-A fundamental theorem (`#672` / SN-043), the SAME obligation the canonicity files carry; and
* the eliminator COMPUTATION (a canonical-scrutinee eliminator reduces to a result —
  `boolElimCanonicalScrutineeReducesToBranch`, `pairCanonicalScrutineeProjectsToComponents`), shipped
  `#672`-free.

Composing them: a well-typed SCRUTINEE makes the eliminator make progress.  Restricted to the
NON-RECURSIVE eliminators (`boolElim` branch selection, `fst`/`snd` projection), whose ι fires once with
no recursive sub-term — so the computation half is fully `#672`-free.  (The recursive eliminators
`natElim`/`natRec`/`listElim` only progress `#672`-free on their base constructor; their `succ`/`cons`
step grows and needs Tait, so they are excluded here.)

* `boolElimProgressViaSconing` — a `boolElim` whose scrutinee is well-typed (bool) reduces to its
  then-branch or its else-branch.
* `pairProjectionProgressViaSconing` — for a well-typed (pair) scrutinee, `fst` and `snd` reduce to the
  scrutinee's two components (and the scrutinee reduces to a `pair` cell).

These are the progress corner of type safety: combined with the canonicity files (value shape) they say
the non-recursive data eliminators are never stuck on well-typed input — modulo the one shared `#672`
fundamental.

## Zero-axiom verification

Each theorem is the eliminator-computation theorem applied to `fundamental scrutinee scrutineeTyped`.
The local cell abbreviations are definitionally equal to the (private) ones in the computation files, so
the compositions typecheck.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- The `boolElim` cell over its three children (scrutinee, then-branch, else-branch) — definitionally the
private `boolElimCellOn` of `BoolElimCanonicalComputation`. -/
private abbrev boolElimCellOn {scope : Nat} (scrutinee thenBranch elseBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_boolElim ()
    (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil)))

/-- The unary `fst` projection cell — definitionally the private `fstCell` of
`SigmaProjectionCanonicalComputation`. -/
private abbrev fstCell {scope : Nat} (scrutinee : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_fst () (.childCons scrutinee .childNil)

/-- The unary `snd` projection cell — definitionally the private `sndCell` of
`SigmaProjectionCanonicalComputation`. -/
private abbrev sndCell {scope : Nat} (scrutinee : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_snd () (.childCons scrutinee .childNil)

/-- **`boolElim` progress on a well-typed scrutinee (SN-063).**  Given the fundamental obligation (closed
well-typed bool ⟹ bool-candidate member) and a well-typed scrutinee, the `boolElim` reduces to its
then-branch or its else-branch — it is never stuck.  Composition of the fundamental with the `#672`-free
`boolElimCanonicalScrutineeReducesToBranch`.  The fundamental is the sole `#672` obligation. -/
theorem boolElimProgressViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0, isWellTyped term → CanonicalFormsPredicate boolIsValue term)
    {scrutinee thenBranch elseBranch : RawTerm 0}
    (scrutineeTyped : isWellTyped scrutinee) :
    StepStar (boolElimCellOn scrutinee thenBranch elseBranch) thenBranch ∨
      StepStar (boolElimCellOn scrutinee thenBranch elseBranch) elseBranch :=
  boolElimCanonicalScrutineeReducesToBranch (fundamental scrutinee scrutineeTyped)

/-- **`fst`/`snd` projection progress on a well-typed scrutinee (SN-058).**  Given the fundamental
obligation (closed well-typed pair ⟹ pair-candidate member) and a well-typed scrutinee, the scrutinee
reduces to a `pair` cell and `fst`/`snd` reduce to its two components — the projections are never stuck.
Composition of the fundamental with the `#672`-free `pairCanonicalScrutineeProjectsToComponents`.  The
fundamental is the sole `#672` obligation. -/
theorem pairProjectionProgressViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0, isWellTyped term → CanonicalFormsPredicate isPairValue term)
    {scrutinee : RawTerm 0}
    (scrutineeTyped : isWellTyped scrutinee) :
    ∃ firstComponent secondComponent : RawTerm 0,
      StepStar scrutinee (pairCell firstComponent secondComponent) ∧
        StepStar (fstCell scrutinee) firstComponent ∧
          StepStar (sndCell scrutinee) secondComponent :=
  pairCanonicalScrutineeProjectsToComponents (fundamental scrutinee scrutineeTyped)

end FX1Poly.Core
