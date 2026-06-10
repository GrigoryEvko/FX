import FX1Poly.Core.DataCanonicityViaSconing
import FX1Poly.Core.BoolElimCanonicalComputation
import FX1Poly.Core.SigmaProjectionCanonicalComputation
import FX1Poly.Core.OptionEitherMatchCanonicalComputation
import FX1Poly.Core.IdentityEliminatorCanonicalComputation

/-! # FX1Poly/Core/DataEliminatorProgressViaSconing
    — operational PROGRESS for the non-recursive data eliminators via the sconing fundamental

The canonicity files answer "what value does a closed well-typed data term reduce TO".  Their operational
COMPLEMENT is progress: a closed well-typed eliminator does not get STUCK — it reduces to a result.  This
file composes the two halves:

* the sconing FUNDAMENTAL (closed well-typed term ⟹ data-candidate member) — the explicit hypothesis,
  the Path-A fundamental theorem, the SAME obligation the canonicity files carry; and
* the eliminator COMPUTATION (a canonical-scrutinee eliminator reduces to a result —
  `boolElimCanonicalScrutineeReducesToBranch`, `pairCanonicalScrutineeProjectsToComponents`), proved
  outright.

Composing them: a well-typed SCRUTINEE makes the eliminator make progress.  This file covers ALL the
NON-RECURSIVE eliminators (`boolElim` branch selection, `fst`/`snd` projection, `optionMatch`/`eitherMatch`
case selection, `idJ`/`idStrictRec` base selection), whose ι fires once with no recursive sub-term — so the
computation half needs no fundamental.  (The recursive eliminators `natElim`/`natRec`/`listElim` only
progress on their base constructor; their `succ`/`cons` step grows and needs Tait, so they are
excluded here.)

* `boolElimProgressViaSconing` — a `boolElim` whose scrutinee is well-typed (bool) reduces to its
  then-branch or its else-branch.
* `pairProjectionProgressViaSconing` — for a well-typed (pair) scrutinee, `fst` and `snd` reduce to the
  scrutinee's two components (and the scrutinee reduces to a `pair` cell).
* `optionMatchProgressViaSconing` / `eitherMatchProgressViaSconing` — an `optionMatch` / `eitherMatch`
  whose scrutinee is well-typed (option / either) reduces to a branch (the `none`-branch, or a branch
  applied to the wrapped payload).
* `idJProgressViaSconing` / `idStrictRecProgressViaSconing` — an `idJ` / `idStrictRec` whose witness is
  well-typed (an identity proof) reduces to its base case.

These are the progress corner of type safety: combined with the canonicity files (value shape) they say
EVERY non-recursive data eliminator is never stuck on well-typed input — modulo the one shared
fundamental.

## Zero-axiom verification

Each theorem is the eliminator-computation theorem applied to `fundamental scrutinee scrutineeTyped`.
The local cell abbreviations are definitionally equal to the (private) ones in the computation files, so
the compositions typecheck.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- The Phase-Z `boolElim` cell over its four children — author order `(motive, scrutinee, thenBranch,
elseBranch)`, emitting the canonical spine `(motive, thenBranch, elseBranch, scrutinee)` with the motive a term
under one binder.  Definitionally the private `boolElimCellOn` of `BoolElimCanonicalComputation`. -/
private abbrev boolElimCellOn {scope : Nat} (motive : RawTerm (scope + 1))
    (scrutinee thenBranch elseBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_boolElim ()
    (.childCons motive
      (.childCons thenBranch
        (.childCons elseBranch
          (.childCons scrutinee .childNil))))

/-- The unary `fst` projection cell — definitionally the private `fstCell` of
`SigmaProjectionCanonicalComputation`. -/
private abbrev fstCell {scope : Nat} (scrutinee : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_fst () (.childCons scrutinee .childNil)

/-- The unary `snd` projection cell — definitionally the private `sndCell` of
`SigmaProjectionCanonicalComputation`. -/
private abbrev sndCell {scope : Nat} (scrutinee : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_snd () (.childCons scrutinee .childNil)

/-- **`boolElim` progress on a well-typed scrutinee.**  Given the fundamental obligation (closed
well-typed bool ⟹ bool-candidate member) and a well-typed scrutinee, the `boolElim` reduces to its
then-branch or its else-branch — it is never stuck.  Composition of the fundamental with the
fundamental-free `boolElimCanonicalScrutineeReducesToBranch`.  The fundamental is the sole obligation. -/
theorem boolElimProgressViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0, isWellTyped term → CanonicalFormsPredicate boolIsValue term)
    {motive : RawTerm 1} {scrutinee thenBranch elseBranch : RawTerm 0}
    (scrutineeTyped : isWellTyped scrutinee) :
    StepStar (boolElimCellOn motive scrutinee thenBranch elseBranch) thenBranch ∨
      StepStar (boolElimCellOn motive scrutinee thenBranch elseBranch) elseBranch :=
  boolElimCanonicalScrutineeReducesToBranch (motive := motive) (fundamental scrutinee scrutineeTyped)

/-- **`fst`/`snd` projection progress on a well-typed scrutinee.**  Given the fundamental
obligation (closed well-typed pair ⟹ pair-candidate member) and a well-typed scrutinee, the scrutinee
reduces to a `pair` cell and `fst`/`snd` reduce to its two components — the projections are never stuck.
Composition of the fundamental with the fundamental-free `pairCanonicalScrutineeProjectsToComponents`.  The
fundamental is the sole obligation. -/
theorem pairProjectionProgressViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0, isWellTyped term → CanonicalFormsPredicate isPairValue term)
    {scrutinee : RawTerm 0}
    (scrutineeTyped : isWellTyped scrutinee) :
    ∃ firstComponent secondComponent : RawTerm 0,
      StepStar scrutinee (pairCell firstComponent secondComponent) ∧
        StepStar (fstCell scrutinee) firstComponent ∧
          StepStar (sndCell scrutinee) secondComponent :=
  pairCanonicalScrutineeProjectsToComponents (fundamental scrutinee scrutineeTyped)

/-- The application cell `app function argument` — definitionally the private `applyCell` of
`OptionEitherMatchCanonicalComputation` (the shape a `some`/`inl`/`inr` branch is applied to its payload). -/
private abbrev applyCell {scope : Nat} (function argument : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_app () (.childCons function (.childCons argument .childNil))

/-- The `optionMatch` cell over its three children — definitionally the private `optionMatchCellOn`. -/
private abbrev optionMatchCellOn {scope : Nat}
    (scrutinee noneBranch someBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_optionMatch ()
    (.childCons scrutinee (.childCons noneBranch (.childCons someBranch .childNil)))

/-- The `eitherMatch` cell over its three children — definitionally the private `eitherMatchCellOn`. -/
private abbrev eitherMatchCellOn {scope : Nat}
    (scrutinee leftBranch rightBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_eitherMatch ()
    (.childCons scrutinee (.childCons leftBranch (.childCons rightBranch .childNil)))

/-- The `idJ` cell over its two children (base case, witness) — definitionally the private `idJCellOn`. -/
private abbrev idJCellOn {scope : Nat} (baseCase witness : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_idJ () (.childCons baseCase (.childCons witness .childNil))

/-- The `idStrictRec` cell over its two children — definitionally the private `idStrictRecCellOn`. -/
private abbrev idStrictRecCellOn {scope : Nat} (baseCase witness : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_idStrictRec () (.childCons baseCase (.childCons witness .childNil))

/-- **`optionMatch` progress on a well-typed scrutinee.**  Given the fundamental obligation
(closed well-typed option ⟹ option-candidate member) and a well-typed scrutinee, the `optionMatch` reduces
to its none-branch or to its some-branch applied to the wrapped payload — never stuck.  Composition of the
fundamental with the fundamental-free `optionMatchCanonicalScrutineeReduces`. -/
theorem optionMatchProgressViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0, isWellTyped term → CanonicalFormsPredicate isOptionValue term)
    {scrutinee noneBranch someBranch : RawTerm 0}
    (scrutineeTyped : isWellTyped scrutinee) :
    StepStar (optionMatchCellOn scrutinee noneBranch someBranch) noneBranch ∨
      ∃ payload : RawTerm 0,
        StepStar scrutinee (optionSomeCell payload) ∧
          StepStar (optionMatchCellOn scrutinee noneBranch someBranch)
            (applyCell someBranch payload) :=
  optionMatchCanonicalScrutineeReduces (fundamental scrutinee scrutineeTyped)

/-- **`eitherMatch` progress on a well-typed scrutinee.**  Given the fundamental obligation
(closed well-typed either ⟹ either-candidate member) and a well-typed scrutinee, the `eitherMatch` reduces
to its left-branch or right-branch applied to the wrapped payload — never stuck.  Composition of the
fundamental with the fundamental-free `eitherMatchCanonicalScrutineeReduces`. -/
theorem eitherMatchProgressViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0, isWellTyped term → CanonicalFormsPredicate isEitherValue term)
    {scrutinee leftBranch rightBranch : RawTerm 0}
    (scrutineeTyped : isWellTyped scrutinee) :
    (∃ payload : RawTerm 0,
        StepStar scrutinee (eitherInlCell payload) ∧
          StepStar (eitherMatchCellOn scrutinee leftBranch rightBranch)
            (applyCell leftBranch payload)) ∨
      ∃ payload : RawTerm 0,
        StepStar scrutinee (eitherInrCell payload) ∧
          StepStar (eitherMatchCellOn scrutinee leftBranch rightBranch)
            (applyCell rightBranch payload) :=
  eitherMatchCanonicalScrutineeReduces (fundamental scrutinee scrutineeTyped)

/-- **`idJ` progress on a well-typed witness.**  Given the fundamental obligation (closed
well-typed identity proof ⟹ refl-candidate member) and a well-typed witness, the `idJ` reduces to its base
case — never stuck.  Composition of the fundamental with the fundamental-free
`idJCanonicalWitnessReducesToBase`. -/
theorem idJProgressViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0, isWellTyped term → CanonicalFormsPredicate isReflValue term)
    {baseCase witness : RawTerm 0}
    (witnessTyped : isWellTyped witness) :
    StepStar (idJCellOn baseCase witness) baseCase :=
  idJCanonicalWitnessReducesToBase (fundamental witness witnessTyped)

/-- **`idStrictRec` progress on a well-typed witness.**  Symmetric to `idJProgressViaSconing`:
given the fundamental obligation and a well-typed witness, the `idStrictRec` reduces to its base case.
Composition of the fundamental with the fundamental-free `idStrictRecCanonicalWitnessReducesToBase`. -/
theorem idStrictRecProgressViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0, isWellTyped term → CanonicalFormsPredicate isReflValue term)
    {baseCase witness : RawTerm 0}
    (witnessTyped : isWellTyped witness) :
    StepStar (idStrictRecCellOn baseCase witness) baseCase :=
  idStrictRecCanonicalWitnessReducesToBase (fundamental witness witnessTyped)

end FX1Poly.Core
