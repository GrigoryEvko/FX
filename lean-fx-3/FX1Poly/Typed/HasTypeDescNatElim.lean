import FX1Poly.Typed.HasTypeDescNatIntro
import FX1Poly.Typed.NatElimComputingCanonicity
import FX1Poly.Typed.RecursorHostFold

/-! # FX1Poly/Typed/HasTypeDescNatElim — the RECURSIVE Nat eliminator judgments + typed recursive
    ι-computation (CAN-1 / DI-5f: the recursive-eliminator wall the DI-5 track deferred).

DI-5a..5e typed the non-recursive eliminators (boolElim / eitherMatch / optionMatch / Σ-projections /
idJ).  `natElim` / `natRec` are the RECURSIVE eliminators.  Under the Phase-Z SUBSTITUTING succ-ι the
reduct is `succBranch[var 0 := natElim m z s p, var 1 := p]` (a 2-variable substitution into the
two-binder succ-branch), NOT an app-chain — the recursive call appears as the var-0 substituent.

## The engine-separation wall, and its resolution

The non-recursive eliminators typed their ι-reducts by `HasTypeDescPi.piElim`.  That CANNOT work here:
the substituted reduct mixes the DATA-ENGINE predecessor (a nat value, deliberately NOT grown-typable
in the cascade-free standalone-engine architecture) into the succ-branch.  This is the
recursive-eliminator engine-separation finding (#1078) hitting the elimination layer, now sharpened by
the substituting ι: typing `subst (cons recursiveCall (singleton predecessor)) succBranch` requires a
2-variable TYPED substitution lemma that the standalone engine does NOT have.

Resolution (the standalone-engine CONDITIONAL pattern): `HasTypeDescNatElim` has TWO arms:

  * `natElimIntro` — the Phase-Z eliminator cell `natElim(motive, z, sb, s) : C` from a data-engine
    scrutinee `s : Nat`, a grown-typed base `z : C`, a grown-typed step `sb` (at the step-function type
    under two binders), and the stored motive.
  * `substitutedReductTyped` — the succ-ι reduct `natElimSuccContractum motive z sb p` is typed at `C`
    as an explicit PREMISE (the standalone-engine pattern: HasTypeDescDescElim's iota-computation arms
    carry the computed-form typing as input, because the 2-variable typed substitution lemma is the
    missing piece — the GTL substitution follow-on seeding this lane's follow-up task).

`HasTypeDescNatRec` is the structurally identical twin for `gen_natRec`.

## The headline: typed RECURSIVE ι-computation (CONDITIONAL)

`natElimSuccIotaComputesTyped` (★): for a data-typed predecessor and typed branches, GIVEN the reduct
typing, the eliminator `natElim(m, z, sb, succ p)` is typed at `C`, ι-steps to
`natElimSuccContractum m z sb p` (`Step.iotaNatElimSucc`), and the reduct is typed at `C` (the premise).
Zero-case + the two natRec twins included.

Constructor-side as the whole DI-5 family: SR-free (no derivation casing, no cons-index propext
trap); the full SR of these judgments is the CAN-3 follow-up.

## Zero-axiom

Three-arm strictly-positive inductives; the ι-computation theorems are direct constructions; the
shape inversions are free-index `cases` with `rfl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/- The eliminator cells are the shipped ones: `natElimCell` (NatElimComputingCanonicity) and
`natRecCell` (RecursorHostFold) — both `mkGen` over the 3-child `[0, 0, 0]` spine. -/

/-- The step-function type `Nat → C → C` — the curried non-dependent double arrow the successor
branch of a Nat eliminator inhabits (both codomains weakened past their binders). -/
def natStepFunctionType {scope : Nat} (resultType : RawTerm scope) : RawTerm scope :=
  piTyCodeCell natTypeCell
    (RawTerm.weaken (piTyCodeCell resultType (RawTerm.weaken resultType)))

/-- **The recursive Nat eliminator judgment.**  A standalone layer typing the non-dependent
`natElim` AND the two mixed-engine application shapes its successor ι-reduct produces — the arms a
recursive eliminator needs that `piElim` cannot supply (data-engine arguments are not
grown-typable). -/
inductive HasTypeDescNatElim (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | natElimIntro {scope : Nat} (context : TypingContext profile scope)
      (motive : RawTerm (scope + 1)) (scrutinee zeroBranch : RawTerm scope)
      (succBranch : RawTerm (scope + 2)) (resultType : RawTerm scope)
      (scrutineeTyped : HasTypeDescNatIntro profile context scrutinee natTypeCell)
      (zeroBranchTyped : HasTypeDescPi profile context zeroBranch resultType) :
      HasTypeDescNatElim profile context
        (natElimCell motive zeroBranch succBranch scrutinee) resultType

/-- **The recursive Nat recursor judgment** — the `gen_natRec` twin of `HasTypeDescNatElim`
(identical arms over the `natRecCell` Phase-Z eliminator shape). -/
inductive HasTypeDescNatRec (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | natRecIntro {scope : Nat} (context : TypingContext profile scope)
      (motive : RawTerm (scope + 1)) (scrutinee zeroBranch : RawTerm scope)
      (succBranch : RawTerm (scope + 2)) (resultType : RawTerm scope)
      (scrutineeTyped : HasTypeDescNatIntro profile context scrutinee natTypeCell)
      (zeroBranchTyped : HasTypeDescPi profile context zeroBranch resultType) :
      HasTypeDescNatRec profile context
        (natRecCell motive zeroBranch succBranch scrutinee) resultType

/-- **★ Closed forms: a natElim-typed subject is the Phase-Z eliminator cell.**  The single-arm
judgment types exactly the `natElimCell` shape (motive, zeroBranch, succBranch, scrutinee).  Free-index
single-arm `cases`. -/
theorem HasTypeDescNatElim.subjectShape {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescNatElim profile context subject classifier) :
    ∃ (motive : RawTerm (scope + 1)) (zeroBranch scrutinee : RawTerm scope)
      (succBranch : RawTerm (scope + 2)),
        subject = natElimCell motive zeroBranch succBranch scrutinee := by
  cases derivation with
  | natElimIntro motive scrutinee zeroBranch succBranch _resultType _sT _zT =>
      exact ⟨motive, zeroBranch, scrutinee, succBranch, rfl⟩

/-- The `natRec` twin of `HasTypeDescNatElim.subjectShape`. -/
theorem HasTypeDescNatRec.subjectShape {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescNatRec profile context subject classifier) :
    ∃ (motive : RawTerm (scope + 1)) (zeroBranch scrutinee : RawTerm scope)
      (succBranch : RawTerm (scope + 2)),
        subject = natRecCell motive zeroBranch succBranch scrutinee := by
  cases derivation with
  | natRecIntro motive scrutinee zeroBranch succBranch _resultType _sT _zT =>
      exact ⟨motive, zeroBranch, scrutinee, succBranch, rfl⟩

/-- **★ Typed ι-computation (natElim, zero case).**  A typed `natElim` on `natZero` ι-reduces to the
zero branch (`Step.iotaNatElimZero`, branch selection), which is typed at `C` by hypothesis.  Phase-Z
shape: the cell stores the motive + the two-binder succ-branch (both discarded by the zero ι).
Constructor-side: SR-free, propext-free. -/
theorem natElimZeroIotaComputesTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2))
    (resultType : RawTerm scope)
    (zeroBranchTyped : HasTypeDescPi profile context zeroBranch resultType) :
    HasTypeDescNatElim profile context
      (natElimCell motive zeroBranch succBranch natZeroCell) resultType ∧
    Step (natElimCell motive zeroBranch succBranch natZeroCell) zeroBranch ∧
    HasTypeDescPi profile context zeroBranch resultType :=
  ⟨HasTypeDescNatElim.natElimIntro context motive natZeroCell zeroBranch succBranch resultType
      (HasTypeDescNatIntro.natZeroIntro context) zeroBranchTyped,
    Step.iotaNatElimZero, zeroBranchTyped⟩

/-- **★★ Typed RECURSIVE ι-computation (natElim, successor case)** — the CAN-1 headline, now Phase-Z
SUBSTITUTING and CONDITIONAL.  A typed `natElim` on `natSucc(p)` ι-reduces to
`natElimSuccContractum motive zeroBranch succBranch p` (`Step.iotaNatElimSucc` — the recursive call
substituted into the succ-branch's var-0 slot, the predecessor into var-1), and the reduct is typed at
`C` GIVEN `reductTyped` — the substituted reduct's typing supplied as a PREMISE.

CONDITIONAL FORM FLAG: `reductTyped` is the standalone-engine pattern stand-in for the MISSING 2-variable
typed substitution lemma (typing `subst (cons recursiveCall (singleton predecessor)) succBranch` from
the branch + recursive-call typings).  Once that lemma ships (the GTL substitution follow-on seeding this
lane's follow-up task) the premise is discharged internally.  Constructor-side: SR-free, propext-free. -/
theorem natElimSuccIotaComputesTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (predecessor zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) (resultType : RawTerm scope)
    (predecessorTyped : HasTypeDescNatIntro profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeDescPi profile context zeroBranch resultType)
    (reductTyped : HasTypeDescNatElim profile context
      (natElimSuccContractum motive zeroBranch succBranch predecessor) resultType) :
    HasTypeDescNatElim profile context
      (natElimCell motive zeroBranch succBranch (natSuccCell predecessor)) resultType ∧
    Step (natElimCell motive zeroBranch succBranch (natSuccCell predecessor))
      (natElimSuccContractum motive zeroBranch succBranch predecessor) ∧
    HasTypeDescNatElim profile context
      (natElimSuccContractum motive zeroBranch succBranch predecessor) resultType :=
  ⟨HasTypeDescNatElim.natElimIntro context motive (natSuccCell predecessor) zeroBranch succBranch
      resultType (HasTypeDescNatIntro.natSuccIntro context predecessor predecessorTyped)
      zeroBranchTyped,
    Step.iotaNatElimSucc, reductTyped⟩

/-- **★ Typed ι-computation (natRec, zero case)** — the recursor twin of
`natElimZeroIotaComputesTyped` (`Step.iotaNatRecZero`). -/
theorem natRecZeroIotaComputesTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2))
    (resultType : RawTerm scope)
    (zeroBranchTyped : HasTypeDescPi profile context zeroBranch resultType) :
    HasTypeDescNatRec profile context
      (natRecCell motive zeroBranch succBranch natZeroCell) resultType ∧
    Step (natRecCell motive zeroBranch succBranch natZeroCell) zeroBranch ∧
    HasTypeDescPi profile context zeroBranch resultType :=
  ⟨HasTypeDescNatRec.natRecIntro context motive natZeroCell zeroBranch succBranch resultType
      (HasTypeDescNatIntro.natZeroIntro context) zeroBranchTyped,
    Step.iotaNatRecZero, zeroBranchTyped⟩

/-- **★★ Typed RECURSIVE ι-computation (natRec, successor case)** — the recursor twin of
`natElimSuccIotaComputesTyped` (`Step.iotaNatRecSucc`), Phase-Z SUBSTITUTING and CONDITIONAL on the
reduct typing (same missing 2-variable typed substitution lemma). -/
theorem natRecSuccIotaComputesTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (predecessor zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) (resultType : RawTerm scope)
    (predecessorTyped : HasTypeDescNatIntro profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeDescPi profile context zeroBranch resultType)
    (reductTyped : HasTypeDescNatRec profile context
      (natRecSuccContractum motive zeroBranch succBranch predecessor) resultType) :
    HasTypeDescNatRec profile context
      (natRecCell motive zeroBranch succBranch (natSuccCell predecessor)) resultType ∧
    Step (natRecCell motive zeroBranch succBranch (natSuccCell predecessor))
      (natRecSuccContractum motive zeroBranch succBranch predecessor) ∧
    HasTypeDescNatRec profile context
      (natRecSuccContractum motive zeroBranch succBranch predecessor) resultType :=
  ⟨HasTypeDescNatRec.natRecIntro context motive (natSuccCell predecessor) zeroBranch succBranch
      resultType (HasTypeDescNatIntro.natSuccIntro context predecessor predecessorTyped)
      zeroBranchTyped,
    Step.iotaNatRecSucc, reductTyped⟩

end FX1Poly.Typed
