import FX1Poly.Typed.HasTypeDescNatIntro
import FX1Poly.Typed.NatElimComputingCanonicity
import FX1Poly.Typed.RecursorHostFold

/-! # FX1Poly/Typed/HasTypeDescNatElim — the RECURSIVE Nat eliminator judgments + typed recursive
    ι-computation (CAN-1 / DI-5f: the recursive-eliminator wall the DI-5 track deferred).

DI-5a..5e typed the non-recursive eliminators (boolElim / eitherMatch / optionMatch / Σ-projections /
idJ).  `natElim` / `natRec` are the RECURSIVE eliminators: the successor ι-reduct is the 2-arg
app-chain `app (app succBranch predecessor) (natElim predecessor zeroBranch succBranch)` — the
RECURSIVE CALL appears as a syntactic sub-term (`Step.iotaNatElimSucc`, SHAPE 4).

## The engine-separation wall, and its resolution

The non-recursive eliminators typed their ι-reducts by `HasTypeDescPi.piElim` (the eitherMatch
pattern): the handler is grown-typed at an arrow, the payload is grown-typed at the domain, done.
That CANNOT work here: the inner application's argument is the PREDECESSOR, a nat value typed by the
DATA-INTRO engine (`HasTypeDescNatIntro`) — and data constructors are deliberately NOT grown-typable
(the cascade-free standalone-engine architecture).  `piElim` demands a grown-typed argument, so the
reduct `app (app s p) (natElim p z s)` is NOT grown-typable for an actual numeral `p`.  This is the
recursive-eliminator engine-separation finding (#1078) hitting the elimination layer.

Resolution: the eliminator judgment itself carries the reduct shapes as arms.  `HasTypeDescNatElim`
has THREE arms:

  * `natElimIntro` — the eliminator cell `natElim(s, z, sb) : C` from a data-engine scrutinee
    `s : Nat`, a grown-typed base `z : C`, and a grown-typed step function
    `sb : Nat → C → C` (`natStepFunctionType C`, the curried non-dependent double arrow).
  * `mixedStepApplication` — the MIXED-ENGINE application `app sb p : C → C` from the grown-typed
    step function and a DATA-ENGINE predecessor.  This is the cross-engine elimination rule `piElim`
    cannot express; baking the non-dependent output type directly into the arm also removes the
    `subst0`-collapse step the eitherMatch route needed.
  * `recursiveResultApplication` — the outer application `app (app sb p) r : C` where BOTH parts are
    typed by THIS judgment (the partial application at `C → C`, the recursive call at `C`) — the
    strictly-positive recursive arm mirroring the recursion in the reduct itself.

`HasTypeDescNatRec` is the structurally identical twin for `gen_natRec` (the v2 substrate gives the
two generators identical arity/shifts/iotas; dependent-vs-non-dependent is a profile-layer
distinction).

## The headline: typed RECURSIVE ι-computation

`natElimSuccIotaComputesTyped` (★): for a data-typed predecessor and typed branches, the eliminator
`natElim(succ p, z, sb)` is typed at `C`, ι-steps to `app (app sb p) (natElim p z sb)`
(`Step.iotaNatElimSucc`), and the reduct is typed at `C` — assembled as
`recursiveResultApplication (mixedStepApplication …) (natElimIntro …)`, where the inner
`natElimIntro` types the RECURSIVE CALL at the predecessor.  The recursion in the typing mirrors the
recursion in the computation.  Zero-case + the two natRec twins included.

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
      (scrutinee zeroBranch succBranch resultType : RawTerm scope)
      (scrutineeTyped : HasTypeDescNatIntro profile context scrutinee natTypeCell)
      (zeroBranchTyped : HasTypeDescPi profile context zeroBranch resultType)
      (succBranchTyped :
        HasTypeDescPi profile context succBranch (natStepFunctionType resultType)) :
      HasTypeDescNatElim profile context
        (natElimCell scrutinee zeroBranch succBranch) resultType
  | mixedStepApplication {scope : Nat} (context : TypingContext profile scope)
      (succBranch predecessor resultType : RawTerm scope)
      (succBranchTyped :
        HasTypeDescPi profile context succBranch (natStepFunctionType resultType))
      (predecessorTyped : HasTypeDescNatIntro profile context predecessor natTypeCell) :
      HasTypeDescNatElim profile context (appCell succBranch predecessor)
        (piTyCodeCell resultType (RawTerm.weaken resultType))
  | recursiveResultApplication {scope : Nat} (context : TypingContext profile scope)
      (stepFunction recursiveCall resultType : RawTerm scope)
      (stepFunctionTyped : HasTypeDescNatElim profile context stepFunction
        (piTyCodeCell resultType (RawTerm.weaken resultType)))
      (recursiveCallTyped : HasTypeDescNatElim profile context recursiveCall resultType) :
      HasTypeDescNatElim profile context (appCell stepFunction recursiveCall) resultType

/-- **The recursive Nat recursor judgment** — the `gen_natRec` twin of `HasTypeDescNatElim`
(identical arms over the `natRecCell` eliminator shape). -/
inductive HasTypeDescNatRec (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | natRecIntro {scope : Nat} (context : TypingContext profile scope)
      (scrutinee zeroBranch succBranch resultType : RawTerm scope)
      (scrutineeTyped : HasTypeDescNatIntro profile context scrutinee natTypeCell)
      (zeroBranchTyped : HasTypeDescPi profile context zeroBranch resultType)
      (succBranchTyped :
        HasTypeDescPi profile context succBranch (natStepFunctionType resultType)) :
      HasTypeDescNatRec profile context
        (natRecCell scrutinee zeroBranch succBranch) resultType
  | mixedStepApplication {scope : Nat} (context : TypingContext profile scope)
      (succBranch predecessor resultType : RawTerm scope)
      (succBranchTyped :
        HasTypeDescPi profile context succBranch (natStepFunctionType resultType))
      (predecessorTyped : HasTypeDescNatIntro profile context predecessor natTypeCell) :
      HasTypeDescNatRec profile context (appCell succBranch predecessor)
        (piTyCodeCell resultType (RawTerm.weaken resultType))
  | recursiveResultApplication {scope : Nat} (context : TypingContext profile scope)
      (stepFunction recursiveCall resultType : RawTerm scope)
      (stepFunctionTyped : HasTypeDescNatRec profile context stepFunction
        (piTyCodeCell resultType (RawTerm.weaken resultType)))
      (recursiveCallTyped : HasTypeDescNatRec profile context recursiveCall resultType) :
      HasTypeDescNatRec profile context (appCell stepFunction recursiveCall) resultType

/-- **★ Closed forms: a natElim-typed subject is the eliminator cell or an application.**  The
recursive eliminator judgment types THREE shapes (unlike the single-shape non-recursive DI-5
judgments), so the honest closed-forms statement is the disjunction.  Free-index three-arm
`cases`. -/
theorem HasTypeDescNatElim.subjectShape {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescNatElim profile context subject classifier) :
    (∃ scrutinee zeroBranch succBranch : RawTerm scope,
        subject = natElimCell scrutinee zeroBranch succBranch) ∨
      (∃ functionPart argumentPart : RawTerm scope,
        subject = appCell functionPart argumentPart) := by
  cases derivation with
  | natElimIntro scrutinee zeroBranch succBranch _resultType _sT _zT _bT =>
      exact Or.inl ⟨scrutinee, zeroBranch, succBranch, rfl⟩
  | mixedStepApplication succBranch predecessor _resultType _sT _pT =>
      exact Or.inr ⟨succBranch, predecessor, rfl⟩
  | recursiveResultApplication stepFunction recursiveCall _resultType _fT _rT =>
      exact Or.inr ⟨stepFunction, recursiveCall, rfl⟩

/-- The `natRec` twin of `HasTypeDescNatElim.subjectShape`. -/
theorem HasTypeDescNatRec.subjectShape {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescNatRec profile context subject classifier) :
    (∃ scrutinee zeroBranch succBranch : RawTerm scope,
        subject = natRecCell scrutinee zeroBranch succBranch) ∨
      (∃ functionPart argumentPart : RawTerm scope,
        subject = appCell functionPart argumentPart) := by
  cases derivation with
  | natRecIntro scrutinee zeroBranch succBranch _resultType _sT _zT _bT =>
      exact Or.inl ⟨scrutinee, zeroBranch, succBranch, rfl⟩
  | mixedStepApplication succBranch predecessor _resultType _sT _pT =>
      exact Or.inr ⟨succBranch, predecessor, rfl⟩
  | recursiveResultApplication stepFunction recursiveCall _resultType _fT _rT =>
      exact Or.inr ⟨stepFunction, recursiveCall, rfl⟩

/-- **★ Typed ι-computation (natElim, zero case).**  A typed `natElim` on `natZero` ι-reduces to the
zero branch (`Step.iotaNatElimZero`, branch selection), which is typed at `C` by hypothesis.
Constructor-side: SR-free, propext-free. -/
theorem natElimZeroIotaComputesTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (zeroBranch succBranch resultType : RawTerm scope)
    (zeroBranchTyped : HasTypeDescPi profile context zeroBranch resultType)
    (succBranchTyped :
      HasTypeDescPi profile context succBranch (natStepFunctionType resultType)) :
    HasTypeDescNatElim profile context
      (natElimCell natZeroCell zeroBranch succBranch) resultType ∧
    Step (natElimCell natZeroCell zeroBranch succBranch) zeroBranch ∧
    HasTypeDescPi profile context zeroBranch resultType :=
  ⟨HasTypeDescNatElim.natElimIntro context natZeroCell zeroBranch succBranch resultType
      (HasTypeDescNatIntro.natZeroIntro context) zeroBranchTyped succBranchTyped,
    Step.iotaNatElimZero, zeroBranchTyped⟩

/-- **★★ Typed RECURSIVE ι-computation (natElim, successor case)** — the CAN-1 headline.  A typed
`natElim` on `natSucc(p)` ι-reduces to `app (app succBranch p) (natElim p zeroBranch succBranch)`
(`Step.iotaNatElimSucc` — the recursive call as a syntactic sub-term), and the reduct is typed at
`C`: the inner mixed-engine application by `mixedStepApplication` (grown step function, DATA-engine
predecessor), the outer by `recursiveResultApplication` with the RECURSIVE CALL typed by
`natElimIntro` at the predecessor.  The recursion in the typing mirrors the recursion in the
computation.  Constructor-side: SR-free, propext-free. -/
theorem natElimSuccIotaComputesTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (predecessor zeroBranch succBranch resultType : RawTerm scope)
    (predecessorTyped : HasTypeDescNatIntro profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeDescPi profile context zeroBranch resultType)
    (succBranchTyped :
      HasTypeDescPi profile context succBranch (natStepFunctionType resultType)) :
    HasTypeDescNatElim profile context
      (natElimCell (natSuccCell predecessor) zeroBranch succBranch) resultType ∧
    Step (natElimCell (natSuccCell predecessor) zeroBranch succBranch)
      (appCell (appCell succBranch predecessor)
        (natElimCell predecessor zeroBranch succBranch)) ∧
    HasTypeDescNatElim profile context
      (appCell (appCell succBranch predecessor)
        (natElimCell predecessor zeroBranch succBranch)) resultType :=
  ⟨HasTypeDescNatElim.natElimIntro context (natSuccCell predecessor) zeroBranch succBranch
      resultType (HasTypeDescNatIntro.natSuccIntro context predecessor predecessorTyped)
      zeroBranchTyped succBranchTyped,
    Step.iotaNatElimSucc,
    HasTypeDescNatElim.recursiveResultApplication context
      (appCell succBranch predecessor) (natElimCell predecessor zeroBranch succBranch) resultType
      (HasTypeDescNatElim.mixedStepApplication context succBranch predecessor resultType
        succBranchTyped predecessorTyped)
      (HasTypeDescNatElim.natElimIntro context predecessor zeroBranch succBranch resultType
        predecessorTyped zeroBranchTyped succBranchTyped)⟩

/-- **★ Typed ι-computation (natRec, zero case)** — the recursor twin of
`natElimZeroIotaComputesTyped` (`Step.iotaNatRecZero`). -/
theorem natRecZeroIotaComputesTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (zeroBranch succBranch resultType : RawTerm scope)
    (zeroBranchTyped : HasTypeDescPi profile context zeroBranch resultType)
    (succBranchTyped :
      HasTypeDescPi profile context succBranch (natStepFunctionType resultType)) :
    HasTypeDescNatRec profile context
      (natRecCell natZeroCell zeroBranch succBranch) resultType ∧
    Step (natRecCell natZeroCell zeroBranch succBranch) zeroBranch ∧
    HasTypeDescPi profile context zeroBranch resultType :=
  ⟨HasTypeDescNatRec.natRecIntro context natZeroCell zeroBranch succBranch resultType
      (HasTypeDescNatIntro.natZeroIntro context) zeroBranchTyped succBranchTyped,
    Step.iotaNatRecZero, zeroBranchTyped⟩

/-- **★★ Typed RECURSIVE ι-computation (natRec, successor case)** — the recursor twin of
`natElimSuccIotaComputesTyped` (`Step.iotaNatRecSucc`). -/
theorem natRecSuccIotaComputesTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (predecessor zeroBranch succBranch resultType : RawTerm scope)
    (predecessorTyped : HasTypeDescNatIntro profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeDescPi profile context zeroBranch resultType)
    (succBranchTyped :
      HasTypeDescPi profile context succBranch (natStepFunctionType resultType)) :
    HasTypeDescNatRec profile context
      (natRecCell (natSuccCell predecessor) zeroBranch succBranch) resultType ∧
    Step (natRecCell (natSuccCell predecessor) zeroBranch succBranch)
      (appCell (appCell succBranch predecessor)
        (natRecCell predecessor zeroBranch succBranch)) ∧
    HasTypeDescNatRec profile context
      (appCell (appCell succBranch predecessor)
        (natRecCell predecessor zeroBranch succBranch)) resultType :=
  ⟨HasTypeDescNatRec.natRecIntro context (natSuccCell predecessor) zeroBranch succBranch
      resultType (HasTypeDescNatIntro.natSuccIntro context predecessor predecessorTyped)
      zeroBranchTyped succBranchTyped,
    Step.iotaNatRecSucc,
    HasTypeDescNatRec.recursiveResultApplication context
      (appCell succBranch predecessor) (natRecCell predecessor zeroBranch succBranch) resultType
      (HasTypeDescNatRec.mixedStepApplication context succBranch predecessor resultType
        succBranchTyped predecessorTyped)
      (HasTypeDescNatRec.natRecIntro context predecessor zeroBranch succBranch resultType
        predecessorTyped zeroBranchTyped succBranchTyped)⟩

end FX1Poly.Typed
