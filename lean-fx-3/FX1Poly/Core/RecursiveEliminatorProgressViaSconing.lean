import FX1Poly.Core.RecursorClosedMembership

/-! # FX1Poly/Core/RecursiveEliminatorProgressViaSconing
    — operational PROGRESS for the RECURSIVE data eliminators via the sconing fundamental

`DataEliminatorProgressViaSconing` covers the NON-recursive data eliminators (`boolElim`, `fst`/`snd`,
`optionMatch`/`eitherMatch`, `idJ`/`idStrictRec`) and EXCLUDES the recursive ones
(`natElim`/`natRec`/`listElim`) on the grounds that their `succ`/`cons` ι re-invokes the eliminator on the
predecessor/tail and so "needs Tait".  That Tait piece ships fundamental-free in `RecursorClosedMembership`
(`natElimClosedIsMember` / `natRecClosedIsMember` / `listElimClosedIsMember`, the scrutinee-reduction
halves) which lands a closed recursor on a MEMBER scrutinee in the result candidate, fed the honest
recursor-SN IH-premise the eventual full WF recursion discharges.  This file lifts the exclusion: it threads the
sconing FUNDAMENTAL (closed well-typed Nat / List ⟹ data-candidate member — the shared fundamental obligation,
parameterised over an abstract `isWellTyped`, exactly as the non-recursive progress file does) into the SCRUTINEE
position of those membership theorems, and reads off the operational payoff via `closedReducesToValue`:

  * `natElimProgressViaSconing` / `natRecProgressViaSconing` — a `natElim` / `natRec` whose scrutinee is
    well-typed (Nat) and whose branches are reducible (the Tait branch interface) REDUCES TO A VALUE — it is
    never stuck.  The canonicity payoff via the sconing leg: the recursor cell normalises to a
    `isValue` result.
  * `listElimProgressViaSconing` — the List twin: a `listElim` on a well-typed (List) scrutinee with
    reducible branches reduces to a value.

The branch behaviours stay explicit Tait-interface hypotheses — they cannot come from the SAME data fundamental
because the branches inhabit DIFFERENT motive types (`zeroBranch : Motive[zero]`, `succBranch : Π …`), so a
single Nat / List `isWellTyped` predicate does not classify them.  Phase-Z note: for `natElim`/`natRec` the
succ-iota SUBSTITUTES, so the branch interface is the SUBSTITUTED-reduct membership/termination pair
(`substitutedReductMember` / `substitutedReductTerminates`) rather than the old app-chain
`succBranchApplication` / `succContractumTerminates`; for `listElim` the cons-iota is still an app-chain, so its
interface keeps the app-chain `consBranchApplication` / `consContractumTerminates`.  This mirrors
`RecursorClosedMembership` exactly; the ONLY move this file makes is replacing its `scrutineeMember` (the
scrutinee is already a member) with `fundamental + scrutineeTyped` (the scrutinee is well-typed, and the
fundamental makes it a member) — the same fundamental-obligation packaging the non-recursive progress file uses,
now closing the recursive corner of the eliminator-progress track.

## Zero-axiom verification

Each theorem is `(<eliminator>ClosedIsMember (fundamental scrutinee scrutineeTyped) <branch hyps …>)`
post-composed with `.closedReducesToValue`.  The local cell abbreviations are definitionally equal to the
(private) ones in `RecursorClosedMembership`, so the compositions typecheck.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- The `natElim` cell — `gen_natElim` in the Phase-Z motive shape (arity 4, `binderShifts =
[1, 0, 2, 0]`), author order `(motive, scrutinee, zeroBranch, succBranch)`, emitting the spine
`(motive, zeroBranch, succBranch, scrutinee)` with the succ-branch under TWO binders and the scrutinee LAST —
definitionally the private `natElimCell` of `RecursorClosedMembership`. -/
private abbrev natElimCellOn (motive : RawTerm 1) (scrutinee zeroBranch : RawTerm 0)
    (succBranch : RawTerm 2) : RawTerm 0 :=
  .mkGen .gen_natElim ()
    (.childCons motive
      (.childCons zeroBranch
        (.childCons succBranch
          (.childCons scrutinee .childNil))))

/-- The `natRec` cell — same Phase-Z motive shape as `natElimCellOn` with `gen_natRec` — definitionally the
private `natRecCell` of `RecursorClosedMembership`. -/
private abbrev natRecCellOn (motive : RawTerm 1) (scrutinee zeroBranch : RawTerm 0)
    (succBranch : RawTerm 2) : RawTerm 0 :=
  .mkGen .gen_natRec ()
    (.childCons motive
      (.childCons zeroBranch
        (.childCons succBranch
          (.childCons scrutinee .childNil))))

/-- The `natElim` succ-iota SUBSTITUTED reduct — definitionally the private `natElimSuccContractumClosed` of
`RecursorClosedMembership` (the Phase-Z succ-iota substitutes the recursive call + predecessor into the
two-binder succ-branch). -/
private abbrev natElimSuccContractumOn (motive : RawTerm 1) (succBranch : RawTerm 2)
    (predecessor zeroBranch : RawTerm 0) : RawTerm 0 :=
  RawTerm.subst
    (RawTermSubst.cons
      (.mkGen .gen_natElim ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch (.childCons predecessor .childNil)))))
      (RawTermSubst.singleton predecessor))
    succBranch

/-- The `natRec` succ-iota SUBSTITUTED reduct — the `gen_natRec` mirror of `natElimSuccContractumOn`. -/
private abbrev natRecSuccContractumOn (motive : RawTerm 1) (succBranch : RawTerm 2)
    (predecessor zeroBranch : RawTerm 0) : RawTerm 0 :=
  RawTerm.subst
    (RawTermSubst.cons
      (.mkGen .gen_natRec ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch (.childCons predecessor .childNil)))))
      (RawTermSubst.singleton predecessor))
    succBranch

/-- The `listElim` cell — `gen_listElim` in the Phase-Z motive shape (arity 4, `binderShifts =
[1, 0, 0, 0]`), author order `(motive, scrutinee, nilBranch, consBranch)`, emitting the spine
`(motive, nilBranch, consBranch, scrutinee)` — definitionally the private `listElimCell` of
`RecursorClosedMembership`. -/
private abbrev listElimCellOn (motive : RawTerm 1) (scrutinee nilBranch consBranch : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_listElim ()
    (.childCons motive
      (.childCons nilBranch
        (.childCons consBranch
          (.childCons scrutinee .childNil))))

/-- **`natElim` progress on a well-typed scrutinee.**  Given the sconing fundamental (closed well-typed
Nat ⟹ Nat-candidate member) and a well-typed scrutinee, plus the Phase-Z motive shape (a stored motive head
child, so a motive-SN hypothesis is threaded) and the SUBSTITUTING Tait branch interface (zero branch a member,
succ branch SN, the SUBSTITUTED succ reduct a member + SN — the substitution-shaped analogues of the old
app-chain `succBranchApplication`/`succContractumTerminates`), the `natElim` cell reduces to an `isValue` value
— it is never stuck.  Composition of the fundamental with the migrated `natElimClosedIsMember` read off via
`closedReducesToValue`. -/
theorem natElimProgressViaSconing {isWellTyped isValue : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0, isWellTyped term → CanonicalFormsPredicate IsNatValue term)
    {motive : RawTerm 1} {scrutinee zeroBranch : RawTerm 0} {succBranch : RawTerm 2}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeTyped : isWellTyped scrutinee)
    (zeroBranchMember : CanonicalFormsPredicate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (substitutedReductMember : ∀ {predecessor : RawTerm 0},
        IsNatValue predecessor →
        CanonicalFormsPredicate isValue
          (natElimSuccContractumOn motive succBranch predecessor zeroBranch))
    (substitutedReductTerminates :
        ∀ (currentMotive : RawTerm 1) (currentSucc : RawTerm 2)
          (predecessor currentZero : RawTerm 0), IsStronglyNormalizing predecessor →
          IsStronglyNormalizing
            (natElimSuccContractumOn currentMotive currentSucc predecessor currentZero)) :
    ∃ value : RawTerm 0,
      StepStar (natElimCellOn motive scrutinee zeroBranch succBranch) value ∧ isValue value :=
  (natElimClosedIsMember motiveStronglyNormalizing (fundamental scrutinee scrutineeTyped)
    zeroBranchMember succBranchTerminates substitutedReductMember
    substitutedReductTerminates).closedReducesToValue

/-- **`natRec` progress on a well-typed scrutinee.**  The dependent-recursor twin of
`natElimProgressViaSconing`: a `natRec` on a well-typed (Nat) scrutinee with the Phase-Z motive shape and the
SUBSTITUTING branch interface reduces to an `isValue` value.  Composition of the fundamental with the migrated
`natRecClosedIsMember` read off via `closedReducesToValue`. -/
theorem natRecProgressViaSconing {isWellTyped isValue : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0, isWellTyped term → CanonicalFormsPredicate IsNatValue term)
    {motive : RawTerm 1} {scrutinee zeroBranch : RawTerm 0} {succBranch : RawTerm 2}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeTyped : isWellTyped scrutinee)
    (zeroBranchMember : CanonicalFormsPredicate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (substitutedReductMember : ∀ {predecessor : RawTerm 0},
        IsNatValue predecessor →
        CanonicalFormsPredicate isValue
          (natRecSuccContractumOn motive succBranch predecessor zeroBranch))
    (substitutedReductTerminates :
        ∀ (currentMotive : RawTerm 1) (currentSucc : RawTerm 2)
          (predecessor currentZero : RawTerm 0), IsStronglyNormalizing predecessor →
          IsStronglyNormalizing
            (natRecSuccContractumOn currentMotive currentSucc predecessor currentZero)) :
    ∃ value : RawTerm 0,
      StepStar (natRecCellOn motive scrutinee zeroBranch succBranch) value ∧ isValue value :=
  (natRecClosedIsMember motiveStronglyNormalizing (fundamental scrutinee scrutineeTyped)
    zeroBranchMember succBranchTerminates substitutedReductMember
    substitutedReductTerminates).closedReducesToValue

/-- **`listElim` progress on a well-typed scrutinee.**  Given the sconing fundamental (closed well-typed
List ⟹ List-candidate member), a well-typed scrutinee, and the Tait branch interface (nil branch a member, cons
branch SN, cons-branch application landing in the candidate with the head a step-NF and the tail an `IsListValue`,
cons-contractum SN), the `listElim` cell reduces to an `isValue` value — never stuck.  Phase-Z motive shape:
the cell carries a stored motive head child, so a motive-SN hypothesis (`motiveStronglyNormalizing`) is threaded
into `listElimClosedIsMember` as well.  The List twin of `natElimProgressViaSconing`, via
`listElimClosedIsMember`. -/
theorem listElimProgressViaSconing {isWellTyped isValue : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0, isWellTyped term → CanonicalFormsPredicate IsListValue term)
    {motive : RawTerm 1} {scrutinee nilBranch consBranch : RawTerm 0}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeTyped : isWellTyped scrutinee)
    (nilBranchMember : CanonicalFormsPredicate isValue nilBranch)
    (consBranchTerminates : IsStronglyNormalizing consBranch)
    (consBranchApplication : ∀ {head tail result : RawTerm 0},
        RawTerm.isStepNormalForm head → IsListValue tail → CanonicalFormsPredicate isValue result →
        CanonicalFormsPredicate isValue
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
                  (.childCons tail .childNil)))
              (.childCons result .childNil))))
    (consContractumTerminates : ∀ head tail : RawTerm 0,
        IsStronglyNormalizing head → IsStronglyNormalizing tail →
        IsStronglyNormalizing
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
                  (.childCons tail .childNil)))
              (.childCons (listElimCellOn motive tail nilBranch consBranch) .childNil)))) :
    ∃ value : RawTerm 0,
      StepStar (listElimCellOn motive scrutinee nilBranch consBranch) value ∧ isValue value :=
  (listElimClosedIsMember motiveStronglyNormalizing (fundamental scrutinee scrutineeTyped) nilBranchMember
    consBranchTerminates consBranchApplication consContractumTerminates).closedReducesToValue

end FX1Poly.Core
