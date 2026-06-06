import FX1Poly.Core.BoolCanonicalFormsCandidate
import FX1Poly.Core.WeakHeadStepCommute

/-! # FX1Poly/Core/BoolElimCanonicalComputation
    — closed `boolElim` on a canonical scrutinee COMPUTES to a branch (the elimination analog of closed-bool canonicity)

`BoolCanonicalFormsCandidate.lean` ships data canonicity: a closed member of the bool candidate reduces to
`boolTrue` or `boolFalse` (`boolClosedReducesToTrueOrFalse`).  This file pushes that one step into the
ELIMINATOR: a closed `boolElim` whose scrutinee is a canonical bool member reduces to one of its branches.  The
elimination analog of closed-bool canonicity, and a fundamental-free step toward `boolElim` reducibility.

* `StepStar.boolElimScrutinee` — the scrutinee-position chain congruence: a `StepStar` in the scrutinee lifts to
  the whole `boolElim` cell.  Built from the generic one-hole-context chain lifter `StepStar.congAt` with the
  uniform `Step.cong … (StepChildren.here …)` at the scrutinee child (the head of the 3-child spine).
* `boolElimCanonicalScrutineeReducesToBranch` — the headline: a closed `boolElim` on a canonical scrutinee
  `StepStar`-reduces to its then-branch OR its else-branch.  The scrutinee reduces to `boolTrue`/`boolFalse`
  (data canonicity), the congruence carries that under the `boolElim`, and the matching ι rule
  (`Step.iotaBoolTrue` / `Step.iotaBoolFalse`) selects the branch.

NOTE: `gen_boolElim` is the NON-dependent 3-child form (scrutinee, then, else) — no motive child.  The cell
shape here matches that 3-child spine.

## Zero-axiom verification

`StepStar.congAt` (chain induction), `boolClosedReducesToTrueOrFalse` (data canonicity via the candidate),
`Step.cong` / `StepChildren.here` (the scrutinee congruence step), and the `Step.iotaBoolTrue` /
`Step.iotaBoolFalse` ι constructors, chained by `StepStar.transLast`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- The non-dependent `boolElim` cell over its three children (scrutinee, then, else) — the current Z₀ shape
(no motive child yet). -/
private abbrev boolElimCellOn {scope : Nat} (scrutinee thenBranch elseBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_boolElim ()
    (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil)))

/-- **Scrutinee-position chain congruence for `boolElim`.**  A reduction chain in the scrutinee lifts to the
whole `boolElim` cell (branches fixed).  Instantiates the generic one-hole-context chain lifter
`StepStar.congAt` with the `boolElim` wrapper around its scrutinee and the uniform `Step.cong … (here …)` at the
scrutinee child (the head of the 3-child spine). -/
theorem StepStar.boolElimScrutinee {scope : Nat}
    {scrutinee scrutineeReduct thenBranch elseBranch : RawTerm scope}
    (scrutineeChain : StepStar scrutinee scrutineeReduct) :
    StepStar (boolElimCellOn scrutinee thenBranch elseBranch)
      (boolElimCellOn scrutineeReduct thenBranch elseBranch) :=
  StepStar.congAt
    (fun hole => boolElimCellOn hole thenBranch elseBranch)
    (fun stepInScrutinee => Step.cong .gen_boolElim () (StepChildren.here _ stepInScrutinee))
    scrutineeChain

/-- **Closed `boolElim` on a canonical scrutinee computes to a branch.**  The elimination analog of closed-bool
canonicity: a closed `boolElim` whose scrutinee is a member of the bool candidate `StepStar`-reduces to
its then-branch or its else-branch.  The scrutinee reduces to `boolTrue`/`boolFalse`
(`boolClosedReducesToTrueOrFalse`), `StepStar.boolElimScrutinee` carries that reduction under the `boolElim`,
and the matching ι rule fires to select the branch.  Fundamental-free — it uses only data canonicity plus the
scrutinee congruence and the ι rules, no fundamental theorem. -/
theorem boolElimCanonicalScrutineeReducesToBranch {scrutinee thenBranch elseBranch : RawTerm 0}
    (scrutineeMember : CanonicalFormsPredicate boolIsValue scrutinee) :
    StepStar (boolElimCellOn scrutinee thenBranch elseBranch) thenBranch ∨
      StepStar (boolElimCellOn scrutinee thenBranch elseBranch) elseBranch := by
  obtain ⟨value, scrutineeReducesToValue, valueIsTrueOrFalse⟩ :=
    boolClosedReducesToTrueOrFalse scrutineeMember
  cases valueIsTrueOrFalse with
  | inl valueIsTrue =>
      subst valueIsTrue
      exact Or.inl
        (StepStar.transLast (StepStar.boolElimScrutinee scrutineeReducesToValue) Step.iotaBoolTrue)
  | inr valueIsFalse =>
      subst valueIsFalse
      exact Or.inr
        (StepStar.transLast (StepStar.boolElimScrutinee scrutineeReducesToValue) Step.iotaBoolFalse)

end FX1Poly.Core
