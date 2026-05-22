import LeanFX2.Term

/-! # Foundation/TermUaToEquivExcludesOeqRefl — vacuity at
`RawTerm.uaToEquiv (RawTerm.oeqRefl _)` typed exclusion

`Term.uaToEquiv` requires its `proof` field at type
`Ty.id (Ty.universe innerLevel _) leftTyRaw rightTyRaw`, while
`Term.oeqRefl` produces a value at type
`Ty.oeq carrier rawWitness rawWitness`.  The Ty constructors
`Ty.id` and `Ty.oeq` are distinct, so no typed `Term` can have raw
projection `RawTerm.uaToEquiv (RawTerm.oeqRefl _)`:

* The only Term ctor whose raw is `RawTerm.uaToEquiv _` is
  `Term.uaToEquiv`, whose proof field must be a Term at `Ty.id ...`.
* The only Term ctor whose raw is `RawTerm.oeqRefl _` is
  `Term.oeqRefl`, which produces `Ty.oeq ...`.

The mismatch refutes via indexed-inductive ctor injectivity.

## Why this matters

`RawStep.par.uaReflEquivApply` and `RawStep.par.uaReflEquivApplyDeep`
(see `Reduction/RawPar/Inductive.lean:1367,1392`) fire when an
`equivApply`'s equiv argument syntactically matches
`uaToEquiv (oeqRefl _)` (shallow case) or develops to it under
parallel reduction (deep case).  Both raw rules are documented
`raw-only` (`isDocumentedRawOnlyParity` Section H) because the typed
parity gate blocks them structurally via the `Ty.id` vs `Ty.oeq`
mismatch above.

Future `RawStep.par.lift_full_equivApply` work (Family E close-out
ticket #2059, unblock-A.leaf.equivApply #2013) needs to discharge
the β arms of `RawStep.par.equivApply_inv` (`uaReflEquivApply` /
`uaReflEquivApplyDeep`).  Both arms reduce a typed
`Term.equivApply equivTerm argumentTerm` whose `equivTerm` would
need raw projection `RawTerm.uaToEquiv (RawTerm.oeqRefl _)`; the
vacuity witness shipped here forces False at exactly that shape.

## Cascade role

* Consumed by future `RawStep.par.lift_full_equivApply` (#2059).
* Same recipe as `TermPathLamExcludes.lean` (#2066 hcomp closed-
  carrier shipped via `Term.pathLam_excludes_closedTy`, commit
  92fa8c42).
* Eligible reuse: any future leaf that needs to refute a typed
  Term whose raw shape forces incompatible Ty constructors at
  nested binder positions.

## Audit

Verified zero-axiom via `#print axioms`.

## Pitfalls + mitigations

* P-1 (Term.var's `varType context position` opaque to dep-elim):
  Direct `cases proofTerm` on a Term at fixed `Ty.id (...) _ _`
  fails on Term.var case because Lean cannot statically refute
  `Ty.id ... = varType context position`.  Mitigation: helper
  `Term.oeqRefl_raw_inv` keeps the target type free during the
  inner cases, then returns an equation we destruct via Ty ctor
  injectivity at the call site.
* P-13: N/A — `False` is the conclusion; no Decidable needed.
-/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat}
variable {context : Ctx mode level scope}

/-- **Universal inversion at `RawTerm.oeqRefl _`.**  Given a typed
Term whose raw is `RawTerm.oeqRefl witnessRawSource`, decompose it
as the unique `Term.oeqRefl` ctor.  The output equation
`targetType = Ty.oeq carrier witnessRawSource witnessRawSource`
pins the type at exactly the `Ty.oeq` shape.

Keeping `targetType` free at the input bypasses the
dep-elim wall on `Ty.id ... = varType context position` that
plagues direct `cases` on a Term at a fixed `Ty.id ...` index. -/
def Term.oeqRefl_raw_inv
    {targetType : Ty level scope}
    {witnessRawSource : RawTerm scope}
    (genericTerm :
      Term context targetType (RawTerm.oeqRefl witnessRawSource)) :
    Σ' (carrier : Ty level scope)
       (_ :
         targetType = Ty.oeq carrier witnessRawSource witnessRawSource),
       HEq genericTerm
         (Term.oeqRefl (context := context) carrier witnessRawSource) := by
  cases genericTerm
  exact ⟨_, rfl, HEq.rfl⟩

/-- A typed `Term` whose raw projection is
`RawTerm.uaToEquiv (RawTerm.oeqRefl witnessRawSource)` is uninhabited.

The proof inverts the outer term to expose its unique
`Term.uaToEquiv` ctor (whose proof field has type
`Ty.id (Ty.universe innerLevel _) _ _`), then applies
`Term.oeqRefl_raw_inv` to extract a `Ty.id ... = Ty.oeq ...`
equation that `cases` refutes via Ty constructor injectivity.

The outer `suffices` indirection frees the `someType` index so the
matcher on `uaTerm` does not see a fixed dependent type. -/
theorem Term.uaToEquiv_excludes_oeqRefl_witness
    {someType : Ty level scope}
    {witnessRawSource : RawTerm scope}
    (uaTerm : Term context someType
                   (RawTerm.uaToEquiv (RawTerm.oeqRefl witnessRawSource))) :
    False := by
  suffices key :
      ∀ {someTypeInner : Ty level scope}
        (genericTerm :
          Term context someTypeInner
            (RawTerm.uaToEquiv (RawTerm.oeqRefl witnessRawSource))),
        False by
    exact key uaTerm
  intro someTypeInner genericTerm
  cases genericTerm with
  | uaToEquiv _ _ _ _ _ _ proofTerm =>
    obtain ⟨_, typeEq, _⟩ := Term.oeqRefl_raw_inv proofTerm
    cases typeEq

end LeanFX2
