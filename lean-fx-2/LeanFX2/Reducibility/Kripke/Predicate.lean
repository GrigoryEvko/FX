import LeanFX2.Reducibility.Basic
import LeanFX2.Term.Rename

/-! # LeanFX2.Reducibility.Kripke.Predicate — step-indexed Kripke Tait

Direct Ty-recursive Kripke `ReducibleK` is rejected by Lean 4 v4.29.1
(the arrow closure's `ReducibleK (domainType.rename rho) ...` is not
a structural sub-Ty call; `termination_by`-based well-founded
recursion is banned by GatesCore line 51).

This file uses **step-indexed Kripke Tait**: recurse on a `Nat`
step counter, with each unfolding decreasing the step.  Lean
accepts Nat-structural recursion trivially.

## Encoding discipline

The naive single-match `ReducibleK : Nat → Ty → ... → Prop` over a
multi-arity (Nat × Ty) scrutinee leaks `propext` per
`feedback_lean_match_arity_axioms` memory.  This file factors the
match so Nat is outer (single-arg recursion) and Ty is inner via
`ReducibleKBody`.

## Reference

- Ahmed 2006, "Step-indexed syntactic logical relations"
- Krebbers et al (Iris), step-indexed predicates for separation logic
-/

namespace LeanFX2

/-- Inner per-Ty arm function: given a fixed step number for sub-calls
plus a Ty and a typed term, returns the per-Ty closure proposition.

This is the workhorse — split out from the outer Nat-scrutinee
to avoid the multi-arity match propext leak. -/
def ReducibleKBody {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (subCallPredicate :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (subTy : Ty level targetScope) {subRaw : RawTerm targetScope},
        Term targetCtx subTy subRaw → Prop)
    : ∀ (ty : Ty level scope) {raw : RawTerm scope},
        Term context ty raw → Prop
  -- Closed-leaf arms.
  | Ty.unit, _, term => Term.isStronglyNormalizing term
  | Ty.bool, _, term => Term.isStronglyNormalizing term
  | Ty.nat, _, term => Term.isStronglyNormalizing term
  | Ty.empty, _, term => Term.isStronglyNormalizing term
  | Ty.interval, _, term => Term.isStronglyNormalizing term
  | Ty.universe _ _, _, term => Term.isStronglyNormalizing term
  | Ty.tyVar _, _, term => Term.isStronglyNormalizing term
  -- Arrow with Kripke closure invoking subCallPredicate at subCallStep.
  | Ty.arrow domainType codomainType, _, functionTerm =>
      Term.isStronglyNormalizing functionTerm ∧
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        {rho : RawRenaming scope targetScope}
        (termRenaming : TermRenaming context targetCtx rho)
        {argumentRaw : RawTerm targetScope}
        (argumentTerm : Term targetCtx (domainType.rename rho) argumentRaw),
        subCallPredicate (domainType.rename rho) argumentTerm →
        subCallPredicate (codomainType.rename rho)
                   (Term.app (Term.rename termRenaming functionTerm)
                             argumentTerm)
  -- Remaining ctors: SN-only fallback for PoC.  Each gets its
  -- per-Ty-former closure in a follow-up port.  Full enumeration
  -- (no wildcard) avoids the match-compiler propext leak.
  | Ty.piTy _ _, _, term => Term.isStronglyNormalizing term
  | Ty.sigmaTy _ _, _, term => Term.isStronglyNormalizing term
  | Ty.id _ _ _, _, term => Term.isStronglyNormalizing term
  | Ty.listType _, _, term => Term.isStronglyNormalizing term
  | Ty.optionType _, _, term => Term.isStronglyNormalizing term
  | Ty.eitherType _ _, _, term => Term.isStronglyNormalizing term
  | Ty.path _ _ _, _, term => Term.isStronglyNormalizing term
  | Ty.glue _ _, _, term => Term.isStronglyNormalizing term
  | Ty.oeq _ _ _, _, term => Term.isStronglyNormalizing term
  | Ty.idStrict _ _ _, _, term => Term.isStronglyNormalizing term
  | Ty.equiv _ _, _, term => Term.isStronglyNormalizing term
  | Ty.refine _ _, _, term => Term.isStronglyNormalizing term
  | Ty.record _, _, term => Term.isStronglyNormalizing term
  | Ty.codata _ _, _, term => Term.isStronglyNormalizing term
  | Ty.session _, _, term => Term.isStronglyNormalizing term
  | Ty.effect _ _, _, term => Term.isStronglyNormalizing term
  | Ty.modal _ _, _, term => Term.isStronglyNormalizing term

/-- **Kripke Tait reducibility candidate**, step-indexed.

`ReducibleK 0 ty t` holds trivially.  At step `n+1`, dispatch to
`ReducibleKBody` with sub-calls at step `n` quantified through
the `subCallPredicate` parameter.

Recursion is on `Nat` only; Lean accepts this trivially. -/
def ReducibleK {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    : Nat → ∀ (ty : Ty level scope) {raw : RawTerm scope},
        Term context ty raw → Prop
  | 0 => fun _ {_} _ => True
  | stepCount + 1 =>
      ReducibleKBody
        (fun {_} {targetCtx'} subTy {_} subTerm =>
          @ReducibleK _ _ _ targetCtx' stepCount subTy _ subTerm)

end LeanFX2
