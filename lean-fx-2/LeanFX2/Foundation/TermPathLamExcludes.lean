import LeanFX2.Term
import LeanFX2.Foundation.IsClosedTy

/-! # Foundation/TermPathLamExcludes — vacuity at `RawTerm.pathLam` under `IsClosedTy`

`Term.pathLam` is the **unique** Term constructor whose raw projection
is `RawTerm.pathLam`, and its return type is forced to `Ty.path
carrierType leftEndpoint rightEndpoint`.  Since `IsClosedTy` does not
enumerate `Ty.path` (path types carry RawTerm endpoints that may
reference bound variables; see `IsClosedTy.lean:31`), any term whose
raw projection is `pathLam` at a closed type is uninhabited.

## Why this matters

Future `RawStep.par.lift_full_hcomp` work needs to discharge the β
arms of `RawStep.par.hcomp_inv` (`hcompBeta` / `hcompBetaDeep`) under
a `DispatchAtom.hcomp` precondition that restricts the carrier type
to `IsClosedTy`-shape.  In those β arms the inversion gives `sidesRaw
= RawTerm.pathLam pathBody.weaken`; the typed `sidesValue : Term ctx
carrierType (RawTerm.pathLam ...)` then must be `Term.pathLam`, forcing
`carrierType = Ty.path ...` and contradicting `IsClosedTy carrierType`.

The single shipped lemma here is the vacuity witness that closes the
β arms via pure structural inversion — no kernel β extension needed.

## Cascade role

* Consumed by future `RawStep.par.lift_full_hcomp` (#2016).
* Same recipe applies to:
  * `lift_full_hcompPath` (#2017) — sides field is path-typed by
    construction, but inversion still leans on `Term.pathLam`
    uniqueness via `Term.pathLamDestruct`.
  * `lift_full_transp` (#2015) — transp_inv's `transpReflBeta` /
    `transpReflBetaDeep` arms put `RawTerm.pathLam` at the path
    position; closed-carrier vacuity discharges β when carrierType is
    closed.

## Audit

Verified zero-axiom via `#print axioms`.

## Pitfalls + mitigations

* P-1 (match-compiler propext on big inductives): The proof uses
  `suffices key` to free `someType` index, then `cases someTerm` runs
  on the freed-index form so the matcher does not partially-apply on
  fixed `someType`.
* P-13 (Decidable instance synthesis): N/A — `False` is the conclusion;
  no Decidable needed.
-/

namespace LeanFX2

/-- A typed `Term` whose raw projection is `RawTerm.pathLam` at a
closed type is uninhabited.  The proof inverts the term to extract its
unique `Term.pathLam` ctor (whose return type is `Ty.path ...`), then
cases on the `IsClosedTy` hypothesis — which has no `Ty.path` ctor —
to derive False.

The `suffices` indirection frees the `someType` index so the
matcher on `genericTerm` does not see a fixed dependent type. -/
theorem Term.pathLam_excludes_closedTy
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {bodyRaw : RawTerm (scope + 1)}
    (someTerm : Term context someType (RawTerm.pathLam bodyRaw))
    (closedSomeType : IsClosedTy someType) : False := by
  suffices key :
      ∀ {someTypeInner : Ty level scope}
        (genericTerm :
          Term context someTypeInner (RawTerm.pathLam bodyRaw)),
        IsClosedTy someTypeInner → False by
    exact key someTerm closedSomeType
  intro someTypeInner genericTerm genericClosed
  cases genericTerm
  cases genericClosed

end LeanFX2
