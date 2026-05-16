import LeanFX2.Term.WeakenInverse

/-! # Term/TypedInversion — typed structural inversion for `Term.app`
shape.

Prerequisite work for the typed-η redesign (per
`feedback_typed_eta_lam_inv_cascade_blocker_2026_05_16.md`).  Ships
typed structural inversion lemmas for `Term.app`-shaped intrinsic
terms, allowing downstream consumers (lift_lam η-arm, subject
reduction, decidable conversion) to recover the inner typed
structure.

## What this module ships

### `Term.app_inv` — universal inversion for `RawTerm.app` shape

Given any typed term `genericTerm : Term context targetType
(RawTerm.app fnRaw argRaw)`, exactly one of `Term.app` or
`Term.appPi` produced it.

* The `Term.app` arm recovers `fnTerm : Term context (Ty.arrow
  innerDomainType targetType) fnRaw` plus `argTerm : Term context
  innerDomainType argRaw`.
* The `Term.appPi` arm recovers a dependent-Π function plus an
  equation `innerCodomainType.subst0 innerDomainType argRaw =
  targetType` (cannot be refuted structurally because `subst0` is
  reducible to any shape).

The disjunction form keeps `targetType` free, sidestepping the
`Ty.X = varType ctx pos` dep-elim wall: `cases genericTerm` runs
cleanly because the result-type index is unconstrained.

### `Term.app_inv_arrow` — arrow-output specialization

Specialization at `targetType = Ty.arrow A B`.  Same disjunction
shape; the consumer that knows the output is an arrow type can use
this directly without re-specializing.

### `Term.app_inv_pi` — Π-output specialization

Specialization at `targetType = Ty.piTy A B`.

## Why no general `Term.weaken_inv`

The general inversion `Term.weaken_inv : Term (ctx.cons newType)
ty.weaken raw.weaken → ∃ inner, ... = Term.weaken inner` requires
75-ctor structural induction with per-ctor type/raw equation
unpacking.  Shipped scope here is the structural foundation
(`Term.app_inv`) on which a focused eta-shape destructor builds.
The general `Term.weaken_inv` is deferred to a follow-up commit
once concrete consumers identify which raw shapes need it.

## Root status

Foundation; zero axioms throughout.  Verified via `lake build
LeanFX2 LeanFX2Audit`. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat}
variable {context : Ctx mode level scope}

/-! ## `Term.app_inv` — universal inversion.

`RawTerm.app fnRaw argRaw` raw shape is produced by exactly two
Term constructors:
* `Term.app    : ...  Term context codomainType                       (RawTerm.app fnRaw argRaw)`
* `Term.appPi  : ...  Term context (codomainType.subst0 dom argRaw)   (RawTerm.app fnRaw argRaw)`

Disambiguation in the universal form keeps `targetType` free so
`cases genericTerm` does not hit the dep-elim wall on
`varType context position` / `Ty.X` indices.  The output is a
disjoint sum over the two producing constructors. -/

/-- **Universal inversion** for `Term.app` / `Term.appPi`.  Given a
typed term whose raw is `RawTerm.app fnRaw argRaw`, decompose as
either `Term.app fnTerm argTerm` (with `fnTerm` at the canonical
arrow type) or `Term.appPi fnTerm argTerm` (with an equation that
the dependent-Π subst0 produces the requested target). -/
def Term.app_inv
    {targetType : Ty level scope}
    {fnRaw argRaw : RawTerm scope}
    (genericTerm :
      Term context targetType (RawTerm.app fnRaw argRaw)) :
    (Σ' (innerDomainType : Ty level scope)
        (fnTerm :
          Term context (Ty.arrow innerDomainType targetType) fnRaw)
        (argTerm : Term context innerDomainType argRaw),
        HEq genericTerm (Term.app fnTerm argTerm)) ⊕'
    (Σ' (innerDomainType : Ty level scope)
        (innerCodomainType : Ty level (scope + 1))
        (_ : innerCodomainType.subst0 innerDomainType argRaw = targetType)
        (fnTerm :
          Term context (Ty.piTy innerDomainType innerCodomainType) fnRaw)
        (argTerm : Term context innerDomainType argRaw),
        HEq genericTerm (Term.appPi fnTerm argTerm)) := by
  cases genericTerm
  case app innerDomain fnTerm argTerm =>
      exact PSum.inl ⟨innerDomain, fnTerm, argTerm, HEq.rfl⟩
  case appPi innerDomain innerCodomain fnTerm argTerm =>
      exact PSum.inr
        ⟨innerDomain, innerCodomain, rfl, fnTerm, argTerm, HEq.rfl⟩

/-- **Arrow-typed specialization** of `Term.app_inv`.  At known
`Ty.arrow A B` output, the `Term.app` arm provides the canonical
arrow function; the `Term.appPi` arm surfaces with an equation
`innerCodomainType.subst0 ... = Ty.arrow A B`.  Both arms remain
because `subst0` can reduce to an arrow shape (the consumer needs
to choose). -/
def Term.app_inv_arrow
    {arrowDomainType arrowCodomainType : Ty level scope}
    {fnRaw argRaw : RawTerm scope}
    (genericTerm :
      Term context (Ty.arrow arrowDomainType arrowCodomainType)
        (RawTerm.app fnRaw argRaw)) :
    (Σ' (innerDomainType : Ty level scope)
        (fnTerm :
          Term context
            (Ty.arrow innerDomainType
              (Ty.arrow arrowDomainType arrowCodomainType)) fnRaw)
        (argTerm : Term context innerDomainType argRaw),
        HEq genericTerm (Term.app fnTerm argTerm)) ⊕'
    (Σ' (innerDomainType : Ty level scope)
        (innerCodomainType : Ty level (scope + 1))
        (_ : innerCodomainType.subst0 innerDomainType argRaw
             = Ty.arrow arrowDomainType arrowCodomainType)
        (fnTerm :
          Term context (Ty.piTy innerDomainType innerCodomainType) fnRaw)
        (argTerm : Term context innerDomainType argRaw),
        HEq genericTerm (Term.appPi fnTerm argTerm)) :=
  Term.app_inv genericTerm

/-- **Π-typed specialization** of `Term.app_inv`.  At known
`Ty.piTy A B` output, both arms surface (the `Term.app` arm has
its target type as the literal `Ty.piTy A B`, which is unusual
but possible if `A B` are independent of `argRaw`; the `Term.appPi`
arm covers the standard case via the `subst0` equation). -/
def Term.app_inv_pi
    {piDomainType : Ty level scope}
    {piCodomainType : Ty level (scope + 1)}
    {fnRaw argRaw : RawTerm scope}
    (genericTerm :
      Term context (Ty.piTy piDomainType piCodomainType)
        (RawTerm.app fnRaw argRaw)) :
    (Σ' (innerDomainType : Ty level scope)
        (fnTerm :
          Term context
            (Ty.arrow innerDomainType
              (Ty.piTy piDomainType piCodomainType)) fnRaw)
        (argTerm : Term context innerDomainType argRaw),
        HEq genericTerm (Term.app fnTerm argTerm)) ⊕'
    (Σ' (innerDomainType : Ty level scope)
        (innerCodomainType : Ty level (scope + 1))
        (_ : innerCodomainType.subst0 innerDomainType argRaw
             = Ty.piTy piDomainType piCodomainType)
        (fnTerm :
          Term context (Ty.piTy innerDomainType innerCodomainType) fnRaw)
        (argTerm : Term context innerDomainType argRaw),
        HEq genericTerm (Term.appPi fnTerm argTerm)) :=
  Term.app_inv genericTerm

end LeanFX2
