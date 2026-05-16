import LeanFX2.Term.WeakenInverse
import LeanFX2.Term.PartialStrengthen

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

### `Term.weaken_inv_arrow_option` — typed weaken inversion (Option form)

Specialization of `Term.unweaken?` (`Term/PartialStrengthen.lean`)
to arrow type and known function-raw: given `Term (context.cons
newType) (Ty.arrow domainType codomainType).weaken fnRaw.weaken`,
returns `Option (Term context (Ty.arrow domainType codomainType)
fnRaw)`.

Why Option rather than `∃ originalFn, ... = Term.weaken originalFn`?
The existence form requires a 78-case parallel induction proving
every typed-strengthening producer commutes with renaming
(equivalent to extending `StrengtheningResult` with a `termRenames`
HEq field).  Estimated ~5500-7000 LoC.  The Option form is the
immediately-shippable infrastructure that downstream consumers can
chain through their own structural information.

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

/-! ## `Term.weaken_inv_arrow` — typed weaken inversion at arrow type.

The typed-eta redesign's `lift_lam` η-arm needs to recover the
unweakened function from a weakened-shape `Term (ctx.cons newType)
(Ty.arrow A B).weaken fnRaw.weaken`.  Mathematically: every
typed term whose type and raw indices are both weakenings is in
the image of `Term.weaken`.

### Architecture

The kernel already ships:

* `Term.unweaken? : Term (ctx.cons newType) sourceType.weaken
  sourceRaw.weaken → Option (Term ctx sourceType sourceRaw)` — the
  computational inversion (`Term/PartialStrengthen.lean`).
* `Term.usesNewestSlotTyped? : Term ... → Bool` — the boolean
  predicate.
* `Term.not_usesNewestSlotTyped?_imp_strengthenTyped?_some` — the
  semantic witness exists when the slot is unused.

These give the **Option-form** of typed weaken inversion at any
type/raw indices.  The companion soundness theorem `wt = Term.weaken
inner` when `unweaken? wt = some inner` requires extending
`StrengtheningResult` with a `termRenames` field (HEq linking
sourceTerm to a rename of targetTerm) — that extension cascades
through all 78 producers, deferred to a follow-up batch.

### What this section ships

* `Term.weaken_inv_arrow_option` — thin arrow-typed wrapper around
  `Term.unweaken?`.  Output: `Option (Term context (Ty.arrow
  domainType codomainType) fnRaw)`.  Zero new infrastructure.
  Consumers (lift_lam η-arm, decidable conversion, subject
  reduction app cases) can refute the `none` case via structural
  information from the context in which they invoke this lemma.

### What's deferred

The full **existence form** `∃ originalFn, weakenedFn = Term.weaken
originalFn` for an OPAQUE `weakenedFn` requires extending
`StrengtheningResult` with a `termRenames` HEq field together with
a parallel 78-case induction proving each typed-strengthening
producer respects renaming.  See `feedback_typed_eta_lam_inv_
cascade_blocker_2026_05_16.md` for the structural reasoning.
Estimated work: ~5500-7000 LoC for the full producer cascade. -/

/-- **Arrow-typed Option-form weaken inversion**.  Thin wrapper
around `Term.unweaken?` at known arrow type and known function-raw.
Returns the unweakened typed function term if the weakened input
genuinely came from a `Term.weaken`; otherwise `none`.

Consumers that have structural information forcing the input to
be a `Term.weaken` (e.g. the lift_lam η-arm, where the input is
derived from a `Term.app fnTerm (Term.var 0)` body via `app_inv`)
can refute the `none` case via their own structural analysis.

This is the immediately-shippable inversion infrastructure; the
universal existence form is gated on the `StrengtheningResult`
`termRenames` extension. -/
def Term.weaken_inv_arrow_option
    {newType : Ty level scope}
    {domainType codomainType : Ty level scope}
    {fnRaw : RawTerm scope}
    (weakenedFn :
      Term (context.cons newType)
           (Ty.arrow domainType codomainType).weaken
           fnRaw.weaken) :
    Option (Term context (Ty.arrow domainType codomainType) fnRaw) :=
  LeanFX2.Term.unweaken? (sourceType := Ty.arrow domainType codomainType)
                         (sourceRaw := fnRaw) weakenedFn

end LeanFX2
