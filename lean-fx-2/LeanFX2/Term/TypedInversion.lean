import LeanFX2.Term.WeakenInverse
import LeanFX2.Term.PartialStrengthen.Weaken

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

This file keeps the older Option-form API because a few eta-planning
consumers still want a computational discriminator.  The later
renaming-image theorem stack now supplies the proper existence-form
API in `StrengtheningImage`: use `Term.weaken_inv_arrow` for new
consumer proofs that need a recovered inner term and an equality
against `Term.weaken`.

### `Ty.weaken_inj` + `Term.weakenInverse_atVarZero`

Two supporting lemmas still used directly by typed eta-planning
proofs and by older computational inversion call sites:

* `Ty.weaken_inj` — `Ty.weaken` is injective.  Proved via the
  round-trip identity `Ty.strengthen?_weaken`.  Foundational for
  recovering the inner type from a weakening-shape type equation
  (e.g. inside the `Term.lam` arm of a `weaken_inv_arrow`-style
  cascade where `(Ty.arrow A B).weaken = (Ty.arrow A' B').weaken`
  needs to be inverted to `A = A'` and `B = B'`).
* `Term.weakenInverse_atVarZero` — Layer 2 typed inversion at the
  `RawTerm.var ⟨0, _⟩` raw shape (companion to
  `Term.weakenInverse_atVar` for `RawTerm.var (Fin.succ pos')`).
  The eta-shape consumer recovers the argTerm of `Term.app fnTerm
  (Term.var 0)` via this helper.

## Root status

Foundation; zero axioms throughout.  Use narrow module builds for
inner-loop verification; broad audit belongs to phase-level closeout. -/

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

/-! ## `Term.weaken_inv_arrow_option` — computational arrow check.

The typed-eta redesign's `lift_lam` η-arm needs to recover the
unweakened function from a weakened-shape `Term (ctx.cons newType)
(Ty.arrow A B).weaken fnRaw.weaken`.  Mathematically: every
typed term whose type and raw indices are both weakenings is in
the image of `Term.weaken`.

The full existence-form arrow inverse now lives in
`StrengtheningImage` as `Term.weaken_inv_arrow`, derived from the
renaming-image theorem stack.  This local definition remains as a
thin `unweaken?` wrapper for call sites that want to compute before
deciding which typed branch to enter. -/

/-- **Arrow-typed Option-form weaken inversion**.  Thin wrapper
around `Term.unweaken?` at known arrow type and known function-raw.
Returns the unweakened typed function term if the weakened input
genuinely came from a `Term.weaken`; otherwise `none`.

Consumers that have structural information forcing the input to
be a `Term.weaken` (e.g. the lift_lam η-arm, where the input is
derived from a `Term.app fnTerm (Term.var 0)` body via `app_inv`)
can refute the `none` case via their own structural analysis.

New proofs should prefer the existence form `Term.weaken_inv_arrow`
unless they specifically need the `Option` discriminator. -/
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

/-! ## Supporting infrastructure for typed weaken inversion.

The renaming-image theorem stack made the old full-cascade plan
obsolete.  This section records the smaller pieces that still matter
independently of the headline existence theorem:

* `Ty.weaken_inj` — `Ty.weaken` is injective.  Foundational; used
  by every step of the cascade that inverts `(Ty.arrow A B).weaken
  = X.weaken` to `Ty.arrow A B = X`.
* `Term.weakenInverse_atVarZero` — Layer 2 typed inversion at the
  `RawTerm.var ⟨0, _⟩` raw shape (companion to the existing
  `Term.weakenInverse_atVar` for `Fin.succ pos'`).  The eta-shape
  consumer recovers the argTerm of `Term.app fnTerm (Term.var 0)`
  via this helper.

These two pieces still compose with `Term.app_inv` and either the
computational `Term.weaken_inv_arrow_option` or the stronger
`Term.weaken_inv_arrow`, depending on what the consumer needs. -/

/-- **`Ty.weaken` is injective.**  Proved via the round-trip identity
`Ty.strengthen?_weaken : T.weaken.strengthen? = some T`: if two types
have equal weakenings, applying `strengthen?` to both sides yields
`some leftTy = some rightTy`, and `Option.some` injectivity finishes
the proof.

Foundational utility used wherever a weaken-shape type equation needs
to be inverted (e.g. recovering the inner domain of an arrow whose
weakening matches another arrow's weakening). -/
theorem Ty.weaken_inj {level scope : Nat}
    {leftTy rightTy : Ty level scope}
    (weakenEq : leftTy.weaken = rightTy.weaken) :
    leftTy = rightTy := by
  have leftStrengthen : leftTy.weaken.strengthen? = some leftTy :=
    Ty.strengthen?_weaken leftTy
  have rightStrengthen : rightTy.weaken.strengthen? = some rightTy :=
    Ty.strengthen?_weaken rightTy
  rw [weakenEq] at leftStrengthen
  rw [rightStrengthen] at leftStrengthen
  injection leftStrengthen with strengthenSomeEq
  exact strengthenSomeEq.symm

/-- **Typed weaken inversion at the `RawTerm.var ⟨0, _⟩` raw shape.**

In a context `context.cons newType`, the only Term ctor producing
`RawTerm.var ⟨0, _⟩` raw is `Term.var ⟨0, _⟩` itself.  Its type is
`varType (context.cons newType) ⟨0, _⟩ = newType.weaken` by the first
arm of `varType`.

This is the companion to `Term.weakenInverse_atVar` (which handles
`RawTerm.var (Fin.succ pos')`).  Together the two cover both arms
of `varType`'s definition.

Consumed by the typed-eta lift_lam η-arm to identify the `Term.var
⟨0, _⟩` argument inside `Term.app fnTerm (Term.var ⟨0, _⟩)`. -/
def Term.weakenInverse_atVarZero
    {newType : Ty level scope}
    {weakenedTy : Ty level (scope + 1)}
    (weakenedTerm : Term (context.cons newType) weakenedTy
                          (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)) :
    Σ' (_ : weakenedTy = newType.weaken),
      HEq weakenedTerm
          (Term.var (context := context.cons newType)
                    ⟨0, Nat.zero_lt_succ scope⟩) := by
  suffices key :
      ∀ {genericTy : Ty level (scope + 1)}
        (genericTerm : Term (context.cons newType) genericTy
                              (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)),
        Σ' (_ : genericTy = newType.weaken),
          HEq genericTerm
              (Term.var (context := context.cons newType)
                        ⟨0, Nat.zero_lt_succ scope⟩) by
    exact key weakenedTerm
  intro genericTy genericTerm
  cases genericTerm
  exact ⟨rfl, HEq.rfl⟩

/-! ## `Term.weaken_inv_arrow` — conditional existence form

The Phase A close-out of the Step.eta integration plan lives in
`LeanFX2/Term/StrengtheningImage.lean` because it consumes
`weaken_inv_of_strengthenTyped?_some`.  The theorem is named
`LeanFX2.Term.weaken_inv_arrow` and ships at the end of that
file's "Image theorem trio" block. -/

end LeanFX2
