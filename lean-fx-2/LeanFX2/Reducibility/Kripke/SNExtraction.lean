import LeanFX2.Reducibility.Kripke.Project

/-! # LeanFX2.Reducibility.Kripke.SNExtraction — universal SN dispatcher.

This module ships the universal SN projection from a `ReducibleK n T t`
reducibility witness at any Ty.  It dispatches case-by-case via the
per-Ty `sn_of_X` extractor family in `Project.lean` (closed-leaf arms
under `Basic.lean`).

The dispatcher closes the M04/K12.27 sub-prerequisite "Tait reducibility
implies SN" half of the strong-normalization headline: once the Kripke
fundamental theorem `Term → ReducibleK` ships (full closure of
`Fundamental.lean`), the corollary `Term.strong_normalization` is one
composition.

This file also ships the partial M04 headline
`Term.strong_normalization_from_reducibility` which forms the second
half of that composition.

## References

- Tait 1967, "Intensional interpretations of functionals of finite type"
- Girard 1971 §6 (universal SN extraction from logical-relation membership)
- Ahmed 2006 §5 (step-indexed SN extraction)
-/

namespace LeanFX2

/-- Universal SN projection from a Kripke Tait reducibility witness at
any Ty.

Given `termIsR : ReducibleK (stepCount + 1) ty term`, dispatches
case-by-case on `ty` via the per-Ty `sn_of_X` extractor family.  All
twenty-five Ty constructors are explicitly enumerated — no wildcard
falls through per the CLAUDE.md no-wildcard discipline.

The proof is purely definitional: each `sn_of_X` lemma already
projects the SN component from its corresponding closure conjunction
(or returns the body directly for closed-leaf arms).  The cascade
follows the structure of `ReducibleKBody` in `Predicate.lean`. -/
theorem ReducibleK.sn_of_any
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    {term : Term context ty raw}
    {stepCount : Nat}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1) ty raw term) :
    Term.isStronglyNormalizing term := by
  cases ty with
  | unit => exact ReducibleK.sn_of_unit termIsR
  | bool => exact ReducibleK.sn_of_bool termIsR
  | nat => exact ReducibleK.sn_of_nat termIsR
  | arrow _ _ => exact ReducibleK.sn_of_arrow termIsR
  | piTy _ _ => exact ReducibleK.sn_of_piTy termIsR
  | sigmaTy _ _ => exact ReducibleK.sn_of_sigmaTy termIsR
  | tyVar _ => exact ReducibleK.sn_of_tyVar termIsR
  | id _ _ _ => exact ReducibleK.sn_of_id termIsR
  | listType _ => exact ReducibleK.sn_of_listType termIsR
  | optionType _ => exact ReducibleK.sn_of_optionType termIsR
  | eitherType _ _ => exact ReducibleK.sn_of_eitherType termIsR
  | «universe» _ _ => exact ReducibleK.sn_of_universe termIsR
  | empty => exact ReducibleK.sn_of_empty termIsR
  | interval => exact ReducibleK.sn_of_interval termIsR
  | path _ _ _ => exact ReducibleK.sn_of_path termIsR
  | glue _ _ => exact ReducibleK.sn_of_glue termIsR
  | oeq _ _ _ => exact ReducibleK.sn_of_oeq termIsR
  | idStrict _ _ _ => exact ReducibleK.sn_of_idStrict termIsR
  | equiv _ _ => exact ReducibleK.sn_of_equiv termIsR
  | refine _ _ => exact ReducibleK.sn_of_refine termIsR
  | record _ => exact ReducibleK.sn_of_record termIsR
  | codata _ _ => exact ReducibleK.sn_of_codata termIsR
  | session _ => exact ReducibleK.sn_of_session termIsR
  | effect _ _ => exact ReducibleK.sn_of_effect termIsR
  | modal _ _ => exact ReducibleK.sn_of_modal termIsR

/-- **M04 — Tait Strong Normalization (PARTIAL — fundamental theorem
pending).**  Given a Kripke Tait reducibility witness at any step
`n + 1`, the witnessing typed term strongly normalizes.

This is the second half of the strong-normalization headline.  The
first half — the fundamental theorem `Term → ReducibleK` — is the
remaining M04/K12.27 work, currently incomplete (closed-leaf base
cases plus eliminator/introducer fundamentals shipped, β-redex
backward closures pending the head-expansion cascade).

Once the fundamental theorem ships in full, the M04 headline
follows by:

```
theorem Term.strong_normalization (term : Term context ty raw) :
    Term.isStronglyNormalizing term :=
  Term.strong_normalization_from_reducibility
    (ReducibleK.fundamental term (stepCount := 0))
```

The partial headline as shipped already discharges the SN extraction
half of the Tait pattern — it is the universally usable corollary
of the full per-Ty closure structure. -/
theorem Term.strong_normalization_from_reducibility
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    {term : Term context ty raw}
    {stepCount : Nat}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1) ty raw term) :
    Term.isStronglyNormalizing term :=
  ReducibleK.sn_of_any termIsR

end LeanFX2
