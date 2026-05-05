import LeanFX2.Reduction.Cumul

/-! # Reduction/CumulCastElim — BHKM cast-elim primitives for `ConvCumul`

Pattern-agnostic primitives shared by both Pattern 2 (Benton rename arms,
`Reduction/CumulBenton.lean`) and Pattern 3 (Allais subst arms,
`Reduction/CumulAllais.lean`).

`Term.substHet`'s `lam` / `lamPi` / `pair` / `snd` / `appPi` arms wrap the
result in propositional `Ty.X_substHet_commute` casts.  Lifting cong rules
through these casts requires the transport-through-eq utility below: for
any propositional type equality `eq : ty1 = ty2`, `(eq ▸ term)` and
`term` are ConvCumul-related (heterogeneously, since their types
differ).  `Term.rename`'s analogous casts (`Ty.X_rename_commute`) reuse
the same primitives.

This is BHKM JAR'12 p.17 `cast_elim_cong` adapted to FX's heterogeneous
`ConvCumul`.

## Reference

Benton, Hur, Kennedy, McBride, *Strongly Typed Term Representations in
Coq*, JAR 2012 §6 (polymorphic case discipline).  FX memory
`reference_pattern_bhkm_ladder`.

## Audit

All four primitives ship zero-axiom under strict policy; verified in
`Smoke/AuditCumulSubstCompat.lean`.
-/

namespace LeanFX2

/-- BHKM cast-elim left: a term and its left-side propositional
cast are ConvCumul-related.  FX analog of BHKM JAR'12 p.17
`cast_elim_cong`. -/
theorem ConvCumul.cast_eq_left_benton
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {someTyOne someTyTwo : Ty level scope}
    {someRaw : RawTerm scope}
    (eq : someTyOne = someTyTwo)
    (someTerm : Term context someTyOne someRaw) :
    ConvCumul (eq ▸ someTerm) someTerm := by
  cases eq
  exact ConvCumul.refl someTerm

/-- BHKM cast-elim right: symmetric to `cast_eq_left_benton`. -/
theorem ConvCumul.cast_eq_right_benton
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {someTyOne someTyTwo : Ty level scope}
    {someRaw : RawTerm scope}
    (eq : someTyOne = someTyTwo)
    (someTerm : Term context someTyOne someRaw) :
    ConvCumul someTerm (eq ▸ someTerm) := by
  cases eq
  exact ConvCumul.refl someTerm

/-- BHKM cast-elim both: when an existing ConvCumul is wrapped
identically on both sides by the same propositional cast, the
cast lifts through.  Used by Allais arms whose `Term.substHet`
output carries a `Ty.subst0_substHet_commute` cast (snd / pair /
appPi / lam / lamPi). -/
theorem ConvCumul.cast_eq_both_benton
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {someTyOne someTyTwo : Ty level scope}
    {firstRaw secondRaw : RawTerm scope}
    {firstTerm : Term context someTyOne firstRaw}
    {secondTerm : Term context someTyOne secondRaw}
    (eq : someTyOne = someTyTwo)
    (origRel : ConvCumul firstTerm secondTerm) :
    ConvCumul (eq ▸ firstTerm) (eq ▸ secondTerm) := by
  cases eq
  exact origRel

/-- BHKM cast-elim INDEPENDENT: each endpoint may carry its own
type-equation cast.  Used for cong cases where the two sides
involve different cast equations (e.g., `lamCong` with different
codomain types per side, `pairCong` / `sndCong` / `appPiCong`
with `Ty.subst0_substHet_commute` casts depending on per-side raw
witnesses). -/
theorem ConvCumul.cast_eq_indep_benton
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstTy firstTy' secondTy secondTy' : Ty level scope}
    {firstRaw secondRaw : RawTerm scope}
    {firstTerm : Term context firstTy firstRaw}
    {secondTerm : Term context secondTy secondRaw}
    (eqFirst : firstTy = firstTy')
    (eqSecond : secondTy = secondTy')
    (origRel : ConvCumul firstTerm secondTerm) :
    ConvCumul (eqFirst ▸ firstTerm) (eqSecond ▸ secondTerm) := by
  cases eqFirst
  cases eqSecond
  exact origRel

end LeanFX2
