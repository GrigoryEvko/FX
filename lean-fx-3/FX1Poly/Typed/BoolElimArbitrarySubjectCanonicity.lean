import FX1Poly.Typed.BoolElimClosedNormalForms
import FX1Poly.Typed.ClosedBoolCanonicity

/-! # FX1Poly/Typed/BoolElimArbitrarySubjectCanonicity
    — ARBITRARY-subject 4-engine bool canonicity: the eliminator engine is vacuous at boolCode (no SN/SR)

`BoolElimClosedNormalForms` (last firing) settled the eliminator engine's contribution to the CLOSED-NORMAL bool
canonical forms (vacuous, because a closed eliminator on a closed value scrutinee always ι-fires).  The
arbitrary-subject upgrade looked like it would need SN + SR over the combined (grown ∪ eliminator) engine — but a
sharper observation collapses it to a one-liner:

  **the current bool-elim engine's branches are GROWN-typed, and the grown engine has NO closed inhabitant of
  boolCode (`noClosedGrownTermAtBoolType`, the firing-45 bool twin of consistency).**

So a closed `boolElim(s, t, e) : boolTypeCell` requires `t : boolTypeCell` GROWN-typed — which is impossible.
Inverting the eliminator derivation to a branch and applying the grown vacuity refutes it directly — NO SN, NO SR.

  * **`HasTypeDescBoolElim.noClosedBoolElimAtBoolType` (★)** — a closed bool-elim term AT boolTypeCell is
    impossible (arbitrary subject): `cases` the derivation, take the `thenBranch` grown-typed at `boolTypeCell`
    (the eliminator's branches are grown-typed, and `cases` unifies the result type to `boolTypeCell`), apply
    `noClosedGrownTermAtBoolType`.

  * **`closedBoolCanonicalFormsWithElim` (★)** — the ARBITRARY-subject 4-engine bool canonicity: a closed term
    typed at boolTypeCell by ANY of the four engines (data-intro / base-type / grown / bool-elim) reduces by `↝*`
    to `boolTrue`/`boolFalse`.  Upgrades `closedNormalBoolCanonicalFormsWithElim` (last firing) OFF the `normal`
    hypothesis — the eliminator disjunct is ruled out for ARBITRARY subjects via the branch grown-vacuity.

## Honest finding: the current eliminator is VACUOUS at data types

This reveals a real limitation worth recording: the current `HasTypeDescBoolElim` (#1070) requires its branches to
be GROWN-typed (`HasTypeDescPi`), so it can eliminate INTO a function/universe (e.g. the smoke
`boolElim(boolTrue, Type@0, Type@0) : Type@1`) but NOT into a data type with data-VALUE branches — `boolElim b
true false : Bool` is NOT typeable (its branches `true`/`false` are data-intro-typed, not grown).  Hence the
eliminator is VACUOUS at `boolCode`, and "eliminator-computing canonicity AT a data type" is vacuous for it.
Genuinely-non-vacuous eliminator-computing canonicity (where `boolElim b true false` COMPUTES to the selected
value) needs a STRONGER eliminator whose branches can reference the data-intro engine — a combined intro/elim
engine, the deferred #1138 / GTL table-residency work.  So this firing CLOSES the bool-elim contribution to bool
canonicity (it adds nothing) and pins the honest boundary for the non-vacuous version.

## Zero-axiom verification

`cases` (the eliminator's single ctor, result type unified to `boolTypeCell`) + `noClosedGrownTermAtBoolType`
(firing 45) for the vacuity; the 4-way `rcases` + `standaloneBoolCanonicalForms` + `noClosedGrownTermAtBoolType`
for the canonicity.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ A closed bool-elim term at boolTypeCell is impossible (arbitrary subject).**  The bool-elim engine's
branches are GROWN-typed; inverting the derivation gives `thenBranch` grown-typed at `boolTypeCell` (the result
type unifies to `boolTypeCell`), which is vacuous (`noClosedGrownTermAtBoolType`).  The current eliminator cannot
eliminate INTO a data type with grown branches — vacuous at `boolCode`.  No SN, no SR. -/
theorem HasTypeDescBoolElim.noClosedBoolElimAtBoolType {profile : PolyProfile} {subject : RawTerm 0}
    (derivation : HasTypeDescBoolElim profile (TypingContext.empty : TypingContext profile 0)
      subject boolTypeCell) :
    False := by
  cases derivation with
  | boolElimIntro _motive scrutinee thenBranch elseBranch resultType _scrutineeTyped thenTyped _elseTyped =>
      exact HasTypeDescPi.noClosedGrownTermAtBoolType thenTyped

/-- **★ ARBITRARY-subject 4-engine bool canonicity.**  A closed term typed at `boolTypeCell` by ANY of the four
engines — data-intro values, base-type codes, the grown `HasTypeDescPi`, OR the bool eliminator
`HasTypeDescBoolElim` — reduces by `↝*` to `boolTrue`/`boolFalse`.  Upgrades `closedNormalBoolCanonicalFormsWithElim`
(last firing) OFF the `normal` hypothesis: the grown and bool-elim disjuncts are both vacuous at `boolCode`
(`noClosedGrownTermAtBoolType` / `noClosedBoolElimAtBoolType`), the value engines settle to a value directly. -/
theorem closedBoolCanonicalFormsWithElim {profile : PolyProfile} {subject : RawTerm 0}
    (typed :
      HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescBaseType profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescBoolElim profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell) :
    ∃ value : RawTerm 0, StepStar subject value ∧
      (value = boolTrueCell ∨ value = boolFalseCell) := by
  rcases typed with dataIntroTyped | baseTypeTyped | grownTyped | elimTyped
  · rcases standaloneBoolCanonicalForms (Or.inl dataIntroTyped) with valueEq | valueEq
    · subst valueEq; exact ⟨_, StepStar.refl _, Or.inl rfl⟩
    · subst valueEq; exact ⟨_, StepStar.refl _, Or.inr rfl⟩
  · rcases standaloneBoolCanonicalForms (Or.inr baseTypeTyped) with valueEq | valueEq
    · subst valueEq; exact ⟨_, StepStar.refl _, Or.inl rfl⟩
    · subst valueEq; exact ⟨_, StepStar.refl _, Or.inr rfl⟩
  · exact (HasTypeDescPi.noClosedGrownTermAtBoolType grownTyped).elim
  · exact (HasTypeDescBoolElim.noClosedBoolElimAtBoolType elimTyped).elim

end FX1Poly.Typed
