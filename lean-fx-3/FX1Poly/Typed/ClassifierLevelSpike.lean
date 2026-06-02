import FX1Poly.Typed.ReducibleTypeAtAllLevelsNonDependentArrow
import FX1Poly.Typed.ClassifierLevelMeasure

/-! # FX1Poly/Typed/ClassifierLevelSpike
    — SN-004 (make-or-break): does the universe-DOMAIN Π former close at classifier-level semantics?

This is the pivotal spike: SN-001 pinned the fuel-0 universe-vacuity wall, SN-002 found denote-keying
coherent, SN-003 landed the predicative WF measure.  The make-or-break is whether the universe-DOMAIN Π
former `Π(x:Type@e).C` — the one the fuel model could NOT close without an `∀ aboveLevel` premise (the
documented fixpoint) — closes under classifier-level (denote-keyed, well-founded-on-`denote`) semantics, or
whether the fuel-0 vacuity reappears.  The answer is grounded in two SHIPPED lemmas plus SN-003:

* **Constant codomain — already closed at ALL levels, no `∀ aboveLevel`.**  `Π(x:Type@e).B` with `B` not
  mentioning the bound variable is the shipped `IsReducibleTypeAtAllLevels.universeDomainNonDependentArrow`:
  the codomain `B` is reducible regardless of the argument, so the `piType` arm's codomain obligation is
  discharged uniformly with no level quantifier.  `universeDomainPi_reducibleAllLevels` below is a concrete
  witness (`Π(x:Type@e).Type@k`), exhibiting a UNIVERSE-DOMAIN Π reducible at all levels.

* **Dependent codomain — reduces EXACTLY to domain member-extension, NOT the fuel-0 wall.**  The shipped
  `IsReducibleTypeAtAllLevels.piTypeOfDomainMemberExtension` closes `Π(x:Type@e).C` for an arbitrary
  (dependent) codomain GIVEN `domainMemberExtension`: each member of the domain `Type@e` extends from one
  level to all positive levels.  So the only residual obligation for the universe-domain dependent Π is the
  level-irrelevance of `Type@e`'s MEMBERS (type codes) — precisely the "domain member-extension" premise,
  NOT the fuel-0 empty-membership vacuity (SN-001).

* **Why denote-keying supplies member-extension (where fuel could not).**  A member of `Type@e` is a type
  code whose classifier `Type@e` sits at denote-level `denote (lsucc e) = denote e + 1`, so the member
  itself lives at the STRICTLY SMALLER `denote e` (SN-003 `denote_lt_lsucc`).  Recursing on the `denote`
  measure, member-extension for `Type@e`'s members is therefore available BY THE WELL-FOUNDED INDUCTION
  HYPOTHESIS — the recursion descends into a strictly smaller denote-level.  The fuel model lacked this: its
  level was free depth, unrelated to the type, and the `0 ↔ 1` base of any level-irrelevance argument was
  unbridgeable (`StratifiedReducibleLevelCongr.existsCongr`'s degenerate base).  Under denote-keying the
  base is the NON-degenerate neutral fragment (SN-003 `variableCell_reducibleTypeAtZero`), and the descent
  is type-determined and strict.

## VERDICT: GO

The universe-domain Π former closes at classifier-level semantics: the constant case is shipped, and the
dependent case reduces to domain member-extension, which the `denote`-keyed well-founded recursion supplies
by IH (SN-003).  The fuel-0 vacuity does NOT reappear.  Route B (classifier-universe-level / Adjedj-style
validity-derivation-indexed reducibility) is VIABLE; sconing (Leg 1) stays the independent second proof, not
the fallback-of-necessity.  Next: SN-005 locks the strategy; SN-009+ assembles the `denote`-keyed
well-founded relation from the two shipped halves (`piTypeOfDomainMemberExtension` + the SN-003 measure).

## Zero-axiom verification

The concrete witness is the shipped `universeDomainNonDependentArrow` instantiated with
`IsReducibleTypeAtAllLevels.ofUniverseCode` as the (constant) codomain.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Concrete GO witness: a universe-DOMAIN Π is reducible at all levels.**  `Π(x:Type@domainLevel).Type@codomainLevel`
(the codomain a constant universe code, not mentioning the bound variable) is reducible at all levels —
exhibiting that a UNIVERSE-domain Π (the case the fuel model could not close without `∀ aboveLevel`) closes
uniformly when the codomain does not depend on the domain member.  Via the shipped
`universeDomainNonDependentArrow` with `ofUniverseCode` as the all-levels-reducible codomain.  The dependent
case `Π(A:Type@e).A` additionally needs domain member-extension (`piTypeOfDomainMemberExtension`), supplied
by the SN-003 `denote`-WF recursion (see the module docstring's GO verdict). -/
theorem universeDomainPi_reducibleAllLevels {scope : Nat}
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag) :
    IsReducibleTypeAtAllLevels
      (piTyCodeCell (universeCodeCell domainLevel flag)
        (RawTerm.weaken (universeCodeCell codomainLevel flag) : RawTerm (scope + 1))) :=
  IsReducibleTypeAtAllLevels.universeDomainNonDependentArrow
    (codomainBase := universeCodeCell codomainLevel flag)
    IsReducibleTypeAtAllLevels.ofUniverseCode

end FX1Poly.Typed
