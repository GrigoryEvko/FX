import FX1Poly.Core.ReducibilityCandidateArrow
import FX1Poly.Core.SimpleTypeInterpretation

/-! # Foundation/PolyCell/Core/SimpleTypeErasure
    — the simple-type erasure of type-codes, as a relation (`ErasesTo`)

The strong-normalization bridge from the dependent kernel down to the simply-typed skeleton
(`SimplyTypedNormalization`) must assign a `SimpleType` to every type-code: a Π-type code
denotes an arrow, every other code denotes the base sort.  A structural *function*
`eraseType : RawTerm → SimpleType` is rejected zero-axiom — dispatching on one generator with a
wildcard over the other 193 leaks `propext` through the match compiler (the same obstacle that
forces the certifier onto fuel recursion).  So erasure is given **relationally**: a plain
inductive `Prop`, which never leaks `propext`.

  `ErasesTo (Π domainCode. codomainCode) (arrow da db)`  when the children erase to `da`, `db`
  `ErasesTo term base`                                    when `term` is not a Π-type code

This is correct for the current `HasTypeDescPi` fragment, whose only redex is Π-β (`piElim`
of `piIntro`): only Π-types need the arrow interpretation; Σ/universe/data codes all denote
`base` because the fragment has no eliminator that would create a redex at those types.  When
Σ-elimination lands, a `sigmaTyCode` arm is added here — additive, never a rewrite.

`ErasesTo` is **deterministic** (`ErasesTo.deterministic`): a type-code erases to at most one
simple type, so the bridge may read off simple types unambiguously.

## Zero-axiom verification

A plain inductive `Prop` + two derivation-inductive inversions (`base_eq`, `arrow_inv`) + a
determinism proof by induction on the first derivation.  Generator dispatch is via the
propext-free `RawTerm.rootGenerator` projection and `DecidableEq Generator`, never a wildcard
term match.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- `ErasesTo term simpleType` — the type-code `term` denotes the simple type `simpleType` in
the strong-normalization skeleton.  A Π-type code denotes an arrow built from the children's
erasures; every non-Π code denotes the base sort. -/
inductive ErasesTo : {scope : Nat} → RawTerm scope → SimpleType → Prop where
  /-- A Π-type code erases to an arrow of its domain and codomain erasures. -/
  | arrowFormer {scope : Nat} {domainCode : RawTerm scope}
      {codomainCode : RawTerm (scope + 1)} {domainErasure codomainErasure : SimpleType} :
      ErasesTo domainCode domainErasure →
      ErasesTo codomainCode codomainErasure →
      ErasesTo
        (.mkGen .gen_piTyCode ()
          (.childCons domainCode (.childCons codomainCode .childNil)))
        (.arrow domainErasure codomainErasure)
  /-- Every non-Π-type code erases to the base sort. -/
  | base {scope : Nat} {term : RawTerm scope} :
      term.rootGenerator ≠ Generator.gen_piTyCode →
      ErasesTo term .base

/-- Inversion at a non-Π code: if a term whose root is not `gen_piTyCode` erases at all, it
erases to `base`.  Induction on the derivation (so the index stays a variable — no
constructor-index unification). -/
theorem ErasesTo.base_eq {scope : Nat} {term : RawTerm scope} {erasure : SimpleType}
    (erases : ErasesTo term erasure)
    (notPiTyCode : term.rootGenerator ≠ Generator.gen_piTyCode) :
    erasure = .base := by
  cases erases with
  | arrowFormer _domainErases _codomainErases => exact absurd rfl notPiTyCode
  | base _ => rfl

/-- Inversion at a Π code: a Π-type code's erasure is the arrow of its children's erasures. -/
theorem ErasesTo.arrow_inv {scope : Nat} {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)} {erasure : SimpleType}
    (erases :
      ErasesTo
        (.mkGen .gen_piTyCode ()
          (.childCons domainCode (.childCons codomainCode .childNil)))
        erasure) :
    ∃ domainErasure codomainErasure,
      erasure = .arrow domainErasure codomainErasure ∧
      ErasesTo domainCode domainErasure ∧ ErasesTo codomainCode codomainErasure := by
  cases erases with
  | arrowFormer domainErases codomainErases =>
      exact ⟨_, _, rfl, domainErases, codomainErases⟩
  | base notPiTyCode => exact absurd rfl notPiTyCode

/-- **Erasure is deterministic**: a type-code erases to at most one simple type.  Induction on
the first derivation; the Π case inverts the second derivation with `arrow_inv` and recurses,
the base case reads off `base` from `base_eq`.  This lets the SN bridge read simple types off
type-codes unambiguously. -/
theorem ErasesTo.deterministic {scope : Nat} {term : RawTerm scope} {erasure1 : SimpleType}
    (erases1 : ErasesTo term erasure1) :
    ∀ {erasure2 : SimpleType}, ErasesTo term erasure2 → erasure1 = erasure2 := by
  induction erases1 with
  | arrowFormer _domainErases1 _codomainErases1 domainInductiveHypothesis
      codomainInductiveHypothesis =>
      intro erasure2 erases2
      obtain ⟨domainErasure2, codomainErasure2, erasure2Equation,
          domainErases2, codomainErases2⟩ := ErasesTo.arrow_inv erases2
      rw [erasure2Equation, domainInductiveHypothesis domainErases2,
        codomainInductiveHypothesis codomainErases2]
  | base notPiTyCode =>
      intro erasure2 erases2
      exact (ErasesTo.base_eq erases2 notPiTyCode).symm

end FX1Poly.Core
