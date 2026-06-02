import FX1Poly.Typed.SimplyTypedTermInversionLevelFree
import FX1Poly.Typed.SimplyTypedNormalForm
import FX1Poly.Typed.SimplyTypedTermSubjectReductionLevelFree
import FX1Poly.Typed.SimplyTypedTermCanonicityLevelFree

/-! # FX1Poly/Typed/SimplyTypedTermConsistencyLevelFree
    — the inhabitation consequences of canonicity: closed simply-typed terms have arrow types, so universe
      codes are uninhabited.

The final theorem of the simply-typed metatheory.  Canonicity says every closed normal `SimplyTypedTermLF`
term is a lambda; a lambda's type is an arrow; reduction preserves typing.  Together: a closed simply-typed
term's type is necessarily an arrow.  Since `SimplyTypedTermLF` has no constants, the base (universe-code)
types are therefore uninhabited by closed terms — the fragment's consistency.

* `SimplyTypedTermLF.closedTermHasArrowType` — every closed simply-typed term has a Π-code (arrow) type.
* `SimplyTypedTermLF.noClosedTermAtUniverseCode` — consistency: no closed simply-typed term has a
  universe-code type (the head generators `gen_piTyCode` and `gen_universeCode` differ).

This closes the simply-typed STLC metatheory: strong normalization, confluence, decidable conversion,
canonical normal form, subject reduction, type-preserving normalization, canonicity, and now the
inhabitation/consistency consequences — all zero-axiom.

## Zero-axiom verification

`closedTermHasArrowType` composes `normalFormIsLambda` (canonicity ∘ normalization), `normalForm_typed`
(type-preserving normalization), and `inversionLambda` (the lambda's type is an arrow);
`noClosedTermAtUniverseCode` then discharges the universe-code case by `congrArg RawTerm.headGenerator` +
`Generator.noConfusion`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Every closed simply-typed term has an arrow type.**  Its canonical normal form is a lambda
(canonicity); the normal form has the same type (type-preserving normalization); and a lambda's type is a
Π-code over a weakened codomain (lambda inversion). -/
theorem SimplyTypedTermLF.closedTermHasArrowType {profile : PolyProfile}
    {term type : RawTerm 0}
    (typed : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term type) :
    ∃ domainCode codomainBase : RawTerm 0, type = piTyCodeCell domainCode (RawTerm.weaken codomainBase) := by
  obtain ⟨body, normalFormEq⟩ := typed.normalFormIsLambda
  have normalFormTyped := typed.normalForm_typed
  rw [normalFormEq] at normalFormTyped
  obtain ⟨domainCode, codomainBase, typeEq, _domainExpr, _codomainExpr, _bodyTyped⟩ :=
    normalFormTyped.inversionLambda
  exact ⟨domainCode, codomainBase, typeEq⟩

/-- **Consistency: universe codes are uninhabited by closed simply-typed terms.**  A closed simply-typed
term cannot have a universe-code type: every closed term has an arrow type, and an arrow (`gen_piTyCode`)
differs from a universe code (`gen_universeCode`) by head generator. -/
theorem SimplyTypedTermLF.noClosedTermAtUniverseCode {profile : PolyProfile}
    {term : RawTerm 0} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typed : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term
      (universeCodeCell levelExpr flag)) :
    False := by
  obtain ⟨_domainCode, _codomainBase, typeEq⟩ := typed.closedTermHasArrowType
  exact Generator.noConfusion (congrArg RawTerm.headGenerator typeEq)

end FX1Poly.Typed
