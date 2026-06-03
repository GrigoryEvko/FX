import FX1Poly.Typed.HasTypeConsistency
import FX1Poly.Typed.HasTypeInversion
import FX1Poly.Typed.WfContext
import FX1Poly.Typed.ClosedNonConvertibility

/-! # FX1Poly/Typed/HasTypeClosedForms
    — the closed-typing CHARACTERIZATION completed (P10 consistency precursor, #460)

`HasTypeConsistency` established that every closed (empty-context) well-typed
subject IS a type (`closedSubjectIsType`).  This file sharpens that into the two
complementary halves of a COMPLETE characterization of closed typing on the
native pi/sigma-formation HasType core (`var` / `conv` / `universeFormation` / `piFormation` /
`sigmaFormation`):

* the SUBJECT side — `closedSubjectIsTypeFormer`: a closed well-typed subject is
  EXACTLY a universe / Π / Σ type-former CODE.  The canonical-forms lemma:
  reading off the precise syntactic shape (not just the semantic `IsType`).
* the CLASSIFIER side — `closedClassifierConvUniverseCode`: its classifier is
  convertible to a universe code.  The consistency-facing interface
  (`closedSubjectIsType` supplies a universe-code typing; `uniqueness` #469
  converts the given classifier to it).

Together they read: a closed typing judgment is exactly
`(type-former code) : (universe code, up to Conv)`.  This is the fragment's
CONSISTENCY content — there is NO closed term below the universe level (no closed
inhabitant of a data / `El`-level type).  It is the precursor to the
starred ★ #460 (`HasType .empty t Empty → False`), which additionally needs an
`Empty` type-former to instantiate: with `gen_empty` and its `El`,
`closedClassifierConvUniverseCode` refutes a closed `El Empty` inhabitant directly
— `El Empty` is not a universe code, so the `Conv` clashes by normal-form
rigidity.

Fragment-specific scope: with term-introduction arms (λ / pair / data
constructors), the SUBJECT side gains canonical-value disjuncts (closed terms
become "type-former OR canonical value").  On the native pi/sigma-formation HasType core the
type-former-only shape is the checkable truth, mirroring `closedSubjectIsType`'s
honesty note.

## Zero-axiom verification

`closedSubjectIsTypeFormer` is an `rcases` on the 4-way shape classification
`subjectIsVariableOrTypeFormerCode` with the `var` disjunct killed by a
`Fin 0` refutation (`Nat.not_lt_zero` on `index.isLt`, NOT `Fin.elim0` — that
routes through the OfNat / casesOn propext trap, see the Fin-cases-axiom lesson).
`closedClassifierConvUniverseCode` composes `closedSubjectIsType` with
`HasType.uniqueness` at the trivially-well-formed empty context
(`WfContext.emptyIsWellFormed`).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Canonical forms (P10 precursor, native pi/sigma-formation HasType core): a closed well-typed
subject is EXACTLY a universe / Π / Σ type-former code.  The empty context has
no variables (`Fin 0`), so the `var` disjunct of the 4-way shape classification
`subjectIsVariableOrTypeFormerCode` is impossible; the other three disjuncts
are the type-former codes.  Sharper than `closedSubjectIsType` (which gives the
semantic `IsType`): this reads off the precise syntactic shape. -/
theorem HasType.closedSubjectIsTypeFormer {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasType profile TypingContext.empty subject classifier) :
    (∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
        subject = universeCodeCell levelExpr flag) ∨
      (∃ (domainCode : RawTerm 0) (codomainCode : RawTerm 1),
        subject = piTyCodeCell domainCode codomainCode) ∨
      (∃ (domainCode : RawTerm 0) (codomainCode : RawTerm 1),
        subject = sigmaTyCodeCell domainCode codomainCode) := by
  rcases typed.subjectIsVariableOrTypeFormerCode with
    ⟨index, _⟩ | universeShape | piShape | sigmaShape
  · exact absurd index.isLt (Nat.not_lt_zero index.val)
  · exact Or.inl universeShape
  · exact Or.inr (Or.inl piShape)
  · exact Or.inr (Or.inr sigmaShape)

/-- P10 consistency interface (native pi/sigma-formation HasType core): in the empty context, every
well-typed subject's classifier is convertible to a universe code.  Hence no
closed term lives below the universe level — the fragment's consistency content
(an `Empty`/`El`-level type, once it exists, has a non-universe-code classifier,
so by normal-form rigidity it has no closed inhabitant).  Proof: the subject is a
type (`closedSubjectIsType`), so it is typed by SOME universe code; uniqueness of
typing (#469) at the trivially-well-formed empty context converts the given
classifier to that universe code. -/
theorem HasType.closedClassifierConvUniverseCode {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasType profile TypingContext.empty subject classifier) :
    ∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
      Conv classifier (universeCodeCell levelExpr flag) := by
  obtain ⟨levelExpr, flag, subjectTyped⟩ := typed.closedSubjectIsType
  exact ⟨levelExpr, flag,
    HasType.uniqueness (WfContext.emptyIsWellFormed (profile := profile))
      typed subjectTyped⟩

/-- **The concrete P10 consistency witness (non-vacuity): no closed term is typed at the identity function.**
The closed identity `λx. x` (`lamCell (variableCell 0)`) is a concrete NON-type classifier — the available
stand-in for the absent `Empty` (`gen_empty` is not in the generator table).  Were a closed term typed at it,
`closedClassifierConvUniverseCode` would make its classifier convertible to a universe code; but
`closedUniverseCode_not_conv_identity` refutes any conversion between a closed universe code and the identity
(distinct normal-form heads `gen_universeCode` / `gen_lam`).  This turns the consistency INTERFACE
(`closedClassifierConvUniverseCode`) into a concrete `→ False` — the first witness that the characterization is
non-vacuous, and the shape the starred ★ #460 takes once an `Empty` former exists (instantiate at `El Empty`
instead of the identity). -/
theorem HasType.noClosedTermAtIdentityClassifier {profile : PolyProfile}
    {subject : RawTerm 0}
    (typed : HasType profile TypingContext.empty subject
      (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))) :
    False := by
  obtain ⟨levelExpr, flag, classifierConv⟩ := typed.closedClassifierConvUniverseCode
  obtain ⟨commonTerm, identityReducesToCommon, universeReducesToCommon⟩ := classifierConv
  exact closedUniverseCode_not_conv_identity levelExpr flag
    ⟨commonTerm, universeReducesToCommon, identityReducesToCommon⟩

end FX1Poly.Typed
