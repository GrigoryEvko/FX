import FX1Poly.Typed.Dimensions.Parametricity.KernelBinaryFundamental
import FX1Poly.Typed.Ledger.Bridge.BridgeRelationalScone

/-! # type-9 — internal parametricity of the universe: the relational universe

The TYPE-axis rung after definitional univalence (`type-7`) and SIP (`type-8`).  Reynolds' reading of the
universe (Bernardy-Coquand-Moulin ICFP 2015, Cavallo-Harper LICS 2020): `Type` is interpreted by RELATIONS.
This module makes that interpretation an internal object of the shipped binary-parametricity model and
internalizes it through the live bridge former — **without adding any new generator**.

## What is genuinely new here (and what is deliberately NOT claimed)

The shipped binary model (`KernelBinaryParametricity`) is a CANONICAL-candidate logical relation: the
candidate relating a type pair is determined by the pair's structure (the `dataFlat` arm pins data codes to
the same-value candidate, `neutral` pins to the SN-product, `piType` to the relational arrow, `universeCode`
to the universe predicate).  It already proves the binary fundamental theorem
(`HasTypeDescPi.binaryFundamentalConjoinedAtBounded`) and the closed corollary
(`HasTypeDescPi.binaryParametricityClosed`).  Re-stating those would be re-citation.

What did NOT yet exist, and is constructed below:

  * **The relational universe as an object** (`IsRelationalUniverseElement`) and the theorem that the binary
    universe candidate IS exactly "the two codes are SN and related by some admissible relation"
    (`binaryUniverse_isTypeOfRelations`) — Reynolds' "`Type` is the type of relations" as an internal `↔`.
  * **The relational universe is reflexive on data types** (`relationalUniverseElement_reflexiveAtFlatData`)
    — every flat data type, paired with itself, is a relational-universe element (the reflexive graph), built
    constructively through the `dataFlat` arm.
  * **The identity-extension lemma** (`binaryDataCandidate_diagonalIsUnary`,
    `binaryEmptyCandidate_diagonalIsUnary`) — on the DIAGONAL, the relational (binary) interpretation of a
    type collapses to its ordinary (unary) membership.  This is the bridge from parametricity to univalence
    (the Reynolds identity-extension underlying SIP / `mode-19`'s `identity_is_relational_at_Eq` and `type-7`
    def-univalence): relational sameness restricted to the diagonal is ordinary sameness.
  * **Internalization through `Bridge Type A B`** (`bridgeOverUniverse_isRelationalUniverseElement`) — the
    live `gen_bridgeCode` former at the UNIVERSE carrier, fed the universe candidate as its carrier relation,
    yields a bridge type whose every inhabitant IS a relational-universe element: an inhabitant of
    `Bridge Type A B` is evidence that `A` and `B` are related types.  The relational universe internalized
    with no new generator, no syntactic `Gel`.

DEFERRED (named honestly, NOT behind any `:= true`/`:= false` flag):

  * **Reynolds at an ARBITRARY relation** — quantifying a type variable over an arbitrary admissible relation
    (not the canonical reducibility candidate) needs an env-of-candidates model (Bernardy-Coquand-Moulin /
    Cavallo-Harper), i.e. re-proving the fundamental theorem with relation-valued environments.  The canonical
    model here does not thread an arbitrary relation through a type variable.
  * **Extracting the abstraction theorem's APPLICATION content** (related arguments map to related results at
    a polymorphic function) from the closed corollary needs an inversion lemma for the binary relation at a Π
    type; not attempted here.
  * The transpension route (`gen_transpension @ affine` recovering `Gel`, the `TRANSP-PARAM-RETIRE` program)
    is the architecture's intended home for the syntactic relational universe; it is blocked on the
    transpension former.

## Zero-axiom verification

Every theorem below is constructive / `rfl`-rewriting over the shipped relation; no `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTypedRelationalUniverse.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core
open FX1Poly.Universe
open StepStar

/-- A **relational-universe element** at `levelExpr`: the two type codes are both strongly normalizing and
related as types by some admissible binary candidate.  This is the internal reading of "`Type` is the type of
relations" — an inhabitant is a pair of types together with (the existence of) a relation between them. -/
def IsRelationalUniverseElement {scope : Nat} (env : Nat → Nat) (levelExpr : LevelExpr)
    (leftCode rightCode : RawTerm scope) : Prop :=
  IsStronglyNormalizing leftCode ∧ IsStronglyNormalizing rightCode ∧
    IsBinaryReducibleTypePairAtBounded env (LevelExpr.denote levelExpr env) leftCode rightCode

/-- ★ **The universe IS the type of relations.**  Below a dominating bound, the binary universe candidate at
`Type@levelExpr` holds of a pair of codes exactly when they form a relational-universe element — Reynolds'
relational interpretation of the universe, internalized as an `↔`. -/
theorem binaryUniverse_isTypeOfRelations {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (levelExpr : LevelExpr) (belowBound : LevelExpr.denote levelExpr env < bound)
    (leftCode rightCode : RawTerm scope) :
    binaryUniverseDenotePredicate env (binaryDenoteBelowFamilyBounded env bound) levelExpr
        leftCode rightCode
      ↔ IsRelationalUniverseElement env levelExpr leftCode rightCode := by
  have funcEq := binaryDenoteBelowFamilyBounded_eq_reducible (scope := scope) env bound
    (LevelExpr.denote levelExpr env) belowBound
  unfold binaryUniverseDenotePredicate IsRelationalUniverseElement IsBinaryReducibleTypePairAtBounded
  rw [funcEq]

/-- ★ **The relational universe is reflexive on data types.**  Every flat data type code, paired with itself,
is a relational-universe element: the witnessing relation is the same-value candidate, built constructively
through the `dataFlat` arm (no inversion).  This is the reflexive-graph law — the diagonal of the relational
universe is total on data types. -/
theorem relationalUniverseElement_reflexiveAtFlatData {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (typeCode : RawTerm scope)
    (flatPinned : typeCode.rootGenerator.isFlatDataCode = true) :
    IsBinaryReducibleTypePairAtBounded env bound typeCode typeCode :=
  ⟨binaryDataCandidate (flatCodeValuePredicate typeCode.rootGenerator),
    BinaryReducibleTypeStepBounded.dataFlat flatPinned rfl⟩

/-- ★ **Identity extension at data codes.**  On the DIAGONAL, the binary (relational) data candidate collapses
to the unary (membership) data candidate: a term is related to ITSELF exactly when it is a data-Tait member
(convertibility to itself is reflexive).  The Reynolds identity-extension lemma — relational sameness
restricted to the diagonal is ordinary sameness, the parametricity-to-univalence bridge. -/
theorem binaryDataCandidate_diagonalIsUnary {scope : Nat} (isValue : RawTerm scope → Prop)
    (term : RawTerm scope) :
    binaryDataCandidate isValue term term ↔ dataTaitCandidate isValue term := by
  unfold binaryDataCandidate
  constructor
  · intro related
    exact related.1
  · intro member
    exact ⟨member, member, Conv.refl term⟩

/-- **Identity extension at the empty code.**  The diagonal of the binary empty candidate is the unary empty
candidate — the consistency core's relational interpretation collapses to its membership on the diagonal. -/
theorem binaryEmptyCandidate_diagonalIsUnary {scope : Nat} (term : RawTerm scope) :
    binaryEmptyCandidate term term ↔ emptyTaitCandidate term := by
  unfold binaryEmptyCandidate
  constructor
  · intro related
    exact related.1
  · intro member
    exact ⟨member, member⟩

/-- ★★ **The relational universe internalized — `Bridge Type A B` is a relation.**  Feed the live bridge
relational scone (`gen_bridgeCode`, no new generator) the binary universe candidate as its carrier relation:
every inhabitant of the bridge type over the universe at endpoints `A`, `B` extracts to a relational-universe
element — an inhabitant of `Bridge Type A B` IS evidence that `A` and `B` are related types.  This is the
syntactic realization of the relational universe, internal to the shipped kernel. -/
theorem bridgeOverUniverse_isRelationalUniverseElement {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (levelExpr : LevelExpr) (belowBound : LevelExpr.denote levelExpr env < bound)
    (leftCode rightCode bridgeProof : RawTerm scope)
    (member : bridgeRelationalCandidate
        (binaryUniverseDenotePredicate env (binaryDenoteBelowFamilyBounded env bound) levelExpr)
        leftCode rightCode bridgeProof) :
    IsRelationalUniverseElement env levelExpr leftCode rightCode :=
  (binaryUniverse_isTypeOfRelations env bound levelExpr belowBound leftCode rightCode).mp
    (bridgeRelationalCandidate_extractsRelation member)

end FX1Poly.Typed
