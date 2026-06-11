import FX1Poly.Typed.KernelBinaryFundamental
import FX1Poly.Typed.TypedLambdaDerivations
import FX1Poly.Core.RawTermStrengthen

/-! # FX1Poly/Typed/KernelAbstractionTheorem
    — ★ kernel free theorems from closed binary parametricity (OP1-K3)

The abstraction-theorem harvest of `HasTypeDescPi.binaryParametricityClosed`: concrete free
theorems for the polymorphic corpus, extracted by chaining the per-pair Π-elimination arm
(`applicationMemberPairAtBounded`) through the closed self-relation and decoding the result
through the pinned data candidates.

  * `subst0WeakenCancel` — instantiating a weakened term is the identity (the de Bruijn
    cancellation the inner-codomain computation needs).
  * `polymorphicIdentityTypeCell` — the scope-generic `Π(A : Type@0). Π(x : A). A`, with the
    `subst`-collapse and `subst0`-instantiation equations (all `rfl`: the cell is a concrete
    constructor tree whose variable children sit at concrete de Bruijn indices).
  * `flatCodeReducibleTypeAtLevelZero` / `flatCodeBinaryTypePairAtBounded` /
    `binaryMemberPairAtFlatCodeDecode` — the flat-data-code candidate intro/decode kit: the
    unary and binary relations PIN flat codes to their (same-value) data candidates, so
    membership at a flat code IS `dataTait × dataTait × Conv`.
  * ★ `kernelFreeTheoremAtFlatCode` — THE free theorem: for every CLOSED `polyFunction` typed
    at the polymorphic-identity type and every strongly-normalizing flat data code `F`, the
    instantiation `polyFunction F` maps CONVERTIBLE data-Tait members of `F` to CONVERTIBLE
    data-Tait members of `F`.  In particular (left = right) every application
    `polyFunction F a` computes to a canonical data value of `F` — polymorphic-instantiation
    canonicity, for free, with NO typing derivation for the application required.
  * `polymorphicIdentity_freeTheoremAtFlatCode` — the concrete instance at the shipped
    polymorphic-identity derivation (#955).

Honest scope: the kernel binary relation interprets the universe by its FIXED candidate
assignment (no relation-polymorphic quantification), so these are the free theorems of the
PINNED relational model; the full Reynolds-style theorems with arbitrary relations are the
`gen_param` internal-parametricity track (OP1-INT).

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-! ## De Bruijn cancellation -/

/-- **Instantiating a weakened term is the identity**: `(weaken term)[argument] = term` — the
substitution never reaches a variable of the weakened body that points at the substituted
slot.  Composition of `weaken_eq_rename`, the rename-then-subst commutation, pointwise
collapse of `singleton ∘ weaken` to the identity substitution, and `subst_identity_apply`. -/
theorem subst0WeakenCancel {scope : Nat} (term argument : RawTerm scope) :
    RawTerm.subst0 (RawTerm.weaken term) argument = term := by
  dsimp only [RawTerm.subst0]
  rw [RawTerm.weaken_eq_rename, RawTerm.rename_subst_commute]
  refine Eq.trans (RawTerm.subst_pointwise (fun position => ?_) term)
    (RawTerm.subst_identity_apply term)
  rfl

/-! ## The scope-generic polymorphic-identity type -/

/-- The scope-generic polymorphic-identity TYPE `Π(A : Type@0). Π(x : A). A`. -/
def polymorphicIdentityTypeCell (scope : Nat) (flag : UniverseFlag) : RawTerm scope :=
  piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
    (piTyCodeCell (variableCell (⟨0, Nat.succ_pos scope⟩ : Fin (scope + 1)))
      (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos scope)⟩ : Fin (scope + 2))))

/-- Closing substitution collapses on the polymorphic-identity type: the cell is a concrete
constructor tree whose two variable children sit at the de Bruijn indices BOUND by its own
binders, so substitution reproduces the same pattern at the target scope. -/
theorem subst_polymorphicIdentityTypeCell {scope targetScope : Nat}
    (substitution : RawTermSubst scope targetScope) (flag : UniverseFlag) :
    RawTerm.subst substitution (polymorphicIdentityTypeCell scope flag)
      = polymorphicIdentityTypeCell targetScope flag := rfl

/-- Instantiating the inner dependent arrow at a type code: `(Π(x : A). A)[F] = Π(x : F). F`
(the codomain occurrence arrives weakened — it lives under the inner binder). -/
theorem subst0_innerDependentArrow {scope : Nat} (typeCode : RawTerm scope) :
    RawTerm.subst0
        (piTyCodeCell (variableCell (⟨0, Nat.succ_pos scope⟩ : Fin (scope + 1)))
          (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos scope)⟩ : Fin (scope + 2))))
        typeCode
      = piTyCodeCell typeCode (RawTerm.weaken typeCode) := rfl

/-! ## The flat-data-code candidate kit -/

/-- A flat data code is a reducible TYPE at level 0 — the unary `dataFlat` pin is gate-free. -/
theorem flatCodeReducibleTypeAtLevelZero {scope : Nat} (env : Nat → Nat)
    {flatCode : RawTerm scope}
    (flatPinned : flatCode.rootGenerator.isFlatDataCode = true) :
    IsReducibleTypeAtBounded env (LevelExpr.denote LevelExpr.lzero env) flatCode :=
  ⟨dataTaitCandidate (flatCodeValuePredicate flatCode.rootGenerator),
    ReducibleTypeStepBounded.dataFlat flatPinned⟩

/-- A flat data code is BINARY-related to itself at every bound — the binary `dataFlat` pin
assigns the same-value data candidate, gate-free. -/
theorem flatCodeBinaryTypePairAtBounded {scope : Nat} (env : Nat → Nat) (bound : Nat)
    {flatCode : RawTerm scope}
    (flatPinned : flatCode.rootGenerator.isFlatDataCode = true) :
    IsBinaryReducibleTypePairAtBounded env bound flatCode flatCode :=
  ⟨binaryDataCandidate (flatCodeValuePredicate flatCode.rootGenerator),
    BinaryReducibleTypeStepBounded.dataFlat flatPinned rfl⟩

/-- **Decode a binary member pair at a flat code**: binary determinism against the `dataFlat`
pin identifies the witnessed relation with the same-value data candidate — related members
are data-Tait members that are CONVERTIBLE. -/
theorem binaryMemberPairAtFlatCodeDecode {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {flatCode leftMember rightMember : RawTerm scope}
    (flatPinned : flatCode.rootGenerator.isFlatDataCode = true)
    (memberPair : IsBinaryReducibleMemberPairAtBounded env bound flatCode flatCode
      leftMember rightMember) :
    binaryDataCandidate (flatCodeValuePredicate flatCode.rootGenerator)
      leftMember rightMember := by
  obtain ⟨relation, related, membersInRelation⟩ := memberPair
  exact (BinaryReducibleTypeAtBounded.deterministic related
    (BinaryReducibleTypeStepBounded.dataFlat flatPinned rfl) leftMember rightMember).mp
    membersInRelation

/-- **Intro a binary member pair at a flat code** from data-Tait memberships + Conv. -/
theorem binaryMemberPairAtFlatCodeIntro {scope : Nat} (env : Nat → Nat) (bound : Nat)
    {flatCode leftMember rightMember : RawTerm scope}
    (flatPinned : flatCode.rootGenerator.isFlatDataCode = true)
    (leftDataMember :
      dataTaitCandidate (flatCodeValuePredicate flatCode.rootGenerator) leftMember)
    (rightDataMember :
      dataTaitCandidate (flatCodeValuePredicate flatCode.rootGenerator) rightMember)
    (membersConvertible : Conv leftMember rightMember) :
    IsBinaryReducibleMemberPairAtBounded env bound flatCode flatCode
      leftMember rightMember :=
  ⟨binaryDataCandidate (flatCodeValuePredicate flatCode.rootGenerator),
    BinaryReducibleTypeStepBounded.dataFlat flatPinned rfl,
    leftDataMember, rightDataMember, membersConvertible⟩

/-- A flat-code data-Tait member is a UNARY bounded member of the flat code at any bound. -/
theorem flatCodeUnaryMemberAtBounded {scope : Nat} (env : Nat → Nat) (bound : Nat)
    {flatCode member : RawTerm scope}
    (flatPinned : flatCode.rootGenerator.isFlatDataCode = true)
    (dataMember : dataTaitCandidate (flatCodeValuePredicate flatCode.rootGenerator) member) :
    IsReducibleMemberAtBounded env bound flatCode member :=
  ⟨dataTaitCandidate (flatCodeValuePredicate flatCode.rootGenerator),
    ReducibleTypeStepBounded.dataFlat flatPinned, dataMember⟩

/-! ## ★ The kernel free theorem at flat data codes -/

/-- ★★ **THE kernel free theorem (the abstraction theorem at the polymorphic-identity
type).**  Every CLOSED term typed at `Π(A : Type@0). Π(x : A). A`, instantiated at any
strongly-normalizing flat data code `F`, maps CONVERTIBLE data-Tait members of `F` to
CONVERTIBLE data-Tait members of `F` — at a budget-derived bound, under every `+1`-closing
substitution.  Extraction: the closed binary self-relation, cumulated one level so the
universe argument's gate is free; the universe-membership intro admits `(F, F)` through the
binary and unary `dataFlat` pins; two chained `applicationMemberPairAtBounded` steps walk the
two Π layers (the inner codomain computes through `subst0_innerDependentArrow` and the
weakening cancellation); the final member pair at `(F, F)` decodes through the binary
`dataFlat` pin.  Setting `leftArgument = rightArgument` yields polymorphic-instantiation
CANONICITY: `polyFunction F a` is a data-Tait member of `F` — with no typing derivation for
the application ever constructed. -/
theorem kernelFreeTheoremAtFlatCode {profile : PolyProfile} (flag : UniverseFlag)
    {polyFunction : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty polyFunction
      (polymorphicIdentityTypeCell 0 flag))
    (env : Nat → Nat) :
    ∃ bound : Nat, ∀ {targetScope : Nat}
      (closingSubstitution : RawTermSubst 0 (targetScope + 1))
      (flatCode leftArgument rightArgument : RawTerm (targetScope + 1)),
      flatCode.rootGenerator.isFlatDataCode = true →
      IsStronglyNormalizing flatCode →
      dataTaitCandidate (flatCodeValuePredicate flatCode.rootGenerator) leftArgument →
      dataTaitCandidate (flatCodeValuePredicate flatCode.rootGenerator) rightArgument →
      Conv leftArgument rightArgument →
      binaryDataCandidate (flatCodeValuePredicate flatCode.rootGenerator)
        (appCell (appCell (RawTerm.subst closingSubstitution polyFunction) flatCode)
          leftArgument)
        (appCell (appCell (RawTerm.subst closingSubstitution polyFunction) flatCode)
          rightArgument) := by
  obtain ⟨boundZero, memberAt⟩ := HasTypeDescPi.binaryParametricityClosed env typed
  refine ⟨boundZero + 1, fun {targetScope} closingSubstitution flatCode
    leftArgument rightArgument flatPinned flatCodeSN leftDataMember rightDataMember
    argumentsConvertible => ?_⟩
  have functionPair := isBinaryReducibleMemberPair_cumulative
    (memberAt closingSubstitution closingSubstitution) (Nat.le_succ boundZero)
  have universeGate : LevelExpr.denote LevelExpr.lzero env < boundZero + 1 :=
    Nat.succ_pos boundZero
  have universeArgumentPair := binaryUniverseMembershipIntroAtBounded env LevelExpr.lzero flag
    (boundZero + 1) universeGate flatCodeSN flatCodeSN
    (flatCodeBinaryTypePairAtBounded env (LevelExpr.denote LevelExpr.lzero env) flatPinned)
  have universeArgumentUnary := universeMembershipIntroAtBounded env LevelExpr.lzero flag
    (boundZero + 1) flatCode universeGate flatCodeSN
    (flatCodeReducibleTypeAtLevelZero env flatPinned)
  have firstApplication : IsBinaryReducibleMemberPairAtBounded env (boundZero + 1)
      (piTyCodeCell flatCode (RawTerm.weaken flatCode))
      (piTyCodeCell flatCode (RawTerm.weaken flatCode))
      (appCell (RawTerm.subst closingSubstitution polyFunction) flatCode)
      (appCell (RawTerm.subst closingSubstitution polyFunction) flatCode) :=
    applicationMemberPairAtBounded env (boundZero + 1)
      functionPair universeArgumentPair universeArgumentUnary universeArgumentUnary
  have secondApplication := applicationMemberPairAtBounded env (boundZero + 1)
    firstApplication
    (binaryMemberPairAtFlatCodeIntro env (boundZero + 1) flatPinned
      leftDataMember rightDataMember argumentsConvertible)
    (flatCodeUnaryMemberAtBounded env (boundZero + 1) flatPinned leftDataMember)
    (flatCodeUnaryMemberAtBounded env (boundZero + 1) flatPinned rightDataMember)
  rw [subst0WeakenCancel, subst0WeakenCancel] at secondApplication
  exact binaryMemberPairAtFlatCodeDecode flatPinned secondApplication

/-- The free theorem instantiated at the SHIPPED polymorphic identity
`λ(A : Type@0). λ(x : A). x` — the concrete non-vacuous witness: the polymorphic identity
respects convertibility and preserves data-membership at every flat data code. -/
theorem polymorphicIdentity_freeTheoremAtFlatCode {profile : PolyProfile}
    (flag : UniverseFlag) (env : Nat → Nat) :
    ∃ bound : Nat, ∀ {targetScope : Nat}
      (closingSubstitution : RawTermSubst 0 (targetScope + 1))
      (flatCode leftArgument rightArgument : RawTerm (targetScope + 1)),
      flatCode.rootGenerator.isFlatDataCode = true →
      IsStronglyNormalizing flatCode →
      dataTaitCandidate (flatCodeValuePredicate flatCode.rootGenerator) leftArgument →
      dataTaitCandidate (flatCodeValuePredicate flatCode.rootGenerator) rightArgument →
      Conv leftArgument rightArgument →
      binaryDataCandidate (flatCodeValuePredicate flatCode.rootGenerator)
        (appCell (appCell
          (RawTerm.subst closingSubstitution
            (lamCell (universeCodeCell LevelExpr.lzero flag)
              (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
                (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))))
          flatCode) leftArgument)
        (appCell (appCell
          (RawTerm.subst closingSubstitution
            (lamCell (universeCodeCell LevelExpr.lzero flag)
              (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
                (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))))
          flatCode) rightArgument) :=
  kernelFreeTheoremAtFlatCode flag
    (polymorphicIdentity_hasTypeDescPi (profile := profile) flag) env

/-- ★ **Polymorphic-instantiation canonicity** (the diagonal projection of the free theorem):
for every CLOSED term at the polymorphic-identity type, every SN flat data code `F`, and every
data-Tait member `a` of `F`, the application `polyFunction F a` is itself a data-Tait member
of `F` — it computes to a canonical data VALUE — with no typing derivation for the
application required.  Parametricity delivers canonicity-of-instantiation for free. -/
theorem polymorphicInstantiationCanonicityAtFlatCode {profile : PolyProfile}
    (flag : UniverseFlag) {polyFunction : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty polyFunction
      (polymorphicIdentityTypeCell 0 flag))
    (env : Nat → Nat) :
    ∃ bound : Nat, ∀ {targetScope : Nat}
      (closingSubstitution : RawTermSubst 0 (targetScope + 1))
      (flatCode argument : RawTerm (targetScope + 1)),
      flatCode.rootGenerator.isFlatDataCode = true →
      IsStronglyNormalizing flatCode →
      dataTaitCandidate (flatCodeValuePredicate flatCode.rootGenerator) argument →
      dataTaitCandidate (flatCodeValuePredicate flatCode.rootGenerator)
        (appCell (appCell (RawTerm.subst closingSubstitution polyFunction) flatCode)
          argument) := by
  obtain ⟨bound, freeTheorem⟩ := kernelFreeTheoremAtFlatCode flag typed env
  exact ⟨bound, fun {targetScope} closingSubstitution flatCode argument flatPinned
    flatCodeSN dataMember =>
    (freeTheorem closingSubstitution flatCode argument argument flatPinned flatCodeSN
      dataMember dataMember (Conv.refl argument)).1⟩

end FX1Poly.Typed
