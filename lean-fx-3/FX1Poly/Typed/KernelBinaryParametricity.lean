import FX1Poly.Typed.DenoteKeyedBoundedReducibility
import FX1Poly.Typed.DenoteKeyedBoundedReducibleEnv
import FX1Poly.Typed.CellConstructors
import FX1Poly.Core.RawConfluence
import FX1Poly.Core.PairCanonicalFormsCandidate

/-! # FX1Poly/Typed/KernelBinaryParametricity
    — ★ the KERNEL binary parametricity relation: pair-indexed stratified reducibility (OP1-K1)

The OP1 arc reaches the kernel: a BINARY logical relation over `RawTerm`, mirroring the shipped
unary stratified model (`ReducibleTypeStepBounded`) cell for cell — the substrate the kernel
binary fundamental theorem (OP1-K2) and the abstraction theorem (OP1-K3) build on.  Where the
unary relation assigns each type code a CANDIDATE (`RawTerm scope → Prop`), the binary relation
assigns each PAIR of type codes a BINARY candidate (`RawTerm scope → RawTerm scope → Prop`):

  * `BinaryCandidate` / `BinaryPointwiseIff` — the candidate vocabulary.
  * `binaryUniverseDenotePredicate` — two members of `Type@e` are related when both are SN and
    the pair is itself binary-related AS TYPES one level down (the stratified universe arm).
  * `binaryEmptyCandidate` — the product of two empty Tait candidates (member-free on closed
    terms, as in the unary consistency story).
  * `binaryDataCandidate` — ★ the SAME-VALUE refinement: two data members are related when both
    are data-Tait members AND convertible — strictly finer than the SN-product (see the teeth
    theorems below).  This is where kernel free theorems get their content.
  * ★ `BinaryReducibleTypeStepBounded` — the pair-indexed bound-gated step functor (8 arms:
    one-sided WHNF expansion left/right, neutral pair, the genuinely-binary `piType`
    (map-related-to-related over a RELATED-argument-indexed codomain family), the same-payload
    `universeCode` pair gated below the bound, the pinned `dataEmpty`/`dataFlat` pairs, and
    `BinaryPointwiseIff` congruence closure).
  * `binaryDenoteBelowFamilyBounded` / `BinaryReducibleTypeAtBounded` /
    `IsBinaryReducibleTypePairAtBounded` — the structural below-family (same propext-clean
    non-well-founded recursion shape as the unary), the level-indexed relation, the
    inhabitation wrapper.
  * `binaryDenoteBelowFamilyBounded_eq_reducible` — coherence (mirror).
  * ★ `binaryStepBounded_cumulative` — cumulativity is FREE in the gated binary model, same
    candidate, exactly as in the unary (`ofPointwiseIff` reconciliation at the universe arm,
    `funext`-free).
  * The K1 leaf/universe/formation ARMS as named theorems — `binaryUniverseFormationArm`,
    `binaryEmptyFormationArm`, `binaryFlatDataFormationArm`, `binaryPiFormationArm` — the
    constructor-level arms the OP1-K2 fundamental theorem's leaf/universe/formation cases
    consume, plus their diagonal `IsBinaryReducibleTypePairAtBounded` instances.
  * ★ TEETH (the relation is a STRICT refinement of the unary square): the universe candidate
    is inhabited (`binaryUniverseCandidate_relatesEmptyCodes`), `binaryDataCandidate` relates a
    value to itself (`binaryPairCandidate_relatesSelf`) but REFUSES two distinct normal pair
    values (`binaryPairCandidate_discriminates`) even though BOTH are unary data-Tait members
    (`binaryDataCandidate_strictlyRefinesSquare`) — the same-value conjunct does real work.

Honest scope (the K1/K2 split): this file is the RELATION and its formation-leaf arms.  The
env-threaded var/conv arms, the piIntro/piElim member arms, and the binary fundamental theorem
assembly need the binary substitution-pair environment and travel with OP1-K2.  Whether binary
relatedness PROJECTS to unary reducibility is deliberately not claimed: at `piType` the binary
data is incomparable to the unary on the diagonal-free side (projection at function types is
equivalent to self-relatedness, i.e. the fundamental theorem itself).

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-! ## The binary candidate vocabulary -/

/-- A binary candidate: a relation between two terms of the same scope. -/
abbrev BinaryCandidate (scope : Nat) := RawTerm scope → RawTerm scope → Prop

/-- Pointwise logical equivalence of binary candidates (the `funext`-free congruence the
`ofPointwiseIff` arm closes under, mirroring the unary `PointwiseIff`). -/
def BinaryPointwiseIff {scope : Nat} (relationA relationB : BinaryCandidate scope) : Prop :=
  ∀ leftTerm rightTerm : RawTerm scope, relationA leftTerm rightTerm ↔ relationB leftTerm rightTerm

/-- **The binary universe candidate**: two members of `Type@levelExpr` are related when both are
strongly normalizing and the pair is binary-related AS TYPES at the decoded level — the
stratified (bound-keyed) binary universe arm, mirroring `universeDenotePredicate`. -/
def binaryUniverseDenotePredicate {scope : Nat} (env : Nat → Nat)
    (lowerAt : Nat → RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop)
    (levelExpr : LevelExpr) : BinaryCandidate scope :=
  fun leftCode rightCode =>
    IsStronglyNormalizing leftCode ∧ IsStronglyNormalizing rightCode ∧
      ∃ relation : BinaryCandidate scope,
        lowerAt (LevelExpr.denote levelExpr env) leftCode rightCode relation

/-- The binary empty candidate — the product of two empty Tait candidates (member-free on
closed terms: the binary consistency core inherits from the unary one). -/
def binaryEmptyCandidate {scope : Nat} : BinaryCandidate scope :=
  fun leftTerm rightTerm => emptyTaitCandidate leftTerm ∧ emptyTaitCandidate rightTerm

/-- ★ **The binary data candidate — the SAME-VALUE refinement.**  Two data members are related
when both are data-Tait members at the pinned value predicate AND they are convertible — by
confluence and value-rigidity, "they compute to the SAME value".  Strictly finer than the
product of the unary candidates (`binaryDataCandidate_strictlyRefinesSquare`). -/
def binaryDataCandidate {scope : Nat} (isValue : RawTerm scope → Prop) : BinaryCandidate scope :=
  fun leftTerm rightTerm =>
    dataTaitCandidate isValue leftTerm ∧ dataTaitCandidate isValue rightTerm
      ∧ Conv leftTerm rightTerm

/-- Related data members are convertible — the projection every kernel free theorem extracts. -/
theorem binaryDataCandidate_relatedAreConvertible {scope : Nat} {isValue : RawTerm scope → Prop}
    {leftTerm rightTerm : RawTerm scope}
    (related : binaryDataCandidate isValue leftTerm rightTerm) : Conv leftTerm rightTerm :=
  related.2.2

/-! ## ★ The pair-indexed bound-gated step functor -/

/-- ★ **The kernel binary reducibility step functor** — the pair-indexed mirror of
`ReducibleTypeStepBounded`.  A derivation relates TWO type codes with a BINARY member
candidate.  One-sided WHNF expansion replaces the unary `whnfExpand`; the `neutral` pair gets
the SN-product candidate (proof-irrelevant at neutral types, the standard parametricity
choice); `piType` is the genuinely binary relational-arrow arm (related arguments map to
related applications, over a related-argument-indexed codomain candidate family); the
`universeCode` pair carries the same payload on both sides (substitution never changes a
closed-payload universe code) and is gated `denote levelExpr env < bound` exactly as in the
unary model, so binary cumulativity is free; `dataEmpty`/`dataFlat` pin the data codes to the
binary empty/same-value candidates (the candidate-bridge edit, doubled). -/
inductive BinaryReducibleTypeStepBounded {scope : Nat} (env : Nat → Nat)
    (lowerAt : Nat → RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop)
    (bound : Nat) :
    RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop where
  | whnfExpandLeft {leftCode leftReduct rightCode : RawTerm scope}
      {relation : BinaryCandidate scope} :
      WeakHeadStep leftCode leftReduct →
      BinaryReducibleTypeStepBounded env lowerAt bound leftReduct rightCode relation →
      BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode relation
  | whnfExpandRight {leftCode rightCode rightReduct : RawTerm scope}
      {relation : BinaryCandidate scope} :
      WeakHeadStep rightCode rightReduct →
      BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightReduct relation →
      BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode relation
  | neutral {leftCode rightCode : RawTerm scope} :
      (∀ reduct : RawTerm scope, ¬ WeakHeadStep leftCode reduct) →
      (∀ reduct : RawTerm scope, ¬ WeakHeadStep rightCode reduct) →
      leftCode.rootGenerator ≠ Generator.gen_piTyCode →
      leftCode.rootGenerator ≠ Generator.gen_universeCode →
      leftCode.rootGenerator ≠ Generator.gen_emptyCode →
      leftCode.rootGenerator.isFlatDataCode = false →
      rightCode.rootGenerator ≠ Generator.gen_piTyCode →
      rightCode.rootGenerator ≠ Generator.gen_universeCode →
      rightCode.rootGenerator ≠ Generator.gen_emptyCode →
      rightCode.rootGenerator.isFlatDataCode = false →
      BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode
        (fun leftTerm rightTerm =>
          IsStronglyNormalizing leftTerm ∧ IsStronglyNormalizing rightTerm)
  | piType {leftDomain rightDomain : RawTerm scope}
      {leftCodomain rightCodomain : RawTerm (scope + 1)}
      {leftDomainCandidate rightDomainCandidate : RawTerm scope → Prop}
      {domainRelation : BinaryCandidate scope}
      (codomainRelation : RawTerm scope → RawTerm scope → BinaryCandidate scope) :
      ReducibleTypeAtBounded env bound leftDomain leftDomainCandidate →
      ReducibleTypeAtBounded env bound rightDomain rightDomainCandidate →
      BinaryReducibleTypeStepBounded env lowerAt bound leftDomain rightDomain domainRelation →
      (∀ leftArgument rightArgument : RawTerm scope,
        leftDomainCandidate leftArgument → rightDomainCandidate rightArgument →
        domainRelation leftArgument rightArgument →
        BinaryReducibleTypeStepBounded env lowerAt bound
          (RawTerm.subst0 leftCodomain leftArgument)
          (RawTerm.subst0 rightCodomain rightArgument)
          (codomainRelation leftArgument rightArgument)) →
      BinaryReducibleTypeStepBounded env lowerAt bound
        (.mkGen .gen_piTyCode () (.childCons leftDomain (.childCons leftCodomain .childNil)))
        (.mkGen .gen_piTyCode () (.childCons rightDomain (.childCons rightCodomain .childNil)))
        (fun leftFunction rightFunction =>
          IsStronglyNormalizing leftFunction ∧ IsStronglyNormalizing rightFunction ∧
            ∀ leftArgument rightArgument : RawTerm scope,
              leftDomainCandidate leftArgument → rightDomainCandidate rightArgument →
              domainRelation leftArgument rightArgument →
              codomainRelation leftArgument rightArgument
                (.mkGen .gen_app ()
                  (.childCons leftFunction (.childCons leftArgument .childNil)))
                (.mkGen .gen_app ()
                  (.childCons rightFunction (.childCons rightArgument .childNil))))
  | universeCode (levelExpr : LevelExpr) (flag : UniverseFlag)
      (belowBound : LevelExpr.denote levelExpr env < bound) :
      BinaryReducibleTypeStepBounded env lowerAt bound
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (binaryUniverseDenotePredicate env lowerAt levelExpr)
  | dataEmpty :
      BinaryReducibleTypeStepBounded env lowerAt bound
        (emptyTypeCell (scope := scope)) (emptyTypeCell (scope := scope)) binaryEmptyCandidate
  | dataFlat {leftCode rightCode : RawTerm scope}
      (flatPinned : leftCode.rootGenerator.isFlatDataCode = true)
      (headsAgree : rightCode.rootGenerator = leftCode.rootGenerator) :
      BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode
        (binaryDataCandidate (flatCodeValuePredicate leftCode.rootGenerator))
  | ofPointwiseIff {leftCode rightCode : RawTerm scope}
      {relation canonical : BinaryCandidate scope} :
      BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode relation →
      BinaryPointwiseIff relation canonical →
      BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode canonical

/-- **The structural below-family for the binary gated relation** — the SAME non-well-founded
structural-recursion shape as the unary `denoteBelowFamilyBounded` (recursive calls at the
predecessor level), inheriting its propext-clean / `Quot.sound`-free discipline. -/
def binaryDenoteBelowFamilyBounded {scope : Nat} (env : Nat → Nat) :
    Nat → Nat → RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop
  | 0, _lvl => fun _ _ _ => False
  | level + 1, lvl =>
      if lvl < level then binaryDenoteBelowFamilyBounded env level lvl
      else if lvl = level then
        BinaryReducibleTypeStepBounded env (binaryDenoteBelowFamilyBounded env level) level
      else fun _ _ _ => False

/-- **The bound-carrying binary reducibility relation**: the binary gated step functor over the
binary structural below-family at the same bound. -/
def BinaryReducibleTypeAtBounded {scope : Nat} (env : Nat → Nat) (bound : Nat) :
    RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop :=
  BinaryReducibleTypeStepBounded env (binaryDenoteBelowFamilyBounded env bound) bound

/-- **Semantically related type pair (bound-carrying)** — some binary candidate relates the two
codes as types. -/
def IsBinaryReducibleTypePairAtBounded {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (leftCode rightCode : RawTerm scope) : Prop :=
  ∃ relation : BinaryCandidate scope,
    BinaryReducibleTypeAtBounded env bound leftCode rightCode relation

/-- **Coherence (level-stability of the binary bounded below-family)** — the exact mirror of
`denoteBelowFamilyBounded_eq_reducible`: below the bound, the below-family at a level IS the
relation at that level (boundary by `rfl`). -/
theorem binaryDenoteBelowFamilyBounded_eq_reducible {scope : Nat} (env : Nat → Nat) :
    ∀ (bound lvl : Nat), lvl < bound →
      binaryDenoteBelowFamilyBounded (scope := scope) env bound lvl
        = BinaryReducibleTypeAtBounded env lvl := by
  intro bound
  induction bound with
  | zero => intro lvl hlt; exact absurd hlt (Nat.not_lt_zero lvl)
  | succ predBound ih =>
      intro lvl hlt
      show (if lvl < predBound then binaryDenoteBelowFamilyBounded env predBound lvl
            else if lvl = predBound then
              BinaryReducibleTypeStepBounded env
                (binaryDenoteBelowFamilyBounded env predBound) predBound
            else fun _ _ _ => False) = BinaryReducibleTypeAtBounded env lvl
      by_cases hbelow : lvl < predBound
      · rw [if_pos hbelow]; exact ih lvl hbelow
      · rw [if_neg hbelow]
        have heq : lvl = predBound :=
          Nat.le_antisymm (Nat.le_of_lt_succ hlt) (Nat.not_lt.mp hbelow)
        rw [if_pos heq, heq]
        rfl

/-- ★ **Binary cumulativity is FREE (step level, same candidate)** — the mirror of
`stepBounded_cumulative`.  Every arm lifts to a higher bound; the `universeCode` arm re-fires
(its gate is guaranteed by transitivity) and the two binary universe candidates are reconciled
pointwise via the coherence-derived function equality — `ofPointwiseIff`, no `funext`. -/
theorem binaryStepBounded_cumulative {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {leftCode rightCode : RawTerm scope} {relation : BinaryCandidate scope}
    (related : BinaryReducibleTypeStepBounded env
      (binaryDenoteBelowFamilyBounded env bound) bound leftCode rightCode relation) :
    ∀ higherBound : Nat, bound ≤ higherBound →
      BinaryReducibleTypeStepBounded env
        (binaryDenoteBelowFamilyBounded env higherBound) higherBound
        leftCode rightCode relation := by
  induction related with
  | whnfExpandLeft weakHeadStep _reductRelated ih =>
      intro higherBound hle
      exact BinaryReducibleTypeStepBounded.whnfExpandLeft weakHeadStep (ih higherBound hle)
  | whnfExpandRight weakHeadStep _reductRelated ih =>
      intro higherBound hle
      exact BinaryReducibleTypeStepBounded.whnfExpandRight weakHeadStep (ih higherBound hle)
  | neutral noStepLeft noStepRight notPiLeft notUniverseLeft notEmptyLeft notFlatLeft
      notPiRight notUniverseRight notEmptyRight notFlatRight =>
      intro higherBound _hle
      exact BinaryReducibleTypeStepBounded.neutral noStepLeft noStepRight
        notPiLeft notUniverseLeft notEmptyLeft notFlatLeft
        notPiRight notUniverseRight notEmptyRight notFlatRight
  | piType codomainRelation leftDomainUnary rightDomainUnary _domainRelated _codomainRelated
      ihDomain ihCodomain =>
      intro higherBound hle
      exact BinaryReducibleTypeStepBounded.piType codomainRelation
        (stepBounded_cumulative leftDomainUnary higherBound hle)
        (stepBounded_cumulative rightDomainUnary higherBound hle)
        (ihDomain higherBound hle)
        (fun leftArgument rightArgument leftGuard rightGuard argumentsRelated =>
          ihCodomain leftArgument rightArgument leftGuard rightGuard argumentsRelated
            higherBound hle)
  | universeCode levelExpr flag belowBound =>
      intro higherBound hle
      have belowHigher : LevelExpr.denote levelExpr env < higherBound :=
        Nat.lt_of_lt_of_le belowBound hle
      have lowEq := binaryDenoteBelowFamilyBounded_eq_reducible (scope := scope) env bound
        (LevelExpr.denote levelExpr env) belowBound
      have highEq := binaryDenoteBelowFamilyBounded_eq_reducible (scope := scope) env higherBound
        (LevelExpr.denote levelExpr env) belowHigher
      have funcEq : binaryDenoteBelowFamilyBounded env bound (LevelExpr.denote levelExpr env)
                  = binaryDenoteBelowFamilyBounded env higherBound
                      (LevelExpr.denote levelExpr env) :=
        lowEq.trans highEq.symm
      refine BinaryReducibleTypeStepBounded.ofPointwiseIff
        (BinaryReducibleTypeStepBounded.universeCode levelExpr flag belowHigher)
        (fun leftTerm rightTerm => ?_)
      show (IsStronglyNormalizing leftTerm ∧ IsStronglyNormalizing rightTerm ∧
              ∃ relation : BinaryCandidate scope,
                binaryDenoteBelowFamilyBounded env higherBound
                  (LevelExpr.denote levelExpr env) leftTerm rightTerm relation)
         ↔ (IsStronglyNormalizing leftTerm ∧ IsStronglyNormalizing rightTerm ∧
              ∃ relation : BinaryCandidate scope,
                binaryDenoteBelowFamilyBounded env bound
                  (LevelExpr.denote levelExpr env) leftTerm rightTerm relation)
      rw [funcEq]
  | dataEmpty =>
      intro higherBound _hle
      exact BinaryReducibleTypeStepBounded.dataEmpty
  | dataFlat flatPinned headsAgree =>
      intro higherBound _hle
      exact BinaryReducibleTypeStepBounded.dataFlat flatPinned headsAgree
  | ofPointwiseIff _related pointwise ih =>
      intro higherBound hle
      exact BinaryReducibleTypeStepBounded.ofPointwiseIff (ih higherBound hle) pointwise

/-- Cumulativity at the wrapper level: a related type pair stays related (same candidate is
witnessed) at every higher bound. -/
theorem isBinaryReducibleTypePair_cumulative {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {leftCode rightCode : RawTerm scope}
    (relatedPair : IsBinaryReducibleTypePairAtBounded env bound leftCode rightCode)
    {higherBound : Nat} (boundLe : bound ≤ higherBound) :
    IsBinaryReducibleTypePairAtBounded env higherBound leftCode rightCode :=
  match relatedPair with
  | ⟨relation, related⟩ => ⟨relation, binaryStepBounded_cumulative related higherBound boundLe⟩

/-! ## The K1 formation arms (the constructor-level arms OP1-K2's leaf cases consume) -/

/-- **The universe FORMATION arm**: `Type@levelExpr` paired with itself is binary-reducible
below any bound dominating its denotation, at the binary universe candidate. -/
theorem binaryUniverseFormationArm {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (belowBound : LevelExpr.denote levelExpr env < bound) :
    BinaryReducibleTypeAtBounded env bound
      (universeCodeCell levelExpr flag : RawTerm scope) (universeCodeCell levelExpr flag)
      (binaryUniverseDenotePredicate env (binaryDenoteBelowFamilyBounded env bound) levelExpr) :=
  BinaryReducibleTypeStepBounded.universeCode levelExpr flag belowBound

/-- **The empty-type FORMATION arm**: `Empty` paired with itself is binary-reducible at every
bound, at the binary empty candidate. -/
theorem binaryEmptyFormationArm {scope : Nat} (env : Nat → Nat) (bound : Nat) :
    BinaryReducibleTypeAtBounded env bound
      (emptyTypeCell (scope := scope)) (emptyTypeCell (scope := scope)) binaryEmptyCandidate :=
  BinaryReducibleTypeStepBounded.dataEmpty

/-- **The flat-data FORMATION arm**: any flat-data-rooted code paired with a same-headed code is
binary-reducible at the SAME-VALUE binary data candidate. -/
theorem binaryFlatDataFormationArm {scope : Nat} (env : Nat → Nat) (bound : Nat)
    {leftCode rightCode : RawTerm scope}
    (flatPinned : leftCode.rootGenerator.isFlatDataCode = true)
    (headsAgree : rightCode.rootGenerator = leftCode.rootGenerator) :
    BinaryReducibleTypeAtBounded env bound leftCode rightCode
      (binaryDataCandidate (flatCodeValuePredicate leftCode.rootGenerator)) :=
  BinaryReducibleTypeStepBounded.dataFlat flatPinned headsAgree

/-- **The Π FORMATION arm**: related domains plus a related-argument-indexed family of related
codomains form a related Π pair at the relational-arrow candidate — the genuinely binary
formation step the OP1-K2 Π-formation case consumes. -/
theorem binaryPiFormationArm {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {leftDomain rightDomain : RawTerm scope} {leftCodomain rightCodomain : RawTerm (scope + 1)}
    {leftDomainCandidate rightDomainCandidate : RawTerm scope → Prop}
    {domainRelation : BinaryCandidate scope}
    (codomainRelation : RawTerm scope → RawTerm scope → BinaryCandidate scope)
    (leftDomainUnary : ReducibleTypeAtBounded env bound leftDomain leftDomainCandidate)
    (rightDomainUnary : ReducibleTypeAtBounded env bound rightDomain rightDomainCandidate)
    (domainsRelated : BinaryReducibleTypeAtBounded env bound leftDomain rightDomain
      domainRelation)
    (codomainsRelated : ∀ leftArgument rightArgument : RawTerm scope,
      leftDomainCandidate leftArgument → rightDomainCandidate rightArgument →
      domainRelation leftArgument rightArgument →
      BinaryReducibleTypeAtBounded env bound
        (RawTerm.subst0 leftCodomain leftArgument)
        (RawTerm.subst0 rightCodomain rightArgument)
        (codomainRelation leftArgument rightArgument)) :
    BinaryReducibleTypeAtBounded env bound
      (.mkGen .gen_piTyCode () (.childCons leftDomain (.childCons leftCodomain .childNil)))
      (.mkGen .gen_piTyCode () (.childCons rightDomain (.childCons rightCodomain .childNil)))
      (fun leftFunction rightFunction =>
        IsStronglyNormalizing leftFunction ∧ IsStronglyNormalizing rightFunction ∧
          ∀ leftArgument rightArgument : RawTerm scope,
            leftDomainCandidate leftArgument → rightDomainCandidate rightArgument →
            domainRelation leftArgument rightArgument →
            codomainRelation leftArgument rightArgument
              (.mkGen .gen_app ()
                (.childCons leftFunction (.childCons leftArgument .childNil)))
              (.mkGen .gen_app ()
                (.childCons rightFunction (.childCons rightArgument .childNil)))) :=
  BinaryReducibleTypeStepBounded.piType codomainRelation leftDomainUnary rightDomainUnary
    domainsRelated codomainsRelated

/-- `Type@levelExpr` is a self-related TYPE PAIR below any dominating bound. -/
theorem universeCode_isBinaryReducibleSelfPair {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (belowBound : LevelExpr.denote levelExpr env < bound) :
    IsBinaryReducibleTypePairAtBounded env bound
      (universeCodeCell levelExpr flag : RawTerm scope) (universeCodeCell levelExpr flag) :=
  ⟨_, binaryUniverseFormationArm env bound levelExpr flag belowBound⟩

/-- `Empty` is a self-related TYPE PAIR at every bound. -/
theorem emptyTypeCell_isBinaryReducibleSelfPair {scope : Nat} (env : Nat → Nat) (bound : Nat) :
    IsBinaryReducibleTypePairAtBounded env bound
      (emptyTypeCell (scope := scope)) (emptyTypeCell (scope := scope)) :=
  ⟨_, binaryEmptyFormationArm env bound⟩

/-! ## Non-degeneracy: the binary universe candidate is inhabited -/

/-- A step-normal form is strongly normalizing (no successor to recurse into). -/
theorem IsStronglyNormalizing.ofIsStepNormalForm {scope : Nat} {term : RawTerm scope}
    (termIsNormal : RawTerm.isStepNormalForm term) : IsStronglyNormalizing term :=
  Acc.intro term (fun reduct step =>
    (RawTerm.isStepNormalForm_blocks_step termIsNormal reduct step).elim)

/-- **The binary universe candidate at `Type@0` is inhabited**: the pair `(Empty, Empty)` is a
related member — both sides SN, and the pair is binary-related as types at level 0 through the
below-family boundary (the `dataEmpty` arm fires at every bound, including 0). -/
theorem binaryUniverseCandidate_relatesEmptyCodes (env : Nat → Nat) :
    binaryUniverseDenotePredicate env (binaryDenoteBelowFamilyBounded env 1) LevelExpr.lzero
      (emptyTypeCell (scope := 0)) (emptyTypeCell (scope := 0)) := by
  refine ⟨IsStronglyNormalizing.ofIsStepNormalForm rfl,
    IsStronglyNormalizing.ofIsStepNormalForm rfl, ⟨binaryEmptyCandidate, ?_⟩⟩
  show BinaryReducibleTypeStepBounded env (binaryDenoteBelowFamilyBounded env 0) 0
    (emptyTypeCell (scope := 0)) (emptyTypeCell (scope := 0)) binaryEmptyCandidate
  exact BinaryReducibleTypeStepBounded.dataEmpty

/-! ## The binary member pair, the binary environment, and the leaf (var) arm -/

/-- **A binary-reducible member pair**: two terms related at a binary-related type pair — the
binary twin of `IsReducibleMemberAtBounded`, the shape the OP1-K2 fundamental theorem's
conclusion quantifies over. -/
def IsBinaryReducibleMemberPairAtBounded {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (leftType rightType leftMember rightMember : RawTerm scope) : Prop :=
  ∃ relation : BinaryCandidate scope,
    BinaryReducibleTypeAtBounded env bound leftType rightType relation
      ∧ relation leftMember rightMember

/-- Member-pair cumulativity: the type-pair relation lifts with the SAME candidate
(`binaryStepBounded_cumulative`), so the membership witness carries over unchanged. -/
theorem isBinaryReducibleMemberPair_cumulative {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {leftType rightType leftMember rightMember : RawTerm scope}
    (memberPair : IsBinaryReducibleMemberPairAtBounded env bound
      leftType rightType leftMember rightMember)
    {higherBound : Nat} (boundLe : bound ≤ higherBound) :
    IsBinaryReducibleMemberPairAtBounded env higherBound
      leftType rightType leftMember rightMember :=
  match memberPair with
  | ⟨relation, typePairRelated, membersRelated⟩ =>
      ⟨relation, binaryStepBounded_cumulative typePairRelated higherBound boundLe, membersRelated⟩

/-- **The binary-related closing environment**: a PAIR of closing substitutions whose images at
every variable are a binary-reducible member pair at the variable's (substituted) type on each
side — the binary twin of `ReducibleEnvAtBounded` and the environment the OP1-K2 fundamental
theorem threads. -/
def BinaryReducibleEnvAtBounded {profile : PolyProfile} {scope targetScope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    (leftSubstitution rightSubstitution : RawTermSubst scope targetScope) : Prop :=
  ∀ index : Fin scope,
    IsBinaryReducibleMemberPairAtBounded env bound
      (RawTerm.subst leftSubstitution (context.lookup index))
      (RawTerm.subst rightSubstitution (context.lookup index))
      (leftSubstitution index) (rightSubstitution index)

/-- **The leaf (var) arm**: a binary-related environment sends each variable to a
binary-reducible member pair of its looked-up type's two closures — the lookup IS the arm. -/
theorem BinaryReducibleEnvAtBounded.lookupRelated {profile : PolyProfile}
    {scope targetScope : Nat} {env : Nat → Nat} {bound : Nat}
    {context : TypingContext profile scope}
    {leftSubstitution rightSubstitution : RawTermSubst scope targetScope}
    (envRelated : BinaryReducibleEnvAtBounded env bound context
      leftSubstitution rightSubstitution)
    (index : Fin scope) :
    IsBinaryReducibleMemberPairAtBounded env bound
      (RawTerm.subst leftSubstitution (context.lookup index))
      (RawTerm.subst rightSubstitution (context.lookup index))
      (leftSubstitution index) (rightSubstitution index) :=
  envRelated index

/-- Every substitution PAIR is binary-related at the empty context (vacuous: `Fin 0` is
uninhabited) — the base environment turning the OP1-K2 fundamental theorem into the closed
abstraction theorem. -/
theorem BinaryReducibleEnvAtBounded.empty {profile : PolyProfile} {targetScope : Nat}
    {env : Nat → Nat} {bound : Nat}
    (leftSubstitution rightSubstitution : RawTermSubst 0 targetScope) :
    BinaryReducibleEnvAtBounded env bound (TypingContext.empty : TypingContext profile 0)
      leftSubstitution rightSubstitution :=
  fun index => index.elim0

/-- **The universeFormation arm in FT shape**: under ANY substitution pair, the two closures of
`Type@levelExpr` (which substitution leaves untouched — closed payload, no children) form a
binary-reducible type pair below a dominating bound. -/
theorem binaryFundamentalUniverseFormationArm {scope targetScope : Nat} (env : Nat → Nat)
    (bound : Nat) (leftSubstitution rightSubstitution : RawTermSubst scope targetScope)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (belowBound : LevelExpr.denote levelExpr env < bound) :
    BinaryReducibleTypeAtBounded env bound
      (RawTerm.subst leftSubstitution (universeCodeCell levelExpr flag))
      (RawTerm.subst rightSubstitution (universeCodeCell levelExpr flag))
      (binaryUniverseDenotePredicate env (binaryDenoteBelowFamilyBounded env bound) levelExpr) :=
  BinaryReducibleTypeStepBounded.universeCode levelExpr flag belowBound

/-! ## ★ TEETH: the same-value data candidate strictly refines the unary square -/

/-- First witness: the normal pair value `(Type@0, Type@0)`. -/
def firstWitnessPairValue : RawTerm 0 :=
  pairCell (universeCodeCell LevelExpr.lzero .standard)
    (universeCodeCell LevelExpr.lzero .standard)

/-- Second witness: the normal pair value `(Empty, Type@0)` — distinct from the first. -/
def secondWitnessPairValue : RawTerm 0 :=
  pairCell emptyTypeCell (universeCodeCell LevelExpr.lzero .standard)

/-- The first witness is a pair value (both components are concrete normal leaves). -/
theorem firstWitnessPairValue_isPairValue : isPairValue firstWitnessPairValue :=
  ⟨universeCodeCell LevelExpr.lzero .standard, universeCodeCell LevelExpr.lzero .standard,
    rfl, rfl, rfl⟩

/-- The second witness is a pair value. -/
theorem secondWitnessPairValue_isPairValue : isPairValue secondWitnessPairValue :=
  ⟨emptyTypeCell, universeCodeCell LevelExpr.lzero .standard, rfl, rfl, rfl⟩

/-- The binary data candidate relates a value to ITSELF (the diagonal is total on values). -/
theorem binaryPairCandidate_relatesSelf :
    binaryDataCandidate isPairValue firstWitnessPairValue firstWitnessPairValue :=
  ⟨dataTaitCandidate.memberOfValue
      (isPairValue_impliesStepNormalForm firstWitnessPairValue_isPairValue)
      firstWitnessPairValue_isPairValue,
   dataTaitCandidate.memberOfValue
      (isPairValue_impliesStepNormalForm firstWitnessPairValue_isPairValue)
      firstWitnessPairValue_isPairValue,
   Conv.refl firstWitnessPairValue⟩

/-- The two witnesses are distinct terms (different first components). -/
theorem witnessPairValues_distinct : firstWitnessPairValue ≠ secondWitnessPairValue := by
  decide

/-- ★ **Discrimination**: the binary data candidate REFUSES the two distinct normal pair
values — convertibility between normal forms forces equality (rigidity), which is refuted. -/
theorem binaryPairCandidate_discriminates :
    ¬ binaryDataCandidate isPairValue firstWitnessPairValue secondWitnessPairValue := by
  intro related
  have firstNormal : RawTerm.isStepNormalForm firstWitnessPairValue :=
    isPairValue_impliesStepNormalForm firstWitnessPairValue_isPairValue
  have secondNormal : RawTerm.isStepNormalForm secondWitnessPairValue :=
    isPairValue_impliesStepNormalForm secondWitnessPairValue_isPairValue
  have witnessesEqual : firstWitnessPairValue = secondWitnessPairValue :=
    Conv.eq_of_noStep
      (fun reduct step => RawTerm.isStepNormalForm_blocks_step firstNormal reduct step)
      (fun reduct step => RawTerm.isStepNormalForm_blocks_step secondNormal reduct step)
      related.2.2
  exact absurd witnessesEqual witnessPairValues_distinct

/-- ★ **Strict refinement**: BOTH witnesses are unary data-Tait members (the unary square
relates them), yet the binary candidate refuses the pair — the same-value conjunct does real
relational work beyond the product of the unary candidates. -/
theorem binaryDataCandidate_strictlyRefinesSquare :
    (dataTaitCandidate isPairValue firstWitnessPairValue
        ∧ dataTaitCandidate isPairValue secondWitnessPairValue)
      ∧ ¬ binaryDataCandidate isPairValue firstWitnessPairValue secondWitnessPairValue :=
  ⟨⟨dataTaitCandidate.memberOfValue
      (isPairValue_impliesStepNormalForm firstWitnessPairValue_isPairValue)
      firstWitnessPairValue_isPairValue,
    dataTaitCandidate.memberOfValue
      (isPairValue_impliesStepNormalForm secondWitnessPairValue_isPairValue)
      secondWitnessPairValue_isPairValue⟩,
   binaryPairCandidate_discriminates⟩

end FX1Poly.Typed
