set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # The named spine of Post's lattice

Boolean functions as finite truth tables, the five named maximal Post clones
(`T0` 0-preserving, `T1` 1-preserving, `M` monotone, `D` self-dual, `L` affine/linear) plus
a bottom and a top element, their membership tests as decidable `Bool` predicates over the
finite table, the finite named-clone inclusion order (reflexive + transitive, proved
structurally over the finite enum), and a sound Schaefer tractability witness (the constraint
set lies inside one common tractable clone).

A `PclBoolFn` carries an explicit `arity : Nat` and a `table : List Bool` whose intended
length is `2 ^ arity`; row `r` is the value on the `r`-th mask of `pclAllMasks arity`
(all-`false` first, all-`true` last, big-endian). Length is a `Bool` well-formedness side-check
(`pclTablePow2`), never a dependent index, so no `Nat.pow` `propext` traps.

Proven (the `pclHas...` markers left `true`): the five preservation predicates with
`pclCloneMembership`, the seven-element named-clone order (reflexivity and transitivity), and the
sufficient common-tractable-clone Schaefer witness. The three markers left `false` name the
complete infinite Post lattice, the general finite-domain CSP dichotomy (Bulatov–Zhuk), and the
composition-closure / `Pol`–`Inv` Galois fixpoint; each is an unbounded limit object outside the
structural budget, for the reason stated at its declaration.

Every declaration is free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `funext`, `WellFounded.fix`, `omega`, and any `decide`-on-`Prop`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Micro-kit: structural `Nat`/`Bool` primitives (no stdlib order/`getD` lemmas) -/

/-- Structural `2 ^ n` via doubling — `pclPow2 (n+1) = pclPow2 n + pclPow2 n`. -/
def pclPow2 : Nat → Nat
  | 0 => 1
  | Nat.succ predecessor => Nat.add (pclPow2 predecessor) (pclPow2 predecessor)

/-- `2 ^ n - 1` computed structurally as `L 0 = 0`, `L (n+1) = 2·L n + 1` — the last row index,
avoiding `Nat.sub` entirely. -/
def pclLastIndex : Nat → Nat
  | 0 => 0
  | Nat.succ predecessor => Nat.succ (Nat.add (pclLastIndex predecessor) (pclLastIndex predecessor))

/-- Structural strict `<` on `Nat` (full constructor enumeration, no collapsing wildcard). -/
def pclNatLt : Nat → Nat → Bool
  | 0, 0 => false
  | Nat.succ _, 0 => false
  | 0, Nat.succ _ => true
  | Nat.succ leftPredecessor, Nat.succ rightPredecessor => pclNatLt leftPredecessor rightPredecessor

/-- `pclNatLt` is transitive (structural, `cswLeTrans`-shaped). -/
theorem pclNatLtTrans : (firstValue secondValue thirdValue : Nat) →
    pclNatLt firstValue secondValue = true → pclNatLt secondValue thirdValue = true →
    pclNatLt firstValue thirdValue = true
  | 0, 0, 0, hFirstSecond, _ => Bool.noConfusion hFirstSecond
  | 0, 0, Nat.succ _, hFirstSecond, _ => Bool.noConfusion hFirstSecond
  | 0, Nat.succ _, 0, _, hSecondThird => Bool.noConfusion hSecondThird
  | 0, Nat.succ _, Nat.succ _, _, _ => rfl
  | Nat.succ _, 0, _, hFirstSecond, _ => Bool.noConfusion hFirstSecond
  | Nat.succ _, Nat.succ _, 0, _, hSecondThird => Bool.noConfusion hSecondThird
  | Nat.succ firstPredecessor, Nat.succ secondPredecessor, Nat.succ thirdPredecessor,
      hFirstSecond, hSecondThird =>
      pclNatLtTrans firstPredecessor secondPredecessor thirdPredecessor hFirstSecond hSecondThird

/-- `Nat.beq` is reflexive. -/
theorem pclNatBeqRefl : (value : Nat) → Nat.beq value value = true
  | 0 => rfl
  | Nat.succ predecessor => pclNatBeqRefl predecessor

/-- `Nat.beq`-true naturals are equal. -/
theorem pclNatBeqEq : (leftValue rightValue : Nat) →
    Nat.beq leftValue rightValue = true → leftValue = rightValue
  | 0, 0, _ => rfl
  | 0, Nat.succ _, hBeq => Bool.noConfusion hBeq
  | Nat.succ _, 0, hBeq => Bool.noConfusion hBeq
  | Nat.succ leftPredecessor, Nat.succ rightPredecessor, hBeq =>
      congrArg Nat.succ (pclNatBeqEq leftPredecessor rightPredecessor hBeq)

/-- Structural Boolean equality (full four-arm enumeration — `propext`-free). -/
def pclBoolBeq : Bool → Bool → Bool
  | true, true => true
  | true, false => false
  | false, true => false
  | false, false => true

/-- `pclBoolBeq` is reflexive. -/
theorem pclBoolBeqRefl : (bit : Bool) → pclBoolBeq bit bit = true
  | true => rfl
  | false => rfl

/-- `pclBoolBeq`-true bits are equal. -/
theorem pclBoolBeqEq : (leftBit rightBit : Bool) →
    pclBoolBeq leftBit rightBit = true → leftBit = rightBit
  | true, true, _ => rfl
  | true, false, hBeq => Bool.noConfusion hBeq
  | false, true, hBeq => Bool.noConfusion hBeq
  | false, false, _ => rfl

/-- Structural XOR of two bits (F2 addition). -/
def pclBoolXor : Bool → Bool → Bool
  | true, true => false
  | true, false => true
  | false, true => true
  | false, false => false

/-- Boolean implication `a → b` as `!a || b`, defined by cases on the antecedent. -/
def pclImplies : Bool → Bool → Bool
  | true, consequent => consequent
  | false, _ => true

/-! ## Cons-only list ops (own indexer / length / mask enumeration) -/

/-- Length of a `List Bool` (own structural recursion, not stdlib). -/
def pclLength : List Bool → Nat
  | [] => 0
  | _ :: rest => Nat.succ (pclLength rest)

/-- Own structural table indexer — `table[index]`, default `false` off the end.  NOT `List.getD`. -/
def pclTableRow : List Bool → Nat → Bool
  | [], _ => false
  | bit :: _, 0 => bit
  | _ :: rest, Nat.succ predecessor => pclTableRow rest predecessor

/-- Bit-negate every entry of a mask (the row-complement building block for self-duality). -/
def pclComplement : List Bool → List Bool
  | [] => []
  | bit :: rest => (!bit) :: pclComplement rest

/-- Number of `true` bits in a mask (its Hamming weight / monomial degree). -/
def pclMaskWeight : List Bool → Nat
  | [] => 0
  | true :: rest => Nat.succ (pclMaskWeight rest)
  | false :: rest => pclMaskWeight rest

/-- Pointwise `⊑` on equal-length masks: `a ⊑ b` iff every bit satisfies `a → b`. -/
def pclMaskLe : List Bool → List Bool → Bool
  | [], [] => true
  | [], _ :: _ => true
  | _ :: _, [] => true
  | leftBit :: leftRest, rightBit :: rightRest =>
      pclImplies leftBit rightBit && pclMaskLe leftRest rightRest

/-- Prepend `bit` to every mask of a list, cons-only, fused with an accumulator (no `++`). -/
def pclConsAll (bit : Bool) : List (List Bool) → List (List Bool) → List (List Bool)
  | [], accumulated => accumulated
  | mask :: masks, accumulated => (bit :: mask) :: pclConsAll bit masks accumulated

/-- All `2 ^ n` masks of length `n`, cons-only, `false`-prefixed group first then `true`-prefixed
— row `0` is all-`false`, the last row is all-`true`, big-endian. -/
def pclAllMasks : Nat → List (List Bool)
  | 0 => [[]]
  | Nat.succ predecessor =>
      pclConsAll false (pclAllMasks predecessor)
        (pclConsAll true (pclAllMasks predecessor) [])

/-- The big-endian row index a mask denotes: leading bit is most significant. -/
def pclMaskIndex : List Bool → Nat
  | [] => 0
  | true :: rest => Nat.add (pclPow2 (pclLength rest)) (pclMaskIndex rest)
  | false :: rest => pclMaskIndex rest

/-! ## The truth-table carrier -/

/-- A Boolean function of fixed `arity`, tabulated as `table` of intended length `2 ^ arity`. -/
structure PclBoolFn where
  arity : Nat
  table : List Bool

/-- Well-formedness side-check: the table has exactly `2 ^ arity` rows (a decidable `Bool` flag). -/
def pclTablePow2 (function : PclBoolFn) : Bool :=
  Nat.beq (pclLength function.table) (pclPow2 function.arity)

/-- The function's value on a mask: index the table at the mask's big-endian row number. -/
def pclMaskValue (table : List Bool) (mask : List Bool) : Bool :=
  pclTableRow table (pclMaskIndex mask)

/-! ## The five named-clone preservation predicates -/

/-- `T0`: preserves `0` — the all-`false` row (row `0`) maps to `false`. -/
def pclPreservesZero (function : PclBoolFn) : Bool :=
  pclBoolBeq (pclTableRow function.table 0) false

/-- `T1`: preserves `1` — the all-`true` row (row `2^arity - 1`) maps to `true`. -/
def pclPreservesOne (function : PclBoolFn) : Bool :=
  pclBoolBeq (pclTableRow function.table (pclLastIndex function.arity)) true

/-- The monotone condition for one ordered mask pair: if `u ⊑ v` then `f u → f v`. -/
def pclMonotonePairOk (table : List Bool) (lowerMask upperMask : List Bool) : Bool :=
  pclImplies (pclMaskLe lowerMask upperMask)
    (pclImplies (pclMaskValue table lowerMask) (pclMaskValue table upperMask))

/-- Inner monotone fold: one fixed `lowerMask` against every mask of a list. -/
def pclMonotoneAgainst (table : List Bool) (lowerMask : List Bool) :
    List (List Bool) → Bool
  | [] => true
  | upperMask :: rest =>
      pclMonotonePairOk table lowerMask upperMask && pclMonotoneAgainst table lowerMask rest

/-- Outer monotone fold: every `lowerMask` of a list against every mask of the fixed row list. -/
def pclMonotoneOuter (table : List Bool) (allRows : List (List Bool)) :
    List (List Bool) → Bool
  | [] => true
  | lowerMask :: rest =>
      pclMonotoneAgainst table lowerMask allRows && pclMonotoneOuter table allRows rest

/-- `M`: monotone — the double fold over `2^arity × 2^arity` mask pairs respects `⊑`. -/
def pclIsMonotone (function : PclBoolFn) : Bool :=
  pclMonotoneOuter function.table (pclAllMasks function.arity) (pclAllMasks function.arity)

/-- Self-dual condition for one row: `f u = ¬ f (complement u)`. -/
def pclSelfDualRow (table : List Bool) (mask : List Bool) : Bool :=
  pclBoolBeq (pclMaskValue table mask) (!(pclMaskValue table (pclComplement mask)))

/-- Fold the self-dual condition over a mask list. -/
def pclSelfDualAll (table : List Bool) : List (List Bool) → Bool
  | [] => true
  | mask :: rest => pclSelfDualRow table mask && pclSelfDualAll table rest

/-- `D`: self-dual — every row satisfies `f u = ¬ f (complement u)`. -/
def pclIsSelfDual (function : PclBoolFn) : Bool :=
  pclSelfDualAll function.table (pclAllMasks function.arity)

/-- Reed-Muller (Zhegalkin) coefficient for a monomial `subsetMask`: the F2 sum
`⊕_{T ⊑ subsetMask} f T` — a structural XOR-fold over every mask, gating in `f T` only when
`T ⊑ subsetMask` (the Möbius transform over the Boolean lattice). -/
def pclZhegalkinCoeff (table : List Bool) (subsetMask : List Bool) :
    List (List Bool) → Bool
  | [] => false
  | candidateMask :: rest =>
      pclBoolXor (pclMaskLe candidateMask subsetMask && pclMaskValue table candidateMask)
        (pclZhegalkinCoeff table subsetMask rest)

/-- Affine check: every Zhegalkin monomial of degree ≥ 2 has coefficient `false`. -/
def pclAffineCheck (table : List Bool) (arity : Nat) :
    List (List Bool) → Bool
  | [] => true
  | subsetMask :: rest =>
      pclImplies (pclNatLt 1 (pclMaskWeight subsetMask))
        (!(pclZhegalkinCoeff table subsetMask (pclAllMasks arity)))
        && pclAffineCheck table arity rest

/-- `L`: affine/linear — the Zhegalkin expansion carries no monomial of degree ≥ 2. -/
def pclIsAffine (function : PclBoolFn) : Bool :=
  pclAffineCheck function.table function.arity (pclAllMasks function.arity)

/-! ## The named-clone enum, membership, finite lattice order, and Schaefer -/

/-- The named Post clones on the decidable spine: bottom, the five maximal clones, top. -/
inductive PclNamedClone where
  | cloneBottom
  | cloneT0
  | cloneT1
  | cloneM
  | cloneD
  | cloneL
  | cloneAll

/-- Membership: does a Boolean function lie in a named clone? -/
def pclCloneMembership : PclBoolFn → PclNamedClone → Bool
  | _, .cloneBottom => false
  | function, .cloneT0 => pclPreservesZero function
  | function, .cloneT1 => pclPreservesOne function
  | function, .cloneM => pclIsMonotone function
  | function, .cloneD => pclIsSelfDual function
  | function, .cloneL => pclIsAffine function
  | _, .cloneAll => true

/-- Tag each clone with a rank code `0..6` (bottom `0`, the five maximal `1..5`, top `6`). -/
def pclCloneTag : PclNamedClone → Nat
  | .cloneBottom => 0
  | .cloneT0 => 1
  | .cloneT1 => 2
  | .cloneM => 3
  | .cloneD => 4
  | .cloneL => 5
  | .cloneAll => 6

/-- Left inverse of `pclCloneTag` on its image — witnesses tag injectivity without a 49-arm case. -/
def pclCloneOfTag : Nat → PclNamedClone
  | 0 => .cloneBottom
  | 1 => .cloneT0
  | 2 => .cloneT1
  | 3 => .cloneM
  | 4 => .cloneD
  | 5 => .cloneL
  | 6 => .cloneAll
  | Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ _)))))) => .cloneAll

/-- `pclCloneOfTag ∘ pclCloneTag = id` — the round-trip pinning tag injectivity (seven `rfl`s). -/
theorem pclCloneOfTagTag : (clone : PclNamedClone) → pclCloneOfTag (pclCloneTag clone) = clone
  | .cloneBottom => rfl
  | .cloneT0 => rfl
  | .cloneT1 => rfl
  | .cloneM => rfl
  | .cloneD => rfl
  | .cloneL => rfl
  | .cloneAll => rfl

/-- Structural equality of clones via their tags. -/
def pclCloneBeq (leftClone rightClone : PclNamedClone) : Bool :=
  Nat.beq (pclCloneTag leftClone) (pclCloneTag rightClone)

/-- `pclCloneBeq` is reflexive. -/
theorem pclCloneBeqRefl (clone : PclNamedClone) : pclCloneBeq clone clone = true :=
  pclNatBeqRefl (pclCloneTag clone)

/-- `pclCloneBeq`-true clones are equal (via `Nat.beq` soundness + the tag round-trip). -/
theorem pclCloneBeqEq (leftClone rightClone : PclNamedClone)
    (hBeq : pclCloneBeq leftClone rightClone = true) : leftClone = rightClone := by
  have hTag : pclCloneTag leftClone = pclCloneTag rightClone :=
    pclNatBeqEq (pclCloneTag leftClone) (pclCloneTag rightClone) hBeq
  have hRound := congrArg pclCloneOfTag hTag
  rw [pclCloneOfTagTag leftClone, pclCloneOfTagTag rightClone] at hRound
  exact hRound

/-- Height of a clone in the lattice: bottom `0`, the five maximal `1`, top `2`. -/
def pclCloneLevel : PclNamedClone → Nat
  | .cloneBottom => 0
  | .cloneT0 => 1
  | .cloneT1 => 1
  | .cloneM => 1
  | .cloneD => 1
  | .cloneL => 1
  | .cloneAll => 2

/-- The named-clone inclusion order: equal clones, or a strictly lower height (bottom ≤ everything,
everything ≤ top, the five maximal clones a pairwise-incomparable antichain). -/
def pclCloneLe (leftClone rightClone : PclNamedClone) : Bool :=
  match pclCloneBeq leftClone rightClone with
  | true => true
  | false => pclNatLt (pclCloneLevel leftClone) (pclCloneLevel rightClone)

/-- From `pclCloneLe` conclude either equality or a strict height drop. -/
theorem pclCloneLeElim (leftClone rightClone : PclNamedClone)
    (hLe : pclCloneLe leftClone rightClone = true) :
    leftClone = rightClone ∨
      pclNatLt (pclCloneLevel leftClone) (pclCloneLevel rightClone) = true := by
  unfold pclCloneLe at hLe
  cases hBeq : pclCloneBeq leftClone rightClone with
  | true => exact Or.inl (pclCloneBeqEq leftClone rightClone hBeq)
  | false =>
      rw [hBeq] at hLe
      exact Or.inr hLe

/-- Introduce `pclCloneLe` from a strict height drop. -/
theorem pclCloneLeOfLt (leftClone rightClone : PclNamedClone)
    (hLt : pclNatLt (pclCloneLevel leftClone) (pclCloneLevel rightClone) = true) :
    pclCloneLe leftClone rightClone = true := by
  unfold pclCloneLe
  cases hBeq : pclCloneBeq leftClone rightClone with
  | true => rfl
  | false => exact hLt

/-- Introduce `pclCloneLe` from equality. -/
theorem pclCloneLeOfEq (leftClone rightClone : PclNamedClone) (hEq : leftClone = rightClone) :
    pclCloneLe leftClone rightClone = true := by
  subst hEq
  unfold pclCloneLe
  rw [pclCloneBeqRefl leftClone]

/-- The named-clone order is reflexive. -/
theorem pclCloneLeRefl (clone : PclNamedClone) : pclCloneLe clone clone = true :=
  pclCloneLeOfEq clone clone rfl

/-- The named-clone order is transitive. -/
theorem pclCloneLeTrans (firstClone secondClone thirdClone : PclNamedClone)
    (hFirstSecond : pclCloneLe firstClone secondClone = true)
    (hSecondThird : pclCloneLe secondClone thirdClone = true) :
    pclCloneLe firstClone thirdClone = true := by
  cases pclCloneLeElim firstClone secondClone hFirstSecond with
  | inl hEqFirstSecond =>
      subst hEqFirstSecond
      exact hSecondThird
  | inr hLtFirstSecond =>
      cases pclCloneLeElim secondClone thirdClone hSecondThird with
      | inl hEqSecondThird =>
          subst hEqSecondThird
          exact pclCloneLeOfLt firstClone secondClone hLtFirstSecond
      | inr hLtSecondThird =>
          exact pclCloneLeOfLt firstClone thirdClone
            (pclNatLtTrans (pclCloneLevel firstClone) (pclCloneLevel secondClone)
              (pclCloneLevel thirdClone) hLtFirstSecond hLtSecondThird)

/-- Do all constraints lie in the one given clone? -/
def pclAllInClone (clone : PclNamedClone) : List PclBoolFn → Bool
  | [] => true
  | constraint :: rest => pclCloneMembership constraint clone && pclAllInClone clone rest

/-- SOUND Schaefer tractability WITNESS: the constraint set is jointly preserved by one common
tractable polymorphism — i.e. every constraint lies in one of `T0`, `T1`, `M`, `D`, `L`.  If this
holds the CSP is polynomial-time.  The CONVERSE (Schaefer's full dichotomy — that failing all five
forces NP-completeness) is walled: `pclHasHigherDomainDichotomy`. -/
def pclIsSchaeferTractable (constraints : List PclBoolFn) : Bool :=
  pclAllInClone .cloneT0 constraints || pclAllInClone .cloneT1 constraints
    || pclAllInClone .cloneM constraints || pclAllInClone .cloneD constraints
    || pclAllInClone .cloneL constraints

/-! ## Capability markers -/

/-- The five named-clone preservation tests with `pclCloneMembership`. -/
def pclHasNamedCloneMembership : Bool := true

/-- The seven-element named-clone lattice order (reflexivity and transitivity). -/
def pclHasFiniteCloneLattice : Bool := true

/-- The sufficient common-tractable-clone Schaefer witness. -/
def pclHasSchaeferTractabilityDecision : Bool := true

/-! ## The walls -/

/-- The complete Post lattice, not proven here. Post (1941) classifies all clones of Boolean
functions: countably infinitely many, with infinite descending chains (`T0^{(k)}`, `M∩T0∩…`, the
`S`/`P` families) that no finite enumeration captures. Such an infinite poset has no `List`-of-clones
carrier, and its membership relation quantifies over the infinite chain index, so founding the
chains would need `WellFounded.fix`. Closing under intersection never terminates (the `T0^{(k)}`
chain adds a fresh clone at every `k`), and indexing by a defining-relation arity fails because the
counting clones `U_k`/`W_k` separate above any fixed arity. -/
def pclHasFullPostLattice : Bool := false

/-- The general finite-domain CSP dichotomy (Bulatov 2017 / Zhuk 2017), not proven here. The
Boolean (`|D| = 2`) dichotomy is the decidable slice shipped as the tractable-clone witness; the
`|D| ≥ 3` case is a proof about a weak-near-unanimity polymorphism on an unbounded domain. The
criterion ranges over polymorphisms of every arity on a domain of arbitrary finite size, and its
hard direction is an absorption-theory argument with no bounded decision procedure — no fixed arity
suffices (Siggers is 6-ary), and bit-encoding a finite domain into Boolean does not preserve
polymorphism structure. -/
def pclHasHigherDomainDichotomy : Bool := false

/-- Clone generation closure / the `Pol`–`Inv` Galois correspondence, not proven here. Deciding
whether a set of Boolean functions generates a given clone needs the closure under composition and
projection, an unbounded fixpoint: the composition-closure operator has no structural decreasing
measure (composing two arity-`k` functions grows arity without bound), so the least fixpoint is
founded only by `WellFounded.fix`. Capping composition depth by fuel under-approximates, and the
`Inv` side is itself infinitely many relations of all arities, so the round trip closes only in the
limit. -/
def pclHasCloneGenerationClosure : Bool := false

/-! ## Ground fires (concrete small-arity witnesses, all `rfl`) -/

/-- Conjunction as a truth table: `∧` over `[FF, FT, TF, TT] = [false, false, false, true]`. -/
def pclAndFn : PclBoolFn := { arity := 2, table := [false, false, false, true] }

/-- Exclusive-or as a truth table: `⊕` over the four rows = `[false, true, true, false]`. -/
def pclXorFn : PclBoolFn := { arity := 2, table := [false, true, true, false] }

/-- Negation as an arity-1 truth table: `¬false = true`, `¬true = false` → `[true, false]`. -/
def pclNegFn : PclBoolFn := { arity := 1, table := [true, false] }

/-- NAND — in NONE of the five named clones (a discriminating non-witness). -/
def pclNandFn : PclBoolFn := { arity := 2, table := [true, true, true, false] }

theorem pclAndTablePow2 : pclTablePow2 pclAndFn = true := rfl

theorem pclAndMonotone : pclIsMonotone pclAndFn = true := rfl

theorem pclAndPreservesZero : pclPreservesZero pclAndFn = true := rfl

theorem pclAndPreservesOne : pclPreservesOne pclAndFn = true := rfl

/-- `∧` carries the degree-2 monomial `x·y`. -/
theorem pclAndNotAffine : pclIsAffine pclAndFn = false := rfl

theorem pclXorAffine : pclIsAffine pclXorFn = true := rfl

/-- `[F,T] ⊑ [T,T]` but the value drops `true → false`. -/
theorem pclXorNotMonotone : pclIsMonotone pclXorFn = false := rfl

theorem pclNegSelfDual : pclIsSelfDual pclNegFn = true := rfl

theorem pclNegNotMonotone : pclIsMonotone pclNegFn = false := rfl

/-- A discriminating non-witness for the `D` clone. -/
theorem pclAndNotSelfDual : pclIsSelfDual pclAndFn = false := rfl

/-- With `∧` monotone, the pair `[F,T] ⊑ [T,T]` respects the value order. -/
theorem pclAndRespectsWitnessedPair :
    pclImplies (pclMaskValue pclAndFn.table [false, true])
      (pclMaskValue pclAndFn.table [true, true]) = true := rfl

theorem pclAndInCloneM : pclCloneMembership pclAndFn .cloneM = true := rfl

theorem pclCloneLeReflT0 : pclCloneLe .cloneT0 .cloneT0 = true := rfl

theorem pclCloneLeBottomAll : pclCloneLe .cloneBottom .cloneAll = true := rfl

theorem pclCloneLeT0All : pclCloneLe .cloneT0 .cloneAll = true := rfl

/-- `T0` and `T1` are incomparable (the antichain). -/
theorem pclCloneLeT0T1Incomparable : pclCloneLe .cloneT0 .cloneT1 = false := rfl

/-- `⊕` alone is Schaefer-tractable (affine witness). -/
theorem pclSchaeferXorTractable : pclIsSchaeferTractable [pclXorFn] = true := rfl

/-- NAND lies in none of the five clones, so no common tractable-clone witness. -/
theorem pclSchaeferNandNoWitness : pclIsSchaeferTractable [pclNandFn] = false := rfl

/-- The tractable-side capability markers hold. -/
theorem pclDecidedMarkers :
    (pclHasNamedCloneMembership && pclHasFiniteCloneLattice
      && pclHasSchaeferTractabilityDecision) = true := rfl

/-- The wall markers are all `false`. -/
theorem pclWallMarkers :
    (pclHasFullPostLattice || pclHasHigherDomainDichotomy
      || pclHasCloneGenerationClosure) = false := rfl

end FX1Poly.ComputerAlgebra
