import FX1Poly.Tier0.Context.ContextDirectedUniverse

/-! # context-34 — DIRECTED univalence at the context category: `Hom_U ↝ Fun` as a reduction

`context-34` (★) is the DIRECTED-UNIVALENCE rung at the context category — the DIRECTED analog of the sibling
`context-31` (`ContextDefinitionalUnivalence.lean`, the SYMMETRIC `Id_U ↝ Equiv` definitional univalence).  It
makes the universe object's DIRECTED univalence hold BY COMPUTATION: the directed-hom former at the universe
object, `Hom_U(A, B)`, REDUCES to the function-type former `Fun(A, B)`.  Read in `context-34`'s
directed-wild-category apparatus (`ContextDirectedUniverse.lean`), this is the directed analog of
`context-31`'s identity-to-equivalence reduction: a path becomes a directed hom, and the directed hom at the
universe object computes to a function — directed univalence as a definitional reduction, not a transport, so
it stays zero-axiom (no funext, no `Quot.sound`).

## The move, mirrored from `context-31`

`context-31` ships `idForm universeObj A B ↝ equivForm A B` (`Id_U ↝ Equiv`) over a small self-contained code
algebra, with a structural normalizer, size-drop strong normalization, canonicity, and decidable conversion.
`context-34` ships the SAME move with the DIRECTED former and the FUNCTION former replacing the symmetric ones:

  * **`ContextDirectedCode`** — the context-universe codes: the universe object `universeObj`, opaque type
    codes `atom`, the DIRECTED-hom former `homForm (scrutinee lhs rhs)` (= `Hom_scrutinee(lhs, rhs)`), and the
    FUNCTION-type former `funForm (lhs rhs)` (= `lhs → rhs`).  Mirrors `gen_universeCode` / a directed-hom code
    / `gen_arrowCode`.
  * **`ContextDirectedUnivStep`** — the reduction relation, whose root rule
    `directedUnivalence : homForm universeObj A B ↝ funForm A B` IS the `Hom_U ↝ Fun` reduction, plus
    congruence.
  * **`ContextDirectedCode.normalize`** — the structural normalizer realizing the reduction; the directed-hom
    redex fires via the smart constructor `reassembleHom`.
  * **`ContextDirectedUnivStep.size_lt` + `isStronglyNormalizing`** — STRONG NORMALIZATION: every step strictly
    decreases `ContextDirectedCode.size` (the rule drops the `universeObj` scrutinee), fed to a structural fuel
    accessibility argument (no `WellFounded.fix`).
  * **`normalize_hasNoDirectedUnivalenceRedex`** — CANONICITY: a normalized code has NO `Hom_U` redex left.
  * **`Conv` + the `Decidable` instance** — DECIDABLE CONVERSION by normalize-and-compare.
  * **`contextDirectedUnivalence`** — ★ the payoff: `Hom_U(A, B)` and `Fun(A, B)` are CONVERTIBLE, and in fact
    their normal forms are EQUAL BY `rfl` (`homOverUniverseObject_normalize_eq`).  Directed univalence at the
    context category: the directed-hom-to-function comparison is the reduction itself.

## Bridge to the apparatus (`context-34` directed universe)

`directedUnivalence_homToFun` feeds the `rfl`-equality of normalized `Hom_U(A,B)` and `Fun(A,B)` into
`homToFun` (`ContextDirectedUniverse.lean`), producing the directed hom that identifies them in the
(directed-univalent, set-level) `discreteUniverseObject`.  This is the directed-wild-category univalence
realized BY COMPUTATION: the universe object's directed-hom and function types are definitionally the same
object.

## Honesty

  * The reduction is the SELF-CONTAINED Tier0 analog of the Core table-native directed-univalence row; it is NOT
    over `StepOverTable` (`fxContextDirectedUnivalence_isOverCoreIotaTable = false`).  The two agree in shape
    (drop the universe scrutinee, size-decreasing, decidable conversion); the Core/Tier0 gluing is cross-axis
    `×type`.
  * This is DEFINITIONAL / DIRECTED-CATEGORICAL univalence (the funext-free fragment,
    `ContextDirectedUniverse.lean`), NOT the full Segal / Rezk-complete directed univalence axiom.

Imports only `ContextDirectedUniverse` (its `context-34` apparatus sibling).  Zero external dependencies — raw
Lean 4 + Init only.

Reference: the sibling `context-31` `Id_U ↝ Equiv` reduction (`ContextDefinitionalUnivalence.lean`); Riehl &
Shulman, "A type theory for synthetic ∞-categories", HHA 2017; the directed universe generator `gen_universeD`.
-/

namespace FX1Poly.Tier0

/-! ## The context-universe code algebra -/

/-- A **context-universe code**: the universe object, opaque type codes, the DIRECTED-hom former, and the
function-type former.  This is the small self-contained algebra over which the `Hom_U ↝ Fun` reduction is
shipped (the directed mirror of `context-31`'s `ContextUnivCode`). -/
inductive ContextDirectedCode where
  /-- The universe object `U` of the context category (the `gen_universeCode` analog). -/
  | universeObj
  /-- An opaque type code / type-in-context (a morphism into the universe object). -/
  | atom (index : Nat)
  /-- The DIRECTED-hom former `Hom_scrutinee(lhs, rhs)` (the directed-hom-code analog). -/
  | homForm (scrutinee lhs rhs : ContextDirectedCode)
  /-- The FUNCTION-type former `lhs → rhs` (the `gen_arrowCode` analog). -/
  | funForm (lhs rhs : ContextDirectedCode)
  deriving DecidableEq

/-- Is this code the universe object?  The head test the `Hom_U` redex fires on (mirrors `context-31`'s
`headIsUniverseObj`, pinning slot-0's head to the universe object). -/
def ContextDirectedCode.headIsUniverseObj : ContextDirectedCode → Bool
  | .universeObj => true
  | .atom _ => false
  | .homForm _ _ _ => false
  | .funForm _ _ => false

/-- The smart directed-hom constructor on already-normalized children: when the (normalized) scrutinee is the
universe object, FIRE the directed univalence reduction `Hom_U(lhs, rhs) ↝ lhs → rhs`; otherwise rebuild the
directed-hom former.  This is the operational core of the `Hom_U ↝ Fun` reduction. -/
def ContextDirectedCode.reassembleHom (normScrutinee normLhs normRhs : ContextDirectedCode) :
    ContextDirectedCode :=
  match normScrutinee with
  | .universeObj => .funForm normLhs normRhs
  | .atom index => .homForm (.atom index) normLhs normRhs
  | .homForm innerScrutinee innerLhs innerRhs =>
      .homForm (.homForm innerScrutinee innerLhs innerRhs) normLhs normRhs
  | .funForm innerLhs innerRhs => .homForm (.funForm innerLhs innerRhs) normLhs normRhs

/-- The structural normalizer realizing the `Hom_U ↝ Fun` reduction (the directed mirror of `context-31`'s
`normalize`): normalize the children, then fire the universe-Hom redex via `reassembleHom`.  Structural
recursion — zero-axiom, no `WellFounded.fix`. -/
def ContextDirectedCode.normalize : ContextDirectedCode → ContextDirectedCode
  | .universeObj => .universeObj
  | .atom index => .atom index
  | .funForm lhs rhs => .funForm lhs.normalize rhs.normalize
  | .homForm scrutinee lhs rhs =>
      ContextDirectedCode.reassembleHom scrutinee.normalize lhs.normalize rhs.normalize

/-- Does this code still contain an unfired `Hom_U(_, _)` redex (a `homForm` whose scrutinee is the universe
object)?  The canonicity yardstick: a normal form has none. -/
def ContextDirectedCode.hasDirectedUnivalenceRedex : ContextDirectedCode → Bool
  | .universeObj => false
  | .atom _ => false
  | .funForm lhs rhs => lhs.hasDirectedUnivalenceRedex || rhs.hasDirectedUnivalenceRedex
  | .homForm scrutinee lhs rhs =>
      scrutinee.headIsUniverseObj || scrutinee.hasDirectedUnivalenceRedex
        || lhs.hasDirectedUnivalenceRedex || rhs.hasDirectedUnivalenceRedex

/-- The size measure — the SN witness's yardstick (mirrors `RawTerm.size`).  The directed univalence rule drops
the `universeObj` scrutinee, so it strictly shrinks this. -/
def ContextDirectedCode.size : ContextDirectedCode → Nat
  | .universeObj => 1
  | .atom _ => 1
  | .funForm lhs rhs => 1 + lhs.size + rhs.size
  | .homForm scrutinee lhs rhs => 1 + scrutinee.size + lhs.size + rhs.size

/-! ## Definitional directed univalence: `Hom_U(A, B)` and `Fun(A, B)` have the SAME normal form, by `rfl` -/

/-- ★ **Definitional directed univalence (the `rfl` core).**  The normal form of `Hom_U(A, B)` IS the normal
form of `Fun(A, B)` — by `rfl`.  `normalize (homForm universeObj A B)` fires `reassembleHom universeObj … =
funForm A.norm B.norm = normalize (funForm A B)`.  The directed-hom former at the universe object computes to
the function former: directed univalence holds definitionally, the directed mirror of `context-31`'s
`idOverUniverseObject_normalize_eq`. -/
theorem ContextDirectedCode.homOverUniverseObject_normalize_eq (codeLeft codeRight : ContextDirectedCode) :
    (ContextDirectedCode.homForm .universeObj codeLeft codeRight).normalize
      = (ContextDirectedCode.funForm codeLeft codeRight).normalize :=
  rfl

/-! ## Canonicity: a normalized code has no `Hom_U` redex left -/

/-- The smart constructor preserves redex-freedom: if the normalized children are redex-free, so is the
reassembled directed-hom former.  When the scrutinee is the universe object the result is a `funForm` (no
`homForm` head at all); otherwise the rebuilt `homForm` has a non-universe scrutinee. -/
theorem ContextDirectedCode.reassembleHom_hasNoDirectedUnivalenceRedex
    {normScrutinee normLhs normRhs : ContextDirectedCode}
    (scrutineeRedexFree : normScrutinee.hasDirectedUnivalenceRedex = false)
    (lhsRedexFree : normLhs.hasDirectedUnivalenceRedex = false)
    (rhsRedexFree : normRhs.hasDirectedUnivalenceRedex = false) :
    (ContextDirectedCode.reassembleHom normScrutinee normLhs normRhs).hasDirectedUnivalenceRedex = false := by
  cases normScrutinee with
  | universeObj =>
      show (normLhs.hasDirectedUnivalenceRedex || normRhs.hasDirectedUnivalenceRedex) = false
      rw [lhsRedexFree, rhsRedexFree]; rfl
  | atom index =>
      show ((ContextDirectedCode.atom index).headIsUniverseObj
            || (ContextDirectedCode.atom index).hasDirectedUnivalenceRedex
            || normLhs.hasDirectedUnivalenceRedex || normRhs.hasDirectedUnivalenceRedex) = false
      rw [lhsRedexFree, rhsRedexFree]; rfl
  | homForm innerScrutinee innerLhs innerRhs =>
      show ((ContextDirectedCode.homForm innerScrutinee innerLhs innerRhs).headIsUniverseObj
            || (ContextDirectedCode.homForm innerScrutinee innerLhs innerRhs).hasDirectedUnivalenceRedex
            || normLhs.hasDirectedUnivalenceRedex || normRhs.hasDirectedUnivalenceRedex) = false
      rw [scrutineeRedexFree, lhsRedexFree, rhsRedexFree]; rfl
  | funForm innerLhs innerRhs =>
      show ((ContextDirectedCode.funForm innerLhs innerRhs).headIsUniverseObj
            || (ContextDirectedCode.funForm innerLhs innerRhs).hasDirectedUnivalenceRedex
            || normLhs.hasDirectedUnivalenceRedex || normRhs.hasDirectedUnivalenceRedex) = false
      rw [scrutineeRedexFree, lhsRedexFree, rhsRedexFree]; rfl

/-- ★ **Canonicity.**  Every normalized code is `Hom_U`-redex-free: the universe-directed-hom former is fully
eliminated by `normalize`.  This is the directed mirror of `context-31`'s
`normalize_hasNoUnivalenceRedex` — the reduction is complete. -/
theorem ContextDirectedCode.normalize_hasNoDirectedUnivalenceRedex (code : ContextDirectedCode) :
    code.normalize.hasDirectedUnivalenceRedex = false := by
  induction code with
  | universeObj => rfl
  | atom index => rfl
  | funForm lhs rhs lhsRedexFree rhsRedexFree =>
      show (lhs.normalize.hasDirectedUnivalenceRedex || rhs.normalize.hasDirectedUnivalenceRedex) = false
      rw [lhsRedexFree, rhsRedexFree]; rfl
  | homForm scrutinee lhs rhs scrutineeRedexFree lhsRedexFree rhsRedexFree =>
      show (ContextDirectedCode.reassembleHom scrutinee.normalize lhs.normalize
              rhs.normalize).hasDirectedUnivalenceRedex = false
      exact ContextDirectedCode.reassembleHom_hasNoDirectedUnivalenceRedex
        scrutineeRedexFree lhsRedexFree rhsRedexFree

/-! ## The reduction relation and strong normalization -/

/-- The **`Hom_U ↝ Fun` reduction relation** at the context category.  Its root rule `directedUnivalence` IS
the directed-univalence reduction `Hom_U(A, B) ↝ A → B`; the remaining rules are congruence.  This is the
directed mirror of `context-31`'s `ContextUnivStep`. -/
inductive ContextDirectedUnivStep : ContextDirectedCode → ContextDirectedCode → Prop
  /-- ★ The directed univalence reduction: the directed-hom former at the universe object reduces to the
  function former. -/
  | directedUnivalence (lhs rhs : ContextDirectedCode) :
      ContextDirectedUnivStep (.homForm .universeObj lhs rhs) (.funForm lhs rhs)
  /-- Congruence in the directed-hom former's scrutinee. -/
  | homScrutinee {scrutinee scrutinee' : ContextDirectedCode} (lhs rhs : ContextDirectedCode) :
      ContextDirectedUnivStep scrutinee scrutinee' →
      ContextDirectedUnivStep (.homForm scrutinee lhs rhs) (.homForm scrutinee' lhs rhs)
  /-- Congruence in the directed-hom former's left argument. -/
  | homLhs (scrutinee : ContextDirectedCode) {lhs lhs' : ContextDirectedCode} (rhs : ContextDirectedCode) :
      ContextDirectedUnivStep lhs lhs' →
      ContextDirectedUnivStep (.homForm scrutinee lhs rhs) (.homForm scrutinee lhs' rhs)
  /-- Congruence in the directed-hom former's right argument. -/
  | homRhs (scrutinee lhs : ContextDirectedCode) {rhs rhs' : ContextDirectedCode} :
      ContextDirectedUnivStep rhs rhs' →
      ContextDirectedUnivStep (.homForm scrutinee lhs rhs) (.homForm scrutinee lhs rhs')
  /-- Congruence in the function former's left argument. -/
  | funLhs {lhs lhs' : ContextDirectedCode} (rhs : ContextDirectedCode) :
      ContextDirectedUnivStep lhs lhs' →
      ContextDirectedUnivStep (.funForm lhs rhs) (.funForm lhs' rhs)
  /-- Congruence in the function former's right argument. -/
  | funRhs (lhs : ContextDirectedCode) {rhs rhs' : ContextDirectedCode} :
      ContextDirectedUnivStep rhs rhs' →
      ContextDirectedUnivStep (.funForm lhs rhs) (.funForm lhs rhs')

/-- ★ **Every reduction step strictly decreases `size`.**  The directed univalence root rule drops the
`universeObj` scrutinee — its reduct is the redex with the universe head removed, strictly smaller — and
congruence is monotone.  The directed mirror of `context-31`'s `size_lt`. -/
theorem ContextDirectedUnivStep.size_lt {codeA codeB : ContextDirectedCode}
    (step : ContextDirectedUnivStep codeA codeB) : codeB.size < codeA.size := by
  induction step with
  | directedUnivalence lhs rhs =>
      exact Nat.add_lt_add_right (Nat.add_lt_add_right (Nat.lt_succ_self 1) lhs.size) rhs.size
  | homScrutinee lhs rhs _ scrutineeDrop =>
      exact Nat.add_lt_add_right
        (Nat.add_lt_add_right (Nat.add_lt_add_left scrutineeDrop 1) lhs.size) rhs.size
  | homLhs scrutinee rhs _ lhsDrop =>
      exact Nat.add_lt_add_right (Nat.add_lt_add_left lhsDrop (1 + scrutinee.size)) rhs.size
  | homRhs scrutinee lhs _ rhsDrop =>
      exact Nat.add_lt_add_left rhsDrop (1 + scrutinee.size + lhs.size)
  | funLhs rhs _ lhsDrop =>
      exact Nat.add_lt_add_right (Nat.add_lt_add_left lhsDrop 1) rhs.size
  | funRhs lhs _ rhsDrop =>
      exact Nat.add_lt_add_left rhsDrop (1 + lhs.size)

/-- Accessibility from a size bound, by structural recursion on the fuel `Nat` — the zero-axiom SN engine
(no `WellFounded.fix`): a code whose size is below the fuel is accessible under the (reversed) reduction. -/
theorem ContextDirectedCode.accessibleUnderStep_ofSizeBelow :
    ∀ (fuel : Nat) (code : ContextDirectedCode), code.size < fuel →
      Acc (fun reduct redex => ContextDirectedUnivStep redex reduct) code
  | 0, _, sizeBelowZero => absurd sizeBelowZero (Nat.not_lt_zero _)
  | fuel + 1, code, sizeBelow =>
      Acc.intro code (fun reduct stepWitness =>
        ContextDirectedCode.accessibleUnderStep_ofSizeBelow fuel reduct
          (Nat.lt_of_lt_of_le (ContextDirectedUnivStep.size_lt stepWitness) (Nat.le_of_lt_succ sizeBelow)))

/-- ★ **Strong normalization.**  Every code is accessible under the reduction — no infinite `Hom_U ↝ Fun`
reduction sequence — by the size-drop fed to the structural fuel argument.  RPO-free, Tait-free: the directed
univalence rule shrinks `size`, the directed mirror of `context-31`'s `isStronglyNormalizing`. -/
theorem ContextDirectedCode.isStronglyNormalizing (code : ContextDirectedCode) :
    Acc (fun reduct redex => ContextDirectedUnivStep redex reduct) code :=
  ContextDirectedCode.accessibleUnderStep_ofSizeBelow (code.size + 1) code (Nat.lt_succ_self _)

/-! ## Decidable conversion -/

/-- Conversion: two codes are convertible when they share a normal form.  Decidable by normalize-and-compare
(the directed mirror of `context-31`'s `Conv`). -/
def ContextDirectedCode.Conv (codeA codeB : ContextDirectedCode) : Prop :=
  codeA.normalize = codeB.normalize

instance ContextDirectedCode.Conv.decidable (codeA codeB : ContextDirectedCode) :
    Decidable (ContextDirectedCode.Conv codeA codeB) :=
  inferInstanceAs (Decidable (codeA.normalize = codeB.normalize))

/-- Conversion is reflexive. -/
theorem ContextDirectedCode.Conv.refl (code : ContextDirectedCode) :
    ContextDirectedCode.Conv code code := rfl

/-- Conversion is symmetric. -/
theorem ContextDirectedCode.Conv.symm {codeA codeB : ContextDirectedCode}
    (convAB : ContextDirectedCode.Conv codeA codeB) : ContextDirectedCode.Conv codeB codeA :=
  Eq.symm convAB

/-- Conversion is transitive. -/
theorem ContextDirectedCode.Conv.trans {codeA codeB codeC : ContextDirectedCode}
    (convAB : ContextDirectedCode.Conv codeA codeB) (convBC : ContextDirectedCode.Conv codeB codeC) :
    ContextDirectedCode.Conv codeA codeC :=
  Eq.trans convAB convBC

/-- ★ **Directed univalence at the context category.**  `Hom_U(A, B)` and `Fun(A, B)` are CONVERTIBLE —
indeed their normal forms are equal by `rfl`.  The directed-hom-to-function comparison at the universe object
IS the reduction.  This is the directed mirror of `context-31`'s `contextDefinitionalUnivalence`. -/
theorem ContextDirectedCode.contextDirectedUnivalence (codeLeft codeRight : ContextDirectedCode) :
    ContextDirectedCode.Conv (.homForm .universeObj codeLeft codeRight) (.funForm codeLeft codeRight) :=
  ContextDirectedCode.homOverUniverseObject_normalize_eq codeLeft codeRight

/-- The directed univalence rule is a genuine step of the reduction relation — the reduction-relation witness
behind the definitional convertibility above. -/
theorem ContextDirectedCode.directedUnivalenceRule_reduces (codeLeft codeRight : ContextDirectedCode) :
    ContextDirectedUnivStep (.homForm .universeObj codeLeft codeRight) (.funForm codeLeft codeRight) :=
  ContextDirectedUnivStep.directedUnivalence codeLeft codeRight

/-! ## Bridge to the apparatus: the reduction REALIZES directed univalence -/

/-- Bridge to `ContextDirectedUniverse.lean`: the directed hom identifying normalized `Hom_U(A, B)` with
normalized `Fun(A, B)` in the (directed-univalent, set-level) `discreteUniverseObject`, produced by feeding the
definitional `rfl`-equality of their normal forms into the apparatus's `homToFun`.  This is directed univalence
realized BY COMPUTATION: in the universe object, the directed-hom and function types of `A, B` are the SAME
object, so `homToFun` connects them by the identity hom — the directed mirror of `context-31`'s
`definitionalUnivalence_idToIso`. -/
def directedUnivalence_homToFun (codeLeft codeRight : ContextDirectedCode) :
    DirectedCategoryHom (discreteUniverseObject ContextDirectedCode)
      ((ContextDirectedCode.homForm .universeObj codeLeft codeRight).normalize)
      ((ContextDirectedCode.funForm codeLeft codeRight).normalize) :=
  homToFun (discreteUniverseObject ContextDirectedCode)
    (ContextDirectedCode.homOverUniverseObject_normalize_eq codeLeft codeRight)

/-! ## Honesty markers -/

/-- **Honesty marker.**  The `Hom_U ↝ Fun` reduction at the context category is shipped, with its definitional
directed univalence (`Hom_U(A,B)` and `Fun(A,B)` share a normal form by `rfl`).  `= true`. -/
def fxContextDirectedUnivalence_homReducesToFun : Bool := true

/-- **Honesty marker.**  Strong normalization (size-drop) + canonicity + DECIDABLE conversion are shipped for
the context-level directed-univalence reduction.  `= true`. -/
def fxContextDirectedUnivalence_hasDecidableConversion : Bool := true

/-- **Honesty marker.**  This is the SELF-CONTAINED Tier0 analog of the Core table-native directed-univalence
row (over `StepOverTable`, with generic orthogonal-table confluence).  A Tier0 design-lock cannot import the
Core engine, so the reduction is re-shipped here as a structural normalizer; the two agree in shape (drop the
universe scrutinee, size-decreasing, decidable conversion).  Gluing the Tier0 and Core forms is cross-axis
`×type`.  `= false`. -/
def fxContextDirectedUnivalence_isOverCoreIotaTable : Bool := false

/-- **Honesty marker.**  This reduction realizes the funext-free DIRECTED-CATEGORICAL univalence
(`ContextDirectedUniverse.lean`), NOT the full Segal / Rezk-complete directed univalence axiom
(`Hom_U(A,B) ≃ (A → B)` with homotopy coherence), which needs `Quot.sound` / funext — the `×type` wall the
`gen_universeD` directed universe defers.  `= false`. -/
def fxContextDirectedUnivalence_hasFullSegalDirectedUA : Bool := false

/-! ## Smoke -/

/-- Smoke: `Hom_U(atom 0, atom 1)` is convertible to `atom 0 → atom 1` — the directed univalence reduction
decided by computation. -/
theorem contextDirectedUnivalence_smoke :
    ContextDirectedCode.Conv
      (.homForm .universeObj (.atom 0) (.atom 1))
      (.funForm (.atom 0) (.atom 1)) :=
  ContextDirectedCode.contextDirectedUnivalence (.atom 0) (.atom 1)

end FX1Poly.Tier0
