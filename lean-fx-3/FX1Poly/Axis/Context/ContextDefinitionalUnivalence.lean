import FX1Poly.Axis.Context.ContextUnivalentUniverse

/-! # context-31 — DEFINITIONAL univalence at the context category: `Id_U ↝ Equiv` as a reduction

`context-31` (★) is the DEFINITIONAL-UNIVALENCE rung at the context category — the context-side analog of the
TYPE-axis `type-7` (`Id_U ↝ Equiv`, shipped zero-axiom over the Core iota table).  It makes the universe
object's univalence hold BY COMPUTATION: the identity former at the universe object, `Id_U(A, B)`, REDUCES to
the (categorical) equivalence former `Equiv(A, B)`.  Read in `context-30`'s wild-category terms, this is the
identity-to-equivalence comparison realized as a definitional reduction rather than a transport — so it stays
zero-axiom (no funext, no `Quot.sound`), exactly as `type-7` does on the type axis.

## The move, mirrored from `type-7`

`type-7` ships the row `univalenceShapedDemoRule : idCode(universeCode, A, B) ↝ equivCode(A, B)` over the Core
`StepOverTable` engine: confluence is generic (orthogonal singleton table), SN is one `RawTerm.size`-drop
lemma (the rule DROPS the `universeCode` scrutinee, so the reduct is strictly smaller), and decidable
conversion is the generic crank.  A Axis design-lock cannot import the Core table engine, so `context-31`
ships the SAME move SELF-CONTAINED over a small context-universe code algebra:

  * **`ContextUnivCode`** — the context-universe codes: the universe object `universeObj`, opaque type codes
    `atom`, the identity former `idForm (scrutinee lhs rhs)` (= `Id_scrutinee(lhs, rhs)`), and the categorical
    equivalence former `equivForm (lhs rhs)` (= `lhs ≅ rhs`).  Mirrors `gen_universeCode` / `gen_idCode` /
    `gen_equivCode`.
  * **`ContextUnivStep`** — the reduction relation, whose root rule
    `univalence : idForm universeObj A B ↝ equivForm A B` IS the `Id_U ↝ Equiv` reduction, plus congruence.
  * **`ContextUnivCode.normalize`** — the structural normalizer realizing the reduction (the Axis analog of
    the Core `normalizeOverTable`); the universe-Id redex fires via the smart constructor `reassembleId`.
  * **`ContextUnivStep.size_lt` + `isStronglyNormalizing`** — STRONG NORMALIZATION: every step strictly
    decreases `ContextUnivCode.size` (the rule drops the `universeObj` scrutinee), fed to a structural fuel
    accessibility argument (no `WellFounded.fix`).  The `type-7` SN-as-data, self-contained.
  * **`normalize_hasNoUnivalenceRedex`** — CANONICITY: a normalized code has NO `Id_U` redex left; the
    universe-identity former is fully eliminated.
  * **`Conv` + the `Decidable` instance** — DECIDABLE CONVERSION by normalize-and-compare.
  * **`contextDefinitionalUnivalence`** — ★ the payoff: `Id_U(A, B)` and `Equiv(A, B)` are CONVERTIBLE, and
    in fact their normal forms are EQUAL BY `rfl` (`idOverUniverseObject_normalize_eq`).  Definitional
    univalence at the context category: the identity-to-equivalence comparison is the reduction itself.

## Bridge to `context-30`

`definitionalUnivalence_idToIso` feeds the `rfl`-equality of normalized `Id_U(A,B)` and `Equiv(A,B)` into
`context-30`'s `idToIso`, producing the categorical iso that identifies them in the (univalent, set-level)
`discreteUniverseObject`.  This is `context-30`'s categorical univalence (CUA) realized BY COMPUTATION via the
`context-31` reduction — the universe object's identity and equivalence types are definitionally the same
object.

## Honesty

  * The reduction is the SELF-CONTAINED Axis analog of the Core table-native `type-7` row; it is NOT literally
    `univalenceShapedDemoRule` over `StepOverTable` (`fxContextDefinitionalUnivalence_isOverCoreIotaTable =
    false`).  The two agree in shape (drop the universe scrutinee, size-decreasing, decidable conversion); the
    Core/Axis gluing is cross-axis `×type`.
  * This is DEFINITIONAL / CATEGORICAL univalence (the funext-free fragment, `context-30`), NOT the univalence
    axiom; see `ContextUnivalentUniverse.lean`.

Imports only `ContextUnivalentUniverse` (its `context-30` sibling).  Zero external dependencies — raw Lean 4 +
Init only.

Reference: the `type-7` `Id_U ↝ Equiv` row (`Core/Substrate/Univalence/UnivalenceTableDecidableConv.lean`);
Cavallo & Höfer, "Univalence without function extensionality", MFPS 2026, arXiv:2605.00812.
-/

namespace FX1Poly.Axis

/-! ## The context-universe code algebra -/

/-- A **context-universe code**: the universe object, opaque type codes, the identity former, and the
categorical-equivalence former.  This is the small self-contained algebra over which the `Id_U ↝ Equiv`
reduction is shipped (mirroring the `gen_universeCode` / `gen_idCode` / `gen_equivCode` generators the Core
`type-7` row rewrites). -/
inductive ContextUnivCode where
  /-- The universe object `U` of the context category (the `gen_universeCode` analog). -/
  | universeObj
  /-- An opaque type code / type-in-context (a morphism into the universe object). -/
  | atom (index : Nat)
  /-- The identity former `Id_scrutinee(lhs, rhs)` (the `gen_idCode` analog). -/
  | idForm (scrutinee lhs rhs : ContextUnivCode)
  /-- The categorical-equivalence former `lhs ≅ rhs` (the `gen_equivCode` analog). -/
  | equivForm (lhs rhs : ContextUnivCode)
  deriving DecidableEq

/-- Is this code the universe object?  The head test the `Id_U` redex fires on (mirrors the `type-7` row
pinning slot-0's head to `gen_universeCode`). -/
def ContextUnivCode.headIsUniverseObj : ContextUnivCode → Bool
  | .universeObj => true
  | .atom _ => false
  | .idForm _ _ _ => false
  | .equivForm _ _ => false

/-- The smart identity constructor on already-normalized children: when the (normalized) scrutinee is the
universe object, FIRE the univalence reduction `Id_U(lhs, rhs) ↝ lhs ≅ rhs`; otherwise rebuild the identity
former.  This is the operational core of the `Id_U ↝ Equiv` reduction. -/
def ContextUnivCode.reassembleId (normScrutinee normLhs normRhs : ContextUnivCode) : ContextUnivCode :=
  match normScrutinee with
  | .universeObj => .equivForm normLhs normRhs
  | .atom index => .idForm (.atom index) normLhs normRhs
  | .idForm innerScrutinee innerLhs innerRhs =>
      .idForm (.idForm innerScrutinee innerLhs innerRhs) normLhs normRhs
  | .equivForm innerLhs innerRhs => .idForm (.equivForm innerLhs innerRhs) normLhs normRhs

/-- The structural normalizer realizing the `Id_U ↝ Equiv` reduction (the Axis analog of `type-7`'s
table-native `normalizeOverTable`): normalize the children, then fire the universe-Id redex via
`reassembleId`.  Structural recursion — zero-axiom, no `WellFounded.fix`. -/
def ContextUnivCode.normalize : ContextUnivCode → ContextUnivCode
  | .universeObj => .universeObj
  | .atom index => .atom index
  | .equivForm lhs rhs => .equivForm lhs.normalize rhs.normalize
  | .idForm scrutinee lhs rhs => ContextUnivCode.reassembleId scrutinee.normalize lhs.normalize rhs.normalize

/-- Does this code still contain an unfired `Id_U(_, _)` redex (an `idForm` whose scrutinee is the universe
object)?  The canonicity yardstick: a normal form has none. -/
def ContextUnivCode.hasUnivalenceRedex : ContextUnivCode → Bool
  | .universeObj => false
  | .atom _ => false
  | .equivForm lhs rhs => lhs.hasUnivalenceRedex || rhs.hasUnivalenceRedex
  | .idForm scrutinee lhs rhs =>
      scrutinee.headIsUniverseObj || scrutinee.hasUnivalenceRedex
        || lhs.hasUnivalenceRedex || rhs.hasUnivalenceRedex

/-- The size measure — the SN witness's yardstick (mirrors `RawTerm.size`).  The univalence rule drops the
`universeObj` scrutinee, so it strictly shrinks this. -/
def ContextUnivCode.size : ContextUnivCode → Nat
  | .universeObj => 1
  | .atom _ => 1
  | .equivForm lhs rhs => 1 + lhs.size + rhs.size
  | .idForm scrutinee lhs rhs => 1 + scrutinee.size + lhs.size + rhs.size

/-! ## Definitional univalence: `Id_U(A, B)` and `Equiv(A, B)` have the SAME normal form, by `rfl` -/

/-- ★ **Definitional univalence (the `rfl` core).**  The normal form of `Id_U(A, B)` IS the normal form of
`Equiv(A, B)` — by `rfl`.  `normalize (idForm universeObj A B)` fires `reassembleId universeObj … = equivForm
A.norm B.norm = normalize (equivForm A B)`.  The identity former at the universe object computes to the
equivalence former: univalence holds definitionally, mirroring `type-7`. -/
theorem ContextUnivCode.idOverUniverseObject_normalize_eq (codeLeft codeRight : ContextUnivCode) :
    (ContextUnivCode.idForm .universeObj codeLeft codeRight).normalize
      = (ContextUnivCode.equivForm codeLeft codeRight).normalize :=
  rfl

/-! ## Canonicity: a normalized code has no `Id_U` redex left -/

/-- The smart constructor preserves redex-freedom: if the normalized children are redex-free, so is the
reassembled identity former.  When the scrutinee is the universe object the result is an `equivForm` (no
`idForm` head at all); otherwise the rebuilt `idForm` has a non-universe scrutinee. -/
theorem ContextUnivCode.reassembleId_hasNoUnivalenceRedex
    {normScrutinee normLhs normRhs : ContextUnivCode}
    (scrutineeRedexFree : normScrutinee.hasUnivalenceRedex = false)
    (lhsRedexFree : normLhs.hasUnivalenceRedex = false)
    (rhsRedexFree : normRhs.hasUnivalenceRedex = false) :
    (ContextUnivCode.reassembleId normScrutinee normLhs normRhs).hasUnivalenceRedex = false := by
  cases normScrutinee with
  | universeObj =>
      show (normLhs.hasUnivalenceRedex || normRhs.hasUnivalenceRedex) = false
      rw [lhsRedexFree, rhsRedexFree]; rfl
  | atom index =>
      show ((ContextUnivCode.atom index).headIsUniverseObj
            || (ContextUnivCode.atom index).hasUnivalenceRedex
            || normLhs.hasUnivalenceRedex || normRhs.hasUnivalenceRedex) = false
      rw [lhsRedexFree, rhsRedexFree]; rfl
  | idForm innerScrutinee innerLhs innerRhs =>
      show ((ContextUnivCode.idForm innerScrutinee innerLhs innerRhs).headIsUniverseObj
            || (ContextUnivCode.idForm innerScrutinee innerLhs innerRhs).hasUnivalenceRedex
            || normLhs.hasUnivalenceRedex || normRhs.hasUnivalenceRedex) = false
      rw [scrutineeRedexFree, lhsRedexFree, rhsRedexFree]; rfl
  | equivForm innerLhs innerRhs =>
      show ((ContextUnivCode.equivForm innerLhs innerRhs).headIsUniverseObj
            || (ContextUnivCode.equivForm innerLhs innerRhs).hasUnivalenceRedex
            || normLhs.hasUnivalenceRedex || normRhs.hasUnivalenceRedex) = false
      rw [scrutineeRedexFree, lhsRedexFree, rhsRedexFree]; rfl

/-- ★ **Canonicity.**  Every normalized code is `Id_U`-redex-free: the universe-identity former is fully
eliminated by `normalize`.  This is the context-level mirror of `type-7`'s "the normalizer eliminates the
univalence redex" — the reduction is complete. -/
theorem ContextUnivCode.normalize_hasNoUnivalenceRedex (code : ContextUnivCode) :
    code.normalize.hasUnivalenceRedex = false := by
  induction code with
  | universeObj => rfl
  | atom index => rfl
  | equivForm lhs rhs lhsRedexFree rhsRedexFree =>
      show (lhs.normalize.hasUnivalenceRedex || rhs.normalize.hasUnivalenceRedex) = false
      rw [lhsRedexFree, rhsRedexFree]; rfl
  | idForm scrutinee lhs rhs scrutineeRedexFree lhsRedexFree rhsRedexFree =>
      show (ContextUnivCode.reassembleId scrutinee.normalize lhs.normalize rhs.normalize).hasUnivalenceRedex
            = false
      exact ContextUnivCode.reassembleId_hasNoUnivalenceRedex scrutineeRedexFree lhsRedexFree rhsRedexFree

/-! ## The reduction relation and strong normalization -/

/-- The **`Id_U ↝ Equiv` reduction relation** at the context category.  Its root rule `univalence` IS the
definitional-univalence reduction `Id_U(A, B) ↝ A ≅ B`; the remaining rules are congruence.  This is the
context-level mirror of the Core `univalenceShapedDemoRule` row. -/
inductive ContextUnivStep : ContextUnivCode → ContextUnivCode → Prop
  /-- ★ The univalence reduction: the identity former at the universe object reduces to the equivalence
  former. -/
  | univalence (lhs rhs : ContextUnivCode) :
      ContextUnivStep (.idForm .universeObj lhs rhs) (.equivForm lhs rhs)
  /-- Congruence in the identity former's scrutinee. -/
  | idScrutinee {scrutinee scrutinee' : ContextUnivCode} (lhs rhs : ContextUnivCode) :
      ContextUnivStep scrutinee scrutinee' →
      ContextUnivStep (.idForm scrutinee lhs rhs) (.idForm scrutinee' lhs rhs)
  /-- Congruence in the identity former's left argument. -/
  | idLhs (scrutinee : ContextUnivCode) {lhs lhs' : ContextUnivCode} (rhs : ContextUnivCode) :
      ContextUnivStep lhs lhs' →
      ContextUnivStep (.idForm scrutinee lhs rhs) (.idForm scrutinee lhs' rhs)
  /-- Congruence in the identity former's right argument. -/
  | idRhs (scrutinee lhs : ContextUnivCode) {rhs rhs' : ContextUnivCode} :
      ContextUnivStep rhs rhs' →
      ContextUnivStep (.idForm scrutinee lhs rhs) (.idForm scrutinee lhs rhs')
  /-- Congruence in the equivalence former's left argument. -/
  | equivLhs {lhs lhs' : ContextUnivCode} (rhs : ContextUnivCode) :
      ContextUnivStep lhs lhs' →
      ContextUnivStep (.equivForm lhs rhs) (.equivForm lhs' rhs)
  /-- Congruence in the equivalence former's right argument. -/
  | equivRhs (lhs : ContextUnivCode) {rhs rhs' : ContextUnivCode} :
      ContextUnivStep rhs rhs' →
      ContextUnivStep (.equivForm lhs rhs) (.equivForm lhs rhs')

/-- ★ **Every reduction step strictly decreases `size`.**  The univalence root rule drops the `universeObj`
scrutinee — its reduct is the redex with the universe head removed, strictly smaller — and congruence is
monotone.  The `type-7` SN-as-data size-drop, self-contained. -/
theorem ContextUnivStep.size_lt {codeA codeB : ContextUnivCode}
    (step : ContextUnivStep codeA codeB) : codeB.size < codeA.size := by
  induction step with
  | univalence lhs rhs =>
      exact Nat.add_lt_add_right (Nat.add_lt_add_right (Nat.lt_succ_self 1) lhs.size) rhs.size
  | idScrutinee lhs rhs _ scrutineeDrop =>
      exact Nat.add_lt_add_right
        (Nat.add_lt_add_right (Nat.add_lt_add_left scrutineeDrop 1) lhs.size) rhs.size
  | idLhs scrutinee rhs _ lhsDrop =>
      exact Nat.add_lt_add_right (Nat.add_lt_add_left lhsDrop (1 + scrutinee.size)) rhs.size
  | idRhs scrutinee lhs _ rhsDrop =>
      exact Nat.add_lt_add_left rhsDrop (1 + scrutinee.size + lhs.size)
  | equivLhs rhs _ lhsDrop =>
      exact Nat.add_lt_add_right (Nat.add_lt_add_left lhsDrop 1) rhs.size
  | equivRhs lhs _ rhsDrop =>
      exact Nat.add_lt_add_left rhsDrop (1 + lhs.size)

/-- Accessibility from a size bound, by structural recursion on the fuel `Nat` — the zero-axiom SN engine
(no `WellFounded.fix`): a code whose size is below the fuel is accessible under the (reversed) reduction. -/
theorem ContextUnivCode.accessibleUnderStep_ofSizeBelow :
    ∀ (fuel : Nat) (code : ContextUnivCode), code.size < fuel →
      Acc (fun reduct redex => ContextUnivStep redex reduct) code
  | 0, _, sizeBelowZero => absurd sizeBelowZero (Nat.not_lt_zero _)
  | fuel + 1, code, sizeBelow =>
      Acc.intro code (fun reduct stepWitness =>
        ContextUnivCode.accessibleUnderStep_ofSizeBelow fuel reduct
          (Nat.lt_of_lt_of_le (ContextUnivStep.size_lt stepWitness) (Nat.le_of_lt_succ sizeBelow)))

/-- ★ **Strong normalization.**  Every code is accessible under the reduction — no infinite `Id_U ↝ Equiv`
reduction sequence — by the size-drop fed to the structural fuel argument.  RPO-free, Tait-free: the
univalence rule shrinks `size`, exactly as `type-7`'s `univalenceTable_isStronglyNormalizing`. -/
theorem ContextUnivCode.isStronglyNormalizing (code : ContextUnivCode) :
    Acc (fun reduct redex => ContextUnivStep redex reduct) code :=
  ContextUnivCode.accessibleUnderStep_ofSizeBelow (code.size + 1) code (Nat.lt_succ_self _)

/-! ## Decidable conversion -/

/-- Conversion: two codes are convertible when they share a normal form.  Decidable by normalize-and-compare
(the generic `type-7` crank, self-contained). -/
def ContextUnivCode.Conv (codeA codeB : ContextUnivCode) : Prop :=
  codeA.normalize = codeB.normalize

instance ContextUnivCode.Conv.decidable (codeA codeB : ContextUnivCode) :
    Decidable (ContextUnivCode.Conv codeA codeB) :=
  inferInstanceAs (Decidable (codeA.normalize = codeB.normalize))

/-- Conversion is reflexive. -/
theorem ContextUnivCode.Conv.refl (code : ContextUnivCode) : ContextUnivCode.Conv code code := rfl

/-- Conversion is symmetric. -/
theorem ContextUnivCode.Conv.symm {codeA codeB : ContextUnivCode}
    (convAB : ContextUnivCode.Conv codeA codeB) : ContextUnivCode.Conv codeB codeA :=
  Eq.symm convAB

/-- Conversion is transitive. -/
theorem ContextUnivCode.Conv.trans {codeA codeB codeC : ContextUnivCode}
    (convAB : ContextUnivCode.Conv codeA codeB) (convBC : ContextUnivCode.Conv codeB codeC) :
    ContextUnivCode.Conv codeA codeC :=
  Eq.trans convAB convBC

/-- ★ **Definitional univalence at the context category.**  `Id_U(A, B)` and `Equiv(A, B)` are CONVERTIBLE —
indeed their normal forms are equal by `rfl`.  The identity-to-equivalence comparison at the universe object
IS the reduction.  This is the context-level `type-7`. -/
theorem ContextUnivCode.contextDefinitionalUnivalence (codeLeft codeRight : ContextUnivCode) :
    ContextUnivCode.Conv (.idForm .universeObj codeLeft codeRight) (.equivForm codeLeft codeRight) :=
  ContextUnivCode.idOverUniverseObject_normalize_eq codeLeft codeRight

/-- The univalence rule is a genuine step of the reduction relation — the reduction-relation witness behind
the definitional convertibility above. -/
theorem ContextUnivCode.univalenceRule_reduces (codeLeft codeRight : ContextUnivCode) :
    ContextUnivStep (.idForm .universeObj codeLeft codeRight) (.equivForm codeLeft codeRight) :=
  ContextUnivStep.univalence codeLeft codeRight

/-! ## Bridge to context-30: the reduction REALIZES categorical univalence -/

/-- Bridge to `context-30`: the categorical iso identifying normalized `Id_U(A, B)` with normalized
`Equiv(A, B)` in the (univalent, set-level) `discreteUniverseObject`, produced by feeding the definitional
`rfl`-equality of their normal forms into `context-30`'s `idToIso`.  This is categorical univalence (CUA,
`context-30`) realized BY COMPUTATION (`context-31`): in the universe object, the identity and equivalence
types of `A, B` are the SAME object, so `idToIso` connects them by the identity iso. -/
def definitionalUnivalence_idToIso (codeLeft codeRight : ContextUnivCode) :
    CategoryIso (discreteUniverseObject ContextUnivCode)
      ((ContextUnivCode.idForm .universeObj codeLeft codeRight).normalize)
      ((ContextUnivCode.equivForm codeLeft codeRight).normalize) :=
  idToIso (discreteUniverseObject ContextUnivCode)
    (ContextUnivCode.idOverUniverseObject_normalize_eq codeLeft codeRight)

/-! ## Honesty markers -/

/-- **Honesty marker.**  The `Id_U ↝ Equiv` reduction at the context category is shipped, with its definitional
univalence (`Id_U(A,B)` and `Equiv(A,B)` share a normal form by `rfl`).  `= true`. -/
def fxContextDefinitionalUnivalence_idReducesToEquiv : Bool := true

/-- **Honesty marker.**  Strong normalization (size-drop) + canonicity + DECIDABLE conversion are shipped for
the context-level univalence reduction.  `= true`. -/
def fxContextDefinitionalUnivalence_hasDecidableConversion : Bool := true

/-- **Honesty marker.**  This is the SELF-CONTAINED Axis analog of the Core table-native `type-7` row
`univalenceShapedDemoRule` (over `StepOverTable`, with generic orthogonal-table confluence).  A Axis
design-lock cannot import the Core engine, so the reduction is re-shipped here as a structural normalizer; the
two agree in shape (drop the universe scrutinee, size-decreasing, decidable conversion).  Gluing the Axis and
Core forms is cross-axis `×type`.  `= false`. -/
def fxContextDefinitionalUnivalence_isOverCoreIotaTable : Bool := false

/-! ## Smoke -/

/-- Smoke: `Id_U(atom 0, atom 1)` is convertible to `atom 0 ≅ atom 1` — the univalence reduction decided by
computation. -/
theorem contextDefinitionalUnivalence_smoke :
    ContextUnivCode.Conv
      (.idForm .universeObj (.atom 0) (.atom 1))
      (.equivForm (.atom 0) (.atom 1)) :=
  ContextUnivCode.contextDefinitionalUnivalence (.atom 0) (.atom 1)

end FX1Poly.Axis
