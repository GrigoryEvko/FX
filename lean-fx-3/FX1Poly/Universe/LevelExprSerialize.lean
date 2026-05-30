import FX1Poly.Universe.LevelExpr

/-! # Foundation/PolyCell/Universe/LevelExprSerialize
   — prefix-code serializer for `LevelExpr` + round-trip

#432 (M24-Z1) deliverable (d), part 1: the `LevelExpr → List Nat`
serializer feeding the FX0 certificate format (polycell.md §3.16.17 /
§12.6.4), with a `decode ∘ encode = id` round-trip proof.  The
`UniverseFlag` serializer (part 2) and the payload-level integration land
in the subsequent #432 commits.

## Design — accumulator / difference-list encoding

`encodeOnto e acc` prepends `e`'s prefix code onto `acc`, so the
two-child constructors (`lmax`, `limax`) are pure NESTED calls with no
list concatenation:

```
encodeOnto (lmax left right) acc = 2 :: encodeOnto left (encodeOnto right acc)
```

This is deliberate.  A naive `2 :: encode left ++ encode right ++ acc`
form forces `List.append_assoc` into the round-trip proof, and core
Lean's `append`/`length` lemmas leak `propext` — this codebase already
had to reimplement `length_append` propext-free in
`LevelExprSimplify.lean`.  The accumulator form never concatenates, so
the round-trip closes by structural induction over `LevelExpr` alone:
zero core-`List` lemmas, zero axioms.

## Prefix tags

| ctor               | code                 |
| ------------------ | -------------------- |
| `lzero`            | `0 :: acc`           |
| `lsucc inner`      | `1 :: <inner>`       |
| `lmax left right`  | `2 :: <left><right>` |
| `limax left right` | `3 :: <left><right>` |
| `lvar index`       | `4 :: index :: acc`  |

Tags `≥ 5` and truncated inputs decode to `none`.

## Fuel

`decodeOnto` recurses with a `Nat` fuel bound (structural recursion on the
fuel, NOT well-founded recursion — whose generated equation lemmas are a
known propext source).  `nodeCount e` is exactly the fuel a single
expression needs, so the headline round-trip
`decodeOnto_nodeCount_encodePrefix` decodes at fuel `e.nodeCount` and the
sufficiency bound is `Nat.le_refl`.

A list-only wrapper (`decodePrefix input := decodeOnto input.length input`,
taking the input's own length as fuel) is a thin follow-up — its only
extra obligation is the length bound `nodeCount e ≤ (encodeOnto e []).length`,
deferred to keep this commit's arithmetic minimal and propext-clean.

## Propext discipline

`decodeOnto`'s nested-match equation lemmas leak `propext` when fed to
`simp`/`unfold`, and `simp only [encodeOnto]` does too.  The round-trip
therefore touches NEITHER: each non-leaf branch rewrites by a combined
`encode + decode` STEP LEMMA whose left-hand side is exactly the induction
goal's `decodeOnto (fuel+1) (ctor.encodeOnto acc)`, closing by `rfl`
(both reductions are definitional).  Inductive hypotheses then fire by
`rw`, and the only remaining match-on-`some` is collapsed by `dsimp only []`
(pure kernel iota).  All declarations audit-gated zero-axiom in
`FX1PolyAudit/AuditUniverse.lean`.
-/

namespace FX1Poly.Universe

/-- Node count of a level expression — the decoding fuel measure.  Each
constructor contributes one node plus its children's counts.  Kept local
to this file (the canonical `LevelExpr.size` lives in
`LevelExprSimplify.lean`; importing that 6 600-line module here just for a
fuel bound would invert the dependency order). -/
def LevelExpr.nodeCount : LevelExpr → Nat
  | .lzero            => 1
  | .lsucc inner      => inner.nodeCount + 1
  | .lmax left right  => left.nodeCount + right.nodeCount + 1
  | .limax left right => left.nodeCount + right.nodeCount + 1
  | .lvar _           => 1

/-- Prefix encoder in accumulator form: `encodeOnto e acc` is `e`'s prefix
code followed by `acc`.  No list concatenation occurs. -/
def LevelExpr.encodeOnto : LevelExpr → List Nat → List Nat
  | .lzero,            acc => 0 :: acc
  | .lsucc inner,      acc => 1 :: inner.encodeOnto acc
  | .lmax left right,  acc => 2 :: left.encodeOnto (right.encodeOnto acc)
  | .limax left right, acc => 3 :: left.encodeOnto (right.encodeOnto acc)
  | .lvar index,       acc => 4 :: index :: acc

/-- Top-level prefix encoder: `encodePrefix e = encodeOnto e []`. -/
def LevelExpr.encodePrefix (expr : LevelExpr) : List Nat :=
  expr.encodeOnto []

/-- Fuel-bounded prefix decoder.  Returns the decoded expression paired
with the unconsumed suffix, or `none` on malformed / fuel-exhausted input.
Structural recursion on the fuel argument. -/
def LevelExpr.decodeOnto : Nat → List Nat → Option (LevelExpr × List Nat)
  | 0,        _                  => none
  | _ + 1,    []                 => none
  | _ + 1,    0 :: rest          => some (.lzero, rest)
  | fuel + 1, 1 :: rest          =>
      match LevelExpr.decodeOnto fuel rest with
      | some (inner, rest1) => some (.lsucc inner, rest1)
      | none                => none
  | fuel + 1, 2 :: rest          =>
      match LevelExpr.decodeOnto fuel rest with
      | some (left, rest1) =>
        match LevelExpr.decodeOnto fuel rest1 with
        | some (right, rest2) => some (.lmax left right, rest2)
        | none                => none
      | none               => none
  | fuel + 1, 3 :: rest          =>
      match LevelExpr.decodeOnto fuel rest with
      | some (left, rest1) =>
        match LevelExpr.decodeOnto fuel rest1 with
        | some (right, rest2) => some (.limax left right, rest2)
        | none                => none
      | none               => none
  | _ + 1,    4 :: index :: rest => some (.lvar index, rest)
  | _ + 1,    4 :: []            => none
  | _ + 1,    (_ + 5) :: _       => none

/-! ## Combined encode-then-decode step lemmas

Each non-leaf constructor's decode-of-its-own-encoding reduces
DEFINITIONALLY (the encoder's head reduction picks the matching decoder
arm), so these equations close by `rfl` — propext-free.  Their left-hand
sides match the induction goal's shape exactly, so the round-trip proof
rewrites with them instead of `simp`ing the leaking equation lemmas. -/

/-- Decoding an `lsucc`-encoding peels the tag and recurses on the child. -/
theorem LevelExpr.decodeOnto_encodeOnto_lsucc
    (fuel : Nat) (inner : LevelExpr) (acc : List Nat) :
    LevelExpr.decodeOnto (fuel + 1) ((LevelExpr.lsucc inner).encodeOnto acc) =
      (match LevelExpr.decodeOnto fuel (inner.encodeOnto acc) with
       | some (decodedInner, residue) => some (.lsucc decodedInner, residue)
       | none                         => none) := rfl

/-- Decoding an `lmax`-encoding peels the tag and recurses on both
children, the second from the first's residue. -/
theorem LevelExpr.decodeOnto_encodeOnto_lmax
    (fuel : Nat) (left right : LevelExpr) (acc : List Nat) :
    LevelExpr.decodeOnto (fuel + 1) ((LevelExpr.lmax left right).encodeOnto acc) =
      (match LevelExpr.decodeOnto fuel (left.encodeOnto (right.encodeOnto acc)) with
       | some (decodedLeft, residue1) =>
         match LevelExpr.decodeOnto fuel residue1 with
         | some (decodedRight, residue2) => some (.lmax decodedLeft decodedRight, residue2)
         | none                          => none
       | none                         => none) := rfl

/-- Decoding an `limax`-encoding peels the tag and recurses on both
children, the second from the first's residue. -/
theorem LevelExpr.decodeOnto_encodeOnto_limax
    (fuel : Nat) (left right : LevelExpr) (acc : List Nat) :
    LevelExpr.decodeOnto (fuel + 1) ((LevelExpr.limax left right).encodeOnto acc) =
      (match LevelExpr.decodeOnto fuel (left.encodeOnto (right.encodeOnto acc)) with
       | some (decodedLeft, residue1) =>
         match LevelExpr.decodeOnto fuel residue1 with
         | some (decodedRight, residue2) => some (.limax decodedLeft decodedRight, residue2)
         | none                          => none
       | none                         => none) := rfl

/-! ## Round-trip soundness

`decodeOnto` left-inverts `encodeOnto` whenever the fuel covers the
expression's node count.  Proof: structural induction on the expression;
the step lemmas above expose each child decode, the inductive hypotheses
discharge them, and `dsimp only []` collapses the residual `match`-on-`some`
by iota. -/

/-- The fuel-parameterized round-trip: with fuel at least the node count,
decoding the accumulator-encoding recovers the expression and returns the
accumulator unchanged as residue. -/
theorem LevelExpr.decodeOnto_encodeOnto (expr : LevelExpr) :
    ∀ (fuel : Nat) (acc : List Nat),
      expr.nodeCount ≤ fuel →
      LevelExpr.decodeOnto fuel (expr.encodeOnto acc) = some (expr, acc) := by
  induction expr with
  | lzero =>
    intro fuel acc hFuel
    cases fuel with
    | zero => simp only [LevelExpr.nodeCount] at hFuel; exact absurd hFuel (Nat.not_succ_le_zero _)
    | succ fuelPred => rfl
  | lsucc inner ihInner =>
    intro fuel acc hFuel
    cases fuel with
    | zero => simp only [LevelExpr.nodeCount] at hFuel; exact absurd hFuel (Nat.not_succ_le_zero _)
    | succ fuelPred =>
      have hInner : inner.nodeCount ≤ fuelPred := by
        simp only [LevelExpr.nodeCount] at hFuel
        exact Nat.le_of_succ_le_succ hFuel
      rw [LevelExpr.decodeOnto_encodeOnto_lsucc, ihInner fuelPred acc hInner]
  | lmax left right ihLeft ihRight =>
    intro fuel acc hFuel
    cases fuel with
    | zero => simp only [LevelExpr.nodeCount] at hFuel; exact absurd hFuel (Nat.not_succ_le_zero _)
    | succ fuelPred =>
      simp only [LevelExpr.nodeCount] at hFuel
      have hLeft : left.nodeCount ≤ fuelPred :=
        Nat.le_of_succ_le_succ
          (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right left.nodeCount right.nodeCount)) hFuel)
      have hRight : right.nodeCount ≤ fuelPred :=
        Nat.le_of_succ_le_succ
          (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_left right.nodeCount left.nodeCount)) hFuel)
      rw [LevelExpr.decodeOnto_encodeOnto_lmax, ihLeft fuelPred (right.encodeOnto acc) hLeft]
      dsimp only []
      rw [ihRight fuelPred acc hRight]
  | limax left right ihLeft ihRight =>
    intro fuel acc hFuel
    cases fuel with
    | zero => simp only [LevelExpr.nodeCount] at hFuel; exact absurd hFuel (Nat.not_succ_le_zero _)
    | succ fuelPred =>
      simp only [LevelExpr.nodeCount] at hFuel
      have hLeft : left.nodeCount ≤ fuelPred :=
        Nat.le_of_succ_le_succ
          (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right left.nodeCount right.nodeCount)) hFuel)
      have hRight : right.nodeCount ≤ fuelPred :=
        Nat.le_of_succ_le_succ
          (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_left right.nodeCount left.nodeCount)) hFuel)
      rw [LevelExpr.decodeOnto_encodeOnto_limax, ihLeft fuelPred (right.encodeOnto acc) hLeft]
      dsimp only []
      rw [ihRight fuelPred acc hRight]
  | lvar index =>
    intro fuel acc hFuel
    cases fuel with
    | zero => simp only [LevelExpr.nodeCount] at hFuel; exact absurd hFuel (Nat.not_succ_le_zero _)
    | succ fuelPred => rfl

/-- Headline serializer round-trip: decoding `encodePrefix e` at fuel
`e.nodeCount` recovers `e` exactly, with empty residue.  The fuel
sufficiency is `Nat.le_refl` — no length estimate needed. -/
theorem LevelExpr.decodeOnto_nodeCount_encodePrefix (expr : LevelExpr) :
    LevelExpr.decodeOnto expr.nodeCount (expr.encodePrefix) = some (expr, []) := by
  simp only [LevelExpr.encodePrefix]
  exact LevelExpr.decodeOnto_encodeOnto expr expr.nodeCount [] (Nat.le_refl _)

end FX1Poly.Universe
