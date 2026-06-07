import FX0Poly.CertSerialize

/-!
# FX0Poly — the binary certificate parser (.fx0c decoder + round-trip)

`CertSerialize` ships the `.fx0c` SERIALIZER (`Cert.encode`, a self-delimiting flat `List Nat`) and its
injectivity.  This file ships the PARSER half: a total `Cert` decoder plus the ROUND-TRIP theorem
`Cert.decode_encode` — decoding an encoded certificate recovers it EXACTLY.  Together they make the
`.fx0c` format faithful in both directions: the external verifier serializes, transmits, and re-parses
the same certificate the rich `FX1Poly` kernel emitted.

## Structural fuel — why the decoder reduces and stays zero-axiom

A flat parser's recursion is NOT structural on the input list (children consume an unknown prefix), so a
naive decoder needs well-founded recursion — but `WellFounded.fix` pulls `propext` + `Quot.sound` AND does
not reduce by `rfl` (no computing smokes).  Instead the decoder is STRUCTURAL ON A FUEL `Nat`: every
recursive call (including per-child in `decodeChildren`) decrements the fuel by one, so the definition
compiles to plain `Nat` recursors — propext-free and `rfl`-computing.  The cost is a slightly larger fuel
requirement, captured by `Cert.budget` (a SUM-based measure — `+1` per decode step — so the round-trip's
fuel bookkeeping uses only `Nat.le_add_left` / `Nat.le_add_right`, never the propext-tainted `Nat.max`).

  * `Cert.decode` / `Cert.decodeChildren` — the structural fuel decoder; `none` on exhaustion or malformed
    input, `some (cert, remaining)` on success.
  * `Cert.budget` / `Cert.childrenBudget` — the sum-based fuel measure: enough fuel to decode the tree.
  * `Cert.decode_encodeAux` / `Cert.decodeChildren_encodeChildrenAux` — the mutual round-trip lemma:
    decoding `encodeAux cert suffix` at sufficient fuel returns `(cert, suffix)` — it recovers the
    certificate AND leaves the trailing `suffix` untouched (the self-delimiting property, computationally).
  * **`Cert.decode_encode`** — the headline: `Cert.decode cert.budget (Cert.encode cert) = some (cert, [])`.
    Encode then decode is the identity (up to the empty remainder); the `.fx0c` round-trip holds.

## Zero-axiom verification

The decoder is structural mutual recursion on the fuel `Nat`; `budget` is structural on `Cert`; the
round-trip is mutual structural recursion closing each node by `dsimp only` (def unfolding) + `rw` (the
recursive round-trips) + `dsimp only []` (match-on-`some` iota), with the fuel destructured by `cases` and
the sum bounds discharged by `Nat.le_of_succ_le_succ` / `Nat.le_add_left` / `Nat.le_add_right` /
`Nat.le_trans`.  No `List.append`, no `Nat.max`, no `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, or `omega`.  Gated per-declaration in `FX1PolyAudit/AuditFX0Poly.lean`.
-/

namespace FX0Poly

mutual
  /-- The structural fuel decoder: parse one certificate from the flat stream.  `0` fuel or a stream too
  short to hold a `tag :: childCount :: …` header yields `none`; otherwise read the tag and child count and
  decode that many children, returning the certificate and the unconsumed remainder.  Structural on the
  fuel `Nat` (every recursive call decrements it) so it reduces by `rfl` and stays propext-free. -/
  def Cert.decode : Nat → List Nat → Option (Cert × List Nat)
    | 0, _ => none
    | _ + 1, [] => none
    | _ + 1, [_] => none
    | fuel + 1, tag :: childCount :: rest =>
        match Cert.decodeChildren fuel childCount rest with
        | some (children, remaining) => some (Cert.node tag children, remaining)
        | none => none
  /-- Decode `count` consecutive child certificates from the stream, threading the remainder.  `count = 0`
  returns the empty list and the input untouched; otherwise decode one child (at the decremented fuel) then
  the rest.  Mutually structural-on-fuel with `decode`. -/
  def Cert.decodeChildren : Nat → Nat → List Nat → Option (List Cert × List Nat)
    | _, 0, input => some ([], input)
    | 0, _ + 1, _ => none
    | fuel + 1, count + 1, input =>
        match Cert.decode fuel input with
        | some (child, rest) =>
            match Cert.decodeChildren fuel count rest with
            | some (children, remaining) => some (child :: children, remaining)
            | none => none
        | none => none
end

/-- Concrete decode: the self-delimiting stream `[2,2,0,0,1,0]` (the `Cert.encode_smoke` bytes) decodes,
at sufficient fuel, back to the Π-code certificate over a variable and a universe code. -/
theorem Cert.decode_smoke :
    Cert.decode 6 [2, 2, 0, 0, 1, 0] = some (.node 2 [.node 0 [], .node 1 []], []) := rfl

mutual
  /-- The fuel a certificate needs to decode: `childrenBudget + 1` (the `+1` is the node's own decode
  step).  A SUM-based measure (so the round-trip avoids the propext-tainted `Nat.max`). -/
  def Cert.budget : Cert → Nat
    | .node _ children => Cert.childrenBudget children + 1
  /-- The fuel a child list needs: each child's budget plus a `+1` per child (the per-child decode step). -/
  def Cert.childrenBudget : List Cert → Nat
    | [] => 0
    | cert :: rest => Cert.budget cert + Cert.childrenBudget rest + 1
end

mutual
  /-- **The serializer/parser round-trip (threaded form).**  At sufficient fuel, decoding `encodeAux cert
  suffix` returns the original `cert` AND the untouched trailing `suffix`: the decoder consumes EXACTLY the
  certificate's bytes, leaving everything after it intact (the self-delimiting property, computationally).
  Mutually structural with the child-list version; each node destructures the fuel, recovers the children
  via the child round-trip, and reduces the decoder by `dsimp` + `rw`. -/
  theorem Cert.decode_encodeAux : ∀ (cert : Cert) (suffix : List Nat) (fuel : Nat),
      Cert.budget cert ≤ fuel →
      Cert.decode fuel (Cert.encodeAux cert suffix) = some (cert, suffix)
    | .node tag children, suffix, fuel, hBudget => by
        cases fuel with
        | zero => exact absurd hBudget (Nat.not_succ_le_zero _)
        | succ budgetMinus =>
            have hChildren : Cert.childrenBudget children ≤ budgetMinus :=
              Nat.le_of_succ_le_succ hBudget
            have childrenRoundTrip :=
              Cert.decodeChildren_encodeChildrenAux children suffix budgetMinus hChildren
            dsimp only [Cert.encodeAux, Cert.decode]
            rw [childrenRoundTrip]
  /-- The child-list companion: at sufficient fuel, decoding `encodeChildrenAux children suffix` for
  `children.length` children returns the children and the untouched `suffix`.  The sum budget gives each
  recursive call its fuel via `Nat.le_add_left` / `Nat.le_add_right` (no `Nat.max`). -/
  theorem Cert.decodeChildren_encodeChildrenAux :
      ∀ (children : List Cert) (suffix : List Nat) (fuel : Nat),
        Cert.childrenBudget children ≤ fuel →
        Cert.decodeChildren fuel children.length (Cert.encodeChildrenAux children suffix)
          = some (children, suffix)
    | [], suffix, fuel, _ => by cases fuel <;> rfl
    | (cert :: rest), suffix, fuel, hBudget => by
        cases fuel with
        | zero => exact absurd hBudget (Nat.not_succ_le_zero _)
        | succ budgetMinus =>
            have hSum : Cert.budget cert + Cert.childrenBudget rest ≤ budgetMinus :=
              Nat.le_of_succ_le_succ hBudget
            have hHead : Cert.budget cert ≤ budgetMinus :=
              Nat.le_trans (Nat.le_add_right _ _) hSum
            have hRest : Cert.childrenBudget rest ≤ budgetMinus :=
              Nat.le_trans (Nat.le_add_left _ _) hSum
            have headRoundTrip :=
              Cert.decode_encodeAux cert (Cert.encodeChildrenAux rest suffix) budgetMinus hHead
            have restRoundTrip :=
              Cert.decodeChildren_encodeChildrenAux rest suffix budgetMinus hRest
            show Cert.decodeChildren (budgetMinus + 1) (rest.length + 1)
                (Cert.encodeAux cert (Cert.encodeChildrenAux rest suffix)) = some (cert :: rest, suffix)
            dsimp only [Cert.decodeChildren]
            rw [headRoundTrip]
            dsimp only []
            rw [restRoundTrip]
end

/-- ★ **The `.fx0c` round-trip: encode then decode is the identity.**  `Cert.decode cert.budget
(Cert.encode cert) = some (cert, [])` — serializing a certificate and re-parsing it (at the certificate's
own fuel budget) recovers it exactly, with no leftover bytes.  Together with `Cert.encode_injective`
(distinct certificates have distinct bytes), the format is a faithful bijection between certificates and
their `.fx0c` byte streams — the external verifier and the rich kernel agree on exactly one certificate per
encoding. -/
theorem Cert.decode_encode (cert : Cert) :
    Cert.decode cert.budget (Cert.encode cert) = some (cert, []) :=
  Cert.decode_encodeAux cert [] cert.budget (Nat.le_refl _)

end FX0Poly
