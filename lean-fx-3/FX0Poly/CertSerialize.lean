import FX0Poly.CertRecheck

/-!
# FX0Poly — the binary certificate serializer (.fx0c flat encoding)

`CertRecheck` defines the certificate tree `Cert` the minimal checker re-checks.  This file ships the
SERIALIZER half of the `.fx0c` binary certificate format: a flat, SELF-DELIMITING `List Nat` encoding of a
`Cert`, with the key soundness property a serialization format must have — INJECTIVITY: distinct
certificates have distinct byte streams, so the external verifier reading the bytes recovers a UNIQUE
certificate (an unambiguous decoder exists).

Format: a node emits its `tag`, then its `childCount`, then its children's encodings in order.  The
`childCount` prefix makes the stream self-delimiting (a decoder knows how many children to read).  The
encoder is written in DIFFERENCE-LIST (accumulator-threaded) style — `encodeAux cert acc` prepends `cert`'s
bytes onto `acc` using only `::` — so the format is built WITHOUT `List.append`, whose core lemmas
(`List.append_assoc` / `List.append_nil`) are NOT propext-free in core Lean; the cons-only encoding keeps the
whole serializer and its injectivity proof zero-axiom.

  * `Cert.encodeAux` / `Cert.encodeChildrenAux` / `Cert.encode` — the difference-list serializer and the
    top-level `encode cert := encodeAux cert []`.
  * `Cert.encodeAux_inj` / `Cert.encodeChildrenAux_inj` — the threaded-accumulator INJECTIVITY: equal
    encodings (at equal accumulators) force equal certificates AND equal accumulators.  The accumulator IS
    the decoder's "remaining input", so this is exactly the self-delimiting / prefix-free property — the
    encoder cannot smear a certificate's bytes into the following stream.
  * **`Cert.encode_injective`** — the headline: `encode cert1 = encode cert2 → cert1 = cert2`.  The `.fx0c`
    format is injective; the external verifier can unambiguously recover the certified tree from its bytes.

The DECODER (parser) half + the round-trip (`decode (encode cert) = cert`) is the deferred follow-up: it
needs either well-founded recursion on the input length (with a "decode shrinks the input" lemma) or a fuel
parameter with fuel-monotonicity — neither needed for injectivity, which the difference-list structure gives
directly.

## Zero-axiom verification

Everything is structural: the serializer is mutual structural recursion over `Cert` / `List Cert`; the
injectivity is the same mutual recursion, closing each node by `injection` (cons / `Nat` constructor
injectivity) and each length mismatch by `Nat.noConfusion` — no `List.append`, no `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, or `omega`.  Gated per-declaration in
`FX1PolyAudit/AuditFX0Poly.lean`.
-/

namespace FX0Poly

mutual
  /-- The difference-list serializer core: prepend `cert`'s flat encoding onto `acc` (the bytes that
  follow).  A node emits `tag :: childCount :: <children's bytes, then acc>`.  Accumulator-threaded (only
  `::`, never `++`) so the encoder avoids `List.append` (whose core lemmas are not propext-free). -/
  def Cert.encodeAux : Cert → List Nat → List Nat
    | .node tag children, acc => tag :: children.length :: Cert.encodeChildrenAux children acc
  /-- Serialize a list of child certificates, threading the accumulator: each child's bytes are prepended
  onto the encoding of the rest (then `acc`).  Mutually structural with `encodeAux`. -/
  def Cert.encodeChildrenAux : List Cert → List Nat → List Nat
    | [], acc => acc
    | cert :: rest, acc => Cert.encodeAux cert (Cert.encodeChildrenAux rest acc)
end

/-- The `.fx0c` flat encoding of a certificate: its difference-list serialization onto the empty tail.
Self-delimiting (each node carries its child count), so a decoder can recover the tree structure. -/
def Cert.encode (cert : Cert) : List Nat := Cert.encodeAux cert []

mutual
  /-- **Threaded-accumulator injectivity of the serializer.**  If `cert1` and `cert2` encode to the same
  bytes ON TOP OF accumulators `acc1` and `acc2`, then the certificates are equal AND the accumulators are
  equal.  The accumulator is the decoder's remaining input, so this says the encoding is SELF-DELIMITING: a
  certificate's bytes cannot be confused with — or smeared into — the bytes that follow.  Mutually
  structural with the child-list version; each node closes by `injection` on the `tag :: childCount :: …`
  cons structure. -/
  theorem Cert.encodeAux_inj :
      ∀ (firstCert secondCert : Cert) (firstAcc secondAcc : List Nat),
        Cert.encodeAux firstCert firstAcc = Cert.encodeAux secondCert secondAcc →
        firstCert = secondCert ∧ firstAcc = secondAcc
    | .node firstTag firstChildren, .node secondTag secondChildren, firstAcc, secondAcc => by
        intro hEq
        dsimp only [Cert.encodeAux] at hEq
        injection hEq with tagEq hEqTail
        injection hEqTail with lenEq restEq
        obtain ⟨childrenEq, accEq⟩ :=
          Cert.encodeChildrenAux_inj firstChildren secondChildren firstAcc secondAcc lenEq restEq
        exact ⟨by rw [tagEq, childrenEq], accEq⟩
  /-- The child-list companion: at EQUAL child counts, equal threaded encodings force equal child lists and
  equal accumulators.  The length hypothesis (recovered from the parent's `childCount` prefix) rules out the
  empty-vs-nonempty mismatches; the cons case peels one child via `encodeAux_inj` then recurses. -/
  theorem Cert.encodeChildrenAux_inj :
      ∀ (firstChildren secondChildren : List Cert) (firstAcc secondAcc : List Nat),
        firstChildren.length = secondChildren.length →
        Cert.encodeChildrenAux firstChildren firstAcc
          = Cert.encodeChildrenAux secondChildren secondAcc →
        firstChildren = secondChildren ∧ firstAcc = secondAcc
    | [], [], _firstAcc, _secondAcc => by
        intro _ hEq
        dsimp only [Cert.encodeChildrenAux] at hEq
        exact ⟨rfl, hEq⟩
    | [], (_secondHead :: _secondRest), _firstAcc, _secondAcc => by
        intro hLen _; exact Nat.noConfusion hLen
    | (_firstHead :: _firstRest), [], _firstAcc, _secondAcc => by
        intro hLen _; exact Nat.noConfusion hLen
    | (firstHead :: firstRest), (secondHead :: secondRest), firstAcc, secondAcc => by
        intro hLen hEq
        dsimp only [Cert.encodeChildrenAux] at hEq
        obtain ⟨headEq, restAccEq⟩ :=
          Cert.encodeAux_inj firstHead secondHead _ _ hEq
        injection hLen with lenRest
        obtain ⟨restEq, accEq⟩ :=
          Cert.encodeChildrenAux_inj firstRest secondRest _ _ lenRest restAccEq
        exact ⟨by rw [headEq, restEq], accEq⟩
end

/-- ★ **The `.fx0c` certificate encoding is injective.**  Distinct certificates have distinct byte streams:
`encode cert1 = encode cert2 → cert1 = cert2`.  This is the soundness core of the binary format — an
external verifier reading the bytes recovers a UNIQUE certificate, with no ambiguity for the FX1Poly /
FX0Poly cross-check to resolve.  Immediate from `encodeAux_inj` at the empty accumulator. -/
theorem Cert.encode_injective {firstCert secondCert : Cert}
    (hEq : Cert.encode firstCert = Cert.encode secondCert) : firstCert = secondCert :=
  (Cert.encodeAux_inj firstCert secondCert [] [] hEq).1

/-- Concrete encoding: a Π-code certificate (`tag 2`) over a variable (`tag 0`) and a universe code
(`tag 1`) serializes to the self-delimiting flat stream `[2, 2, 0, 0, 1, 0]` (parent tag `2`, child count
`2`, then each child's `tag :: 0`). -/
theorem Cert.encode_smoke :
    Cert.encode (.node 2 [.node 0 [], .node 1 []]) = [2, 2, 0, 0, 1, 0] := rfl

/-- Non-vacuity: two distinct certificates have distinct encodings (so injectivity is not the vacuous claim
about an encoding that collapses everything). -/
theorem Cert.encode_distinguishes :
    Cert.encode (.node 0 []) ≠ Cert.encode (.node 1 []) := by decide

end FX0Poly
