/-!
# FX0Poly — Metamath-Zero–flavored minimal checker (greenfield)

`FX0Poly` is the SMALL, independently-auditable verifier that re-checks the
certificates emitted by the rich `FX1Poly` kernel.  Its design philosophy is
that of Metamath Zero (Carneiro 2019): the trusted computing base is a tiny,
total, easily-auditable program — NOT the full elaborator.

Trust architecture:

```
  FX1Poly  (rich Lean kernel, ~10k+ lines, proof-carrying)
     |  emits
     v
  certificate  (.fx0c binary — a compact, self-contained record of a
                certified RawCell / typing derivation)
     |  re-checked by
     v
  FX0Poly  (minimal checker, target ~600 lines, a host-minimal Lean
            prelude-only checker)
```

If FX0Poly accepts a certificate, a reader need only audit FX0Poly's small
core — they do not have to trust FX1Poly's elaborator, its tactics, or Lean
itself beyond the kernel.  Disagreement between the two layers is a bug in
exactly one of them, surfaced by a cross-check corpus.

## Status

This file defines only the verdict vocabulary the checker reports
(`CheckVerdict` + `wasAccepted`).  It contains NO checking logic: no
certificate format, no re-check procedure, no soundness theorem, and no
cross-check corpus.  Nothing here claims soundness.  Zero-axiom discipline
applies in full once checking logic is added.
-/

namespace FX0Poly

/-- The verdict the minimal checker returns for a single certificate.
Distinguishing a structural rejection (the certificate is malformed) from a
semantic rejection (well-formed but the re-check disagrees) lets the
cross-check corpus localise which layer is wrong. -/
inductive CheckVerdict where
  /-- The certificate re-checks: FX0Poly agrees with FX1Poly. -/
  | accepted
  /-- The certificate is structurally malformed (bad header / truncated). -/
  | malformed
  /-- The certificate parses but the independent re-check disagrees. -/
  | disagreed
  deriving DecidableEq, Repr

/-- Did the minimal checker accept the certificate outright? -/
def CheckVerdict.wasAccepted : CheckVerdict → Bool
  | .accepted => true
  | .malformed => false
  | .disagreed => false

end FX0Poly
