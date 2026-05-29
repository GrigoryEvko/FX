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
  FX0Poly  (minimal checker, target ~600 lines, eventually in C or Rust;
            here first as a host-minimal Lean prelude-only checker)
```

If FX0Poly accepts a certificate, a reader need only audit FX0Poly's small
core — they do not have to trust FX1Poly's elaborator, its tactics, or Lean
itself beyond the kernel.  Disagreement between the two layers is a bug in
exactly one of them, surfaced by a cross-check corpus.

## Status: NOT YET IMPLEMENTED

This file is a greenfield placeholder.  The checker proper is tracked by the
FX0-PC task series:

* FX0-PC.1  host-minimal `certifyRawCellExact?` (prelude-only gate)
* FX0-PC.2  binary certificate format (`.fx0c`) serializer + parser
* FX0-PC.3  `certifyRawCellExact?_sound` under host-minimal (Layer-1 soundness)
* FX0-PC.4  external verifier specification (language-independent)
* FX0-PC.5  first milestone (`var 0` end-to-end through both verifiers)
* FX0-PC.6  external implementation in C or Rust (~600 lines)
* FX0-PC.7  rich-layer bridge (`encodeCell` + `encodeCellSound`, incremental)
* FX0-PC.8  cross-check corpus (Lean vs external on the full fixture set)

The only declarations below are the verdict vocabulary the checker will
report.  No checking logic is asserted yet; nothing here claims soundness.
Zero-axiom discipline applies in full once real logic lands.
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
