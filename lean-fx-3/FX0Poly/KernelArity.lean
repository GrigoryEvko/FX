import FX0Poly.CertRecheckSound

/-!
# FX0Poly — concrete kernel-fragment arity model + end-to-end cell re-check

`CertRecheck`/`CertRecheckSound` define the recursive re-checker generic over an abstract tag→arity model.
This file PINS that model to the FX1Poly kernel's formation fragment, turning the abstract checker into a
concrete one that re-checks actual kernel-shaped certificate trees.

`fxArity` is FX0Poly's OWN authoritative table of the recognized generator tags and their child arities
(var / universe-code / Π-code / Σ-code).  It is deliberately self-contained — FX0Poly never imports
FX1Poly's `Generator` enum; aligning FX1Poly's emitted tags to this table is the cross-check bridge's job,
not the checker's.  The tag numbers here are FX0Poly's convention.

The end-to-end smokes exercise the full recursive driver on real cell shapes: a concrete certificate for
each formation-fragment generator (var / Π / Σ) re-checks `accepted`, and malformed ones (wrong arity,
unknown tag) re-check `malformed`.

## Zero-axiom verification

`fxArity` is a total `Nat` match; the soundness corollary is `recheck_wasAccepted_eq_isValidB` at `fxArity`;
the smokes close by `rfl` (full evaluation).  No `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, or `omega`.  Gated per-declaration in `FX1PolyAudit/AuditFX0Poly.lean`.
-/

namespace FX0Poly

/-- FX0Poly's authoritative tag→arity table for the FX1Poly kernel's formation fragment.  Recognized
generator tags and their child counts: `0` = variable (0 children), `1` = universe code (0), `2` = Π code
(2: domain, codomain), `3` = Σ code (2: domain, codomain).  Every other tag is unrecognized (`none`), so a
certificate naming it re-checks as malformed.  Self-contained: FX0Poly's own convention, not an import of
FX1Poly's `Generator`. -/
def fxArity : Nat → Option Nat
  | 0 => some 0
  | 1 => some 0
  | 2 => some 2
  | 3 => some 2
  | _ => none

/-- **The concrete kernel re-checker is sound.**  Specialising the recursive soundness theorem to `fxArity`:
re-checking a certificate under the kernel-fragment arity model accepts EXACTLY the structurally-valid
trees over the recognized generators. -/
theorem recheck_fxArity_wasAccepted_eq_isValidB (c : Cert) :
    (Cert.recheck fxArity c).wasAccepted = Cert.isValidB fxArity c :=
  Cert.recheck_wasAccepted_eq_isValidB fxArity c

/-- End-to-end: a variable certificate (`tag 0`, no children) re-checks accepted. -/
theorem recheck_fxArity_smoke_var :
    Cert.recheck fxArity (.node 0 []) = CheckVerdict.accepted := rfl

/-- End-to-end: a universe-code certificate (`tag 1`, no children) re-checks accepted. -/
theorem recheck_fxArity_smoke_universe :
    Cert.recheck fxArity (.node 1 []) = CheckVerdict.accepted := rfl

/-- End-to-end: a Π-code certificate (`tag 2`) over a domain (var) and codomain (universe) re-checks
accepted — the recursive driver descends into both children and admits the former. -/
theorem recheck_fxArity_smoke_pi :
    Cert.recheck fxArity (.node 2 [.node 0 [], .node 1 []]) = CheckVerdict.accepted := rfl

/-- End-to-end: a Σ-code certificate (`tag 3`) over two variable children re-checks accepted. -/
theorem recheck_fxArity_smoke_sigma :
    Cert.recheck fxArity (.node 3 [.node 0 [], .node 0 []]) = CheckVerdict.accepted := rfl

/-- End-to-end (rejection): a Π-code certificate with the wrong child count (1, not 2) re-checks malformed. -/
theorem recheck_fxArity_smoke_piWrongArity :
    Cert.recheck fxArity (.node 2 [.node 0 []]) = CheckVerdict.malformed := rfl

/-- End-to-end (rejection): a certificate naming an unrecognized generator tag re-checks malformed. -/
theorem recheck_fxArity_smoke_unknownTag :
    Cert.recheck fxArity (.node 9 []) = CheckVerdict.malformed := rfl

end FX0Poly
