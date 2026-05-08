import LeanFX2.Foundation.RawTerm
import LeanFX2.Reduction.RawPar

/-! # Smoke/AuditD36P1UaToEquiv — D3.6-P1 univalence-β raw vocabulary audit.

Phase D3.6-P1 ships `RawTerm.uaToEquiv proofRaw` and the matching
parallel-step cong rule `RawStep.par.uaToEquivCong`.  These are the
raw-layer vocabulary for the term-level univalence-to-equivalence
operation: `uaToEquiv proof` represents turning a univalence proof
(`proof : Id (Universe lvl) leftTy rightTy` at the typing layer) into
the corresponding type equivalence.  The actual β-rule
`transp at (uaToEquiv e)` reducing to `equivApply e` ships in a later
phase (S1+); P1 is the vocabulary baseline so downstream functions can
pattern-match on the new ctor.

## What this audit proves

* `RawTerm.uaToEquiv` zero-axiom (new unary ctor).
* `RawStep.par.uaToEquivCong` zero-axiom (new cong rule mirroring the
  cumulUpMarkerCong shape).
* Mechanical 30-file cascade across the kernel preserves zero-axiom
  discipline: every match site over `RawTerm` enumerates the new ctor
  with the structurally appropriate handler (none / refl / recurse-on-
  proofRaw, etc.).

## Why a raw-only ctor (no typed mirror in P1)

The typed mirror (`Term.uaToEquiv`) lives at Layer 7+ of the kernel:
its source-side type is `Ty.id (Ty.universe lvl) leftTy rightTy` and
the typed Term layer must witness that the input term has that
specific identity type.  P1 ships only the raw vocabulary because:

1. The raw cong rule alone is sufficient to extend confluence's `cd`
   cascade (cd dispatches on raw shape).
2. The typed inversion lemmas in `Term/Inversion.lean` continue to
   work via raw-ctor mismatch (uaToEquiv vs every other RawTerm ctor).
3. Adding the typed mirror requires the Step.par typed cong + bridge
   arms, scheduled for P3.

The raw cong is documented in
`LeanFX2/Tools/StrictHarness/Common.lean`'s
`isDocumentedRawOnlyParity` allowlist as a deliberate raw-only entry
to keep the parity gate green during P1-P2.
-/

namespace LeanFX2

/-! ## Smoke: the new ctors construct trivially. -/

example {scope : Nat} (proofRaw : RawTerm scope) : RawTerm scope :=
  RawTerm.uaToEquiv proofRaw

example {scope : Nat} (proofRaw : RawTerm scope) :
    RawStep.par (RawTerm.uaToEquiv proofRaw) (RawTerm.uaToEquiv proofRaw) :=
  RawStep.par.uaToEquivCong (RawStep.par.refl proofRaw)

/-! ## Audit declarations — all zero-axiom for D3.6-P1. -/

#print axioms LeanFX2.RawTerm.uaToEquiv
#print axioms LeanFX2.RawStep.par.uaToEquivCong

end LeanFX2
