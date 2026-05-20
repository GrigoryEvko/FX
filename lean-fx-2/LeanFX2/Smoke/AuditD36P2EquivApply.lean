import LeanFX2.Foundation.RawTerm
import LeanFX2.Reduction.RawPar.Inductive

/-! # Smoke/AuditD36P2EquivApply — D3.6-P2 univalence-β raw vocabulary audit.

Phase D3.6-P2 ships `RawTerm.equivApply equivRaw argRaw` and the matching
parallel-step cong rule `RawStep.par.equivApplyCong`.  These are the
raw-layer vocabulary for the term-level equivalence-application
operation: `equivApply equiv arg` represents applying a type
equivalence (`equiv : Equiv leftTy rightTy` at the typing layer) to an
argument of the source type.  The actual β-rule
`transp at (uaToEquiv e)` reducing to `equivApply e` ships in a later
phase (S1+); P2 is the vocabulary baseline so downstream functions can
pattern-match on the new ctor.

## What this audit proves

* `RawTerm.equivApply` zero-axiom (new binary ctor).
* `RawStep.par.equivApplyCong` zero-axiom (new cong rule mirroring
  `uaToEquivCong`'s shape but with two recursing premises).
* Mechanical 28-file cascade across the kernel preserves zero-axiom
  discipline: every match site over `RawTerm` enumerates the new ctor
  with the structurally appropriate handler (none / refl / recurse-on-
  equiv-and-arg-raws, etc.).

## Why a raw-only ctor (no typed mirror in P2)

The typed mirror (`Term.equivApply`) lives at Layer 7+ of the kernel:
its source-side type is `Ty.equiv leftTy rightTy → leftTy → rightTy`,
which requires the typed Term layer to witness an inhabitant of an
`Equiv` type and an inhabitant of the source type simultaneously.  P2
ships only the raw vocabulary because:

1. The raw cong rule alone is sufficient to extend confluence's `cd`
   cascade (cd dispatches on raw shape).
2. The typed inversion lemmas in `Term/Inversion.lean` continue to
   work via raw-ctor mismatch (equivApply vs every other RawTerm ctor).
3. Adding the typed mirror requires the Step.par typed cong + bridge
   arms, scheduled for P4.

The raw cong is documented in
`LeanFX2/Tools/StrictHarness/Common.lean`'s
`isDocumentedRawOnlyParity` allowlist as a deliberate raw-only entry
to keep the parity gate green during P1-P4.
-/

namespace LeanFX2

/-! ## Smoke: the new ctors construct trivially. -/

example {scope : Nat} (equivRaw argRaw : RawTerm scope) : RawTerm scope :=
  RawTerm.equivApply equivRaw argRaw

example {scope : Nat} (equivRaw argRaw : RawTerm scope) :
    RawStep.par (RawTerm.equivApply equivRaw argRaw)
                (RawTerm.equivApply equivRaw argRaw) :=
  RawStep.par.equivApplyCong (RawStep.par.refl equivRaw)
                             (RawStep.par.refl argRaw)

/-! ## Audit declarations — all zero-axiom for D3.6-P2. -/

#print axioms LeanFX2.RawTerm.equivApply
#print axioms LeanFX2.RawStep.par.equivApplyCong

end LeanFX2
