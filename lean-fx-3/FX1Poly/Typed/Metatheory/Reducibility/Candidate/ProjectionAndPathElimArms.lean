import FX1Poly.Typed.Metatheory.Reducibility.Candidate.DataElimArm
import FX1Poly.Core.Eliminators.Sigma.SigmaProjectionClosedMembership
import FX1Poly.Core.Eliminators.Identity.IdEliminatorClosedMembership

/-! # FX1Poly/Typed/Metatheory/Reducibility/Candidate/ProjectionAndPathElimArms
    — the projection + path-induction FT arms (FTGEN-11), CLOSED layer: fst / snd / idJ / idStrictRec

The third FTGEN-11 elim-arm file, completing the descriptor's `projection` and `pathInduction` roles.  Unlike
the recursor arms (`RecursorElimArms`) and the two-branch match (`DataElimArm`), these four eliminators have
only the CLOSED scope-0 `…ClosedIsMember` reducibility proven in Core — the regime where data weak-head
expansion holds unconditionally, so NO `headExpand` interface hypothesis is needed.  Their OPEN
general-scrutinee versions (arbitrary candidate-member scrutinee, lifted through the scrutinee congruence)
remain Core work; this is the honest scope, stated at the file level rather than hidden.

  * **projection** — `fstClosedArm` / `sndClosedArm`: a closed `fst`/`snd` on a Σ-candidate-member pair whose
    relevant component is a member lands in the result candidate (Core `fstClosedIsMember` / `sndClosedIsMember`;
    cell SN + projection ι + value-reaching weak-head expansion).
  * **pathInduction** — `idJClosedArm` / `idStrictRecClosedArm`: a closed `idJ` / `idStrictRec` on a
    refl-candidate-member witness with a member base case lands in the result candidate (Core
    `idJClosedIsMember` / `idStrictRecClosedIsMember`; the `idStrictRec` twin is the UIP-flavoured strict
    recursor sharing the same `(base, witness)` spine and single ι rule).

All over the elim-native `canonicalDataCandidate` (= `CanonicalFormsPredicate`; see `DataElimArm` for the
formation-side reconciliation note).

## Zero-axiom verification

Each arm is a direct application of a shipped, audited Core `…ClosedIsMember` theorem.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core
open StepStar

/-- **★ FTGEN-11 — the closed `fst` projection arm.**  A closed `fst` on a Σ-candidate-member scrutinee whose
first component is a member (whenever the scrutinee reduces to a pair) is a member of the result candidate, via
the Core `fstClosedIsMember`. -/
theorem fstClosedArm {isValue : RawTerm 0 → Prop} {scrutinee : RawTerm 0}
    (scrutineeMember : canonicalDataCandidate isPairValue scrutinee)
    (firstComponentMember : ∀ first second : RawTerm 0,
      StepStar scrutinee (pairCell first second) → canonicalDataCandidate isValue first) :
    canonicalDataCandidate isValue (.mkGen .gen_fst () (.childCons scrutinee .childNil)) :=
  fstClosedIsMember scrutineeMember firstComponentMember

/-- **★ FTGEN-11 — the closed `snd` projection arm**, symmetric to `fstClosedArm`, via the Core
`sndClosedIsMember`. -/
theorem sndClosedArm {isValue : RawTerm 0 → Prop} {scrutinee : RawTerm 0}
    (scrutineeMember : canonicalDataCandidate isPairValue scrutinee)
    (secondComponentMember : ∀ first second : RawTerm 0,
      StepStar scrutinee (pairCell first second) → canonicalDataCandidate isValue second) :
    canonicalDataCandidate isValue (.mkGen .gen_snd () (.childCons scrutinee .childNil)) :=
  sndClosedIsMember scrutineeMember secondComponentMember

/-- **★ FTGEN-11 — the closed `idJ` path-induction arm.**  A closed `idJ` with an SN motive, a refl-candidate-
member witness, and a member base case is a member of the result candidate, via the Core `idJClosedIsMember`
(cell SN + the canonical-witness reduces-to-base computation + value-reaching weak-head expansion). -/
theorem idJClosedArm {isValue : RawTerm 0 → Prop}
    {motive : RawTerm 2} {baseCase witness : RawTerm 0}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (witnessMember : canonicalDataCandidate isReflValue witness)
    (baseCaseMember : canonicalDataCandidate isValue baseCase) :
    canonicalDataCandidate isValue
      (.mkGen .gen_idJ ()
        (.childCons motive (.childCons baseCase (.childCons witness .childNil)))) :=
  idJClosedIsMember motiveStronglyNormalizing witnessMember baseCaseMember

/-- **★ FTGEN-11 — the closed `idStrictRec` path-induction arm**, the UIP-flavoured strict twin of
`idJClosedArm` (same `(base, witness)` spine and single ι rule), via the Core `idStrictRecClosedIsMember`. -/
theorem idStrictRecClosedArm {isValue : RawTerm 0 → Prop}
    {motive : RawTerm 2} {baseCase witness : RawTerm 0}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (witnessMember : canonicalDataCandidate isReflValue witness)
    (baseCaseMember : canonicalDataCandidate isValue baseCase) :
    canonicalDataCandidate isValue
      (.mkGen .gen_idStrictRec ()
        (.childCons motive (.childCons baseCase (.childCons witness .childNil)))) :=
  idStrictRecClosedIsMember motiveStronglyNormalizing witnessMember baseCaseMember

end FX1Poly.Typed
