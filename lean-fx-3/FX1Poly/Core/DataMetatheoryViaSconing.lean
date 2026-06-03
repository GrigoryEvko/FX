import FX1Poly.Core.DataCanonicityViaSconing

/-! # FX1Poly/Core/DataMetatheoryViaSconing
    — the BKS bundling capstone: ONE fundamental obligation ⟹ BOTH normalization AND canonicity (SN-096/110)

`DataCanonicityViaSconing.lean` extracts canonicity from a data candidate; `reducibilityScone`
(`SconingWitness.lean`) extracts strong normalization.  The BKS "sconing is enough" thesis (FSCD 2023)
is precisely that the metatheorems are CHEAP once the fundamental theorem is in hand — a SINGLE
fundamental discharges canonicity AND normalization AND parametricity.  This file makes the
normalization-plus-canonicity slice of that thesis concrete for the data axis: one fundamental
obligation yields BOTH metatheorems, sharing the SAME (`#672`-gated) hard work.

A data candidate `CanonicalFormsPredicate isValue` carries strong normalization as its FIRST conjunct
(CR1, `CanonicalFormsPredicate.stronglyNormalizing`) and reduces-to-a-value as the closed-term
extraction (`CanonicalFormsPredicate.closedReducesToValue`).  Both projections are `#672`-free.  So
from the one fundamental obligation (closed well-typed ⟹ candidate member — the fundamental theorem of
the logical relation, gated on `#672` / SN-043) BOTH metatheorems follow with no further hard work.

* `DataMetatheory` — the bundle: normalization (every well-typed term is strongly normalizing) AND
  canonicity (every well-typed term reduces to a constructor value satisfying `isValue`).
* `dataMetatheoryViaSconing` — the BKS capstone: given the single fundamental obligation, BOTH
  metatheorems hold.  Normalization is CR1; canonicity is the closed extraction (= the
  `dataCanonicityViaSconing` content).  The data-axis realization of "one functor ⟹ many metatheorems"
  (SN-110, the sconing-is-enough thesis; the bundling SN-096 wants at the BKS-package ledger level),
  restricted to the data axis where both extractions are `#672`-free.

This does NOT flip the Tier-0 `ln.hasBKSMetatheoryPackage` ledger flag: that flag tracks the CATEGORICAL
BKS package over `fxBaseRMC` (SN-090/091, the glued-model preservation of Π/Σ/universe), which is a
different and unshipped obligation.  This file ships the LOGICAL-PREDICATE bundling for the data axis —
honest about which slice is done.

## Zero-axiom verification

A structure plus a record literal whose fields are `CanonicalFormsPredicate.stronglyNormalizing` (CR1,
the first conjunct) and `CanonicalFormsPredicate.closedReducesToValue` (the closed extraction), each
applied to the explicit fundamental hypothesis.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation
open StepStar

/-- **The bundled data-axis BKS metatheory outputs.**  Relative to a notion of well-typedness
`isWellTyped` and a value predicate `isValue`, the two metatheorems the sconing leg produces for the
data axis: NORMALIZATION (every well-typed term is strongly normalizing) and CANONICITY (every
well-typed term reduces to a constructor value satisfying `isValue`).  Bundling them in one record
witnesses the BKS thesis that a single fundamental theorem discharges multiple metatheorems. -/
structure DataMetatheory (isWellTyped : RawTerm 0 → Prop) (isValue : RawTerm 0 → Prop) where
  /-- Normalization: every closed well-typed term of the data type is strongly normalizing (CR1). -/
  normalization : ∀ term : RawTerm 0, isWellTyped term → IsStronglyNormalizing term
  /-- Canonicity: every closed well-typed term of the data type reduces to a constructor value. -/
  canonicity : ∀ term : RawTerm 0,
    isWellTyped term → ∃ value : RawTerm 0, StepStar term value ∧ isValue value

/-- **The BKS bundling capstone for the data axis (SN-096/110): one fundamental ⟹ both metatheorems.**
Given the single fundamental obligation (closed well-typed ⟹ data-candidate member — the fundamental
theorem of the logical relation, the SOLE `#672`-gated hard work), BOTH normalization and canonicity
follow with no further hard work: normalization is the candidate's CR1 first conjunct
(`CanonicalFormsPredicate.stronglyNormalizing`), canonicity is the closed extraction
(`CanonicalFormsPredicate.closedReducesToValue`, = `dataCanonicityViaSconing`).  This is the concrete
data-axis realization of the BKS "sconing is enough" thesis — the metatheorems are cheap once the
fundamental is in hand, and they SHARE that single obligation. -/
def dataMetatheoryViaSconing {isWellTyped : RawTerm 0 → Prop} {isValue : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0,
      isWellTyped term → CanonicalFormsPredicate isValue term) :
    DataMetatheory isWellTyped isValue :=
  { normalization := fun term typed => (fundamental term typed).stronglyNormalizing
    canonicity := fun term typed => CanonicalFormsPredicate.closedReducesToValue (fundamental term typed) }

end FX1Poly.Core
