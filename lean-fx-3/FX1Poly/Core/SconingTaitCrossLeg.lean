import FX1Poly.Core.ReducibilityNormalizationViaSconing

/-! # FX1Poly/Core/SconingTaitCrossLeg
    — the sconing leg and the Tait/Path-A leg produce strong normalization over the SAME object: the
    cross-leg triangulation is an object-level identity, NOT two independent proofs

Milestone A's metatheory is targeted by three routes: the syntactic Tait reducibility logical relation
(Path A), the internal-sconing / Sterling-Tait-computability route (the "sconing leg"), and the
combinatorial recursive-path-order route.  A natural hope for the capstone is that the sconing leg gives an
INDEPENDENT second strong-normalization proof, so SN is established two genuinely different ways.

This file proves that, with the current zero-axiom substrate, the sconing leg's SN is NOT independent: it is
the SAME object as the Tait leg's.  The sconing witness `reducibilityScone` (the only shipped zero-axiom FX
logical relation) has

  * its displayed computability predicate (`computable`) DEFINITIONALLY EQUAL to the Path-A reducibility
    candidate (`sconingScone_computable_eq_candidate`), and
  * its strong-normalization extraction DEFINITIONALLY EQUAL to CR1
    (`sconingScone_extraction_eq_candidateCR1`),

so the SN it delivers for a well-typed term, `(reducibilityScone …).canonicity term typed`, is the very term
`candidateIsReducibility.stronglyNormalizing (fundamental term typed)` — CR1 applied to the fundamental
theorem, exactly the Tait-leg composition (`sconingSN_eq_taitComposition`).  The strong-normalization and
weak-normalization sconing witnesses even share one displayed predicate
(`sconingScone_and_normalizationScone_share_computable`): "one fundamental ⟹ many metatheorems" ranges over a
SINGLE object, the candidate.

## Why this is the honest triangulation (and why genuine independence stays open)

The cross-leg agreement is real but DEGENERATE: the sconing leg is built FROM the Tait ingredients (its
`computable` IS the reducibility candidate, its extraction IS CR1).  So the two legs coincide as one object —
which is precisely the parity-ledger reading that the sconing-SN cell is bridged to Tait, not an independent
route.

A genuinely independent second SN proof would need a sconing witness whose `computable` predicate is NOT the
reducibility candidate — the synthetic Sterling-Tait-computability logical relation, glued from the closed
modality.  The shipped STC substrate (`FX1Poly.STC`) deliberately CANNOT supply that zero-axiom: its
`ClosedMod` is a computable one-constructor wrapper, NOT the higher-inductive quotient closed modality the
synthetic construction requires (the genuine modality pulls `Quot.sound`, breaking the zero-axiom
discipline).  Accordingly the only zero-axiom FX logical relation that exists is the
proof-relevant-predicate realization, which is Path A — the STC ledger's
`fxSTC_hasLogicalRelationConstruction` is witnessed by `STC/FxLogicalRelation.lean`, whose semantic side is
DEFINITIONALLY the Tait pipeline (`fxStcFundamental_semantic_isTaitWitness`), i.e. the BRIDGED construction,
not an independent one.  Hence the independent-second-SN goal is not merely unbuilt but zero-axiom-blocked at
the closed modality; this file pins exactly that boundary.  The boundary is now also FORMALIZED as committed
theorems in `STC/FxIndependenceBoundary.lean`: the STC Prop-payload glue families are SYNTAX-DETERMINED
(`stcPropGlue_syntaxDetermined` — by definitional proof irrelevance two glues with the same syntax are EQUAL),
every inhabitant's semantic component IS the kernel witness (`anyStcSNGlue_semantic_isTaitWitness`), and every
syntax-faithful SN-fundamental equals `fxStcFundamental` (`anySNFundamental_eq_fxStcFundamental`) — the STC
twin of `anySconingSN_eq_taitComposition` below.

## What this ships

  * `sconingScone_computable_eq_candidate` / `normalizationScone_computable_eq_candidate` — each sconing
    witness's displayed predicate IS the Path-A reducibility candidate.
  * `sconingScone_and_normalizationScone_share_computable` — the SN and WN witnesses scone ONE object.
  * `sconingScone_extraction_eq_candidateCR1` — the SN extraction IS CR1, not a fresh argument.
  * **`sconingSN_eq_taitComposition` (★)** — for a well-typed term, the sconing leg's extracted SN is the
    identical witness `CR1 (fundamental term typed)` the Tait leg produces.  The object-level triangulation.

## Zero-axiom verification

Every theorem is `rfl`: the sconing witness's fields are literally the candidate / CR1 / the fundamental
obligation, so the projections compute definitionally.  No induction, no `funext`, no `propext`,
`Quot.sound`, `Classical`, `sorry`, `axiom`, `native_decide`, or `omega`.  Audit-gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- The strong-normalization sconing witness's displayed computability predicate IS the Path-A reducibility
candidate — the two legs scone the same object. -/
theorem sconingScone_computable_eq_candidate {scope : Nat} {candidate : RawTerm scope → Prop}
    (candidateIsReducibility : IsReducibilityCandidate candidate)
    {isWellTyped : RawTerm scope → Prop}
    (fundamental : ∀ term : RawTerm scope, isWellTyped term → candidate term) :
    (reducibilityScone candidateIsReducibility fundamental).computable = candidate :=
  rfl

/-- The weak-normalization sconing witness shares the SAME displayed predicate (the candidate). -/
theorem normalizationScone_computable_eq_candidate {scope : Nat} {candidate : RawTerm scope → Prop}
    (candidateIsReducibility : IsReducibilityCandidate candidate)
    {isWellTyped : RawTerm scope → Prop}
    (fundamental : ∀ term : RawTerm scope, isWellTyped term → candidate term) :
    (reducibilityNormalizationScone candidateIsReducibility fundamental).computable = candidate :=
  rfl

/-- The strong-normalization and weak-normalization sconing witnesses scone ONE shared object: "one
fundamental ⟹ many metatheorems" ranges over a single displayed predicate. -/
theorem sconingScone_and_normalizationScone_share_computable {scope : Nat}
    {candidate : RawTerm scope → Prop}
    (candidateIsReducibility : IsReducibilityCandidate candidate)
    {isWellTyped : RawTerm scope → Prop}
    (fundamental : ∀ term : RawTerm scope, isWellTyped term → candidate term) :
    (reducibilityScone candidateIsReducibility fundamental).computable
      = (reducibilityNormalizationScone candidateIsReducibility fundamental).computable :=
  rfl

/-- The strong-normalization extraction IS CR1 (candidate membership ⟹ strong normalization), not an
independent argument — so the sconing leg's "every computable is canonical (SN)" step is literally the Path-A
reducibility-candidate property. -/
theorem sconingScone_extraction_eq_candidateCR1 {scope : Nat} {candidate : RawTerm scope → Prop}
    (candidateIsReducibility : IsReducibilityCandidate candidate)
    {isWellTyped : RawTerm scope → Prop}
    (fundamental : ∀ term : RawTerm scope, isWellTyped term → candidate term) :
    (reducibilityScone candidateIsReducibility fundamental).extraction
      = fun _term reducible => candidateIsReducibility.stronglyNormalizing reducible :=
  rfl

/-- **★ The cross-leg triangulation, object-level.**  For a well-typed term, the strong normalization the
sconing leg extracts is the IDENTICAL witness the Tait/Path-A leg produces: `CR1` applied to the fundamental
theorem.  The two legs are not independent — the sconing SN is `CR1 ∘ fundamental`, the Tait composition. -/
theorem sconingSN_eq_taitComposition {scope : Nat} {candidate : RawTerm scope → Prop}
    (candidateIsReducibility : IsReducibilityCandidate candidate)
    {isWellTyped : RawTerm scope → Prop}
    (fundamental : ∀ term : RawTerm scope, isWellTyped term → candidate term)
    (term : RawTerm scope) (typed : isWellTyped term) :
    (reducibilityScone candidateIsReducibility fundamental).canonicity term typed
      = candidateIsReducibility.stronglyNormalizing (fundamental term typed) :=
  rfl

end FX1Poly.Core
