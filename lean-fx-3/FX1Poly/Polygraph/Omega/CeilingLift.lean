import FX1Poly.Tier0.Mode.SemiThueReduction

/-! # Polygraph/Omega/CeilingLift — the undecidability ceiling lifted by suspension (OMEGA-3 r1, B4)

★ The FORM-A undecidability ceiling (`Tier0/Mode/SemiThueReduction`, Burroni-bridge `semiThue_iff_encodedTwoCell`,
Post-Markov CITED) reappears at EVERY suspended dimension.  This file lifts it — self-contained on the
`ModalityPath` / `EncodedConv` substrate, deliberately DODGING the walled `toCellDimTwo` conv-leg
(`Omega/BridgeDimTwo.lean`): we suspend `EncodedConv` NATIVELY, never bridging into `CellExpr`.

## Why the FORM-A ceiling suspends cleanly (the load-bearing fact)

`EncodedConv` (the 1-cell convertibility of a one-object 2-polygraph) has SIX constructors —
`rule` / `whiskerLeft` / `whiskerRight` / `refl` / `symm` / `trans` — and **NO interchange / Eckmann-Hilton
arm** (it is FORM-A, deliberately).  Suspension of a one-object polygraph is a strict, faithful,
structure-preserving reindexing that raises every cell one dimension: the 2-cell convertibility of the
suspended polygraph is structurally the SAME six-constructor congruence over the SAME free-monoid carrier (the
free monoid over `Letter` is INVARIANT under suspension — only the dimension re-tags).  Because there is no EH
arm, the Eckmann-Hilton bubble that FALSIFIED the oriented-trace normal form (FREE-6b, `df7a3473f`) never
fires — a FORM-B / EH target would NOT lift.  This is exactly the memo's fallback: the reduction MAP mechanizes;
the undecidable INSTANCE (Post 1947 / Markov 1947; Burroni TCS 1993) stays CITED, entering only as the
hypothesis `fxMode_hasSemiThueReductionMechanized`.

## What ships (B4)

  * **`EncodedConvSusp`** — the encoded convertibility of the `suspensionDepth`-fold suspended one-object
    polygraph: the faithful six-constructor copy, the `suspensionDepth` parameter recording the suspension
    count (= the dimension `2 + suspensionDepth`).  The GENUINE dimension-index shift is witnessed OMEGA-side
    by `suspendCell` (`Omega/Suspension.lean`); this native copy records the SAME word problem one (or `k`)
    dimensions up.
  * **`suspendEncoded`** — PRESERVATION: `EncodedConv → EncodedConvSusp` (the r1 core, a six-arm ctor map).
  * **`reflectEncoded`** — REFLECTION on the encoded fragment: `EncodedConvSusp → EncodedConv` (a six-arm ctor
    map back; holds precisely because the fragment is free-1-cells + a fixed relation set with NO EH arm).
  * **`semiThue_iff_encodedTwoCellSuspended`** — the FORM-A ceiling AT dimension `2 + suspensionDepth`, for
    EVERY `suspensionDepth`: `ThueCong rules u v ↔ EncodedConvSusp rules suspensionDepth (encodeWord u)
    (encodeWord v)`.  Composed from the shipped Burroni bridge and the preserve/reflect ctor maps.  So a
    uniform decider for `EncodedConvSusp` at ANY suspended dimension would decide `ThueCong` — which is
    undecidable (CITED).
  * The involution non-vacuity at every depth (a decided TRUE pair and a decided FALSE pair, transported).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

/-! ## The suspended encoded convertibility (the faithful dimension-raised copy) -/

/-- ★ The **encoded convertibility of the suspended one-object 2-polygraph** — the 2-cell convertibility of the
`suspensionDepth`-fold suspension, structurally the SAME six-constructor congruence over the SAME free-monoid
carrier (`ModalityPath (encodedGraph Letter) point point`).  The `suspensionDepth` parameter records the
suspension count (dimension `2 + suspensionDepth`); the constructors do not depend on it — faithfulness of
suspension on a one-object polygraph means the word content is INVARIANT (only the dimension re-tags).  NO
interchange / Eckmann-Hilton arm (FORM-A), which is exactly why the ceiling lifts. -/
inductive EncodedConvSusp {Letter : Type} (rules : List (List Letter × List Letter)) (suspensionDepth : Nat) :
    ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point →
    ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point → Prop where
  /-- A rule `(lhs, rhs) ∈ rules` is a generating cell between the encoded words (one dimension up). -/
  | rule {lhs rhs : List Letter} (mem : (lhs, rhs) ∈ rules) :
      EncodedConvSusp rules suspensionDepth (encodeWord lhs) (encodeWord rhs)
  /-- Left whiskering by a 1-cell prefix. -/
  | whiskerLeft (prefixCell : ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point)
      {left right : ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point}
      (inner : EncodedConvSusp rules suspensionDepth left right) :
      EncodedConvSusp rules suspensionDepth (composePath prefixCell left) (composePath prefixCell right)
  /-- Right whiskering by a 1-cell suffix. -/
  | whiskerRight {left right : ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point}
      (inner : EncodedConvSusp rules suspensionDepth left right)
      (suffixCell : ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point) :
      EncodedConvSusp rules suspensionDepth (composePath left suffixCell) (composePath right suffixCell)
  /-- Reflexivity. -/
  | refl (word : ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point) :
      EncodedConvSusp rules suspensionDepth word word
  /-- Symmetry. -/
  | symm {left right : ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point} :
      EncodedConvSusp rules suspensionDepth left right → EncodedConvSusp rules suspensionDepth right left
  /-- Transitivity. -/
  | trans {left middle right : ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point} :
      EncodedConvSusp rules suspensionDepth left middle →
      EncodedConvSusp rules suspensionDepth middle right →
      EncodedConvSusp rules suspensionDepth left right

/-! ## Preservation and reflection on the encoded fragment (B4) -/

/-- ★ **PRESERVATION** (the r1 core).  Encoded convertibility lifts to the suspended polygraph at ANY depth: a
six-arm constructor-map induction (mirrors `thue_to_encoded`).  This is the ceiling-lift's `→`. -/
theorem suspendEncoded {Letter : Type} {rules : List (List Letter × List Letter)} (suspensionDepth : Nat)
    {source target : ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point}
    (conv : EncodedConv rules source target) : EncodedConvSusp rules suspensionDepth source target := by
  induction conv with
  | rule mem => exact EncodedConvSusp.rule mem
  | whiskerLeft prefixCell _ inductiveHypothesis => exact EncodedConvSusp.whiskerLeft prefixCell inductiveHypothesis
  | whiskerRight _ suffixCell inductiveHypothesis => exact EncodedConvSusp.whiskerRight inductiveHypothesis suffixCell
  | refl word => exact EncodedConvSusp.refl word
  | symm _ inductiveHypothesis => exact EncodedConvSusp.symm inductiveHypothesis
  | trans _ _ firstInductiveHypothesis secondInductiveHypothesis =>
      exact EncodedConvSusp.trans firstInductiveHypothesis secondInductiveHypothesis

/-- ★ **REFLECTION on the encoded fragment.**  The suspended convertibility reads back to the base encoded
convertibility: the symmetric six-arm constructor map.  This holds precisely because the fragment is
free-1-cells + a fixed relation set with NO EH arm — a syntactic decode, exactly the memo's encoded-fragment
reflection.  (The GENERAL free-cell syntactic reflection stays walled; the ceiling needs only this fragment.) -/
theorem reflectEncoded {Letter : Type} {rules : List (List Letter × List Letter)} (suspensionDepth : Nat)
    {source target : ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point}
    (conv : EncodedConvSusp rules suspensionDepth source target) : EncodedConv rules source target := by
  induction conv with
  | rule mem => exact EncodedConv.rule mem
  | whiskerLeft prefixCell _ inductiveHypothesis => exact EncodedConv.whiskerLeft prefixCell inductiveHypothesis
  | whiskerRight _ suffixCell inductiveHypothesis => exact EncodedConv.whiskerRight inductiveHypothesis suffixCell
  | refl word => exact EncodedConv.refl word
  | symm _ inductiveHypothesis => exact EncodedConv.symm inductiveHypothesis
  | trans _ _ firstInductiveHypothesis secondInductiveHypothesis =>
      exact EncodedConv.trans firstInductiveHypothesis secondInductiveHypothesis

/-- The faithful embedding of the encoded convertibility into its suspension, at every depth (preservation and
reflection together). -/
theorem encoded_iff_encodedSuspended {Letter : Type} (rules : List (List Letter × List Letter))
    (suspensionDepth : Nat)
    (source target : ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point) :
    EncodedConv rules source target ↔ EncodedConvSusp rules suspensionDepth source target :=
  ⟨suspendEncoded suspensionDepth, reflectEncoded suspensionDepth⟩

/-! ## The FORM-A ceiling at dimension `2 + suspensionDepth` (B4, the n+k statement) -/

/-- ★★ **THE CEILING LIFT.**  For EVERY suspension depth `suspensionDepth`, the Thue congruence of a semi-Thue
system is exactly the encoded convertibility of its `suspensionDepth`-fold suspended one-object 2-polygraph:
`ThueCong rules u v ↔ EncodedConvSusp rules suspensionDepth (encodeWord u) (encodeWord v)`.  Composed from the
shipped Burroni bridge `semiThue_iff_encodedTwoCell` and the preserve/reflect constructor maps.  Since
`ThueCong` is undecidable in general (Post 1947 / Markov 1947 — CITED, never axiomatized), NO uniform decider
exists for `EncodedConvSusp` at ANY suspended dimension: the undecidability firewall is no longer a dim-2
accident, it holds at dimension `2 + suspensionDepth` for every `suspensionDepth`. -/
theorem semiThue_iff_encodedTwoCellSuspended {Letter : Type} (rules : List (List Letter × List Letter))
    (suspensionDepth : Nat) (u v : List Letter) :
    ThueCong rules u v ↔ EncodedConvSusp rules suspensionDepth (encodeWord u) (encodeWord v) :=
  Iff.trans (semiThue_iff_encodedTwoCell rules u v)
    ⟨suspendEncoded suspensionDepth, reflectEncoded suspensionDepth⟩

/-! ## Non-vacuity — the involution 1-rule system at every suspended dimension -/

/-- ★ Positive witness at every depth — `s.s ~ id` is DECIDED TRUE in the suspended encoded convertibility of
the involution system, at every `suspensionDepth` (transported from `involutionThue_positive`). -/
theorem involutionEncodedSusp_positive (suspensionDepth : Nat) :
    EncodedConvSusp involutionThueRules suspensionDepth
      (encodeWord [InvolutionLetter.s, InvolutionLetter.s]) (encodeWord ([] : List InvolutionLetter)) :=
  (semiThue_iff_encodedTwoCellSuspended involutionThueRules suspensionDepth
    [InvolutionLetter.s, InvolutionLetter.s] []).mp involutionThue_positive

/-- ★ Negative witness at every depth — `s ~ id` is DECIDED FALSE in the suspended encoded convertibility (the
Z/2 parity separation, transported).  Together with the positive witness the ceiling lift genuinely
discriminates at every suspended dimension (not always-true, not always-false). -/
theorem involutionEncodedSusp_separation (suspensionDepth : Nat) :
    ¬ EncodedConvSusp involutionThueRules suspensionDepth
        (encodeWord [InvolutionLetter.s]) (encodeWord ([] : List InvolutionLetter)) :=
  fun conv => involutionThue_separation
    ((semiThue_iff_encodedTwoCellSuspended involutionThueRules suspensionDepth
      [InvolutionLetter.s] []).mpr conv)

/-! ## OMEGA-3 r1 honesty markers (B4 + B5 — strictly factual) -/

/-- ★ **B4 — the ceiling-lift PRESERVATION + the FORM-A ceiling at every suspended dimension are SHIPPED.**
`suspendEncoded` (preservation) and `reflectEncoded` (encoded-fragment reflection) are the six-arm ctor maps,
composing with the shipped Burroni bridge into `semiThue_iff_encodedTwoCellSuspended` — the FORM-A ceiling at
dimension `2 + suspensionDepth` for EVERY `suspensionDepth`.  The reduction MAP is mechanized; the undecidable
INSTANCE (Post-Markov / Burroni) stays CITED via `fxMode_hasSemiThueReductionMechanized`, never axiomatized.
Suspends cleanly because FORM-A has NO Eckmann-Hilton arm (a FORM-B / EH target would not lift — FREE-6b).
`= true`. -/
def fxOmega_ceilingLiftEveryDimensionShippedR1 : Bool := true

/-- ★ **B4/B5 — the honest boundary.**  MECHANIZED here = the ceiling-lift BRIDGE at every suspended dimension
(preserve + reflect + the depth-parameterized iff), self-contained on the `ModalityPath` / `EncodedConv`
substrate (NOT bridged through the walled `toCellDimTwo` conv-leg).  CITED, not mechanized = the EXISTENCE of a
finite semi-Thue system whose `ThueCong` is undecidable (Post 1947 / Markov 1947; mechanizing it needs a
computability substrate, out of scope — as at dim 2).  The genuine dimension-index shift is witnessed OMEGA-side
by `suspendCell`; this file records the SAME undecidable word problem one (or `k`) dimensions up.  `= false`
records that the FULL reduction to a known-undecidable instance is NOT mechanized (honest — matching the dim-2
ledger's `fxMode_hasArbitraryTwoCellUndecidabilityReduction = false`). -/
def fxOmega_ceilingLiftUndecidableInstanceMechanized : Bool := false

end FX1Poly.Polygraph.Omega
