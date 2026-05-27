import LeanFX2.Foundation.PolyCell.Core.CertifyRawCellExactV2

/-! # Foundation/PolyCell/Core/CertifyRawCellExactV2TermBase — termBase shape pin

V2-L3.1 phase D step 1 (2026-05-27).  Ships the **termBase dispatcher
shape pin** — the missing arm in the `CertifyRawCellExactV2Shape.lean`
family.

## Why this arm matters most for SR

The Subject Reduction theorem (V2-L3.1) is stated over `Step source
target` where `source` and `target` are `RawTermV2 scope`.  The SR
proof's cong arm and iota arms all need to **project** from
`Certified parent` to `Certified child` (where `parent` is a composite
generator like `lam body`, `app f arg`, `fst (pair a b)`, etc., and
`child` is one of its spine elements).

The certifier's `.termBase` dispatcher arm is the gate every SR-relevant
input passes through.  An "accepted termBase implies spine succeeds"
shape pin is the structural building block for the projection — it
extracts the spine certification's success witness from the parent's
acceptance, exposing the per-child certificates without needing to
unfold the mutual recursive certifier (which would leak `Quot.sound`).

## Pattern variant: reducibility-aware dispatcher pin

The existing `CertifyRawCellExactV2Shape.lean` family pins
`.identityCell`, `.verticalComposite`, `.generatingCell` arms — each
case-analyzes on recursive certifier calls that are NOT `@[reducible]`.
The termBase arm differs: its inner `supportedGeneratorV2?` and
`genPayloadEvidence?` are both `@[reducible]`, so they pre-reduce to
`some _` definitionally and Lean's `cases` tactic cannot non-trivially
case-analyze on them (the `.none` case is unreachable by reducibility).

The shape lemma adapts: the dispatcherEq `rfl`-bridge already collapses
both `@[reducible]` decisions to their `.some` branches, leaving ONLY
the spine certification as the dispatcher's remaining match.  Then
`cases hSpine : ...` performs the one non-trivial case analysis: spine
success → witnesses produced, spine failure → contradiction with
acceptance.

## Inner-call fuel value

The wrapper calls `certifyRawCellExactV2Fueled? (raw.size + 1) scope
raw`.  For `raw := .termBase (.mkGen generator payload children)`:

  * raw.size + 1 = (.mkGen generator payload children).size + 2
  * The fueled function matches `fuel' + 1` with
    `fuel' := raw.size = (.mkGen generator payload children).size + 1`
  * The inner `certifyChildrenInlineV2Fueled?` call receives
    `fuel' = (.mkGen generator payload children).size + 1`

The shape pin's existential records THIS exact fuel value (the
dispatcher's `fuel'`), keeping the lemma's statement tied to the
certifier's actual operational behavior.

## What this unlocks

Future SR-related work uses this shape pin to:

  1. From `Certified (mkGen gen p ch)` extract the spine success witness.
  2. From spine success on `(childCons head tail)` (a later shape pin)
     extract head and tail certificate success.
  3. Combined with subst-preservation (V2-L2.12, already shipped),
     discharge SR's iota and cong arms.

## Zero-axiom verification

Identical structural-proof discipline to the sibling shape pins.
Pattern matching on closed inductives + `rfl` + `cases accepted` for
contradiction.  No `unfold` on mutual defs; no `omega`; no `simp`-set
expansion.  Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- **Behavioral shape pin: termBase implies all three inner stages succeed.**

If the certifier accepts `.termBase (.mkGen generator payload children)`,
then the dispatcher's three inner machinery stages all produced their
positive outcomes:

  * `supportedGeneratorV2? generator = some _` (generator admitted —
    always definitional under the current admission table; the shape
    pin pins the witness for forward-compatible profile restrictions).
  * `genPayloadEvidence? payload = some _` (payload admissible — same
    forward-compatible discipline).
  * `certifyChildrenInlineV2Fueled? fuel scope ... children = .ok _`
    (spine successfully certified — the NON-DEFINITIONAL stage).

A regression that broke any of the three stages — e.g., an admission
table that erroneously rejected an admitted generator, or a spine
walker that short-circuited recursion — would fail to discharge this
lemma because the existential witnesses would be unobtainable.

Mirrors `_verticalComposite_accepted_implies_inner_certs` /
`_generatingCell_accepted_implies_inner_certs` from
`CertifyRawCellExactV2Shape.lean`, extending the family to the
three-stage termBase dispatcher arm. -/
theorem certifyRawCellExactV2?_termBase_accepted_implies_inner_succeeds
    {profile : PolyProfile} {scope : Nat}
    (generator : Generator) (payload : generator.payload scope)
    (children : RawTermChildrenV2 generator.binderShifts scope)
    {cert :
      CertifiedRawCellV2 profile scope
        (.termBase (.mkGen generator payload children))}
    (accepted :
      certifyRawCellExactV2? (profile := profile) scope
        (.termBase (.mkGen generator payload children)) = Except.ok cert) :
    (∃ admission : SupportedGeneratorV2 generator,
      supportedGeneratorV2? generator = some admission) ∧
    (∃ payloadEvidence : GenPayloadEvidence generator scope payload,
      genPayloadEvidence? payload = some payloadEvidence) ∧
    (∃ spine :
        CertifiedTermSpineV2 profile generator.childSpecs scope
          generator.binderShifts children,
      certifyChildrenInlineV2Fueled?
          ((RawTermV2.mkGen generator payload children).size + 1)
          scope generator.childSpecs
          (Generator.childSpecs_scopeShifts_eq_binderShifts generator).symm
          children
        = Except.ok spine) := by
  -- `rfl`-bridge exposing the dispatcher's reduced match body.  Both
  -- `supportedGeneratorV2?` and `genPayloadEvidence?` are `@[reducible]`
  -- so they pre-reduce to `some _` definitionally — the dispatcher's
  -- three-stage match collapses to the spine match.
  have dispatcherEq :
      certifyRawCellExactV2? (profile := profile) scope
        (.termBase (.mkGen generator payload children))
      = (match certifyChildrenInlineV2Fueled?
              ((RawTermV2.mkGen generator payload children).size + 1)
              scope generator.childSpecs
              (Generator.childSpecs_scopeShifts_eq_binderShifts
                generator).symm
              children with
         | .error rejection => .error rejection
         | .ok spine =>
             .ok ⟨generator.cellSort, CellBoundaryV2.trivial,
                  PolyCellV2.gen
                    (supportedGeneratorV2 generator)
                    (genPayloadEvidence payload) spine⟩) := rfl
  rw [dispatcherEq] at accepted
  -- The only non-definitional stage: spine certification.
  cases hSpine : certifyChildrenInlineV2Fueled?
          ((RawTermV2.mkGen generator payload children).size + 1)
          scope generator.childSpecs
          (Generator.childSpecs_scopeShifts_eq_binderShifts generator).symm
          children with
  | error rejection =>
    rw [hSpine] at accepted
    cases accepted
  | ok spine =>
    -- The admission and payload witnesses are produced by their
    -- `@[reducible]` total definitions; `rfl` discharges each
    -- existential equation by reducibility.  The spine equation is
    -- the genuine non-trivial witness, supplied by `hSpine` rewritten
    -- by `cases`.
    exact ⟨⟨supportedGeneratorV2 generator, rfl⟩,
           ⟨genPayloadEvidence payload, rfl⟩,
           ⟨spine, rfl⟩⟩

end LeanFX2.Foundation.PolyCell.Core
