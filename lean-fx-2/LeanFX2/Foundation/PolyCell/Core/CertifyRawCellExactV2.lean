import LeanFX2.Foundation.PolyCell.Core.CertifiedRawCellV2
import LeanFX2.Foundation.PolyCell.Core.BuildGeneratingCellExactV2
import LeanFX2.Foundation.PolyCell.Core.BuildVerticalCompositeExactV2
import LeanFX2.Foundation.PolyCell.Core.RawSizeV2
import LeanFX2.Foundation.PolyCell.Core.PolyCellV2Helpers
import LeanFX2.Foundation.PolyCell.Core.RawCellV2DecEq

/-! # Foundation/PolyCell/Core/CertifyRawCellExactV2 — the recursive workhorse

This file ships `certifyRawCellExactV2?`: ONE recursion over
`RawCellV2` that certifies the entire non-`horizontalComposite`
fragment at every dimension.  This is the architectural HEADLINE of
the v2 certifier — every raw cell either certifies cleanly or
rejects with a specific reason.

Direct v2 counterpart to v1's `certifyRawCellExact?`
(`Core/Check.lean:1851`).

## Architecture — fuel-based mutual recursion

The recursion spans both `RawCellV2` and `RawTermChildrenV2`, which
are not in the same mutual inductive block.  Lean's structural
recursion cannot see across the inductive boundary (the
`.termBase` constructor wraps a `RawTermV2` inside a `RawCellV2`).

Two standard solutions exist:

1. **Mutual block with `termination_by` + per-function measure** +
   `decreasing_by` proving custom Nat inequalities.  In Lean 4
   v4.29.1 this approach hits a substitution gap: the
   `decreasing_by` goal references the function parameter
   (e.g. `children`) abstractly, even when a `match`/`cases`
   in the body has pattern-substituted it.  Without `omega`
   (which leaks `propext` + `Quot.sound`), the proof obligation
   `(.childCons head rest).size = children.size` is not
   discharable.

2. **Fuel-based structural recursion on Nat** (chosen here).  Each
   function carries an explicit `fuel : Nat` parameter that
   decreases by exactly one on each recursive call.  Lean's
   structural recursion on Nat is straightforward and propext-free.
   When fuel reaches zero, the function rejects with
   `.fuelExhausted`.  A top-level wrapper supplies sufficient fuel
   (`raw.size + 1`) so the rejection path is unreachable for
   well-formed inputs.

The fuel approach trades a parameter and an unreachable rejection
case for a far simpler termination story.  Soundness lemmas (in
later tasks) prove the fuel-allocation in the wrapper always suffices.

## The five-way dispatch on RawCellV2

`certifyRawCellExactV2Fueled?` dispatches on the input raw:

* `.termBase termRaw` — destructure termRaw = `.mkGen gen payload
  children`, look up admission + payload evidence + certify the
  children spine, package via `PolyCellV2.gen`.
* `.generatingCell ruleId source target` — recurse on source and
  target, dispatch to `buildGeneratingCellExactV2?` (#160).
* `.verticalComposite first second` — recurse on first and second,
  pattern-match on first.dim to obtain `parentDimension`, dispatch
  to `buildVerticalCompositeExactV2?` (#161) with witnesses.
* `.horizontalComposite _ _` — reject with `.unsupportedCompH`
  (Gray-tensor semantics pending Axis 6).
* `.identityCell base` — recurse on base, build via
  `PolyCellV2.identityCell` (no transport needed — the output's
  rawCell dim equals `base.dim + 1` definitionally).

## The dim transport in `certifyChildrenInlineV2Fueled?`

After certifying a child cell as `(.termBase headRaw)`, its dim is
`(.termBase headRaw).dim = 0` definitionally.  The cons constructor
expects `headSpec.cellDimension`.  For fxProfile these are always
equal (every ChildSpecV2 has cellDimension = 0), but the function
handles the general case via:

1. Decidable check `hDim : headSpec.cellDimension = 0`.
2. Explicit `Eq.rec` with multi-arg motive abstracting both the
   dim AND the dim-dependent boundary in lockstep.

Same pattern as `buildVerticalCompositeExactV2?` (#161).

## Zero-axiom verification

All tactics are propext-free:
* Structural recursion on Nat (fuel)
* Pattern matching on closed inductives (full enumeration)
* `cases`, `subst`, `if-then-else` with explicit Decidable
* `▸` and explicit `Eq.rec` (standard recursors)

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

mutual

/-- Fueled recursive certifier.  Decreases `fuel` by 1 on each
recursive call.  When `fuel = 0`, rejects with `.fuelExhausted`.

For well-formed inputs, the top-level wrapper supplies
`raw.size + 1` fuel which is always sufficient. -/
def certifyRawCellExactV2Fueled? {profile : PolyProfile} (fuel : Nat)
    (scope : Nat) (raw : RawCellV2 scope) :
    Except CellCheckRejection (CertifiedRawCellV2 profile scope raw) :=
  match fuel with
  | 0 => .error .fuelExhausted
  | fuel' + 1 =>
    match raw with
    | .termBase termRaw =>
        match termRaw with
        | .mkGen generator payload children =>
            match supportedGeneratorV2? generator with
            | none => .error .unknownGenerator
            | some admission =>
              match genPayloadEvidence? payload with
              | none => .error .badPayload
              | some payloadEvidence =>
                let coherence :=
                  (Generator.childSpecs_scopeShifts_eq_binderShifts generator).symm
                match certifyChildrenInlineV2Fueled? fuel' scope
                        generator.childSpecs coherence children with
                | .error rejection => .error rejection
                | .ok spine =>
                    .ok ⟨generator.cellSort, CellBoundaryV2.trivial,
                         PolyCellV2.gen admission payloadEvidence spine⟩
    | .generatingCell ruleId source target =>
        match certifyRawCellExactV2Fueled? fuel' scope source with
        | .error rejection => .error rejection
        | .ok certSource =>
          match certifyRawCellExactV2Fueled? fuel' scope target with
          | .error rejection => .error rejection
          | .ok certTarget =>
              buildGeneratingCellExactV2? ruleId source target certSource certTarget
    | .verticalComposite first second =>
        match certifyRawCellExactV2Fueled? fuel' scope first with
        | .error rejection => .error rejection
        | .ok certFirst =>
          match certifyRawCellExactV2Fueled? fuel' scope second with
          | .error rejection => .error rejection
          | .ok certSecond =>
              match hFirstDim : first.dim with
              | 0 => .error .badVerticalBoundary
              | parentDim + 1 =>
                  if hDimEq : first.dim = second.dim then
                    let hSecondDim : second.dim = parentDim + 1 :=
                      hDimEq.symm.trans hFirstDim
                    buildVerticalCompositeExactV2? parentDim first second
                      hFirstDim hSecondDim certFirst certSecond
                  else
                    .error .badVerticalBoundary
    | .horizontalComposite _ _ => .error .unsupportedCompH
    | .identityCell base =>
        match certifyRawCellExactV2Fueled? fuel' scope base with
        | .error rejection => .error rejection
        | .ok certBase =>
            .ok ⟨certBase.sort,
                 CellBoundaryV2.endpoints base base,
                 PolyCellV2.identityCell certBase.certifiedCell⟩

/-- Fueled children-spine walker.  Walks `childSpecs` and `children`
in parallel, certifying each head via
`certifyRawCellExactV2Fueled?` on `(.termBase headRaw)`, reconciling
sort and dim via Decidable checks + `Eq.rec` transport, and
combining via `CertifiedTermSpineV2.cons`. -/
def certifyChildrenInlineV2Fueled? {profile : PolyProfile} (fuel : Nat)
    (parentScope : Nat) (childSpecs : List ChildSpecV2)
    {binderShifts : List Nat}
    (coherence : binderShifts = childSpecs.map (·.scopeShift))
    (children : RawTermChildrenV2 binderShifts parentScope) :
    Except CellCheckRejection
      (CertifiedTermSpineV2 profile childSpecs parentScope
        binderShifts children) := by
  subst coherence
  match fuel with
  | 0 => exact .error .fuelExhausted
  | fuel' + 1 =>
    match childSpecs, children with
    | [], .childNil => exact .ok .nil
    | headSpec :: restSpecs, .childCons headRaw restRaws =>
        let headResult :
            Except CellCheckRejection
              (CertifiedRawCellV2 profile (parentScope + headSpec.scopeShift)
                (.termBase headRaw)) :=
          certifyRawCellExactV2Fueled? fuel'
            (parentScope + headSpec.scopeShift) (.termBase headRaw)
        cases headResult with
        | error rejection => exact .error rejection
        | ok headCert =>
          cases headCert with
          | mk headSort headBoundary headCertCell =>
            if hSort : headSort = headSpec.cellSort then
              subst hSort
              if hDim : headSpec.cellDimension = 0 then
                let restResult :
                    Except CellCheckRejection
                      (CertifiedTermSpineV2 profile restSpecs parentScope
                        (restSpecs.map (·.scopeShift)) restRaws) :=
                  certifyChildrenInlineV2Fueled? fuel' parentScope
                    restSpecs rfl restRaws
                cases restResult with
                | error rejection => exact .error rejection
                | ok restSpine =>
                    let cellAtSpecDim :
                        PolyCellV2 profile headSpec.cellSort
                          headSpec.cellDimension
                          (parentScope + headSpec.scopeShift)
                          (hDim.symm ▸ headBoundary)
                          (.termBase headRaw) :=
                      @Eq.rec Nat 0
                        (fun (targetDim : Nat)
                             (transportEq : 0 = targetDim) =>
                          PolyCellV2 profile headSpec.cellSort targetDim
                            (parentScope + headSpec.scopeShift)
                            (transportEq ▸ headBoundary)
                            (.termBase headRaw))
                        headCertCell headSpec.cellDimension hDim.symm
                    exact .ok (.cons cellAtSpecDim restSpine)
              else
                exact .error .wrongChildShape
            else
              exact .error .wrongChildShape

end -- mutual

/-- Top-level recursive certifier — supplies sufficient fuel
(`raw.size + 1`) to the fueled implementation so the `.fuelExhausted`
path is unreachable for well-formed inputs.

This is the user-facing entry point per the polycell.md §4 spec. -/
def certifyRawCellExactV2? {profile : PolyProfile} (scope : Nat)
    (raw : RawCellV2 scope) :
    Except CellCheckRejection (CertifiedRawCellV2 profile scope raw) :=
  certifyRawCellExactV2Fueled? (raw.size + 1) scope raw

end LeanFX2.Foundation.PolyCell.Core
