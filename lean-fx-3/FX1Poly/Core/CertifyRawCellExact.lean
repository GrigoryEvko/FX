import FX1Poly.Core.CertifiedRawCell
import FX1Poly.Core.BuildGeneratingCellExact
import FX1Poly.Core.BuildVerticalCompositeExact
import FX1Poly.Core.RawSize
import FX1Poly.Core.PolyCellHelpers
import FX1Poly.Core.RawCellDecEq

/-! # Foundation/PolyCell/Core/CertifyRawCellExact — the recursive workhorse

This file ships `certifyRawCellExact?`: ONE recursion over
`RawCell` that certifies the entire non-`horizontalComposite`
fragment at every dimension.  This is the architectural HEADLINE of
the v2 certifier — every raw cell either certifies cleanly or
rejects with a specific reason.

Direct v2 counterpart to v1's `certifyRawCellExact?`
(`Core/Check.lean:1851`).

## Architecture — fuel-based mutual recursion

The recursion spans both `RawCell` and `RawTermChildren`, which
are not in the same mutual inductive block.  Lean's structural
recursion cannot see across the inductive boundary (the
`.termBase` constructor wraps a `RawTerm` inside a `RawCell`).

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

## The five-way dispatch on RawCell

`certifyRawCellExactFueled?` dispatches on the input raw:

* `.termBase termRaw` — destructure termRaw = `.mkGen gen payload
  children`, look up admission + payload evidence + certify the
  children spine, package via `PolyCell.gen`.
* `.generatingCell ruleId source target` — recurse on source and
  target, dispatch to `buildGeneratingCellExact?` (#160).
* `.verticalComposite first second` — recurse on first and second,
  pattern-match on first.dim to obtain `parentDimension`, dispatch
  to `buildVerticalCompositeExact?` (#161) with witnesses.
* `.horizontalComposite _ _` — reject with `.unsupportedCompH`
  (Gray-tensor semantics pending Axis 6).
* `.identityCell base` — recurse on base, build via
  `PolyCell.identityCell` (no transport needed — the output's
  rawCell dim equals `base.dim + 1` definitionally).

## The dim transport in `certifyChildrenInlineFueled?`

After certifying a child cell as `(.termBase headRaw)`, its dim is
`(.termBase headRaw).dim = 0` definitionally.  The cons constructor
expects `headSpec.cellDimension`.  For fxProfile these are always
equal (every ChildSpec has cellDimension = 0), but the function
handles the general case via:

1. Decidable check `hDim : headSpec.cellDimension = 0`.
2. Explicit `Eq.rec` with multi-arg motive abstracting both the
   dim AND the dim-dependent boundary in lockstep.

Same pattern as `buildVerticalCompositeExact?` (#161).

## Zero-axiom verification

All tactics are propext-free:
* Structural recursion on Nat (fuel)
* Pattern matching on closed inductives (full enumeration)
* `cases`, `subst`, `if-then-else` with explicit Decidable
* `▸` and explicit `Eq.rec` (standard recursors)

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

mutual

/-- Fueled recursive certifier.  Decreases `fuel` by 1 on each
recursive call.  When `fuel = 0`, rejects with `.fuelExhausted`.

For well-formed inputs, the top-level wrapper supplies
`raw.size + 1` fuel which is always sufficient. -/
def certifyRawCellExactFueled? {profile : PolyProfile} (fuel : Nat)
    (scope : Nat) (raw : RawCell scope) :
    Except CellCheckRejection (CertifiedRawCell profile scope raw) :=
  match fuel with
  | 0 => .error .fuelExhausted
  | fuel' + 1 =>
    match raw with
    | .termBase termRaw =>
        match termRaw with
        | .mkGen generator payload children =>
            match supportedGenerator? generator with
            | none => .error .unknownGenerator
            | some admission =>
              match genPayloadEvidence? payload with
              | none => .error .badPayload
              | some payloadEvidence =>
                let coherence :=
                  (Generator.childSpecs_scopeShifts_eq_binderShifts generator).symm
                match certifyChildrenInlineFueled? fuel' scope
                        generator.childSpecs coherence children with
                | .error rejection => .error rejection
                | .ok spine =>
                    .ok ⟨generator.cellSort, CellBoundary.trivial,
                         PolyCell.gen admission payloadEvidence spine⟩
    | .generatingCell ruleId source target =>
        match certifyRawCellExactFueled? fuel' scope source with
        | .error rejection => .error rejection
        | .ok certSource =>
          match certifyRawCellExactFueled? fuel' scope target with
          | .error rejection => .error rejection
          | .ok certTarget =>
              buildGeneratingCellExact? ruleId source target certSource certTarget
    | .verticalComposite first second =>
        match certifyRawCellExactFueled? fuel' scope first with
        | .error rejection => .error rejection
        | .ok certFirst =>
          match certifyRawCellExactFueled? fuel' scope second with
          | .error rejection => .error rejection
          | .ok certSecond =>
              match hFirstDim : first.dim with
              | 0 => .error .badVerticalBoundary
              | parentDim + 1 =>
                  if hDimEq : first.dim = second.dim then
                    let hSecondDim : second.dim = parentDim + 1 :=
                      hDimEq.symm.trans hFirstDim
                    buildVerticalCompositeExact? parentDim first second
                      hFirstDim hSecondDim certFirst certSecond
                  else
                    .error .badVerticalBoundary
    | .horizontalComposite _ _ => .error .unsupportedCompH
    | .identityCell base =>
        match certifyRawCellExactFueled? fuel' scope base with
        | .error rejection => .error rejection
        | .ok certBase =>
            .ok ⟨certBase.sort,
                 CellBoundary.endpoints base base,
                 PolyCell.identityCell certBase.certifiedCell⟩

/-- Fueled children-spine walker.  Walks `childSpecs` and `children`
in parallel, certifying each head via
`certifyRawCellExactFueled?` on `(.termBase headRaw)`, reconciling
sort and dim via Decidable checks + `Eq.rec` transport, and
combining via `CertifiedTermSpine.cons`. -/
def certifyChildrenInlineFueled? {profile : PolyProfile} (fuel : Nat)
    (parentScope : Nat) (childSpecs : List ChildSpec)
    {binderShifts : List Nat}
    (coherence : binderShifts = childSpecs.map (·.scopeShift))
    (children : RawTermChildren binderShifts parentScope) :
    Except CellCheckRejection
      (CertifiedTermSpine profile childSpecs parentScope
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
              (CertifiedRawCell profile (parentScope + headSpec.scopeShift)
                (.termBase headRaw)) :=
          certifyRawCellExactFueled? fuel'
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
                      (CertifiedTermSpine profile restSpecs parentScope
                        (restSpecs.map (·.scopeShift)) restRaws) :=
                  certifyChildrenInlineFueled? fuel' parentScope
                    restSpecs rfl restRaws
                cases restResult with
                | error rejection => exact .error rejection
                | ok restSpine =>
                    let cellAtSpecDim :
                        PolyCell profile headSpec.cellSort
                          headSpec.cellDimension
                          (parentScope + headSpec.scopeShift)
                          (hDim.symm ▸ headBoundary)
                          (.termBase headRaw) :=
                      @Eq.rec Nat 0
                        (fun (targetDim : Nat)
                             (transportEq : 0 = targetDim) =>
                          PolyCell profile headSpec.cellSort targetDim
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
def certifyRawCellExact? {profile : PolyProfile} (scope : Nat)
    (raw : RawCell scope) :
    Except CellCheckRejection (CertifiedRawCell profile scope raw) :=
  certifyRawCellExactFueled? (raw.size + 1) scope raw

end FX1Poly.Core
