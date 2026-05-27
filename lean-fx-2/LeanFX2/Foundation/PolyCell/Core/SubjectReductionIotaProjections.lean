import LeanFX2.Foundation.PolyCell.Core.CertifiedToPolyCell
import LeanFX2.Foundation.PolyCell.Core.Step

/-! # Foundation/PolyCell/Core/SubjectReductionIotaProjections — nested-projection iotas

V2-L3.1 phase D step 8 (2026-05-27).  Ships SR arms 7-8: the
NESTED PROJECTION iotas.

After the 6 pure-projection iotas (5 base-case branch-selection +
`iotaBoolFalse`) shipped, the next family is **content-projection
iotas**.  These project a value out of an explicitly-constructed
wrapper, where the value sits TWO levels deep in the certified
spine rather than one:

  * iotaFstPair : `fst(pair fst snd) ↝ fst`
  * iotaSndPair : `snd(pair fst snd) ↝ snd`

## The nesting structure

Compare to the pure-projection iotas already shipped:

  * iotaBoolTrue source:
      `boolElim boolTrue thenBranch elseBranch`
      spine = `[boolTrue, thenBranch, elseBranch]`  (1 layer)

  * iotaFstPair source:
      `fst (pair firstValue secondValue)`
      outer spine = `[pair(firstValue, secondValue)]`         (layer 1)
      inner spine of pair = `[firstValue, secondValue]`        (layer 2)

The target (`firstValue`) lives in the INNER spine, so the proof
needs TWO levels of `cases` on `.gen` constructors and TWO
`headAtDim0` projections.

## Proof template (extends `iotaBoolTrue`)

```
cases sourceCert with
| intro sort outerCell =>
  cases outerCell with
  | gen _ _ outerSpine =>
    -- outerSpine.headAtDim0 rfl :
    --   PolyCell profile .term 0 scope CellBoundary.trivial
    --     (.termBase (.mkGen .gen_pair () ...))
    cases outerSpine.headAtDim0 rfl with
    | gen _ _ innerSpine =>
      -- For iotaFstPair: innerSpine.headAtDim0 rfl extracts firstValue.
      -- For iotaSndPair: innerSpine.tail.headAtDim0 rfl extracts secondValue.
      exact .intro .term (...)
```

## Why this extends — but does not break — the template

The new technique is purely COMPOSITIONAL: one extra `cases ... |
gen _ _ innerSpine =>` line on the result of the outer
`headAtDim0`.  The PolyCell returned by `headAtDim0` on a
`.termBase`-shaped raw cell has only ONE constructor arm (the
`.gen` arm — see iotaBoolTrue's docstring), so the inner `cases`
is single-armed and deterministic just like the outer one.

No HEq.  No subst.  No new dim-0 transport.  The existing
infrastructure (`headAtDim0`, the dim-0 boundary collapse via
`Subsingleton.elim`) was already designed to compose at arbitrary
depth.

## Sibling iotas

Pure projection iotas (already shipped, 6/6):
  * iotaBoolTrue, iotaBoolFalse — branch selection from boolElim
  * iotaNatElimZero, iotaNatRecZero — zero-branch from nat
    elimination
  * iotaListElimNil — nil-branch from list elimination
  * iotaOptionMatchNone — none-branch from option matching

Nested projection iotas (this commit, 2/2):
  * iotaFstPair, iotaSndPair — first/second from pair

Compound iotas (next family, 0/4):
  * iotaNatElimSucc, iotaListElimCons, iotaNatRecSucc,
    iotaOptionMatchSome — build a `gen_app` term after
    extracting wrapped components

These three families together cover all 12 pure-iota arms.  The
remaining SR arms are:
  * 4 compound iotas (above)
  * 2 identity iotas (idJ/idStrictRec on refl)
  * 1 beta (uses V2-L2.12 subst preservation)
  * 1 cong (structural induction over child step + spine recursion)

## Zero-axiom verification

Both arms close by the template above.  No `simp`, no `omega`,
no propext-touching tactics.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.

## Total SR arm progress

After this commit: 8/18 SR arms shipped.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- **SR arm: `Step.iotaFstPair` preserves `HasCertifiedCellDim0`.**

If `HasCertifiedCellDim0` holds on the source `fst(pair firstValue
secondValue)`, it holds on the target `firstValue`.

Nested-projection template: two layers of `cases` on `.gen`
constructors (outer for `gen_fst`, inner for `gen_pair`) followed
by a `headAtDim0` extraction from the inner spine. -/
theorem HasCertifiedCellDim0.preservedByIotaFstPair
    {profile : PolyProfile} {scope : Nat}
    {firstValue secondValue : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_fst ()
          (.childCons
            (.mkGen .gen_pair ()
              (.childCons firstValue
                (.childCons secondValue .childNil)))
            .childNil)
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) firstValue := by
  cases sourceCert with
  | intro sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      cases outerSpine with
      | cons pairCell _restSpine =>
        -- Generalize the concrete `termSameScope.cellSort` to a free
        -- variable BEFORE the inner `cases`.  The dep-elim matcher
        -- otherwise tries to solve `.term = generator.cellSort` for
        -- free `generator` (100+ generators satisfy this -> no unique
        -- solution), failing.  Replacing the concrete sort with a
        -- free var lets the matcher derive the generator from the
        -- (concrete) raw cell index alone -- exactly the discipline
        -- that lets the OUTER `cases outerCell` succeed.
        generalize hSort : (ChildSpec.termSameScope.cellSort) = innerSort
          at pairCell
        cases pairCell with
        | gen _ _ innerSpine =>
          exact .intro .term (innerSpine.headAtDim0 rfl)

/-- **SR arm: `Step.iotaSndPair` preserves `HasCertifiedCellDim0`.**

Symmetric to `preservedByIotaFstPair`: the only difference is that
the target lives at the SECOND position of the inner spine, so we
`tail` once before `headAtDim0`. -/
theorem HasCertifiedCellDim0.preservedByIotaSndPair
    {profile : PolyProfile} {scope : Nat}
    {firstValue secondValue : RawTerm scope}
    (sourceCert :
      HasCertifiedCellDim0 (profile := profile)
        (.mkGen .gen_snd ()
          (.childCons
            (.mkGen .gen_pair ()
              (.childCons firstValue
                (.childCons secondValue .childNil)))
            .childNil)
          : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) secondValue := by
  cases sourceCert with
  | intro sort outerCell =>
    cases outerCell with
    | gen _ _ outerSpine =>
      cases outerSpine with
      | cons pairCell _restSpine =>
        generalize hSort : (ChildSpec.termSameScope.cellSort) = innerSort
          at pairCell
        cases pairCell with
        | gen _ _ innerSpine =>
          -- (innerSpine.tail).headAtDim0 rfl extracts secondValue's
          -- cell after skipping firstValue.
          exact .intro .term ((innerSpine.tail).headAtDim0 rfl)

end LeanFX2.Foundation.PolyCell.Core
