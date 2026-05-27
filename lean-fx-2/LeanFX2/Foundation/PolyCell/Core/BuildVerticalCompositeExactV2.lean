import LeanFX2.Foundation.PolyCell.Core.CertifiedRawCellV2
import LeanFX2.Foundation.PolyCell.Core.CheckResult
import LeanFX2.Foundation.PolyCell.Core.RawCellV2DecEq

/-! # Foundation/PolyCell/Core/BuildVerticalCompositeExactV2 — vertical composer

This file ships `buildVerticalCompositeExactV2?`: the reconciler that
takes already-certified first and second cells (both at the same
dim+1) and constructs a certified vertical composite, or rejects with
a specific reason.

Direct v2 counterpart to v1's `buildVerticalCompositeExact?`
(`Core/Check.lean:1825`).

## The signature shape — value-level dim as DATA

v1 took `cdim : CellDim` as a TYPE parameter, forcing
`first second : PolyTerm profile (cdim + 1)` at the type level.  v2's
un-indexed raw layer cannot pin dim this way, so the equivalent
"dim positive" constraint travels as DATA:

* `parentDimension : Nat` parameter — the "n" in n+1
* `hFirstDim : firstRaw.dim = parentDimension + 1` witness
* `hSecondDim : secondRaw.dim = parentDimension + 1` witness

The recursive certifier (#162) computes `parentDimension` from
its structural recursion and supplies both witnesses before
invocation.  This function never case-splits on dim — the caller has
already discharged that proof obligation.

This is the **"thread coherence as data"** pattern that cleared
#159's `binderShifts` blocker, applied here to dim coherence.

## The reconciliation steps

`buildVerticalCompositeExactV2?` performs two Decidable checks before
building the certified cell:

1. **Sort match**: do the certified first and second cells share a
   sort?  (Vertical composition requires same-sort cells.)

2. **Middle endpoint match**: does the first cell's target endpoint
   equal the second cell's source endpoint?  (The shared "middle"
   that makes the composition well-defined.)

If either check fails, returns `.badVerticalBoundary`.  If both pass,
builds the `PolyCellV2.verticalComposite` cell via the proven
transport pattern.

## The transport pattern — generalize + subst + Eq.rec

After destructuring both certified packages and reconciling sort:

1. `generalize hGenFD : firstRaw.dim = freshFirstDim at firstBoundary
   firstCert hFirstDim` — abstracts firstRaw.dim in the listed
   hypotheses, leaving the goal untouched.
2. `subst hFirstDim` — after generalize, `hFirstDim` reads
   `freshFirstDim = parentDimension + 1`; subst rewrites
   `freshFirstDim → parentDimension + 1` throughout.  Now
   `firstBoundary` and `firstCert` have types at dim
   `parentDimension + 1` (which is def-equal to `RawCellV2 ×
   RawCellV2` per `CellBoundaryV2`'s succ arm).
3. Same dance for `secondRaw.dim`.
4. `cases firstBoundary` / `cases secondBoundary` destructure the
   boundaries into explicit source/middle/target raw cells — Lean's
   `cases` whnf-reduces `CellBoundaryV2 ... (parentDim+1) ...` to
   `Prod` and applies `Prod.mk`-elim.  This step is essential: it
   makes the typeclass search for `DecidableEq RawCellV2` reach the
   propext-free `decRawCellV2` instance from L0 #133.
5. `if hMiddle : ... then ... else ...` — uses `Decidable` typeclass
   directly (whereas `by_cases` would fall back to
   `Classical.propDecidable` here, producing a noncomputable
   declaration).
6. After both substs, `hGenFD : firstRaw.dim = parentDimension + 1`
   is the surviving witness used for the final transport.

## The dependent Eq.rec for the cell transport

The output's expected dim is `(.verticalComposite firstRaw secondRaw).dim`
which reduces to `firstRaw.dim`.  We've constructed the cell at
`parentDimension + 1`.  Transport from one to the other is via
`hGenFD.symm : parentDimension + 1 = firstRaw.dim`.

For the BOUNDARY field alone, simple `▸` works (motive is
`fun d => CellBoundaryV2 profile sort d scope`).

For the CERT field, the motive is **multi-argument** — both the dim
and the boundary (which itself depends on dim) need to transport in
lockstep.  Surface `▸` cannot infer this; we use an explicit
`Eq.rec` with motive

```
fun (targetDim : Nat) (transportEq : parentDim+1 = targetDim) =>
  PolyCellV2 profile sort targetDim scope
    (transportEq ▸ <boundary at parentDim+1>)
    (.verticalComposite firstRaw secondRaw)
```

At the base case (`targetDim = parentDim+1`, `transportEq = rfl`),
the motive evaluates to the type of `cellAtFresh`.  At the target
(`targetDim = firstRaw.dim`, `transportEq = hGenFD.symm`), the motive
matches the output's expected cert type.

## Zero-axiom verification

All tactics are propext-free:
* `if-then-else` with explicit Decidable (`CellSort.decEq`,
  propext-free `decRawCellV2` from L0 #133)
* `subst` via Eq.ndrec
* `cases` on a single-ctor struct / on a Prod (no wildcards)
* `generalize` via Eq.ndrec
* `▸` and explicit `Eq.rec` via standard recursor (propext-free)
* `exact` with direct constructor applications

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Build a certified vertical composite from a `parentDimension`,
two raw cells, two dim witnesses, and two already-certified packages.

This is the dispatcher for the `.verticalComposite` case of the
recursive certifier (#162).  The caller threads the parentDimension
and dim witnesses as data — the function never case-splits on dim
internally.

Returns a raw-indexed `CertifiedRawCellV2` whose rawCell is exactly
`.verticalComposite firstRaw secondRaw` (the input shape). -/
def buildVerticalCompositeExactV2? {profile : PolyProfile} {scope : Nat}
    (parentDimension : Nat)
    (firstRaw secondRaw : RawCellV2 scope)
    (hFirstDim : firstRaw.dim = parentDimension + 1)
    (hSecondDim : secondRaw.dim = parentDimension + 1)
    (certifiedFirst : CertifiedRawCellV2 profile scope firstRaw)
    (certifiedSecond : CertifiedRawCellV2 profile scope secondRaw) :
    Except CellCheckRejection
      (CertifiedRawCellV2 profile scope
        (.verticalComposite firstRaw secondRaw)) := by
  -- Step 1: Destructure both certified packages
  cases certifiedFirst with
  | mk firstSort firstBoundary firstCert =>
    cases certifiedSecond with
    | mk secondSort secondBoundary secondCert =>
      -- Step 2: Sort reconciliation via if-form (constructive Decidable)
      if hSort : firstSort = secondSort then
        subst hSort
        -- Step 3: Align firstRaw.dim to parentDimension + 1 via
        -- generalize + subst
        generalize hGenFD : firstRaw.dim = freshFirstDim at firstBoundary firstCert hFirstDim
        subst hFirstDim
        -- After: firstBoundary, firstCert at CellBoundaryV2 ... (parentDimension+1) ...
        -- hGenFD : firstRaw.dim = parentDimension + 1 (surviving witness)
        generalize hGenSD : secondRaw.dim = freshSecondDim at secondBoundary secondCert hSecondDim
        subst hSecondDim
        -- Step 4: Destructure boundaries into raw-cell components.
        -- CellBoundaryV2 ... (parentDim+1) ... whnf-reduces to Prod,
        -- so `cases` applies Prod's elim.
        cases firstBoundary with
        | mk firstSource firstMiddle =>
          cases secondBoundary with
          | mk secondMiddle secondTarget =>
            -- firstCert : PolyCellV2 ... firstSort (parentDim+1) scope
            --   (firstSource, firstMiddle) firstRaw
            -- secondCert : PolyCellV2 ... firstSort (parentDim+1) scope
            --   (secondMiddle, secondTarget) secondRaw
            -- Step 5: Middle endpoint reconciliation via if-form
            if hMiddle : firstMiddle = secondMiddle then
              subst hMiddle
              -- secondCert now has type
              --   PolyCellV2 ... firstSort (parentDim+1) scope (firstMiddle, secondTarget) secondRaw
              -- Step 6: Build the verticalComposite cell at dim (parentDimension + 1)
              -- The boundaries (firstSource, firstMiddle) and (firstMiddle, secondTarget)
              -- are def-equal to CellBoundaryV2.endpoints _ _ via @[reducible].
              let cellAtFresh :
                  PolyCellV2 profile firstSort (parentDimension + 1) scope
                    (CellBoundaryV2.endpoints firstSource secondTarget)
                    (.verticalComposite firstRaw secondRaw) :=
                PolyCellV2.verticalComposite
                  (source := firstSource)
                  (middle := firstMiddle)
                  (target := secondTarget)
                  firstCert secondCert
              -- Step 7: Transport back to firstRaw.dim via hGenFD.symm
              refine Except.ok ⟨firstSort, ?_, ?_⟩
              · -- boundary field at firstRaw.dim
                exact hGenFD.symm ▸
                  (CellBoundaryV2.endpoints firstSource secondTarget :
                    CellBoundaryV2 profile firstSort (parentDimension + 1) scope)
              · -- certifiedCell field at firstRaw.dim with the transported boundary;
                -- needs multi-arg motive transport via explicit Eq.rec
                exact @Eq.rec Nat (parentDimension + 1)
                  (fun (targetDim : Nat) (transportEq : parentDimension + 1 = targetDim) =>
                    PolyCellV2 profile firstSort targetDim scope
                      (transportEq ▸
                        (CellBoundaryV2.endpoints firstSource secondTarget :
                          CellBoundaryV2 profile firstSort (parentDimension + 1) scope))
                      (.verticalComposite firstRaw secondRaw))
                  cellAtFresh firstRaw.dim hGenFD.symm
            else
              exact .error .badVerticalBoundary
      else
        exact .error .badVerticalBoundary

end LeanFX2.Foundation.PolyCell.Core
