import FX1Poly.Core.CertifiedRawCell
import FX1Poly.Core.CheckResult
import FX1Poly.Core.RawCellDecEq

/-! # Foundation/PolyCell/Core/BuildVerticalCompositeExact — vertical composer

This file ships `buildVerticalCompositeExact?`: the reconciler that
takes already-certified first and second cells (both at the same
dim+1) and constructs a certified vertical composite, or rejects with
a specific reason.

## The signature shape — value-level dim as DATA

The un-indexed raw layer cannot pin dim at the type level, so the
"dim positive" constraint travels as DATA:

* `parentDimension : Nat` parameter — the "n" in n+1
* `hFirstDim : firstRaw.dim = parentDimension + 1` witness
* `hSecondDim : secondRaw.dim = parentDimension + 1` witness

The recursive certifier computes `parentDimension` from its
structural recursion and supplies both witnesses before invocation.
This function never case-splits on dim — the caller has already
discharged that proof obligation.

This is the **"thread coherence as data"** pattern, applied here to
dim coherence.

## The reconciliation steps

`buildVerticalCompositeExact?` performs two Decidable checks before
building the certified cell:

1. **Sort match**: do the certified first and second cells share a
   sort?  (Vertical composition requires same-sort cells.)

2. **Middle endpoint match**: does the first cell's target endpoint
   equal the second cell's source endpoint?  (The shared "middle"
   that makes the composition well-defined.)

If either check fails, returns `.badVerticalBoundary`.  If both pass,
builds the `PolyCell.verticalComposite` cell via the proven
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
   `parentDimension + 1` (which is def-equal to `RawCell ×
   RawCell` per `CellBoundary`'s succ arm).
3. Same dance for `secondRaw.dim`.
4. `cases firstBoundary` / `cases secondBoundary` destructure the
   boundaries into explicit source/middle/target raw cells — Lean's
   `cases` whnf-reduces `CellBoundary ... (parentDim+1) ...` to
   `Prod` and applies `Prod.mk`-elim.  This step is essential: it
   makes the typeclass search for `DecidableEq RawCell` reach the
   propext-free `decRawCell` instance.
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
`fun d => CellBoundary profile sort d scope`).

For the CERT field, the motive is **multi-argument** — both the dim
and the boundary (which itself depends on dim) need to transport in
lockstep.  Surface `▸` cannot infer this; we use an explicit
`Eq.rec` with motive

```
fun (targetDim : Nat) (transportEq : parentDim+1 = targetDim) =>
  PolyCell profile sort targetDim scope
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
  propext-free `decRawCell`)
* `subst` via Eq.ndrec
* `cases` on a single-ctor struct / on a Prod (no wildcards)
* `generalize` via Eq.ndrec
* `▸` and explicit `Eq.rec` via standard recursor (propext-free)
* `exact` with direct constructor applications

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- Build a certified vertical composite from a `parentDimension`,
two raw cells, two dim witnesses, and two already-certified packages.

This is the dispatcher for the `.verticalComposite` case of the
recursive certifier.  The caller threads the parentDimension and
dim witnesses as data — the function never case-splits on dim
internally.

Returns a raw-indexed `CertifiedRawCell` whose rawCell is exactly
`.verticalComposite firstRaw secondRaw` (the input shape). -/
def buildVerticalCompositeExact? {profile : PolyProfile} {scope : Nat}
    (parentDimension : Nat)
    (firstRaw secondRaw : RawCell scope)
    (hFirstDim : firstRaw.dim = parentDimension + 1)
    (hSecondDim : secondRaw.dim = parentDimension + 1)
    (certifiedFirst : CertifiedRawCell profile scope firstRaw)
    (certifiedSecond : CertifiedRawCell profile scope secondRaw) :
    Except CellCheckRejection
      (CertifiedRawCell profile scope
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
        -- After: firstBoundary, firstCert at CellBoundary ... (parentDimension+1) ...
        -- hGenFD : firstRaw.dim = parentDimension + 1 (surviving witness)
        generalize hGenSD : secondRaw.dim = freshSecondDim at secondBoundary secondCert hSecondDim
        subst hSecondDim
        -- Step 4: Destructure boundaries into raw-cell components.
        -- CellBoundary ... (parentDim+1) ... whnf-reduces to Prod,
        -- so `cases` applies Prod's elim.
        cases firstBoundary with
        | mk firstSource firstMiddle =>
          cases secondBoundary with
          | mk secondMiddle secondTarget =>
            -- firstCert : PolyCell ... firstSort (parentDim+1) scope
            --   (firstSource, firstMiddle) firstRaw
            -- secondCert : PolyCell ... firstSort (parentDim+1) scope
            --   (secondMiddle, secondTarget) secondRaw
            -- Step 5: Middle endpoint reconciliation via if-form
            if hMiddle : firstMiddle = secondMiddle then
              subst hMiddle
              -- secondCert now has type
              --   PolyCell ... firstSort (parentDim+1) scope (firstMiddle, secondTarget) secondRaw
              -- Step 6: Build the verticalComposite cell at dim (parentDimension + 1)
              -- The boundaries (firstSource, firstMiddle) and (firstMiddle, secondTarget)
              -- are def-equal to CellBoundary.endpoints _ _ via @[reducible].
              let cellAtFresh :
                  PolyCell profile firstSort (parentDimension + 1) scope
                    (CellBoundary.endpoints firstSource secondTarget)
                    (.verticalComposite firstRaw secondRaw) :=
                PolyCell.verticalComposite
                  (source := firstSource)
                  (middle := firstMiddle)
                  (target := secondTarget)
                  firstCert secondCert
              -- Step 7: Transport back to firstRaw.dim via hGenFD.symm
              refine Except.ok ⟨firstSort, ?_, ?_⟩
              · -- boundary field at firstRaw.dim
                exact hGenFD.symm ▸
                  (CellBoundary.endpoints firstSource secondTarget :
                    CellBoundary profile firstSort (parentDimension + 1) scope)
              · -- certifiedCell field at firstRaw.dim with the transported boundary;
                -- needs multi-arg motive transport via explicit Eq.rec
                exact @Eq.rec Nat (parentDimension + 1)
                  (fun (targetDim : Nat) (transportEq : parentDimension + 1 = targetDim) =>
                    PolyCell profile firstSort targetDim scope
                      (transportEq ▸
                        (CellBoundary.endpoints firstSource secondTarget :
                          CellBoundary profile firstSort (parentDimension + 1) scope))
                      (.verticalComposite firstRaw secondRaw))
                  cellAtFresh firstRaw.dim hGenFD.symm
            else
              exact .error .badVerticalBoundary
      else
        exact .error .badVerticalBoundary

end FX1Poly.Core
