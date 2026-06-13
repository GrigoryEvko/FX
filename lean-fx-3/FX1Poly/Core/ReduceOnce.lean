import FX1Poly.Core.TableReduceOnce
import FX1Poly.Core.StepTable

/-! # FX1Poly/Core/ReduceOnce
    — one deterministic reduction step as a total function, TABLE-BACKED.

`RawTerm.reduceOnce : RawTerm scope → Option (RawTerm scope)` is the leftmost-outermost one-step
reducer: fire a root redex if some rule matches, otherwise descend the child spine to the first
reducible child.  Since the IOTA-T11 reducer rebase, the ENGINE is the generic table walk
(`reduceOnceOverTable`, TableReduceOnce.lean) instantiated at the 17-row LEGACY table — the rows
that mirror the bespoke `Step` exactly — so the per-iota `fireRootRedex` dispatch is no longer in
this chain.  The spec surface is unchanged:

* `reduceOnce_sound` — every produced reduct is a genuine `Step`: the table walk's generic
  soundness gives a `StepOverTable iotaRuleTable` step, and the IOTA-T1 backward adequacy
  (`StepOverTable.toStep`) maps it onto the bespoke relation;
* the completeness direction (`reduceOnce = none → isStepNormalForm`, ReduceOnceComplete.lean)
  pins the halting set, turning the existential `exists_normalForm_of_isStronglyNormalizing` into
  a real `RawTerm`-valued normalizer (`RawTerm.normalize`, Normalize.lean) iterated along
  `Acc StepSuccessor`.

The CANONICAL reducer is `StepTable.reduceOnce` (the full table, endpoint-β live); this
legacy-table instance exists for the surviving `Step`-stated consumers and retires with the
bespoke relation.

## Zero-axiom verification

Direct instantiations of the separately-gated generic table walk (`reduceOnceOverTable` /
`reduceOnceSpineOverTable` + soundness) composed with the adequacy.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open Foundation

/-- **One reduction step, as a function.**  The generic table walk at the canonical table: fire a
root redex if some legacy row matches; otherwise descend the child spine to the first reducible
child.  `none` means no redex was found at the root or in any child (the leftmost-outermost
strategy bottomed out). -/
def RawTerm.reduceOnce {scope : Nat} (term : RawTerm scope) : Option (RawTerm scope) :=
  reduceOnceOverTable iotaRuleTable term

/-- **One reduction step inside a child spine.**  Reduce the first reducible child, leaving the
rest fixed; `none` if no child reduces. -/
def RawTermChildren.reduceOnceSpine {binderShifts : List Nat} {scope : Nat}
    (children : RawTermChildren binderShifts scope) :
    Option (RawTermChildren binderShifts scope) :=
  reduceOnceSpineOverTable iotaRuleTable children

/-- **Soundness of `reduceOnce`.**  Every reduct it produces is a genuine `Step` — the generic
table-walk soundness mapped back through the adequacy. -/
theorem RawTerm.reduceOnce_sound {scope : Nat} {term reduct : RawTerm scope}
    (reduced : RawTerm.reduceOnce term = some reduct) :
    Step term reduct :=
  (reduceOnceOverTable_sound (table := iotaRuleTable) reduced).toStep

/-- **Soundness of `reduceOnceSpine`.**  The reduced spine is a genuine `StepChildren` — the
spine companion mapped back through the adequacy. -/
theorem RawTermChildren.reduceOnceSpine_sound {binderShifts : List Nat} {scope : Nat}
    {children reducedChildren : RawTermChildren binderShifts scope}
    (reduced : RawTermChildren.reduceOnceSpine children = some reducedChildren) :
    StepChildren children reducedChildren :=
  (reduceOnceSpineOverTable_sound (table := iotaRuleTable)
    reduced).toStepChildren

end FX1Poly.Core
