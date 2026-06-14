import FX1Poly.Core.IotaRuleTable
import FX1Poly.Core.StepTableEquivariance
import FX1Poly.Core.TableTakahashiTriangle
import FX1Poly.Core.IotaTableOrthogonality

/-! # DefUnivConfluence — DEFUNIV-CONFLUENCE (#1422), machine-checked

The DEFUNIV-SN spike (#1412) resolved that the definitional-univalence
rule needs no bespoke termination measure — it shrinks its reduct and
rides the shipped oriented-table SN (IOTA-T8).  That migrated the open
def-univ risk to ORTHOGONALITY / CONFLUENCE with the live βι rows.  This
file discharges that crux for the IOTA-T10 demonstrator.

The candidate table is the canonical 21-row `iotaRuleTable` extended
with `univalenceShapedDemoRule`, whose root pattern is

  `Id (Type@l) lhs rhs ↝ Equiv lhs rhs`

i.e. eliminator head `gen_idCode`, primary scrutinee head
`gen_universeCode`, reduct `builtGen gen_equivCode` from spine slots
1 and 2.  Two facts make the extension orthogonal by the shipped
decidable certificate (IOTA-T5 `WfIotaTable`):

  * `gen_idCode` is a TYPE FORMER, not an eliminator of any live row —
    the live identity ELIMINATORS key on `gen_idJ` / `gen_idStrictRec`,
    distinct generators — so the new root key
    `(gen_idCode, some 0, some gen_universeCode)` is distinct from every
    live key and shares no eliminator;
  * `gen_universeCode` is a TYPE head, not a constructor scrutinee head
    of any live row, so the elim-root / scrutinee-head disjointness
    survives.

Hence all four `WfIotaTable` checks re-decide by `rfl`, and — supplying
the one new row's scope-uniformity — the generic orthogonal-systems
confluence (IOTA-T6 `StepOverTable.confluent`) yields actual confluence
of the extended relation with ZERO bespoke critical-pair analysis.  This
is the green answer to #1422: the type-directed univalence-shaped rule
joins β/ι confluently, the genuine def-univ keystone.

Zero-axiom; audit-gated in `FX1PolyAudit/AuditDefUnivConfluence.lean`. -/

namespace FX1Poly.Core

/-- The candidate table: the canonical 21-row iota table extended with
the definitional-univalence demonstrator row. -/
abbrev candidateUnivalenceTable : List IotaRuleDesc :=
  iotaRuleTable ++ [univalenceShapedDemoRule]

/-- ★ **Orthogonality GO** — appending the univalence-shaped row
preserves the decidable well-formed-orthogonal-table certificate.  All
four `WfIotaTable` checks re-decide by `rfl`: the new root key is
distinct (its `gen_idCode` eliminator is fresh), the fresh eliminator is
vacuously slot-coherent, no scrutinee head is the `gen_idCode`
elim-root, and the row has a primary scrutinee.  This is the IOTA-T5
guard re-passing on the extended table. -/
theorem candidateUnivalenceTable_isWf : WfIotaTable candidateUnivalenceTable :=
  { keysAreDistinct := rfl
    elimDeterminesSlots := rfl
    elimRootsAvoidHeads := rfl
    rowsHavePrimaryScrutinee := rfl }

/-- The univalence-shaped row is scope-uniform: its eliminator head
`gen_idCode` is not the variable generator, its reduct's `gen_equivCode`
payload is the scope-invariant constant unit (the `cast` collapses to
`rfl`, as for every shipped `gen_app` app-chain row) over two
`spineChildAt` projections, and its single guard-free
`gen_universeCode` scrutinee spec is scope-uniform. -/
theorem univalenceShapedDemoRule_isScopeUniform :
    univalenceShapedDemoRule.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra,
    ⟨⟨fun contra => Generator.noConfusion contra, fun _ _ _ => rfl⟩,
      ⟨⟩, ⟨⟩, ⟨⟩⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩

/-- Appending one scope-uniform row to a scope-uniform table keeps every
row scope-uniform.  Proved by structural recursion over the prefix with
`List.Mem` casing — no `mem_append` iff lemma, so propext-free. -/
theorem appendedUnivalenceRowKeepsScopeUniform :
    (table : List IotaRuleDesc) →
    (∀ rule, rule ∈ table → rule.IsScopeUniform) →
    univalenceShapedDemoRule.IsScopeUniform →
    ∀ rule, rule ∈ table ++ [univalenceShapedDemoRule] →
      rule.IsScopeUniform
  | [], _, extraUniform, _, isRow => by
      cases isRow with
      | head => exact extraUniform
      | tail _ emptyMem => cases emptyMem
  | head :: rest, tableUniform, extraUniform, _, isRow => by
      cases isRow with
      | head => exact tableUniform head (List.Mem.head _)
      | tail _ restMem =>
          exact appendedUnivalenceRowKeepsScopeUniform rest
            (fun innerRule innerMem =>
              tableUniform innerRule (List.Mem.tail _ innerMem))
            extraUniform _ restMem

/-- Every row of the candidate table is scope-uniform — the live prefix
via the shipped `iotaRuleTable_isScopeUniform`, the appended row via
`univalenceShapedDemoRule_isScopeUniform`. -/
theorem candidateUnivalenceTable_isScopeUniform :
    ∀ rule, rule ∈ candidateUnivalenceTable → rule.IsScopeUniform :=
  appendedUnivalenceRowKeepsScopeUniform iotaRuleTable
    iotaRuleTable_isScopeUniform univalenceShapedDemoRule_isScopeUniform

/-- ★★ **DEFUNIV-CONFLUENCE (#1422)** — the candidate table (canonical
βι table + the definitional-univalence row) is CONFLUENT.  Both IOTA-T6
certificates discharge — orthogonality (`candidateUnivalenceTable_isWf`)
and scope-uniformity (`candidateUnivalenceTable_isScopeUniform`) — so
the generic orthogonal-systems confluence theorem applies with no
bespoke critical-pair work.  The type-directed univalence-shaped rule
joins β/ι confluently. -/
theorem candidateUnivalenceTable_isConfluent {scope : Nat} :
    Confluent
      (fun source target : RawTerm scope =>
        StepOverTable candidateUnivalenceTable source target) :=
  StepOverTable.confluent candidateUnivalenceTable_isWf
    candidateUnivalenceTable_isScopeUniform

end FX1Poly.Core
