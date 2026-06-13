import FX1Poly.Core.StepOverBundleConfluence
import FX1Poly.Core.StepTableEquivariance

/-! # FX1Poly/Core/IotaTableOperationalExtension — IOTA-T12: the
operational-axis profile extension as a VALUE with machine-checked
admission.

This is the payoff of the RW-5 bundle (`StepOver`) + the RW-6 generic
instantiation gate (`StepOver.iotaOnlyConfluent`): a profile that
extends the OPERATIONAL axis by ADDING iota rows inherits bundle
confluence FOR FREE, provided the extended table re-passes the
decidable well-formedness (`WfIotaTable`) + scope-uniformity
certificates.  No fresh critical-pair work — exactly RW-6's
no-regression promise, now packaged as an extension VALUE.

  * `OperationalAxisExtension` — the extension VALUE over a fixed base
    iota table: the rows it adds, plus the two RE-DECIDED certificates
    for the EXTENDED table (`base ++ added`).  IOTA-T5's "re-decides on
    table growth" discipline made into a value: adding rows is
    admissible exactly when the extended certificates close.
  * `OperationalAxisExtension.extendedTable` — `base ++ addedIotaRows`.
  * `OperationalAxisExtension.preservesConfluence` — ★ the admission
    payoff: the extended bundle's `StepOver` is confluent.  Pure
    instantiation of the generic gate; zero new metatheory.
  * `OperationalAxisExtension.floor` — the empty extension (adds no
    rows): always admissible, the honest floor mirroring
    `AdmissibleProfile.bottom`.  Its certificates discharge by the
    canonical-table certificates the empty append computes back to.
  * `floor_extendedTable_eq` — the floor's table IS the canonical
    21-row table (the empty append reduces).

## Honest scope

The general theorem holds for ANY certified extension; the certificate
fields are re-decided per extension (the orthogonality guard).  The
FLOOR is the only shipped concrete inhabitant — every live eliminator
generator already sits in the canonical table, so no spare eliminator
is available for a non-vacuous demonstration row.  This mirrors how the
ledger-admission discipline ships `AdmissibleProfile.bottom` plus the
FX-specific admissions, not an open-ended family.

## Zero-axiom verification

The structure + the generic-gate instantiation + concrete certificates
that close by computation on the literal table.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  The
empty-append certificates reduce on the concrete cons-list, so no
`List.append_nil` (which would leak `propext`) is used.  Per-declaration
gated in `FX1PolyAudit/AuditIotaTableOperationalExtension.lean`. -/

namespace FX1Poly.Core

/-- An operational-axis profile extension over a fixed base iota table:
the rows it adds, together with the re-decided certificates that the
EXTENDED table (`baseIotaTable ++ addedIotaRows`) is still a well-formed
orthogonal, scope-uniform iota table.  Adding rows is admissible exactly
when these two certificates close — the value carries its own proof of
admission. -/
structure OperationalAxisExtension (baseIotaTable : List IotaRuleDesc) where
  /-- The iota rows this extension contributes on top of the base. -/
  addedIotaRows : List IotaRuleDesc
  /-- The extended table re-passes the decidable orthogonality guard. -/
  extendedIsWf : WfIotaTable (baseIotaTable ++ addedIotaRows)
  /-- Every row of the extended table is scope-uniform. -/
  extendedIsScopeUniform :
    ∀ rule, rule ∈ baseIotaTable ++ addedIotaRows → rule.IsScopeUniform

/-- The extended iota table the extension presents — the base rows
followed by the added rows. -/
@[reducible] def OperationalAxisExtension.extendedTable
    {baseIotaTable : List IotaRuleDesc}
    (extension : OperationalAxisExtension baseIotaTable) :
    List IotaRuleDesc :=
  baseIotaTable ++ extension.addedIotaRows

/-- ★ **The admission payoff for the operational axis.**  Extending the
operational axis by adding rows preserves bundle confluence: the
extended bundle's `StepOver` is confluent.  Pure instantiation of the
generic gate `StepOver.iotaOnlyConfluent` at the extension's re-decided
certificates — no fresh critical-pair work, exactly RW-6's
no-regression promise.  This is the sense in which
`extendProfile_preserves_admissible` holds for the operational axis:
any `OperationalAxisExtension` VALUE yields the confluence guarantee. -/
theorem OperationalAxisExtension.preservesConfluence
    {baseIotaTable : List IotaRuleDesc}
    (extension : OperationalAxisExtension baseIotaTable)
    {scope : Nat} :
    Confluent (fun source target : RawTerm scope =>
      StepOver { iotaRows := extension.extendedTable, etaRows := [] }
        source target) :=
  StepOver.iotaOnlyConfluent extension.extendedIsWf
    extension.extendedIsScopeUniform

/-- The FLOOR extension over the canonical table: adds NO rows.  Always
admissible — the extended table `iotaRuleTable ++ []` computes back to
`iotaRuleTable` on the literal cons-list, so the canonical certificates
discharge the obligations by `rfl` (no `List.append_nil` lemma, hence no
`propext`).  The honest floor, mirroring `AdmissibleProfile.bottom`. -/
def OperationalAxisExtension.floor :
    OperationalAxisExtension iotaRuleTable where
  addedIotaRows := []
  extendedIsWf :=
    { keysAreDistinct := rfl
      elimDeterminesSlots := rfl
      elimRootsAvoidHeads := rfl
      rowsHavePrimaryScrutinee := rfl }
  extendedIsScopeUniform := fun rule membership =>
    iotaRuleTable_isScopeUniform rule membership

/-- The floor's extended table IS the canonical 21-row table — the empty
append reduces on the literal cons-list. -/
theorem floor_extendedTable_eq :
    OperationalAxisExtension.floor.extendedTable = iotaRuleTable := rfl

end FX1Poly.Core
