import FX1Poly.Core.EtaTableOrthogonality

/-! # EtaObservationCompleteness — ETA-T6 increment 1: observations
cover every iota destructor

The typed eta-VALIDITY ingredient: a raw eta row asserts that its
intro cell is determined by the listed observations — that assertion
is only as strong as the list.  If iota can destruct the former
through an eliminator the row does NOT observe, typed eta-validity is
false (pair eta listing only `fst` would identify pairs that differ
in their second component).  The certificate below is the decidable
check: for every iota row whose pattern scrutinizes the eta row's
intro head, the eta row observes through that iota row's eliminator.
Destructors are derived OPERATIONALLY — from the iota table itself —
so the certificate re-decides automatically when either table grows.

Typed-tier eta rows (no syntactic pattern, type-directed firing) are
exempt: their validity is the typing gate's job, not an observation
list's.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditEtaObservationCompleteness.lean`. -/

namespace FX1Poly.Core

/-! ## The checkers -/

/-- Does some observation in the list observe through this head? -/
def observationsContainObserverHead :
    List EtaObservationSpec → Generator → Bool
  | [], _ => false
  | spec :: restSpecs, destructorHead =>
      if spec.observerHead = destructorHead then true
      else observationsContainObserverHead restSpecs destructorHead

/-- Does some scrutinee spec in the list scrutinize this former? -/
def scrutineeListScrutinizes : List ScrutineeSpec → Generator → Bool
  | [], _ => false
  | spec :: restSpecs, former =>
      if spec.head = former then true
      else scrutineeListScrutinizes restSpecs former

/-- One eta row's observations cover every iota destructor of its
former: every iota row whose pattern scrutinizes the intro head is
observed through its eliminator. -/
def rowObservationsCoverIotaDestructors (etaRule : EtaRuleDesc)
    (iotaTable : List IotaRuleDesc) : Bool :=
  listForall
    (fun iotaRule =>
      if scrutineeListScrutinizes iotaRule.scrutinees
          etaRule.introGenerator then
        observationsContainObserverHead etaRule.observations
          iotaRule.elimGenerator
      else true)
    iotaTable

/-- Table-level: every RAW eta row covers its former's iota
destructors; typed-tier rows are exempt. -/
def allRawObservationsCoverIotaDestructors (etaTable : List EtaRuleDesc)
    (iotaTable : List IotaRuleDesc) : Bool :=
  listForall
    (fun etaRule =>
      if etaRule.requiresTypedFiring = true then true
      else rowObservationsCoverIotaDestructors etaRule iotaTable)
    etaTable

/-! ## The canonical pin -/

/-- ★ The canonical tables are observation-COMPLETE: etaLam covers
beta (`gen_app`), etaPair covers BOTH projections (`gen_fst`,
`gen_snd`), etaPathLam covers pathBeta (`gen_pathApp`); mod/glue are
typed-tier.  Re-decides when either table grows. -/
theorem etaRuleTable_observationsComplete :
    allRawObservationsCoverIotaDestructors etaRuleTable iotaRuleTable
      = true := rfl

/-! ## Extraction -/

/-- A positive containment check yields the observing spec. -/
theorem observationsContainObserverHead_extract :
    (observations : List EtaObservationSpec) →
    (destructorHead : Generator) →
    observationsContainObserverHead observations destructorHead = true →
    ∃ spec, spec ∈ observations
      ∧ spec.observerHead = destructorHead
  | [], _, contains => nomatch contains
  | spec :: restSpecs, destructorHead, contains => by
      dsimp only [observationsContainObserverHead] at contains
      by_cases headMatches : spec.observerHead = destructorHead
      · exact ⟨spec, .head _, headMatches⟩
      · rw [if_neg headMatches] at contains
        obtain ⟨innerSpec, isMember, observes⟩ :=
          observationsContainObserverHead_extract restSpecs
            destructorHead contains
        exact ⟨innerSpec, .tail _ isMember, observes⟩

/-- A member scrutinee spec with the matching head makes the
scrutinizes check fire. -/
theorem scrutineeListScrutinizes_ofMember :
    (specs : List ScrutineeSpec) → {spec : ScrutineeSpec} →
    spec ∈ specs → (former : Generator) → spec.head = former →
    scrutineeListScrutinizes specs former = true
  | headSpec :: restSpecs, spec, isMember, former, headMatches => by
      dsimp only [scrutineeListScrutinizes]
      by_cases headFires : headSpec.head = former
      · rw [if_pos headFires]
      · rw [if_neg headFires]
        cases isMember with
        | head _ => exact absurd headMatches headFires
        | tail _ isInRest =>
            exact scrutineeListScrutinizes_ofMember restSpecs isInRest
              former headMatches

/-- ★ **The consumable form**: under the table certificate, every way
iota can destruct a raw eta row's former is observed — given any iota
row scrutinizing the intro head, the eta row has an observation
through that row's eliminator. -/
theorem allRawObservationsCoverIotaDestructors_extract
    {etaTable : List EtaRuleDesc} {iotaTable : List IotaRuleDesc}
    (tableCovers :
      allRawObservationsCoverIotaDestructors etaTable iotaTable = true)
    {etaRule : EtaRuleDesc} (isEtaRow : etaRule ∈ etaTable)
    (isRawTier : etaRule.requiresTypedFiring = false)
    {iotaRule : IotaRuleDesc} (isIotaRow : iotaRule ∈ iotaTable)
    {spec : ScrutineeSpec} (isScrutinee : spec ∈ iotaRule.scrutinees)
    (scrutinizesIntro : spec.head = etaRule.introGenerator) :
    ∃ observation, observation ∈ etaRule.observations
      ∧ observation.observerHead = iotaRule.elimGenerator := by
  have rowCheck := listForall_mem etaTable tableCovers isEtaRow
  rw [isRawTier] at rowCheck
  have rowCovers :
      rowObservationsCoverIotaDestructors etaRule iotaTable = true :=
    rowCheck
  have iotaCheck := listForall_mem iotaTable rowCovers isIotaRow
  rw [scrutineeListScrutinizes_ofMember iotaRule.scrutinees isScrutinee
    etaRule.introGenerator scrutinizesIntro] at iotaCheck
  exact observationsContainObserverHead_extract etaRule.observations
    iotaRule.elimGenerator iotaCheck

end FX1Poly.Core
