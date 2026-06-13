import FX1Poly.Core.TableFireRoot
import FX1Poly.Core.IotaTableHeadExpansion

/-! # TableReduceOnce — IOTA-T9: the table-driven one-step reducer

The first consumer-migration brick of the canonicality flip: the
leftmost-outermost one-step reducer re-based from the bespoke
`fireRootRedex` onto the TABLE root walk (`fireTableRedexOver`), generic
over the rule table.  Fire a root redex if some row matches; otherwise
descend the child spine to the first reducible child.  Mirrors
`RawTerm.reduceOnce` arm for arm — but where the bespoke reducer's root
case is a 194-way generator dispatch compiled from 17 hand-written
firings, the table reducer's root case is a LIST WALK over rows: adding
an iota rule to the kernel changes the reducer by adding a row, with the
soundness/completeness proofs below untouched.

* `reduceOnceOverTable` / `reduceOnceSpineOverTable` — the mutual
  reducer;
* soundness — every produced reduct is a `StepOverTable` step (the root
  case is the shipped generic `fireTableRedexOver_sound`);
* blocking completeness — a term the reducer cannot step admits NO
  table step at all (`invertOrCong` splits a hypothetical step into a
  root firing, refuted through the `firesOn?_toFireAtRootAtCell` seam
  and `fireTableRedexOver_complete` against the failed walk, or a child
  congruence, refuted by the spine companion);
* `IsNormalFormOverTable` + the `none`-iff and the descent guarantee —
  the reducer halts EXACTLY at table normal forms;
* the canonical 21-row instantiations (`StepTable.reduceOnce` & co.),
  under which the table-native endpoint-β `pathBeta` is operationally
  LIVE: the reducer contracts `pathApp(pathLam(body), arg)` with no
  bespoke `Step` constructor anywhere.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTableReduceOnce.lean`. -/

namespace FX1Poly.Core

/-! ## The reducer -/

mutual

/-- **One table reduction step, as a function.**  Fire a root redex via
the table walk if some row matches; otherwise descend the child spine to
the first reducible child (leftmost-outermost).  `none` means no row
fires at the root or in any child. -/
def reduceOnceOverTable (table : List IotaRuleDesc) {scope : Nat}
    (term : RawTerm scope) : Option (RawTerm scope) :=
  match term with
  | .mkGen generator payload children =>
      match fireTableRedexOver table generator payload children with
      | some reduct => some reduct
      | none =>
          (reduceOnceSpineOverTable table children).map
            (fun reducedChildren => .mkGen generator payload reducedChildren)

/-- **One table reduction step inside a child spine.**  Reduce the first
reducible child, leaving the rest fixed; `none` if no child reduces. -/
def reduceOnceSpineOverTable (table : List IotaRuleDesc)
    {binderShifts : List Nat} {scope : Nat}
    (children : RawTermChildren binderShifts scope) :
    Option (RawTermChildren binderShifts scope) :=
  match binderShifts, children with
  | [], .childNil => none
  | _headShift :: _restShifts, .childCons childHead childTail =>
      match reduceOnceOverTable table childHead with
      | some reducedHead => some (.childCons reducedHead childTail)
      | none =>
          (reduceOnceSpineOverTable table childTail).map
            (fun reducedTail => .childCons childHead reducedTail)

end

/-! ## Soundness -/

mutual

/-- **Soundness of `reduceOnceOverTable`.**  Every produced reduct is a
genuine table step — a root firing via the generic walk soundness, a
child reduction via `StepOverTable.cong` over the spine companion. -/
theorem reduceOnceOverTable_sound {table : List IotaRuleDesc} {scope : Nat}
    {term reduct : RawTerm scope}
    (reduced : reduceOnceOverTable table term = some reduct) :
    StepOverTable table term reduct := by
  match term with
  | .mkGen generator payload children =>
      dsimp only [reduceOnceOverTable] at reduced
      cases fireEq : fireTableRedexOver table generator payload children with
      | some rootReduct =>
          rw [fireEq] at reduced
          injection reduced with reductEq
          rw [← reductEq]
          exact fireTableRedexOver_sound table (fun _ isRow => isRow) fireEq
      | none =>
          rw [fireEq] at reduced
          cases spineEq : reduceOnceSpineOverTable table children with
          | some reducedChildren =>
              rw [spineEq] at reduced
              dsimp only [Option.map] at reduced
              injection reduced with reductEq
              rw [← reductEq]
              exact StepOverTable.cong generator payload
                (reduceOnceSpineOverTable_sound spineEq)
          | none =>
              rw [spineEq] at reduced
              nomatch reduced

/-- **Soundness of `reduceOnceSpineOverTable`.**  The reduced spine is a
genuine `StepOverTableChildren` — `here` for a head reduction, `there`
for a tail reduction. -/
theorem reduceOnceSpineOverTable_sound {table : List IotaRuleDesc}
    {binderShifts : List Nat} {scope : Nat}
    {children reducedChildren : RawTermChildren binderShifts scope}
    (reduced : reduceOnceSpineOverTable table children
      = some reducedChildren) :
    StepOverTableChildren table children reducedChildren := by
  match binderShifts, children with
  | [], .childNil =>
      nomatch reduced
  | _headShift :: _restShifts, .childCons childHead childTail =>
      have unfoldSpine :
          reduceOnceSpineOverTable table (.childCons childHead childTail) =
            (match reduceOnceOverTable table childHead with
              | some reducedHead => some (.childCons reducedHead childTail)
              | none =>
                  (reduceOnceSpineOverTable table childTail).map
                    (fun reducedTail =>
                      .childCons childHead reducedTail)) := rfl
      rw [unfoldSpine] at reduced
      cases headEq : reduceOnceOverTable table childHead with
      | some reducedHead =>
          rw [headEq] at reduced
          injection reduced with reductEq
          rw [← reductEq]
          exact StepOverTableChildren.here childTail
            (reduceOnceOverTable_sound headEq)
      | none =>
          rw [headEq] at reduced
          cases tailEq : reduceOnceSpineOverTable table childTail with
          | some reducedTail =>
              rw [tailEq] at reduced
              dsimp only [Option.map] at reduced
              injection reduced with reductEq
              rw [← reductEq]
              exact StepOverTableChildren.there childHead
                (reduceOnceSpineOverTable_sound tailEq)
          | none =>
              rw [tailEq] at reduced
              nomatch reduced

end

/-! ## Blocking completeness -/

mutual

/-- **Blocking completeness of `reduceOnceOverTable`.**  A term the
reducer cannot step admits NO table step: a hypothetical root firing is
refuted by the walk completeness against the failed walk; a hypothetical
child congruence is refuted by the spine companion. -/
theorem reduceOnceOverTable_eq_none_blocks_step {table : List IotaRuleDesc}
    {scope : Nat} {term : RawTerm scope}
    (irreducible : reduceOnceOverTable table term = none)
    {next : RawTerm scope} (tableStep : StepOverTable table term next) :
    False := by
  match term with
  | .mkGen generator payload children =>
      dsimp only [reduceOnceOverTable] at irreducible
      cases fireEq : fireTableRedexOver table generator payload children with
      | some rootReduct =>
          rw [fireEq] at irreducible
          nomatch irreducible
      | none =>
          rw [fireEq] at irreducible
          cases tableStep.invertOrCong rfl with
          | inl rootFiring =>
              obtain ⟨rule, isRow, elimPayload, spine, cellEq, fires⟩ :=
                rootFiring
              have atRoot : rule.fireAtRoot? generator payload children
                  = some next :=
                rule.firesOn?_toFireAtRootAtCell cellEq fires
              have walkFires :=
                fireTableRedexOver_complete atRoot table isRow
              rw [fireEq] at walkFires
              exact Bool.noConfusion walkFires
          | inr congShape =>
              obtain ⟨reducedChildren, _nextShape, childrenStep⟩ := congShape
              cases spineEq : reduceOnceSpineOverTable table children with
              | some reducedSpine =>
                  rw [spineEq] at irreducible
                  dsimp only [Option.map] at irreducible
                  nomatch irreducible
              | none =>
                  exact reduceOnceSpineOverTable_eq_none_blocks_step spineEq
                    childrenStep

/-- **Blocking completeness of `reduceOnceSpineOverTable`.**  A spine the
reducer cannot step admits no children step at any position. -/
theorem reduceOnceSpineOverTable_eq_none_blocks_step
    {table : List IotaRuleDesc} {binderShifts : List Nat} {scope : Nat}
    {children : RawTermChildren binderShifts scope}
    (irreducible : reduceOnceSpineOverTable table children = none)
    {reducedChildren : RawTermChildren binderShifts scope}
    (childrenStep : StepOverTableChildren table children reducedChildren) :
    False := by
  match binderShifts, children with
  | [], .childNil =>
      exact nomatch (childrenStep :
        StepOverTableChildren table RawTermChildren.childNil reducedChildren)
  | _headShift :: _restShifts, .childCons childHead childTail =>
      have unfoldSpine :
          reduceOnceSpineOverTable table (.childCons childHead childTail) =
            (match reduceOnceOverTable table childHead with
              | some reducedHead => some (.childCons reducedHead childTail)
              | none =>
                  (reduceOnceSpineOverTable table childTail).map
                    (fun reducedTail =>
                      .childCons childHead reducedTail)) := rfl
      rw [unfoldSpine] at irreducible
      cases headEq : reduceOnceOverTable table childHead with
      | some reducedHead =>
          rw [headEq] at irreducible
          nomatch irreducible
      | none =>
          rw [headEq] at irreducible
          cases tailEq : reduceOnceSpineOverTable table childTail with
          | some reducedTail =>
              rw [tailEq] at irreducible
              dsimp only [Option.map] at irreducible
              nomatch irreducible
          | none =>
              cases childrenStep with
              | here _rest headStep =>
                  exact reduceOnceOverTable_eq_none_blocks_step headEq
                    headStep
              | there _head restStep =>
                  exact reduceOnceSpineOverTable_eq_none_blocks_step tailEq
                    restStep

end

/-! ## The halting set is exactly the table normal forms -/

/-- A term is a normal form of the table relation: no row fires at any
position. -/
def IsNormalFormOverTable (table : List IotaRuleDesc) {scope : Nat}
    (term : RawTerm scope) : Prop :=
  ∀ next : RawTerm scope, StepOverTable table term next → False

/-- **The reducer halts exactly at table normal forms.**  Forward is
blocking completeness; backward refutes a produced reduct by soundness
against the normal form. -/
theorem reduceOnceOverTable_eq_none_iff_isNormalFormOverTable
    {table : List IotaRuleDesc} {scope : Nat} {term : RawTerm scope} :
    reduceOnceOverTable table term = none
      ↔ IsNormalFormOverTable table term := by
  constructor
  · intro irreducible _next tableStep
    exact reduceOnceOverTable_eq_none_blocks_step irreducible tableStep
  · intro isNormal
    cases reduceEq : reduceOnceOverTable table term with
    | none => rfl
    | some reduct =>
        exact absurd (reduceOnceOverTable_sound reduceEq) (isNormal reduct)

/-- **Descent guarantee.**  A non-normal term genuinely reduces — the
successor the accessibility-driven normalizer steps to. -/
theorem not_isNormalFormOverTable_imp_reduceOnceOverTable_isSome
    {table : List IotaRuleDesc} {scope : Nat} {term : RawTerm scope}
    (notNormal : ¬ IsNormalFormOverTable table term) :
    (reduceOnceOverTable table term).isSome = true := by
  cases reduceEq : reduceOnceOverTable table term with
  | some reduct => rfl
  | none =>
      exact absurd
        (reduceOnceOverTable_eq_none_iff_isNormalFormOverTable.mp reduceEq)
        notNormal

/-! ## The canonical 21-row instantiation -/

/-- One canonical-table reduction step — the kernel's table-driven
leftmost-outermost reducer.  The table-native endpoint-β `pathBeta` is
operationally LIVE here: `pathApp(pathLam(body), arg)` contracts with no
bespoke `Step` constructor anywhere. -/
def StepTable.reduceOnce {scope : Nat} (term : RawTerm scope) :
    Option (RawTerm scope) :=
  reduceOnceOverTable iotaRuleTable term

/-- Canonical soundness: every produced reduct is a `StepTable` step. -/
theorem StepTable.reduceOnce_sound {scope : Nat}
    {term reduct : RawTerm scope}
    (reduced : StepTable.reduceOnce term = some reduct) :
    StepTable term reduct :=
  reduceOnceOverTable_sound reduced

/-- Canonical halting characterization: the reducer halts exactly at
`StepTable` normal forms. -/
theorem StepTable.reduceOnce_eq_none_iff {scope : Nat}
    {term : RawTerm scope} :
    StepTable.reduceOnce term = none
      ↔ IsNormalFormOverTable iotaRuleTable term :=
  reduceOnceOverTable_eq_none_iff_isNormalFormOverTable

/-- **Endpoint-β fires through the canonical reducer** — the
operational-liveness smoke for the table-native `pathBeta` row:
`pathApp(pathLam(var 0), refl(unit))` contracts to `refl(unit)` by
`rfl`, with no bespoke constructor involved. -/
theorem StepTable.reduceOnce_firesPathBeta :
    StepTable.reduceOnce (scope := 0)
      (.mkGen .gen_pathApp ()
        (.childCons
          (.mkGen .gen_pathLam ()
            (.childCons
              (.mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil)
              .childNil))
          (.childCons
            (.mkGen .gen_refl ()
              (.childCons (.mkGen .gen_unit () .childNil) .childNil))
            .childNil)))
    = some (.mkGen .gen_refl ()
        (.childCons (.mkGen .gen_unit () .childNil) .childNil)) := rfl

end FX1Poly.Core
