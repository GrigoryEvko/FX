import FX1Poly.Core.TableReduceOnce
import FX1Poly.Core.TableTakahashiTriangle

/-! # TableNormalize — IOTA-T9: the table normalizer and decidable
table conversion

The second consumer-migration brick of the canonicality flip: the
normalizer FUNCTION and the conversion relation re-based onto the rule
table.

* `normalizeOverTable` — iterate `reduceOnceOverTable` along an
  accessibility witness (`Acc.rec`, because β/ι grow terms so the
  recursion is on the proof, not a measure); correctness =
  `normalizeOverTable_reducesTo` (the output is reached by a step
  chain) + `normalizeOverTable_isNormalForm` (the output admits no
  table step).
* `ConvOverTable` — table conversion in join form (a shared common
  reduct), mirroring the bespoke `Conv = StepStar.Join`; reflexive and
  symmetric unconditionally, TRANSITIVE under confluence.
* `ConvOverTable.iff_normalize_eq` — on the strongly-normalizing
  fragment of a CONFLUENT table, conversion is normalize-equality.
  Where the bespoke decider had to manufacture confluence per term from
  the two SN witnesses, the table world holds GLOBAL confluence
  (IOTA-T6), so the characterization is three confluence applications
  and the chain-from-normal-form collapse.
* `ConvOverTable.decidableOfStronglyNormalizing` — normalize both sides
  and compare, a literal `RawTerm` equality decided by
  `instDecidableEqRawTerm`.
* the canonical 18-row instantiations: `StepTable.normalize`,
  `ConvTable` (+ refl/sym/trans with confluence discharged by
  `StepTable.confluent`), and `ConvTable.decidableOfStronglyNormalizing`
  — the relations the canonicality flip declares official, with the
  table-native endpoint-β live inside them.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTableNormalize.lean`. -/

namespace FX1Poly.Core

/-! ## The normalizer -/

/-- **The table normalizer.**  Iterate `reduceOnceOverTable` along the
accessibility witness until the reducer halts; the result is a table
normal form reached by a genuine step chain.  Written with `Acc.rec`
because the descent shrinks the accessibility proof, not the term. -/
def normalizeOverTable (table : List IotaRuleDesc) {scope : Nat}
    (term : RawTerm scope)
    (accessible : Acc (StepOverTable.successorOver table) term) :
    RawTerm scope :=
  Acc.rec
    (motive := fun _currentTerm _acc => RawTerm scope)
    (fun currentTerm _accStep normalizeRec =>
      match reduceEq : reduceOnceOverTable table currentTerm with
      | none => currentTerm
      | some reduct =>
          normalizeRec reduct (reduceOnceOverTable_sound reduceEq))
    accessible

/-- One-step unfolding of `normalizeOverTable` at an `Acc.intro` witness
(holds by `rfl`; the proof handle for the correctness theorems). -/
theorem normalizeOverTable_unfold (table : List IotaRuleDesc) {scope : Nat}
    (term : RawTerm scope)
    (accStep : ∀ later, StepOverTable.successorOver table later term →
      Acc (StepOverTable.successorOver table) later) :
    normalizeOverTable table term (.intro term accStep) =
      (match reduceEq : reduceOnceOverTable table term with
        | none => term
        | some reduct =>
            normalizeOverTable table reduct
              (accStep reduct (reduceOnceOverTable_sound reduceEq))) := rfl

/-- **The normalizer reaches its output by a step chain.** -/
theorem normalizeOverTable_reducesTo (table : List IotaRuleDesc)
    {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (StepOverTable.successorOver table) term) :
    ReflTransClosure (StepOverTable table) term
      (normalizeOverTable table term accessible) := by
  induction accessible with
  | intro currentTerm accStep ih =>
      rw [normalizeOverTable_unfold table currentTerm accStep]
      split
      · exact ReflTransClosure.refl _
      · next reduct reduceEq =>
          exact ReflTransClosure.head (reduceOnceOverTable_sound reduceEq)
            (ih reduct (reduceOnceOverTable_sound reduceEq))

/-- **The normalizer's output is a table normal form.** -/
theorem normalizeOverTable_isNormalForm (table : List IotaRuleDesc)
    {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (StepOverTable.successorOver table) term) :
    IsNormalFormOverTable table (normalizeOverTable table term accessible) := by
  induction accessible with
  | intro currentTerm accStep ih =>
      rw [normalizeOverTable_unfold table currentTerm accStep]
      split
      · next reduceEq =>
          exact reduceOnceOverTable_eq_none_iff_isNormalFormOverTable.mp
            reduceEq
      · next reduct reduceEq =>
          exact ih reduct (reduceOnceOverTable_sound reduceEq)

/-! ## Chains out of normal forms collapse -/

/-- A step chain out of a table normal form is the identity chain. -/
theorem ReflTransClosure.eq_of_isNormalFormOverTable
    {table : List IotaRuleDesc} {scope : Nat}
    {source target : RawTerm scope}
    (chain : ReflTransClosure (StepOverTable table) source target)
    (sourceIsNormal : IsNormalFormOverTable table source) :
    source = target := by
  cases chain with
  | refl _ => rfl
  | head first _rest => exact (sourceIsNormal _ first).elim

/-! ## Table conversion -/

/-- **Table conversion** (join form): the two sides reach a shared
common reduct — the table twin of the bespoke `Conv = StepStar.Join`. -/
def ConvOverTable (table : List IotaRuleDesc) {scope : Nat}
    (sourceTerm targetTerm : RawTerm scope) : Prop :=
  Joinable (StepOverTable table) sourceTerm targetTerm

/-- Reflexivity of table conversion. -/
theorem ConvOverTable.refl {table : List IotaRuleDesc} {scope : Nat}
    (sourceTerm : RawTerm scope) :
    ConvOverTable table sourceTerm sourceTerm :=
  ⟨sourceTerm, ReflTransClosure.refl _, ReflTransClosure.refl _⟩

/-- Symmetry of table conversion. -/
theorem ConvOverTable.sym {table : List IotaRuleDesc} {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (convertible : ConvOverTable table sourceTerm targetTerm) :
    ConvOverTable table targetTerm sourceTerm :=
  Exists.elim convertible
    (fun commonTerm chains => ⟨commonTerm, chains.2, chains.1⟩)

/-- A step chain induces table conversion (its target as the common
reduct). -/
theorem ConvOverTable.fromClosure {table : List IotaRuleDesc} {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (chain : ReflTransClosure (StepOverTable table) sourceTerm targetTerm) :
    ConvOverTable table sourceTerm targetTerm :=
  ⟨targetTerm, chain, ReflTransClosure.refl _⟩

/-- **Transitivity of table conversion under confluence**: the two
middle chains diverge from the shared middle term, so confluence joins
the two common reducts, and the outer chains extend to the join. -/
theorem ConvOverTable.trans {table : List IotaRuleDesc} {scope : Nat}
    (confluent : Confluent (fun source target : RawTerm scope =>
      StepOverTable table source target))
    {firstTerm middleTerm lastTerm : RawTerm scope}
    (firstConv : ConvOverTable table firstTerm middleTerm)
    (secondConv : ConvOverTable table middleTerm lastTerm) :
    ConvOverTable table firstTerm lastTerm := by
  obtain ⟨firstCommon, firstChain, middleToFirstCommon⟩ := firstConv
  obtain ⟨secondCommon, middleToSecondCommon, lastChain⟩ := secondConv
  obtain ⟨joined, firstCommonToJoined, secondCommonToJoined⟩ :=
    confluent middleToFirstCommon middleToSecondCommon
  exact ⟨joined,
    ReflTransClosure.trans firstChain firstCommonToJoined,
    ReflTransClosure.trans lastChain secondCommonToJoined⟩

/-! ## Conversion is normalize-equality on the SN fragment -/

/-- **Table conversion = normalize-equality** on the
strongly-normalizing fragment of a confluent table — the NbE
soundness+completeness characterization, with confluence GLOBAL
(IOTA-T6) rather than manufactured per term. -/
theorem ConvOverTable.iff_normalize_eq {table : List IotaRuleDesc}
    {scope : Nat}
    (confluent : Confluent (fun source target : RawTerm scope =>
      StepOverTable table source target))
    {leftTerm rightTerm : RawTerm scope}
    (leftTerminates : Acc (StepOverTable.successorOver table) leftTerm)
    (rightTerminates : Acc (StepOverTable.successorOver table) rightTerm) :
    ConvOverTable table leftTerm rightTerm ↔
      normalizeOverTable table leftTerm leftTerminates
        = normalizeOverTable table rightTerm rightTerminates := by
  have leftToNormal := normalizeOverTable_reducesTo table leftTerm
    leftTerminates
  have rightToNormal := normalizeOverTable_reducesTo table rightTerm
    rightTerminates
  have leftNormal := normalizeOverTable_isNormalForm table leftTerm
    leftTerminates
  have rightNormal := normalizeOverTable_isNormalForm table rightTerm
    rightTerminates
  constructor
  · intro convertible
    obtain ⟨common, leftChain, rightChain⟩ := convertible
    obtain ⟨joinedLeft, commonToJoinedLeft, normalLeftChain⟩ :=
      confluent leftChain leftToNormal
    obtain rfl := ReflTransClosure.eq_of_isNormalFormOverTable
      normalLeftChain leftNormal
    obtain ⟨joinedRight, commonToJoinedRight, normalRightChain⟩ :=
      confluent rightChain rightToNormal
    obtain rfl := ReflTransClosure.eq_of_isNormalFormOverTable
      normalRightChain rightNormal
    obtain ⟨finalJoin, normalLeftToFinal, normalRightToFinal⟩ :=
      confluent commonToJoinedLeft commonToJoinedRight
    exact (ReflTransClosure.eq_of_isNormalFormOverTable normalLeftToFinal
        leftNormal).trans
      (ReflTransClosure.eq_of_isNormalFormOverTable normalRightToFinal
        rightNormal).symm
  · intro normalsEq
    exact ⟨normalizeOverTable table leftTerm leftTerminates,
      leftToNormal, normalsEq ▸ rightToNormal⟩

/-- **Decidable table conversion on the strongly-normalizing fragment of
a confluent table**: normalize both sides, compare — a literal `RawTerm`
equality decided by `instDecidableEqRawTerm`. -/
def ConvOverTable.decidableOfStronglyNormalizing {table : List IotaRuleDesc}
    {scope : Nat}
    (confluent : Confluent (fun source target : RawTerm scope =>
      StepOverTable table source target))
    {leftTerm rightTerm : RawTerm scope}
    (leftTerminates : Acc (StepOverTable.successorOver table) leftTerm)
    (rightTerminates : Acc (StepOverTable.successorOver table) rightTerm) :
    Decidable (ConvOverTable table leftTerm rightTerm) :=
  decidable_of_iff _
    (ConvOverTable.iff_normalize_eq confluent leftTerminates
      rightTerminates).symm

/-! ## The canonical 18-row instantiation -/

/-- The canonical table normalizer. -/
def StepTable.normalize {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (StepOverTable.successorOver iotaRuleTable) term) :
    RawTerm scope :=
  normalizeOverTable iotaRuleTable term accessible

/-- **THE canonical conversion relation**: `ConvOverTable` at the full
18-row `iotaRuleTable` — the IOTA-T9 canonicality-flip target alongside
`StepTable`. -/
def ConvTable {scope : Nat} (sourceTerm targetTerm : RawTerm scope) : Prop :=
  ConvOverTable iotaRuleTable sourceTerm targetTerm

/-- Reflexivity of the canonical conversion. -/
theorem ConvTable.refl {scope : Nat} (sourceTerm : RawTerm scope) :
    ConvTable sourceTerm sourceTerm :=
  ConvOverTable.refl sourceTerm

/-- Symmetry of the canonical conversion. -/
theorem ConvTable.sym {scope : Nat} {sourceTerm targetTerm : RawTerm scope}
    (convertible : ConvTable sourceTerm targetTerm) :
    ConvTable targetTerm sourceTerm :=
  ConvOverTable.sym convertible

/-- **Transitivity of the canonical conversion** — confluence discharged
by the shipped `StepTable.confluent`, NO per-term hypotheses (the
bespoke `Conv.trans` needed a typed middle-SN witness; the table
relation's global confluence removes that seam entirely). -/
theorem ConvTable.trans {scope : Nat}
    {firstTerm middleTerm lastTerm : RawTerm scope}
    (firstConv : ConvTable firstTerm middleTerm)
    (secondConv : ConvTable middleTerm lastTerm) :
    ConvTable firstTerm lastTerm :=
  ConvOverTable.trans StepTable.confluent firstConv secondConv

/-- **Decidable canonical conversion on the strongly-normalizing
fragment** — both certificates discharged by the shipped table pins. -/
def ConvTable.decidableOfStronglyNormalizing {scope : Nat}
    {leftTerm rightTerm : RawTerm scope}
    (leftTerminates : Acc (StepOverTable.successorOver iotaRuleTable)
      leftTerm)
    (rightTerminates : Acc (StepOverTable.successorOver iotaRuleTable)
      rightTerm) :
    Decidable (ConvTable leftTerm rightTerm) :=
  ConvOverTable.decidableOfStronglyNormalizing StepTable.confluent
    leftTerminates rightTerminates

end FX1Poly.Core
