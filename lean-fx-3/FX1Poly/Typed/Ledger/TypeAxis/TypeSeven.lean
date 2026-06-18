import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaRuleTable
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableHonesty
import FX1Poly.Core.Rewriting.Confluence.DefUnivConfluence
import FX1Poly.Core.Substrate.Univalence.DefUnivSnResolution
import FX1Poly.Core.Metatheory.Canonicity.ReflCanonicalFormsCandidate
import FX1Poly.Core.Metatheory.Canonicity.IdentityEliminatorCanonicalComputation
import FX1Poly.Core.Substrate.Semantics.EitherEquivCodeUniverseMembership
import FX1Poly.Typed.Engine.RuleTables.UnionRuleTables

/-! # type-7 ★ — definitional univalence: Id at the universe computes to Equiv + its canonicity

THE flagship rung of the type axis: definitional univalence — `Id (Type@l) A B ↝ Equiv A B` as a computation
rule, plus the canonicity of the identity type it builds on.  FX ships this to a genuinely-certified
DEMONSTRATOR grade: the identity type has a computing eliminator (J on refl) with full canonicity, the Equiv
type former is real (typed + strongly normalizing + a reducible universe member), and the definitional-
univalence rule FIRES (`Id_U ↝ Equiv`) and is metatheoretically sound (well-formed-orthogonal + RPO-SN +
confluent on the candidate table).  What is NOT yet shipped — honestly — is the rule's residency in the LIVE
operational table (it lives only in `candidateUnivalenceTable`), the `Conv`/`Step.eqType` bridge, the
equivalence eliminators, and a univalent universe in any model.  Like `type-1`..`type-6`, a NON-DUPLICATIVE
ledger ABOVE Typed: markers + `_isBacked` referencing named shipped theorems.

## What this rung backs (each `= true`, conjoined with named shipped theorems)

  * **`fxType_hasIdentityComputation`** — the identity type COMPUTES: path-induction on `refl` reduces to the
    base case, `J(motive, base, refl(w)) ↝ base` (`idJReflIotaRow_interpretsTarget`, `rfl`, a LIVE table
    row), and `gen_idJ` carries a reduction rule (`hasReductionRule_idJ`).
  * **`fxType_hasIdentityCanonicity`** — the identity type's CANONICITY: a closed candidate member of the
    identity type reduces to a `refl` value (`reflClosedReducesToValue`), and a closed `J` on a canonical
    `refl` witness reduces to its base case (`idJCanonicalWitnessReducesToBase`) — the "its canonicity" half
    of the headline, for the identity type, fundamental-theorem-free.
  * **`fxType_hasEquivalenceTypeFormer`** — the TARGET of univalence is a genuine type: `Equiv A B` is a flat-
    typed former (`flatTypingRuleDescOf_equivCode`, output a universe code at `lmax`) and a REDUCIBLE MEMBER
    of its universe when both endpoints are strongly normalizing (`equivCode_isReducibleMemberOfUniverse`).
  * **`fxType_hasDefinitionalUnivalenceShape`** ★ — the keystone: `Id (Type@l) A B ↝ Equiv A B` FIRES
    (`univalenceShapedDemoRule_firesOnUniverse`, `rfl`) and is metatheoretically sound on the candidate table
    — well-formed-orthogonal (`candidateUnivalenceTable_isWf`), RPO-orientable / strongly normalizing with no
    new measure (`univalenceShapedDemoRule_isRpoOrientable`), and CONFLUENT
    (`candidateUnivalenceTable_isConfluent`).  Definitional univalence as a certified reduction.

## What is deferred (the genuine definitional-univalence frontier)

  * `fxType_hasLiveDefinitionalUnivalence` — the univalence reduction is a DEMONSTRATOR: it lives in
    `candidateUnivalenceTable = iotaRuleTable ++ [univalenceShapedDemoRule]`, NOT in the LIVE operational
    `iotaRuleTable`; there is no `Step.eqType` constructor and no `Conv`/definitional-equality object bridging
    `Id` and `Equiv` (`Univalence := Conv.fromStep Step.eqType` is the absent TARGET).  Promoting the row to
    the live table + the `Conv` bridge is DEFUNIV-HEADLINE / EXT-4.  `= false`.
  * `fxType_hasEquivalenceEliminators` — the equivalence eliminators / coercions `gen_equivIntro` /
    `gen_equivApp` / `gen_equivApply` / `gen_equivCompose` / `gen_idToEquiv` / `gen_uaToEquiv` /
    `gen_pathCompose` / `gen_pathInverse` are all reserved tags (no iota / redex head / typing); only the
    `gen_equivCode` type-former head is operational.  `= false`.
  * `fxType_hasUnivalentUniverse` — the model-level univalent universe: every shipped context model self-marks
    `hasUnivalentUniverse = false` (`fxCubicalModel_hasUnivalentUniverse`, plus the simplicial and
    `(∞,1)`-CwF twins).  The universe is not yet univalent in any model.  `= false`.

## Zero-axiom verification

Four `Bool` markers `:= true` (each `_isBacked` conjunction closed by `rfl` + named shipped theorems:
`hasReductionRule_idJ` / `idJReflIotaRow_interpretsTarget`; `reflClosedReducesToValue` /
`idJCanonicalWitnessReducesToBase`; `flatTypingRuleDescOf_equivCode` /
`equivCode_isReducibleMemberOfUniverse`; `univalenceShapedDemoRule_firesOnUniverse` /
`candidateUnivalenceTable_isWf` / `univalenceShapedDemoRule_isRpoOrientable` /
`candidateUnivalenceTable_isConfluent`) and three `:= false` deferral markers.  All cited substrate is
`FX1Poly.Core` / `FX1Poly.Typed`, funext-free, `Quot.sound`-free.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTier0TypeSeven.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core
open FX1Poly.Core.StepStar
open FX1Poly.Typed
open FX1Poly.Universe

/-! ## Identity computation (J on refl) -/

/-- **Honesty marker** — `type-7` (identity computation).  Path-induction on `refl` reduces to the base case;
`gen_idJ` carries a reduction rule.  Backed in `fxType_identityComputation_isBacked`.  `= true`. -/
def fxType_hasIdentityComputation : Bool := true

/-- ★ **Backed flip (identity computation).**  The marker is `true` AND (i) `gen_idJ` carries a reduction
rule (`hasReductionRule_idJ`); (ii) `J(motive, base, refl(w)) ↝ base` (`idJReflIotaRow_interpretsTarget`). -/
theorem fxType_identityComputation_isBacked :
    fxType_hasIdentityComputation = true
      ∧ Generator.hasReductionRule .gen_idJ = true
      ∧ (∀ {scope : Nat} (motive : RawTerm (scope + 2)) (baseCase rawWitness : RawTerm scope),
          idJReflIotaRow.interpretTarget? ()
            (.childCons motive
              (.childCons baseCase
                (.childCons (.mkGen .gen_refl () (.childCons rawWitness .childNil)) .childNil)))
            = some baseCase) := by
  refine ⟨rfl, hasReductionRule_idJ, ?_⟩
  intro scope motive baseCase rawWitness
  exact idJReflIotaRow_interpretsTarget motive baseCase rawWitness

/-! ## Identity canonicity -/

/-- **Honesty marker** — `type-7` (identity canonicity).  Closed identity members reduce to `refl`, and `J`
on a canonical `refl` witness reduces to the base case.  Backed in `fxType_identityCanonicity_isBacked`.
`= true`. -/
def fxType_hasIdentityCanonicity : Bool := true

/-- ★ **Backed flip (identity canonicity).**  The marker is `true` AND (i) a closed candidate member of the
identity type reduces to a `refl` value (`reflClosedReducesToValue`); (ii) a closed `J` on a canonical `refl`
witness reduces to its base case (`idJCanonicalWitnessReducesToBase`). -/
theorem fxType_identityCanonicity_isBacked :
    fxType_hasIdentityCanonicity = true
      ∧ (∀ {term : RawTerm 0}, CanonicalFormsPredicate isReflValue term →
          ∃ value : RawTerm 0, StepStar term value ∧ isReflValue value)
      ∧ (∀ {motive : RawTerm 2} {baseCase witness : RawTerm 0},
          CanonicalFormsPredicate isReflValue witness →
          StepStar
            (.mkGen .gen_idJ ()
              (.childCons motive (.childCons baseCase (.childCons witness .childNil))))
            baseCase) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro term member
    exact reflClosedReducesToValue member
  · intro motive baseCase witness witnessMember
    exact idJCanonicalWitnessReducesToBase witnessMember

/-! ## The equivalence type former (the univalence target) -/

/-- **Honesty marker** — `type-7` (equivalence type former).  `Equiv A B` is a genuine flat-typed former and
a reducible member of its universe — the target of the univalence reduction is a real type.  Backed in
`fxType_equivalenceTypeFormer_isBacked`.  `= true`. -/
def fxType_hasEquivalenceTypeFormer : Bool := true

/-- ★ **Backed flip (equivalence type former).**  The marker is `true` AND (i) `gen_equivCode` is flat-typed
to a universe code at the children's `lmax` (`flatTypingRuleDescOf_equivCode`); (ii) `Equiv A B` is a
reducible member of its universe when both endpoints are strongly normalizing
(`equivCode_isReducibleMemberOfUniverse`). -/
theorem fxType_equivalenceTypeFormer_isBacked :
    fxType_hasEquivalenceTypeFormer = true
      ∧ flatTypingRuleDescOf .gen_equivCode = some { outputType := universeFormerOutput }
      ∧ (∀ {scope predLevel : Nat} (levelExpr : LevelExpr) (flag : UniverseFlag)
          {sourceType targetType : RawTerm scope},
          IsStronglyNormalizing sourceType → IsStronglyNormalizing targetType →
          IsReducibleMemberAt (predLevel + 1)
            (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
            (.mkGen .gen_equivCode () (.childCons sourceType (.childCons targetType .childNil)))) := by
  refine ⟨rfl, flatTypingRuleDescOf_equivCode, ?_⟩
  intro scope predLevel levelExpr flag sourceType targetType sourceNormalizing targetNormalizing
  exact equivCode_isReducibleMemberOfUniverse levelExpr flag sourceNormalizing targetNormalizing

/-! ## Definitional univalence (the keystone) -/

/-- **Honesty marker** — `type-7` ★ (definitional univalence shape).  `Id (Type@l) A B ↝ Equiv A B` fires and
is metatheoretically sound (well-formed-orthogonal + RPO-SN + confluent) on the candidate table.  Backed in
`fxType_definitionalUnivalenceShape_isBacked`.  `= true`. -/
def fxType_hasDefinitionalUnivalenceShape : Bool := true

/-- ★ **Backed flip (definitional univalence shape).**  The marker is `true` AND (i) the candidate table is
well-formed-orthogonal (`candidateUnivalenceTable_isWf`); (ii) the univalence row is RPO-orientable / SN with
no new measure (`univalenceShapedDemoRule_isRpoOrientable`); (iii) the candidate table is CONFLUENT
(`candidateUnivalenceTable_isConfluent`); (iv) the rule FIRES: `Id (Type@l) lhs rhs ↝ Equiv lhs rhs`
(`univalenceShapedDemoRule_firesOnUniverse`). -/
theorem fxType_definitionalUnivalenceShape_isBacked :
    fxType_hasDefinitionalUnivalenceShape = true
      ∧ WfIotaTable candidateUnivalenceTable
      ∧ univalenceShapedDemoRule.isRpoOrientable = true
      ∧ (∀ {scope : Nat}, Confluent (fun source target : RawTerm scope =>
          StepOverTable candidateUnivalenceTable source target))
      ∧ (∀ {scope : Nat} (levelExpr : LevelExpr) (flag : UniverseFlag)
          (lhsCode rhsCode : RawTerm scope),
          univalenceShapedDemoRule.firesOn? ()
            (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
              (.childCons lhsCode (.childCons rhsCode .childNil)))
            = some (.mkGen .gen_equivCode ()
                (.childCons lhsCode (.childCons rhsCode .childNil)))) := by
  refine ⟨rfl, candidateUnivalenceTable_isWf, univalenceShapedDemoRule_isRpoOrientable, ?_, ?_⟩
  · intro scope
    exact candidateUnivalenceTable_isConfluent
  · intro scope levelExpr flag lhsCode rhsCode
    exact univalenceShapedDemoRule_firesOnUniverse levelExpr flag lhsCode rhsCode

/-! ## Honesty markers (the deferred definitional-univalence frontier) -/

/-- **Honesty marker.**  The univalence reduction is a DEMONSTRATOR — it lives in `candidateUnivalenceTable`,
NOT the live operational `iotaRuleTable`; there is no `Step.eqType` constructor and no `Conv` / definitional-
equality object bridging `Id` and `Equiv` (`Univalence := Conv.fromStep Step.eqType` is the absent TARGET).
Route: DEFUNIV-HEADLINE / EXT-4 (promote the row to the live table + the `Conv` bridge).  Deferred.
`= false`. -/
def fxType_hasLiveDefinitionalUnivalence : Bool := false

/-- **Honesty marker.**  The equivalence eliminators / coercions `gen_equivIntro` / `gen_equivApp` /
`gen_equivApply` / `gen_equivCompose` / `gen_idToEquiv` / `gen_uaToEquiv` / `gen_pathCompose` /
`gen_pathInverse` are all reserved tags (no iota / redex head / typing); only the `gen_equivCode`
type-former head is operational.  Deferred.  `= false`. -/
def fxType_hasEquivalenceEliminators : Bool := false

/-- **Honesty marker.**  The model-level univalent universe — every shipped context model self-marks
`hasUnivalentUniverse = false` (`fxCubicalModel_hasUnivalentUniverse`, plus the simplicial and `(∞,1)`-CwF
twins).  The universe is not yet univalent in any model.  Deferred.  `= false`. -/
def fxType_hasUnivalentUniverse : Bool := false

end FX1Poly.Tier0
