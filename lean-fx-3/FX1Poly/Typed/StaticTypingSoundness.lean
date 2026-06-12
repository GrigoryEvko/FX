import FX1Poly.Typed.TypedBySomeEngine
import FX1Poly.Typed.UntypableHeadDecision
import FX1Poly.Typed.RawTermHeadGenerator
import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.HasTypeDescBridge

/-! # FX1Poly/Typed/StaticTypingSoundness — the honest classifier's NEGATIVE soundness (reserved ⟹ untyped by the surviving engines)

`TypedBySomeEngine.hasSomeTypingRule` is the total static-typing classifier: it returns `true` iff SOME union arm
types a cell headed by the given generator.  That file ships the POSITIVE witnesses — one `rfl` per rule family
showing a representative live head computes `true`.  This file ships the missing soundness half, turning
`hasSomeTypingRule` from "computes a `Bool`" into "the `Bool` is TRUTHFUL": **a head the classifier reports as
RESERVED (`= false`) is typed by no SURVIVING standalone engine.**  Without this, the classifier could lie —
branding a genuinely-typed head reserved — and the honesty arc's whole premise (that the 205-generator table
truthfully records which names carry static meaning) would be unverified.

The statement is one negative-soundness theorem per surviving standalone engine, each of the form
`hasSomeTypingRule (headGenerator subject) = false → Engine context subject classifier → False`, plus the
bundle `reservedHeadUntypedBySurvivingEngines` conjoining them.

  * **Grown engine** (`HasTypeDescPi`, the formation/intro/elim trio behind `typingRuleDescOf` /
    `introRuleDescOf` / `elimRuleDescOf` + the bespoke `var` / `universeCode` heads).  Routed through the shipped
    `UntypableHeadDecision.isUntypableHead_sound` (which already encapsulates the grown induction) via the bridge
    `hasSomeTypingRule_false_imp_isUntypableHead`: a head reserved by the union classifier is roleless and
    non-bespoke, exactly `isUntypableHead`'s precondition.
  * **Bridge engine** (`HasTypeDescBridge`, interval/bridge formation, endpoints, path intro/elim).  The leg
    cases the derivation directly — every arm's subject is a concrete cell whose head the classifier reports
    `true`, so a `false` report is `Bool.noConfusion`.

The single-judgment successor covering ALL native typing — including the retired base-type / data-intro / flat
FORMATION arms, now `baseTypeFormation` / `dataIntroNullary` / `flatFormation` arms of `HasTypeNativeUnion` — is
`HasTypeNativeUnion.reservedHeadUntyped` (`UnionStaticTypingSoundness`), stated over the full-union classifier
`hasUnionEliminatorTypingRule`.  That is the canonical place a reserved head is shown untyped by EVERY native
rule; this file keeps only the two surviving standalone-engine legs (grown + bridge) that the tier ledger's
representative head still consults directly.

This is the exact honest claim — "untyped by the surviving engines `hasSomeTypingRule` consults".  The
formation-only engine `HasTypeDesc` is the formation fragment of `HasTypeDescPi` (its subjects are
`typingRuleDescOf` heads, so a reserved head is untyped there too, by the same grown leg); the
canonicity-restricted `HasTypeDescBoolElimValue` is not a member of the classifier union and is out of scope.

## Zero-axiom

The grown bridge peels the left-associated 27-disjunct `||` chain with the propext-free `orEqFalse_leftFalse` /
`orEqFalse_rightFalse` projections (`cases` + `Bool.noConfusion`, never `Bool.or_eq_false_iff` which would leak
`propext`), reduces `typingRoleOf` via `if_neg` on the three failed guards, and discharges `isUntypableHead` with
`decide_eq_true` (the propext-free `decide`-introduction).  The bridge leg is `cases` on the derivation +
`Bool.noConfusion`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## propext-free Bool projections -/

/-- `(left || right) = false → left = false`, propext-free (`cases` + `Bool.noConfusion`). -/
theorem orEqFalse_leftFalse {left right : Bool} (orFalse : (left || right) = false) : left = false := by
  cases left with
  | false => rfl
  | true => exact Bool.noConfusion orFalse

/-- `(left || right) = false → right = false`, propext-free. -/
theorem orEqFalse_rightFalse {left right : Bool} (orFalse : (left || right) = false) : right = false := by
  cases left with
  | false => exact orFalse
  | true => exact Bool.noConfusion orFalse

/-- A `false` Bool is not `true` — the `if`-guard refutation, propext-free. -/
theorem notEqTrue_ofEqFalse {value : Bool} (isFalse : value = false) : ¬ (value = true) :=
  fun isTrue => Bool.noConfusion (isFalse ▸ isTrue)

/-! ## The grown bridge: reserved ⟹ untypable-head -/

/-- **A head the union classifier reports RESERVED is `isUntypableHead`.**  `hasSomeTypingRule generator = false`
forces every disjunct false, in particular the three grown-table membership tests and the two bespoke-head
equalities — exactly `typingRoleOf generator = none ∧ generator ≠ gen_var ∧ generator ≠ gen_universeCode`, the
precondition of the shipped grown-untyping decision procedure.  This is the propext-free bridge that lets the
grown leg reuse `UntypableHeadDecision.isUntypableHead_sound` rather than re-inverting the grown inductive. -/
theorem hasSomeTypingRule_false_imp_isUntypableHead (generator : Generator)
    (reserved : hasSomeTypingRule generator = false) : isUntypableHead generator = true := by
  dsimp only [hasSomeTypingRule] at reserved
  -- Peel the left-associated 27-disjunct chain to the five grown-relevant atoms.
  -- NATIVE-11 dropped the three interval decides (intervalCode / interval0 / interval1) once they
  -- became table-resident, shrinking the tail from 30 to 27 — so the peel now starts at `rest26`
  -- (the four tail disjuncts above `var` are pathApp / pathLam / bridgeCode / universeCode).
  have rest26 := orEqFalse_leftFalse reserved
  have rest25 := orEqFalse_leftFalse rest26
  have rest24 := orEqFalse_leftFalse rest25
  have rest23 := orEqFalse_leftFalse rest24
  have universeCodeFalse := orEqFalse_rightFalse rest24
  have varFalse := orEqFalse_rightFalse rest23
  have rest22 := orEqFalse_leftFalse rest23
  have rest21 := orEqFalse_leftFalse rest22
  have rest20 := orEqFalse_leftFalse rest21
  have rest19 := orEqFalse_leftFalse rest20
  have rest18 := orEqFalse_leftFalse rest19
  have rest17 := orEqFalse_leftFalse rest18
  have rest16 := orEqFalse_leftFalse rest17
  have rest15 := orEqFalse_leftFalse rest16
  have rest14 := orEqFalse_leftFalse rest15
  have rest13 := orEqFalse_leftFalse rest14
  have rest12 := orEqFalse_leftFalse rest13
  have rest11 := orEqFalse_leftFalse rest12
  have rest10 := orEqFalse_leftFalse rest11
  have rest9 := orEqFalse_leftFalse rest10
  have rest8 := orEqFalse_leftFalse rest9
  have rest7 := orEqFalse_leftFalse rest8
  have rest6 := orEqFalse_leftFalse rest7
  have rest5 := orEqFalse_leftFalse rest6
  have rest4 := orEqFalse_leftFalse rest5
  have rest3 := orEqFalse_leftFalse rest4
  have rest2 := orEqFalse_leftFalse rest3
  have elimFalse := orEqFalse_rightFalse rest3
  have introFalse := orEqFalse_rightFalse rest2
  have formationFalse := orEqFalse_leftFalse rest2
  have roleless : typingRoleOf generator = none := by
    dsimp only [typingRoleOf]
    rw [if_neg (notEqTrue_ofEqFalse formationFalse),
        if_neg (notEqTrue_ofEqFalse introFalse),
        if_neg (notEqTrue_ofEqFalse elimFalse)]
  have notVar : generator ≠ Generator.gen_var := by
    intro isVar; rw [isVar] at varFalse; exact Bool.noConfusion varFalse
  have notUniverse : generator ≠ Generator.gen_universeCode := by
    intro isUniverse; rw [isUniverse] at universeCodeFalse; exact Bool.noConfusion universeCodeFalse
  exact decide_eq_true ⟨roleless, notVar, notUniverse⟩

/-! ## Per-engine negative soundness -/

/-- GROWN engine: a reserved-head cell has no `HasTypeDescPi` typing (via the bridge + `isUntypableHead_sound`). -/
theorem grownReservedUntyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (reserved : hasSomeTypingRule (RawTerm.headGenerator subject) = false)
    (typed : HasTypeDescPi profile context subject classifier) : False := by
  cases subject with
  | mkGen generator payload children =>
    exact isUntypableHead_sound (hasSomeTypingRule_false_imp_isUntypableHead generator reserved) typed

/-- BRIDGE engine (interval/bridge formation, endpoints, path intro/elim).  Every arm's subject is a
concrete cell whose head the classifier reports `true`, so a `false` report is `Bool.noConfusion`. -/
theorem bridgeReservedUntyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (reserved : hasSomeTypingRule (RawTerm.headGenerator subject) = false)
    (typed : HasTypeDescBridge profile context subject classifier) : False := by
  cases typed <;> exact Bool.noConfusion reserved

/-! ## ★ The bundle — reserved ⟹ untyped by the surviving standalone engines -/

/-- **★ HON-5 headline: a head the honest classifier reports RESERVED is typed by no surviving standalone
engine.**  For a subject whose head `hasSomeTypingRule` reports `false`, both surviving standalone typing
engines — grown (`HasTypeDescPi`) and bridge (`HasTypeDescBridge`) — reject it at every classifier.  This is
the soundness that makes `hasSomeTypingRule = false` a TRUTHFUL "statically reserved" verdict, not just a
`Bool` that happens to compute.  The retired base-type / data-intro / flat formation arms (now
`baseTypeFormation` / `dataIntroNullary` / `flatFormation` arms of `HasTypeNativeUnion`) are subsumed by the
single-judgment successor `HasTypeNativeUnion.reservedHeadUntyped` in `UnionStaticTypingSoundness`, stated over
the full-union classifier `hasUnionEliminatorTypingRule`; consult that for the every-native-rule statement. -/
theorem reservedHeadUntypedBySurvivingEngines {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject : RawTerm scope}
    (reserved : hasSomeTypingRule (RawTerm.headGenerator subject) = false) :
    (∀ classifier : RawTerm scope, ¬ HasTypeDescPi profile context subject classifier) ∧
    (∀ classifier : RawTerm scope, ¬ HasTypeDescBridge profile context subject classifier) :=
  ⟨fun _ typed => grownReservedUntyped reserved typed,
   fun _ typed => bridgeReservedUntyped reserved typed⟩

end FX1Poly.Typed
