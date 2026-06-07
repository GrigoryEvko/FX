import FX1Poly.Typed.HasTypeDesc

/-! # FX1Poly/Typed/DescTelescopeReach
    — the formation premise telescope's structural REACH: its children's binderShifts are forced cumulative

The formation engine's `genFormation` arm (`HasTypeDesc.lean`) types a former cell `mkGen generator payload
children` whenever `typingRuleDescOf generator = some rule` AND the children form a `DescTelescope` of types.
But the `DescTelescope.cons` arm always recurses with `currentDepth + 1` under `context.cons head`, so each
successive child is typed one binder deeper than the previous — child `i` sits at de Bruijn shift `i`.  This
file makes that precise: a `DescTelescope` forces its children's `binderShifts` index to be exactly the
CUMULATIVE sequence `[depth, depth+1, depth+2, ...]`.

## The reach consequence (and a correction to the data-former roadmap)

The genFormation premise is constructible only for formers whose `binderShifts` is the cumulative prefix
`[0, 1, ..., n-1]`.  Surveying the type-code generators (`GeneratorCore.binderShifts`):

  * **cumulative, REACHABLE**: `piTyCode` / `sigmaTyCode` (`[0, 1]` — the dependent formers, codomain under the
    domain binder) and `listCode` / `optionCode` (`[0]` — the one-child data formers).  These are exactly the
    four formation rows `typingRuleDescOf` carries today.
  * **non-dependent `[0, 0]`, UNREACHABLE**: `productCode` / `sumCode` / `eitherCode` / `arrowCode` /
    `equivCode` — both children at the SAME (base) scope, NOT cumulative.  `DescTelescope.noFlatTwoChildTelescope`
    proves no depth-0 telescope has `[0, 0]` children (the cumulative sequence at length 2 is `[0, 1]`, whose
    second shift is `1`, not `0`).

So adding a `typingRuleDescOf` row for a non-dependent former would be VACUOUS: `genFormation`'s telescope
premise can never be built, so no `HasTypeDesc` derivation for a `productCode` / `sumCode` / … cell would
exist.  Typing the non-dependent data formers therefore requires GENERALIZING the premise telescope to a
non-cumulative ("flat") shape where sibling children share the base context — a change to the formation
engine's premise structure, NOT the `listCode`-style additive cascade (GTL-11 / GTL-13).  This corrects the
assumption that the next data type-code is "the same cascade with a multi-child telescope": the one-child
`listCode` / `optionCode` cascade reused the cumulative `[0]` telescope, but the `[0, 0]` formers have no
telescope at all yet.

## Zero-axiom verification

`binderShiftsAreCumulative` is structural recursion over the mutual telescope (term-mode `match` with a
recursive self-call on the tail, the established pattern from `DescTelescopePi.convTelescopeOfPiElimArm`); the
`nil` arm is `rfl`, the `cons` arm rewrites by the cumulative-step equation and the tail hypothesis.  The
`[0, 0]` impossibility extracts `levels.length = 2` (via `cumulativeShifts_length` + `congrArg List.length`),
specializes the cumulative sequence to `[0, 1]`, and refutes the second-shift equation `0 = 1` by plain
`Nat.noConfusion` after two `List` injections — no impossible-case `cases` on an indexed inductive, so no
`propext` / `Quot.sound` leak.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The cumulative shift sequence `[start, start+1, ..., start+count-1]` — the binderShifts a depth-`start`
formation telescope of `count` children is forced to carry. -/
def cumulativeShifts (start : Nat) : Nat → List Nat
  | 0 => []
  | count + 1 => start :: cumulativeShifts (start + 1) count

/-- One unfolding step of `cumulativeShifts` (the recursive equation, by `rfl`). -/
theorem cumulativeShifts_succ (start count : Nat) :
    cumulativeShifts start (count + 1) = start :: cumulativeShifts (start + 1) count := rfl

/-- A cumulative sequence of `count` children has length `count`. -/
theorem cumulativeShifts_length (start count : Nat) :
    (cumulativeShifts start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ innerCount innerHypothesis =>
      rw [cumulativeShifts_succ, List.length_cons, innerHypothesis]

/-- **The formation telescope forces cumulative binderShifts.**  A `DescTelescope` over children indexed by
`binderShifts`, with `count = levels.length` children at current depth `currentDepth`, forces
`binderShifts = [currentDepth, currentDepth+1, ..., currentDepth + count - 1]`.  Proved by structural recursion
over the mutual telescope (the `convTelescopeOfPiElimArm` pattern): `nil` gives `[] = cumulativeShifts _ 0`;
`cons` prepends the head shift `currentDepth` and rewrites the tail by the recursive hypothesis at
`currentDepth + 1`. -/
theorem DescTelescope.binderShiftsAreCumulative {profile : PolyProfile} {baseScope currentDepth : Nat}
    {binderShifts : List Nat} {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescope profile context levels flag children) :
    binderShifts = cumulativeShifts currentDepth levels.length :=
  match telescope with
  | .nil _context _flag => rfl
  | .cons _context _head _headLevel restLevels _flag _rest _headTyped restTyped => by
      have restHypothesis := DescTelescope.binderShiftsAreCumulative restTyped
      show _ :: _ = cumulativeShifts _ (restLevels.length + 1)
      rw [cumulativeShifts_succ, restHypothesis]

/-- **Depth-0 specialization.**  A genFormation-level (`currentDepth = 0`) telescope forces its children's
shifts to be `[0, 1, ..., levels.length - 1]` — the only shift shapes the formation engine can type. -/
theorem DescTelescope.binderShiftsAreCumulativeFromZero {profile : PolyProfile} {baseScope : Nat}
    {binderShifts : List Nat} {context : TypingContext profile baseScope}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescope profile (currentDepth := 0) context levels flag children) :
    binderShifts = cumulativeShifts 0 levels.length :=
  DescTelescope.binderShiftsAreCumulative telescope

/-- **The non-dependent `[0, 0]` shape is OUTSIDE the telescope's reach.**  No depth-0 formation telescope has
`[0, 0]` children: the cumulative sequence at length 2 is `[0, 1]`, whose second shift `1 ≠ 0`.  This is the
structural obstruction blocking the non-dependent two-child type-code formers
(`product` / `sum` / `either` / `arrow` / `equiv`) from the formation engine. -/
theorem DescTelescope.noFlatTwoChildTelescope {profile : PolyProfile} {baseScope : Nat}
    {context : TypingContext profile baseScope} {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren [0, 0] baseScope}
    (telescope : DescTelescope profile (currentDepth := 0) context levels flag children) : False := by
  have shapeEq := DescTelescope.binderShiftsAreCumulativeFromZero telescope
  have lengthEq : levels.length = 2 := by
    have lengthsAgree : (cumulativeShifts 0 levels.length).length = ([0, 0] : List Nat).length :=
      congrArg List.length shapeEq.symm
    rw [cumulativeShifts_length] at lengthsAgree
    exact lengthsAgree
  rw [lengthEq] at shapeEq
  injection shapeEq with _firstShift tailEq
  injection tailEq with secondShift _tailRest
  exact Nat.noConfusion secondShift

/-- **`gen_productCode`'s formation telescope is impossible** — the worked generator-level corollary.  Since
`(Generator.gen_productCode).binderShifts = [0, 0]` (a non-dependent pair), the genFormation premise for a
`productCode` cell is exactly a `[0, 0]` telescope, ruled out by `noFlatTwoChildTelescope`.  The same holds
verbatim for `gen_sumCode` / `gen_eitherCode` / `gen_arrowCode` / `gen_equivCode` (all `[0, 0]`); productCode
is the representative.  Consequence: a `typingRuleDescOf .gen_productCode` row could never be exercised, so the
non-dependent data formers need a flat-telescope generalization, not a row addition. -/
theorem DescTelescope.productCodeFormationTelescopeImpossible {profile : PolyProfile} {baseScope : Nat}
    {context : TypingContext profile baseScope} {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren (Generator.gen_productCode).binderShifts baseScope}
    (telescope : DescTelescope profile (currentDepth := 0) context levels flag children) : False :=
  DescTelescope.noFlatTwoChildTelescope telescope

end FX1Poly.Typed
