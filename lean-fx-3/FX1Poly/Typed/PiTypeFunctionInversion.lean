import FX1Poly.Typed.EmptyTypeValueInversion

/-! # FX1Poly/Typed/PiTypeFunctionInversion — a type former / universe code is not a Π-type member
    (the piElim-killing toolkit for the grown closed canonical forms)

The grown closed canonical-forms argument (`HasTypeDescPi .empty t T → isStepNormalForm t → t is
λ / Π / Σ / universe`) turns on its `piElim` (application) case: a closed NORMAL application `appCell f a`
has `f` closed, normal, typed at a Π-code, so by the induction hypothesis `f` is a λ / Π-former / Σ-former /
universe-code.  This file ships the two ingredients that close that case:

* `eq_lamCell_of_headGenerator` — the missing fourth head→shape reconstruction (alongside the shipped
  `eq_{piTyCodeCell,sigmaTyCodeCell,universeCodeCell,variableCell}_of_headGenerator`): a `gen_lam`-headed cell
  IS a `lamCell`.  In the `piElim` case this turns `f`'s λ head into the syntactic β-redex `appCell (lamCell _)
  a`, which is not normal — contradiction.

* the three `*NotTypedAtPiType` inversions — a Π-type FORMER, a Σ-type former, or a universe CODE is never a
  member of a Π-type.  A function type's member is a function (a λ or a neutral); a type former / universe code
  is a TYPE, classified by a universe code, and a Π-code is not `Conv` a universe code
  (`Conv.piTyCode_not_universeCode`).  These are the Π-classifier analogues of the empty-type value-case
  inversions in `EmptyTypeValueInversion` (`*NotTypedAtEmptyType`), via the SAME grown inversions
  (`invertPiTyCode` / `invertSigmaTyCode` / `inversionUniverseCode`, all context-free).

Together with the formation-engine canonical forms (`FormationCanonicalForms.lean`) and β-redex
non-normality, these discharge every non-λ shape `f` can take in the `piElim` case — so a closed normal
function-typed term is a λ, the grown progress fact feeding SN-050 consistency (modulo SN + SR).

## Zero-axiom verification

`eq_lamCell_of_headGenerator`: `cases` on the single-constructor `RawTerm`, `change` (defeq) to the
`gen_lam` head + `[1]` child spine, `RawTermChildren.eq_childNil` collapse — the same propext-free substrate
as `eq_piTyCodeCell_of_headGenerator`.  The inversions: one shipped grown inversion + `Conv.piTyCode_not_universeCode`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The fourth head→shape reconstruction.**  A cell whose head generator is `gen_lam` IS a Church-style
`lamCell`: its two-entry child spine (`gen_lam.binderShifts = [0, 1]`, the domain annotation at `scope` then
the body at `scope + 1`) is recovered by destructuring the `RawTermChildren` twice and collapsing the
`childNil` tail — the λ companion to `eq_piTyCodeCell_of_headGenerator` (same `[0, 1]` two-child spine). -/
theorem eq_lamCell_of_headGenerator {scope : Nat} {cell : RawTerm scope}
    (headIsLam : RawTerm.headGenerator cell = Generator.gen_lam) :
    ∃ (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)), cell = lamCell domainAnn body := by
  cases cell with
  | mkGen generator payload children =>
      change generator = Generator.gen_lam at headIsLam
      subst headIsLam
      change RawTermChildren [0, 1] scope at children
      cases children with
      | childCons domainAnn restChildren =>
          cases restChildren with
          | childCons body tailChildren =>
              refine ⟨domainAnn, body, ?_⟩
              rw [RawTermChildren.eq_childNil tailChildren]
              rfl

/-- **A Π-type FORMER is not a member of a Π-type.**  Inverting the former (`invertPiTyCode`) exposes the
would-be Π-type classifier as `Conv` a universe code; a Π-code is not `Conv` a universe code
(`Conv.piTyCode_not_universeCode`).  The Π-classifier analogue of `piFormerNotTypedAtEmptyType`. -/
theorem HasTypeDescPi.piFormerNotTypedAtPiType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {innerDomain : RawTerm scope} {innerCodomain : RawTerm (scope + 1)}
    {outerDomain : RawTerm scope} {outerCodomain : RawTerm (scope + 1)}
    (typed :
      HasTypeDescPi profile context (piTyCodeCell innerDomain innerCodomain)
        (piTyCodeCell outerDomain outerCodomain)) :
    False := by
  obtain ⟨_, _, _, _, _, convToUniverseCode⟩ := HasTypeDescPi.invertPiTyCode typed
  exact Conv.piTyCode_not_universeCode convToUniverseCode

/-- **A Σ-type former is not a member of a Π-type** — the Σ dual of `piFormerNotTypedAtPiType`. -/
theorem HasTypeDescPi.sigmaFormerNotTypedAtPiType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {innerDomain : RawTerm scope} {innerCodomain : RawTerm (scope + 1)}
    {outerDomain : RawTerm scope} {outerCodomain : RawTerm (scope + 1)}
    (typed :
      HasTypeDescPi profile context (sigmaTyCodeCell innerDomain innerCodomain)
        (piTyCodeCell outerDomain outerCodomain)) :
    False := by
  obtain ⟨_, _, _, _, _, convToUniverseCode⟩ := HasTypeDescPi.invertSigmaTyCode typed
  exact Conv.piTyCode_not_universeCode convToUniverseCode

/-- **A universe code is not a member of a Π-type.**  Inverting the universe code
(`inversionUniverseCode`) exposes the would-be Π-type classifier as `Conv` the next universe; a Π-code is not
`Conv` a universe code.  Completes the type-shaped piElim cases. -/
theorem HasTypeDescPi.universeCodeNotTypedAtPiType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    {outerDomain : RawTerm scope} {outerCodomain : RawTerm (scope + 1)}
    (typed :
      HasTypeDescPi profile context (universeCodeCell levelExpr flag)
        (piTyCodeCell outerDomain outerCodomain)) :
    False :=
  Conv.piTyCode_not_universeCode (HasTypeDescPi.inversionUniverseCode typed)

end FX1Poly.Typed
