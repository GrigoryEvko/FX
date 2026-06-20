import FX1Poly.Typed.Engine.RuleTables.ElimRuleTable
import FX1Poly.Typed.Engine.RuleTables.DataIntroSpec
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescGradedIntro
import FX1Poly.Typed.Dimensions.Graded.GradedIntroPremiseSpike

/-! # FX1Poly/Typed/IntroRuleTable — TYTAB-1 intro-collapse foundation (the uniform introducer signature)

The FOUR introducer families of `HasTypeUnionOver` — nullary data constructors
(boolTrue / boolFalse / unit / interval endpoints / natZero), graded binders (lam / pathLam), recursive
data constructors (natSucc / listCons), and grown data constructors (optionSome / optionNone / listNil /
eitherInl / eitherInr / pair / refl) — are shape-heterogeneous exactly as the eliminators were: premise
count 0-3, base and binder-shifted (`scope + 1`) union premises, a load-bearing usage-grade side
condition on the graded binders, and level/flag existentials feeding the universe-formation premises.
A four-way sum would merely re-tag.  Instead this module gives ONE uniform introducer descriptor — the
`ElimRule` shape plus exactly two additions — so the four current intro arms collapse to ONE generic
`.intro` arm, and a NEW constructor of any arity is a table row, never an arm.

  * Reuses **`ElimObligation`** (scope-packing) — every introducer premise (a child's formation, a
    binder body, a formedness obligation) is a union obligation, grown premises homogenized via the
    union's `ofGrown` embedding exactly as `listElim` homogenized its branches.
  * **`IntroRule`** = `argShifts`/`paramShifts` + an `obligations` function (now also reading the
    `levels`/`flag` existentials for the universe-formation premises) + a **`sideCondition`** (the
    load-bearing `gradedBinderChecks binderUsage body` for the graded rows; `True` elsewhere) +
    `memberCell` + dependent `outputType`.
  * **`introRuleOf`** — the merged 17-row table.

The companion `.intro` arm (landed after the elim cascade settles) carries the children + params +
levels + flag + a `sideHolds : rule.sideCondition …` + a single `∀ obligation ∈ rule.obligations …,
HasTypeUnionOver …` premise — same strictly-positive nesting the elim arm uses.

## Zero-axiom

Pure data: structures, `def`s building obligation lists by total single-shape `match` over the
concrete-index children vectors (no partial-match propext leak; the formation levels are carried as two
explicit `LevelExpr` args, NOT a `List` — `List.getD` itself depends on `propext`), and `rfl` metadata.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-- **The uniform introducer rule.**  Profile-independent table data describing one introducer of ANY
arity.  Mirrors `ElimRule` (argShifts / paramShifts / obligations / memberCell / outputType) with two
additions: `obligations` also reads the `levels`/`flag` existentials (the universe at which a
domain/formedness premise must be formed), and a `sideCondition` (the graded binders' usage-grade
check).  A new constructor is one more value of this record — no new arm. -/
structure IntroRule where
  /-- The introducer cell's children binder-shifts (= the generator's `binderShifts`). -/
  argShifts : List Nat
  /-- The existential type-index binder-shifts. -/
  paramShifts : List Nat
  /-- The introducer's premise obligations, built from the children, type indices, and the
  formation levels/flag.  Every obligation is a UNION obligation (grown premises homogenized via
  `ofGrown`); binder-shifted premises (a graded binder's body) live at their own scope. -/
  obligations : {profile : PolyProfile} → (scope : Nat) → TypingContext profile scope →
    RawTermChildren argShifts scope → RawTermChildren paramShifts scope →
    LevelExpr → LevelExpr → UniverseFlag → List (ElimObligation profile)
  /-- The introducer's structural side condition (the load-bearing `gradedBinderChecks` usage discipline
  for graded binders; `True` for the data constructors). -/
  sideCondition : (scope : Nat) → RawTermChildren argShifts scope → Prop
  /-- The introduced member cell, built from its children. -/
  memberCell : (scope : Nat) → RawTermChildren argShifts scope → RawTerm scope
  /-- The introduced type, dependent on the children and the type indices. -/
  outputType : (scope : Nat) → RawTermChildren argShifts scope →
    RawTermChildren paramShifts scope → RawTerm scope

/-! ## Nullary data constructors — childless values at a pinned type code (no premises) -/

/-- **boolTrue** — `boolTrue : Bool`. -/
def boolTrueIntroRule : IntroRule where
  argShifts := []; paramShifts := []
  obligations := fun _scope _context _args _params _level0 _level1 _flag => []
  sideCondition := fun _scope _args => True
  memberCell := fun _scope _args => RawTerm.mkGen .gen_boolTrue () .childNil
  outputType := fun _scope _args _params => boolTypeCell

/-- **boolFalse** — `boolFalse : Bool`. -/
def boolFalseIntroRule : IntroRule where
  argShifts := []; paramShifts := []
  obligations := fun _scope _context _args _params _level0 _level1 _flag => []
  sideCondition := fun _scope _args => True
  memberCell := fun _scope _args => RawTerm.mkGen .gen_boolFalse () .childNil
  outputType := fun _scope _args _params => boolTypeCell

/-- **unit** — `() : Unit`. -/
def unitIntroRule : IntroRule where
  argShifts := []; paramShifts := []
  obligations := fun _scope _context _args _params _level0 _level1 _flag => []
  sideCondition := fun _scope _args => True
  memberCell := fun _scope _args => unitCell
  outputType := fun _scope _args _params => unitTypeCell

/-- **interval0** — `0 : Interval`. -/
def interval0IntroRule : IntroRule where
  argShifts := []; paramShifts := []
  obligations := fun _scope _context _args _params _level0 _level1 _flag => []
  sideCondition := fun _scope _args => True
  memberCell := fun _scope _args => intervalZeroCell
  outputType := fun _scope _args _params => intervalTypeCell

/-- **interval1** — `1 : Interval`. -/
def interval1IntroRule : IntroRule where
  argShifts := []; paramShifts := []
  obligations := fun _scope _context _args _params _level0 _level1 _flag => []
  sideCondition := fun _scope _args => True
  memberCell := fun _scope _args => intervalOneCell
  outputType := fun _scope _args _params => intervalTypeCell

/-- **natZero** — `0 : Nat`. -/
def natZeroIntroRule : IntroRule where
  argShifts := []; paramShifts := []
  obligations := fun _scope _context _args _params _level0 _level1 _flag => []
  sideCondition := fun _scope _args => True
  memberCell := fun _scope _args => natZeroCell
  outputType := fun _scope _args _params => natTypeCell

/-! ## Graded binders — λ / pathLam (the keystone family: union body premise + usage side condition) -/

/-- **lam** — `λ(x : A). body`: domain + codomain formation (at the level existentials) and a body typed
under the domain-extended context; usage grade unrestricted (`.omega`); output the Π code. -/
def lamIntroRule : IntroRule where
  argShifts := [0, 1]; paramShifts := [1]
  obligations := fun _scope context args params level0 level1 flag =>
    match args with
    | .childCons domainCode (.childCons body .childNil) =>
      match params with
      | .childCons codomainCode .childNil =>
        [ { scope := _scope, context := context, subject := domainCode,
            classifier := universeCodeCell (level0) flag },
          { scope := _scope + 1, context := context.cons domainCode,
            subject := codomainCode,
            classifier := universeCodeCell (level1) flag },
          { scope := _scope + 1, context := context.cons domainCode,
            subject := body, classifier := codomainCode } ]
  sideCondition := fun _scope args =>
    match args with
    | .childCons _domainCode (.childCons body .childNil) =>
      gradedBinderChecks UsageGrade.omega body
  memberCell := fun _scope args =>
    match args with
    | .childCons domainCode (.childCons body .childNil) => lamCell domainCode body
  outputType := fun _scope args params =>
    match args with
    | .childCons domainCode (.childCons _body .childNil) =>
      match params with
      | .childCons codomainCode .childNil => piTyCodeCell domainCode codomainCode

/-- **pathLam** — `λ⟨i⟩. body`: the affine path abstraction.  Domain pinned to the interval, no formation
premises; the body typed under the interval-extended context at the weakened carrier; usage AFFINE
(`.one`); output the body-dependent bridge code. -/
def pathLamIntroRule : IntroRule where
  argShifts := [1]; paramShifts := [0]
  obligations := fun _scope context args params _level0 _level1 _flag =>
    match args with
    | .childCons body .childNil =>
      match params with
      | .childCons carrierCode .childNil =>
        [ { scope := _scope + 1, context := context.cons intervalTypeCell,
            subject := body, classifier := RawTerm.weaken carrierCode } ]
  sideCondition := fun _scope args =>
    match args with
    | .childCons body .childNil => gradedBinderChecks UsageGrade.one body
  memberCell := fun _scope args =>
    match args with
    | .childCons body .childNil => pathLamCell body
  outputType := fun _scope args params =>
    match args with
    | .childCons body .childNil =>
      match params with
      | .childCons carrierCode .childNil =>
        bridgeTypeCell carrierCode (RawTerm.subst0 body intervalZeroCell)
          (RawTerm.subst0 body intervalOneCell)

/-! ## Recursive data constructors — natSucc / listCons (a union-recursive child) -/

/-- **natSucc** — `natSucc(n) : Nat` with `n : Nat` typed in the union. -/
def natSuccIntroRule : IntroRule where
  argShifts := [0]; paramShifts := []
  obligations := fun _scope context args _params _level0 _level1 _flag =>
    match args with
    | .childCons child .childNil =>
      [ { scope := _scope, context := context, subject := child, classifier := natTypeCell } ]
  sideCondition := fun _scope _args => True
  memberCell := fun _scope args =>
    match args with
    | .childCons child .childNil => natSuccCell child
  outputType := fun _scope _args _params => natTypeCell

/-- **listCons** — `cons(head, tail) : List(A)` with a grown head at `A` (homogenized to union) and a
union-recursive tail at `List(A)`. -/
def listConsIntroRule : IntroRule where
  argShifts := [0, 0]; paramShifts := [0]
  obligations := fun _scope context args params _level0 _level1 _flag =>
    match args with
    | .childCons head (.childCons tail .childNil) =>
      match params with
      | .childCons elementType .childNil =>
        [ { scope := _scope, context := context, subject := head, classifier := elementType },
          { scope := _scope, context := context, subject := tail,
            classifier := listTypeCell elementType } ]
  sideCondition := fun _scope _args => True
  memberCell := fun _scope args =>
    match args with
    | .childCons head (.childCons tail .childNil) => listConsCell head tail
  outputType := fun _scope _args params =>
    match params with
    | .childCons elementType .childNil => listTypeCell elementType

/-! ## Grown data constructors — optionSome/None / listNil / eitherInl/Inr / pair / refl
(grown child/formedness premises homogenized to union obligations via `ofGrown`) -/

/-- **optionSome** — `some(a) : option(A)` with a grown value at `A`. -/
def optionSomeIntroRule : IntroRule where
  argShifts := [0]; paramShifts := [0]
  obligations := fun _scope context args params _level0 _level1 _flag =>
    match args with
    | .childCons value .childNil =>
      match params with
      | .childCons typeParam0 .childNil =>
        [ { scope := _scope, context := context, subject := value, classifier := typeParam0 } ]
  sideCondition := fun _scope _args => True
  memberCell := fun _scope args =>
    match args with
    | .childCons value .childNil => optionSomeCell value
  outputType := fun _scope _args params =>
    match params with
    | .childCons typeParam0 .childNil => optionTypeCell typeParam0

/-- **optionNone** — `none : option(A)` with a formedness premise on the free `A`. -/
def optionNoneIntroRule : IntroRule where
  argShifts := []; paramShifts := [0]
  obligations := fun _scope context _args params level0 level1 flag =>
    match params with
    | .childCons typeParam0 .childNil =>
      [ { scope := _scope, context := context, subject := typeParam0,
          classifier := universeCodeCell (level0) flag } ]
  sideCondition := fun _scope _args => True
  memberCell := fun _scope _args => optionNoneCell
  outputType := fun _scope _args params =>
    match params with
    | .childCons typeParam0 .childNil => optionTypeCell typeParam0

/-- **listNil** — `nil : List(A)` with a formedness premise on the free `A`. -/
def listNilIntroRule : IntroRule where
  argShifts := []; paramShifts := [0]
  obligations := fun _scope context _args params level0 level1 flag =>
    match params with
    | .childCons typeParam0 .childNil =>
      [ { scope := _scope, context := context, subject := typeParam0,
          classifier := universeCodeCell (level0) flag } ]
  sideCondition := fun _scope _args => True
  memberCell := fun _scope _args => listNilCell
  outputType := fun _scope _args params =>
    match params with
    | .childCons typeParam0 .childNil => listTypeCell typeParam0

/-- **eitherInl** — `inl(a) : either(A, B)` with a grown value at the LEFT `A` and a formedness premise
on the free RIGHT `B`. -/
def eitherInlIntroRule : IntroRule where
  argShifts := [0]; paramShifts := [0, 0]
  obligations := fun _scope context args params level0 level1 flag =>
    match args with
    | .childCons value .childNil =>
      match params with
      | .childCons typeParam0 (.childCons typeParam1 .childNil) =>
        [ { scope := _scope, context := context, subject := value, classifier := typeParam0 },
          { scope := _scope, context := context, subject := typeParam1,
            classifier := universeCodeCell (level0) flag } ]
  sideCondition := fun _scope _args => True
  memberCell := fun _scope args =>
    match args with
    | .childCons value .childNil => eitherInlCell value
  outputType := fun _scope _args params =>
    match params with
    | .childCons typeParam0 (.childCons typeParam1 .childNil) => eitherTypeCell typeParam0 typeParam1

/-- **eitherInr** — `inr(b) : either(A, B)` with a grown value at the pinned RIGHT type (`typeParam0`), a
formedness premise on the free LEFT (`typeParam1`); output puts the free side first. -/
def eitherInrIntroRule : IntroRule where
  argShifts := [0]; paramShifts := [0, 0]
  obligations := fun _scope context args params level0 level1 flag =>
    match args with
    | .childCons value .childNil =>
      match params with
      | .childCons typeParam0 (.childCons typeParam1 .childNil) =>
        [ { scope := _scope, context := context, subject := value, classifier := typeParam0 },
          { scope := _scope, context := context, subject := typeParam1,
            classifier := universeCodeCell (level0) flag } ]
  sideCondition := fun _scope _args => True
  memberCell := fun _scope args =>
    match args with
    | .childCons value .childNil => eitherInrCell value
  outputType := fun _scope _args params =>
    match params with
    | .childCons typeParam0 (.childCons typeParam1 .childNil) => eitherTypeCell typeParam1 typeParam0

/-- **pair** — `(a, b) : product(A, B)` with two grown children at the two independent type params. -/
def pairIntroRule : IntroRule where
  argShifts := [0, 0]; paramShifts := [0, 0]
  obligations := fun _scope context args params _level0 _level1 _flag =>
    match args with
    | .childCons child0 (.childCons child1 .childNil) =>
      match params with
      | .childCons typeParam0 (.childCons typeParam1 .childNil) =>
        [ { scope := _scope, context := context, subject := child0, classifier := typeParam0 },
          { scope := _scope, context := context, subject := child1, classifier := typeParam1 } ]
  sideCondition := fun _scope _args => True
  memberCell := fun _scope args =>
    match args with
    | .childCons child0 (.childCons child1 .childNil) => pairCell child0 child1
  outputType := fun _scope _args params =>
    match params with
    | .childCons typeParam0 (.childCons typeParam1 .childNil) => productTypeCell typeParam0 typeParam1

/-- **refl** — `refl(a) : Id(A, a, a)`; a grown witness at its type, output reads the witness VALUE. -/
def reflIntroRule : IntroRule where
  argShifts := [0]; paramShifts := [0]
  obligations := fun _scope context args params _level0 _level1 _flag =>
    match args with
    | .childCons witness .childNil =>
      match params with
      | .childCons typeParam0 .childNil =>
        [ { scope := _scope, context := context, subject := witness, classifier := typeParam0 } ]
  sideCondition := fun _scope _args => True
  memberCell := fun _scope args =>
    match args with
    | .childCons witness .childNil => reflCell witness
  outputType := fun _scope args params =>
    match args with
    | .childCons witness .childNil =>
      match params with
      | .childCons typeParam0 .childNil => idTypeCell typeParam0 witness witness

/-! ## The merged table -/

/-- **The uniform introducer table.**  Every intro generator's `IntroRule` row.  A `ProfileExtension`
adding a constructor of any arity is one more row here, never a new typing arm. -/
def introRuleOf (generator : Generator) : Option IntroRule :=
  if generator = .gen_boolTrue then some boolTrueIntroRule
  else if generator = .gen_boolFalse then some boolFalseIntroRule
  else if generator = .gen_unit then some unitIntroRule
  else if generator = .gen_interval0 then some interval0IntroRule
  else if generator = .gen_interval1 then some interval1IntroRule
  else if generator = .gen_natZero then some natZeroIntroRule
  else if generator = .gen_lam then some lamIntroRule
  else if generator = .gen_pathLam then some pathLamIntroRule
  else if generator = .gen_natSucc then some natSuccIntroRule
  else if generator = .gen_listCons then some listConsIntroRule
  else if generator = .gen_optionSome then some optionSomeIntroRule
  else if generator = .gen_optionNone then some optionNoneIntroRule
  else if generator = .gen_listNil then some listNilIntroRule
  else if generator = .gen_eitherInl then some eitherInlIntroRule
  else if generator = .gen_eitherInr then some eitherInrIntroRule
  else if generator = .gen_pair then some pairIntroRule
  else if generator = .gen_refl then some reflIntroRule
  else none

/-! ## Table metadata (cascade-death `rfl` lemmas) -/

theorem introRuleOf_boolTrue : introRuleOf .gen_boolTrue = some boolTrueIntroRule := rfl
theorem introRuleOf_boolFalse : introRuleOf .gen_boolFalse = some boolFalseIntroRule := rfl
theorem introRuleOf_unit : introRuleOf .gen_unit = some unitIntroRule := rfl
theorem introRuleOf_interval0 : introRuleOf .gen_interval0 = some interval0IntroRule := rfl
theorem introRuleOf_interval1 : introRuleOf .gen_interval1 = some interval1IntroRule := rfl
theorem introRuleOf_natZero : introRuleOf .gen_natZero = some natZeroIntroRule := rfl
theorem introRuleOf_lam : introRuleOf .gen_lam = some lamIntroRule := rfl
theorem introRuleOf_pathLam : introRuleOf .gen_pathLam = some pathLamIntroRule := rfl
theorem introRuleOf_natSucc : introRuleOf .gen_natSucc = some natSuccIntroRule := rfl
theorem introRuleOf_listCons : introRuleOf .gen_listCons = some listConsIntroRule := rfl
theorem introRuleOf_optionSome : introRuleOf .gen_optionSome = some optionSomeIntroRule := rfl
theorem introRuleOf_optionNone : introRuleOf .gen_optionNone = some optionNoneIntroRule := rfl
theorem introRuleOf_listNil : introRuleOf .gen_listNil = some listNilIntroRule := rfl
theorem introRuleOf_eitherInl : introRuleOf .gen_eitherInl = some eitherInlIntroRule := rfl
theorem introRuleOf_eitherInr : introRuleOf .gen_eitherInr = some eitherInrIntroRule := rfl
theorem introRuleOf_pair : introRuleOf .gen_pair = some pairIntroRule := rfl
theorem introRuleOf_refl : introRuleOf .gen_refl = some reflIntroRule := rfl

end FX1Poly.Typed
