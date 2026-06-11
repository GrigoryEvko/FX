import FX1Poly.Typed.HasTypeDescIdIntro

/-! # FX1Poly/Typed/HasTypeDescIdElim — the identity ELIMINATOR (idJ) + typed branch-selection ι-computation
    (DI-5e: the identity eliminator, completing the identity data story — intro DI-2d + this elim).

DI-2d typed the reflexivity constructor `refl`; this adds the identity ELIMINATOR `idJ` and its typed
ι-COMPUTATION.  The substrate's `gen_idJ` carries the Phase-Z motive shape (3-child J,
`idJ(motive, baseCase, witness)`, arity 3, `binderShifts = [2, 0, 0]`, the motive a term under two binders, the
witness LAST), and on a `refl` witness its ι SELECTS the base case (DISCARDING the motive — pure projection):

  * `idJ(motive, baseCase, refl(x)) ↝ baseCase`  (`Step.iotaIdJRefl`)

the BRANCH-SELECTION shape (the boolElim shape — the reduct IS the base case directly).  So this reuses the
DI-5a framing exactly, on identity instead of bool.  Following the cascade-free pattern (a brand-new standalone
judgment), consuming `HasTypeDescIdIntro` (DI-2d) for the witness premise.  Following the committed
`HasTypeDescBoolElim` precedent, the stored Phase-Z motive is a PASSIVE child of the judgment (carried but not
typed) and the classifier shape stays NON-DEPENDENT (result type = the base case's type).

  * `idJCell` — the `gen_idJ` cell `idJ(motive, baseCase, witness)` (arity 3, `[2, 0, 0]`).
  * `HasTypeDescIdElim` — the judgment: `idJ(motive, baseCase, witness) : C` from a witness typed at a reflexive
    identity type `Id(A, x, x)` (by the id-intro engine — so it is a `refl`) and a base case `baseCase : C` (by
    the grown engine), with the stored motive carried passively.  The non-dependent J (result type = the base
    case's type).
  * `HasTypeDescIdElim.idJOfUniverseCodesTyped` (★) — the non-vacuous smoke `idJ(Type@0, refl(Type@0)) : Type@1`.
  * `HasTypeDescIdElim.subjectIsIdJ` — the free-index closed-forms inversion.
  * `idJReflIotaComputesTyped` (★) — the typed branch-selection ι-computation: a typed `idJ` on a `refl`
    ι-reduces to the base case, AND that base case is typed at the result `C`.  The eliminator COMPUTES and the
    computation PRESERVES TYPING — the reduct's typing is the base-case hypothesis verbatim.

## The SR-free, propext-free framing (as DI-5a)

Constructor-side: the elim is BUILT from the witness + base-case premises, the reduct's typing IS the base-case
typing.  No derivation casing (no cons-index propext trap), no witness-congruence (the full SR consumes the grown
master SR / GrownCtxConv-5 #842).  The genuinely-new content is the identity eliminator typed-and-computing.

## Zero-axiom

A single-arm positive inductive; the smoke + ι-computation theorem are direct constructions (`idJIntro` +
`reflIntro` + `Step.iotaIdJRefl`); the inversion is a free-index `cases` with `rfl`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The identity eliminator cell `idJ(motive, baseCase, witness)` — `gen_idJ` (arity 3,
`binderShifts = [2, 0, 0]`; Phase-Z motive shape: the motive a term under two binders at `scope + 2`, the
base case second, the witness LAST). -/
def idJCell {scope : Nat} (motive : RawTerm (scope + 2))
    (baseCase witness : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_idJ ()
    (.childCons motive (.childCons baseCase (.childCons witness .childNil)))

/-- **The identity eliminator judgment.**  A standalone layer typing the Phase-Z `idJ`:
`idJ(motive, baseCase, witness) : C` when the witness is typed at a reflexive identity type `Id(A, x, x)` (by the
id-intro engine — so it is a `refl`) and the base case is `baseCase : C` (by the grown engine).  The result type
is the base case's type (the substrate's J is non-dependent; following the `HasTypeDescBoolElim` precedent the
stored motive is a PASSIVE child, carried but not typed). -/
inductive HasTypeDescIdElim (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | idJIntro {scope : Nat} (context : TypingContext profile scope)
      (motive : RawTerm (scope + 2))
      (baseCase witness typeCode endpoint resultType : RawTerm scope)
      (witnessTyped :
        HasTypeDescIdIntro profile context witness (idTypeCell typeCode endpoint endpoint))
      (baseCaseTyped : HasTypeDescPi profile context baseCase resultType) :
      HasTypeDescIdElim profile context (idJCell motive baseCase witness) resultType

/-- **★ An identity eliminator is typed.**  `idJ(Type@0, refl(Type@0)) : Type@1` — the non-vacuous smoke (base
case `Type@0 : Type@1`, witness `refl(Type@0) : Id(Type@1, Type@0, Type@0)`).  The first identity eliminator the
kernel types. -/
theorem HasTypeDescIdElim.idJOfUniverseCodesTyped {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescIdElim profile (TypingContext.empty : TypingContext profile 0)
      (idJCell (.mkGen .gen_var ⟨0, Nat.zero_lt_succ 1⟩ .childNil)
        (universeCodeCell LevelExpr.lzero flag) (reflCell (universeCodeCell LevelExpr.lzero flag)))
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag) :=
  HasTypeDescIdElim.idJIntro TypingContext.empty
    (.mkGen .gen_var ⟨0, Nat.zero_lt_succ 1⟩ .childNil)
    (universeCodeCell LevelExpr.lzero flag) (reflCell (universeCodeCell LevelExpr.lzero flag))
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (universeCodeCell LevelExpr.lzero flag)
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (HasTypeDescIdIntro.reflOfUniverseCodeTyped flag)
    (HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))

/-- **★ Closed forms: an id-elim-typed subject is an `idJCell`.**  Every term typed by `HasTypeDescIdElim` is
`idJ(motive, baseCase, witness)`.  Free-index single-arm `cases`. -/
theorem HasTypeDescIdElim.subjectIsIdJ {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescIdElim profile context subject classifier) :
    ∃ (motive : RawTerm (scope + 2)) (baseCase witness : RawTerm scope),
      subject = idJCell motive baseCase witness := by
  cases derivation with
  | idJIntro motive baseCase witness _typeCode _endpoint _resultType _witnessTyped _baseCaseTyped =>
      exact ⟨motive, baseCase, witness, rfl⟩

/-- **★ Typed branch-selection ι-computation (idJ on refl).**  A typed `idJ` on `refl(witness)` is typed at the
result `C`, ι-reduces to the base case (`Step.iotaIdJRefl`), and that base case is typed at `C`.  The
branch-selection typed ι (the reduct IS the base case): the eliminator COMPUTES and the computation PRESERVES
TYPING — the reduct's typing is the base-case hypothesis verbatim.  Constructor-side: SR-free and propext-free.
The `refl(witness)` witness typing needs only the witness's own typing (`witness : A`). -/
theorem idJReflIotaComputesTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 2))
    (witness baseCase typeCode resultType : RawTerm scope)
    (witnessTyped : HasTypeDescPi profile context witness typeCode)
    (baseCaseTyped : HasTypeDescPi profile context baseCase resultType) :
    HasTypeDescIdElim profile context (idJCell motive baseCase (reflCell witness)) resultType ∧
    Step (idJCell motive baseCase (reflCell witness)) baseCase ∧
    HasTypeDescPi profile context baseCase resultType := by
  refine ⟨?_, Step.iotaIdJRefl, baseCaseTyped⟩
  exact HasTypeDescIdElim.idJIntro context motive baseCase (reflCell witness) typeCode witness resultType
    (HasTypeDescIdIntro.reflIntro context witness typeCode witnessTyped)
    baseCaseTyped

end FX1Poly.Typed
