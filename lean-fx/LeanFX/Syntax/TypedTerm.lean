import LeanFX.Syntax.Context

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Terms

`Term context currentType` is a well-typed term in `context` of type
`currentType`.  Constructor signatures are the typing rules; Lean's
kernel checks each rule at declaration time, so a misstated rule is
rejected before any program is written using it. -/

/-- Intrinsically-typed terms.  No separate typing relation — the
constructor signatures *are* the typing rules. -/
inductive Term : {mode : Mode} → {level scope : Nat} →
                 (context : Ctx mode level scope) → Ty level scope → Type
  /-- Variable rule.  A term is a variable iff it carries a Fin-scoped
  position; the type is computed by `varType` from the context.
  Replaces the v1.0 `Lookup`-indexed form, which forced propext through
  the match compiler at term-level rawRenaming.  v1.9. -/
  | var :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      (position : Fin scope) →
      Term context (varType context position)
  /-- Unit introduction at every scope. -/
  | unit :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      Term context Ty.unit
  /-- λ-abstraction.  The body is checked in the context extended with
  the bound variable; its expected type is the codomain weakened to
  the extended scope. -/
  | lam :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {domainType codomainType : Ty level scope} →
      (body : Term (Ctx.cons context domainType) codomainType.weaken) →
      Term context (Ty.arrow domainType codomainType)
  /-- Non-dependent application — function expects the codomain at the
  same scope as the domain. -/
  | app :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {domainType codomainType : Ty level scope} →
      (functionTerm : Term context (Ty.arrow domainType codomainType)) →
      (argumentTerm : Term context domainType) →
      Term context codomainType
  /-- λ-abstraction for dependent `piTy`.  Body's type is the codomain
  directly (at scope `+1`) — no weakening needed because `piTy`'s
  codomain is already at the extended scope. -/
  | lamPi :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {domainType : Ty level scope} →
      {codomainType : Ty level (scope + 1)} →
      (body : Term (Ctx.cons context domainType) codomainType) →
      Term context (Ty.piTy domainType codomainType)
  /-- Application for dependent `piTy`.  Result type is the codomain
  with var 0 substituted by the argument's domain type — using
  `Ty.subst0` which is axiom-free thanks to the function-typed `Subst`
  threading scope information without Nat arithmetic.

  For v1.0+ `Ty` (no `Ty.tyVar`), `B.subst0 A` reduces to `B`'s
  structural shape at scope (the substituent is unused since `B` has
  no variable references).  When `Ty.tyVar` lands in v1.5+, this rule
  remains unchanged but `subst0` actually looks up the substituent. -/
  | appPi :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {domainType : Ty level scope} →
      {codomainType : Ty level (scope + 1)} →
      (functionTerm : Term context (Ty.piTy domainType codomainType)) →
      (argumentTerm : Term context domainType) →
      Term context (codomainType.subst0 domainType)
  /-- Pair introduction for dependent `sigmaTy`.  The second
  component's type is `secondType` with var 0 substituted by
  `firstType` — same `Ty.subst0` mechanism `appPi` uses. -/
  | pair :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {firstType : Ty level scope} →
      {secondType : Ty level (scope + 1)} →
      (firstVal : Term context firstType) →
      (secondVal : Term context (secondType.subst0 firstType)) →
      Term context (Ty.sigmaTy firstType secondType)
  /-- First projection.  Extracts the first component of a pair. -/
  | fst :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {firstType : Ty level scope} →
      {secondType : Ty level (scope + 1)} →
      (pairTerm : Term context (Ty.sigmaTy firstType secondType)) →
      Term context firstType
  /-- Second projection.  Result type uses the same `subst0`
  placeholder substitution as `pair`. -/
  | snd :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {firstType : Ty level scope} →
      {secondType : Ty level (scope + 1)} →
      (pairTerm : Term context (Ty.sigmaTy firstType secondType)) →
      Term context (secondType.subst0 firstType)
  /-- Boolean introduction — `true` literal at every context.  v1.13+. -/
  | boolTrue :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      Term context Ty.bool
  /-- Boolean introduction — `false` literal at every context.  v1.13+. -/
  | boolFalse :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      Term context Ty.bool
  /-- Boolean elimination (non-dependent) — case-analysis on a boolean
  scrutinee produces one of two same-typed branches.  Non-dependent
  because the result type is a fixed `Ty level scope`, not a function on
  `bool`; dependent elim would require representing motives as
  functions on `Term`-valued booleans, which doesn't fit the current
  scope-only `Ty` indexing.  v1.14+. -/
  | boolElim :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {resultType : Ty level scope} →
      (scrutinee : Term context Ty.bool) →
      (thenBranch : Term context resultType) →
      (elseBranch : Term context resultType) →
      Term context resultType
  /-- Natural-number introduction — `0`. -/
  | natZero :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      Term context Ty.nat
  /-- Natural-number introduction — `succ n`. -/
  | natSucc :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      (predecessor : Term context Ty.nat) →
      Term context Ty.nat
  /-- Natural-number elimination (case-analysis form).  Cases on the
  scrutinee: zero produces `zeroBranch`, `succ n` applies the
  predecessor function `succBranch` to `n`.  Case-analysis only — the
  succ branch does NOT see a recursive result; primitive recursion
  with the IH lands in v1.32 as `Term.natRec`.

  Result type is fixed to `resultType : Ty level scope`, parallel to
  `Term.boolElim` — non-dependent.  Dependent elimination requires
  motives over Term-valued scrutinees, which the current scope-only
  Ty indexing doesn't accommodate. -/
  | natElim :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {resultType : Ty level scope} →
      (scrutinee : Term context Ty.nat) →
      (zeroBranch : Term context resultType) →
      (succBranch : Term context (Ty.arrow Ty.nat resultType)) →
      Term context resultType
  /-- Primitive recursion on naturals — Church-style recursor with
  induction hypothesis.  Strictly stronger than `natElim`
  (case-analysis): the succ-branch sees BOTH the predecessor `n` and
  the recursive result `natRec n z s : resultType`.

  Surface analogue:
      `natRec(scrutinee, z, fn n ih => …)` — `ih` is the recursion's
      result on the predecessor.  Primitive recursion captures
      addition, multiplication, factorial, fold/Foldr, etc.

  Reduction:
      `natRec 0       z s ⟶ z`
      `natRec (succ n) z s ⟶ s n (natRec n z s)`

  Result type is fixed (non-dependent), parallel to `natElim`.
  *True* dependent induction (`natInd`) — where the result type
  varies with the scrutinee — requires either universe codes
  (`El : Term Γ (Ty.universe u rfl) → Ty u scope`) or term-aware
  Ty indexing.  Both deferred until after v1.40 identity types,
  which supplies the cast machinery the dependent ι-rule needs. -/
  | natRec :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {resultType : Ty level scope} →
      (scrutinee : Term context Ty.nat) →
      (zeroBranch : Term context resultType) →
      (succBranch : Term context
         (Ty.arrow Ty.nat (Ty.arrow resultType resultType))) →
      Term context resultType
  /-- Empty list — `[]` at any element type.  The `elementType` is an
  implicit argument that callers supply via the expected return type
  (or `(elementType := T)`). -/
  | listNil :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {elementType : Ty level scope} →
      Term context (Ty.list elementType)
  /-- List cons — `head :: tail`.  Both head and tail share the same
  element type, propagated to the result. -/
  | listCons :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {elementType : Ty level scope} →
      (head : Term context elementType) →
      (tail : Term context (Ty.list elementType)) →
      Term context (Ty.list elementType)
  /-- List elimination (case-analysis form).  Cases on the scrutinee:
  empty list produces `nilBranch`, `cons head tail` applies the curried
  function `consBranch` to head and then tail.  Case-analysis only —
  no recursive-result IH (primitive recursion comes later via
  `Term.listRec`).  Result type fixed; non-dependent. -/
  | listElim :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {elementType : Ty level scope} →
      {resultType : Ty level scope} →
      (scrutinee : Term context (Ty.list elementType)) →
      (nilBranch : Term context resultType) →
      (consBranch : Term context
         (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))) →
      Term context resultType
  /-- Empty option — `none`.  ElementType is supplied via the expected
  return type or `(elementType := T)`. -/
  | optionNone :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {elementType : Ty level scope} →
      Term context (Ty.option elementType)
  /-- Option wrap — `some value`. -/
  | optionSome :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {elementType : Ty level scope} →
      (value : Term context elementType) →
      Term context (Ty.option elementType)
  /-- Option elimination (case-analysis form).  None case: `noneBranch`.
  Some case: apply `someBranch : elem → result` to the contained value.
  Mirror of `listElim` but with no tail in the some-case. -/
  | optionMatch :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {elementType : Ty level scope} →
      {resultType : Ty level scope} →
      (scrutinee : Term context (Ty.option elementType)) →
      (noneBranch : Term context resultType) →
      (someBranch : Term context (Ty.arrow elementType resultType)) →
      Term context resultType
  /-- Sum left-injection — `inl value` at element type `leftType`,
  with `rightType` carried implicitly via the expected return type. -/
  | eitherInl :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {leftType rightType : Ty level scope} →
      (value : Term context leftType) →
      Term context (Ty.either leftType rightType)
  /-- Sum right-injection — `inr value` at element type `rightType`,
  with `leftType` carried implicitly. -/
  | eitherInr :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {leftType rightType : Ty level scope} →
      (value : Term context rightType) →
      Term context (Ty.either leftType rightType)
  /-- Sum elimination (case-analysis form).  Left case: apply
  `leftBranch : leftType → resultType` to the contained value.
  Right case: apply `rightBranch : rightType → resultType`.
  Symmetric to `optionMatch` but with both branches function-shaped
  (since both carry payloads). -/
  | eitherMatch :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {leftType rightType : Ty level scope} →
      {resultType : Ty level scope} →
      (scrutinee : Term context (Ty.either leftType rightType)) →
      (leftBranch : Term context (Ty.arrow leftType resultType)) →
      (rightBranch : Term context (Ty.arrow rightType resultType)) →
      Term context resultType
  /-- **Reflexivity introduction for identity types** — `refl rawTerm`
  inhabits `Id carrier rawTerm rawTerm` for any FX type `carrier` and
  any raw term `rawTerm` in the surrounding scope.

  This layer does NOT enforce that `rawTerm` actually inhabits
  `carrier` at the FX level — endpoint type-correctness is a
  property checked by `HasType` / the bridge `Term.toRaw`
  (v2.2j).  Within the kernel, `Term.refl` is the introduction
  form for `Ty.id` as an inductive proposition; the J eliminator
  (v2.2m) consumes it. -/
  | refl :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {carrier : Ty level scope} →
      (rawTerm : RawTerm scope) →
      Term context (Ty.id carrier rawTerm rawTerm)
  /-- **J eliminator for identity types** (open-endpoint, non-dependent
  motive form).  Given a base case `baseCase : resultType` and a
  witness `witness : Id carrier leftEnd rightEnd`, produces a term of
  `resultType`.

  In this non-dependent form, a `Term.refl` witness can only
  inhabit `Id A rt rt` (both endpoints equal), so the only canonical
  J reduction is the ι-rule `J base (refl rt) ⟶ base`.  The
  non-dependent motive (`resultType : Ty level scope` instead of a
  motive function over endpoints) keeps the constructor signature
  inside the kernel without needing Term-mentioning Ty constructors
  beyond Ty.id itself.

  Full dependent J — where the result type depends on the endpoints
  and the witness — requires open endpoints + a motive of shape
  `(a b : A) → Id A a b → Ty`.  That waits for the joint Subst
  refactor (v2.3+), at which point this constructor becomes a
  specialised non-dependent form derivable from dependent J. -/
  | idJ :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {carrier : Ty level scope} →
      {leftEnd rightEnd : RawTerm scope} →
      {resultType : Ty level scope} →
      (baseCase : Term context resultType) →
      (witness : Term context (Ty.id carrier leftEnd rightEnd)) →
      Term context resultType

/-! ## Term-level rawRenaming.

`TermRenaming Γ Δ ρ` is the position-equality property: at every
`Fin scope` of `Γ`, the looked-up type at `ρ i` in `Δ` equals
`varType Γ i` after type-level rawRenaming.  A `Prop` rather than a
`Type` so `Term.rename` can descend through the term without the
match compiler emitting `Ctx.noConfusion`. -/

/-- Property witnessing that the type-level rawRenaming `ρ` is consistent
with two contexts: at every position `i` of `Γ`, the looked-up type at
`ρ i` in `Δ` equals the looked-up type at `i` in `Γ` after rawRenaming.
Replaces the v1.8 type-of-Lookups formulation. -/
def TermRenaming {m : Mode} {level scope scope' : Nat}
    (Γ : Ctx m level scope) (Δ : Ctx m level scope')
    (ρ : Renaming scope scope') : Prop :=
  ∀ (i : Fin scope), varType Δ (ρ i) = (varType Γ i).rename ρ

/-- Lift a term-level rawRenaming under a binder.  Pattern-matches on
`i : Fin (scope + 1)` directly via Fin's structure (`⟨0, _⟩` and
`⟨k+1, h⟩`), so the match never sees a cons-specialised Ctx index.
Both Fin cases reduce to `Ty.rename_weaken_commute` plus, in the
successor case, the predecessor's `ρt` proof. -/
theorem TermRenaming.lift {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope'}
    (ρt : TermRenaming Γ Δ ρ) (newType : Ty level scope) :
    TermRenaming (Γ.cons newType) (Δ.cons (newType.rename ρ)) ρ.lift := by
  intro i
  match i with
  | ⟨0, _⟩ =>
      show (newType.rename ρ).weaken
         = newType.weaken.rename ρ.lift
      exact (Ty.rename_weaken_commute newType ρ).symm
  | ⟨k + 1, h⟩ =>
      show (varType Δ (ρ ⟨k, Nat.lt_of_succ_lt_succ h⟩)).weaken
           = (varType Γ ⟨k, Nat.lt_of_succ_lt_succ h⟩).weaken.rename ρ.lift
      have hρ := ρt ⟨k, Nat.lt_of_succ_lt_succ h⟩
      have hcomm := Ty.rename_weaken_commute
                      (varType Γ ⟨k, Nat.lt_of_succ_lt_succ h⟩) ρ
      exact (congrArg Ty.weaken hρ).trans hcomm.symm

/-- Renaming by the identity is the identity on `Ty`.  Derived from
the existing v1.7 substitution discipline: `Ty.rename` factors through
`Ty.subst` via `Renaming.toSubst` (lemma `Ty.rename_eq_subst`); the
identity rawRenaming corresponds to the identity substitution pointwise
(both map `i` to `Ty.tyVar i`); and the substitution discipline already
provides `Ty.subst_id`.  No fresh structural induction needed. -/
theorem Ty.rename_identity {level scope : Nat} (T : Ty level scope) :
    T.rename Renaming.identity = T :=
  let renamingIdEqSubstId :
      Subst.equiv (Renaming.toSubst (@Renaming.identity scope))
                  Subst.identity := And.intro (fun _ => rfl) (fun _ => rfl)
  (Ty.rename_eq_subst T Renaming.identity).trans
    ((Ty.subst_congr renamingIdEqSubstId T).trans (Ty.subst_id T))

/-- The identity term-level rawRenaming.  Witnesses `TermRenaming Γ Γ id`
from `Ty.rename_identity`. -/
theorem TermRenaming.identity {m : Mode} {level scope : Nat} (Γ : Ctx m level scope) :
    TermRenaming Γ Γ Renaming.identity := fun i =>
  (Ty.rename_identity (varType Γ i)).symm

/-- **Term-level rawRenaming** — apply a type-level rawRenaming `ρ` (and the
position-consistency proof `ρt`) to a `Term`, producing a `Term` in
the target context with the renamed type.

The variable case uses the position-equality witness `ρt i` to align
the type after rawRenaming.  The `lam` / `appPi` / `pair` / `snd` cases
use the v1.7 substitution-rename commute lemmas.  Every cast is via
`▸` on a `Type`-valued `Term` motive, going through `Eq.rec` — no
match-compiler `noConfusion`, no propext. -/
def Term.rename {m scope scope'}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope'}
    (ρt : TermRenaming Γ Δ ρ) :
    {T : Ty level scope} → Term Γ T → Term Δ (T.rename ρ)
  | _, .var i => (ρt i) ▸ Term.var (ρ i)
  | _, .unit       => Term.unit
  | _, .lam (codomainType := codomainType) body =>
      Term.lam (codomainType := codomainType.rename ρ)
        ((Ty.rename_weaken_commute codomainType ρ) ▸
          (Term.rename (TermRenaming.lift ρt _) body))
  | _, .app f a =>
      Term.app (Term.rename ρt f) (Term.rename ρt a)
  | _, .lamPi (domainType := domainType) body =>
      Term.lamPi (Term.rename (TermRenaming.lift ρt domainType) body)
  | _, .appPi (domainType := domainType) (codomainType := codomainType) f a =>
      (Ty.subst0_rename_commute codomainType domainType ρ).symm ▸
        Term.appPi (Term.rename ρt f) (Term.rename ρt a)
  | _, .pair (firstType := firstType) (secondType := secondType)
             firstVal secondVal =>
      Term.pair (Term.rename ρt firstVal)
        ((Ty.subst0_rename_commute secondType firstType ρ) ▸
          (Term.rename ρt secondVal))
  | _, .fst p => Term.fst (Term.rename ρt p)
  | _, .snd (firstType := firstType) (secondType := secondType) p =>
      (Ty.subst0_rename_commute secondType firstType ρ).symm ▸
        Term.snd (Term.rename ρt p)
  | _, .boolTrue  => Term.boolTrue
  | _, .boolFalse => Term.boolFalse
  | _, .boolElim scrutinee thenBr elseBr =>
      Term.boolElim (Term.rename ρt scrutinee)
                    (Term.rename ρt thenBr)
                    (Term.rename ρt elseBr)
  | _, .natZero        => Term.natZero
  | _, .natSucc pred   => Term.natSucc (Term.rename ρt pred)
  | _, .natRec scrutinee zeroBranch succBranch =>
      Term.natRec (Term.rename ρt scrutinee)
                  (Term.rename ρt zeroBranch)
                  (Term.rename ρt succBranch)
  | _, .natElim scrutinee zeroBranch succBranch =>
      Term.natElim (Term.rename ρt scrutinee)
                   (Term.rename ρt zeroBranch)
                   (Term.rename ρt succBranch)
  | _, .listNil       => Term.listNil
  | _, .listCons hd tl =>
      Term.listCons (Term.rename ρt hd) (Term.rename ρt tl)
  | _, .listElim scrutinee nilBranch consBranch =>
      Term.listElim (Term.rename ρt scrutinee)
                    (Term.rename ρt nilBranch)
                    (Term.rename ρt consBranch)
  | _, .optionNone     => Term.optionNone
  | _, .optionSome v   => Term.optionSome (Term.rename ρt v)
  | _, .optionMatch scrutinee noneBranch someBranch =>
      Term.optionMatch (Term.rename ρt scrutinee)
                       (Term.rename ρt noneBranch)
                       (Term.rename ρt someBranch)
  | _, .eitherInl v    => Term.eitherInl (Term.rename ρt v)
  | _, .eitherInr v    => Term.eitherInr (Term.rename ρt v)
  | _, .eitherMatch scrutinee leftBranch rightBranch =>
      Term.eitherMatch (Term.rename ρt scrutinee)
                       (Term.rename ρt leftBranch)
                       (Term.rename ρt rightBranch)
  | _, .refl rawTerm => Term.refl (rawTerm.rename ρ)
  | _, .idJ baseCase witness =>
      Term.idJ (Term.rename ρt baseCase) (Term.rename ρt witness)

/-! ## Term-level weakening. -/

/-- The shift-by-one rawRenaming witnesses a `TermRenaming` from `Γ` to
`Γ.cons newType`: the position-equality `varType (Γ.cons newType) (Fin.succ i) = (varType Γ i).rename Renaming.weaken`
is `rfl` because both sides reduce to the same `Ty.rename` application
under the new `Ty.weaken := T.rename Renaming.weaken` defn. -/
theorem TermRenaming.weaken {m : Mode} {level scope : Nat}
    (Γ : Ctx m level scope) (newType : Ty level scope) :
    TermRenaming Γ (Γ.cons newType) Renaming.weaken := fun _ => rfl

/-- Weaken a term by extending its context with one fresh binding.
The result type is the original type weakened in lockstep, mirroring
the type-level `Ty.weaken`.  Implemented via `Term.rename` with the
shift-by-one rawRenaming. -/
def Term.weaken {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    (newType : Ty level scope) {T : Ty level scope} (term : Term Γ T) :
    Term (Γ.cons newType) T.weaken :=
  Term.rename (TermRenaming.weaken Γ newType) term

/-! ## `Term.toRaw` — the intrinsic-to-raw bridge.

Every well-typed intrinsic `Term context T` has a corresponding raw
`RawTerm scope` obtained by erasing all Ty-level annotations.  This
bridge witnesses that the intrinsic kernel embeds into the raw
syntax — half of the v2.2 architectural commitment that intrinsic
discipline and Term-mentioning identity types coexist in one kernel.

Defined here (rather than in the dedicated `ToRaw.lean`) so that
later modules — notably `TermSubst.singleton` — can reference
`Term.toRaw arg` in their type signatures, enabling the term-bearing
joint substitution `Subst.termSingleton T_arg (Term.toRaw arg)`. -/
def Term.toRaw {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    {T : Ty level scope} → Term context T → RawTerm scope
  | _, .var position    => RawTerm.var position
  | _, .unit            => RawTerm.unit
  | _, .lam body        => RawTerm.lam body.toRaw
  | _, .app function argument =>
      RawTerm.app function.toRaw argument.toRaw
  | _, .lamPi body      => RawTerm.lam body.toRaw
  | _, .appPi function argument =>
      RawTerm.app function.toRaw argument.toRaw
  | _, .pair firstVal secondVal =>
      RawTerm.pair firstVal.toRaw secondVal.toRaw
  | _, .fst pairTerm    => RawTerm.fst pairTerm.toRaw
  | _, .snd pairTerm    => RawTerm.snd pairTerm.toRaw
  | _, .boolTrue        => RawTerm.boolTrue
  | _, .boolFalse       => RawTerm.boolFalse
  | _, .boolElim scrutinee thenBranch elseBranch =>
      RawTerm.boolElim scrutinee.toRaw thenBranch.toRaw elseBranch.toRaw
  | _, .natZero         => RawTerm.natZero
  | _, .natSucc predecessor => RawTerm.natSucc predecessor.toRaw
  | _, .natElim scrutinee zeroBranch succBranch =>
      RawTerm.natElim scrutinee.toRaw zeroBranch.toRaw succBranch.toRaw
  | _, .natRec scrutinee zeroBranch succBranch =>
      RawTerm.natRec scrutinee.toRaw zeroBranch.toRaw succBranch.toRaw
  | _, .listNil         => RawTerm.listNil
  | _, .listCons head tail =>
      RawTerm.listCons head.toRaw tail.toRaw
  | _, .listElim scrutinee nilBranch consBranch =>
      RawTerm.listElim scrutinee.toRaw nilBranch.toRaw consBranch.toRaw
  | _, .optionNone      => RawTerm.optionNone
  | _, .optionSome value => RawTerm.optionSome value.toRaw
  | _, .optionMatch scrutinee noneBranch someBranch =>
      RawTerm.optionMatch scrutinee.toRaw noneBranch.toRaw someBranch.toRaw
  | _, .eitherInl value  => RawTerm.eitherInl value.toRaw
  | _, .eitherInr value  => RawTerm.eitherInr value.toRaw
  | _, .eitherMatch scrutinee leftBranch rightBranch =>
      RawTerm.eitherMatch scrutinee.toRaw leftBranch.toRaw rightBranch.toRaw
  | _, .refl rawTerm     =>
      RawTerm.refl rawTerm
  | _, .idJ baseCase witness =>
      RawTerm.idJ baseCase.toRaw witness.toRaw

end LeanFX.Syntax
