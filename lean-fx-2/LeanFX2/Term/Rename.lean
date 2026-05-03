import LeanFX2.Term.ToRaw

/-! # Term/Rename — typed termRenaming on Term.

`Term.rename` lifts a raw `RawRenaming` on RawTerm scopes to a typed
termRenaming on the dependently-typed Term inductive.  The raw index of the
result is automatically `rawSrc.rename rho` (no proof obligation —
type-index propagation handles it via per-ctor structural pinning in
the Term inductive).

## TermRenaming

A `TermRenaming sourceCtx targetCtx rho` is the typed companion to a
`RawRenaming sourceScope targetScope`: it asserts that the termRenaming
preserves variable types under the two contexts.  Concretely, looking
up position `rho i` in `targetCtx` gives the rename of position `i`'s
type from `sourceCtx`.

Two operations:
* `TermRenaming.lift termRenaming newSourceType` — extend under one binder
* `TermRenaming.weakenStep context newType` — the canonical weakening
  TermRenaming for adding one binding to the head

## Cast discipline

The non-trivial cases (`var`, `lam`, `lamPi`, `appPi`, `pair`, `snd`)
need type-equality casts to align the recursive call's type with the
expected ctor argument shape.  Each cast uses `▸` on a foundation lemma:

* `var` — cast via `(termRenaming i).symm` to align `varType` lookup
* `lam` / `lamPi` — cast via `Ty.weaken_rename_commute` to align body type
* `appPi` — cast via `Ty.subst0_rename_commute` to align β-redex result
* `pair` — cast via `Ty.subst0_rename_commute` for the second component
* `snd` — cast via `Ty.subst0_rename_commute` for the projection result

All casts on `Term`-typed values are axiom-free (verified via
Smoke/AuditCast — recursor-based `Eq.rec` + reducible motive).
-/

namespace LeanFX2

/-! ## TermRenaming -/

/-- A typed termRenaming relates two contexts via a raw termRenaming, requiring
that variable types align: looking up position `rho i` in target gives
the rename of position `i`'s type from source. -/
def TermRenaming {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    (sourceCtx : Ctx mode level sourceScope)
    (targetCtx : Ctx mode level targetScope)
    (rho : RawRenaming sourceScope targetScope) : Prop :=
  ∀ position, varType targetCtx (rho position) =
              (varType sourceCtx position).rename rho

/-- Lift a TermRenaming under a binder.  Both contexts gain one
binding; the target's binding type is the renamed source binding.
The new positions agree because:
* Position 0: `(newSourceType.rename rho).weaken =
              newSourceType.weaken.rename rho.lift` (Ty.weaken_rename_commute)
* Position k+1: `(varType target (rho ⟨k, _⟩)).weaken` agrees with
                `((varType source ⟨k, _⟩).rename rho).weaken` via the
                termRenaming hypothesis at k, modulo Ty.weaken_rename_commute. -/
theorem TermRenaming.lift
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (newSourceType : Ty level sourceScope) :
    TermRenaming (sourceCtx.cons newSourceType)
                 (targetCtx.cons (newSourceType.rename rho))
                 rho.lift := by
  intro position
  cases position with
  | mk val isLt =>
    cases val with
    | zero =>
      show (newSourceType.rename rho).weaken =
           newSourceType.weaken.rename rho.lift
      exact (Ty.weaken_rename_commute rho newSourceType).symm
    | succ k =>
      show (varType targetCtx (rho ⟨k, Nat.lt_of_succ_lt_succ isLt⟩)).weaken =
           ((varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ isLt⟩).weaken).rename rho.lift
      rw [termRenaming ⟨k, Nat.lt_of_succ_lt_succ isLt⟩,
          Ty.weaken_rename_commute rho (varType sourceCtx _)]

/-- The canonical weakening TermRenaming: adding one binding to the
head of a context, with `RawRenaming.weaken` shifting all positions
up by one.  Pure rfl per `varType`'s second arm. -/
theorem TermRenaming.weakenStep {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope) (newType : Ty level scope) :
    TermRenaming context (context.cons newType) RawRenaming.weaken :=
  fun _ => rfl

/-! ## Term.rename -/

/-- Apply a typed termRenaming to a typed term.  The output's raw index is
automatically `raw.rename rho` (the Term inductive's raw index pins the
shape per ctor — recursive calls supply the renamed sub-raws and Lean
elaborates the result raw structurally).

This is a 29-case structural recursion mirroring the Term inductive.
Type-equality casts via `▸` use the Phase 1.D-foundation and 1.E
foundation lemmas to align the recursive call's result with the
expected ctor argument shape. -/
def Term.rename {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho) :
    ∀ {someType : Ty level sourceScope} {raw : RawTerm sourceScope},
      Term sourceCtx someType raw →
      Term targetCtx (someType.rename rho) (raw.rename rho)
  -- Variable: cast via the termRenaming's equation at this position.
  | _, _, .var position =>
      (termRenaming position).symm ▸ Term.var (rho position)
  -- Unit: trivial.
  | _, _, .unit => Term.unit
  -- Non-dep arrow lam: body's type is codomain.weaken; cast to
  -- (codomain.rename rho).weaken via Ty.weaken_rename_commute.
  | _, _, .lam (codomainType := codomainType) body =>
      Term.lam (Ty.weaken_rename_commute rho codomainType ▸
                Term.rename (termRenaming.lift _) body)
  -- Non-dep arrow app: result type Ty.arrow renames automatically.
  | _, _, .app functionTerm argumentTerm =>
      Term.app (Term.rename termRenaming functionTerm)
               (Term.rename termRenaming argumentTerm)
  -- Dep Π lam: body's type is just codomainType (no weaken); direct.
  | _, _, .lamPi body =>
      Term.lamPi (Term.rename (termRenaming.lift _) body)
  -- Dep Π app: result type uses subst0; cast via Ty.subst0_rename_commute.
  | _, _, .appPi (codomainType := codomainType) (domainType := domainType)
                 (argumentRaw := argumentRaw) functionTerm argumentTerm =>
      (Ty.subst0_rename_commute codomainType domainType argumentRaw rho).symm ▸
        Term.appPi (Term.rename termRenaming functionTerm)
                   (Term.rename termRenaming argumentTerm)
  -- Σ pair: second value's type uses subst0; cast.
  | _, _, .pair (secondType := secondType) (firstType := firstType)
                (firstRaw := firstRaw) firstValue secondValue =>
      Term.pair (Term.rename termRenaming firstValue)
                (Ty.subst0_rename_commute secondType firstType firstRaw rho ▸
                  Term.rename termRenaming secondValue)
  -- Σ fst: result is firstType; direct.
  | _, _, .fst pairTerm => Term.fst (Term.rename termRenaming pairTerm)
  -- Σ snd: result type uses subst0 with RawTerm.fst pairRaw; cast.
  | _, _, .snd (secondType := secondType) (firstType := firstType)
               (pairRaw := pairRaw) pairTerm =>
      (Ty.subst0_rename_commute secondType firstType
        (RawTerm.fst pairRaw) rho).symm ▸
        Term.snd (Term.rename termRenaming pairTerm)
  -- Booleans: trivial.
  | _, _, .boolTrue => Term.boolTrue
  | _, _, .boolFalse => Term.boolFalse
  | _, _, .boolElim scrutinee thenBranch elseBranch =>
      Term.boolElim (Term.rename termRenaming scrutinee)
                    (Term.rename termRenaming thenBranch)
                    (Term.rename termRenaming elseBranch)
  -- Naturals: trivial constants + structural cong.
  | _, _, .natZero => Term.natZero
  | _, _, .natSucc predecessor =>
      Term.natSucc (Term.rename termRenaming predecessor)
  | _, _, .natElim scrutinee zeroBranch succBranch =>
      Term.natElim (Term.rename termRenaming scrutinee)
                   (Term.rename termRenaming zeroBranch)
                   (Term.rename termRenaming succBranch)
  | _, _, .natRec scrutinee zeroBranch succBranch =>
      Term.natRec (Term.rename termRenaming scrutinee)
                  (Term.rename termRenaming zeroBranch)
                  (Term.rename termRenaming succBranch)
  -- Lists: structural.
  | _, _, .listNil => Term.listNil
  | _, _, .listCons headTerm tailTerm =>
      Term.listCons (Term.rename termRenaming headTerm)
                    (Term.rename termRenaming tailTerm)
  | _, _, .listElim scrutinee nilBranch consBranch =>
      Term.listElim (Term.rename termRenaming scrutinee)
                    (Term.rename termRenaming nilBranch)
                    (Term.rename termRenaming consBranch)
  -- Options: structural.
  | _, _, .optionNone => Term.optionNone
  | _, _, .optionSome valueTerm =>
      Term.optionSome (Term.rename termRenaming valueTerm)
  | _, _, .optionMatch scrutinee noneBranch someBranch =>
      Term.optionMatch (Term.rename termRenaming scrutinee)
                       (Term.rename termRenaming noneBranch)
                       (Term.rename termRenaming someBranch)
  -- Eithers: structural.
  | _, _, .eitherInl valueTerm =>
      Term.eitherInl (Term.rename termRenaming valueTerm)
  | _, _, .eitherInr valueTerm =>
      Term.eitherInr (Term.rename termRenaming valueTerm)
  | _, _, .eitherMatch scrutinee leftBranch rightBranch =>
      Term.eitherMatch (Term.rename termRenaming scrutinee)
                       (Term.rename termRenaming leftBranch)
                       (Term.rename termRenaming rightBranch)
  -- Identity types.  refl carries explicit raw witness.
  | _, _, .refl carrier rawWitness =>
      Term.refl (carrier.rename rho) (rawWitness.rename rho)
  | _, _, .idJ baseCase witness =>
      Term.idJ (Term.rename termRenaming baseCase)
               (Term.rename termRenaming witness)
  -- Modal: Layer 1 scaffolding preserves innerType.
  | _, _, .modIntro innerTerm =>
      Term.modIntro (Term.rename termRenaming innerTerm)
  | _, _, .modElim innerTerm =>
      Term.modElim (Term.rename termRenaming innerTerm)
  | _, _, .subsume innerTerm =>
      Term.subsume (Term.rename termRenaming innerTerm)
  -- Universe-code: scope-polymorphic.  Both `Ty.universe outerLevel
  -- levelEq` and `RawTerm.universeCode innerLevel.toNat` rename to
  -- themselves (no scope-dependent payload), so the `someType.rename
  -- rho` and `raw.rename rho` results match the ctor's expected types
  -- definitionally.
  | _, _, .universeCode innerLevel outerLevel cumulOk levelEq =>
      Term.universeCode innerLevel outerLevel cumulOk levelEq
  -- Cumul-up (REAL cumul ctor): the inner Term lives at scope 0, so
  -- it is invariant under any renaming on the outer scope.  We just
  -- pass `lowerTerm` through unchanged and reconstruct the cumulUp
  -- ctor at the new target scope (the output context uses the new
  -- scope, the inner context stays at scope 0).  Both sides project
  -- to `RawTerm.universeCode innerLevel.toNat`, identical at any
  -- scope, so no cast is needed for the raw axis.  The output type
  -- `Ty.universe higherLevel rfl` renames to itself.
  | _, _, .cumulUp innerLevel lowerLevel higherLevel
                   cumulOkLow cumulOkHigh cumulMonotone
                   levelEqLow levelEqHigh lowerTerm =>
      Term.cumulUp (ctxHigh := targetCtx)
                   innerLevel lowerLevel higherLevel
                   cumulOkLow cumulOkHigh cumulMonotone
                   levelEqLow levelEqHigh lowerTerm

/-! ## Term.weaken — convenience wrapper -/

/-- Single-binder weakening on a typed term: lift through one new
binder via the canonical weakening TermRenaming. -/
@[reducible] def Term.weaken {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {someType : Ty level scope}
    {raw : RawTerm scope} (newType : Ty level scope)
    (term : Term context someType raw) :
    Term (context.cons newType) someType.weaken raw.weaken :=
  Term.rename (TermRenaming.weakenStep context newType) term

end LeanFX2
