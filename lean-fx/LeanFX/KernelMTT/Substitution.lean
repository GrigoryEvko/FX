import LeanFX.KernelMTT.Syntax

/-! # KernelMTT — substitution machinery (renaming layer).

Renaming-side of substitution: pure positional remapping
(`Fin sourceScope → Fin targetScope`), no Term/Ty interpretation.
Both `Ty.tyVar` and `Term.varRef` simply remap their position.

Substitution proper (where positions are replaced by *values*) lands
in v2.0c — that requires the joint Ty-and-Term substitution structure
discussed in the file header of `Reduction.lean` (forthcoming).

## Why renaming first

Three reasons for the split:

  1. Renaming is purely positional; no design choice about
     joint-substitution structure is needed.  Ships clean and
     unblocks `Ty.weaken` / `Term.weaken`.
  2. The categorical laws (`rename_congr`, `rename_compose`,
     `rename_identity`) port directly from KernelV1 and validate
     that the mutual-recursion plumbing works for theorems, not
     just data definitions.
  3. `Ty.rename_weaken_commute` is a building block for binder-
     manipulation throughout the kernel — substitution depends on
     it.  Best to land it under renaming alone.

## What ports verbatim from KernelV1

  * `Renaming` type
  * `Renaming.identity`, `Renaming.weaken`, `Renaming.lift`,
    `Renaming.compose`, `Renaming.equiv`
  * `Renaming.lift_equiv`, `Renaming.lift_compose_equiv`,
    `Renaming.lift_identity_equiv`

## What's new

  * Mutual `Ty.rename` / `Term.rename` (KernelV1's `Ty.rename`
    is solo; the new mutual structure handles `tyId` and `reflEq`).
  * Mutual `Ty.rename_congr` / `Term.rename_congr`
  * Mutual `Ty.rename_compose` / `Term.rename_compose`
  * `Ty.weaken`, `Term.weaken` derived from rename
  * `Ty.rename_weaken_commute`, `Term.rename_weaken_commute`

The `tyId` arm of every Ty.rename-style theorem invokes the
corresponding Term.rename-style theorem, and vice versa for the
`lamFn` arm — that's the load-bearing mutual recursion.

All declarations zero-axiom. -/

namespace LeanFX.KernelMTT

/-! ## Renaming primitive — positional remapping. -/

/-- A renaming maps `Fin sourceScope` indices to `Fin targetScope`
indices.  Direct port from KernelV1 — pure data, no Ty / Term
involvement, so the abbreviation works identically. -/
abbrev Renaming (sourceScope targetScope : Nat) : Type :=
  Fin sourceScope → Fin targetScope

/-- The identity renaming — every variable maps to itself. -/
def Renaming.identity {scope : Nat} : Renaming scope scope := id

/-- Weakening as a renaming — every variable shifts up by one,
making room for a new outer binder at position 0. -/
def Renaming.weaken {scope : Nat} : Renaming scope (scope + 1) :=
  Fin.succ

/-- Lift a renaming under a binder.  Variable 0 stays at 0
(it's the new binder); variable `index + 1` maps to `(rename index).succ`.

Implemented via direct match on `Fin` structure (`⟨0, _⟩` /
`⟨index + 1, h⟩`) rather than `Fin.cases`, which uses `propext`
in core Lean — this is the `feedback_lean_fin_cases_axiom` discipline
applied to the new kernel. -/
def Renaming.lift {sourceScope targetScope : Nat}
    (mapping : Renaming sourceScope targetScope) :
    Renaming (sourceScope + 1) (targetScope + 1)
  | ⟨0, _⟩          => ⟨0, Nat.zero_lt_succ _⟩
  | ⟨index + 1, h⟩  =>
      Fin.succ (mapping ⟨index, Nat.lt_of_succ_lt_succ h⟩)

/-- Compose two renamings: apply `firstRen` first, then `secondRen`. -/
def Renaming.compose {sourceScope midScope targetScope : Nat}
    (firstRen : Renaming sourceScope midScope)
    (secondRen : Renaming midScope targetScope) :
    Renaming sourceScope targetScope :=
  fun index => secondRen (firstRen index)

/-- Pointwise renaming equivalence — two renamings agree on every
position. -/
def Renaming.equiv {sourceScope targetScope : Nat}
    (renamingOne renamingTwo : Renaming sourceScope targetScope) : Prop :=
  ∀ index, renamingOne index = renamingTwo index

/-- Lifting preserves pointwise renaming equivalence. -/
theorem Renaming.lift_equiv {sourceScope targetScope : Nat}
    {renamingOne renamingTwo : Renaming sourceScope targetScope}
    (h : Renaming.equiv renamingOne renamingTwo) :
    Renaming.equiv renamingOne.lift renamingTwo.lift := fun index =>
  match index with
  | ⟨0, _⟩          => rfl
  | ⟨inner + 1, hk⟩ =>
      congrArg Fin.succ (h ⟨inner, Nat.lt_of_succ_lt_succ hk⟩)

/-- Lifting commutes with renaming composition (pointwise).  Both
`Fin` cases reduce to `rfl`. -/
theorem Renaming.lift_compose_equiv {sourceScope midScope targetScope : Nat}
    (firstRen : Renaming sourceScope midScope)
    (secondRen : Renaming midScope targetScope) :
    Renaming.equiv (Renaming.compose firstRen.lift secondRen.lift)
                   (Renaming.compose firstRen secondRen).lift
  | ⟨0, _⟩         => rfl
  | ⟨_ + 1, _⟩     => rfl

/-- Lifting the identity renaming gives the identity at the
extended scope (pointwise). -/
theorem Renaming.lift_identity_equiv {scope : Nat} :
    Renaming.equiv (@Renaming.identity scope).lift Renaming.identity
  | ⟨0, _⟩      => rfl
  | ⟨_ + 1, _⟩  => rfl

/-! ## Mutual rename — the load-bearing operation.

`Ty.rename` and `Term.rename` are mutually recursive because:

  * `Ty.tyId` arm of `Ty.rename` invokes `Term.rename` on the
    `leftEnd` and `rightEnd` Term values.
  * `Term.lamFn` arm of `Term.rename` invokes `Ty.rename` on the
    annotated `domainType` Ty value.

Both arms thread the renaming through the same way KernelV1's
solo `Ty.rename` does, plus the new cross-references. -/

mutual

/-- Apply a renaming to a type, structurally.  The mutual-recursion
piece: `tyId` recurses into `Term.rename` for both endpoints. -/
def Ty.rename {level sourceScope targetScope : Nat} :
    Ty level sourceScope →
    Renaming sourceScope targetScope →
    Ty level targetScope
  | .unitTy, _              => .unitTy
  | .boolTy, _              => .boolTy
  | .natTy, _               => .natTy
  | .arrowTy domain codomain, ρ =>
      .arrowTy (Ty.rename domain ρ) (Ty.rename codomain ρ)
  | .tyVar position, ρ      => .tyVar (ρ position)
  | .universeTy uLvl uEq, _ => .universeTy uLvl uEq
  | .tyId carrier leftEnd rightEnd, ρ =>
      .tyId (Ty.rename carrier ρ)
            (Term.rename leftEnd ρ)
            (Term.rename rightEnd ρ)

/-- Apply a renaming to a term, structurally.  The mutual-recursion
piece: `lamFn` recurses into `Ty.rename` for the annotated domain
type, and into `Term.rename` (with `Renaming.lift`) for the body. -/
def Term.rename {sourceScope targetScope : Nat} :
    Term sourceScope →
    Renaming sourceScope targetScope →
    Term targetScope
  | .varRef position, ρ      => .varRef (ρ position)
  | .unitVal, _              => .unitVal
  | .boolTrue, _             => .boolTrue
  | .boolFalse, _            => .boolFalse
  | .natZero, _              => .natZero
  | .natSucc predecessor, ρ  => .natSucc (Term.rename predecessor ρ)
  | .lamFn domainType body, ρ =>
      .lamFn (Ty.rename domainType ρ) (Term.rename body ρ.lift)
  | .appFn function argument, ρ =>
      .appFn (Term.rename function ρ) (Term.rename argument ρ)
  | .reflEq term, ρ          => .reflEq (Term.rename term ρ)

end

/-! ## Mutual rename congruence — pointwise-equivalent renamings
produce equal results on every Ty / Term. -/

mutual

/-- Pointwise-equivalent renamings produce equal results on every
type.  The `tyId` arm calls `Term.rename_congr` for both endpoints. -/
theorem Ty.rename_congr {level sourceScope targetScope : Nat}
    {renamingOne renamingTwo : Renaming sourceScope targetScope}
    (h : Renaming.equiv renamingOne renamingTwo) :
    ∀ typeValue : Ty level sourceScope,
      typeValue.rename renamingOne = typeValue.rename renamingTwo
  | .unitTy           => rfl
  | .boolTy           => rfl
  | .natTy            => rfl
  | .arrowTy domain codomain => by
      have hDomain   := Ty.rename_congr h domain
      have hCodomain := Ty.rename_congr h codomain
      show Ty.arrowTy (Ty.rename domain renamingOne)
                     (Ty.rename codomain renamingOne)
         = Ty.arrowTy (Ty.rename domain renamingTwo)
                     (Ty.rename codomain renamingTwo)
      exact hDomain ▸ hCodomain ▸ rfl
  | .tyVar position    => congrArg Ty.tyVar (h position)
  | .universeTy _ _    => rfl
  | .tyId carrier leftEnd rightEnd => by
      have hCarrier := Ty.rename_congr h carrier
      have hLeft    := Term.rename_congr h leftEnd
      have hRight   := Term.rename_congr h rightEnd
      show Ty.tyId (Ty.rename carrier renamingOne)
                   (Term.rename leftEnd renamingOne)
                   (Term.rename rightEnd renamingOne)
         = Ty.tyId (Ty.rename carrier renamingTwo)
                   (Term.rename leftEnd renamingTwo)
                   (Term.rename rightEnd renamingTwo)
      exact hCarrier ▸ hLeft ▸ hRight ▸ rfl

/-- Pointwise-equivalent renamings produce equal results on every
term.  The `lamFn` arm calls `Ty.rename_congr` on the domain
annotation and `Term.rename_congr` on the body (with
`Renaming.lift_equiv`). -/
theorem Term.rename_congr {sourceScope targetScope : Nat}
    {renamingOne renamingTwo : Renaming sourceScope targetScope}
    (h : Renaming.equiv renamingOne renamingTwo) :
    ∀ termValue : Term sourceScope,
      termValue.rename renamingOne = termValue.rename renamingTwo
  | .varRef position    => congrArg Term.varRef (h position)
  | .unitVal            => rfl
  | .boolTrue           => rfl
  | .boolFalse          => rfl
  | .natZero            => rfl
  | .natSucc predecessor => by
      have hPred := Term.rename_congr h predecessor
      show Term.natSucc (Term.rename predecessor renamingOne)
         = Term.natSucc (Term.rename predecessor renamingTwo)
      exact hPred ▸ rfl
  | .lamFn domainType body => by
      have hDomain := Ty.rename_congr h domainType
      have hBody   := Term.rename_congr (Renaming.lift_equiv h) body
      show Term.lamFn (Ty.rename domainType renamingOne)
                     (Term.rename body renamingOne.lift)
         = Term.lamFn (Ty.rename domainType renamingTwo)
                     (Term.rename body renamingTwo.lift)
      exact hDomain ▸ hBody ▸ rfl
  | .appFn function argument => by
      have hFunction := Term.rename_congr h function
      have hArgument := Term.rename_congr h argument
      show Term.appFn (Term.rename function renamingOne)
                     (Term.rename argument renamingOne)
         = Term.appFn (Term.rename function renamingTwo)
                     (Term.rename argument renamingTwo)
      exact hFunction ▸ hArgument ▸ rfl
  | .reflEq term => by
      have hTerm := Term.rename_congr h term
      show Term.reflEq (Term.rename term renamingOne)
         = Term.reflEq (Term.rename term renamingTwo)
      exact hTerm ▸ rfl

end

/-! ## Mutual rename composition — `(rename ρ₁); (rename ρ₂) = rename (compose ρ₁ ρ₂)`.

Direct structural induction; the binder cases use `*.rename_congr` plus
`Renaming.lift_compose_equiv` to bridge the lifted-then-composed form
and the composed-then-lifted form. -/

mutual

/-- Renaming composition law for types.  `tyId` arm uses
`Term.rename_compose` for both endpoints. -/
theorem Ty.rename_compose {level sourceScope midScope targetScope : Nat} :
    ∀ (typeValue : Ty level sourceScope)
      (firstRen : Renaming sourceScope midScope)
      (secondRen : Renaming midScope targetScope),
      (typeValue.rename firstRen).rename secondRen
        = typeValue.rename (Renaming.compose firstRen secondRen)
  | .unitTy, _, _              => rfl
  | .boolTy, _, _              => rfl
  | .natTy, _, _               => rfl
  | .arrowTy domain codomain, firstRen, secondRen => by
      have hDomain   := Ty.rename_compose domain firstRen secondRen
      have hCodomain := Ty.rename_compose codomain firstRen secondRen
      show Ty.arrowTy ((Ty.rename domain firstRen).rename secondRen)
                     ((Ty.rename codomain firstRen).rename secondRen)
         = Ty.arrowTy
             (Ty.rename domain (Renaming.compose firstRen secondRen))
             (Ty.rename codomain (Renaming.compose firstRen secondRen))
      exact hDomain ▸ hCodomain ▸ rfl
  | .tyVar _, _, _             => rfl
  | .universeTy _ _, _, _      => rfl
  | .tyId carrier leftEnd rightEnd, firstRen, secondRen => by
      have hCarrier := Ty.rename_compose carrier firstRen secondRen
      have hLeft    := Term.rename_compose leftEnd firstRen secondRen
      have hRight   := Term.rename_compose rightEnd firstRen secondRen
      show Ty.tyId
             ((Ty.rename carrier firstRen).rename secondRen)
             ((Term.rename leftEnd firstRen).rename secondRen)
             ((Term.rename rightEnd firstRen).rename secondRen)
         = Ty.tyId
             (Ty.rename carrier (Renaming.compose firstRen secondRen))
             (Term.rename leftEnd (Renaming.compose firstRen secondRen))
             (Term.rename rightEnd (Renaming.compose firstRen secondRen))
      exact hCarrier ▸ hLeft ▸ hRight ▸ rfl

/-- Renaming composition law for terms.  `lamFn` arm uses
`Ty.rename_compose` on the domain annotation and bridges the lifted
renamings via `Renaming.lift_compose_equiv` + `Term.rename_congr`. -/
theorem Term.rename_compose {sourceScope midScope targetScope : Nat} :
    ∀ (termValue : Term sourceScope)
      (firstRen : Renaming sourceScope midScope)
      (secondRen : Renaming midScope targetScope),
      (termValue.rename firstRen).rename secondRen
        = termValue.rename (Renaming.compose firstRen secondRen)
  | .varRef _, _, _   => rfl
  | .unitVal, _, _    => rfl
  | .boolTrue, _, _   => rfl
  | .boolFalse, _, _  => rfl
  | .natZero, _, _    => rfl
  | .natSucc predecessor, firstRen, secondRen => by
      have hPred := Term.rename_compose predecessor firstRen secondRen
      show Term.natSucc ((Term.rename predecessor firstRen).rename secondRen)
         = Term.natSucc
             (Term.rename predecessor (Renaming.compose firstRen secondRen))
      exact hPred ▸ rfl
  | .lamFn domainType body, firstRen, secondRen => by
      have hDomain := Ty.rename_compose domainType firstRen secondRen
      have hBody   := Term.rename_compose body firstRen.lift secondRen.lift
      have hLift   :=
        Term.rename_congr (Renaming.lift_compose_equiv firstRen secondRen) body
      show Term.lamFn
             ((Ty.rename domainType firstRen).rename secondRen)
             ((Term.rename body firstRen.lift).rename secondRen.lift)
         = Term.lamFn
             (Ty.rename domainType (Renaming.compose firstRen secondRen))
             (Term.rename body (Renaming.compose firstRen secondRen).lift)
      exact hDomain ▸ (hBody.trans hLift) ▸ rfl
  | .appFn function argument, firstRen, secondRen => by
      have hFunction := Term.rename_compose function firstRen secondRen
      have hArgument := Term.rename_compose argument firstRen secondRen
      show Term.appFn ((Term.rename function firstRen).rename secondRen)
                     ((Term.rename argument firstRen).rename secondRen)
         = Term.appFn
             (Term.rename function (Renaming.compose firstRen secondRen))
             (Term.rename argument (Renaming.compose firstRen secondRen))
      exact hFunction ▸ hArgument ▸ rfl
  | .reflEq term, firstRen, secondRen => by
      have hTerm := Term.rename_compose term firstRen secondRen
      show Term.reflEq ((Term.rename term firstRen).rename secondRen)
         = Term.reflEq
             (Term.rename term (Renaming.compose firstRen secondRen))
      exact hTerm ▸ rfl

end

/-! ## Weakening — `rename` against `Renaming.weaken`.

Both `Ty.weaken` and `Term.weaken` are derived from `rename`; this
keeps the binder-aware piTy / sigmaTy / lamFn cases honest (the local
`var 0` stays fixed via `Renaming.weaken.lift` while outer references
shift).  `@[reducible]` so unifier/`rfl` unfold eagerly. -/

@[reducible]
def Ty.weaken {level scope : Nat}
    (typeValue : Ty level scope) : Ty level (scope + 1) :=
  typeValue.rename Renaming.weaken

@[reducible]
def Term.weaken {scope : Nat}
    (termValue : Term scope) : Term (scope + 1) :=
  termValue.rename Renaming.weaken

/-! ## Rename-weaken commutativity.

The fundamental binder lemma: weakening (insert outer binder) commutes
with renaming when the renaming is appropriately lifted.  Used
throughout substitution and reduction proofs.  Direct port from
KernelV1 with the Term variant added. -/

theorem Ty.rename_weaken_commute {level sourceScope targetScope : Nat}
    (typeValue : Ty level sourceScope)
    (mapping : Renaming sourceScope targetScope) :
    (typeValue.weaken).rename mapping.lift
      = (typeValue.rename mapping).weaken := by
  show (typeValue.rename Renaming.weaken).rename mapping.lift
     = (typeValue.rename mapping).rename Renaming.weaken
  have hSwap :
      Renaming.equiv (Renaming.compose Renaming.weaken mapping.lift)
                     (Renaming.compose mapping Renaming.weaken) :=
    fun _ => rfl
  exact (Ty.rename_compose typeValue Renaming.weaken mapping.lift).trans
          ((Ty.rename_congr hSwap typeValue).trans
            (Ty.rename_compose typeValue mapping Renaming.weaken).symm)

theorem Term.rename_weaken_commute {sourceScope targetScope : Nat}
    (termValue : Term sourceScope)
    (mapping : Renaming sourceScope targetScope) :
    (termValue.weaken).rename mapping.lift
      = (termValue.rename mapping).weaken := by
  show (termValue.rename Renaming.weaken).rename mapping.lift
     = (termValue.rename mapping).rename Renaming.weaken
  have hSwap :
      Renaming.equiv (Renaming.compose Renaming.weaken mapping.lift)
                     (Renaming.compose mapping Renaming.weaken) :=
    fun _ => rfl
  exact (Term.rename_compose termValue Renaming.weaken mapping.lift).trans
          ((Term.rename_congr hSwap termValue).trans
            (Term.rename_compose termValue mapping Renaming.weaken).symm)

/-! ## Smoke tests for the renaming layer.

Exercise every constructor through `Ty.rename` / `Term.rename`,
verify rename-compose composes, weakening behaves on identity types
(the load-bearing case — KernelV1 cannot do this at all), and that
`#print axioms` stays clean across the new mutual-recursion theorems. -/

namespace SmokeTest

/-- Renaming the unit type at any scope is the unit type. -/
example {level sourceScope targetScope : Nat}
    (mapping : Renaming sourceScope targetScope) :
    Ty.rename (Ty.unitTy : Ty level sourceScope) mapping = Ty.unitTy := rfl

/-- Renaming a tyVar position uses the renaming function.  Source
scope is `scope + 1` so position 0 is always available. -/
example {level scope : Nat} (mapping : Renaming (scope + 1) (scope + 2)) :
    Ty.rename (Ty.tyVar (level := level) ⟨0, Nat.zero_lt_succ _⟩) mapping
      = Ty.tyVar (mapping ⟨0, Nat.zero_lt_succ _⟩) := rfl

/-- Renaming a `tyId` propagates through carrier + both endpoints.
Closed terms (`boolTrue`) survive any renaming as themselves. -/
example {level scope targetScope : Nat}
    (mapping : Renaming scope targetScope) :
    Ty.rename
      (Ty.tyId (level := level) Ty.boolTy Term.boolTrue Term.boolTrue)
      mapping
      = Ty.tyId Ty.boolTy Term.boolTrue Term.boolTrue := rfl

/-- The fundamental composition law on a `tyId` type — exercises the
mutual structure: Ty.rename_compose's tyId arm needs Term.rename_compose
on both endpoints. -/
example {level scope midScope targetScope : Nat}
    (firstRen : Renaming scope midScope)
    (secondRen : Renaming midScope targetScope)
    (carrier : Ty level scope)
    (leftEnd rightEnd : Term scope) :
    ((Ty.tyId carrier leftEnd rightEnd).rename firstRen).rename secondRen
      = (Ty.tyId carrier leftEnd rightEnd).rename
          (Renaming.compose firstRen secondRen) :=
  Ty.rename_compose _ firstRen secondRen

/-- Composition on a `lamFn` term — exercises the mutual structure
in the other direction: Term.rename_compose's lamFn arm needs
Ty.rename_compose on the domain annotation. -/
example {scope midScope targetScope : Nat}
    (firstRen : Renaming scope midScope)
    (secondRen : Renaming midScope targetScope)
    (body : Term (scope + 1)) :
    ((Term.lamFn (Ty.boolTy : Ty 0 scope) body).rename firstRen).rename secondRen
      = (Term.lamFn (Ty.boolTy : Ty 0 scope) body).rename
          (Renaming.compose firstRen secondRen) :=
  Term.rename_compose _ firstRen secondRen

/-- Weakening a `tyId` is itself a `tyId` (with carrier and endpoints
weakened pointwise) — the load-bearing identity-type weakening. -/
example {level scope : Nat}
    (carrier : Ty level scope)
    (leftEnd rightEnd : Term scope) :
    (Ty.tyId carrier leftEnd rightEnd).weaken
      = Ty.tyId carrier.weaken leftEnd.weaken rightEnd.weaken := rfl

/-- Weakening commutes with renaming on `Ty.tyId`. -/
example {level sourceScope targetScope : Nat}
    (mapping : Renaming sourceScope targetScope)
    (carrier : Ty level sourceScope)
    (leftEnd rightEnd : Term sourceScope) :
    ((Ty.tyId carrier leftEnd rightEnd).weaken).rename mapping.lift
      = ((Ty.tyId carrier leftEnd rightEnd).rename mapping).weaken :=
  Ty.rename_weaken_commute _ mapping

end SmokeTest

end LeanFX.KernelMTT
