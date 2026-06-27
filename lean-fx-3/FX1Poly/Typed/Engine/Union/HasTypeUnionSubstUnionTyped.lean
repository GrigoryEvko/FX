import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.Union.HasTypeUnionWeakening
import FX1Poly.Typed.Cell.CellSubstitution

/-! # FX1Poly/Typed/HasTypeUnionSubstUnionTyped — the NATIVE substitution-context condition

The substitution analogue of the renaming-respects-context discipline (`HasTypeUnionWeakening`), but
where the renaming case carried an EQUALITY on lookups, the substitution case carries a TYPING: each
variable image `substitution index` must be typed at the substituted lookup.  `SubstUnionTyped` demands
those images be UNION-typed (`HasTypeUnion`) — the native condition.  It is strictly weaker than the
host `HasTypeUnion.SubstHostTyped` (every host image is a union image via `ofGrown`), and it is what the
NATIVE substitution master needs: the `var` arm reads its typing straight off the condition with no host
detour.

This condition + its binder-lift API live HERE — upstream of both substitution masters — so the host
substitution master (`HasTypeUnion.substRespectingContext`) and the union-image generalization
(`substRespectingContextUnionImages`) can both re-base on the native condition without an import cycle.
The one-binder lift `cons` resolves the fresh `var 0` through the NATIVE `HasTypeUnion.var` (its subject
`RawTermSubst.lift substitution 0` is defeq `variableCell 0`) and the shifted images through the native
weakening corollary `HasTypeUnion.weakenUnderBinding`.

## Zero-axiom

Each lemma is `Fin`-case analysis + the cell-substitution commutation `subst_lift_weaken_commute` + the
native `var` / `weakenUnderBinding`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditUnionSubstUnionTyped.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax FX1Poly.Modal

/-- **The native substitution-context condition.**  Every variable image is UNION-typed at the
substituted lookup type — the union mirror of `HasTypeUnion.SubstHostTyped`, weakening the requirement
from `HasTypeDescPi` to `HasTypeUnion` (every host image is a union image via `ofGrown`, so this
condition is strictly weaker, the one the substitution masters need). -/
abbrev HasTypeUnion.SubstUnionTyped {profile : PolyProfile} {sourceScope targetScope : Nat}
    (sourceContext : TypingContext profile sourceScope)
    (targetContext : TypingContext profile targetScope)
    (substitution : RawTermSubst sourceScope targetScope) : Prop :=
  ∀ index : Fin sourceScope,
    HasTypeUnion profile targetContext (substitution index)
      (RawTerm.subst substitution (sourceContext.lookup index))

/-- **The one-binder lift of the native substitution condition.**  If `substitution`'s images are
union-typed at the substituted source bindings, then its single lift's images are union-typed at the
context extended by `domainCode` (substituted).  `0` resolves to the fresh `var` (the NATIVE
`HasTypeUnion.var` — `RawTermSubst.lift substitution 0` is defeq `variableCell 0`), `k+1` to the base
union image weakened (`HasTypeUnion.weakenUnderBinding`). -/
theorem HasTypeUnion.SubstUnionTyped.cons {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (domainCode : RawTerm sourceScope) (substitution : RawTermSubst sourceScope targetScope)
    (condition : HasTypeUnion.SubstUnionTyped sourceContext targetContext substitution) :
    HasTypeUnion.SubstUnionTyped (sourceContext.cons domainCode)
      (targetContext.cons (RawTerm.subst substitution domainCode))
      (iterateLiftRaw substitution 1) := by
  intro index
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      show HasTypeUnion profile
        (targetContext.cons (RawTerm.subst substitution domainCode))
        (RawTermSubst.lift substitution ⟨0, indexBound⟩)
        (RawTerm.subst (RawTermSubst.lift substitution)
          ((sourceContext.cons domainCode).lookup ⟨0, indexBound⟩))
      rw [TypingContext.lookup_cons_zero, subst_lift_weaken_commute]
      exact HasTypeUnion.var
        (targetContext.cons (RawTerm.subst substitution domainCode))
        ⟨0, Nat.succ_pos _⟩
  | succ priorValue =>
      show HasTypeUnion profile
        (targetContext.cons (RawTerm.subst substitution domainCode))
        (RawTermSubst.lift substitution ⟨priorValue + 1, indexBound⟩)
        (RawTerm.subst (RawTermSubst.lift substitution)
          ((sourceContext.cons domainCode).lookup ⟨priorValue + 1, indexBound⟩))
      rw [TypingContext.lookup_cons_succ, subst_lift_weaken_commute]
      exact (condition ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderBinding
        (RawTerm.subst substitution domainCode)

/-- **The one-binder lift of the native substitution condition UNDER THE AFFINE DIMENSION LOCK
(`lockCons`).**  The `lockCons` twin of `SubstUnionTyped.cons`: `lockCons`'s `lookup` zero/successor
arms are byte-identical to `cons`'s (the lock mark is invisible to `lookup`), so the proof is the same
modulo the unfolders `lookup_lockCons_zero/succ` and the lock-aware weakening corollary
`HasTypeUnion.weakenUnderLockBinding`.  This is the substitution-side mirror the pathLam case of the
native substitution master needs once pathLam binds its dimension via `lockCons`. -/
theorem HasTypeUnion.SubstUnionTyped.lockCons {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (dimensionType : RawTerm sourceScope) (substitution : RawTermSubst sourceScope targetScope)
    (condition : HasTypeUnion.SubstUnionTyped sourceContext targetContext substitution) :
    HasTypeUnion.SubstUnionTyped (sourceContext.lockCons dimensionType)
      (targetContext.lockCons (RawTerm.subst substitution dimensionType))
      (iterateLiftRaw substitution 1) := by
  intro index
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      show HasTypeUnion profile
        (targetContext.lockCons (RawTerm.subst substitution dimensionType))
        (RawTermSubst.lift substitution ⟨0, indexBound⟩)
        (RawTerm.subst (RawTermSubst.lift substitution)
          ((sourceContext.lockCons dimensionType).lookup ⟨0, indexBound⟩))
      rw [TypingContext.lookup_lockCons_zero, subst_lift_weaken_commute]
      exact HasTypeUnion.var
        (targetContext.lockCons (RawTerm.subst substitution dimensionType))
        ⟨0, Nat.succ_pos _⟩
  | succ priorValue =>
      show HasTypeUnion profile
        (targetContext.lockCons (RawTerm.subst substitution dimensionType))
        (RawTermSubst.lift substitution ⟨priorValue + 1, indexBound⟩)
        (RawTerm.subst (RawTermSubst.lift substitution)
          ((sourceContext.lockCons dimensionType).lookup ⟨priorValue + 1, indexBound⟩))
      rw [TypingContext.lookup_lockCons_succ, subst_lift_weaken_commute]
      exact (condition ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderLockBinding
        (RawTerm.subst substitution dimensionType)

/-- **The two-binder lift of the native substitution condition** (the recursiveElim / idJ succ-branch
shape): the double lift of a union condition is a union condition at the context extended by the two
domains.  An iterate of `SubstUnionTyped.cons` — the union mirror of
`HasTypeUnion.SubstHostTyped.consTwice`. -/
theorem HasTypeUnion.SubstUnionTyped.consTwice {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (outerType : RawTerm sourceScope) (innerType : RawTerm (sourceScope + 1))
    {substitution : RawTermSubst sourceScope targetScope}
    (condition : HasTypeUnion.SubstUnionTyped sourceContext targetContext substitution) :
    HasTypeUnion.SubstUnionTyped ((sourceContext.cons outerType).cons innerType)
      ((targetContext.cons (RawTerm.subst substitution outerType)).cons
        (RawTerm.subst (iterateLiftRaw substitution 1) innerType))
      (iterateLiftRaw substitution 2) :=
  HasTypeUnion.SubstUnionTyped.cons innerType (iterateLiftRaw substitution 1)
    (HasTypeUnion.SubstUnionTyped.cons outerType substitution condition)

end FX1Poly.Typed
