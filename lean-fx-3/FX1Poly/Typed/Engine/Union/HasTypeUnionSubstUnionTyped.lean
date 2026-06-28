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

/-- **The native substitution-context condition (A1-RESTRICT, single-goal, MODALITY-GENERAL #1795).**  Every
variable accessible at a USE-MODALITY has its image UNION-typed at the substituted lookup type — the union
mirror of `HasTypeUnion.SubstHostTyped`, weakening the requirement from `HasTypeDescPi` to `HasTypeUnion`.  The
accessibility gate `sourceContext.isAccessibleAtModality index useModality = true` is what the modality-parametric
var-leaf discipline needs: the substitution master's var case fires for a source variable accessible at the
use-modality the original `var` derivation chose (the union `var` rule now carries that premise at ANY modality),
so the condition types the image of every variable the derivation could have used — a `lockCons`-bound dimension
variable is covered at its `.dimensional` use-modality (its interval use), and ordinary variables at `.fibrant`.
The `useModality` is IMPLICIT so the master's var case `condition index isAccessible` threads the var's own
use-modality with no change. -/
abbrev HasTypeUnion.SubstUnionTyped {profile : PolyProfile} {sourceScope targetScope : Nat}
    (sourceContext : TypingContext profile sourceScope)
    (targetContext : TypingContext profile targetScope)
    (substitution : RawTermSubst sourceScope targetScope) : Prop :=
  (∀ (index : Fin sourceScope) {useModality : ObligationModality},
    sourceContext.isAccessibleAtModality index useModality = true →
    HasTypeUnion profile targetContext (substitution index)
      (RawTerm.subst substitution (sourceContext.lookup index))) ∧
  (∀ (modality : ObligationModality) (index : Fin sourceScope),
    sourceContext.isAccessibleAtModality index modality = true →
    targetContext.isSubjectUsableAtModality (substitution index) modality = true)

/-- **★ A1-CONJUNCT-WIRE (the lock-FREE single-substitution `.2`, fibrant-image form).**  The cons / fibrant
twin of `substLockSingletonAccessibilityPreserved`: the accessibility-preservation conjunct for
`RawTermSubst.singleton argument` substituting INTO `context.cons domain` (the ordinary β single-substitution),
keyed on a FIBRANTLY-usable `argument` rather than a lock-free target.  It holds because the substitution maps
the freshest `var 0` to `argument` (usable at the fibrant position the `cons` binder demands,
`argumentUsableFibrantly`) and maps every deeper `var k` to itself — and a plain `cons` is transparent to the
suffix-lock (`isFibrantlyAccessibleAt_cons_succ`), so the tail transports accessibility identically.  The
fibrant counterpart of the dimensional `substLockSingletonAccessibilityPreserved`: where the lock case demanded
a DIMENSIONALLY-usable image for the locked `var 0`, the ordinary `cons` case demands a FIBRANTLY-usable image —
the leaf single-substitution lemmas (`subst0WithUnionImage`) discharge their bundled `.2` through this, replacing
the lock-free-target precondition with the (strictly weaker, lock-aware) fibrant-image precondition. -/
theorem substSingletonAccessibilityPreserved {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (domain : RawTerm scope) (argument : RawTerm scope)
    (argumentUsableFibrantly : context.isSubjectUsableAtModality argument .fibrant = true) :
    ∀ (modality : ObligationModality) (index : Fin (scope + 1)),
      (context.cons domain).isAccessibleAtModality index modality = true →
      context.isSubjectUsableAtModality (RawTermSubst.singleton argument index) modality = true := by
  intro modality index accessible
  cases modality with
  | fibrant =>
      obtain ⟨indexValue, indexBound⟩ := index
      cases indexValue with
      | zero =>
          -- `RawTermSubst.singleton argument ⟨0, _⟩` is defeq `argument`.
          exact argumentUsableFibrantly
      | succ priorValue =>
          rw [isAccessibleAtModality_fibrant, isFibrantlyAccessibleAt_cons_succ] at accessible
          show context.isSubjectUsableAtModality
            (.mkGen .gen_var ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩ .childNil) .fibrant = true
          rw [isSubjectUsableAtModality_var, isAccessibleAtModality_fibrant]
          exact accessible
  | dimensional =>
      obtain ⟨indexValue, indexBound⟩ := index
      cases indexValue with
      | zero =>
          -- `(context.cons domain).isDimensionallyAccessibleAt ⟨0, _⟩` is defeq `false`.
          rw [isAccessibleAtModality_dimensional] at accessible
          exact Bool.noConfusion accessible
      | succ priorValue =>
          have accessibleInRest :
              context.isDimensionallyAccessibleAt
                ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩ = true := accessible
          show context.isSubjectUsableAtModality
            (.mkGen .gen_var ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩ .childNil) .dimensional = true
          rw [isSubjectUsableAtModality_var, isAccessibleAtModality_dimensional]
          exact accessibleInRest

/-- **★ A1-CONJUNCT-WIRE (the lock single-substitution `.2`, dimensional-image form).**  The `lockCons` twin of
`substSingletonAccessibilityPreserved`: the accessibility-preservation conjunct for `RawTermSubst.singleton
argument` substituting INTO `context.lockCons dimensionType` (the pathLam body-endpoint substitution), keyed on a
DIMENSIONALLY-usable `argument`.  The substitution maps the locked `var 0` to `argument` (usable at the
dimensional position the lock demands) and every deeper `var k` to itself; the lock is transparent to the
suffix-lock.  The fibrant zero leg is vacuous (the locked `var 0` is NOT fibrantly accessible). -/
theorem substLockSingletonAccessibilityPreserved {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (dimensionType : RawTerm scope) (argument : RawTerm scope)
    (argumentUsableDimensionally : context.isSubjectUsableAtModality argument .dimensional = true) :
    ∀ (modality : ObligationModality) (index : Fin (scope + 1)),
      (context.lockCons dimensionType).isAccessibleAtModality index modality = true →
      context.isSubjectUsableAtModality (RawTermSubst.singleton argument index) modality = true := by
  intro modality index accessible
  obtain ⟨indexValue, indexBound⟩ := index
  cases modality with
  | fibrant =>
      cases indexValue with
      | zero =>
          rw [isAccessibleAtModality_fibrant, isFibrantlyAccessibleAt_lockCons_zero] at accessible
          exact Bool.noConfusion accessible
      | succ priorValue =>
          rw [isAccessibleAtModality_fibrant, isFibrantlyAccessibleAt_lockCons_succ] at accessible
          show context.isSubjectUsableAtModality
            (.mkGen .gen_var ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩ .childNil) .fibrant = true
          rw [isSubjectUsableAtModality_var, isAccessibleAtModality_fibrant]
          exact accessible
  | dimensional =>
      cases indexValue with
      | zero =>
          -- `RawTermSubst.singleton argument ⟨0, _⟩` is defeq `argument`.
          exact argumentUsableDimensionally
      | succ priorValue =>
          have accessibleInRest :
              context.isDimensionallyAccessibleAt
                ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩ = true := accessible
          show context.isSubjectUsableAtModality
            (.mkGen .gen_var ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩ .childNil) .dimensional = true
          rw [isSubjectUsableAtModality_var, isAccessibleAtModality_dimensional]
          exact accessibleInRest

/-- **★ A1-CONJUNCT-WIRE (the lock-FREE two-substitution `.2`, fibrant-image form).**  The two-binder cons.cons /
fibrant twin: the accessibility-preservation conjunct for `RawTermSubst.cons innerArg (RawTermSubst.singleton
outerArg)` substituting INTO `(context.cons outerType).cons innerType` (the β-pair / recursor-step simultaneous
substitution), keyed on BOTH substituents being fibrantly usable.  It holds because the substitution maps
`var 0` to `innerArg` and `var 1` to `outerArg` (each usable at the fibrant position its ordinary `cons` binder
demands) and maps every deeper `var (k + 2)` to itself — both `cons` binders transparent to the suffix-lock, so
the deep tail transports accessibility identically.  The two-binder counterpart of
`substSingletonAccessibilityPreserved`; the pair leaf lemma (`substPairUnderTwoBindingsUnionImages`) discharges
its bundled `.2` through this once it carries `innerArgUsableFibrantly` / `outerArgUsableFibrantly` instead of
the lock-free-target precondition. -/
theorem substPairAccessibilityPreserved {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (outerType : RawTerm scope) (innerType : RawTerm (scope + 1))
    (innerArg outerArg : RawTerm scope)
    (innerArgUsableFibrantly : context.isSubjectUsableAtModality innerArg .fibrant = true)
    (outerArgUsableFibrantly : context.isSubjectUsableAtModality outerArg .fibrant = true) :
    ∀ (modality : ObligationModality) (index : Fin (scope + 2)),
      ((context.cons outerType).cons innerType).isAccessibleAtModality index modality = true →
      context.isSubjectUsableAtModality
        (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg) index) modality = true := by
  intro modality index accessible
  cases modality with
  | fibrant =>
      obtain ⟨indexValue, indexBound⟩ := index
      cases indexValue with
      | zero =>
          -- `RawTermSubst.cons innerArg _ ⟨0, _⟩` is defeq `innerArg`.
          exact innerArgUsableFibrantly
      | succ tailValue =>
          cases tailValue with
          | zero =>
              -- `RawTermSubst.cons innerArg (singleton outerArg) ⟨1, _⟩` is defeq `outerArg`.
              exact outerArgUsableFibrantly
          | succ priorValue =>
              rw [isAccessibleAtModality_fibrant, isFibrantlyAccessibleAt_cons_succ,
                isFibrantlyAccessibleAt_cons_succ] at accessible
              show context.isSubjectUsableAtModality
                (.mkGen .gen_var
                  ⟨priorValue, Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ indexBound)⟩ .childNil)
                .fibrant = true
              rw [isSubjectUsableAtModality_var, isAccessibleAtModality_fibrant]
              exact accessible
  | dimensional =>
      obtain ⟨indexValue, indexBound⟩ := index
      cases indexValue with
      | zero =>
          rw [isAccessibleAtModality_dimensional] at accessible
          exact Bool.noConfusion accessible
      | succ tailValue =>
          cases tailValue with
          | zero =>
              rw [isAccessibleAtModality_dimensional] at accessible
              exact Bool.noConfusion accessible
          | succ priorValue =>
              have accessibleInRest :
                  context.isDimensionallyAccessibleAt
                    ⟨priorValue, Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ indexBound)⟩ = true :=
                accessible
              show context.isSubjectUsableAtModality
                (.mkGen .gen_var
                  ⟨priorValue, Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ indexBound)⟩ .childNil)
                .dimensional = true
              rw [isSubjectUsableAtModality_var, isAccessibleAtModality_dimensional]
              exact accessibleInRest

/-! ### `.2`-lift substrate (relocated up from the substitution master for the bundled condition)

The two structural lemmas that lift the accessibility-preservation conjunct (`.2`) across a `cons` /
`lockCons` binder.  They live HERE (not in the master) so the bundled `SubstUnionTyped.cons` / `.lockCons`
below can produce the lifted `.2` directly; they depend only on the rename-side usability transport
(`subjectUsabilityPreservedUnderRename` + `accessibilityAtModalityPreservedUnderWeaken{Cons,LockCons}`,
all upstream in `HasTypeUnionWeakening`), so the relocation introduces no cycle. -/

/-- **★ `substRespectsModality` lifts across a `cons` binder.**  If `substitution` carries every accessible
source variable to a usable image, so does its single lift across a fresh ordinary binder.  Zero case: the
fresh `var 0` is usable fibrantly (`cons`-zero is fibrantly accessible) and the dimensional leg is vacuous
(the source `cons`-zero dimensional check is `false`); deeper case: the image `RawTerm.weaken (substitution
k)` is weakened past the new binder via `subjectUsabilityPreservedUnderRename`. -/
theorem substRespectsModalityUnderConsLift {profile : PolyProfile} {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (domainCode : RawTerm sourceScope) (newTargetBinding : RawTerm targetScope)
    {substitution : RawTermSubst sourceScope targetScope} (modality : ObligationModality)
    (substRespectsModality : ∀ index : Fin sourceScope,
        sourceContext.isAccessibleAtModality index modality = true →
        targetContext.isSubjectUsableAtModality (substitution index) modality = true) :
    ∀ index : Fin (sourceScope + 1),
      (sourceContext.cons domainCode).isAccessibleAtModality index modality = true →
      (targetContext.cons newTargetBinding).isSubjectUsableAtModality
        (iterateLiftRaw substitution 1 index) modality = true := by
  intro index accessible
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      show (targetContext.cons newTargetBinding).isSubjectUsableAtModality
        (.mkGen .gen_var ⟨0, Nat.zero_lt_succ targetScope⟩ .childNil) modality = true
      rw [isSubjectUsableAtModality_var]
      cases modality with
      | fibrant => rfl
      | dimensional => exact Bool.noConfusion (show (false : Bool) = true from accessible)
  | succ priorValue =>
      have accessibleInRest :
          sourceContext.isAccessibleAtModality
            ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩ modality = true := by
        cases modality with
        | fibrant => exact accessible
        | dimensional => exact accessible
      show (targetContext.cons newTargetBinding).isSubjectUsableAtModality
        (RawTerm.weaken (substitution ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩)) modality = true
      exact subjectUsabilityPreservedUnderRename RawRenaming.weaken modality
        (accessibilityAtModalityPreservedUnderWeakenCons targetContext newTargetBinding modality)
        (substitution ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩)
        (substRespectsModality ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩ accessibleInRest)

/-- **★ `substRespectsModality` lifts across a `lockCons` (affine dimension lock) binder.**  The
`pathLam`-body twin of `substRespectsModalityUnderConsLift`.  Zero case is MODALITY-SWAPPED: the fresh
dimension `var 0` is usable DIMENSIONALLY (`lockCons`-zero is dimensionally accessible) and the FIBRANT leg
is vacuous (the source `lockCons`-zero fibrant check is `false` — the SR-soundness half: the locked
dimension is not a fibrant value); deeper case is identical via the `lockCons` weaken-accessibility glue. -/
theorem substRespectsModalityUnderLockConsLift {profile : PolyProfile} {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (dimensionType : RawTerm sourceScope) (newTargetDimensionType : RawTerm targetScope)
    {substitution : RawTermSubst sourceScope targetScope} (modality : ObligationModality)
    (substRespectsModality : ∀ index : Fin sourceScope,
        sourceContext.isAccessibleAtModality index modality = true →
        targetContext.isSubjectUsableAtModality (substitution index) modality = true) :
    ∀ index : Fin (sourceScope + 1),
      (sourceContext.lockCons dimensionType).isAccessibleAtModality index modality = true →
      (targetContext.lockCons newTargetDimensionType).isSubjectUsableAtModality
        (iterateLiftRaw substitution 1 index) modality = true := by
  intro index accessible
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      show (targetContext.lockCons newTargetDimensionType).isSubjectUsableAtModality
        (.mkGen .gen_var ⟨0, Nat.zero_lt_succ targetScope⟩ .childNil) modality = true
      rw [isSubjectUsableAtModality_var]
      cases modality with
      | fibrant => exact Bool.noConfusion (show (false : Bool) = true from accessible)
      | dimensional => rfl
  | succ priorValue =>
      have accessibleInRest :
          sourceContext.isAccessibleAtModality
            ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩ modality = true := by
        cases modality with
        | fibrant => exact accessible
        | dimensional => exact accessible
      show (targetContext.lockCons newTargetDimensionType).isSubjectUsableAtModality
        (RawTerm.weaken (substitution ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩)) modality = true
      exact subjectUsabilityPreservedUnderRename RawRenaming.weaken modality
        (accessibilityAtModalityPreservedUnderWeakenLockCons targetContext newTargetDimensionType modality)
        (substitution ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩)
        (substRespectsModality ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩ accessibleInRest)

/-- **The bare (UNgated) one-binder lift of the substitution images.**  The lift of an UNRESTRICTED
`∀ index` typing across a `cons` binder — the form the host-substitution leg (`hostSubstWithUnionImages`,
whose source is structurally lock-free, so every index is typed) consumes.  `0` resolves to the fresh `var`
(the `cons`-zero binding is fibrantly accessible, so the native `var` rule admits it by `rfl`); `k+1` to the
base image weakened. -/
theorem HasTypeUnion.bareSubstImagesUnderConsLift {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (domainCode : RawTerm sourceScope) (substitution : RawTermSubst sourceScope targetScope)
    (bareImages : ∀ index : Fin sourceScope,
        HasTypeUnion profile targetContext (substitution index)
          (RawTerm.subst substitution (sourceContext.lookup index))) :
    ∀ index : Fin (sourceScope + 1),
      HasTypeUnion profile (targetContext.cons (RawTerm.subst substitution domainCode))
        (iterateLiftRaw substitution 1 index)
        (RawTerm.subst (iterateLiftRaw substitution 1)
          ((sourceContext.cons domainCode).lookup index)) := by
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
        ⟨0, Nat.succ_pos _⟩ (useModality := .fibrant) rfl
  | succ priorValue =>
      show HasTypeUnion profile
        (targetContext.cons (RawTerm.subst substitution domainCode))
        (RawTermSubst.lift substitution ⟨priorValue + 1, indexBound⟩)
        (RawTerm.subst (RawTermSubst.lift substitution)
          ((sourceContext.cons domainCode).lookup ⟨priorValue + 1, indexBound⟩))
      rw [TypingContext.lookup_cons_succ, subst_lift_weaken_commute]
      exact (bareImages ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderBinding
        (RawTerm.subst substitution domainCode)

/-- **The one-binder lift of the native substitution condition.**  The restricted typing condition lifts
across a `cons` binder: `0` is the fresh `var` (`cons`-zero accessible by `rfl`); `k+1` weakens the base image,
its accessibility gate lowered through `isFibrantlyAccessibleAt_cons_succ`. -/
theorem HasTypeUnion.SubstUnionTyped.cons {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (domainCode : RawTerm sourceScope) (substitution : RawTermSubst sourceScope targetScope)
    (condition : HasTypeUnion.SubstUnionTyped sourceContext targetContext substitution) :
    HasTypeUnion.SubstUnionTyped (sourceContext.cons domainCode)
      (targetContext.cons (RawTerm.subst substitution domainCode))
      (iterateLiftRaw substitution 1) := by
  refine ⟨?_, fun modality => substRespectsModalityUnderConsLift domainCode
    (RawTerm.subst substitution domainCode) modality (condition.2 modality)⟩
  intro index useModality isAccessible
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
        ⟨0, Nat.succ_pos _⟩ (useModality := .fibrant) rfl
  | succ priorValue =>
      show HasTypeUnion profile
        (targetContext.cons (RawTerm.subst substitution domainCode))
        (RawTermSubst.lift substitution ⟨priorValue + 1, indexBound⟩)
        (RawTerm.subst (RawTermSubst.lift substitution)
          ((sourceContext.cons domainCode).lookup ⟨priorValue + 1, indexBound⟩))
      rw [TypingContext.lookup_cons_succ, subst_lift_weaken_commute]
      -- a plain `cons` is transparent to the suffix-lock at EVERY modality, so the gate transports by defeq
      -- (`cons_succ` is modality-uniform); feed the prior condition at the var's own use-modality.
      exact (condition.1 ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩
        isAccessible).weakenUnderBinding
        (RawTerm.subst substitution domainCode)

/-- **The one-binder lift of the native substitution condition UNDER THE AFFINE DIMENSION LOCK
(`lockCons`).**  The `lockCons` twin of `SubstUnionTyped.cons`.  The fresh locked dimension `var 0` is NOT
fibrantly accessible (`isFibrantlyAccessibleAt_lockCons_zero`), so the restricted condition's gate is FALSE at
index 0 — the locked dimension is excluded VACUOUSLY (it is never a fibrant `var`; its interval use is admitted
by the `.dimensional` ObligationModality on the eliminator's interval-argument obligation row, not this
condition).  The deeper images (`k+1`) weaken the base under the lock,
their gate lowered through `isFibrantlyAccessibleAt_lockCons_succ` (the lock is CX/EXTEND-transparent to the
suffix). -/
theorem HasTypeUnion.SubstUnionTyped.lockCons {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (dimensionType : RawTerm sourceScope) (substitution : RawTermSubst sourceScope targetScope)
    (condition : HasTypeUnion.SubstUnionTyped sourceContext targetContext substitution) :
    HasTypeUnion.SubstUnionTyped (sourceContext.lockCons dimensionType)
      (targetContext.lockCons (RawTerm.subst substitution dimensionType))
      (iterateLiftRaw substitution 1) := by
  refine ⟨?_, fun modality => substRespectsModalityUnderLockConsLift dimensionType
    (RawTerm.subst substitution dimensionType) modality (condition.2 modality)⟩
  intro index useModality isAccessible
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      -- the fresh locked dimension `var 0`: at `.fibrant` the gate is FALSE (vacuous); at `.dimensional` the
      -- locked dimension IS accessible, and its image (the fresh `var 0`) is typed at the dimensional modality.
      cases useModality with
      | fibrant =>
          rw [isAccessibleAtModality_fibrant, isFibrantlyAccessibleAt_lockCons_zero] at isAccessible
          exact Bool.noConfusion isAccessible
      | dimensional =>
          show HasTypeUnion profile
            (targetContext.lockCons (RawTerm.subst substitution dimensionType))
            (RawTermSubst.lift substitution ⟨0, indexBound⟩)
            (RawTerm.subst (RawTermSubst.lift substitution)
              ((sourceContext.lockCons dimensionType).lookup ⟨0, indexBound⟩))
          rw [TypingContext.lookup_lockCons_zero, subst_lift_weaken_commute]
          exact HasTypeUnion.var
            (targetContext.lockCons (RawTerm.subst substitution dimensionType))
            ⟨0, Nat.succ_pos _⟩ (useModality := .dimensional) rfl
  | succ priorValue =>
      show HasTypeUnion profile
        (targetContext.lockCons (RawTerm.subst substitution dimensionType))
        (RawTermSubst.lift substitution ⟨priorValue + 1, indexBound⟩)
        (RawTerm.subst (RawTermSubst.lift substitution)
          ((sourceContext.lockCons dimensionType).lookup ⟨priorValue + 1, indexBound⟩))
      rw [TypingContext.lookup_lockCons_succ, subst_lift_weaken_commute]
      -- the lock is CX/EXTEND-transparent to the suffix at EVERY modality (`lockCons_succ` recurses like
      -- `cons_succ`), so the gate transports by defeq; feed the prior condition at the var's use-modality.
      exact (condition.1 ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩
        isAccessible).weakenUnderLockBinding
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
