import LeanFX.Syntax.StrengthenSubst
import LeanFX.Syntax.TypedTerm

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Typed strengthening results.

`Ty.strengthen` and `RawTerm.strengthen` recover syntax from the image
of weakening.  Typed terms need one more piece of data: the recovered
type.  A term in an extended context has some extended type
`extendedType`; when strengthening succeeds we return the original type,
the proof that weakening it gives `extendedType`, and the recovered term
at that original type.
-/

/-- A successfully strengthened term packaged with its recovered type. -/
structure StrengthenedTerm {mode : Mode} {scope : Nat}
    (context : Ctx mode level scope) (extendedType : Ty level (scope + 1)) where
  /-- The type before weakening. -/
  originalType : Ty level scope
  /-- Weakening the recovered type reconstructs the extended type. -/
  typeEquality : originalType.weaken = extendedType
  /-- The recovered term at the recovered type. -/
  term : Term context originalType

namespace StrengthenedTerm

/-- If the extended type strengthens to a chosen expected type, the
recovered type in a `StrengthenedTerm` is that expected type. -/
theorem original_eq_of_strengthen {mode : Mode} {scope : Nat}
    {context : Ctx mode level scope}
    {extendedType : Ty level (scope + 1)} {expectedType : Ty level scope}
    (strengthenedTerm : StrengthenedTerm context extendedType)
    (expectedStrengthening : extendedType.strengthen = some expectedType) :
    strengthenedTerm.originalType = expectedType := by
  have recoveredStrengthening :
      extendedType.strengthen = some strengthenedTerm.originalType :=
    (Ty.strengthen_eq_some_iff_weaken
      extendedType strengthenedTerm.originalType).mpr strengthenedTerm.typeEquality
  exact Option.some.inj (recoveredStrengthening.symm.trans expectedStrengthening)

/-- Cast the recovered term to an expected type when the extended type
strengthens to that expected type. -/
def termAs {mode : Mode} {scope : Nat}
    {context : Ctx mode level scope}
    {extendedType : Ty level (scope + 1)} {expectedType : Ty level scope}
    (strengthenedTerm : StrengthenedTerm context extendedType)
    (expectedStrengthening : extendedType.strengthen = some expectedType) :
    Term context expectedType :=
  (original_eq_of_strengthen strengthenedTerm expectedStrengthening) ▸
    strengthenedTerm.term

end StrengthenedTerm

/-! ## Generic typed optional-renaming results. -/

/-- A successfully optional-renamed term packaged with its recovered
type and the proof connecting that type to the source type's optional
renaming. -/
structure OptionalRenamedTerm {mode : Mode} {sourceScope targetScope : Nat}
    (targetContext : Ctx mode level targetScope)
    (optionalRenaming : OptionalRenaming sourceScope targetScope)
    (sourceType : Ty level sourceScope) where
  /-- The type after optional renaming succeeds. -/
  renamedType : Ty level targetScope
  /-- Optional-renaming the source type reconstructs `renamedType`. -/
  typeEquality : sourceType.optRename optionalRenaming = some renamedType
  /-- The recovered term at the recovered type. -/
  term : Term targetContext renamedType

namespace OptionalRenamedTerm

/-- If the source type optional-renames to an expected type, the
packaged recovered type is that expected type. -/
theorem renamed_eq_of_optRename {mode : Mode} {sourceScope targetScope : Nat}
    {targetContext : Ctx mode level targetScope}
    {optionalRenaming : OptionalRenaming sourceScope targetScope}
    {sourceType : Ty level sourceScope} {expectedType : Ty level targetScope}
    (renamedTerm :
      OptionalRenamedTerm targetContext optionalRenaming sourceType)
    (expectedRenaming : sourceType.optRename optionalRenaming =
      some expectedType) :
    renamedTerm.renamedType = expectedType :=
  Option.some.inj (renamedTerm.typeEquality.symm.trans expectedRenaming)

/-- Cast the recovered term to an expected type when the source type
optional-renames to that expected type. -/
def termAs {mode : Mode} {sourceScope targetScope : Nat}
    {targetContext : Ctx mode level targetScope}
    {optionalRenaming : OptionalRenaming sourceScope targetScope}
    {sourceType : Ty level sourceScope} {expectedType : Ty level targetScope}
    (renamedTerm :
      OptionalRenamedTerm targetContext optionalRenaming sourceType)
    (expectedRenaming : sourceType.optRename optionalRenaming =
      some expectedType) :
    Term targetContext expectedType :=
  (renamed_eq_of_optRename renamedTerm expectedRenaming) ▸ renamedTerm.term

/-- Specialise an optional-renamed term along `OptionalRenaming.unweaken`
to the strengthening package. -/
def toStrengthened {mode : Mode} {scope : Nat}
    {context : Ctx mode level scope} {extendedType : Ty level (scope + 1)}
    (renamedTerm :
      OptionalRenamedTerm context OptionalRenaming.unweaken extendedType) :
    StrengthenedTerm context extendedType where
  originalType := renamedTerm.renamedType
  typeEquality :=
    (Ty.strengthen_eq_some_iff_weaken
      extendedType renamedTerm.renamedType).mp renamedTerm.typeEquality
  term := renamedTerm.term

end OptionalRenamedTerm

/-! ## Context compatibility for typed optional renaming. -/

/-- A typed optional renaming is compatible with source and target
contexts when every successful variable-position mapping also maps the
source variable type to the target variable type.  This is the typed
counterpart of `OptionalRenaming`: it supplies exactly the cast needed
to turn a successful variable mapping into a `Term.var` in the target
context. -/
def TermOptionalRenaming {mode : Mode} {sourceScope targetScope : Nat}
    (sourceContext : Ctx mode level sourceScope)
    (targetContext : Ctx mode level targetScope)
    (optionalRenaming : OptionalRenaming sourceScope targetScope) : Prop :=
  ∀ sourcePosition targetPosition,
    optionalRenaming sourcePosition = some targetPosition →
      (varType sourceContext sourcePosition).optRename optionalRenaming =
        some (varType targetContext targetPosition)

namespace TermOptionalRenaming

/-- Identity optional renaming is compatible with any context. -/
theorem identity {mode : Mode} {scope : Nat}
    (context : Ctx mode level scope) :
    TermOptionalRenaming context context OptionalRenaming.identity := by
  intro sourcePosition targetPosition positionMaps
  change some sourcePosition = some targetPosition at positionMaps
  cases positionMaps
  exact Ty.optRename_identity (varType context sourcePosition)

/-- Dropping the newest context variable is compatible with the prefix
context: variable 0 is unmapped, and every successor variable's type is
itself a weakening of the corresponding prefix variable type. -/
theorem unweaken {mode : Mode} {scope : Nat}
    (context : Ctx mode level scope) (newType : Ty level scope) :
    TermOptionalRenaming (context.cons newType) context
      OptionalRenaming.unweaken := by
  intro sourcePosition targetPosition positionMaps
  match sourcePosition with
  | ⟨0, _⟩ =>
      cases positionMaps
  | ⟨position + 1, isWithinSource⟩ =>
      cases positionMaps
      exact Ty.strengthen_weaken
        (varType context ⟨position, Nat.lt_of_succ_lt_succ isWithinSource⟩)

/-- Typed optional-renaming compatibility is stable under binders when
the binder type itself optional-renames successfully. -/
theorem lift {mode : Mode} {sourceScope targetScope : Nat}
    {sourceContext : Ctx mode level sourceScope}
    {targetContext : Ctx mode level targetScope}
    {optionalRenaming : OptionalRenaming sourceScope targetScope}
    {sourceType : Ty level sourceScope} {targetType : Ty level targetScope}
    (renamingIsCompatible :
      TermOptionalRenaming sourceContext targetContext optionalRenaming)
    (sourceTypeMaps : sourceType.optRename optionalRenaming = some targetType) :
    TermOptionalRenaming
      (sourceContext.cons sourceType) (targetContext.cons targetType)
      optionalRenaming.lift := by
  intro sourcePosition targetPosition positionMaps
  match sourcePosition with
  | ⟨0, _⟩ =>
      change some ⟨0, Nat.zero_lt_succ targetScope⟩ =
        some targetPosition at positionMaps
      cases positionMaps
      change sourceType.weaken.optRename optionalRenaming.lift =
        some targetType.weaken
      rw [Ty.weaken_optRename_lift optionalRenaming sourceType, sourceTypeMaps]
      rfl
  | ⟨sourceIndex + 1, isWithinSource⟩ =>
      let sourcePredecessor : Fin sourceScope :=
        ⟨sourceIndex, Nat.lt_of_succ_lt_succ isWithinSource⟩
      change Option.map Fin.succ (optionalRenaming sourcePredecessor) =
        some targetPosition at positionMaps
      cases predecessorMapping : optionalRenaming sourcePredecessor with
      | none =>
          rw [predecessorMapping] at positionMaps
          cases positionMaps
      | some targetPredecessor =>
          rw [predecessorMapping] at positionMaps
          cases positionMaps
          change
            (varType sourceContext sourcePredecessor).weaken.optRename
                optionalRenaming.lift =
              some (varType targetContext targetPredecessor).weaken
          rw [Ty.weaken_optRename_lift optionalRenaming
            (varType sourceContext sourcePredecessor)]
          rw [renamingIsCompatible sourcePredecessor
            targetPredecessor predecessorMapping]
          rfl

end TermOptionalRenaming

/-! ## Typed optional renaming for terms. -/

/-- Bind an `Option` while exposing the proof that the successful
branch is the one being used.  This is the dependent version of
`Option.bind` needed when a typed constructor also has to return the
proof that its type optional-renamed successfully. -/
def Option.bindSome {valueType resultType : Type}
    (optionalValue : Option valueType)
    (next :
      (mappedValue : valueType) → optionalValue = some mappedValue →
        Option resultType) :
    Option resultType :=
  match optionalValue with
  | none => none
  | some mappedValue => next mappedValue rfl

/-- Successful optional renaming of arrow components rebuilds the
renamed arrow type. -/
theorem Ty.arrow_optRename_success {source target : Nat}
    (optionalRenaming : OptionalRenaming source target)
    {domainType codomainType : Ty level source}
    {renamedDomain renamedCodomain : Ty level target}
    (domainMaps : domainType.optRename optionalRenaming = some renamedDomain)
    (codomainMaps :
      codomainType.optRename optionalRenaming = some renamedCodomain) :
    (Ty.arrow domainType codomainType).optRename optionalRenaming =
      some (Ty.arrow renamedDomain renamedCodomain) := by
  change Option.bind (domainType.optRename optionalRenaming)
      (fun mappedDomain =>
        Option.bind (codomainType.optRename optionalRenaming)
          (fun mappedCodomain =>
            some (Ty.arrow mappedDomain mappedCodomain))) =
    some (Ty.arrow renamedDomain renamedCodomain)
  rw [domainMaps, codomainMaps]
  rfl

/-- Successful optional renaming of dependent-pi components rebuilds
the renamed `piTy`. -/
theorem Ty.piTy_optRename_success {source target : Nat}
    (optionalRenaming : OptionalRenaming source target)
    {domainType : Ty level source} {codomainType : Ty level (source + 1)}
    {renamedDomain : Ty level target}
    {renamedCodomain : Ty level (target + 1)}
    (domainMaps : domainType.optRename optionalRenaming = some renamedDomain)
    (codomainMaps :
      codomainType.optRename optionalRenaming.lift = some renamedCodomain) :
    (Ty.piTy domainType codomainType).optRename optionalRenaming =
      some (Ty.piTy renamedDomain renamedCodomain) := by
  change Option.bind (domainType.optRename optionalRenaming)
      (fun mappedDomain =>
        Option.bind (codomainType.optRename optionalRenaming.lift)
          (fun mappedCodomain =>
            some (Ty.piTy mappedDomain mappedCodomain))) =
    some (Ty.piTy renamedDomain renamedCodomain)
  rw [domainMaps, codomainMaps]
  rfl

/-- Successful optional renaming of dependent-sigma components rebuilds
the renamed `sigmaTy`. -/
theorem Ty.sigmaTy_optRename_success {source target : Nat}
    (optionalRenaming : OptionalRenaming source target)
    {firstType : Ty level source} {secondType : Ty level (source + 1)}
    {renamedFirst : Ty level target}
    {renamedSecond : Ty level (target + 1)}
    (firstMaps : firstType.optRename optionalRenaming = some renamedFirst)
    (secondMaps :
      secondType.optRename optionalRenaming.lift = some renamedSecond) :
    (Ty.sigmaTy firstType secondType).optRename optionalRenaming =
      some (Ty.sigmaTy renamedFirst renamedSecond) := by
  change Option.bind (firstType.optRename optionalRenaming)
      (fun mappedFirst =>
        Option.bind (secondType.optRename optionalRenaming.lift)
          (fun mappedSecond =>
            some (Ty.sigmaTy mappedFirst mappedSecond))) =
    some (Ty.sigmaTy renamedFirst renamedSecond)
  rw [firstMaps, secondMaps]
  rfl

/-- Successful optional renaming of a list element type rebuilds the
renamed list type. -/
theorem Ty.list_optRename_success {source target : Nat}
    (optionalRenaming : OptionalRenaming source target)
    {elementType : Ty level source} {renamedElement : Ty level target}
    (elementMaps :
      elementType.optRename optionalRenaming = some renamedElement) :
    (Ty.list elementType).optRename optionalRenaming =
      some (Ty.list renamedElement) := by
  change Option.map Ty.list (elementType.optRename optionalRenaming) =
    some (Ty.list renamedElement)
  rw [elementMaps]
  rfl

/-- Successful optional renaming of an option element type rebuilds the
renamed option type. -/
theorem Ty.option_optRename_success {source target : Nat}
    (optionalRenaming : OptionalRenaming source target)
    {elementType : Ty level source} {renamedElement : Ty level target}
    (elementMaps :
      elementType.optRename optionalRenaming = some renamedElement) :
    (Ty.option elementType).optRename optionalRenaming =
      some (Ty.option renamedElement) := by
  change Option.map Ty.option (elementType.optRename optionalRenaming) =
    some (Ty.option renamedElement)
  rw [elementMaps]
  rfl

/-- Successful optional renaming of either components rebuilds the
renamed either type. -/
theorem Ty.either_optRename_success {source target : Nat}
    (optionalRenaming : OptionalRenaming source target)
    {leftType rightType : Ty level source}
    {renamedLeft renamedRight : Ty level target}
    (leftMaps : leftType.optRename optionalRenaming = some renamedLeft)
    (rightMaps : rightType.optRename optionalRenaming = some renamedRight) :
    (Ty.either leftType rightType).optRename optionalRenaming =
      some (Ty.either renamedLeft renamedRight) := by
  change Option.bind (leftType.optRename optionalRenaming)
      (fun mappedLeft =>
        Option.bind (rightType.optRename optionalRenaming)
          (fun mappedRight =>
            some (Ty.either mappedLeft mappedRight))) =
    some (Ty.either renamedLeft renamedRight)
  rw [leftMaps, rightMaps]
  rfl

/-- Successful optional renaming of identity components rebuilds the
renamed identity type. -/
theorem Ty.id_optRename_success {source target : Nat}
    (optionalRenaming : OptionalRenaming source target)
    {carrier : Ty level source} {leftEnd rightEnd : RawTerm source}
    {renamedCarrier : Ty level target}
    {renamedLeft renamedRight : RawTerm target}
    (carrierMaps : carrier.optRename optionalRenaming = some renamedCarrier)
    (leftMaps : leftEnd.optRename optionalRenaming = some renamedLeft)
    (rightMaps : rightEnd.optRename optionalRenaming = some renamedRight) :
    (Ty.id carrier leftEnd rightEnd).optRename optionalRenaming =
      some (Ty.id renamedCarrier renamedLeft renamedRight) := by
  change Option.bind (carrier.optRename optionalRenaming)
      (fun mappedCarrier =>
        Option.bind (leftEnd.optRename optionalRenaming)
          (fun mappedLeft =>
            Option.bind (rightEnd.optRename optionalRenaming)
              (fun mappedRight =>
                some (Ty.id mappedCarrier mappedLeft mappedRight)))) =
    some (Ty.id renamedCarrier renamedLeft renamedRight)
  rw [carrierMaps, leftMaps, rightMaps]
  rfl

/-- Apply an optional renaming to an intrinsically typed term.

The result is packaged with the renamed type because strengthening can
drop variables from both the term and its type.  Constructor cases bind
the renamed type components first, then use `OptionalRenamedTerm.termAs`
to cast recursively-renamed subterms to the expected constructor input
types. -/
def Term.optRename {mode : Mode} {sourceScope targetScope : Nat}
    {sourceContext : Ctx mode level sourceScope}
    {targetContext : Ctx mode level targetScope}
    {optionalRenaming : OptionalRenaming sourceScope targetScope}
    (renamingIsCompatible :
      TermOptionalRenaming sourceContext targetContext optionalRenaming) :
    {sourceType : Ty level sourceScope} →
      Term sourceContext sourceType →
        Option (OptionalRenamedTerm targetContext optionalRenaming sourceType)
  | _, .var sourcePosition =>
      Option.bindSome (optionalRenaming sourcePosition)
        fun targetPosition positionMaps =>
        some {
          renamedType := varType targetContext targetPosition
          typeEquality :=
            renamingIsCompatible sourcePosition targetPosition positionMaps
          term := Term.var targetPosition
        }
  | _, .unit =>
      some {
        renamedType := Ty.unit
        typeEquality := rfl
        term := Term.unit
      }
  | _, .lam (domainType := domainType) (codomainType := codomainType) body =>
      Option.bindSome (domainType.optRename optionalRenaming)
        fun renamedDomain domainMaps =>
        Option.bindSome (codomainType.optRename optionalRenaming)
          fun renamedCodomain codomainMaps =>
          Option.bind
            (Term.optRename
              (TermOptionalRenaming.lift renamingIsCompatible domainMaps) body)
            fun renamedBody =>
              some {
                renamedType := Ty.arrow renamedDomain renamedCodomain
                typeEquality :=
                  Ty.arrow_optRename_success optionalRenaming domainMaps
                    codomainMaps
                term :=
                  Term.lam
                    (domainType := renamedDomain)
                    (codomainType := renamedCodomain)
                    (OptionalRenamedTerm.termAs renamedBody (by
                      rw [Ty.weaken_optRename_lift optionalRenaming codomainType]
                      rw [codomainMaps]
                      rfl))
              }
  | _, .app (domainType := domainType) (codomainType := codomainType)
        functionTerm argumentTerm =>
      Option.bindSome (domainType.optRename optionalRenaming)
        fun renamedDomain domainMaps =>
        Option.bindSome (codomainType.optRename optionalRenaming)
          fun renamedCodomain codomainMaps =>
          Option.bind (Term.optRename renamingIsCompatible functionTerm)
            fun renamedFunction =>
              Option.bind (Term.optRename renamingIsCompatible argumentTerm)
                fun renamedArgument =>
                  some {
                    renamedType := renamedCodomain
                    typeEquality := codomainMaps
                    term :=
                      Term.app
                        (OptionalRenamedTerm.termAs renamedFunction
                          (Ty.arrow_optRename_success optionalRenaming
                            domainMaps codomainMaps))
                        (OptionalRenamedTerm.termAs renamedArgument domainMaps)
                  }
  | _, .lamPi (domainType := domainType) (codomainType := codomainType) body =>
      Option.bindSome (domainType.optRename optionalRenaming)
        fun renamedDomain domainMaps =>
        Option.bindSome (codomainType.optRename optionalRenaming.lift)
          fun renamedCodomain codomainMaps =>
            Option.bind
              (Term.optRename
                (TermOptionalRenaming.lift renamingIsCompatible domainMaps) body)
              fun renamedBody =>
                some {
                  renamedType := Ty.piTy renamedDomain renamedCodomain
                  typeEquality :=
                    Ty.piTy_optRename_success optionalRenaming domainMaps
                      codomainMaps
                  term :=
                    Term.lamPi
                      (OptionalRenamedTerm.termAs renamedBody codomainMaps)
                }
  | _, .appPi (domainType := domainType) (codomainType := codomainType)
        (argumentRaw := argumentRaw) resultEq functionTerm argumentTerm =>
      Option.bindSome (domainType.optRename optionalRenaming)
        fun renamedDomain domainMaps =>
        Option.bindSome (codomainType.optRename optionalRenaming.lift)
          fun renamedCodomain codomainMaps =>
          Option.bindSome (argumentRaw.optRename optionalRenaming)
            fun renamedArgumentRaw rawArgMaps =>
            Option.bind (Term.optRename renamingIsCompatible functionTerm)
              fun renamedFunction =>
                Option.bind (Term.optRename renamingIsCompatible argumentTerm)
                  fun renamedArgument =>
                    some {
                      renamedType :=
                        renamedCodomain.subst (Subst.termSingleton
                          renamedDomain renamedArgumentRaw)
                      typeEquality :=
                        -- W9.B1.3a — `resultEq` is in termSingleton form;
                        -- chain it with `subst_termSingleton_optRename_success`.
                        resultEq ▸
                          Ty.subst_termSingleton_optRename_success
                            optionalRenaming codomainType domainType
                            renamedDomain argumentRaw renamedArgumentRaw
                            renamedCodomain codomainMaps domainMaps rawArgMaps
                      term :=
                        Term.appPi (argumentRaw := renamedArgumentRaw) rfl
                          (OptionalRenamedTerm.termAs renamedFunction
                            (Ty.piTy_optRename_success optionalRenaming
                              domainMaps codomainMaps))
                          (OptionalRenamedTerm.termAs renamedArgument domainMaps)
                    }
  | _, .pair (firstType := firstType) (secondType := secondType)
        firstVal secondVal =>
      Option.bindSome (firstType.optRename optionalRenaming)
        fun renamedFirst firstMaps =>
        Option.bindSome (secondType.optRename optionalRenaming.lift)
          fun renamedSecond secondMaps =>
            Option.bind (Term.optRename renamingIsCompatible firstVal)
              fun renamedFirstVal =>
                Option.bind (Term.optRename renamingIsCompatible secondVal)
                  fun renamedSecondVal =>
                    some {
                      renamedType := Ty.sigmaTy renamedFirst renamedSecond
                      typeEquality :=
                        Ty.sigmaTy_optRename_success optionalRenaming firstMaps
                          secondMaps
                      term :=
                        Term.pair
                          (OptionalRenamedTerm.termAs renamedFirstVal firstMaps)
                          (OptionalRenamedTerm.termAs renamedSecondVal
                            (Ty.subst0_optRename_success optionalRenaming
                              secondType firstType renamedFirst renamedSecond
                              secondMaps firstMaps))
                    }
  | _, .fst (firstType := firstType) (secondType := secondType) pairTerm =>
      Option.bindSome (firstType.optRename optionalRenaming)
        fun renamedFirst firstMaps =>
        Option.bindSome (secondType.optRename optionalRenaming.lift)
          fun renamedSecond secondMaps =>
            Option.bind (Term.optRename renamingIsCompatible pairTerm)
              fun renamedPair =>
                some {
                  renamedType := renamedFirst
                  typeEquality := firstMaps
                  term :=
                    Term.fst
                      (OptionalRenamedTerm.termAs renamedPair
                        (Ty.sigmaTy_optRename_success optionalRenaming
                          firstMaps secondMaps))
                }
  | _, .snd (firstType := firstType) (secondType := secondType)
            pairTerm resultEq =>
      Option.bindSome (firstType.optRename optionalRenaming)
        fun renamedFirst firstMaps =>
        Option.bindSome (secondType.optRename optionalRenaming.lift)
          fun renamedSecond secondMaps =>
            Option.bind (Term.optRename renamingIsCompatible pairTerm)
              fun renamedPair =>
                some {
                  renamedType := renamedSecond.subst0 renamedFirst
                  typeEquality :=
                    -- W9.B1.2 — chain resultEq (resultType =
                    -- secondType.subst0 firstType) with the canonical
                    -- subst0-rename success.
                    resultEq ▸
                      Ty.subst0_optRename_success optionalRenaming secondType
                        firstType renamedFirst renamedSecond secondMaps firstMaps
                  term :=
                    Term.snd
                      (OptionalRenamedTerm.termAs renamedPair
                        (Ty.sigmaTy_optRename_success optionalRenaming
                          firstMaps secondMaps))
                      rfl
                }
  | _, .boolTrue =>
      some {
        renamedType := Ty.bool
        typeEquality := rfl
        term := Term.boolTrue
      }
  | _, .boolFalse =>
      some {
        renamedType := Ty.bool
        typeEquality := rfl
        term := Term.boolFalse
      }
  | _, .boolElim (resultType := resultType)
        scrutinee thenBranch elseBranch =>
      Option.bindSome (resultType.optRename optionalRenaming)
        fun renamedResult resultMaps =>
        Option.bind (Term.optRename renamingIsCompatible scrutinee)
          fun renamedScrutinee =>
            Option.bind (Term.optRename renamingIsCompatible thenBranch)
              fun renamedThen =>
                Option.bind (Term.optRename renamingIsCompatible elseBranch)
                  fun renamedElse =>
                    some {
                      renamedType := renamedResult
                      typeEquality := resultMaps
                      term :=
                        Term.boolElim
                          (OptionalRenamedTerm.termAs renamedScrutinee rfl)
                          (OptionalRenamedTerm.termAs renamedThen resultMaps)
                          (OptionalRenamedTerm.termAs renamedElse resultMaps)
                    }
  | _, .natZero =>
      some {
        renamedType := Ty.nat
        typeEquality := rfl
        term := Term.natZero
      }
  | _, .natSucc predecessor =>
      Option.bind (Term.optRename renamingIsCompatible predecessor)
        fun renamedPredecessor =>
          some {
            renamedType := Ty.nat
            typeEquality := rfl
            term :=
              Term.natSucc
                (OptionalRenamedTerm.termAs renamedPredecessor rfl)
          }
  | _, .natRec (resultType := resultType)
        scrutinee zeroBranch succBranch =>
      Option.bindSome (resultType.optRename optionalRenaming)
        fun renamedResult resultMaps =>
        Option.bind (Term.optRename renamingIsCompatible scrutinee)
          fun renamedScrutinee =>
            Option.bind (Term.optRename renamingIsCompatible zeroBranch)
              fun renamedZero =>
                Option.bind (Term.optRename renamingIsCompatible succBranch)
                  fun renamedSucc =>
                    some {
                      renamedType := renamedResult
                      typeEquality := resultMaps
                      term :=
                        Term.natRec
                          (OptionalRenamedTerm.termAs renamedScrutinee rfl)
                          (OptionalRenamedTerm.termAs renamedZero resultMaps)
                          (OptionalRenamedTerm.termAs renamedSucc
                            (Ty.arrow_optRename_success optionalRenaming rfl
                              (Ty.arrow_optRename_success optionalRenaming
                                resultMaps resultMaps)))
                    }
  | _, .natElim (resultType := resultType)
        scrutinee zeroBranch succBranch =>
      Option.bindSome (resultType.optRename optionalRenaming)
        fun renamedResult resultMaps =>
        Option.bind (Term.optRename renamingIsCompatible scrutinee)
          fun renamedScrutinee =>
            Option.bind (Term.optRename renamingIsCompatible zeroBranch)
              fun renamedZero =>
                Option.bind (Term.optRename renamingIsCompatible succBranch)
                  fun renamedSucc =>
                    some {
                      renamedType := renamedResult
                      typeEquality := resultMaps
                      term :=
                        Term.natElim
                          (OptionalRenamedTerm.termAs renamedScrutinee rfl)
                          (OptionalRenamedTerm.termAs renamedZero resultMaps)
                          (OptionalRenamedTerm.termAs renamedSucc
                            (Ty.arrow_optRename_success optionalRenaming rfl
                              resultMaps))
                    }
  | _, .listNil (elementType := elementType) =>
      Option.bindSome (elementType.optRename optionalRenaming)
        fun renamedElement elementMaps =>
        some {
          renamedType := Ty.list renamedElement
          typeEquality :=
            Ty.list_optRename_success optionalRenaming elementMaps
          term := Term.listNil
        }
  | _, .listCons (elementType := elementType) head tail =>
      Option.bindSome (elementType.optRename optionalRenaming)
        fun renamedElement elementMaps =>
        Option.bind (Term.optRename renamingIsCompatible head)
          fun renamedHead =>
            Option.bind (Term.optRename renamingIsCompatible tail)
              fun renamedTail =>
                some {
                  renamedType := Ty.list renamedElement
                  typeEquality :=
                    Ty.list_optRename_success optionalRenaming elementMaps
                  term :=
                    Term.listCons
                      (OptionalRenamedTerm.termAs renamedHead elementMaps)
                      (OptionalRenamedTerm.termAs renamedTail
                        (Ty.list_optRename_success optionalRenaming
                          elementMaps))
                }
  | _, .listElim (elementType := elementType) (resultType := resultType)
        scrutinee nilBranch consBranch =>
      Option.bindSome (elementType.optRename optionalRenaming)
        fun renamedElement elementMaps =>
        Option.bindSome (resultType.optRename optionalRenaming)
          fun renamedResult resultMaps =>
          Option.bind (Term.optRename renamingIsCompatible scrutinee)
            fun renamedScrutinee =>
              Option.bind (Term.optRename renamingIsCompatible nilBranch)
                fun renamedNil =>
                  Option.bind (Term.optRename renamingIsCompatible consBranch)
                    fun renamedCons =>
                      some {
                        renamedType := renamedResult
                        typeEquality := resultMaps
                        term :=
                          Term.listElim
                            (OptionalRenamedTerm.termAs renamedScrutinee
                              (Ty.list_optRename_success optionalRenaming
                                elementMaps))
                            (OptionalRenamedTerm.termAs renamedNil resultMaps)
                            (OptionalRenamedTerm.termAs renamedCons
                              (Ty.arrow_optRename_success optionalRenaming
                                elementMaps
                                (Ty.arrow_optRename_success optionalRenaming
                                  (Ty.list_optRename_success optionalRenaming
                                    elementMaps)
                                  resultMaps)))
                      }
  | _, .optionNone (elementType := elementType) =>
      Option.bindSome (elementType.optRename optionalRenaming)
        fun renamedElement elementMaps =>
        some {
          renamedType := Ty.option renamedElement
          typeEquality :=
            Ty.option_optRename_success optionalRenaming elementMaps
          term := Term.optionNone
        }
  | _, .optionSome (elementType := elementType) value =>
      Option.bindSome (elementType.optRename optionalRenaming)
        fun renamedElement elementMaps =>
        Option.bind (Term.optRename renamingIsCompatible value)
          fun renamedValue =>
            some {
              renamedType := Ty.option renamedElement
              typeEquality :=
                Ty.option_optRename_success optionalRenaming elementMaps
              term :=
                Term.optionSome
                  (OptionalRenamedTerm.termAs renamedValue elementMaps)
            }
  | _, .optionMatch (elementType := elementType) (resultType := resultType)
        scrutinee noneBranch someBranch =>
      Option.bindSome (elementType.optRename optionalRenaming)
        fun renamedElement elementMaps =>
        Option.bindSome (resultType.optRename optionalRenaming)
          fun renamedResult resultMaps =>
          Option.bind (Term.optRename renamingIsCompatible scrutinee)
            fun renamedScrutinee =>
              Option.bind (Term.optRename renamingIsCompatible noneBranch)
                fun renamedNone =>
                  Option.bind (Term.optRename renamingIsCompatible someBranch)
                    fun renamedSome =>
                      some {
                        renamedType := renamedResult
                        typeEquality := resultMaps
                        term :=
                          Term.optionMatch
                            (OptionalRenamedTerm.termAs renamedScrutinee
                              (Ty.option_optRename_success optionalRenaming
                                elementMaps))
                            (OptionalRenamedTerm.termAs renamedNone resultMaps)
                            (OptionalRenamedTerm.termAs renamedSome
                              (Ty.arrow_optRename_success optionalRenaming
                                elementMaps resultMaps))
                      }
  | _, .eitherInl (leftType := leftType) (rightType := rightType) value =>
      Option.bindSome (leftType.optRename optionalRenaming)
        fun renamedLeft leftMaps =>
        Option.bindSome (rightType.optRename optionalRenaming)
          fun renamedRight rightMaps =>
          Option.bind (Term.optRename renamingIsCompatible value)
            fun renamedValue =>
              some {
                renamedType := Ty.either renamedLeft renamedRight
                typeEquality :=
                  Ty.either_optRename_success optionalRenaming leftMaps
                    rightMaps
                term :=
                  Term.eitherInl
                    (OptionalRenamedTerm.termAs renamedValue leftMaps)
              }
  | _, .eitherInr (leftType := leftType) (rightType := rightType) value =>
      Option.bindSome (leftType.optRename optionalRenaming)
        fun renamedLeft leftMaps =>
        Option.bindSome (rightType.optRename optionalRenaming)
          fun renamedRight rightMaps =>
          Option.bind (Term.optRename renamingIsCompatible value)
            fun renamedValue =>
              some {
                renamedType := Ty.either renamedLeft renamedRight
                typeEquality :=
                  Ty.either_optRename_success optionalRenaming leftMaps
                    rightMaps
                term :=
                  Term.eitherInr
                    (OptionalRenamedTerm.termAs renamedValue rightMaps)
              }
  | _, .eitherMatch (leftType := leftType) (rightType := rightType)
        (resultType := resultType) scrutinee leftBranch rightBranch =>
      Option.bindSome (leftType.optRename optionalRenaming)
        fun renamedLeft leftMaps =>
        Option.bindSome (rightType.optRename optionalRenaming)
          fun renamedRight rightMaps =>
          Option.bindSome (resultType.optRename optionalRenaming)
            fun renamedResult resultMaps =>
              Option.bind (Term.optRename renamingIsCompatible scrutinee)
                fun renamedScrutinee =>
                  Option.bind (Term.optRename renamingIsCompatible leftBranch)
                    fun renamedLeftBranch =>
                      Option.bind (Term.optRename renamingIsCompatible rightBranch)
                        fun renamedRightBranch =>
                          some {
                            renamedType := renamedResult
                            typeEquality := resultMaps
                            term :=
                              Term.eitherMatch
                                (OptionalRenamedTerm.termAs renamedScrutinee
                                  (Ty.either_optRename_success optionalRenaming
                                    leftMaps rightMaps))
                                (OptionalRenamedTerm.termAs renamedLeftBranch
                                  (Ty.arrow_optRename_success optionalRenaming
                                    leftMaps resultMaps))
                                (OptionalRenamedTerm.termAs renamedRightBranch
                                  (Ty.arrow_optRename_success optionalRenaming
                                    rightMaps resultMaps))
                          }
  | _, .refl (carrier := carrier) rawTerm =>
      Option.bindSome (carrier.optRename optionalRenaming)
        fun renamedCarrier carrierMaps =>
        Option.bindSome (rawTerm.optRename optionalRenaming)
          fun renamedRawTerm rawTermMaps =>
          some {
            renamedType := Ty.id renamedCarrier renamedRawTerm renamedRawTerm
            typeEquality :=
              Ty.id_optRename_success optionalRenaming carrierMaps rawTermMaps
                rawTermMaps
            term := Term.refl renamedRawTerm
          }
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd)
        (rightEnd := rightEnd) (resultType := resultType)
        baseCase witness =>
      Option.bindSome (carrier.optRename optionalRenaming)
        fun renamedCarrier carrierMaps =>
        Option.bindSome (leftEnd.optRename optionalRenaming)
          fun renamedLeft leftMaps =>
          Option.bindSome (rightEnd.optRename optionalRenaming)
            fun renamedRight rightMaps =>
            Option.bindSome (resultType.optRename optionalRenaming)
              fun renamedResult resultMaps =>
                Option.bind (Term.optRename renamingIsCompatible baseCase)
                  fun renamedBase =>
                    Option.bind (Term.optRename renamingIsCompatible witness)
                      fun renamedWitness =>
                        some {
                          renamedType := renamedResult
                          typeEquality := resultMaps
                          term :=
                            Term.idJ
                              (OptionalRenamedTerm.termAs renamedBase resultMaps)
                              (OptionalRenamedTerm.termAs renamedWitness
                                (Ty.id_optRename_success optionalRenaming
                                  carrierMaps leftMaps rightMaps))
                        }

/-- Strengthen a typed term by dropping the newest context variable,
when both the term and its type are independent of that variable. -/
def Term.strengthen {mode : Mode} {scope : Nat}
    {context : Ctx mode level scope} {newType : Ty level scope}
    {extendedType : Ty level (scope + 1)}
    (term : Term (context.cons newType) extendedType) :
    Option (StrengthenedTerm context extendedType) :=
  Option.map OptionalRenamedTerm.toStrengthened
    (Term.optRename (TermOptionalRenaming.unweaken context newType) term)

end LeanFX.Syntax
