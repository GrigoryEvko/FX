namespace LeanFX.Syntax

universe firstUniverse secondUniverse thirdUniverse

theorem lengthListCongrArgTwo {firstType secondType resultType : Sort _}
    {function : firstType → secondType → resultType}
    {firstValue firstValue' : firstType}
    {secondValue secondValue' : secondType}
    (firstEquality : firstValue = firstValue')
    (secondEquality : secondValue = secondValue') :
    function firstValue secondValue =
      function firstValue' secondValue' := by
  cases firstEquality
  cases secondEquality
  rfl

/-! ## Generic inductive-family descriptions.

This file is the axiom-free substrate for FX `Ind { spec }` types
from `fx_design.md` §30.2 and Appendix H.4.  The current layer is
only data: constructor signatures, family arity, and length-indexed
parameter vectors.  Later tasks add strict-positivity and mutual-block
well-formedness checks on top of this data.
-/

/-- A small length-indexed list used for inductive parameters.

The project avoids importing a vector library so the kernel remains
self-contained and its theorem dependencies stay auditable. -/
inductive LengthList (elementType : Type firstUniverse) : Nat → Type firstUniverse
  | nil : LengthList elementType 0
  | cons : {length : Nat} →
      (head : elementType) →
      (tail : LengthList elementType length) →
      LengthList elementType (length + 1)
deriving DecidableEq

namespace LengthList

/-- Map a function over a length-indexed list. -/
def map {firstElementType : Type firstUniverse}
    {secondElementType : Type secondUniverse}
    (mapElement : firstElementType → secondElementType) :
    {length : Nat} → LengthList firstElementType length →
      LengthList secondElementType length
  | _, .nil => .nil
  | _, .cons head tail => .cons (mapElement head) (map mapElement tail)

/-- Pointwise-equal mapping functions produce equal mapped lists. -/
theorem map_congr {firstElementType : Type firstUniverse}
    {secondElementType : Type secondUniverse}
    {firstMap secondMap : firstElementType → secondElementType}
    (mapsAreEquivalent : ∀ element, firstMap element = secondMap element) :
    {length : Nat} →
      ∀ elements : LengthList firstElementType length,
        map firstMap elements = map secondMap elements
  | _, .nil => rfl
  | _, .cons head tail => by
      exact lengthListCongrArgTwo (function := LengthList.cons)
        (mapsAreEquivalent head)
        (map_congr mapsAreEquivalent tail)

/-- Mapping by identity is neutral. -/
theorem map_identity {elementType : Type firstUniverse} :
    {length : Nat} →
      ∀ elements : LengthList elementType length,
        map id elements = elements
  | _, .nil => rfl
  | _, .cons head tail => by
      exact congrArg (LengthList.cons head) (map_identity tail)

/-- Mapping composition law. -/
theorem map_compose {firstElementType : Type firstUniverse}
    {secondElementType : Type secondUniverse}
    {thirdElementType : Type thirdUniverse}
    (firstMap : firstElementType → secondElementType)
    (secondMap : secondElementType → thirdElementType) :
    {length : Nat} →
      ∀ elements : LengthList firstElementType length,
        map secondMap (map firstMap elements) =
          map (fun element => secondMap (firstMap element)) elements
  | _, .nil => rfl
  | _, .cons head tail => by
      exact congrArg (LengthList.cons (secondMap (firstMap head)))
        (map_compose firstMap secondMap tail)

/-- Append two length-indexed lists. -/
def append {elementType : Type firstUniverse} :
    {firstLength secondLength : Nat} →
      LengthList elementType firstLength →
      LengthList elementType secondLength →
      LengthList elementType (secondLength + firstLength)
  | _, _, .nil, secondElements => secondElements
  | _, _, .cons head tail, secondElements =>
      .cons head (append tail secondElements)

/-- One-element length-indexed list. -/
def singleton {elementType : Type firstUniverse}
    (element : elementType) : LengthList elementType 1 :=
  .cons element .nil

/-- Mapping distributes over append. -/
theorem map_append {firstElementType : Type firstUniverse}
    {secondElementType : Type secondUniverse}
    (mapElement : firstElementType → secondElementType) :
    {firstLength secondLength : Nat} →
      ∀ (firstElements : LengthList firstElementType firstLength)
        (secondElements : LengthList firstElementType secondLength),
        map mapElement (append firstElements secondElements) =
          append (map mapElement firstElements) (map mapElement secondElements)
  | _, _, .nil, _ => rfl
  | _, _, .cons head tail, secondElements => by
      exact congrArg (LengthList.cons (mapElement head))
        (map_append mapElement tail secondElements)

/-- A concrete vector append computation. -/
example :
    append
      (LengthList.cons 1 (LengthList.cons 2 LengthList.nil))
      (LengthList.cons 3 LengthList.nil) =
      LengthList.cons 1
        (LengthList.cons 2
          (LengthList.cons 3 LengthList.nil)) := rfl

end LengthList

/-- Plain structural lists for executable inductive-family smoke tests
that do not need an index. -/
inductive StandardList (elementType : Type firstUniverse) where
  | nil : StandardList elementType
  | cons : elementType → StandardList elementType → StandardList elementType
deriving DecidableEq

namespace StandardList

/-- Append two standard lists. -/
def append {elementType : Type firstUniverse} :
    StandardList elementType → StandardList elementType → StandardList elementType
  | .nil, secondElements => secondElements
  | .cons head tail, secondElements => .cons head (append tail secondElements)

/-- Singleton standard list. -/
def singleton {elementType : Type firstUniverse}
    (element : elementType) : StandardList elementType :=
  .cons element .nil

/-- Reverse a standard list. -/
def reverse {elementType : Type firstUniverse} :
    StandardList elementType → StandardList elementType
  | .nil => .nil
  | .cons head tail => append (reverse tail) (singleton head)

/-- Concrete list reverse computes. -/
example :
    reverse
      (StandardList.cons 1
        (StandardList.cons 2
          (StandardList.cons 3 StandardList.nil))) =
      StandardList.cons 3
        (StandardList.cons 2
          (StandardList.cons 1 StandardList.nil)) := rfl

end StandardList

/-- Natural numbers expressed through the generic inductive smoke layer. -/
inductive StandardNat where
  | zero : StandardNat
  | succ : StandardNat → StandardNat
deriving DecidableEq

namespace StandardNat

/-- Addition by recursion on the left operand. -/
def add : StandardNat → StandardNat → StandardNat
  | .zero, rightValue => rightValue
  | .succ leftValue, rightValue => .succ (add leftValue rightValue)

/-- Convert smoke natural numbers to Lean `Nat` for benchmark-sized examples. -/
def toNat : StandardNat → Nat
  | .zero => 0
  | .succ predecessor => predecessor.toNat + 1

/-- Small numeral helpers for computation smoke tests. -/
def one : StandardNat := .succ .zero

def two : StandardNat := .succ one

def three : StandardNat := .succ two

def five : StandardNat := .succ (.succ three)

/-- Concrete Nat addition computes. -/
example : add two three = five := rfl

/-- Addition result decodes to the expected Lean natural. -/
example : (add two three).toNat = 5 := rfl

end StandardNat

/-- Constructor argument shape for the generic inductive-family
framework.

The strictly-positive checker reads this as a tiny functor language:
ordinary parameters are non-recursive, `recursive` is a direct
positive occurrence of the family, and `function domain codomain`
models an arrow-shaped argument where recursive occurrences in the
domain would be negative. -/
inductive InductiveArgumentShape where
  | parameter : InductiveArgumentShape
  | recursive : InductiveArgumentShape
  | mutualRecursive : (familyIndex : Nat) → InductiveArgumentShape
  | function :
      (domain : InductiveArgumentShape) →
      (codomain : InductiveArgumentShape) →
      InductiveArgumentShape
deriving DecidableEq

namespace InductiveArgumentShape

/-- Does this argument shape contain any recursive occurrence? -/
def hasRecursiveOccurrence : InductiveArgumentShape → Bool
  | .parameter => false
  | .recursive => true
  | .mutualRecursive _ => true
  | .function domain codomain =>
      domain.hasRecursiveOccurrence || codomain.hasRecursiveOccurrence

/-- Is every recursive occurrence in this shape strictly positive? -/
def isStrictlyPositive : InductiveArgumentShape → Bool
  | .parameter => true
  | .recursive => true
  | .mutualRecursive _ => true
  | .function domain codomain =>
      if domain.hasRecursiveOccurrence then
        false
      else
        codomain.isStrictlyPositive

/-- Count ordinary non-recursive argument leaves. -/
def countNonrecursiveLeaves : InductiveArgumentShape → Nat
  | .parameter => 1
  | .recursive => 0
  | .mutualRecursive _ => 0
  | .function domain codomain =>
      domain.countNonrecursiveLeaves + codomain.countNonrecursiveLeaves

/-- Count recursive argument leaves. -/
def countRecursiveLeaves : InductiveArgumentShape → Nat
  | .parameter => 0
  | .recursive => 1
  | .mutualRecursive _ => 1
  | .function domain codomain =>
      domain.countRecursiveLeaves + codomain.countRecursiveLeaves

/-- Decidable less-than as a standalone Boolean recursion.

Using a local Boolean relation keeps the audit surface explicit and
avoids importing any order-decision machinery for mutual-block checks. -/
def isLessThan : Nat → Nat → Bool
  | 0, _ + 1 => true
  | _, 0 => false
  | candidateIndex + 1, targetCount + 1 =>
      isLessThan candidateIndex targetCount

/-- Every mutual-family reference points into the current block. -/
def hasValidMutualReferences
    (familyCount : Nat) : InductiveArgumentShape → Bool
  | .parameter => true
  | .recursive => true
  | .mutualRecursive familyIndex => isLessThan familyIndex familyCount
  | .function domain codomain =>
      domain.hasValidMutualReferences familyCount &&
        codomain.hasValidMutualReferences familyCount

/-- A direct recursive occurrence is strictly positive. -/
example : InductiveArgumentShape.recursive.isStrictlyPositive = true := rfl

/-- A mutual recursive occurrence is also positive when used directly. -/
example :
    (InductiveArgumentShape.mutualRecursive 1).isStrictlyPositive = true := rfl

/-- Recursive occurrence in a function domain is rejected. -/
example :
    (InductiveArgumentShape.function
      InductiveArgumentShape.recursive
      InductiveArgumentShape.parameter).isStrictlyPositive = false := rfl

end InductiveArgumentShape

/-- Shape of one constructor in a generic inductive family.

`nonrecursiveArgumentCount` counts ordinary argument positions.
`recursiveArgumentCount` counts strictly-positive recursive
occurrences of the family.  Task v1.38 refines this coarse shape with
a structural positivity audit. -/
structure InductiveConstructorSpec where
  constructorName : String
  nonrecursiveArgumentCount : Nat
  recursiveArgumentCount : Nat
  argumentShapes : List InductiveArgumentShape
deriving DecidableEq

namespace InductiveConstructorSpec

/-- Count non-recursive leaves across all argument shapes. -/
def countNonrecursiveLeaves : List InductiveArgumentShape → Nat
  | [] => 0
  | argumentShape :: remainingShapes =>
      argumentShape.countNonrecursiveLeaves +
        countNonrecursiveLeaves remainingShapes

/-- Count recursive leaves across all argument shapes. -/
def countRecursiveLeaves : List InductiveArgumentShape → Nat
  | [] => 0
  | argumentShape :: remainingShapes =>
      argumentShape.countRecursiveLeaves +
        countRecursiveLeaves remainingShapes

/-- Check that every argument shape is strictly positive. -/
def allArgumentsAreStrictlyPositive : List InductiveArgumentShape → Bool
  | [] => true
  | argumentShape :: remainingShapes =>
      argumentShape.isStrictlyPositive &&
        allArgumentsAreStrictlyPositive remainingShapes

/-- Check mutual references in all argument shapes. -/
def allArgumentsHaveValidMutualReferences
    (familyCount : Nat) : List InductiveArgumentShape → Bool
  | [] => true
  | argumentShape :: remainingShapes =>
      argumentShape.hasValidMutualReferences familyCount &&
        allArgumentsHaveValidMutualReferences familyCount remainingShapes

/-- Constructor arity counters agree with the declared argument shapes. -/
def hasConsistentArity (constructorSpec : InductiveConstructorSpec) : Bool :=
  constructorSpec.nonrecursiveArgumentCount ==
      countNonrecursiveLeaves constructorSpec.argumentShapes &&
    constructorSpec.recursiveArgumentCount ==
      countRecursiveLeaves constructorSpec.argumentShapes

/-- Constructor is admissible for the current v1.38 check. -/
def isStrictlyPositive (constructorSpec : InductiveConstructorSpec) : Bool :=
  constructorSpec.hasConsistentArity &&
    allArgumentsAreStrictlyPositive constructorSpec.argumentShapes

/-- Constructor is admissible inside a mutual block of `familyCount`
families. -/
def isValidInMutualBlock
    (familyCount : Nat)
    (constructorSpec : InductiveConstructorSpec) : Bool :=
  constructorSpec.isStrictlyPositive &&
    allArgumentsHaveValidMutualReferences familyCount
      constructorSpec.argumentShapes

end InductiveConstructorSpec

/-- Generic inductive-family specification.

`parameterCount` tracks uniform type parameters such as the element
type of `list` or `vec`; `indexCount` tracks family indices such as
the length index of `vec`; each constructor is given by a
constructor-spec row. -/
structure InductiveSpec where
  familyName : String
  parameterCount : Nat
  indexCount : Nat
  constructors : List InductiveConstructorSpec
deriving DecidableEq

namespace InductiveSpec

/-- Check every constructor in a family. -/
def allConstructorsAreStrictlyPositive :
    List InductiveConstructorSpec → Bool
  | [] => true
  | constructorSpec :: remainingConstructors =>
      constructorSpec.isStrictlyPositive &&
        allConstructorsAreStrictlyPositive remainingConstructors

/-- The generic v1.38 strict-positivity and arity audit. -/
def isStrictlyPositive (inductiveSpec : InductiveSpec) : Bool :=
  allConstructorsAreStrictlyPositive inductiveSpec.constructors

/-- Check all constructors against mutual-block reference bounds. -/
def allConstructorsAreValidInMutualBlock
    (familyCount : Nat) : List InductiveConstructorSpec → Bool
  | [] => true
  | constructorSpec :: remainingConstructors =>
      constructorSpec.isValidInMutualBlock familyCount &&
        allConstructorsAreValidInMutualBlock familyCount remainingConstructors

/-- Check one family inside a mutual block. -/
def isValidInMutualBlock
    (familyCount : Nat)
    (inductiveSpec : InductiveSpec) : Bool :=
  allConstructorsAreValidInMutualBlock familyCount
    inductiveSpec.constructors

/-- Boolean-like closed enum: two nullary constructors. -/
def bool : InductiveSpec where
  familyName := "bool"
  parameterCount := 0
  indexCount := 0
  constructors := [
    {
      constructorName := "False",
      nonrecursiveArgumentCount := 0,
      recursiveArgumentCount := 0,
      argumentShapes := []
    },
    {
      constructorName := "True",
      nonrecursiveArgumentCount := 0,
      recursiveArgumentCount := 0,
      argumentShapes := []
    }
  ]

/-- Natural numbers: zero plus one strictly-positive recursive argument. -/
def nat : InductiveSpec where
  familyName := "nat"
  parameterCount := 0
  indexCount := 0
  constructors := [
    {
      constructorName := "Zero",
      nonrecursiveArgumentCount := 0,
      recursiveArgumentCount := 0,
      argumentShapes := []
    },
    {
      constructorName := "Succ",
      nonrecursiveArgumentCount := 0,
      recursiveArgumentCount := 1,
      argumentShapes := [InductiveArgumentShape.recursive]
    }
  ]

/-- Lists: one uniform element parameter and recursive tail. -/
def list : InductiveSpec where
  familyName := "list"
  parameterCount := 1
  indexCount := 0
  constructors := [
    {
      constructorName := "Nil",
      nonrecursiveArgumentCount := 0,
      recursiveArgumentCount := 0,
      argumentShapes := []
    },
    {
      constructorName := "Cons",
      nonrecursiveArgumentCount := 1,
      recursiveArgumentCount := 1,
      argumentShapes := [
        InductiveArgumentShape.parameter,
        InductiveArgumentShape.recursive
      ]
    }
  ]

/-- Length-indexed vectors: one type parameter and one natural index. -/
def vec : InductiveSpec where
  familyName := "vec"
  parameterCount := 1
  indexCount := 1
  constructors := [
    {
      constructorName := "Nil",
      nonrecursiveArgumentCount := 0,
      recursiveArgumentCount := 0,
      argumentShapes := []
    },
    {
      constructorName := "Cons",
      nonrecursiveArgumentCount := 1,
      recursiveArgumentCount := 1,
      argumentShapes := [
        InductiveArgumentShape.parameter,
        InductiveArgumentShape.recursive
      ]
    }
  ]

/-- Options: one uniform element parameter. -/
def option : InductiveSpec where
  familyName := "option"
  parameterCount := 1
  indexCount := 0
  constructors := [
    {
      constructorName := "None",
      nonrecursiveArgumentCount := 0,
      recursiveArgumentCount := 0,
      argumentShapes := []
    },
    {
      constructorName := "Some",
      nonrecursiveArgumentCount := 1,
      recursiveArgumentCount := 0,
      argumentShapes := [InductiveArgumentShape.parameter]
    }
  ]

/-- Binary tagged sums: two uniform parameters. -/
def either : InductiveSpec where
  familyName := "either"
  parameterCount := 2
  indexCount := 0
  constructors := [
    {
      constructorName := "Inl",
      nonrecursiveArgumentCount := 1,
      recursiveArgumentCount := 0,
      argumentShapes := [InductiveArgumentShape.parameter]
    },
    {
      constructorName := "Inr",
      nonrecursiveArgumentCount := 1,
      recursiveArgumentCount := 0,
      argumentShapes := [InductiveArgumentShape.parameter]
    }
  ]

/-- The standard v1 inductive specs pass the structural audit. -/
example : bool.isStrictlyPositive = true := rfl

example : nat.isStrictlyPositive = true := rfl

example : list.isStrictlyPositive = true := rfl

example : vec.isStrictlyPositive = true := rfl

example : option.isStrictlyPositive = true := rfl

example : either.isStrictlyPositive = true := rfl

end InductiveSpec

/-- A mutually-recursive inductive block.  Family positions are the
indices referenced by `InductiveArgumentShape.mutualRecursive`. -/
structure MutualInductiveSpec where
  blockName : String
  families : List InductiveSpec
deriving DecidableEq

namespace MutualInductiveSpec

/-- Count families in a block without relying on list library helpers. -/
def countFamilies : List InductiveSpec → Nat
  | [] => 0
  | _ :: remainingFamilies => countFamilies remainingFamilies + 1

/-- Check every family against a known block size. -/
def allFamiliesAreValid
    (familyCount : Nat) : List InductiveSpec → Bool
  | [] => true
  | inductiveSpec :: remainingFamilies =>
      inductiveSpec.isValidInMutualBlock familyCount &&
        allFamiliesAreValid familyCount remainingFamilies

/-- The block-level v1.39 mutual-family audit. -/
def isWellFormed (mutualSpec : MutualInductiveSpec) : Bool :=
  allFamiliesAreValid (countFamilies mutualSpec.families)
    mutualSpec.families

/-- Small mutually-recursive expression/branch shape. -/
def exprBranch : MutualInductiveSpec where
  blockName := "expr_branch"
  families := [
    {
      familyName := "expr",
      parameterCount := 0,
      indexCount := 0,
      constructors := [
        {
          constructorName := "Lit",
          nonrecursiveArgumentCount := 1,
          recursiveArgumentCount := 0,
          argumentShapes := [InductiveArgumentShape.parameter]
        },
        {
          constructorName := "If",
          nonrecursiveArgumentCount := 0,
          recursiveArgumentCount := 1,
          argumentShapes := [InductiveArgumentShape.mutualRecursive 1]
        }
      ]
    },
    {
      familyName := "branch",
      parameterCount := 0,
      indexCount := 0,
      constructors := [
        {
          constructorName := "ThenElse",
          nonrecursiveArgumentCount := 0,
          recursiveArgumentCount := 2,
          argumentShapes := [
            InductiveArgumentShape.mutualRecursive 0,
            InductiveArgumentShape.mutualRecursive 0
          ]
        }
      ]
    }
  ]

/-- The sample mutual block passes positivity and reference-bounds checks. -/
example : exprBranch.isWellFormed = true := rfl

end MutualInductiveSpec

end LeanFX.Syntax
