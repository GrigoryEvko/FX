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

end LengthList

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
  | .function domain codomain =>
      domain.hasRecursiveOccurrence || codomain.hasRecursiveOccurrence

/-- Is every recursive occurrence in this shape strictly positive? -/
def isStrictlyPositive : InductiveArgumentShape → Bool
  | .parameter => true
  | .recursive => true
  | .function domain codomain =>
      if domain.hasRecursiveOccurrence then
        false
      else
        codomain.isStrictlyPositive

/-- Count ordinary non-recursive argument leaves. -/
def countNonrecursiveLeaves : InductiveArgumentShape → Nat
  | .parameter => 1
  | .recursive => 0
  | .function domain codomain =>
      domain.countNonrecursiveLeaves + codomain.countNonrecursiveLeaves

/-- Count recursive argument leaves. -/
def countRecursiveLeaves : InductiveArgumentShape → Nat
  | .parameter => 0
  | .recursive => 1
  | .function domain codomain =>
      domain.countRecursiveLeaves + codomain.countRecursiveLeaves

/-- A direct recursive occurrence is strictly positive. -/
example : InductiveArgumentShape.recursive.isStrictlyPositive = true := rfl

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

end LeanFX.Syntax
