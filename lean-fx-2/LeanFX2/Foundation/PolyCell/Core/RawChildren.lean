import LeanFX2.Foundation.PolyCell.Core.CellChildren
/-!
# RawChildren — Decoder Output Before Certification

This file defines the raw child descriptors that payload decoders may return.
They record the sort, dimension, and scope shape declared by decoding, but they
do **not** certify the raw child as meaningful.  Certification remains the job
of the future raw-to-certified checker.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Raw child cell together with the shape claimed by a payload decoder.

The indices are declared metadata, not a proof that the raw child is accepted.
The stored raw cell is only indexed by dimension because `PolyTerm` itself is
still intentionally permissive raw syntax. -/
structure RawChildDescriptor
    (profile : PolyProfile) (cellSort : CellSort)
    (cellDimension : CellDim) (scope : Nat) where
  /-- Raw child syntax at the declared dimension. -/
  rawCell : PolyTerm profile cellDimension

namespace RawChildDescriptor

/-- Build a raw child descriptor with an externally declared shape. -/
def ofRawCell {profile : PolyProfile} {cellSort : CellSort}
    {cellDimension : CellDim} {scope : Nat}
    (rawCell : PolyTerm profile cellDimension) :
    RawChildDescriptor profile cellSort cellDimension scope where
  rawCell := rawCell

/-- The raw erasure of a descriptor is exactly its stored raw cell. -/
theorem rawCell_ofRawCell {profile : PolyProfile} {cellSort : CellSort}
    {cellDimension : CellDim} {scope : Nat}
    (rawCell : PolyTerm profile cellDimension) :
    (ofRawCell (profile := profile) (cellSort := cellSort)
      (cellDimension := cellDimension) (scope := scope) rawCell).rawCell =
      rawCell := rfl

end RawChildDescriptor

/-- Raw child descriptor expected by one child spec at one parent scope. -/
def RawChildForSpec (profile : PolyProfile) (parentScope : Nat)
    (childSpec : ChildSpec) : Type :=
  RawChildDescriptor profile childSpec.cellSort childSpec.cellDimension
    (childSpec.expectedScope parentScope)

/-- Raw descriptor spine following a child-spec list.

This is a decoder-output shape, not a certified child list.  It reuses the
generic `CellChildren` spine with `RawChildDescriptor` as the carrier. -/
def RawChildDescriptors (profile : PolyProfile) (parentScope : Nat)
    (childSpecs : List ChildSpec) : Type :=
  CellChildren (RawChildDescriptor profile) parentScope childSpecs

/-- Raw descriptor spine expected by one generator. -/
def RawChildDescriptors.forGenerator
    (profile : PolyProfile) (parentScope : Nat)
    (generatorSpec : GeneratorSpec) : Type :=
  RawChildDescriptors profile parentScope generatorSpec.childSpecs

namespace RawChildDescriptors

/-- Build raw descriptors matching the lambda generator metadata. -/
def lambda {profile : PolyProfile} {parentScope : Nat}
    (domainRaw : PolyTerm profile 0)
    (bodyRaw : PolyTerm profile 0) :
    RawChildDescriptors.forGenerator profile parentScope lambdaGeneratorSpec :=
  CellChildren.lambdaChildren
    (RawChildDescriptor.ofRawCell domainRaw)
    (RawChildDescriptor.ofRawCell bodyRaw)

/-- Build raw descriptors matching the dependent-function type metadata. -/
def piType {profile : PolyProfile} {parentScope : Nat}
    (domainRaw : PolyTerm profile 0)
    (codomainRaw : PolyTerm profile 0) :
    RawChildDescriptors.forGenerator profile parentScope piTypeGeneratorSpec :=
  CellChildren.piTypeChildren
    (RawChildDescriptor.ofRawCell domainRaw)
    (RawChildDescriptor.ofRawCell codomainRaw)

/-- Build raw descriptors matching the context-extension metadata. -/
def contextCons {profile : PolyProfile} {parentScope : Nat}
    (contextRaw : PolyTerm profile 0)
    (typeRaw : PolyTerm profile 0)
    (modeRaw : PolyTerm profile 0) :
    RawChildDescriptors.forGenerator profile parentScope contextConsGeneratorSpec :=
  CellChildren.contextConsChildren
    (RawChildDescriptor.ofRawCell contextRaw)
    (RawChildDescriptor.ofRawCell typeRaw)
    (RawChildDescriptor.ofRawCell modeRaw)

/-- Lambda raw descriptors carry exactly the lambda generator arity. -/
theorem lambda_arity_eq_generator {profile : PolyProfile} {parentScope : Nat}
    (domainRaw : PolyTerm profile 0)
    (bodyRaw : PolyTerm profile 0) :
    (lambda (parentScope := parentScope) domainRaw bodyRaw).arity =
      lambdaGeneratorSpec.arity := rfl

/-- Dependent-function raw descriptors carry exactly the generator arity. -/
theorem piType_arity_eq_generator {profile : PolyProfile} {parentScope : Nat}
    (domainRaw : PolyTerm profile 0)
    (codomainRaw : PolyTerm profile 0) :
    (piType (parentScope := parentScope) domainRaw codomainRaw).arity =
      piTypeGeneratorSpec.arity := rfl

/-- Context-extension raw descriptors carry exactly the generator arity. -/
theorem contextCons_arity_eq_generator {profile : PolyProfile}
    {parentScope : Nat}
    (contextRaw : PolyTerm profile 0)
    (typeRaw : PolyTerm profile 0)
    (modeRaw : PolyTerm profile 0) :
    (contextCons (parentScope := parentScope) contextRaw typeRaw modeRaw).arity =
      contextConsGeneratorSpec.arity := rfl

end RawChildDescriptors

end LeanFX2.Foundation.PolyCell.Core
