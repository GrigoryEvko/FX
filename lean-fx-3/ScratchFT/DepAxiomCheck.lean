import FX1Poly.Typed.BoundedBindingTypeReducible
import FX1Poly.Typed.BoundedNeutralMember
import FX1Poly.Typed.BoundExceedsPiDischarge
import FX1Poly.Typed.WfContext
import FX1Poly.Typed.HasTypeDescClosedForms
open FX1Poly.Typed FX1Poly.Core
#print axioms WfContext.headIsType
#print axioms WfContext.tailWellFormed
#print axioms BoundExceedsPi.existsBound
#print axioms BoundExceedsPi.monotoneInBound
#print axioms HasType.toHasTypeDesc
#print axioms HasTypeDesc.toHasTypeDescPi
#print axioms IsReducibleMemberAtBounded.cumulative
#print axioms ReducibleEnvAtBounded.cons
#print axioms ReducibleEnvAtBounded.empty
