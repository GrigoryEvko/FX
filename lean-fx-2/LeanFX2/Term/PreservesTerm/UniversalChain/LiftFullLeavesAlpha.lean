import LeanFX2.Term.PreservesTerm.UniversalChain.LiftFullTerm

/-! # LeanFX2.Term.PreservesTerm.UniversalChain.LiftFullLeavesAlpha

Witness-builder layer for the CONVTRANS-C universal chain close-out
(#2070 — "drop the `DispatchAtom` restriction").

The headline `RawStep.par.lift_full_term` lifts a raw parallel step to
the typed layer for any source whose dispatchability is witnessed by a
`DispatchAtom`.  The close-out toward a fully universal lift needs
`DispatchAtom` witnesses to be *constructible* rather than supplied by
the caller.  This file ships the constructible fragment:

* **Atomic builders** — every closed-leaf source term (`unit`,
  `boolTrue`, `boolFalse`, `natZero`, `interval0`, `interval1`,
  `listNil`, `optionNone`, `var`) admits a `DispatchAtom` with no
  side data, so the builder is a one-liner.

* **Derived universal lifts** — combining a builder with the
  dispatcher yields a `StepParExists` for that source *without* the
  caller threading a `DispatchAtom` hypothesis.  These corollaries
  are the shape the #2070 headline consumes once the totality theorem
  enumerates the remaining (data-carrying) constructors.

Every declaration is verified zero-axiom by the matching
`#print axioms` line in `Smoke/AuditUniversalChainAlpha.lean`.
-/

namespace LeanFX2

/-! ## Atomic `DispatchAtom` builders

Each closed-leaf source term is dispatchable with no auxiliary data.
The builders make those witnesses constructible by name, so callers
need not pattern the constructor manually. -/

/-- `Term.unit` is dispatchable. -/
theorem DispatchAtom.ofUnit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    DispatchAtom (Term.unit (context := context)
                  : Term context Ty.unit (RawTerm.unit : RawTerm scope)) :=
  DispatchAtom.unit

/-- `Term.boolTrue` is dispatchable. -/
theorem DispatchAtom.ofBoolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    DispatchAtom (Term.boolTrue (context := context)
                  : Term context Ty.bool (RawTerm.boolTrue : RawTerm scope)) :=
  DispatchAtom.boolTrue

/-- `Term.boolFalse` is dispatchable. -/
theorem DispatchAtom.ofBoolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    DispatchAtom (Term.boolFalse (context := context)
                  : Term context Ty.bool (RawTerm.boolFalse : RawTerm scope)) :=
  DispatchAtom.boolFalse

/-- `Term.natZero` is dispatchable. -/
theorem DispatchAtom.ofNatZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    DispatchAtom (Term.natZero (context := context)
                  : Term context Ty.nat (RawTerm.natZero : RawTerm scope)) :=
  DispatchAtom.natZero

/-- `Term.interval0` is dispatchable. -/
theorem DispatchAtom.ofInterval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    DispatchAtom (Term.interval0 (context := context)
                  : Term context Ty.interval (RawTerm.interval0 : RawTerm scope)) :=
  DispatchAtom.interval0

/-- `Term.interval1` is dispatchable. -/
theorem DispatchAtom.ofInterval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    DispatchAtom (Term.interval1 (context := context)
                  : Term context Ty.interval (RawTerm.interval1 : RawTerm scope)) :=
  DispatchAtom.interval1

/-- `Term.listNil` is dispatchable at any element type. -/
theorem DispatchAtom.ofListNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType : Ty level scope} :
    DispatchAtom (Term.listNil (context := context) (elementType := elementType)
                  : Term context (Ty.listType elementType)
                                 (RawTerm.listNil : RawTerm scope)) :=
  DispatchAtom.listNil

/-- `Term.optionNone` is dispatchable at any element type. -/
theorem DispatchAtom.ofOptionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType : Ty level scope} :
    DispatchAtom (Term.optionNone (context := context) (elementType := elementType)
                  : Term context (Ty.optionType elementType)
                                 (RawTerm.optionNone : RawTerm scope)) :=
  DispatchAtom.optionNone

/-- `Term.var` is dispatchable at every position. -/
theorem DispatchAtom.ofVar
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (position : Fin scope) :
    DispatchAtom (Term.var (context := context) position
                  : Term context (varType context position)
                                 (RawTerm.var position)) :=
  DispatchAtom.var position

/-! ## Derived universal lifts

Combining an atomic builder with the dispatcher gives a
`StepParExists` for the source term directly — the close-out shape
that does not expose the `DispatchAtom` hypothesis. -/

/-- Universal lift for `Term.unit`. -/
theorem RawStep.par.lift_universal_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.unit : RawTerm scope) targetRaw) :
    StepParExists (Term.unit (context := context)
                   : Term context Ty.unit (RawTerm.unit : RawTerm scope))
                  targetRaw :=
  RawStep.par.lift_full_term DispatchAtom.ofUnit rawStep

/-- Universal lift for `Term.boolTrue`. -/
theorem RawStep.par.lift_universal_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.boolTrue : RawTerm scope) targetRaw) :
    StepParExists (Term.boolTrue (context := context)
                   : Term context Ty.bool (RawTerm.boolTrue : RawTerm scope))
                  targetRaw :=
  RawStep.par.lift_full_term DispatchAtom.ofBoolTrue rawStep

/-- Universal lift for `Term.boolFalse`. -/
theorem RawStep.par.lift_universal_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.boolFalse : RawTerm scope) targetRaw) :
    StepParExists (Term.boolFalse (context := context)
                   : Term context Ty.bool (RawTerm.boolFalse : RawTerm scope))
                  targetRaw :=
  RawStep.par.lift_full_term DispatchAtom.ofBoolFalse rawStep

/-- Universal lift for `Term.natZero`. -/
theorem RawStep.par.lift_universal_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.natZero : RawTerm scope) targetRaw) :
    StepParExists (Term.natZero (context := context)
                   : Term context Ty.nat (RawTerm.natZero : RawTerm scope))
                  targetRaw :=
  RawStep.par.lift_full_term DispatchAtom.ofNatZero rawStep

/-- Universal lift for `Term.interval0`. -/
theorem RawStep.par.lift_universal_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.interval0 : RawTerm scope) targetRaw) :
    StepParExists (Term.interval0 (context := context)
                   : Term context Ty.interval (RawTerm.interval0 : RawTerm scope))
                  targetRaw :=
  RawStep.par.lift_full_term DispatchAtom.ofInterval0 rawStep

/-- Universal lift for `Term.interval1`. -/
theorem RawStep.par.lift_universal_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.interval1 : RawTerm scope) targetRaw) :
    StepParExists (Term.interval1 (context := context)
                   : Term context Ty.interval (RawTerm.interval1 : RawTerm scope))
                  targetRaw :=
  RawStep.par.lift_full_term DispatchAtom.ofInterval1 rawStep

/-- Universal lift for `Term.listNil`. -/
theorem RawStep.par.lift_universal_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.listNil : RawTerm scope) targetRaw) :
    StepParExists (Term.listNil (context := context) (elementType := elementType)
                   : Term context (Ty.listType elementType)
                                  (RawTerm.listNil : RawTerm scope))
                  targetRaw :=
  RawStep.par.lift_full_term DispatchAtom.ofListNil rawStep

/-- Universal lift for `Term.optionNone`. -/
theorem RawStep.par.lift_universal_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.optionNone : RawTerm scope) targetRaw) :
    StepParExists
      (Term.optionNone (context := context) (elementType := elementType)
       : Term context (Ty.optionType elementType)
                      (RawTerm.optionNone : RawTerm scope))
      targetRaw :=
  RawStep.par.lift_full_term DispatchAtom.ofOptionNone rawStep

/-- Universal lift for `Term.var`. -/
theorem RawStep.par.lift_universal_var
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (position : Fin scope)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.var position) targetRaw) :
    StepParExists (Term.var (context := context) position
                   : Term context (varType context position)
                                  (RawTerm.var position))
                  targetRaw :=
  RawStep.par.lift_full_term (DispatchAtom.ofVar position) rawStep

end LeanFX2
