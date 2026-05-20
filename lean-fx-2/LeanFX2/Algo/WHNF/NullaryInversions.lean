import LeanFX2.Algo.WHNF.Evaluator
import LeanFX2.Algo.WHNF.HeadCtorBridge

/-! # LeanFX2.Algo.WHNF.NullaryInversions — raw recovery for nullary heads

If `term.headCtor = X`, then term's raw form is uniquely determined
by `X` for nullary canonical heads (boolTrue/False, natZero, listNil,
optionNone).  These bridge lemmas convert the Bool-level dispatch
in `Term.headStep?` back into typed-level facts about the term's
raw projection — useful for deriving Step witnesses from headStep?
behavior (Algo/Soundness, Phase 9.G).

## Root status

Layer 3 typed-algorithm WHNF helper.  Zero-axiom under
`LeanFX2Audit`. -/

namespace LeanFX2

/-- If a term's `headCtor` is `boolTrue`, its raw projection
is `RawTerm.boolTrue`.  Zero-axiom via full Term enumeration with
`nomatch` for the contradictory cases. -/
theorem Term.headCtor_boolTrue_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.boolTrue) :
    raw = RawTerm.boolTrue := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | rfl | nomatch bridge

/-- If a term's `headCtor` is `boolFalse`, its raw is `RawTerm.boolFalse`. -/
theorem Term.headCtor_boolFalse_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.boolFalse) :
    raw = RawTerm.boolFalse := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | rfl | nomatch bridge

/-- If a term's `headCtor` is `natZero`, its raw is `RawTerm.natZero`. -/
theorem Term.headCtor_natZero_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.natZero) :
    raw = RawTerm.natZero := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | rfl | nomatch bridge

/-- If a term's `headCtor` is `listNil`, its raw is `RawTerm.listNil`. -/
theorem Term.headCtor_listNil_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.listNil) :
    raw = RawTerm.listNil := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | rfl | nomatch bridge

/-- If a term's `headCtor` is `optionNone`, its raw is `RawTerm.optionNone`. -/
theorem Term.headCtor_optionNone_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.optionNone) :
    raw = RawTerm.optionNone := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | rfl | nomatch bridge

end LeanFX2
