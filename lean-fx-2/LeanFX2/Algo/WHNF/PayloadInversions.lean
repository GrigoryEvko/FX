import LeanFX2.Algo.WHNF.NullaryInversions
import LeanFX2.Algo.WHNF.HeadCtorBridge

/-! # LeanFX2.Algo.WHNF.PayloadInversions — raw recovery for payload heads

For `natSucc / listCons / optionSome / eitherInl / eitherInr`,
the raw form has a payload (predecessor / head-tail / value).
Each headCtor witness gives an EXISTENTIAL: the raw is some
ctor-application with a specific payload.

These extend the no-payload lemmas in `NullaryInversions` to support
payload-bearing β/ι firings in `Term.headStep?` (M08).  The trailing
`unit` recovery rounds out the canonical-leaf set.

## Root status

Layer 3 typed-algorithm WHNF helper.  Zero-axiom under
`LeanFX2Audit`. -/

namespace LeanFX2

/-- If `someTerm.headCtor = .natSucc`, the raw is `natSucc`-shaped
for some predecessor raw. -/
theorem Term.headCtor_natSucc_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.natSucc) :
    ∃ (predRaw : RawTerm scope), raw = RawTerm.natSucc predRaw := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | nomatch bridge

/-- If `someTerm.headCtor = .listCons`, the raw is `listCons`-shaped. -/
theorem Term.headCtor_listCons_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.listCons) :
    ∃ (headRaw tailRaw : RawTerm scope), raw = RawTerm.listCons headRaw tailRaw := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | nomatch bridge

/-- If `someTerm.headCtor = .optionSome`, the raw is `optionSome`-shaped. -/
theorem Term.headCtor_optionSome_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.optionSome) :
    ∃ (valueRaw : RawTerm scope), raw = RawTerm.optionSome valueRaw := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | nomatch bridge

/-- If `someTerm.headCtor = .eitherInl`, the raw is `eitherInl`-shaped. -/
theorem Term.headCtor_eitherInl_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.eitherInl) :
    ∃ (valueRaw : RawTerm scope), raw = RawTerm.eitherInl valueRaw := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | nomatch bridge

/-- If `someTerm.headCtor = .eitherInr`, the raw is `eitherInr`-shaped. -/
theorem Term.headCtor_eitherInr_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.eitherInr) :
    ∃ (valueRaw : RawTerm scope), raw = RawTerm.eitherInr valueRaw := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | nomatch bridge

/-- If a term's `headCtor` is `unit`, its raw is `RawTerm.unit`. -/
theorem Term.headCtor_unit_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.unit) :
    raw = RawTerm.unit := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | rfl | nomatch bridge


end LeanFX2
