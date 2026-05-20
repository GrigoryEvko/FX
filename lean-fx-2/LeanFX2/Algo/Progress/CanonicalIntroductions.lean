import LeanFX2.Algo.WHNF
import LeanFX2.Algo.WHNF.HeadCtorBridge
import LeanFX2.Term.Inversion
import LeanFX2.Reduction.Step.Inductive

/-! # LeanFX2.Algo.Progress.CanonicalIntroductions

Canonical-form raw inversions for value-introduction head ctors.
Given a typed Term whose `headCtor` is an introduction form
(`lam`, `pair`, `refl`, `lamPi`, `recordIntro`, `modIntro`,
`pathLam`, `glueIntro`, `refineIntro`, `codataUnfold`), extract
the raw shape `RawTerm.<ctor> ...`.

## Proof strategy - raw-routed inversion

Each lemma routes through `Term.headCtor_toRawTag`
(`Algo/WHNF/HeadCtorBridge.lean`): the single 78-arm `Term.rec` that
relates the coarsened head tag to the representative tag of the raw
projection.  Per-lemma the proof is then `cases raw` over the plain
`RawTerm` family (`RawTerm.rec`, no `Ty`/`Ctx` motive), which is
markedly cheaper to kernel-recheck than the indexed `Term.rec` that a
direct `cases someTerm` 78-arm split pays.

The introduction heads inverted here are all fixed points of
`Term.HeadCtor.toRawTag` (or, for `lamPi`, share `lam`'s raw shape),
so `headEq` + the bridge pins `raw.headCtor` to the target
tag; `cases raw` then builds the witness on the matching arm and
discharges every other arm by `RawTerm`-ctor `noConfusion` against the
bridge equation.

## Root status

Value-introduction canonical-form inversions; feed the headline
Progress proof. Zero-axiom under strict policy. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat}

/-! ## Canonical-form raw inversions (Term.headCtor -> raw shape)

If a Term's `headCtor` projection is `.lam`, then its raw is
`RawTerm.lam bodyRaw` for some `bodyRaw`.  This mirrors the
existing inversions in `Algo/WHNF.lean` for nullary canonical
heads (`boolTrue`, `boolFalse`, `natZero`, `listNil`, `optionNone`,
`unit`) plus unary canonical heads (`natSucc`, `listCons`,
`optionSome`, `eitherInl`, `eitherInr`).
-/

/-- If a term's `headCtor` is `lam`, its raw is `RawTerm.lam` of
some body raw form.  Routed through `Term.headCtor_toRawTag`: the
head tag `.lam` maps to raw tag `.lam`, so the bridge pins
`raw.headCtor = .lam`; `cases raw` builds the witness on the
`lam` arm and refutes the rest via the bridge equation. -/
theorem Term.headCtor_lam_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.lam) :
    ∃ bodyRaw : RawTerm (scope + 1), raw = RawTerm.lam bodyRaw := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | nomatch bridge

/-- If a term's `headCtor` is `pair`, its raw is `RawTerm.pair`
of two body raw forms.  Routed through `Term.headCtor_toRawTag`. -/
theorem Term.headCtor_pair_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.pair) :
    ∃ (firstRaw secondRaw : RawTerm scope),
      raw = RawTerm.pair firstRaw secondRaw := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | nomatch bridge

/-- If a term's `headCtor` is `refl`, its raw is `RawTerm.refl`
of a witness raw form.  Routed through `Term.headCtor_toRawTag`. -/
theorem Term.headCtor_refl_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.refl) :
    ∃ witnessRaw : RawTerm scope, raw = RawTerm.refl witnessRaw := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | nomatch bridge

/-- If a term's `headCtor` is `lamPi`, its raw is `RawTerm.lam`
of a body raw form.  Note: the dependent-Π lambda `Term.lamPi`
shares the surface raw shape `RawTerm.lam` with the non-dependent
`Term.lam`; the distinction lives only in the type index
(`Ty.piTy` vs `Ty.arrow`).  The headCtor projection separates
them at the flat-enum level, and `Term.HeadCtor.toRawTag` collapses
`.lamPi` back onto `.lam`, so the bridge pins `raw.headCtor =
.lam` exactly as for `Term.lam`. -/
theorem Term.headCtor_lamPi_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.lamPi) :
    ∃ bodyRaw : RawTerm (scope + 1), raw = RawTerm.lam bodyRaw := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | nomatch bridge

/-- If a term's `headCtor` is `recordIntro`, its raw is
`RawTerm.recordIntro` of a first-field raw form.  Needed by the
Progress proof for the `recordProj` case (scrutinee inversion).
Records are encoded directly via `Term.recordIntro` (single-field
placeholder); not Sigma-encoded.  Routed through
`Term.headCtor_toRawTag`. -/
theorem Term.headCtor_recordIntro_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.recordIntro) :
    ∃ firstRaw : RawTerm scope,
      raw = RawTerm.recordIntro firstRaw := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | nomatch bridge

/-- If a term's `headCtor` is `modIntro`, its raw is
`RawTerm.modIntro` of an inner raw form.  Modal-value canonical
form needed by the Progress proof for the `modElim` case.  Routed
through `Term.headCtor_toRawTag`. -/
theorem Term.headCtor_modIntro_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.modIntro) :
    ∃ innerRaw : RawTerm scope, raw = RawTerm.modIntro innerRaw := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | nomatch bridge

/-- If a term's `headCtor` is `pathLam`, its raw is `RawTerm.pathLam`
of a body raw form under one binder.  Cubical-path canonical form
needed by the Progress proof for the `pathApp` case (scrutinee
inversion).  Routed through `Term.headCtor_toRawTag`. -/
theorem Term.headCtor_pathLam_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.pathLam) :
    ∃ bodyRaw : RawTerm (scope + 1),
      raw = RawTerm.pathLam bodyRaw := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | nomatch bridge

/-- If a term's `headCtor` is `glueIntro`, its raw is
`RawTerm.glueIntro` of a base raw form and a partial raw form.
Cubical-Glue canonical form needed by the Progress proof for the
`glueElim` case (scrutinee inversion).  Routed through
`Term.headCtor_toRawTag`. -/
theorem Term.headCtor_glueIntro_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.glueIntro) :
    ∃ baseRaw partialRaw : RawTerm scope,
      raw = RawTerm.glueIntro baseRaw partialRaw := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | nomatch bridge

/-- If a term's `headCtor` is `refineIntro`, its raw is
`RawTerm.refineIntro` of a value raw form and a proof raw form.
Refinement-introduction canonical form needed by the Progress proof
for the `refineElim` case (scrutinee inversion).  Routed through
`Term.headCtor_toRawTag`. -/
theorem Term.headCtor_refineIntro_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.refineIntro) :
    ∃ valueRaw proofRaw : RawTerm scope,
      raw = RawTerm.refineIntro valueRaw proofRaw := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | nomatch bridge

/-- If a term's `headCtor` is `codataUnfold`, its raw is
`RawTerm.codataUnfold` of a state raw form and a transition raw form.
Codata-unfold canonical form needed by the Progress proof for the
`codataDest` case (scrutinee inversion).  The current raw kernel has
no codata observation β-rule, so this lemma is currently stocked for
future use when `codataDest (codataUnfold _ _)` becomes a redex; it
also rounds out the canonical-form cohort by parity with
`recordIntro` / `glueIntro` / `refineIntro`.  Routed through
`Term.headCtor_toRawTag`. -/
theorem Term.headCtor_codataUnfold_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.codataUnfold) :
    ∃ stateRaw transitionRaw : RawTerm scope,
      raw = RawTerm.codataUnfold stateRaw transitionRaw := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | nomatch bridge


end LeanFX2
