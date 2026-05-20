import LeanFX2.Algo.WHNF
import LeanFX2.Term.Inversion
import LeanFX2.Reduction.Step.Inductive

/-! # LeanFX2.Algo.Progress.CanonicalTypeCodes

Canonical-form raw inversions for type-code head ctors.
Given a typed Term whose `headCtor` is a type-code introduction
(`universeCode`, `arrowCode`, `piTyCode`, `sigmaTyCode`,
`productCode`, `sumCode`, `listCode`, `optionCode`, `eitherCode`,
`idCode`, `equivCode`), extract the raw shape
`RawTerm.<codeCtor> ...`.

## Root status

Type-code canonical-form inversions; feed the headline Progress
proof for `cumulUp` and code-elimination cases. Zero-axiom
under strict policy. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat}

/-- Per-head-ctor target proposition collecting all eleven type-code
raw inversions into one shared shape.  For each type-code head, this
gives the existential raw shape that the public inversion theorem
below extracts; every non-type-code head maps to `True`.  Full
enumeration (no wildcard) keeps the definition propext-free under the
strict zero-axiom policy.  This is the single carrier that lets all
eleven public theorems share ONE structural `cases someTerm` (in
`Term.typeCodeRawShape_self`) rather than each performing its own
seventy-seven-arm split. -/
private def Term.typeCodeRawShape {scope : Nat} (raw : RawTerm scope) :
    Term.HeadCtor → Prop
  | .var => True
  | .unit => True
  | .lam => True
  | .app => True
  | .lamPi => True
  | .appPi => True
  | .pair => True
  | .fst => True
  | .snd => True
  | .boolTrue => True
  | .boolFalse => True
  | .boolElim => True
  | .natZero => True
  | .natSucc => True
  | .natElim => True
  | .natRec => True
  | .listNil => True
  | .listCons => True
  | .listElim => True
  | .optionNone => True
  | .optionSome => True
  | .optionMatch => True
  | .eitherInl => True
  | .eitherInr => True
  | .eitherMatch => True
  | .refl => True
  | .idJ => True
  | .oeqRefl => True
  | .oeqJ => True
  | .oeqFunext => True
  | .idStrictRefl => True
  | .idStrictRec => True
  | .modIntro => True
  | .modElim => True
  | .subsume => True
  | .interval0 => True
  | .interval1 => True
  | .intervalOpp => True
  | .intervalMeet => True
  | .intervalJoin => True
  | .pathLam => True
  | .pathApp => True
  | .glueIntro => True
  | .glueElim => True
  | .transp => True
  | .hcomp => True
  | .recordIntro => True
  | .recordProj => True
  | .refineIntro => True
  | .refineElim => True
  | .codataUnfold => True
  | .codataDest => True
  | .sessionSend => True
  | .sessionRecv => True
  | .effectPerform => True
  | .universeCode => ∃ universeLevelRaw : Nat, raw = RawTerm.universeCode universeLevelRaw
  | .cumulUp => True
  | .equivReflId => True
  | .funextRefl => True
  | .equivReflIdAtId => True
  | .funextReflAtId => True
  | .equivIntroHet => True
  | .equivApp => True
  | .uaIntroHet => True
  | .funextIntroHet => True
  | .uaToEquiv => True
  | .equivApply => True
  | .arrowCode => ∃ domainCodeRaw codomainCodeRaw : RawTerm scope, raw = RawTerm.arrowCode domainCodeRaw codomainCodeRaw
  | .piTyCode => ∃ (domainCodeRaw : RawTerm scope) (codomainCodeRaw : RawTerm (scope + 1)), raw = RawTerm.piTyCode domainCodeRaw codomainCodeRaw
  | .sigmaTyCode => ∃ (domainCodeRaw : RawTerm scope) (codomainCodeRaw : RawTerm (scope + 1)), raw = RawTerm.sigmaTyCode domainCodeRaw codomainCodeRaw
  | .productCode => ∃ firstCodeRaw secondCodeRaw : RawTerm scope, raw = RawTerm.productCode firstCodeRaw secondCodeRaw
  | .sumCode => ∃ leftCodeRaw rightCodeRaw : RawTerm scope, raw = RawTerm.sumCode leftCodeRaw rightCodeRaw
  | .listCode => ∃ elementCodeRaw : RawTerm scope, raw = RawTerm.listCode elementCodeRaw
  | .optionCode => ∃ elementCodeRaw : RawTerm scope, raw = RawTerm.optionCode elementCodeRaw
  | .eitherCode => ∃ leftCodeRaw rightCodeRaw : RawTerm scope, raw = RawTerm.eitherCode leftCodeRaw rightCodeRaw
  | .idCode => ∃ typeCodeRaw leftRaw rightRaw : RawTerm scope, raw = RawTerm.idCode typeCodeRaw leftRaw rightRaw
  | .equivCode => ∃ leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope, raw = RawTerm.equivCode leftTypeCodeRaw rightTypeCodeRaw

/-- The single shared seventy-seven-arm `cases someTerm`: every typed
term satisfies `typeCodeRawShape` at its own head ctor.  Type-code
heads land in their existential arm (witnesses read off the matched
constructor's raw fields); all other heads land in the trivial `True`
arm.  The eleven public theorems below specialise this with their
`headEq` hypothesis, paying ZERO additional case-split cost. -/
private theorem Term.typeCodeRawShape_self {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw) :
    Term.typeCodeRawShape raw someTerm.headCtor := by
  cases someTerm <;> first
    | exact ⟨_, _, _, rfl⟩
    | exact ⟨_, _, rfl⟩
    | exact ⟨_, rfl⟩
    | exact True.intro

/-- If a term's `headCtor` is `universeCode`, its raw is
`RawTerm.universeCode` of a single inner-universe level (a `Nat`).
Universe-code canonical form needed by the Progress proof for the
`cumulUp` and code-elimination cases (scrutinee inversion).  Mirrors
the single-payload pattern of `modIntro` / `optionSome` inversions but
the payload is a `Nat` (the inner universe level) rather than a
`RawTerm`.  Stocked for the future `Step.cumulUpInner` β-rule and
universe-level decoding lemmas. -/
theorem Term.headCtor_universeCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.universeCode) :
    ∃ universeLevelRaw : Nat,
      raw = RawTerm.universeCode universeLevelRaw := by
  have shape := someTerm.typeCodeRawShape_self
  rw [headEq] at shape
  exact shape

/-- If a term's `headCtor` is `arrowCode`, its raw is
`RawTerm.arrowCode` of a domain code raw form and a codomain code raw
form (both at the outer scope).  Arrow-code canonical form needed by
the Progress proof for the future arrow-code-elimination β-rules
(scrutinee inversion).  Mirrors the binary-payload pattern of
`pair` / `recordIntro` / `codataUnfold` inversions but the payloads
are SCHEMATIC raw fields (per CUMUL-2.4 VALUE-shape discipline)
rather than recursive Term children. -/
theorem Term.headCtor_arrowCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.arrowCode) :
    ∃ domainCodeRaw codomainCodeRaw : RawTerm scope,
      raw = RawTerm.arrowCode domainCodeRaw codomainCodeRaw := by
  have shape := someTerm.typeCodeRawShape_self
  rw [headEq] at shape
  exact shape

/-- If a term's `headCtor` is `piTyCode`, its raw is `RawTerm.piTyCode`
of a domain code raw form (at scope) and a codomain code raw form (at
`scope + 1`, under the Π binder).  Mirror of `arrowCode` inversion;
the codomain raw lives at scope+1 because piTyCode encodes a
DEPENDENT function type at the raw level.  Schematic-payload pattern
per CUMUL-2.4 VALUE-shape discipline. -/
theorem Term.headCtor_piTyCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.piTyCode) :
    ∃ (domainCodeRaw : RawTerm scope) (codomainCodeRaw : RawTerm (scope + 1)),
      raw = RawTerm.piTyCode domainCodeRaw codomainCodeRaw := by
  have shape := someTerm.typeCodeRawShape_self
  rw [headEq] at shape
  exact shape

/-- If a term's `headCtor` is `sigmaTyCode`, its raw is
`RawTerm.sigmaTyCode` of a domain code raw form (at scope) and a
codomain code raw form (at `scope + 1`, under the Σ binder).  Mirror
of `piTyCode` inversion; the codomain raw lives at scope+1 because
sigmaTyCode encodes a DEPENDENT pair type at the raw level (the
second component's type may depend on the first).  Schematic-payload
pattern per CUMUL-2.4 VALUE-shape discipline. -/
theorem Term.headCtor_sigmaTyCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.sigmaTyCode) :
    ∃ (domainCodeRaw : RawTerm scope) (codomainCodeRaw : RawTerm (scope + 1)),
      raw = RawTerm.sigmaTyCode domainCodeRaw codomainCodeRaw := by
  have shape := someTerm.typeCodeRawShape_self
  rw [headEq] at shape
  exact shape

/-- If a term's `headCtor` is `productCode`, its raw is
`RawTerm.productCode` of a first-component code raw form and a
second-component code raw form (both at the outer scope).
Product-type-code canonical form needed by the Progress proof for
the future product-type-code-elimination beta-rules (scrutinee
inversion).  Binary-payload pattern with both raws at outer scope
(non-dependent product); SCHEMATIC raw fields per CUMUL-2.4
VALUE-shape discipline.  Mirror of `arrowCode` inversion. -/
theorem Term.headCtor_productCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.productCode) :
    ∃ firstCodeRaw secondCodeRaw : RawTerm scope,
      raw = RawTerm.productCode firstCodeRaw secondCodeRaw := by
  have shape := someTerm.typeCodeRawShape_self
  rw [headEq] at shape
  exact shape

/-- If a term's `headCtor` is `sumCode`, its raw is `RawTerm.sumCode`
of a left-component code raw form and a right-component code raw form
(both at the outer scope; binary sum type code).  Sum-type-code
canonical form needed by the Progress proof for the future
sum-type-code-elimination beta-rules (scrutinee inversion).  Mirror
of `productCode` inversion (binary outer-scope payloads); SCHEMATIC
raw fields per CUMUL-2.4 VALUE-shape discipline. -/
theorem Term.headCtor_sumCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.sumCode) :
    ∃ leftCodeRaw rightCodeRaw : RawTerm scope,
      raw = RawTerm.sumCode leftCodeRaw rightCodeRaw := by
  have shape := someTerm.typeCodeRawShape_self
  rw [headEq] at shape
  exact shape

/-- If a term's `headCtor` is `listCode`, its raw is `RawTerm.listCode`
of a single element-type code raw form (at outer scope).  List-type-
code canonical form needed by the Progress proof for the future
list-type-code-elimination beta-rules (scrutinee inversion).  Single-
payload pattern with the raw at outer scope; SCHEMATIC raw field per
CUMUL-2.4 VALUE-shape discipline.  Mirror of single-payload
inversions like `optionSome` but the payload is a SCHEMATIC raw
(rather than a recursive Term child). -/
theorem Term.headCtor_listCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.listCode) :
    ∃ elementCodeRaw : RawTerm scope,
      raw = RawTerm.listCode elementCodeRaw := by
  have shape := someTerm.typeCodeRawShape_self
  rw [headEq] at shape
  exact shape

/-- If a term's `headCtor` is `optionCode`, its raw is
`RawTerm.optionCode` of a single element-type code raw form (at outer
scope).  Option-type-code canonical form needed by the Progress proof
for the future option-type-code-elimination beta-rules (scrutinee
inversion).  Mirror of `listCode` inversion (single outer-scope
payload); SCHEMATIC raw field per CUMUL-2.4 VALUE-shape discipline. -/
theorem Term.headCtor_optionCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.optionCode) :
    ∃ elementCodeRaw : RawTerm scope,
      raw = RawTerm.optionCode elementCodeRaw := by
  have shape := someTerm.typeCodeRawShape_self
  rw [headEq] at shape
  exact shape

/-- If a term's `headCtor` is `eitherCode`, its raw is
`RawTerm.eitherCode` of a left-component code raw and a
right-component code raw (both at the outer scope).  Either-type-code
canonical form needed by the Progress proof for the future
either-type-code-elimination beta-rules (scrutinee inversion).
Mirror of `sumCode` / `productCode` inversions (binary outer-scope
payloads); SCHEMATIC raw fields per CUMUL-2.4 VALUE-shape
discipline. -/
theorem Term.headCtor_eitherCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.eitherCode) :
    ∃ leftCodeRaw rightCodeRaw : RawTerm scope,
      raw = RawTerm.eitherCode leftCodeRaw rightCodeRaw := by
  have shape := someTerm.typeCodeRawShape_self
  rw [headEq] at shape
  exact shape

/-- If a term's `headCtor` is `idCode`, its raw is `RawTerm.idCode` of
a type code raw and two endpoint raws (left and right) at outer scope
(identity type code with three payloads: typeCodeRaw, leftRaw,
rightRaw).  Identity-type-code canonical form needed by the Progress
proof for the future identity-type-code-elimination beta-rules
(scrutinee inversion).  Ternary-payload pattern with all three raws
at outer scope; SCHEMATIC raw fields per CUMUL-2.4 VALUE-shape
discipline. -/
theorem Term.headCtor_idCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.idCode) :
    ∃ typeCodeRaw leftRaw rightRaw : RawTerm scope,
      raw = RawTerm.idCode typeCodeRaw leftRaw rightRaw := by
  have shape := someTerm.typeCodeRawShape_self
  rw [headEq] at shape
  exact shape

/-- If a term's `headCtor` is `equivCode`, its raw is
`RawTerm.equivCode` of a left-type code raw and a right-type code raw
(both at the outer scope).  Equivalence-type-code canonical form
needed by the Progress proof for the future
equivalence-type-code-elimination beta-rules (scrutinee inversion).
Mirror of `eitherCode` / `sumCode` / `productCode` / `arrowCode`
inversions (binary outer-scope payloads); SCHEMATIC raw fields per
CUMUL-2.4 VALUE-shape discipline.  Closes the type-code subset of
M05's canonical-form cohort. -/
theorem Term.headCtor_equivCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.equivCode) :
    ∃ leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope,
      raw = RawTerm.equivCode leftTypeCodeRaw rightTypeCodeRaw := by
  have shape := someTerm.typeCodeRawShape_self
  rw [headEq] at shape
  exact shape


end LeanFX2
