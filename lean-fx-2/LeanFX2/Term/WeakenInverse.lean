import LeanFX2.Term.Rename
import LeanFX2.Foundation.RawPartialRename.UnweakenInversion

/-! # Term/WeakenInverse — typed strengthening foundation lemmas.

The load-bearing inversion lemmas: given a typed term whose raw
projection is a weakened raw form, the typed structure is forced
to be `Term.weaken` of some inner-scope term.

## What this module ships

Three layers of inversion infrastructure, each shipped zero-axiom:

### Layer 1 — Raw inversion helpers (~250 LoC, 3 helpers shipped)

For each RawTerm constructor `C`, a helper proves: given
`RawTerm.C args = rawOrig.weaken`, `rawOrig = RawTerm.C args'` with
`args = args'.weaken` (or `.rename .lift` for binder sub-raws).

Shipped: `RawTerm.weakenInverse_var`, `RawTerm.weakenInverse_lam`,
`RawTerm.weakenInverse_app`.  Each is a structural cases on
`rawOrig` enumerating all 74 RawTerm ctors (single positive arm + 73
negative arms via `cases rawEq`).  Extensions for the other 71 raw
ctors land per-need; the proof pattern is uniform.

### Layer 2 — Typed weaken inversions at fixed raw shape (~150 LoC, 5 shipped)

Given a typed term whose raw is `RawTerm.<ctor> args` (a specific
shape), pin the typed Term ctor that produced it and extract the
inner-scope witness.

Shipped (5 canonical-form inversions):
* `Term.weakenInverse_atUnit` — `Term.unit` ↦ `Term.unit` at outer
* `Term.weakenInverse_atBoolTrue` — `Term.boolTrue` ↦ outer
* `Term.weakenInverse_atBoolFalse` — `Term.boolFalse` ↦ outer
* `Term.weakenInverse_atNatZero` — `Term.natZero` ↦ outer
* `Term.weakenInverse_atVar` — `Term.var (Fin.succ pos')` ↦ `Term.var pos'`

Each pattern: free the type index via `suffices`, run `cases`, the
single matching arm pins the inner Term ctor with HEq.rfl.

Recursive ctor inversions (lam, app, pair, etc.) require parallel
recursive sub-inversions plus careful type-equality threading; they
land per-need in follow-up commits.

### Layer 3 — Cascade construction helpers (~25 LoC, 3 shipped)

Convenience lemmas for building / projecting the eta-redex shape:

* `Term.eta_shape_construct` — builds
  `Term.app (Term.weaken functionTerm) (Term.var 0)` from
  `functionTerm`.  The load-bearing constructor for D2.5.5's typed
  eta ctors.
* `Term.weaken_var_unfolds` — `Term.weaken (Term.var pos) = Term.var
  (Fin.succ pos)` (rfl).
* `Term.weaken_app_toRaw` — `Term.weaken (Term.app f a) = Term.app
  (Term.weaken f) (Term.weaken a)` (rfl).

## Why this is the right scope for this commit

The **full universal `Term.weakenInverse`** requires 75-ctor
structural induction over `Term`, with each case doing 74-ctor raw
disambiguation on `rawOrig`.  Cross-product: ~5500-7000 LoC of
zero-axiom inversion infrastructure.  That is genuinely outside the
scope of a single commit and demands its own milestone.

The per-shape Layer 2 specializations shipped here cover the
ctors actively needed by:

* **D2.5.5 transpPi β cascade** — `lift_lam` Or.inr (eta) constructs
  `Term.app (Term.weaken functionTerm) (Term.var 0)`.  The CONSUMER
  (the typed eta ctor) builds this from a known `functionTerm`; the
  Layer 3 `Term.eta_shape_construct` gives the canonical builder.
  The INVERSION side (recognizing an eta-redex inside `Term.lam body`)
  routes through Layer 2 `Term.weakenInverse_atVar` for the argument
  and the recursive case on the function (deferred follow-up commit).
* **K12.20.U2 Reducible.cr3 typed** — same Layer 2 pattern.
* **CONVTRANS-B.* families** — Layer 2 destructors for relevant raw
  shapes (added per-need).
* **Future D2.5.6 transpSigma cascade** — pair-eta uses
  `Term.weakenInverse_atFst` / `_atSnd` per-need extensions.
* **Future K18.7 LeanKernel η reduction** — same Layer pattern at
  the FX1 layer.

## Extension protocol (for the next warrior)

Adding a Layer 1 raw inversion for `RawTerm.C`:

1. Copy `RawTerm.weakenInverse_app` template.
2. Change the positive arm to match `| C args' => ...`.
3. Update the result Sigma' to thread `args'` and the per-arg
   `.weaken` equations.
4. All other 73 arms stay as `cases rawEq`.
5. Add `#assert_no_axioms` gate.

Adding a Layer 2 typed inversion at `RawTerm.C raw shape`:

1. Copy `Term.weakenInverse_atVar` template.
2. Change the raw constraint to `RawTerm.C subRaws`.
3. The single Term ctor case is `Term.<correspondingTypedCtor> ...`.
4. Return the HEq via `HEq.rfl` (the cases pinpoints uniquely when
   the result type is forced).
5. Add `#assert_no_axioms` gate.

## Root status

Foundation infrastructure; zero axioms throughout.  All shipped
declarations elaborated by `lake build LeanFX2` and audited by
`lake build LeanFX2 LeanFX2Audit`. -/

namespace LeanFX2

/-! ## Raw-shape inversion helpers.

A constellation of small raw lemmas: given `rawOrig.weaken =
RawTerm.<ctor> args`, recover the original raw structure
`rawOrig = RawTerm.<ctor> args'` with `args` related to `args'` by
`.weaken` (or `.rename .lift` for binder sub-raws).

These discharge the raw inversion step inside each typed
`Term.weakenInverse_atX` specialization.

We avoid `simp` at the raw equation (propext-leak risk through match
compilation) and instead use `cases rawOrig` + `injection`. -/

/-- Inversion: raw weakening of any raw produces a `RawTerm.var pos`
only when the original is `RawTerm.var pos'` with `pos = Fin.succ pos'`.

Each Layer 1 helper enumerates all 74 RawTerm ctors explicitly to
maintain the strict no-wildcard discipline from
`feedback_lean_zero_axiom_match.md`.  The positive arm extracts the
inner structure via `injection`; the 73 negative arms discharge by
`cases rawEq` (constructor mismatch). -/
def RawTerm.weakenInverse_var
    {scope : Nat} {pos : Fin (scope + 1)} {rawOrig : RawTerm scope}
    (rawEq : (RawTerm.var pos) = rawOrig.weaken) :
    Σ' (pos' : Fin scope) (_ : pos = Fin.succ pos'),
      rawOrig = RawTerm.var pos' := by
  cases rawOrig with
  | var pos' =>
      have posEq : pos = Fin.succ pos' := by injection rawEq
      exact ⟨pos', posEq, rfl⟩
  | unit => cases rawEq
  | lam _ => cases rawEq
  | app _ _ => cases rawEq
  | pair _ _ => cases rawEq
  | fst _ => cases rawEq
  | snd _ => cases rawEq
  | boolTrue => cases rawEq
  | boolFalse => cases rawEq
  | boolElim _ _ _ => cases rawEq
  | natZero => cases rawEq
  | natSucc _ => cases rawEq
  | natElim _ _ _ => cases rawEq
  | natRec _ _ _ => cases rawEq
  | listNil => cases rawEq
  | listCons _ _ => cases rawEq
  | listElim _ _ _ => cases rawEq
  | optionNone => cases rawEq
  | optionSome _ => cases rawEq
  | optionMatch _ _ _ => cases rawEq
  | eitherInl _ => cases rawEq
  | eitherInr _ => cases rawEq
  | eitherMatch _ _ _ => cases rawEq
  | refl _ => cases rawEq
  | idJ _ _ => cases rawEq
  | modIntro _ => cases rawEq
  | modElim _ => cases rawEq
  | subsume _ => cases rawEq
  | interval0 => cases rawEq
  | interval1 => cases rawEq
  | intervalOpp _ => cases rawEq
  | intervalMeet _ _ => cases rawEq
  | intervalJoin _ _ => cases rawEq
  | pathLam _ => cases rawEq
  | pathApp _ _ => cases rawEq
  | glueIntro _ _ => cases rawEq
  | glueElim _ => cases rawEq
  | transp _ _ => cases rawEq
  | transpFill _ _ _ => cases rawEq
  | hcomp _ _ => cases rawEq
  | oeqRefl _ => cases rawEq
  | oeqJ _ _ => cases rawEq
  | oeqFunext _ => cases rawEq
  | oeqTrans _ _ => cases rawEq
  | idStrictRefl _ => cases rawEq
  | idStrictRec _ _ => cases rawEq
  | equivIntro _ _ => cases rawEq
  | equivApp _ _ => cases rawEq
  | equivApply _ _ => cases rawEq
  | refineIntro _ _ => cases rawEq
  | refineElim _ => cases rawEq
  | recordIntro _ => cases rawEq
  | recordProj _ => cases rawEq
  | codataUnfold _ _ => cases rawEq
  | codataDest _ => cases rawEq
  | sessionSend _ _ => cases rawEq
  | sessionRecv _ => cases rawEq
  | effectPerform _ _ => cases rawEq
  | universeCode _ => cases rawEq
  | arrowCode _ _ => cases rawEq
  | piTyCode _ _ => cases rawEq
  | sigmaTyCode _ _ => cases rawEq
  | productCode _ _ => cases rawEq
  | sumCode _ _ => cases rawEq
  | listCode _ => cases rawEq
  | optionCode _ => cases rawEq
  | eitherCode _ _ => cases rawEq
  | idCode _ _ _ => cases rawEq
  | equivCode _ _ => cases rawEq
  | cumulUpMarker _ => cases rawEq
  | idToEquiv _ => cases rawEq
  | equivCompose _ _ => cases rawEq
  | uaToEquiv _ => cases rawEq
  | pathCompose _ _ => cases rawEq

/-- Inversion: raw weakening of any raw produces a `RawTerm.lam body`
only when the original is `RawTerm.lam body'` with
`body = body'.rename RawRenaming.weaken.lift`. -/
def RawTerm.weakenInverse_lam
    {scope : Nat} {body : RawTerm (scope + 1 + 1)} {rawOrig : RawTerm scope}
    (rawEq : (RawTerm.lam body) = rawOrig.weaken) :
    Σ' (body' : RawTerm (scope + 1)) (_ : body = body'.rename RawRenaming.weaken.lift),
      rawOrig = RawTerm.lam body' := by
  cases rawOrig with
  | var _ => cases rawEq
  | unit => cases rawEq
  | lam body' =>
      have bodyEq : body = body'.rename RawRenaming.weaken.lift := by injection rawEq
      exact ⟨body', bodyEq, rfl⟩
  | app _ _ => cases rawEq
  | pair _ _ => cases rawEq
  | fst _ => cases rawEq
  | snd _ => cases rawEq
  | boolTrue => cases rawEq
  | boolFalse => cases rawEq
  | boolElim _ _ _ => cases rawEq
  | natZero => cases rawEq
  | natSucc _ => cases rawEq
  | natElim _ _ _ => cases rawEq
  | natRec _ _ _ => cases rawEq
  | listNil => cases rawEq
  | listCons _ _ => cases rawEq
  | listElim _ _ _ => cases rawEq
  | optionNone => cases rawEq
  | optionSome _ => cases rawEq
  | optionMatch _ _ _ => cases rawEq
  | eitherInl _ => cases rawEq
  | eitherInr _ => cases rawEq
  | eitherMatch _ _ _ => cases rawEq
  | refl _ => cases rawEq
  | idJ _ _ => cases rawEq
  | modIntro _ => cases rawEq
  | modElim _ => cases rawEq
  | subsume _ => cases rawEq
  | interval0 => cases rawEq
  | interval1 => cases rawEq
  | intervalOpp _ => cases rawEq
  | intervalMeet _ _ => cases rawEq
  | intervalJoin _ _ => cases rawEq
  | pathLam _ => cases rawEq
  | pathApp _ _ => cases rawEq
  | glueIntro _ _ => cases rawEq
  | glueElim _ => cases rawEq
  | transp _ _ => cases rawEq
  | transpFill _ _ _ => cases rawEq
  | hcomp _ _ => cases rawEq
  | oeqRefl _ => cases rawEq
  | oeqJ _ _ => cases rawEq
  | oeqFunext _ => cases rawEq
  | oeqTrans _ _ => cases rawEq
  | idStrictRefl _ => cases rawEq
  | idStrictRec _ _ => cases rawEq
  | equivIntro _ _ => cases rawEq
  | equivApp _ _ => cases rawEq
  | equivApply _ _ => cases rawEq
  | refineIntro _ _ => cases rawEq
  | refineElim _ => cases rawEq
  | recordIntro _ => cases rawEq
  | recordProj _ => cases rawEq
  | codataUnfold _ _ => cases rawEq
  | codataDest _ => cases rawEq
  | sessionSend _ _ => cases rawEq
  | sessionRecv _ => cases rawEq
  | effectPerform _ _ => cases rawEq
  | universeCode _ => cases rawEq
  | arrowCode _ _ => cases rawEq
  | piTyCode _ _ => cases rawEq
  | sigmaTyCode _ _ => cases rawEq
  | productCode _ _ => cases rawEq
  | sumCode _ _ => cases rawEq
  | listCode _ => cases rawEq
  | optionCode _ => cases rawEq
  | eitherCode _ _ => cases rawEq
  | idCode _ _ _ => cases rawEq
  | equivCode _ _ => cases rawEq
  | cumulUpMarker _ => cases rawEq
  | idToEquiv _ => cases rawEq
  | equivCompose _ _ => cases rawEq
  | uaToEquiv _ => cases rawEq
  | pathCompose _ _ => cases rawEq

/-- Inversion: raw weakening producing `RawTerm.app fnRaw argRaw` forces
the original to be `RawTerm.app fnRaw' argRaw'` with sub-raws weakened. -/
def RawTerm.weakenInverse_app
    {scope : Nat} {fnRaw argRaw : RawTerm (scope + 1)}
    {rawOrig : RawTerm scope}
    (rawEq : (RawTerm.app fnRaw argRaw) = rawOrig.weaken) :
    Σ' (fnRaw' : RawTerm scope) (argRaw' : RawTerm scope)
       (_ : fnRaw = fnRaw'.weaken) (_ : argRaw = argRaw'.weaken),
      rawOrig = RawTerm.app fnRaw' argRaw' := by
  cases rawOrig with
  | var _ => cases rawEq
  | unit => cases rawEq
  | lam _ => cases rawEq
  | app fnRaw' argRaw' =>
      have fnEq : fnRaw = fnRaw'.weaken := by injection rawEq
      have argEq : argRaw = argRaw'.weaken := by injection rawEq
      exact ⟨fnRaw', argRaw', fnEq, argEq, rfl⟩
  | pair _ _ => cases rawEq
  | fst _ => cases rawEq
  | snd _ => cases rawEq
  | boolTrue => cases rawEq
  | boolFalse => cases rawEq
  | boolElim _ _ _ => cases rawEq
  | natZero => cases rawEq
  | natSucc _ => cases rawEq
  | natElim _ _ _ => cases rawEq
  | natRec _ _ _ => cases rawEq
  | listNil => cases rawEq
  | listCons _ _ => cases rawEq
  | listElim _ _ _ => cases rawEq
  | optionNone => cases rawEq
  | optionSome _ => cases rawEq
  | optionMatch _ _ _ => cases rawEq
  | eitherInl _ => cases rawEq
  | eitherInr _ => cases rawEq
  | eitherMatch _ _ _ => cases rawEq
  | refl _ => cases rawEq
  | idJ _ _ => cases rawEq
  | modIntro _ => cases rawEq
  | modElim _ => cases rawEq
  | subsume _ => cases rawEq
  | interval0 => cases rawEq
  | interval1 => cases rawEq
  | intervalOpp _ => cases rawEq
  | intervalMeet _ _ => cases rawEq
  | intervalJoin _ _ => cases rawEq
  | pathLam _ => cases rawEq
  | pathApp _ _ => cases rawEq
  | glueIntro _ _ => cases rawEq
  | glueElim _ => cases rawEq
  | transp _ _ => cases rawEq
  | transpFill _ _ _ => cases rawEq
  | hcomp _ _ => cases rawEq
  | oeqRefl _ => cases rawEq
  | oeqJ _ _ => cases rawEq
  | oeqFunext _ => cases rawEq
  | oeqTrans _ _ => cases rawEq
  | idStrictRefl _ => cases rawEq
  | idStrictRec _ _ => cases rawEq
  | equivIntro _ _ => cases rawEq
  | equivApp _ _ => cases rawEq
  | equivApply _ _ => cases rawEq
  | refineIntro _ _ => cases rawEq
  | refineElim _ => cases rawEq
  | recordIntro _ => cases rawEq
  | recordProj _ => cases rawEq
  | codataUnfold _ _ => cases rawEq
  | codataDest _ => cases rawEq
  | sessionSend _ _ => cases rawEq
  | sessionRecv _ => cases rawEq
  | effectPerform _ _ => cases rawEq
  | universeCode _ => cases rawEq
  | arrowCode _ _ => cases rawEq
  | piTyCode _ _ => cases rawEq
  | sigmaTyCode _ _ => cases rawEq
  | productCode _ _ => cases rawEq
  | sumCode _ _ => cases rawEq
  | listCode _ => cases rawEq
  | optionCode _ => cases rawEq
  | eitherCode _ _ => cases rawEq
  | idCode _ _ _ => cases rawEq
  | equivCode _ _ => cases rawEq
  | cumulUpMarker _ => cases rawEq
  | idToEquiv _ => cases rawEq
  | equivCompose _ _ => cases rawEq
  | uaToEquiv _ => cases rawEq
  | pathCompose _ _ => cases rawEq

/-! ## Typed weaken inversions — at fixed raw shape. -/

variable {mode : Mode} {level scope : Nat}
variable {context : Ctx mode level scope}
variable {newType : Ty level scope}

/-! ### `weakenedTerm` raw-form rfl helpers.

When we project `Term.weaken` of an inner term, the raw form is
`innerRaw.weaken`.  These rfl-shape lemmas pin the raw form for the
`Term.app` case (the load-bearing eta-redex destructor for D2.5.5). -/

/-- `Term.weaken` of `Term.app` projects to `RawTerm.app (.weaken) (.weaken)`
at the raw level.  Pure structural rfl.  Used inside HEq witnesses. -/
theorem Term.weaken_app_toRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {newType : Ty level scope}
    {domainType codomainType : Ty level scope}
    {fnRaw argRaw : RawTerm scope}
    (functionTerm : Term context (Ty.arrow domainType codomainType) fnRaw)
    (argumentTerm : Term context domainType argRaw) :
    Term.weaken (newType := newType) (Term.app functionTerm argumentTerm) =
      Term.app (Term.weaken (newType := newType) functionTerm)
               (Term.weaken (newType := newType) argumentTerm) := rfl

/-! ## Typed weaken inversions — at fixed raw shape. -/

/-- Typed weaken inversion at the `RawTerm.unit` raw shape.

The only Term ctor producing `RawTerm.unit` raw is `Term.unit`.
Its type is `Ty.unit` at any context.  Since `Ty.unit.weaken = Ty.unit`
and `RawTerm.unit.weaken = RawTerm.unit`, the inversion at this shape
is trivial: the inner term is `Term.unit` at the outer scope. -/
def Term.weakenInverse_atUnit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {newType : Ty level scope}
    {weakenedTy : Ty level (scope + 1)}
    (weakenedTerm : Term (context.cons newType) weakenedTy RawTerm.unit) :
    Σ' (_ : weakenedTy = Ty.unit),
      HEq weakenedTerm
          (Term.weaken (newType := newType) (Term.unit (context := context))) := by
  suffices key :
      ∀ {genericTy : Ty level (scope + 1)}
        (genericTerm : Term (context.cons newType) genericTy RawTerm.unit),
        Σ' (_ : genericTy = Ty.unit),
          HEq genericTerm
              (Term.weaken (newType := newType)
                (Term.unit (context := context))) by
    exact key weakenedTerm
  intro genericTy genericTerm
  cases genericTerm
  exact ⟨rfl, HEq.rfl⟩

/-- Typed weaken inversion at the `RawTerm.boolTrue` raw shape. -/
def Term.weakenInverse_atBoolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {newType : Ty level scope}
    {weakenedTy : Ty level (scope + 1)}
    (weakenedTerm : Term (context.cons newType) weakenedTy RawTerm.boolTrue) :
    Σ' (_ : weakenedTy = Ty.bool),
      HEq weakenedTerm
          (Term.weaken (newType := newType)
            (Term.boolTrue (context := context))) := by
  suffices key :
      ∀ {genericTy : Ty level (scope + 1)}
        (genericTerm : Term (context.cons newType) genericTy RawTerm.boolTrue),
        Σ' (_ : genericTy = Ty.bool),
          HEq genericTerm
              (Term.weaken (newType := newType)
                (Term.boolTrue (context := context))) by
    exact key weakenedTerm
  intro genericTy genericTerm
  cases genericTerm
  exact ⟨rfl, HEq.rfl⟩

/-- Typed weaken inversion at the `RawTerm.boolFalse` raw shape. -/
def Term.weakenInverse_atBoolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {newType : Ty level scope}
    {weakenedTy : Ty level (scope + 1)}
    (weakenedTerm : Term (context.cons newType) weakenedTy RawTerm.boolFalse) :
    Σ' (_ : weakenedTy = Ty.bool),
      HEq weakenedTerm
          (Term.weaken (newType := newType)
            (Term.boolFalse (context := context))) := by
  suffices key :
      ∀ {genericTy : Ty level (scope + 1)}
        (genericTerm : Term (context.cons newType) genericTy RawTerm.boolFalse),
        Σ' (_ : genericTy = Ty.bool),
          HEq genericTerm
              (Term.weaken (newType := newType)
                (Term.boolFalse (context := context))) by
    exact key weakenedTerm
  intro genericTy genericTerm
  cases genericTerm
  exact ⟨rfl, HEq.rfl⟩

/-- Typed weaken inversion at the `RawTerm.natZero` raw shape. -/
def Term.weakenInverse_atNatZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {newType : Ty level scope}
    {weakenedTy : Ty level (scope + 1)}
    (weakenedTerm : Term (context.cons newType) weakenedTy RawTerm.natZero) :
    Σ' (_ : weakenedTy = Ty.nat),
      HEq weakenedTerm
          (Term.weaken (newType := newType)
            (Term.natZero (context := context))) := by
  suffices key :
      ∀ {genericTy : Ty level (scope + 1)}
        (genericTerm : Term (context.cons newType) genericTy RawTerm.natZero),
        Σ' (_ : genericTy = Ty.nat),
          HEq genericTerm
              (Term.weaken (newType := newType)
                (Term.natZero (context := context))) by
    exact key weakenedTerm
  intro genericTy genericTerm
  cases genericTerm
  exact ⟨rfl, HEq.rfl⟩

/-- Typed weaken inversion at the `RawTerm.var` raw shape (slot Fin.succ).

Given a typed term whose raw is `RawTerm.var (Fin.succ pos')` (i.e. the
weakened var of `RawTerm.var pos'`), the only Term ctor producing this
raw is `Term.var (Fin.succ pos')`.  Its type is then
`varType (context.cons newType) (Fin.succ pos') =
 (varType context pos').weaken` (by `varType`'s second arm).

We return: the term equals `Term.weaken newType (Term.var pos')` up
to HEq, with the type witness packaged in `tyEq`.

The HEq is needed because the input's type index `weakenedTy` is
existentially "the right thing" — we recover an inner `varType
context pos'` and witness `weakenedTy = (varType context pos').weaken`. -/
def Term.weakenInverse_atVar
    {pos' : Fin scope}
    {weakenedTy : Ty level (scope + 1)}
    (weakenedTerm : Term (context.cons newType) weakenedTy
                          (RawTerm.var (Fin.succ pos'))) :
    Σ' (_ : weakenedTy = (varType context pos').weaken),
      HEq weakenedTerm
          (Term.weaken (newType := newType)
            (Term.var (context := context) pos')) := by
  -- The raw is `RawTerm.var (Fin.succ pos')`; only `Term.var` produces a `.var` raw.
  -- Free the type index so cases discharges other ctors via raw mismatch.
  suffices key :
      ∀ {genericTy : Ty level (scope + 1)}
        (genericTerm : Term (context.cons newType) genericTy
                              (RawTerm.var (Fin.succ pos'))),
        Σ' (_ : genericTy = (varType context pos').weaken),
          HEq genericTerm
              (Term.weaken (newType := newType)
                (Term.var (context := context) pos')) by
    exact key weakenedTerm
  intro genericTy genericTerm
  cases genericTerm
  -- Single arm: Term.var (Fin.succ pos'); its type is varType (context.cons newType) (Fin.succ pos').
  -- By definition this equals (varType context pos').weaken.
  exact ⟨rfl, HEq.rfl⟩

/-- **D2.5.5-targeted construction lemma**: the canonical eta-shape
`Term.app (Term.weaken functionTerm) (Term.var ⟨0, _⟩)` at type
`codomainType.weaken` is built from any `functionTerm` at arrow type.

This is the **CONSTRUCTOR** for the eta-shape; the inversion (which
requires the full 75-ctor `Term.weakenInverse` infrastructure) is
deferred.  At the cascade construction site, the consumer KNOWS the
shape they're building, so the constructor lemma plus a structural
HEq are sufficient infrastructure.

The raw form is `(RawTerm.app fRaw.weaken (RawTerm.var ⟨0, _⟩))` —
the function's raw is weakened (per Term.weaken's projection), the
argument's raw is `var 0` (the new binder). -/
def Term.eta_shape_construct
    {domainType codomainType : Ty level scope}
    {fRaw : RawTerm scope}
    (functionTerm : Term context (Ty.arrow domainType codomainType) fRaw) :
    Term (context.cons domainType) codomainType.weaken
         (RawTerm.app fRaw.weaken (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)) :=
  Term.app (Term.weaken (newType := domainType) functionTerm)
           (Term.var (context := context.cons domainType)
                     ⟨0, Nat.zero_lt_succ scope⟩)

/-! ### Companion: definitional unfolding of Term.weaken on Term.var.

`Term.weaken newType (Term.var pos') = Term.var (Fin.succ pos')`
is `rfl` via `Term.rename`'s `.var` arm under `TermRenaming.weakenStep`
(whose termRenaming equation is itself `rfl`). -/

/-- `Term.weaken` of `Term.var` is definitionally `Term.var (Fin.succ pos')`.
The cast `(termRenaming pos').symm ▸ ...` in `Term.rename`'s var arm
collapses to identity because `TermRenaming.weakenStep` returns `rfl`. -/
theorem Term.weaken_var_unfolds
    {pos' : Fin scope} :
    Term.weaken (newType := newType) (Term.var (context := context) pos')
      = Term.var (context := context.cons newType) (Fin.succ pos') := rfl

end LeanFX2
