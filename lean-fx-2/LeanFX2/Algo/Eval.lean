import LeanFX2.Algo.WHNF
import LeanFX2.Algo.RawWHNF
import LeanFX2.Reduction.Step
import LeanFX2.Term.Inversion

/-! # Algo/Eval — fuel-bounded typed evaluator

```lean
def Term.headStep? (someTerm : Term ctx ty raw) :
    Option (Σ (resultRaw : RawTerm scope), Term ctx ty resultRaw)

def Term.eval (fuel : Nat) (someTerm : Term ctx ty raw) :
    Σ (resultRaw : RawTerm scope), Term ctx ty resultRaw
```

`headStep?` fires a single ι-redex at the head of the term whenever
the firing **does not require destructuring inner Term constructors**
— i.e., when the canonical scrutinee form has no payload that the
reduct depends on.

Coverage (zero-axiom subset):

| Redex                                | Fires? | Reason                          |
|--------------------------------------|--------|---------------------------------|
| `boolElim true t e   → t`            | yes    | `t` already destructured        |
| `boolElim false t e  → e`            | yes    | `e` already destructured        |
| `natElim zero z s    → z`            | yes    | `z` already destructured        |
| `natRec zero z s     → z`            | yes    | `z` already destructured        |
| `listElim nil n c    → n`            | yes    | `n` already destructured        |
| `optionMatch none n s → n`           | yes    | `n` already destructured        |

The remaining redex rules (β-app, β-Π, β-pair, succ-elim, cons-elim,
some-match, inl/inr-match, path-app beta) require **inner Term
destructuring** — e.g., `app (lam body) arg ⟶ body[arg/x]` and
`pathApp (pathLam body) interval ⟶ body[interval/i]` need to extract
`body` from the canonical head.  In Lean 4 v4.29.1, that triggers
`propext` via the dep-pattern matcher (Discipline #2 Rule 5 from
`WORKING_RULES.md`: "full enum on dep+restricted-index FAILS").
These rules are deferred to a future revision that uses Step-witness
construction or RawTerm-level reduction + subject reduction lifting
(the latter blocked on Phase 7.D — SR for arrow / non-closed types).

`headStep?` returning `none` does not mean WHNF.  It means *this
implementation cannot fire the redex zero-axiom*.  Use `Term.isWHNF`
for true WHNF classification.

`eval` iterates `headStep?` up to `fuel` times.

## Result type preserves Ty

Each ι-rule we handle has the form `eliminator scrutinee branches →
selectedBranch`, where `selectedBranch : Term context motiveType _`.
The eliminator's own Ty is also `motiveType`.  No cast needed.

## Zero-axiom

Pattern match on outer Term ctor (full enumeration to avoid wildcard
propext leak).  Dispatch on `scrutinee.headCtor` which is a flat
`Term.HeadCtor` enum projection (already proven propext-free in
`Algo/WHNF.lean`).

## Dependencies

* `Algo/WHNF.lean` — `Term.HeadCtor` + `Term.headCtor` projection
* `Reduction/Step.lean` — semantic anchor (eval witnesses Step+ later)

## Downstream

* `Pipeline.lean` — end-to-end pipeline runs eval at the end
* Future `Algo/Soundness.lean` — eval ⟹ Step+
-/

namespace LeanFX2

variable {mode : Mode} {level : Nat}

/-! ## Typed-destruct helpers — bridge raw projections to typed payloads

Each `tryDestruct<Ctor>` follows a uniform recipe:
1. Project to Option payload via the raw `<projection>?` helper.
2. On `some`, lift to the Eq witness via the iff lemma.
3. Cast the typed term to the raw-indexed shape.
4. Apply the typed destructor to extract the payload.
5. Return the typed payload (some) or fall through (none).

These let `Term.headStep?` fire payload-bearing β/ι rules
zero-axiom — the destructor + iff combo discharges the
propext-leak that direct `match rawEq:` patterns trigger. -/

/-- Try to destruct a typed `Term ctx Ty.nat raw` as a
`Term.natSucc` of a predecessor.  Returns the predecessor's
raw + typed payload, or `none` if the raw isn't natSucc-shaped. -/
def Term.tryDestructNatSucc
    {scope : Nat} {context : Ctx mode level scope} {raw : RawTerm scope}
    (someTerm : Term context Ty.nat raw) :
    Option (Σ' (predRaw : RawTerm scope), Term context Ty.nat predRaw) :=
  match witnessPred : raw.natSuccPred? with
  | some predRaw =>
      have rawIsNatSucc : raw = RawTerm.natSucc predRaw :=
        RawTerm.natSuccPred?_eq_some witnessPred
      let scrutineeAtRaw : Term context Ty.nat (RawTerm.natSucc predRaw) :=
        rawIsNatSucc ▸ someTerm
      let ⟨predTerm, _⟩ := Term.natSuccDestruct scrutineeAtRaw
      some ⟨predRaw, predTerm⟩
  | none => none

/-- Try to destruct a typed list term as a `Term.listCons` of
head + tail.  Returns the typed parts on success. -/
def Term.tryDestructListCons
    {scope : Nat} {context : Ctx mode level scope}
    {elementType : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context (Ty.listType elementType) raw) :
    Option (Σ' (headRaw tailRaw : RawTerm scope)
              (_ : Term context elementType headRaw),
              Term context (Ty.listType elementType) tailRaw) :=
  match witnessParts : raw.listConsParts? with
  | some (headRaw, tailRaw) =>
      have rawIsListCons : raw = RawTerm.listCons headRaw tailRaw :=
        RawTerm.listConsParts?_eq_some witnessParts
      let scrutineeAtRaw : Term context (Ty.listType elementType)
                                         (RawTerm.listCons headRaw tailRaw) :=
        rawIsListCons ▸ someTerm
      let ⟨headTerm, tailTerm, _⟩ := Term.listConsDestruct scrutineeAtRaw
      some ⟨headRaw, tailRaw, headTerm, tailTerm⟩
  | none => none

/-- Try to destruct a typed option term as a `Term.optionSome`. -/
def Term.tryDestructOptionSome
    {scope : Nat} {context : Ctx mode level scope}
    {elementType : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context (Ty.optionType elementType) raw) :
    Option (Σ' (valueRaw : RawTerm scope),
              Term context elementType valueRaw) :=
  match witnessValue : raw.optionSomeValue? with
  | some valueRaw =>
      have rawIsOptionSome : raw = RawTerm.optionSome valueRaw :=
        RawTerm.optionSomeValue?_eq_some witnessValue
      let scrutineeAtRaw : Term context (Ty.optionType elementType)
                                         (RawTerm.optionSome valueRaw) :=
        rawIsOptionSome ▸ someTerm
      let ⟨valueTerm, _⟩ := Term.optionSomeDestruct scrutineeAtRaw
      some ⟨valueRaw, valueTerm⟩
  | none => none

/-- Try to destruct a typed either term as a `Term.eitherInl`. -/
def Term.tryDestructEitherInl
    {scope : Nat} {context : Ctx mode level scope}
    {leftType rightType : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context (Ty.eitherType leftType rightType) raw) :
    Option (Σ' (valueRaw : RawTerm scope),
              Term context leftType valueRaw) :=
  match witnessValue : raw.eitherInlValue? with
  | some valueRaw =>
      have rawIsEitherInl : raw = RawTerm.eitherInl valueRaw :=
        RawTerm.eitherInlValue?_eq_some witnessValue
      let scrutineeAtRaw : Term context (Ty.eitherType leftType rightType)
                                         (RawTerm.eitherInl valueRaw) :=
        rawIsEitherInl ▸ someTerm
      let ⟨valueTerm, _⟩ := Term.eitherInlDestruct scrutineeAtRaw
      some ⟨valueRaw, valueTerm⟩
  | none => none

/-- Try to destruct a typed either term as a `Term.eitherInr`. -/
def Term.tryDestructEitherInr
    {scope : Nat} {context : Ctx mode level scope}
    {leftType rightType : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context (Ty.eitherType leftType rightType) raw) :
    Option (Σ' (valueRaw : RawTerm scope),
              Term context rightType valueRaw) :=
  match witnessValue : raw.eitherInrValue? with
  | some valueRaw =>
      have rawIsEitherInr : raw = RawTerm.eitherInr valueRaw :=
        RawTerm.eitherInrValue?_eq_some witnessValue
      let scrutineeAtRaw : Term context (Ty.eitherType leftType rightType)
                                         (RawTerm.eitherInr valueRaw) :=
        rawIsEitherInr ▸ someTerm
      let ⟨valueTerm, _⟩ := Term.eitherInrDestruct scrutineeAtRaw
      some ⟨valueRaw, valueTerm⟩
  | none => none

/-- Fire a single ι-redex at the head of a typed term, restricted to
the cases where the reduct does not require inner-Term destructuring
(see file docstring for the coverage table).  Returns `none` for
non-redexes AND for redexes whose firing is currently blocked on the
propext-clean Term destructuring infrastructure.

Full Term.ctor enumeration ensures no wildcard propext leak. -/
def Term.headStep? : ∀ {scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {raw : RawTerm scope},
    Term context someType raw →
    Option (Σ (resultRaw : RawTerm scope), Term context someType resultRaw)
  -- Atomic / canonical / WHNF heads — never reduce.
  | _, _, _, _, .var _ => none
  | _, _, _, _, .unit => none
  | _, _, _, _, .lam _ => none
  | _, _, _, _, .lamPi _ => none
  | _, _, _, _, .pair _ _ => none
  | _, _, _, _, .boolTrue => none
  | _, _, _, _, .boolFalse => none
  | _, _, _, _, .natZero => none
  | _, _, _, _, .natSucc _ => none
  | _, _, _, _, .listNil => none
  | _, _, _, _, .listCons _ _ => none
  | _, _, _, _, .optionNone => none
  | _, _, _, _, .optionSome _ => none
  | _, _, _, _, .eitherInl _ => none
  | _, _, _, _, .eitherInr _ => none
  | _, _, _, _, .refl _ _ => none
  | _, _, _, _, .modIntro _ => none
  | _, _, _, _, .subsume _ => none
  | _, _, _, _, .universeCode _ _ _ _ => none
  -- Cumul-up is a value (not a redex head)
  | _, _, _, _, .cumulUp _ _ _ _ _ _ => none
  -- HoTT canonical equivalence/funext refl-fragment witnesses are
  -- values (not β/ι redex heads).
  | _, _, _, _, .equivReflId _ => none
  | _, _, _, _, .funextRefl _ _ _ => none
  | _, _, _, _, .equivReflIdAtId _ _ _ _ => none
  | _, _, _, _, .funextReflAtId _ _ _ => none
  -- HoTT heterogeneous-carrier equivIntroHet is a value (canonical
  -- equivalence form, not a β/ι redex head): no head step fires.
  | _, _, _, _, .equivIntroHet _ _ => none
  -- HoTT heterogeneous-carrier uaIntroHet (Phase 12.A.B8.5b): a value
  -- (canonical path-from-equivalence form at the universe).  The future
  -- `Step.eqTypeHet` rule will fire from this ctor, but at the headStep?
  -- level we treat it as a non-redex head (mirror of equivReflIdAtId,
  -- whose Step.eqType reduction is also not yet wired into headStep?).
  | _, _, _, _, .uaIntroHet _ _ _ _ _ => none
  -- HoTT heterogeneous-carrier funextIntroHet (Phase 12.A.B8.8): a value
  -- (canonical heterogeneous-funext witness at Id-of-arrow).  The future
  -- `Step.eqArrowHet` rule will fire from this ctor, but at the headStep?
  -- level we treat it as a non-redex head (mirror of funextReflAtId).
  | _, _, _, _, .funextIntroHet _ _ _ _ => none
  -- CUMUL-2.4 typed type-code constructors (VALUE-shaped).  No β/ι
  -- redex head fires from these ctors — they are canonical type
  -- codes inhabiting `Ty.universe outerLevel`.
  | _, _, _, _, .arrowCode _ _ _ _ => none
  | _, _, _, _, .piTyCode _ _ _ _ => none
  | _, _, _, _, .sigmaTyCode _ _ _ _ => none
  | _, _, _, _, .productCode _ _ _ _ => none
  | _, _, _, _, .sumCode _ _ _ _ => none
  | _, _, _, _, .listCode _ _ _ => none
  | _, _, _, _, .optionCode _ _ _ => none
  | _, _, _, _, .eitherCode _ _ _ _ => none
  | _, _, _, _, .idCode _ _ _ _ _ => none
  | _, _, _, _, .equivCode _ _ _ _ => none
  -- Cubical interval endpoints and path lambdas are canonical values.
  -- `pathApp (pathLam body) interval` has a semantic Step.par beta
  -- rule, but headStep? does not yet fire it because extracting the
  -- typed `body` payload is the same dependent-destructor problem as
  -- β-app above.
  | _, _, _, _, .interval0 => none
  | _, _, _, _, .interval1 => none
  | _, _, _, _, .pathLam _ _ _ _ => none
  | _, _, _, _, .glueIntro _ _ _ _ => none
  -- Eliminators — fire only when the canonical scrutinee has no payload.
  | _, _, _, _, .app _ _ => none           -- β-app needs body extraction
  | _, _, _, _, .appPi _ _ => none          -- β-Π needs body extraction
  | _, _, _, _, .pathApp _ _ => none        -- path β needs body extraction
  | _, _, _, _, .glueElim _ => none         -- Glue β needs value extraction
  | _, _, _, _, .fst _ => none              -- β-pair-fst needs first extraction
  | _, _, _, _, .snd _ => none              -- β-pair-snd needs second extraction
  | _, _, _, _, .boolElim scrutinee thenBranch elseBranch =>
      let scrutineeHead := scrutinee.headCtor
      if scrutineeHead == .boolTrue then
        some ⟨_, thenBranch⟩
      else if scrutineeHead == .boolFalse then
        some ⟨_, elseBranch⟩
      else
        none
  -- Eliminator cases: fire only no-payload canonical cases for
  -- compatibility with the existing `Term.headStep?_sound` closure
  -- proof (whose `show ... from rfl` patterns expect this shape).
  -- Payload firings are SHIPPED as standalone theorems
  -- (`Term.headStep?_sound_<rule>` for natElimSucc / natRecSucc /
  -- listElimCons / optionMatchSome / eitherMatchInl / eitherMatchInr)
  -- in `Algo/Soundness.lean`.  Future work: rewrite the closure
  -- proof to dispatch via per-firing sound theorems, unblocking
  -- the full headStep? extension.
  | _, _, _, _, .natElim scrutinee zeroBranch _ =>
      let scrutineeHead := scrutinee.headCtor
      if scrutineeHead == .natZero then
        some ⟨_, zeroBranch⟩
      else
        none
  | _, _, _, _, .natRec scrutinee zeroBranch _ =>
      let scrutineeHead := scrutinee.headCtor
      if scrutineeHead == .natZero then
        some ⟨_, zeroBranch⟩
      else
        none
  | _, _, _, _, .listElim scrutinee nilBranch _ =>
      let scrutineeHead := scrutinee.headCtor
      if scrutineeHead == .listNil then
        some ⟨_, nilBranch⟩
      else
        none
  | _, _, _, _, .optionMatch scrutinee noneBranch _ =>
      let scrutineeHead := scrutinee.headCtor
      if scrutineeHead == .optionNone then
        some ⟨_, noneBranch⟩
      else
        none
  | _, _, _, _, .eitherMatch _ _ _ => none
  | _, _, _, _, .idJ _ _ => none            -- J-on-refl needs witness extraction
  | _, _, _, _, .modElim _ => none          -- needs inner extraction

/-- Fuel-bounded head reducer.  Repeatedly fires head ι-redexes via
`Term.headStep?` until either the term is non-reducible (per the
restricted coverage) or fuel runs out.  Returns the current
`(rawForm, typedTerm)` pair.

## Termination guarantees

* Every well-typed pure term has a normal form (Tait's reducibility,
  not yet proven for this kernel).
* Until SN is mechanised, fuel is essential to guarantee that
  `Term.eval` itself terminates.
* For terms with `Div` effect, fuel is the *only* reason eval ever
  returns. -/
def Term.eval {scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {raw : RawTerm scope} :
    Nat → Term context someType raw →
    Σ (resultRaw : RawTerm scope), Term context someType resultRaw
  | 0, someTerm => ⟨_, someTerm⟩
  | fuel + 1, someTerm =>
    match someTerm.headStep? with
    | some ⟨_, reducedTerm⟩ => Term.eval fuel reducedTerm
    | none => ⟨_, someTerm⟩

end LeanFX2

namespace LeanFX2.Algo

-- TODO Layer 9 + Phase 7.D: extend headStep? to β-app, β-Π, β-pair,
-- and the payload-carrying ι-rules (succ-elim, cons-elim, some-match,
-- inl/inr-match, J-on-refl, modElim-on-modIntro).  Two viable paths:
--
-- 1. Build the result via Step-witness construction (define a typed
--    one-step parallel reducer that produces a Σ pair (target,
--    Step.par source target) and project from there).  Casts route
--    through Eq.rec in the Step-rule indices.
--
-- 2. Reduce on RawTerm via existing Algo/RawWHNF, then lift the
--    raw-result back to Term via subject reduction.  Blocked on
--    Phase 7.D — current SR proofs only cover closed types
--    (Ty.nat / Ty.bool / Ty.unit).  Extending to Ty.arrow requires
--    weaken-stable preservation reasoning.
--
-- Both paths preserve zero-axiom but require non-trivial scaffolding.

end LeanFX2.Algo
