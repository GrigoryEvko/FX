# kernel-sprint.md

## Cubical + 2LTT + HOTT + Lean Kernel Verification + Cross-Theory Bridges

### A 9-Day Total Sprint Plan for lean-fx-2

> "If you can prove something, it's not frontier anymore."

---

# Section 0 — Mission Statement

## 0.1 What we are building

Over 9 contiguous days of focused agentic work, lean-fx-2 graduates from
"intrinsic dependently-typed kernel with raw-aware Term + closed-type
SR + typed Tait-Martin-Löf chain" to:

A **strict zero-axiom** dependently-typed graded modal type theory with:

1. **Higher Observational Type Theory** (Pujet-Tabareau 2022, Sterling et al. 2024)
   set-level. Equality is a *reducing* type-former; funext and univalence
   are *definitional* — `Eq Type A B ↦ Equiv A B` by reduction rule.
2. **Cubical** type theory primitives (interval, paths, comp, transp, Glue)
   sufficient for syntactic path manipulation.
3. **2LTT** (Annenkov–Capriotti–Kraus) outer/inner stratification with
   `◇ ⊣ □` adjunction; cohesive `♭ ⊣ ◇ ⊣ □ ⊣ ♯` adjoint chain.
4. **All 21 graded dimensions** (FX type theory, Wood/Atkey 2022 corrected
   Lam rule rejecting Atkey 2018 attack).
5. **Refinement types** with decidable predicates + SMT cert placeholder.
6. **Effect handlers** with single-shot continuations.
7. **Linear session types** with full duality.
8. **Codata with productivity** via Later modality.
9. **All 7 HITs**: Quot, propTrunc, setTrunc, S¹, suspension, pushout, coequalizer.
10. **Surface frontend complete** with M01+M02 lex/parse roundtrip + elab
    soundness theorem.
11. **Lean 4 kernel meta-verification over FX1**: a faithful encoding of Lean's
    12-ctor expression syntax + 8 reduction rules + `HasType` typing relation,
    with `LeanFX2.FX1.LeanKernel.check_sound` proven zero-axiom after
    `FX1.check_sound` — reducing Lean's TCB for the modeled fragment from
    "trust the C++ kernel" to "trust lean-fx-2's machine-verified FX1
    meta-theory".
12. **Cross-theory bridges**: provable equivalences between cubical Path,
    observational Id, modal-projected variants, plus conservativity proofs
    establishing theory-relative-faithful-translation.

## 0.2 What zero-axiom means here

Per `AXIOMS.md` Layer K/M/E policy, lean-fx-2 commits to:

* No `propext` in any kernel theorem (use `IsClosedTy`-based machinery + 
  observational reduction at h-prop level instead).
* No `Quot.sound` (HITs constructed via observational quotient with definitional
  reduction).
* No `Classical.choice` (constructive throughout — OEq + cubical paths give us
  enough computational structure).
* No `funext` axiom (HOTT delivers it as a definitional reduction).
* No `Univalence` postulate (HOTT delivers it as `def Univalence := rfl`).
* No `K` rule (intentionally reject — would block higher-dimensional structure).
* No `sorry` (durable; transient `sorry` only allowed during in-flight edits,
  with audit gate enforcing zero before commit).

The `#print axioms` of EVERY kernel declaration must report
"does not depend on any axioms". This is enforced by `Tools/AuditAll.lean`
running ~500 `#assert_no_axioms` calls per build.

## 0.2.1 Metaplan overlay: rich layer vs trusted root

`kernel-metaplan.md` is normative for trusted-computing-base claims. This
sprint still builds the existing lean-fx-2 rich kernel, but a feature being
implemented in the rich kernel does not automatically make it part of the
minimal trusted root.

The trust stack is:

```text
LeanFX2 rich layer
  Existing Ty / RawTerm / Term / Step / Conv / Graded / HoTT / Cubical code.
  This is where Day 1-7 feature work lands first.

FX1
  Minimal Lean-like lambda-Pi kernel.
  This is the ergonomic self-hosting target and the substrate for Lean-in-FX.

FX0
  MM0-like first-order certificate checker.
  This is the eventual skeptical root verifier.
```

Every new module or theorem must be classified with one of these root-status
labels:

```text
Root-FX1
  Part of the minimal lambda-Pi kernel and covered by FX1.check_sound.

LeanKernel-FX1
  Part of the Lean-kernel reimplementation over FX1.

FX-rich
  Existing expressive lean-fx-2 layer. Zero-axiom, but not minimal-root trusted.

Bridge
  Translation/soundness connection between the rich layer and FX1/FX0.

FX0-root
  First-order certificate checker layer.

Scaffold
  Syntax, file layout, or documentation without load-bearing theorem.

Deferred
  Explicitly not claimed.
```

Day 2 and Day 3 may continue before FX1.check_sound is complete. Their output
is classified as `FX-rich` unless an explicit `encode_*_sound` theorem promotes
the corresponding fragment to `Bridge` or `Root-FX1`. This avoids a later
rewrite: the rich primitives are "fired in" first, then justified through the
FX1 bridge when the minimal checker is ready.

The Lean kernel reimplementation is no longer a direct Day 8 layer over the
full rich kernel. It targets `LeanFX2.FX1.LeanKernel`, and it is blocked on
FX1/Core syntax, substitution, typing, reduction, and checker soundness.

## 0.3 Acceptance criteria for v1.0

A green build with the following invariants:

* `lake build LeanFX2` exit code 0.
* `lake build LeanFX2.Smoke.AuditAll` reports zero axioms across all
  declarations in scope.
* `axiom Univalence` is DELETED from the source tree.
* `axiom` keyword does NOT appear in any kernel file (excluding documentation
  text that mentions it for didactic purposes).
* `sorry` does NOT appear in any kernel file (durable check).
* Every Day 2+ primitive has a root-status label from §0.2.1.
* `FX1.check_sound` typechecks zero-axiom before any Lean-in-FX claim is made.
* `LeanFX2.FX1.LeanKernel.check_sound` typechecks zero-axiom OR a documented
  gap is filed with a local reproducer and an upstream Lean issue if the gap is
  in Lean's reference behavior.
* `Bridge.PathToId.equiv` is a zero-axiom theorem proving the cubical-
  observational identity-type bridge.
* All 95 currently-pending tasks in TaskList resolved (some via shipping the
  feature, others via documenting it as v1.1+ deferred).
* `MIGRATION.md` updated: `lean-fx → lean-fx.deprecated`,
  `lean-fx-2 → lean-fx`, parent project imports updated.
* `ROADMAP.md` Phases 0–15 marked COMPLETE.
* Git tag `v1.0` placed at the final commit.

## 0.4 What this plan is NOT

This plan does NOT commit to:

* H-groupoid level coherence in HOTT (set-level only for v1.0; higher
  truncation levels are v1.1).
* Full CCHM cofibration lattice (we ship boundary cofibrations only —
  `i = i0`, `i = i1`; general face lattice is v1.1).
* Multi-shot effect continuations (single-shot only; multi-shot is v1.1).
* SMT external recheck (Decidable predicates only at v1.0; SMT recheck
  via external solver is v1.1).
* Pipeline parser handling 100% of fx_grammar.md (we target the canonical
  fragment; full grammar is incrementally added in v1.1+).
* Higher-rank polymorphism beyond rank-2 (rank-N is v1.1).
* Full v3.x cubical computational univalence WITH cubical-style canonicity
  (we use HOTT for univalence canonicity; cubical paths are syntactic).

These cuts are intentional and documented. v1.0 is "everything that is
possible and beneficial in 9 days of focused agentic work."

## 0.5 Reading order for this document

* Section 1: bottom-to-top architecture (each layer described, with what
  depends on it).
* Section 2: top-to-bottom dependency analysis (each goal's prerequisites).
* Section 3: comprehensive pitfall catalog (25+ known issues + mitigations).
* Section 4: risk register (probabilistic risks + impact + mitigation).
* Section 5: day-by-day execution plan (granular sub-tasks per day), including
  the FX1 trust-spine interlock.
* Section 6: cut order if behind schedule.
* Section 7: per-day acceptance criteria.
* Section 8: v1.0 manifest (what ships).
* Section 9: post-v1.0 roadmap (what's deferred).

---

# Section 1 — Bottom-to-Top Architecture

## 1.0 Trust spine below the rich kernel

The rich lean-fx-2 kernel remains the feature implementation layer. The minimal
root is introduced underneath it, not by replacing it in-place.

### 1.0.1 FX1/Core

`LeanFX2/FX1/Core` is a minimal Lean-like lambda-Pi kernel. It starts smaller
than Lean's real kernel:

```lean
namespace LeanFX2.FX1

inductive Name where
  | anonymous
  | str (prefix : Name) (part : String)
  | num (prefix : Name) (index : Nat)

inductive Level where
  | zero
  | succ (base : Level)
  | max (left right : Level)
  | imax (left right : Level)
  | param (name : Name)

inductive Expr where
  | bvar (index : Nat)
  | sort (level : Level)
  | const (name : Name)
  | pi (domain body : Expr)
  | lam (domain body : Expr)
  | app (function argument : Expr)

end LeanFX2.FX1
```

FX1/Core intentionally omits free variables, metavariables, let expressions,
literals, metadata, projections, inductives, quotient primitives, proof
irrelevance, eta, unsafe declarations, partial declarations, and opaque
declarations until the smaller core has preservation and checker soundness.

Allowed host imports for FX1/Core are restricted to `prelude` and
`Init.Prelude` unless a later line-item justifies an exception. Forbidden host
dependencies include `Lean`, `Std`, `Classical`, `Quot`, `propext`,
`noncomputable`, `unsafe`, `partial`, `opaque` proof shortcuts, `extern`,
`implemented_by`, `sorry`, `admit`, `sorryAx`, and tactic-heavy automation.

### 1.0.2 FX1 metatheory gates

FX1/Core does not become trusted merely because it is small. It needs:

* scope checking;
* weakening;
* renaming;
* substitution;
* substitution identity and composition;
* renaming/substitution interaction;
* beta substitution;
* environment and context well-formedness;
* beta and delta preservation;
* conversion soundness;
* WHNF soundness;
* executable checker soundness.

The root theorem is:

```lean
theorem FX1.check_sound :
    FX1.check environment context expression = some typeExpression ->
    FX1.HasType environment context expression typeExpression
```

No feature counts as `Root-FX1` until it is covered by this theorem or by a
separate theorem reducing it to the covered fragment.

### 1.0.3 Rich-layer bridge

Existing `Ty`, `RawTerm`, `Term`, `Step`, `Conv`, HoTT, cubical, graded,
refinement, effect, session, and codata modules are bridged into FX1 by
translation:

```lean
def encodeTy :
    LeanFX2.Ty level scope -> FX1.Expr

def encodeRawTerm :
    LeanFX2.RawTerm scope -> FX1.Expr

def encodeCtx :
    LeanFX2.Ctx mode level scope -> FX1.Context

theorem encode_term_sound :
    LeanFX2.Term context typeExpression rawExpression ->
    FX1.HasType environment
      (encodeCtx context)
      (encodeRawTerm rawExpression)
      (encodeTy typeExpression)
```

The bridge is incremental: variables, unit, Pi/lambda/app, universe codes,
identity, declared rich constants, then rich constructors with real
definitions. A rich primitive moves through:

```text
declared -> typed -> computational -> encoded-sound -> checker-sound -> FX0-certified
```

Only `checker-sound` and `FX0-certified` are root-trust statuses.

## 1.1 Layer 0: Foundation

The ground floor. No upward dependencies; everything else builds on this.

### 1.1.1 Mode (orientation flag)

`Foundation/Mode.lean` defines five modes:

```
inductive Mode
  | strict           -- intensional MLTT, decidable Ty equality, no path/oeq reduction
  | observational    -- HOTT inner-set-level, OEq reduces structurally
  | univalent        -- HOTT inner + cubical paths for syntactic path manipulation
  | cohesiveFlat     -- ♭ A : crisp/discrete subspace
  | cohesiveSharp    -- ♯ A : codiscrete subspace
```

Why five and not three:

* `strict` is the outer 2LTT mode. It does NOT have univalence. `Ty.id` does
  NOT reduce here — `Ty.id` is freely-generated MLTT-style. This mode is
  essential for hardware specs, decidable equality, and outer-layer
  meta-reasoning where univalence would be unsound.
* `observational` is the inner 2LTT mode at h-set level. `Ty.id` reduces
  structurally per type former. `Eq Nat zero zero ↝ Ty.unit`, etc.
* `univalent` adds cubical path syntax on top of observational. Useful for
  programs that reason about specific paths (composition, inverse, ap).
  At type level: `Eq Type A B ↦ Equiv A B` (HOTT) AND
  `Path Type A B ≃ Equiv A B` (cubical, derived).
* `cohesiveFlat` and `cohesiveSharp` are advanced modalities for cohesive
  homotopy type theory. Reserved for v1.0 if budget permits; otherwise → v1.1.

Mode lives at the `Ctx` level (existing convention). Term constructors carry
`{mode : Mode}` as implicit; Lean infers it from context's type.

Mode-changing constructors:
* `Term.modIntro` takes inner-mode `Term innerCtx innerType innerRaw` and
  produces outer-mode `Term outerCtx (Ty.modal box innerType.lift) ...`.
  The Ctx changes mode at the same time.
* `Term.modElim`, `Term.subsume` analogously.

### 1.1.2 Universe levels

`Foundation/Universe.lean` defines the cumulative universe hierarchy:

```
inductive UniverseLevel
  | zero
  | succ (l : UniverseLevel)
  | max (l1 l2 : UniverseLevel)
  | imax (l1 l2 : UniverseLevel)         -- imax l 0 = 0; otherwise = max l v
  -- No level polymorphism in v1.0; param/mvar reserved for v1.1
```

Decidable equality. Decidable `≤`. Cumulativity `Ty l ⊆ Ty (l+1)` is
expressed as a `Conv` rule, NOT a `Ty` constructor (cumulativity-as-ctor
historically broke our build per
`feedback_lean_cumul_subst_mismatch.md`).

The `Ty.universe (lvl : UniverseLevel)` ctor explicitly indexes by level.
A type lives at `Ty (succ lvl) scope` if it inhabits universe `lvl`.

### 1.1.3 Interval (cubical primitive)

`Foundation/Interval.lean`:

```
inductive Interval : Type
  | i0 : Interval
  | i1 : Interval
  deriving DecidableEq, Repr
```

Operations as functions (not constructors):

```
def Interval.opp : Interval → Interval         -- 1 - i
def Interval.meet : Interval → Interval → Interval  -- i ∧ j (min)
def Interval.join : Interval → Interval → Interval  -- i ∨ j (max)
```

Algebraic laws as theorems (~10 total, all `cases <;> rfl` zero-axiom):
involution of opp, idempotence of meet/join, commutativity, associativity,
distributivity of meet over join.

### 1.1.4 Cofibration (face lattice)

`Foundation/Cofib.lean` defines the boundary face lattice:

```
inductive BoundaryCofib : Type
  | atZero      -- i = i0 only
  | atOne       -- i = i1 only  
  | atBoth      -- i = i0 ∨ i = i1
  | atNeither   -- never holds (for trivial composition)
```

Sufficient for `ua` via Glue (which only needs boundary cofibs).
General face lattice (CCHM-style) is v1.1.

### 1.1.5 Ty extensions (~17 ctors)

`Foundation/Ty.lean` extended:

Existing ctors (preserved):
* `unit`, `bool`, `nat`, `arrow`, `piTy`, `sigmaTy`, `id`, `tyVar`,
  `listType`, `optionType`, `eitherType`, `universe`

New ctors:
* `interval` — at universe 0 only, no value-level introduction beyond intervalLit
* `path (carrier : Ty level scope) (left right : RawTerm scope)` — cubical Path
* `glue (A : Ty level scope) (cofib : BoundaryCofib) (T equiv : RawTerm scope)`
  — Glue type for ua-via-Glue
* `oeq (A : Ty level scope) (left right : RawTerm scope)` — alias for `id` in
  observational/univalent mode; reduces by HOTT rules
* `idStrict (A : Ty level scope) (left right : RawTerm scope)` — strict
  intensional id, valid in `strict` mode only, freely-generated
* `equiv (A B : Ty level scope)` — equivalence type, Σ f, isContr (fiber f);
  separate ctor for clean OEq reduction at Type
* `refine (carrier : Ty level scope) (predicate : RawTerm (scope+1))` — T{P}
* `record (fields : List (Ident × Ty level scope))` — first-class records
* `codata (head : Ty level scope) (observations : List Observation)` —
  corecursive with explicit observation list
* `session (protocol : SessionProtocol)` — linear session types
* `effect (carrier : Ty level scope) (effects : EffectRow)` — T with eff
* `modal (modality : Modality) (inner : Ty level scope)` — modality applied to type
* `empty` — the empty type, Bot, used by HOTT for failed equality cases

Pitfall: `modal` ctor needs `Modality` defined before Ty. We forward-declare
`Modality` in Layer 0a as an opaque type; the actual Modality structure is in
Layer 7. This creates a stratification: Ty.modal is parametric in Modality
without knowing its internals.

### 1.1.6 RawTerm extensions (~40 new ctors)

`Foundation/RawTerm.lean` extended:

Existing ctors (preserved):
* `var, lam, app, pair, fst, snd, unit, boolTrue, boolFalse,
   boolElim, natZero, natSucc, natElim, natRec,
   listNil, listCons, listElim, optionNone, optionSome, optionMatch,
   eitherInl, eitherInr, eitherMatch,
   refl, idJ, modIntro, modElim, subsume`

New ctors (cubical):
* `pathLam (body : RawTerm (scope+1))` — λi. body
* `pathApp (path : RawTerm scope) (point : Interval)` — p @ i
* `pathRefl (carrier : RawTerm scope) (witness : RawTerm scope)` — refl-as-path
* `transp (typeFamily : RawTerm (scope+1)) (start : Interval) (term : RawTerm scope)`
  — transport along a type family
* `comp (typeFamily : RawTerm (scope+1)) (cofib : BoundaryCofib) (partial base : RawTerm scope)`
  — composition (CCHM-style boundary cofibs only)
* `hcomp (cofib : BoundaryCofib) (partial base : RawTerm scope)`
  — homogeneous composition
* `glueIntro (A : RawTerm scope) (witness partial : RawTerm scope)`
  — glue introduction
* `unglue (witness : RawTerm scope)`
  — glue elimination
* `intervalLit (i : Interval)` — literal interval

New ctors (HOTT-specific, mostly derivable but useful as syntax):
* `oeqRefl (witness : RawTerm scope)` — observational refl
* `oeqJ (motive baseCase witness : RawTerm scope)` — observational J
* `oeqTransp (motive baseCase pathProof : RawTerm scope)` — derivable but useful

New ctors (refinement):
* `refineIntro (witness predicate : RawTerm scope)` — T{P} introduction
* `refineExtract (refined : RawTerm scope)` — T{P} → T projection

New ctors (records):
* `recordIntro (fields : List (Ident × RawTerm scope))` — record literal
* `recordProj (record : RawTerm scope) (field : Ident)` — field access

New ctors (codata):
* `codataUnfold (head : RawTerm scope) (observations : List (Ident × RawTerm scope))`
* `codataObserve (codata : RawTerm scope) (observation : Ident)`

New ctors (sessions):
* `sessionSend (channel value : RawTerm scope)`
* `sessionRecv (channel : RawTerm scope)`
* `sessionBranch (channel : RawTerm scope) (branches : List (Tag × RawTerm scope))`
* `sessionSelect (channel : RawTerm scope) (tag : Tag)`
* `sessionEnd (channel : RawTerm scope)`

New ctors (effects):
* `effectPerform (operation : RawTerm scope)`
* `effectHandle (body : RawTerm scope) (handlers : List (Op × RawTerm (scope+2)))`
  — handlers take continuation + value as bound vars

New ctors (strict equality):
* `reflStrict (witness : RawTerm scope)` — strict intensional refl
* `idStrictJ (motive baseCase witness : RawTerm scope)` — J for strict id

Pitfall: 40 new ctors × 5 files (RawTerm + 2 substitution + 2 reduction) =
200 changes. Mitigation: scripted templating; one ctor at a time with
green build between each.

### 1.1.7 Substitution machinery extension

`Foundation/RawSubst.lean`:
* `RawTerm.rename` extended with one arm per new ctor (40 new arms).
* `RawTermSubst.subst` extended analogously.
* `RawTermSubst.lift` — automatically extends if rename/subst extend.

`Foundation/Subst.lean`:
* `Ty.subst` extended for new type formers (path, glue, oeq, idStrict,
  equiv, refine, record, codata, session, effect, modal, empty,
  interval).

Each new ctor's substitution arm is structurally recursive. Termination
by `sizeOf`. All zero-axiom by exhaustive case analysis with no
wildcards.

## 1.2 Layer 1: Term

`Term.lean` adds typed Term constructors mirroring RawTerm. The Term type is:

```
inductive Term : ∀ {mode : Mode} {level scope : Nat} (context : Ctx mode level scope),
    Ty level scope → RawTerm scope → Type
```

Each new ctor is a typed analog. Examples:

```
| pathLam {bodyType : Ty level (scope+1)} {bodyRaw : RawTerm (scope+1)}
    (body : Term (context.cons Ty.interval) bodyType bodyRaw) :
    Term context (Ty.path bodyType.subst0_at_i0_endpoint ...
                          bodyType.subst0_at_i1_endpoint ...)
                 (RawTerm.pathLam bodyRaw)

| pathApp {carrier left right} {pathRaw}
    (path : Term context (Ty.path carrier left right) pathRaw)
    (point : Interval) :
    Term context carrier (RawTerm.pathApp pathRaw point)
```

Pitfall: `pathLam`'s type indices reference the body's type at endpoints.
This requires substituting `Ty.interval` with `i0`/`i1` in the body's type.
We define `Ty.subst0_interval_endpoint` as a Layer 0 helper.

### 1.2.1 Mode-restriction in Term ctors

Some ctors are mode-restricted at the type level:

* `Term.refl` works in `observational` or `univalent` modes (HOTT id).
* `Term.reflStrict` works in `strict` mode only.
* `Term.pathLam`, `pathApp`, `transp`, `comp`, `glueIntro`, `unglue` work in
  `univalent` mode only.
* `Term.modIntro` is mode-changing (takes one mode, produces another).

Mode constraints expressed as `Ctx.mode = X` premises in the constructor
signature. Type checking enforces mode discipline structurally.

### 1.2.2 Term/Rename, Subst, Pointwise, ToRaw

All extended for new ctors. The `Term.toRaw_X = rfl` pattern continues to hold
because every Term constructor's RawTerm output is the matching RawTerm
constructor — by indexing.

Pitfall: parametric ctors at different scope (like pathLam's body at scope+1)
need careful index handling in Subst. Mitigation: existing `Subst.singleton`
+ raw-aware Term design handles this; the pattern is identical to existing
`piTy`/`sigmaTy`.

## 1.3 Layer 2: Reduction

`Reduction/Step.lean` extended with ~80 new Step constructors covering all
reduction rules across cubical, HOTT, modal, refinement, records, codata,
sessions, effects.

### 1.3.1 Step rules: cubical β

```
| betaPathApp (body : Term ... bodyType bodyRaw) (point : Interval) :
    Step (Term.pathApp (Term.pathLam body) point)
         (body.subst0_interval point)

| betaPathReflApp (carrier witness) (point : Interval) :
    Step (Term.pathApp (Term.pathRefl carrier witness) point)
         (... reconstruct typed term from witness ...)

| pathLamBody : Step body body' →
    Step (Term.pathLam body) (Term.pathLam body')

| pathAppPath : Step path path' →
    Step (Term.pathApp path i) (Term.pathApp path' i)
```

### 1.3.2 Step rules: transport

```
| transpRefl (constantPath : Term ... constantPathRaw) (term) :
    -- transp on a constant family is identity
    Step (Term.transp constantPath start term) term

| transpPi (...) :
    -- transp through Π reduces to pointwise transport
    Step (Term.transp (pathLam (Π_type ...)) start f)
         (pathLam (fun a => transp B (f.app (transp A.opp a))))

| transpSigma : similar
| transpPath : path-of-path composition rule
| transpNat / transpBool / transpUnit : identity (closed type)
| transpListType / transpOption / transpEither : pointwise
| transpRecord : field-wise
| transpRefine : preserves predicate
```

12 transp rules total. Each is a Step ctor + a `Step._eq_betaTransp` lemma
giving the equation form. Termination via `sizeOf typeFamily` decreasing
through Π/Σ projections.

### 1.3.3 Step rules: HOTT OEq reductions

This is the headline of HOTT — equality reduces structurally per type former:

```
| eqNatZeroZero :
    Step (Ty.id Ty.nat (RawTerm.natZero) (RawTerm.natZero))
         Ty.unit  -- (this is at the Type level, see Pitfall O2)

| eqNatSuccSucc (m n : RawTerm scope) :
    -- Eq Nat (succ m) (succ n) ↦ Eq Nat m n
    Step (Ty.id Ty.nat (RawTerm.natSucc m) (RawTerm.natSucc n))
         (Ty.id Ty.nat m n)

| eqNatZeroSucc (n : RawTerm scope) :
    Step (Ty.id Ty.nat RawTerm.natZero (RawTerm.natSucc n))
         Ty.empty

| eqNatSuccZero (m : RawTerm scope) :
    Step (Ty.id Ty.nat (RawTerm.natSucc m) RawTerm.natZero)
         Ty.empty

| eqBoolEq (b : Bool) :
    Step (Ty.id Ty.bool (b-as-RawTerm) (b-as-RawTerm))
         Ty.unit

| eqBoolDiff (b1 b2 : Bool) (h : b1 ≠ b2) :
    Step (Ty.id Ty.bool (b1-as-RawTerm) (b2-as-RawTerm))
         Ty.empty

| eqArrow (A B : Ty level scope) (f g : RawTerm scope) :
    -- Eq (A → B) f g ↦ Π x:A, Eq B (f x) (g x)  -- funext FREE
    Step (Ty.id (Ty.arrow A B) f g)
         (Ty.piTy A (Ty.id B (f.app (RawTerm.var 0)) (g.app (RawTerm.var 0))))

| eqPi : analogous for dependent Π
| eqSigma (A B) (a1 b1 a2 b2) :
    -- Eq (Σ A B) (a1, b1) (a2, b2) ↦ Σ (p : Eq A a1 a2), Eq (B a2) (transp B p b1) b2
    Step (Ty.id (Ty.sigmaTy A B) (RawTerm.pair a1 b1) (RawTerm.pair a2 b2))
         (Ty.sigmaTy (Ty.id A a1 a2)
                     (Ty.id (B[a2/0]) (transp...) b2))

| eqType (A B : Ty (level+1) scope) :
    -- Eq Type A B ↦ Equiv A B  -- UNIVALENCE DEFINITIONAL
    Step (Ty.id (Ty.universe lvl) A B)
         (Ty.equiv A B)

| eqList : pointwise on length-matched lists
| eqOption : matched ctors
| eqEither : matched ctors
| eqRecord : field-wise
| eqCodata : observation-wise (set-level coinduction)
```

~15 OEq reduction rules, each generating a `_eq_betaOEq` lemma.

Pitfall O2 (from earlier obstacle catalog): OEq reductions are at the *Type*
level. They reduce `Ty.id A x y` to a different Ty. This is a Conv-level
phenomenon, used through `Conv.fromStep` + `Term.castTargetType` to coerce
between Ty representations.

This means `Term.refl Nat zero : Term ctx (Ty.id Ty.nat 0 0) (RawTerm.refl 0)`
exists, AND there's a Conv proof that `Ty.id Ty.nat 0 0 = Ty.unit`, so the
refl term is convertible to a `Term.unit` value. The kernel's two-Ty Conv
shape handles this.

### 1.3.4 Step rules: Glue

```
| betaUnglueGlue (a : Term ...) :
    Step (Term.unglue (Term.glueIntro a)) a

| betaGlueAtZero (cofib : BoundaryCofib) (...) :
    -- glueIntro at i=0 reduces to applying the equivalence
    Step (Term.glueIntro [cofib = atZero] a)
         (... e.fwd a ...)
```

6 Glue reduction rules covering boundary cases.

### 1.3.5 Step rules: refinement, records, codata, sessions, effects, modal

```
-- Refinement
| refineExtractIntro :
    Step (Term.refineExtract (Term.refineIntro witness predicate))
         witness

-- Records
| recordProjIntro (field : Ident) (fields : List (Ident × ...)) :
    Step (Term.recordProj (Term.recordIntro fields) field)
         (lookup-field-by-name fields field)

-- Codata
| codataObserveUnfold (obs : Ident) :
    Step (Term.codataObserve (Term.codataUnfold ... observations) obs)
         (lookup-observation observations obs)

-- Sessions
| sessionSendBeta (channel value) :
    Step (Term.sessionSend channel value) (Term.sessionEnd channel)
| sessionRecvBeta (channel) :
    Step (Term.sessionRecv channel) (... pair (received-value, channel-after) ...)
| sessionBranchSelect (...) :
    Step (Term.sessionBranch (Term.sessionSelect channel tag) branches)
         (lookup-branch-by-tag branches tag)

-- Effects
| effectHandleReturn (value handlers ret-clause) :
    Step (Term.effectHandle value handlers)
         (apply-return-clause ret-clause value)
| effectHandleOp (op handlers k-applied) :
    Step (Term.effectHandle (Term.effectPerform op) handlers)
         (... apply matching handler with k = surrounding handle ...)

-- Modal
| modIntroElim :
    Step (Term.modElim (Term.modIntro innerTerm)) innerTerm
| modElimIntro (modalTerm) :
    -- η for modality
    Step (Term.modIntro (Term.modElim modalTerm)) modalTerm
```

~25 additional Step rules.

### 1.3.6 ParRed, RawPar, Compat

Each new Step rule needs:
* A `Step.par` analog (parallel reduction allowing simultaneous redex
  reduction).
* A `RawStep.par` analog at raw level.
* Compatibility lemmas: `rename` and `subst` preserve `Step.par`.

This is mechanical but voluminous: 80 Step rules × 3 propagations = 240
new entries across `ParRed.lean` + `RawPar.lean` + `Compat.lean`.

Mitigation: scripted generation. Each new Step ctor follows the standard
pattern (cong rules use existing mapStep-like abstractions; β/ι rules
have their RawPar analog with the same redex pattern).

## 1.4 Layer 2.5: General Subject Reduction

CRITICAL LAYER. Without this, we cannot ship Conv cong rules generically.

`Foundation/Ty.lean` adds:

```
inductive IsClosedTy : ∀ {level scope : Nat}, Ty level scope → Prop
  | unit : IsClosedTy Ty.unit
  | bool : IsClosedTy Ty.bool
  | nat : IsClosedTy Ty.nat
  | empty : IsClosedTy Ty.empty
  | interval : IsClosedTy Ty.interval
  | arrow : IsClosedTy A → IsClosedTy B → IsClosedTy (Ty.arrow A B)
  | listType : IsClosedTy A → IsClosedTy (Ty.listType A)
  | optionType : IsClosedTy A → IsClosedTy (Ty.optionType A)
  | eitherType : IsClosedTy A → IsClosedTy B → IsClosedTy (Ty.eitherType A B)
  | record : (∀ field ∈ fields, IsClosedTy field.type) → IsClosedTy (Ty.record fields)
  -- piTy, sigmaTy, id, path, oeq NOT closed (depend on bound vars / raw)
  -- equiv NOT closed (depends on inner types' closure)
  -- modal NOT closed in this sense (depends on Modality)
  -- refine NOT closed (predicate has bound var)
  | universe : IsClosedTy (Ty.universe lvl)  -- universe is closed
```

Decidable: `instance : DecidablePred IsClosedTy`.

`Term/SubjectReduction.lean` adds:

```
theorem Step.preserves_isClosedTy
    {sourceTerm : Term ctx sourceType sourceRaw}
    {targetTerm : Term ctx targetType targetRaw}
    (someStep : Step sourceTerm targetTerm)
    (sourceClosed : IsClosedTy sourceType) :
    sourceType = targetType
  -- Proof: induction on someStep.
  -- Each Step ctor either preserves type structurally (cong rules)
  -- or reduces via subst0 of a closed type (β rules, where subst0 of
  -- closed type is identity). The IsClosedTy hypothesis gives subst0
  -- invariance.

theorem StepStar.preserves_isClosedTy : analogous
```

This unblocks:
* M06 (arrow SR): `IsClosedTy (Ty.arrow A B)` when both A and B are closed
* M07 (parametric SR): listType, optionType, eitherType, record at closed
  inner types
* All Conv cong rules: convertibility of subterms lifts to convertibility
  of the whole, via SR-preservation through the chain

After Layer 2.5 ships, Conv cong rules become 5-line proofs that obtain the
chain pair, lift via mapStep, reconstruct the outer Term — all type-checked
because SR guarantees the intermediate terms have the right type.

### 1.4.1 Conv cong rules unblocked

```
theorem Conv.app_cong (h_fn : Conv funA funB) (h_arg : Conv argA argB) :
    Conv (Term.app funA argA) (Term.app funB argB)
  -- proof: compose chains via mapStep + cd_lemma diamond

theorem Conv.lam_cong (h_body : Conv bodyA bodyB) :
    Conv (Term.lam bodyA) (Term.lam bodyB)

theorem Conv.idJ_baseCase_cong (h : Conv baseA baseB) :
    Conv (Term.idJ baseA witness) (Term.idJ baseB witness)
  -- previously blocked; now provable via SR + mapStep

theorem Conv.pathLam_cong, Conv.transp_cong, Conv.glueIntro_cong, ...
  -- ~25 cong rules total
```

## 1.5 Layer 3: Confluence

`Confluence/Cd.lean`, `CdLemma.lean`, `Diamond.lean`, `ChurchRosser.lean`,
`CanonicalForm.lean` — all extended for new ctors.

Each new Step ctor needs a `Term.cd` case:
* Cong rules: cd descends recursively (5-line cases)
* β rules: cd produces the reduct (10-line cases)
* OEq reductions: cd handles type-level reduction (cleanly, since OEq is
  type-level not term-level — no overlap with term β/ι)

`CdLemma` extension: ~30 new cases.

`Diamond` auto-extends provided cd is correct.

`ChurchRosser` (Tait-Martin-Löf chain) — verify still holds with new ctors;
typically auto-extends from cd.

`CanonicalForm` — extend for new closed types (refine, record at closed
inner; codata observed; session at terminal state).

## 1.6 Layer 4: Cubical Path Machinery

`Cubical/Path.lean` builds derived path operations on top of Layer 0-3:

* `Path.refl A x := pathLam (fun _ => x)` — constant path
* `Path.inv : Path A x y → Path A y x := pathLam (fun i => p @ (i.opp))`
* `Path.compose : Path A x y → Path A y z → Path A x z := comp [...] ...`
* `Path.ap (f : A → B) : Path A x y → Path B (f x) (f y)`
* `Path.transport : Path Type A B → A → B`

`Cubical/Composition.lean` — comp + hcomp + transp (already in Layer 2; this
file collects derived theorems).

`Cubical/Transport.lean` — transport lemmas: transport of refl, transport
along compose, transport along inv.

`Cubical/Glue.lean` — Glue construction:
* `Glue A φ T e` : Glue type
* `glue : (cofib-aware construction)` 
* `unglue : Glue A φ T e → A`
* β/η rules from Layer 2

`Cubical/Ua.lean` — ua via Glue:
```
def ua {A B : Ty (lvl+1) scope} (e : Term ctx (Ty.equiv A B) eRaw) :
    Term ctx (Ty.path Ty.universe (RawTerm-of-A) (RawTerm-of-B)) (uaRaw e)
  := pathLam (fun i => Term.glueIntro [i = i0 ↦ A; i = i1 ↦ B; e applies] ...)
```

ua_β as a Conv-equality (set-level computational univalence):
```
theorem ua_β (e : Equiv A B) (x : A) :
    Conv (Term.transp (ua e) i0 x) (e.fwd x)
  -- proof: 6 sub-lemmas via Glue β + transp Glue rule
```

## 1.7 Layer 5: HOTT Equality

`HoTT/OEq.lean` — observational equality machinery:

* `Ty.id` reductions (already in Layer 2 Step) collected as theorems
* `Eq.refl A x : Term ctx (Ty.id A x x) (RawTerm.refl x)` (already
  Layer 1)
* `Eq.J : motive → Term ctx (Ty.id A x y) raw → Term ctx (motive y) ...`
  — derived from idJ + OEq reductions
* `Eq.transport : (motive : A → Type) → Term ctx (Ty.id A x y) p →
   motive x → motive y` — the workhorse
* `Eq.funext : (∀ a, Eq B (f a) (g a)) → Eq (A → B) f g`
  — DEFINITIONAL via `eqArrow` reduction; `Eq.funext h := h` (literally)
* `Eq.propext : (P ↔ Q) → Eq Prop P Q` for h-prop P, Q — derivable from
  HOTT reduction at h-prop level

`HoTT/HIT/Spec.lean` — HIT specifications:
```
structure HITSpec where
  pointCtors : List PointCtorSpec
  pathCtors : List PathCtorSpec  -- path ctors carry path-eq witness
```

`HoTT/HIT/Eliminator.lean` — generic dependent eliminator:
```
def HIT.rec (motive : HIT → Type) 
    (pointCases : ...) (pathCases : ...) : ∀ h : HIT, motive h
```

`HoTT/HIT/Examples.lean` — concrete HITs:
* `Quot R` — quotient of A by relation R; no Quot.sound axiom
* `propTrunc A := ∥A∥` — propositional truncation
* `setTrunc A := ∥A∥₀` — set truncation (h-level 2)
* `S¹ := base + loop : Path _ base base` — circle
* `suspension A := north + south + meridian : A → Path _ north south`
* `pushout f g := inl + inr + glue` — pushout
* `coequalizer f g := point + path` — coequalizer

Each HIT is a kernel inductive with computational paths. The path
constructors compute as expected via OEq reduction.

## 1.8 Layer 6: Equivalence + Univalence

`HoTT/Equivalence.lean`:
* `IsContr A := Σ x : A, ∀ y : A, Eq A x y` — contractible type
* `Fiber f y := Σ x, Eq B (f x) y` — fiber of f over y
* `IsEquiv f := ∀ y, IsContr (Fiber f y)` — equivalence
* `Equiv A B := Σ f : A → B, IsEquiv f` — full equivalence type
* `idEquiv : Equiv A A`
* `Equiv.compose : Equiv A B → Equiv B C → Equiv A C`
* `Equiv.inverse : Equiv A B → Equiv B A`
* Functoriality + groupoid laws as theorems

`HoTT/Univalence.lean` — REWRITTEN as definitional theorem:
```
-- BEFORE (Phase 6):
-- axiom Univalence : Equiv A B → Path Type A B

-- AFTER (Phase 12 — Day 3 in this sprint):
def Univalence (A B : Ty (lvl+1) scope) :
    Conv (Ty.id (Ty.universe lvl) A B) (Ty.equiv A B) :=
  Conv.fromStep Step.eqType  -- direct from HOTT reduction

def ua : Equiv A B → Term ctx (Ty.id (Ty.universe lvl) (RawTerm-of-A)
                                                       (RawTerm-of-B)) raw :=
  fun e => Term.castTargetType (Conv.sym Univalence) e

theorem axiomUnivalence_DELETED :
  -- The placeholder previously held a postulate; now it's a theorem.
  -- Verify via: #print axioms ua  reports zero.
  True := trivial
```

The `axiom Univalence` is DELETED from the source tree.

## 1.9 Layer 7: 2LTT Modal

`Modal/TwoLevel.lean`:

```
structure Modality where
  fromMode : Mode
  toMode : Mode
  -- coherence laws: identity, composition

def Modality.box : Modality :=
  { fromMode := .observational, toMode := .strict, ... }

def Modality.diamond : Modality :=
  { fromMode := .strict, toMode := .observational, ... }
```

`Modal/Adjunction.lean` — `◇ ⊣ □`:
* Unit: `η : A → □ ◇ A`
* Counit: `ε : ◇ □ A → A`
* Triangle identities: `□.map ε ∘ η_□A = id_□A`, `ε_◇A ∘ ◇.map η = id_◇A`
* Naturality: `□` and `◇` are functors

`Modal/BoxPath.lean` — modality respects equality:
```
theorem boxPath (A : Ty inner-mode) (x y : Term inner-ctx A _) :
    Equiv (Path (Ty.modal box A) (boxIntro x) (boxIntro y))
          (Ty.modal box (Path A x y))
```

`Modal/Cohesive.lean` — `♭ ⊣ ◇ ⊣ □ ⊣ ♯` adjoint chain:
* `♭ A` : crisp/discrete subspace
* `♯ A` : codiscrete subspace
* 6 adjunction theorems (3 pairs × 2 directions)
* Pentagon for 4-modality chain

`Modal/Bridge.lean` — strict ↔ observational ↔ univalent transfer:
* Lift strict equality to path
* Project path to strict via `□`
* Provable equivalences in shared types

`Modal/Ghost.lean`, `Modal/Cap.lean`, `Modal/Later.lean`, `Modal/Clock.lean` — populated with concrete modalities used by FX:
* Ghost: ◇ specialized for compile-time-only types
* Cap: capability modality (effects + permissions)
* Later: guarded recursion for codata productivity
* Clock: variable-clock modality (Atkey-McBride GuardedTT)

## 1.10 Layer 8: Graded Type Theory

`Graded/Semiring.lean` — abstract resource semiring:
```
structure Semiring (R : Type) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  add_zero : ∀ a, add a zero = a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_one : ∀ a, mul a one = a
  one_mul : ∀ a, mul one a = a
  zero_mul : ∀ a, mul zero a = zero
  mul_zero : ∀ a, mul a zero = zero
  distrib_l : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  distrib_r : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
```

`Graded/GradeVector.lean` — 21-dim grade vector:
```
structure GradeVector where
  type : Unit  -- not graded
  refinement : Unit  -- not graded
  usage : UsageGrade  -- {0, 1, w}
  effect : EffectRow  -- lattice
  security : SecurityGrade  -- {U, C}
  protocol : ProtocolStep
  lifetime : RegionPreorder
  provenance : ProvenanceLattice
  trust : TrustLevel
  representation : ReprPreorder
  observability : ObservabilityLattice
  clockDomain : ClockDomain
  complexity : Nat
  precision : RationalULPs
  space : Nat
  overflow : OverflowMode
  fpOrder : FPOrderMode
  mutation : MutationLattice
  reentrancy : ReentrancyMode
  size : SizeBound
  version : VersionLattice
  -- pointwise composition: + and * are pointwise across all 21 fields
```

`Graded/Ctx.lean` — graded context (extends existing Ctx):
* Each binding carries a grade
* Context multiplication for App rule

`Graded/Rules.lean` — typing rules with grades:
```
-- Wood/Atkey 2022 corrected Lam rule:
def Lam_rule (G : GradedCtx) (p : GradeVector) (r : GradeVector)
    (A : Ty) (B : Ty) (b : Term (G/p, A^r) B) :
    Term G (Pi A^r B)^p
  -- G/p is context division: each binding's grade divided by p.
  -- For usage semiring: 1/w = 0, so linear bindings get erased
  -- when constructing replicable closure.
```

`Graded/Instances/{Usage,Effect,Security,...}.lean` — concrete semirings, one
file per dimension. Each has:
* Concrete element type
* Zero, one, add, mul tables
* Verified semiring laws

Atkey 2018 attack term verification:
```
example : ¬ (typeable (λ f : i64 → i64. λ x : i64. f (f x))) := by
  -- shows the term is rejected by Wood/Atkey 2022 Lam rule
  -- because f's grade 1 cannot be divided by w (replicable closure)
  -- giving 1/w = 0, so f isn't available in the inner closure
  ...
```

## 1.11 Layer 9: Refinement Types

`Refine/Ty.lean` — `Ty.refine` is in Layer 0; this collects derived
operations:
* `Refine.unrefine : T{P} → T` — forget refinement (subtyping)
* `Refine.intro : (witness : T) → P[witness] → T{P}` — introduce
* `Refine.elim : T{P} → (T → P → motive) → motive` — analysis with witness

`Refine/Decidable.lean`:
* `instance : Decidable (P x)` for ground predicates
* Compile-time discharge via `decide`

`Refine/SMTCert.lean` — placeholder structure:
```
structure SMTCert where
  goal : RawTerm scope
  proof : Lean.Expr  -- Lean's expression for the proof
  -- No verification at v1.0; placeholder for v1.1 SMT recheck
```

`Refine/SMTRecheck.lean` — placeholder; v1.1 deferred.

## 1.12 Layer 10: Effects + Sessions + Codata

`Effects/Foundation.lean`:
* `EffectRow := List Op` — set of operations
* `Effect.empty : EffectRow := []`
* `Effect.union : EffectRow → EffectRow → EffectRow`
* `Op` records a single operation: name + parameter type + result type

`Effects/Handlers.lean`:
* `Term.effectPerform op : Term ctx resultType (effects ⊇ {op})`
* `Term.effectHandle body handlers` : 
  * body : Term ctx A (effects)
  * handlers : Map Op (Term ctx (paramType ⊸ contType ⊸ A))
  * single-shot continuation: `cont : (B → A)` is graded usage = 1
* Step rules in Layer 2

`Sessions/Foundation.lean`:
* `SessionProtocol` inductive: `send T S | recv T S | branch [(tag, S)] | end`
* `Ty.session : SessionProtocol → Ty 0 scope` (sessions are at universe 0)
* Linear typing: session channels have usage = 1

`Sessions/Duality.lean`:
```
def SessionProtocol.dual : SessionProtocol → SessionProtocol
  | .send T S => .recv T S.dual
  | .recv T S => .send T S.dual
  | .branch options => .branch (options.map (fun (t, s) => (t, s.dual)))
  | .end => .end

theorem dual_involutive (p : SessionProtocol) : p.dual.dual = p
```

`Codata/Foundation.lean`:
* `Ty.codata` ctor in Layer 0 takes head + observations
* `Term.codataUnfold` introduces; `codataObserve` projects
* Step rules in Layer 2 unfold lazily

`Codata/Productivity.lean`:
* Productivity check via Later modality
* `corecursive_call_under_later` predicate
* Verified termination

## 1.13 Layer 11: Surface Frontend

`Surface/AST.lean` — extended with all deferred features:
* A05: pre/post/decreases/where on `Decl.fnDecl`
* A06: `match` expression with intrinsic exhaustiveness
* A07: type-expression vs value-expression refinement (`isType` predicate)
* A08: try/catch
* A09: handle/effect handlers
* A10: select (channel-select)
* A11: modal markers (comptime, ghost, secret, await, etc.)
* A12: verify/assert/calc proof blocks
* A13: machine/contract/codata/session/hardware top-level decls
* A14-A15: type params + effect rows on `fnDecl`
* H01-H05: dependent FnParam, type-class context, forall/exists, variance

`Surface/Token.lean` + `TokenSchema.lean` + `GrammarToken.lean` extended:
* T01: `bitLit value < 2^width` refinement
* T02: int suffix typed (`IntSuffix` enum)
* T03: `DecSuffix` / `FloatSuffix` / `TritSuffix` enums
* T04: `ident name` carries `LowerIdent`; `uident` carries `UpperIdent`
* T05: `StrEscape` / `StrLitContent` refinement
* T06-T10: well-formed token stream invariants

`Surface/Lex.lean` extended with audits:
* L01: lex consumes all input or produces error
* L02: `classifyIdent kind.toLexemeChars` round-trips
* L03: lex output is EOF-terminated
* L04: lex output positions monotonically increasing
* L05: refine output to `Array WellFormedToken`
* L06: invalid characters always produce errors (no silent drop)
* L07: `LexError.offset` lies within source range
* L08: `Lex.runFromString` documented as the only sanctioned axiom-leak boundary

`Surface/Parse.lean` — full LALR(1)-compatible parser:
* Implements full FX grammar (1981 lines spec)
* Precedence-climbing for operators (matches §3 ladder)
* Position tracking via P-series
* Disambiguation rules from §2.7 (28 rules)

`Surface/Print.lean` — pretty printer:
* Inverse of Parse: AST → String
* Canonical formatting

`Surface/Roundtrip.lean` — M01+M02 theorems:
```
theorem M01 : ∀ tok : List Token, Lex.run (Print.runTokens tok) = ok tok
theorem M02 : ∀ ast : AST, Parse.run (Lex.run (Print.run ast)) = ok ast
```

`Surface/Elab.lean` + `ElabSoundness.lean` + `ElabCompleteness.lean`:
* Elaboration: AST → typed Term
* Soundness: every elaborated Term is well-typed
* Completeness: every well-typed program elaborates

`Surface/KernelEnv.lean` — propext-clean B10 refactor (cleanup task):
* Replace mutual block tactic-mode with term-mode `Option.recOn`
* Verify zero-axiom

`Surface/Bridge.lean` extended for new ctors:
* Bridge handles path/glue/refine/record/codata/session/effect
* All gap-free (R-series complete)

## 1.14 Layer 12: Pipeline

`Pipeline.lean` — end-to-end compose:
* `def compile : String → Either Error (Term ctx ty raw)` 
* String → Tokens → AST → Term → Reduced value
* One example program per FX dimension demonstrating end-to-end

## 1.15 Layer 13: Tools

`Tools/AuditAll.lean` — comprehensive audit:
* ~500 `#assert_no_axioms` calls
* Auto-generated by `Tools/AuditGen.lean`

`Tools/AuditGen.lean` — auto-generation tactic:
* Walks all .lean files
* Extracts theorem/def names
* Emits AuditAll entries

`Tools/Tactics/Cast.lean` — cast simplification helper.
`Tools/Tactics/HEq.lean` — HEq simplification (closes recurring W8-style HEq cascades).
`Tools/Tactics/SimpStrip.lean` — simp lemma stripping for clean equation generation.

## 1.16 Layer 14 (Day 8): FX1 and Lean Kernel Encoding

Layer 14 is split. FX1/Core is the minimal root. LeanKernel-FX1 is the faithful
Lean-kernel model over that root. Existing `Lean/Kernel/*` files are historical
scaffolding unless they are moved or mirrored under `LeanFX2/FX1/LeanKernel`.

`FX1/Core/Level.lean` — minimal FX1 universe levels.

`FX1/LeanKernel/Level.lean` — Lean's universe levels:
```
inductive Level
  | zero
  | succ : Level → Level
  | max : Level → Level → Level
  | imax : Level → Level → Level
  | param : Name → Level
  | mvar : Name → Level
  deriving DecidableEq, Repr
```

`FX1/LeanKernel/Name.lean` — hierarchical names.

`FX1/LeanKernel/Expr.lean` — 12-ctor expression syntax:
```
inductive Expr (level scope : Nat) : Type
  | bvar : Fin scope → Expr level scope
  | fvar : FVarId → Expr level scope
  | sort : Level → Expr level scope
  | const : Name → List Level → Expr level scope
  | app : Expr level scope → Expr level scope → Expr level scope
  | lam : Expr level scope → Expr level (scope+1) → Expr level scope
  | pi : Expr level scope → Expr level (scope+1) → Expr level scope
  | letE : Expr level scope → Expr level scope → Expr level (scope+1) → Expr level scope
  | lit : Literal → Expr level scope
  | mdata : MData → Expr level scope → Expr level scope
  | proj : Name → Nat → Expr level scope → Expr level scope
```

`FX1/LeanKernel/Substitution.lean` — instantiate + abstract + lift.

`FX1/LeanKernel/Reduction.lean` — all 8 reduction rules:
* β (App-Lambda)
* η (Lambda-App when bvar 0 not free in body)
* δ (Const unfolding via env)
* ζ (Let unfolding)
* ι (recursor on ctor)
* proj (projection on structure ctor)
* Quot β (Quot.lift on Quot.mk)
* Nat literal reduction (`reduceBin`)

`FX1/LeanKernel/Inductive.lean` — inductive type encoding:
* Inductive specifications (parameters, indices, constructors)
* Recursor synthesis (motive + cases)
* ι-reduction per inductive
* Strict positivity check
* Universe constraint inference

`FX1/LeanKernel/HasType.lean` — typing relation (~25 typing rules).

`FX1/LeanKernel/Check.lean` — executable type checker:
```
def check : Environment → LocalContext → Expr → Option Expr
```

`FX1/LeanKernel/Soundness.lean` — THE THEOREM:
```
theorem check_sound :
    LeanFX2.FX1.LeanKernel.check env ctx e = some ty →
    LeanFX2.FX1.LeanKernel.HasType env ctx e ty
```

`FX1/LeanKernel/Audit.lean` — `#print axioms check_sound`.

## 1.17 Layer 15 (Day 9): Cross-Theory Bridges

`Bridge/PathToId.lean` — `Path A x y → Ty.id A x y`:
```
def pathToId : Path A x y → Ty.id A x y :=
  fun p => -- Apply path at i0 / i1 endpoints; OEq reduces refl-equality
           -- when interval is constant; recover Id witness.
```

`Bridge/IdToPath.lean` — reverse direction.

`Bridge/PathIdInverse.lean` — composition is identity:
```
theorem pathToId_idToPath_inv (i : Ty.id A x y) :
    pathToId (idToPath i) = i

theorem idToPath_pathToId_inv (p : Path A x y) :
    idToPath (pathToId p) = p

theorem pathIdEquiv : Equiv (Path A x y) (Ty.id A x y)
```

`Bridge/IdEqType.lean` — definitional bridge:
```
theorem idEqType (A B : Ty (lvl+1) scope) :
    Conv (Ty.id (Ty.universe lvl) A B) (Ty.equiv A B) :=
  Conv.fromStep Step.eqType  -- pure HOTT
```

`Bridge/PathEqType.lean` — cubical ua equivalence:
```
theorem pathEqType (A B : Ty (lvl+1) scope) :
    Equiv (Path Ty.universe A B) (Equiv A B)
```

`Bridge/BoxObservational.lean` — `□ commutes with Id`:
```
theorem boxObservational :
    Equiv (Ty.id (Ty.modal box A) (boxIntro x) (boxIntro y))
          (Ty.modal box (Ty.id A x y))
```

`Bridge/BoxCubical.lean` — `□ commutes with Path`.

`Conservativity/HOTTOverMLTT.lean` — translation HOTT → MLTT preserves
typing on MLTT-only types.

`Conservativity/CubicalOverHOTT.lean` — cubical paths can be observationalized.

`Conservativity/ModalOverObservational.lean` — modal layer is conservative
over observational.

`Translation/CubicalToObservational.lean` — explicit translation functor.

`Translation/ObservationalToCubical.lean` — reverse functor.

`Translation/Inverse.lean` — they compose to identity (set-level).

`InternalLanguage/Coherence.lean` — diamond commutation:
```
theorem diamond_coherence :
    -- The triangle of translations Cubical, Observational, MLTT commutes
    -- up to provable equality at set-level.
    True := ...
```

---

# Section 2 — Top-to-Bottom Dependency Analysis

## 2.1 Goal: `FX1.check_sound` and `LeanKernel.check_sound` zero-axiom

The terminal trust-spine goal of Day 8 has two gates:

1. `LeanFX2.FX1.check_sound`, proving the minimal lambda-Pi checker sound.
2. `LeanFX2.FX1.LeanKernel.check_sound`, proving the Lean-kernel model sound
   over FX1.

The second gate is not allowed to bypass the first.

Direct dependencies:
* `FX1.Core.Check` — minimal FX1 checker
* `FX1.Core.HasType` — minimal FX1 typing relation
* `FX1.LeanKernel.Check` — Lean-kernel checker model
* `FX1.LeanKernel.HasType` — Lean-kernel typing relation
* Faithful Lean.Kernel.Expr encoding (12 ctors)
* Faithful Step encoding (8 reduction rules)
* `FX1.LeanKernel.Reduction.confluence` — Lean's reduction is confluent
* `FX1.LeanKernel.SR` — subject reduction for Lean's reduction
* Decidable Conv for Lean's `is_def_eq`
* WHNF termination for Lean's reduction

These transitively need:
* General SR via IsClosedTy (Layer 2.5)
* Confluence machinery generalized (Layer 3)
* Decidable Conv with bounded fuel (Algo)
* All Step rules covering all 8 Lean reductions
* Lean's universe level computation
* Lean's inductive elaboration
* Lean's Quot.sound axiom modeled as a typing rule (not a Lean axiom!)

Where does Quot.sound fit? In our verified Lean kernel, `Quot.sound` is a
typing JUDGMENT we explicitly model:
```
HasType env ctx (Quot.sound rrefl) (Eq (Quot R) (Quot.mk x) (Quot.mk y))
```

We do NOT use Lean's actual Quot.sound axiom in lean-fx-2's metatheory. We
model it. This is the difference between "the kernel uses Quot.sound" and
"we model the kernel's use of Quot.sound as a typing judgment."

## 2.2 Goal: `axiom Univalence` DELETED

Direct dependency:
* `Step.eqType : Step (Ty.id (Ty.universe lvl) A B) (Ty.equiv A B)` reduction rule
  — the HOTT rule that makes `Eq Type A B = Equiv A B` definitional.

Transitively needs:
* `Ty.equiv` ctor (Layer 0e)
* `Ty.universe` ctor (Layer 0e)
* HOTT mode discipline (Layer 0a Mode)

Once `Step.eqType` ships, `Univalence` becomes `Conv.fromStep Step.eqType`.

## 2.3 Goal: `axiom funext` removed (was inherited via stdlib)

Direct dependency:
* `Step.eqArrow : Step (Ty.id (Ty.arrow A B) f g) (Ty.piTy A (Ty.id B (f x) (g x)))`
  — the HOTT rule that makes `Eq (A → B) f g ≡ Π x, Eq B (f x) (g x)`.

Once shipped, `funext h := h` (literally — `h` is already the right type).

## 2.4 Goal: M06 (arrow SR) and M07 (parametric SR)

Direct dependency:
* `IsClosedTy` predicate (Layer 0e) covering all closed type formers.
* `Step.preserves_isClosedTy` theorem (Layer 2.5).

Once shipped, M06 and M07 are corollaries via `IsClosedTy.arrow A_closed B_closed`
and `IsClosedTy.listType A_closed` etc.

## 2.5 Goal: All Conv cong rules

Direct dependency:
* General SR (Layer 2.5)
* `mapStep` abstraction (existing in StepStar.lean)

Each cong rule is a 5-line proof: obtain Conv's existential triple, lift
both chains via mapStep, reconstruct outer Term.

## 2.6 Goal: All HITs (7 of them)

Direct dependencies:
* `HoTT/HIT/Spec.lean` (Layer 5)
* `HoTT/HIT/Eliminator.lean` (Layer 5)
* HOTT OEq reductions (Layer 2)
* For S¹: cubical Path machinery (Layer 4)

Each HIT is a kernel inductive + path constructors + computation rules.

## 2.7 Goal: Cross-theory bridges (Day 9)

Direct dependencies:
* HOTT machinery (Layer 5)
* Cubical Path machinery (Layer 4)
* 2LTT modal stratification (Layer 7)
* All three theories typecheck zero-axiom

## 2.8 Goal: Surface frontend complete

Direct dependencies:
* Full AST (A-series + H-series)
* Token schema (T-series)
* Lex audits (L-series)
* Parser + printer + roundtrip (M01, M02)
* Elaboration soundness + completeness

## 2.9 Goal: All 95 pending tasks resolved

Each task corresponds to a file or theorem:
* L01-L08 → Lex audits
* T01-T10 → Token refinements
* C01, C06, C09 → schema audits remaining
* A01-A15 → AST refinements
* B01-B12 → bridge correctness theorems
* G01-G07 → gap closures
* K01-K10 → kernel extensions
* M01-M10 → metatheory
* P01-P04 → position handling
* S01-S04 → semantic theorems
* H01-H05 → higher-rank polymorphism
* B10-cleanup → propext-clean refactor

Most are direct deliverables of Layer 0-12. The K-series and M-series are the
most foundational (covered in Layer 0-3). The L/T/A/B/S/G/H/P-series ride on
the surface frontend (Layer 11).

---

# Section 3 — Comprehensive Pitfall Catalog

## P-1: Match-compiler propext leaks (mutual blocks)

**Symptom:** Mutual recursive theorems leak `propext` and `Quot.sound` even when
each individual building block (cases on Option, nomatch on impossible
equalities, rw chains) is propext-clean in isolation.

**Cause:** Lean 4 v4.29.1's match compiler emits propext-using equation lemmas
when combining nested `cases`+`rw` patterns across mutual recursion.

**Reference:** `feedback_lean_match_propext_recipe.md`, B10 lesson from this
session.

**Mitigation:**
* Use term-mode `Option.recOn` / `Sum.recOn` instead of tactic `cases h : ... with`.
* Prefer `match h : x with | none => ... | some _ => ...` syntax in tactic mode
  (slightly different match compilation).
* Pre-write a `MatchPropextProbe.lean` template; consult before each new
  mutual-recursive theorem.
* Apply paired-predicate pattern (W8 trick) where mutual induction needed.

**Diagnosis kit:** Drop in a probe file with each suspect tactic in isolation;
binary search to find the propext source.

## P-2: Match-arity propext (multi-Nat-indexed inductives)

**Symptom:** Theorems whose types involve N implicit Nat indices inside `∀`
trigger propext+Quot.sound.

**Cause:** When N implicits sit inside the ∀, the match compiler synthesizes
helper functions that use propext.

**Reference:** `feedback_lean_match_arity_axioms.md`.

**Mitigation:** Hoist all but one Nat index to the theorem header (before `:`)
to keep the proof zero-axiom. Cost: slightly less general theorem statement,
but provable zero-axiom.

## P-3: Universe constructor blocker

**Symptom:** `Ty.universe (u : Nat) : Ty (u+1) scope` breaks pattern-form match
in any theorem whose goal uses the scrutinee through a function (e.g.,
goal `f (Ty.universe u) = ...`).

**Cause:** Pattern-form match on a level-constraining ctor (level depends on
constructor argument) fails to elaborate.

**Reference:** `feedback_lean_universe_constructor_block.md`.

**Mitigation:** Add a propositional-equation parameter to the constructor
case: `(levelEq : level = u + 1)`. Then case-split on this equation to recover
the level.

## P-4: Cumulativity Subst mismatch

**Symptom:** If we add cumulativity as a `Ty` constructor, Subst on a
cumul-typed type fails because Subst at level `levelHigh` doesn't compose with
base-Subst at level `levelLow`.

**Cause:** Subst is parameterized by level; level-mismatch makes composition
fail.

**Reference:** `feedback_lean_cumul_subst_mismatch.md`.

**Mitigation:** Cumulativity as a Conv RULE, not a Ty ctor. The Conv layer
handles level shifts; Ty stays parametric.

## P-5: Mutual index rule

**Symptom:** Lean 4 forbids sibling references in mutual *index* signatures
(not just positivity).

**Cause:** Lean's elaborator restriction on mutual inductive types.

**Reference:** `feedback_lean_mutual_index_rule.md`.

**Mitigation:** Use well-scoped Term + extrinsic HasType instead of intrinsic
Ctx⇄Ty⇄Term mutual block. (Existing lean-fx-2 design already follows this.)

## P-6: Termination via sizeOf for new mutual blocks

**Symptom:** Mutual block of N functions over inductive types fails Lean's
auto-termination heuristic.

**Cause:** Lean's auto-termination doesn't always trace `sizeOf` decreases
through cross-function calls in mutual blocks.

**Mitigation:** Always provide explicit `termination_by sizeOf <scrutinee>`
for each function in a mutual block.

## P-7: Conv mid-term type mismatch

**Symptom:** Conv decomposed via `obtain ⟨_, _, midTerm, ...⟩` gives a
`midTerm : Term ctx midType midRaw` where `midType` is existential. Cannot use
`midTerm` directly as input to a Term constructor that requires a specific
type.

**Cause:** Conv's definitional shape allows the common-reduct's type to differ
from source's type. Without SR, we can't constrain it.

**Reference:** This conversation's HoTT/Identity attempt.

**Mitigation:** General SR via `IsClosedTy` (Layer 2.5) constrains midTerm's
type. For non-closed types, defer cong rules to per-type SR specialization.

## P-8: Induction generalization with duplicate indices

**Symptom:** `induction chain` fails with "Target (or one of its indices) occurs
more than once" when the goal has duplicate type indices (e.g., motiveType
appearing in both source and target Term-types).

**Cause:** Lean's `induction` tactic can't generalize a value that appears
multiple times in the goal/hypotheses.

**Reference:** This conversation's StepStar.idJ_baseCase_lift attempt.

**Mitigation:**
* Free the duplicate via `srcTy/tgtTy` variables + equality hypotheses.
* Use `induction chain generalizing motiveType` if Lean accepts it.
* Or: use manual recursion via Lean's `match` on the chain.
* Or: use Lean 4's `induction ... using` with a specialized recursor.

## P-9: Free-type-via-suffices for parametric Term ctors

**Symptom:** Failed to solve equation `ParametricType.X = varType ctx pos` when
proving HEq uniqueness on parametric Term ctors at fixed types.

**Cause:** Lean's elaborator can't unify a fully-applied parametric type with
a varType-determined type.

**Reference:** `feedback_lean_free_type_via_suffices.md`.

**Mitigation:** Free the type indices via `suffices`, then `cases` through,
realign with `Ty.X.inj`.

## P-10: HEq cascades

**Symptom:** Theorems involving cross-type Term comparisons require multiple
nested HEq + cast manipulations, often with cryptic mismatch errors.

**Cause:** Type indices on Term make comparisons heterogeneous; HEq is the
machinery for relating Terms of different types.

**Mitigation:** Use `Term.toRaw_X = rfl` whenever possible (since
`Term.toRaw` projects to RawTerm regardless of type). Build via
`Tools/Tactics/HEq.lean` (Day 7) — a tactic for systematically reducing HEq
cascades.

## P-11: Paired-predicate pattern for tactic-mode opacity

**Symptom:** Tactic-mode theorems can't extract data from inductive proofs
because the inductive's payload is opaque to the tactic.

**Cause:** Tactic mode operates on the proof term abstractly; doesn't see
inside inductive constructors.

**Reference:** `feedback_lean_paired_predicate_pattern.md`.

**Mitigation:** Switch to a paired-predicate value (e.g., `parWithBi` for
parallel reduction with bi-witness). Construct fresh witnesses at each
induction case via direct term construction, not tactic.

## P-12: AuditAll axiom semantics

**Symptom:** `#print axioms` reports clean for individual declarations but the
overall AuditAll smoke fails because some theorem transitively pulls in propext.

**Cause:** Per-declaration audit only checks direct dependencies; transitive
propext from Lean stdlib lemmas (`Int.lt_irrefl`, `Int.lt_of_le_of_lt`, etc.)
slips in.

**Mitigation:** Probe stdlib lemmas BEFORE using them in zero-axiom theorems.
Replace with constructive alternatives (e.g., `if_neg` directly) or take the
hypothesis form to defer the propext-using derivation to call sites.

## P-13: Decidable instance synthesis

**Symptom:** `decide` tactic on a complex predicate fails with "failed to
synthesize Decidable instance" or times out.

**Cause:** Lean's typeclass resolution doesn't always find Decidable instances
for compound predicates.

**Mitigation:** Provide explicit `instance : Decidable (P x)` definitions for
the specific predicates we care about. Use `DecidableEq` derived instances for
finite enums.

## P-14: Universe polymorphism in Equiv

**Symptom:** `Equiv A B` should work at any universe level, but Lean 4's
universe polymorphism + our explicit `Nat`-indexed levels could conflict.

**Cause:** Lean's `Type u` and our `Ty (lvl : Nat)` are different conceptions
of universes.

**Mitigation:** `Ty.equiv {level : Nat} (A B : Ty level scope)` is parametric
in our explicit Nat level. Universe coherence theorems handle level shifts via
`cumul` Conv rule.

## P-15: Mode polymorphism in modal ctors

**Symptom:** `Term.modIntro` must take a Term in one mode and produce a Term
in another mode. The signature gets complex.

**Mitigation:** Mode is on `Ctx`, so `Term.modIntro` takes
`(innerCtx : Ctx innerMode ...) (innerTerm : Term innerCtx ...)` and produces
`Term outerCtx ...`. Mode discipline at the Ctx level — Term ctors thread mode
implicitly via the context.

## P-16: Name shadowing across cubical+HOTT+2LTT

**Symptom:** Each theory has its own `refl`, `sym`, `trans`. Different
signatures, possibly different operational semantics.

**Mitigation:** Namespacing:
* `Term.refl` — HOTT observational refl (unified)
* `Term.reflStrict` — outer-mode strict refl
* `Term.pathRefl` — cubical refl-as-constant-path
With provable equalities `Conv (Term.pathRefl A x) ...`.

## P-17: Pipeline end-to-end mode tracking

**Symptom:** A program containing all theories needs to typecheck through
Surface → AST → Term with mode tracking. Mode-changing operations make
elaboration complex.

**Mitigation:** Mode is part of the AST node where mode-changing ctors appear
(modIntro/modElim/comptime/ghost). Elaborator picks default mode per
declaration context. Surface AST is mode-agnostic; elaboration sets it.

## P-18: Glue construction for ua

**Symptom:** Glue's reduction rules involve cofibration handling that's
intricate to encode.

**Mitigation:** Boundary cofibrations only (4 cases: atZero, atOne, atBoth,
atNeither). General face lattice is v1.1.

## P-19: Strict positivity for inductive types in Lean encoding

**Symptom:** Lean's kernel checks strict positivity for inductive types.
Encoding this faithfully in lean-fx-2 requires structural decidability.

**Mitigation:** `LeanFX2.FX1.LeanKernel.Inductive.IsStrictlyPositive` decidable
predicate, checked structurally.

## P-20: Native nat reductions in Lean kernel

**Symptom:** Lean's kernel has efficient native reductions for Nat operations
(`reduceBin`, `reducePow`, etc.). Encoding these faithfully requires modeling
the C++ Nat arithmetic.

**Mitigation:** Trust the Nat operations as `decide`-equivalent in lean-fx-2
(Nat arithmetic is decidable, so we can compute). Document this as "trust the
Nat decision procedure" in TCB.

## P-21: Mutual + nested inductives in Lean

**Symptom:** Lean's elaborator translates mutual + nested inductives into
single inductives before the kernel sees them. The kernel only sees the
elaborated form.

**Mitigation:** Faithfully encode the elaborated form, not the surface mutual
form. lean-fx-2's general inductive framework + dependent eliminators (K07)
handle the elaborated form.

## P-22: Decidable proof irrelevance for Prop

**Symptom:** Lean's kernel has definitional proof irrelevance for `Prop`.
Encoding this requires special handling in Conv decision.

**Mitigation:** Single line in DefEq: when both sides are at type `Prop`,
return `true` regardless. This is well-understood behavior.

## P-23: Lazy delta heuristic in Lean

**Symptom:** Lean's `is_def_eq` uses a lazy delta heuristic that could be
unsound or incomplete.

**Mitigation:** We prove our `check` SOUND. We don't claim completeness for
v1.0 (Lean's heuristic may accept things our pure relation rejects, which is
acceptable; the inverse — Lean rejecting things we accept — is what we'd need
to prove, and it's not strictly necessary for soundness).

## P-24: H-groupoid coherence in HOTT

**Symptom:** Higher OTT (Sterling et al. 2024) hasn't fully mechanized
n-truncation coherence for n ≥ 2.

**Mitigation:** Set-level (n = 0) only for v1.0. Equality-of-equality at h-set
collapses to `Ty.unit`. Higher coherence → v1.1.

## P-25: SMT cert format

**Symptom:** Refinement types may need SMT-discharged predicates. Format and
recheck mechanism are non-trivial.

**Mitigation:** Decidable predicates only for v1.0 (Lean's `Decidable`
typeclass). SMT certificate is a placeholder structure; recheck via external
solver is v1.1.

## P-26: Conservativity proofs

**Symptom:** Proving HOTT is conservative over MLTT requires constructing a
translation function and proving it preserves typing for MLTT-only types.

**Mitigation:** Translation is the identity on MLTT-only types (no path/oeq
appear). Typing preservation is by structural induction. Set-level only.

## P-27: Cross-theory bridge equivalences

**Symptom:** Bridges between Path/Id/OEq/StrictId require constructing
equivalences manually for each pair.

**Mitigation:** Define each bridge function separately; prove inverse-pair
equivalence at set-level. ~50 LoC per bridge × 6 bridges = ~300 LoC for Day 9.

## P-28: Bootstrap order for Equiv

**Symptom:** `Equiv A B` should be available before HOTT's `eqType` rule fires
(since the rule produces `Ty.equiv`). Bootstrap order matters.

**Mitigation:** `Ty.equiv` is a separate Ty ctor in Layer 0e (not derived
from Σ + Π). HOTT's `eqType` rule produces this ctor.

## P-29: Effect handlers + linearity composition

**Symptom:** Effect handlers don't always compose cleanly with linear types.
Multi-shot continuations conflict with linearity.

**Mitigation:** Single-shot only for v1.0. Each handler's `cont` is graded
usage = 1.

## P-30: Codata productivity check

**Symptom:** Corecursive functions can spin without producing observable
output, breaking productivity.

**Mitigation:** Productivity check via Later modality. Corecursive call must
appear under `Later`. Standard guarded recursion.

---

# Section 4 — Risk Register

## R-1: Day-1 ctor explosion (40 ctors × 5 files = 200 changes)

**Severity:** HIGH
**Probability:** 60%
**Impact:** Day 1 overruns by 8-12h.
**Mitigation:** Scripted templates per ctor; do RawTerm first; build green between
each ctor.

## R-2: ua_β proof intractable

**Severity:** HIGH
**Probability:** 30% (HIGH because we're using HOTT, where ua_β is direct)
**Impact:** Cubical-ua not provable; defer to v1.1.
**Mitigation:** HOTT delivers univalence definitionally; cubical ua_β is
secondary. If cubical ua_β proves intractable, ship it as a Conv-equality
(6 sub-lemmas) instead of a Step rule.

## R-3: Cubical kernel size explodes Day 2-3 budget

**Severity:** HIGH
**Probability:** 40%
**Impact:** Days 2-3 overrun, cohesive modalities deferred.
**Mitigation:** Cohesive modalities ♭/♯ are first cut. Boundary cofibrations
only.

## R-4: HITs require general cofibrations beyond boundary

**Severity:** MEDIUM
**Probability:** 25%
**Impact:** Some HITs (suspension, pushout) deferred to v1.1.
**Mitigation:** Restrict ctors to point/path; 2-path → v1.1.

## R-5: Mutual-block propext (B10 lesson)

**Severity:** MEDIUM
**Probability:** 50% (encountered in this session)
**Impact:** Days 2-3 mutual proofs leak propext; need refactor.
**Mitigation:** Term-mode `Option.recOn` everywhere new mutual recursion
appears. Pre-write Match-compiler propext probe.

## R-6: General SR via IsClosedTy doesn't compose

**Severity:** MEDIUM
**Probability:** 20%
**Impact:** Per-type SR fallback (ship more lemmas, less elegance).
**Mitigation:** Per-type SR fallback is mechanical (already shipped for
nat/bool/unit). 12 closed type formers × 30 LoC = 360 LoC.

## R-7: Refinement type SMT cert mechanism

**Severity:** MEDIUM
**Probability:** 30%
**Impact:** SMT external recheck deferred to v1.1.
**Mitigation:** Decidable predicates only for v1.0.

## R-8: Parser complete in 8h

**Severity:** MEDIUM
**Probability:** 60%
**Impact:** Parser handles canonical fragment only at v1.0.
**Mitigation:** Canonical fragment first, full grammar incrementally to v1.1.

## R-9: Atkey 2018 attack rejection proof

**Severity:** LOW
**Probability:** 10%
**Impact:** Attack term rejection proof has technical issue.
**Mitigation:** Direct counterexample via Lam rule typing; explicit derivation.

## R-10: Build time ballooning

**Severity:** LOW
**Probability:** 20%
**Impact:** Each build cycle adds 30-60s.
**Mitigation:** Lake supports incremental; disable AuditAll except at
end-of-day.

## R-11: 21-dim graded semiring instances

**Severity:** LOW
**Probability:** 5%
**Impact:** Each ~10 LoC; uniform pattern.
**Mitigation:** Each semiring proven correct via `@[law]` annotations.

## R-12: Lean kernel encoding faithfulness (Day 8)

**Severity:** HIGH
**Probability:** 30% (semantic gap discovery)
**Impact:** Soundness proof goes through but encoding doesn't match Lean's
behavior; ship modulo a "trust list".
**Mitigation:** Cross-reference Lean source for each reduction rule;
implementation-by-the-book.

## R-13: Cubical Glue construction

**Severity:** HIGH
**Probability:** 35%
**Impact:** ua via Glue intractable; rely on HOTT-only univalence.
**Mitigation:** HOTT's `eqType` rule delivers definitional univalence
without Glue. Cubical-ua is a derived theorem only if Glue construction
goes through.

## R-14: 2LTT BoxPath coherence

**Severity:** MEDIUM
**Probability:** 25%
**Impact:** BoxPath equivalence non-trivial.
**Mitigation:** Use ACK 2LTT paper Lemma 4.2 directly; ~80 LoC adaptation.
HOTT actually makes this CLEANER because OEq's Π reduction handles it
definitionally.

## R-15: Cross-theory bridge proofs

**Severity:** MEDIUM
**Probability:** 30%
**Impact:** Some bridge equivalences harder than expected.
**Mitigation:** Set-level bridges are tractable; higher-coherence bridges
(h-groupoid level) → v1.1.

## R-16: Effect handlers + linear typing composition

**Severity:** MEDIUM
**Probability:** 25%
**Impact:** Some effect handlers don't typecheck with linear types.
**Mitigation:** Single-shot continuations only; multi-shot → v1.1.

## R-17: Nested inductive elaboration in Lean encoding

**Severity:** MEDIUM
**Probability:** 30%
**Impact:** Lean's elaborator handles nested inductives via translation;
faithful encoding non-trivial.
**Mitigation:** We model ELABORATED inductives, not surface mutual.

## R-18: Universe polymorphism in Lean encoding

**Severity:** LOW
**Probability:** 15%
**Impact:** Some Lean theorems use universe polymorphism we can't faithfully
encode.
**Mitigation:** Lean's `Level` is a separate algebraic type; we mirror it
exactly.

## R-19: Pipeline elaboration mode-inference

**Severity:** LOW
**Probability:** 20%
**Impact:** Surface AST mode-inference fails for some constructs.
**Mitigation:** Default mode per declaration context; explicit mode markers
(comptime, ghost) override.

## R-20: Days 2-3 mutual block coordination

**Severity:** MEDIUM
**Probability:** 30%
**Impact:** Coordination between Step + ParRed + RawPar + Compat across all
new ctors creates ordering dependencies.
**Mitigation:** Strict layering: Step first (Day 2 PM), ParRed/RawPar/Compat
second (Day 2 evening). Test each layer green before next.

---

# Section 5 — Day-by-Day Execution Plan

## Day 0 (4h) — Scaffold

**Mission:** Create directory structure + stub files for the entire sprint.
Build green at end. Initial commit.

**Dependencies:** Current lean-fx-2 build green at master HEAD.

### Tasks

**Task 0.1 — Create directory structure (1h)**

Create:
* `LeanFX2/Foundation/Interval.lean`
* `LeanFX2/Foundation/Universe.lean` (already exists; will extend)
* `LeanFX2/Foundation/Cofib.lean`
* `LeanFX2/Cubical/` directory
  - `Path.lean`
  - `Composition.lean`
  - `Transport.lean`
  - `Glue.lean`
  - `Ua.lean`
  - `PathLemmas.lean`
  - `Bridge.lean` (cubical→observational bridge)
* `LeanFX2/HoTT/OEq.lean`
* `LeanFX2/HoTT/HIT/{Spec, Eliminator, Examples, Setoid, Quot, PropTrunc, S1, Suspension, Pushout, Coequalizer}.lean`
* `LeanFX2/Modal/{TwoLevel, BoxPath, Cohesive, Bridge, Adjunction}.lean`
  (some exist; will extend)
* `LeanFX2/Refine/{Decidable, SMTCert, SMTRecheck}.lean` (already exist; will extend)
* `LeanFX2/Effects/{Foundation, Handlers, Step}.lean`
* `LeanFX2/Sessions/{Foundation, Duality, Step}.lean`
* `LeanFX2/Codata/{Foundation, Productivity, Step}.lean`
* `LeanFX2/Bridge/{PathToId, IdToPath, PathIdInverse, IdEqType, PathEqType, BoxObservational, BoxCubical}.lean`
* `LeanFX2/Conservativity/{HOTTOverMLTT, CubicalOverHOTT, ModalOverObservational}.lean`
* `LeanFX2/Translation/{CubicalToObservational, ObservationalToCubical, Inverse}.lean`
* `LeanFX2/InternalLanguage/Coherence.lean`
* `LeanFX2/FX1/Core/{Name, Level, Expr, Declaration, Environment, Context, Substitution, Reduction, HasType, Check, Soundness}.lean`
* `LeanFX2/FX1/LeanKernel/{Level, Name, Expr, Substitution, Reduction, Inductive, HasType, Check, Soundness, Audit}.lean`
* `LeanFX2/Tools/{AuditGen, Tactics/Cast, Tactics/HEq, Tactics/SimpStrip}.lean` (some exist)
* `LeanFX2/Smoke/AuditAll.lean` (will extend)

**Pitfall:** Lean's import resolution gets confused if files import each other
in cycles.
**Mitigation:** Use Layer ordering strictly. Each file imports only files in
strictly lower layers.

**Deliverable:** All ~40 new .lean files exist with stub docstrings.

**Task 0.2 — Stub each file (2h)**

Each file gets a docstring describing its theorem deliverable. Example for
`Foundation/Interval.lean`:

```lean
import LeanFX2.Foundation.Mode

/-! # Foundation/Interval — cubical interval primitive

The interval type `Interval` with two endpoints `i0`, `i1` and three
algebraic operations: `opp`, `meet`, `join`. Used as the type of cubical
"path lambdas" — `pathLam (body : Term ctx (... at I) ty)`.

## Algebraic structure

`Interval` is a *bounded distributive lattice with involution*:
* `(meet, i1)` and `(join, i0)` are commutative monoid structures
* `meet` and `join` are mutually distributive
* `opp` is the De Morgan involution: `opp (meet a b) = join (opp a) (opp b)`

## Coverage

* `opp_opp` : involution
* `meet_comm`, `meet_assoc`, `meet_idem`, `meet_idl`, `meet_idr`
* `join_comm`, `join_assoc`, `join_idem`, `join_idl`, `join_idr`
* `meet_join_distrib_l`, `meet_join_distrib_r`
* `de_morgan_meet`, `de_morgan_join`

All ~10 lemmas are `cases <;> rfl` zero-axiom proofs.

## Downstream consumers

* `Cubical/Path.lean` — pathLam binds an interval-typed parameter
* `Cubical/Composition.lean` — comp/hcomp use cofibrations on intervals
* `Cubical/Transport.lean` — transp at interval start point
-/

namespace LeanFX2

inductive Interval : Type
  | i0 : Interval
  | i1 : Interval
  deriving DecidableEq, Repr

end LeanFX2
```

Repeat for each new file: ~2 minutes per stub.

**Task 0.3 — Build green + initial commit (1h)**

```
cd /root/iprit/FX/lean-fx-2
lake build LeanFX2 2>&1 | tail -3
# Expected: "Build completed successfully (N jobs)."
```

If build fails: fix import dependencies (most likely cycles).

Commit:
```
git add -A
git commit -m "Phase 12.A.0: scaffold cubical+2LTT+HOTT directory layout"
```

**Day 0 acceptance criteria:**
* All ~40 new .lean files exist with stub docstrings
* `lake build LeanFX2` exits 0
* Commit `Phase 12.A.0` exists in git log

**Day 0 cut-line:** None. Day 0 is pure scaffolding; if it doesn't fit in 4h,
the planning is wrong.

---

## Day 1 (24h) — Foundation rebuild

**Mission:** Add interval + cubical primitives + universe hierarchy + extend
ALL substitution machinery for ~40 new ctors. Build green at end.

**Dependencies:** Day 0 scaffold complete.

### AM (8h) — Type-level foundations

**Task 1.1 — Foundation/Interval.lean (2h)**

Implement Interval + algebraic operations + ~10 algebraic lemmas.

```lean
def Interval.opp : Interval → Interval
  | .i0 => .i1
  | .i1 => .i0

def Interval.meet : Interval → Interval → Interval
  | .i0, _   => .i0
  | _,   .i0 => .i0
  | .i1, .i1 => .i1

def Interval.join : Interval → Interval → Interval
  | .i1, _   => .i1
  | _,   .i1 => .i1
  | .i0, .i0 => .i0

theorem Interval.opp_opp (i : Interval) : i.opp.opp = i := by cases i <;> rfl
theorem Interval.meet_comm (i j : Interval) : i.meet j = j.meet i := by
  cases i <;> cases j <;> rfl
-- etc. ~10 algebraic lemmas
```

**Pitfall:** Lean's match compiler may emit propext for the `meet`/`join`
pattern rules.
**Mitigation:** Use full enumeration (3 cases for meet, 3 cases for join);
verify zero-axiom with `#print axioms Interval.meet`.

**Smoke:** `#print axioms` clean for all 10 lemmas. Commit.

**Task 1.2 — Foundation/Universe.lean extension (1h)**

Extend existing Universe.lean with:
* `UniverseLevel` inductive (zero, succ, max, imax)
* Decidable equality
* Decidable `≤` order
* Cumulativity Conv rule placeholder

**Pitfall:** P-3 (universe constructor blocker) for level-constraining ctors.
**Mitigation:** Use propositional-equation parameter pattern.

**Smoke:** Build green; cumulativity Conv-rule stub typechecks.

**Task 1.3 — Foundation/Cofib.lean (1h)**

```lean
inductive BoundaryCofib : Type
  | atZero | atOne | atBoth | atNeither
  deriving DecidableEq, Repr

def BoundaryCofib.holds : BoundaryCofib → Interval → Bool
  | .atZero,   .i0 => true
  | .atOne,    .i1 => true
  | .atBoth,   _   => true
  | .atNeither, _  => false
  | _, _ => false  -- explicit; no wildcard
```

**Pitfall:** Wildcard catch-all leaks propext on big inductives.
**Mitigation:** Full enumeration even for "_, _ => false" cases.

**Smoke:** Build green; ~3 cofib lemmas zero-axiom.

**Task 1.4 — Foundation/Mode.lean refinement (1h)**

Extend Mode with cohesive modes:
```lean
inductive Mode
  | strict
  | observational
  | univalent
  | cohesiveFlat
  | cohesiveSharp
  deriving DecidableEq, Repr
```

Mode-related decidable predicates:
```lean
def Mode.canHavePath : Mode → Bool
  | .univalent => true
  | _ => false  -- with full enumeration

def Mode.canHaveOEq : Mode → Bool
  | .observational | .univalent => true
  | _ => false  -- full enumeration

def Mode.isStrict : Mode → Bool
  | .strict => true
  | _ => false  -- full enumeration
```

**Pitfall:** Wildcard `_ => false` — verify zero-axiom.
**Mitigation:** Test with `#print axioms Mode.canHavePath`. If it leaks,
enumerate fully.

**Smoke:** All 3 mode-predicates zero-axiom.

**Task 1.5 — Foundation/Ty.lean extension (3h)**

Add ~17 new ctors to Ty:
* `interval` (at level 0)
* `path (carrier left right)`
* `glue (A cofib T equiv)`
* `oeq` (alias-with-different-reduction-rules for id)
* `idStrict`
* `equiv`
* `refine`
* `record`
* `codata`
* `session`
* `effect`
* `modal`
* `empty`

**Pitfall:** P-21 (modal needs Modality ctor; circular dep with Layer 7).
**Mitigation:** Forward-declare `Modality` as opaque structure in Layer 0a.
Concrete Modality structure in Layer 7.

**Pitfall:** P-9 (free-type-via-suffices for parametric Ty ctors).
**Mitigation:** Use propositional-equation parameter pattern for all
level-constraining or type-determining indices.

**Smoke:** Build green; each new ctor typechecks; ~17 zero-axiom existence
witnesses (one per ctor).

### PM (8h) — RawTerm + substitution

**Task 1.6 — Foundation/RawTerm.lean extension (5h)**

Add ~40 new ctors. Group by category:

* Cubical (9 ctors): pathLam, pathApp, pathRefl, transp, comp, hcomp,
  glueIntro, unglue, intervalLit
* HOTT-specific (3 ctors, mostly redundant with Term.refl/idJ, but useful for
  pattern-matching reductions): oeqRefl, oeqJ, oeqTransp
* Refinement (2): refineIntro, refineExtract
* Records (2): recordIntro, recordProj
* Codata (2): codataUnfold, codataObserve
* Sessions (5): sessionSend, sessionRecv, sessionBranch, sessionSelect,
  sessionEnd
* Effects (2): effectPerform, effectHandle
* Strict equality (2): reflStrict, idStrictJ

Total: ~27 new RawTerm ctors. (40 was overestimate; some are derived.)

**Pitfall:** R-1 (ctor explosion). Each ctor adds boilerplate to RawSubst,
Subst, Term, Term/Rename, Term/Subst.
**Mitigation:** Scripted templating; do RawTerm first, then propagate via
templates.

**Smoke:** Build green; each ctor constructs a sample term.

**Task 1.7 — Foundation/RawSubst.lean extension (2h)**

Extend `RawTerm.rename` and `RawTermSubst.subst` for all 27 new ctors. Each
arm is structurally recursive.

```lean
def RawTerm.rename (renaming : RawRename src tgt) :
    RawTerm src → RawTerm tgt
  | ... existing arms ...
  | .pathLam body => .pathLam (body.rename (renaming.lift Ty.interval))
  | .pathApp path point => .pathApp (path.rename renaming) point
  | .transp typeFamily start term => 
      .transp (typeFamily.rename (renaming.lift Ty.interval))
              start
              (term.rename renaming)
  -- ... 27 new arms total
```

**Pitfall:** Termination of rename through `lift`-compositions.
**Mitigation:** `termination_by sizeOf body` for each arm; pre-existing
infrastructure handles compositions.

**Smoke:** Build green; rename preserves type by structural induction.

**Task 1.8 — Foundation/Subst.lean extension (1h)**

Extend `Ty.subst` for new type formers (path, glue, oeq, idStrict, equiv,
refine, record, codata, session, effect, modal, empty, interval).

Most are structural (substitute through inner Ty). `path` substitutes through
carrier and endpoints. `glue` substitutes through A, T, equiv. Etc.

**Smoke:** Build green; substitution preserves type structure.

### Evening (8h) — Term layer + audits

**Task 1.9 — Term.lean extension (4h)**

Add ~27 typed Term ctors mirroring RawTerm. Each ctor's signature is the
intrinsically-typed form.

```lean
| pathLam {bodyType : Ty level (scope+1)} {bodyRaw : RawTerm (scope+1)}
    (body : Term (context.cons Ty.interval) bodyType bodyRaw) :
    Term context (Ty.path (bodyType.subst0Interval Interval.i0 ...)
                          (bodyType.subst0Interval Interval.i1 ...))
                 (RawTerm.pathLam bodyRaw)

| pathApp {carrier : Ty level scope} {left right : RawTerm scope}
    {pathRaw : RawTerm scope}
    (path : Term context (Ty.path carrier left right) pathRaw)
    (point : Interval) :
    Term context carrier (RawTerm.pathApp pathRaw point)
```

**Pitfall:** P-15 (mode polymorphism).
**Mitigation:** Mode constraints expressed as `Ctx.mode = X` premises in some
ctor signatures (e.g., `pathLam` requires `Ctx.mode ∈ {observational, univalent}`).

**Pitfall:** P-9 (free-type-via-suffices).
**Mitigation:** Use suffices-pattern for parametric Term ctors at fixed types.

**Smoke:** Each typed Term ctor constructs a sample term zero-axiom.

**Task 1.10 — Term/Rename.lean + Term/Subst.lean (2h)**

Extend rename and subst for new Term ctors. Each preserves the
`Term.toRaw_X = rfl` pattern.

**Smoke:** `Term.toRaw_rename = rfl` and `Term.toRaw_subst = rfl` hold for
each new ctor.

**Task 1.11 — Term/Pointwise.lean extension (1h)**

Add pointwise lemmas for new Term ctors. Mostly mechanical.

**Task 1.12 — Day 1 audit + commit (1h)**

```lean
import LeanFX2.Foundation.Interval
import LeanFX2.Foundation.Cofib
import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.RawTerm
import LeanFX2.Term

#print axioms LeanFX2.Interval
#print axioms LeanFX2.BoundaryCofib
#print axioms LeanFX2.Ty.path
-- ... ~27 ctor existence audits
#print axioms LeanFX2.Term.pathLam
-- ... ~27 typed ctor audits
```

All zero-axiom.

Commit: `Phase 12.A.1: foundation rebuild — interval + cofib + ~27 ctors`.

**Day 1 acceptance criteria:**
* `lake build LeanFX2` exits 0
* All new ctors zero-axiom verified
* ~27 new RawTerm ctors + ~27 new Term ctors shipped
* All substitution/rename machinery extended

**Day 1 cut-line:** Cohesive modes (♭/♯) in Mode → defer to Day 4.

---

## Day M0 (2-4h) — Trust-spine interlock

**Mission:** Before continuing Day 2/3 or starting any Lean reimplementation,
make the metaplan operational. This is not a rewrite. It is the classification
and audit interlock that prevents rich-layer work from being overclaimed as
minimal-root work.

**Dependencies:** Day 1 foundation rebuild complete enough for current source
to build. `kernel-metaplan.md` exists and is the trust-spine reference.

### Tasks

**Task M0.1 — Root-status classification (1h)**

Add a root-status paragraph to sprint execution notes and any touched module
docstrings:

```text
Root status: FX-rich
Bridge obligations:
  - encodeTy/encodeRawTerm/encodeCtx case
  - encode_term_sound case
  - optional FX0 certificate later
```

For Day 2/3, the default status is `FX-rich`. Promotion requires an explicit
bridge theorem.

**Task M0.2 — FX1/Core import policy (1h)**

Create or update the strict-harness policy so files under `LeanFX2/FX1/Core`
are checked against the host-minimal import/dependency rules in §1.0.1.

This can start as a path-aware scan plus namespace audit. It does not need to
prove FX1.check_sound yet.

**Task M0.3 — Timeline guard (0.5h)**

Record in this sprint that Day 8 is blocked on FX1 M1-M4. The old direct
`Lean/Kernel/*` path is now historical scaffolding unless it is moved under
`LeanFX2/FX1/LeanKernel`.

**Task M0.4 — Build/audit checkpoint (0.5-1.5h)**

Run:

```bash
lake build LeanFX2
```

Expected result: build green; strict audit green; no root-status regression.

**Day M0 acceptance criteria:**
* `kernel-sprint.md` explicitly references `kernel-metaplan.md`.
* Day 2/3 claims are classified as rich-layer unless bridged.
* FX1/Core host-minimal policy exists as a planned or implemented harness gate.
* Day 8 LeanKernel work is retargeted to `LeanFX2.FX1.LeanKernel`.
* `lake build LeanFX2` exits 0 after any code changes.

**Day M0 cut-line:** None. If this interlock is skipped, later work can become
mathematically clean but TCB-ambiguous.

---

## Day 2 (24h) — Reduction + General SR

**Mission:** Add ~80 new Step rules + general SR via IsClosedTy. Unblock Conv
cong rules and HOTT machinery at the rich-layer level.

**Dependencies:** Day 1 foundation rebuild complete. Day M0 trust-spine
interlock complete.

**Root status:** Day 2 output is `FX-rich` by default. A rule becomes `Bridge`
only when its corresponding FX1 encoding and soundness theorem exist.

### AM (8h) — General Subject Reduction

**Task 2.1 — Foundation/Ty.lean: IsClosedTy (2h)**

```lean
inductive IsClosedTy : ∀ {level scope : Nat}, Ty level scope → Prop
  | unit : IsClosedTy Ty.unit
  | bool : IsClosedTy Ty.bool
  | nat : IsClosedTy Ty.nat
  | empty : IsClosedTy Ty.empty
  | interval : IsClosedTy Ty.interval
  | universe (lvl : UniverseLevel) : IsClosedTy (Ty.universe lvl)
  | arrow {A B : Ty level scope} :
      IsClosedTy A → IsClosedTy B → IsClosedTy (Ty.arrow A B)
  | listType {A : Ty level scope} :
      IsClosedTy A → IsClosedTy (Ty.listType A)
  | optionType {A : Ty level scope} :
      IsClosedTy A → IsClosedTy (Ty.optionType A)
  | eitherType {A B : Ty level scope} :
      IsClosedTy A → IsClosedTy B → IsClosedTy (Ty.eitherType A B)
  | record {fields : List (Ident × Ty level scope)} :
      (∀ field ∈ fields, IsClosedTy field.2) → IsClosedTy (Ty.record fields)
  -- piTy, sigmaTy, id, oeq, idStrict, equiv, path, glue, refine, codata,
  -- session, effect, modal NOT closed (depend on bound vars / raw / Modality)
  -- empty IS closed (no inner)

instance IsClosedTy.decidable {level scope : Nat} (t : Ty level scope) :
    Decidable (IsClosedTy t) := ...
```

**Pitfall:** Decidability for compound predicates.
**Mitigation:** Manual instance with structural decision.

**Smoke:** Decidable instance synthesizes; sample closed types verify.

**Task 2.2 — Term/SubjectReduction.lean: Step.preserves_isClosedTy (3h)**

```lean
theorem Step.preserves_isClosedTy
    {ctx : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term ctx sourceType sourceRaw}
    {targetTerm : Term ctx targetType targetRaw}
    (someStep : Step sourceTerm targetTerm)
    (sourceClosed : IsClosedTy sourceType) :
    sourceType = targetType := by
  induction someStep with
  | refl _ => rfl
  | appLeft head tail _ tailIH =>
      -- application's type = codomain of arrow; structural
      ...
  -- ... per-Step-ctor case analysis
```

**Pitfall:** P-8 (induction generalization with duplicate indices).
**Mitigation:** Free indices via srcTy/tgtTy variables; thread equality
hypotheses.

**Smoke:** Theorem typechecks zero-axiom; sample Step preserves closed type.

**Task 2.3 — StepStar.preserves_isClosedTy (1h)**

Trivial induction on chain length.

**Task 2.4 — Specialized SR for closed types (2h)**

Provide `Step.preserves_arrow` + `Step.preserves_listType` + ... as direct
corollaries.

```lean
theorem Step.preserves_arrow {A B : Ty level scope}
    (closedA : IsClosedTy A) (closedB : IsClosedTy B)
    (someStep : ...) :
    sourceType = (Ty.arrow A B) → targetType = (Ty.arrow A B) :=
  fun h => Step.preserves_isClosedTy someStep (h ▸ IsClosedTy.arrow closedA closedB)
```

This unblocks M06, M07, M08.

**Smoke:** All M-tasks (subject reduction at closed types) shipped via
specialization. Mark M06, M07, M08 as completed.

### PM (8h) — Step rules: cubical + HOTT + modal

**Task 2.5 — Reduction/Step.lean: cubical β rules (3h)**

Add ~10 cubical β/cong rules:
* betaPathApp
* betaPathReflApp
* pathLamBody (cong)
* pathAppPath (cong)
* transpRefl
* transpPi
* transpSigma
* transpPath
* transpClosedTypes (one per closed type former — 6 rules)
* glueBeta
* glueAtFace

**Pitfall:** Termination of transp through Π/Σ requires `sizeOf typeFamily`
decreasing.
**Mitigation:** `termination_by sizeOf typeFamily` per Step ctor.

**Smoke:** Each Step ctor + `_eq_` lemma zero-axiom; sample reduction proofs.

**Task 2.6 — Reduction/Step.lean: HOTT OEq rules (3h)**

Add ~15 HOTT reduction rules:
* eqNatZeroZero
* eqNatSuccSucc, eqNatZeroSucc, eqNatSuccZero
* eqBoolEq, eqBoolDiff
* eqArrow (funext-by-construction)
* eqPi (dependent funext)
* eqSigma
* eqType (univalence-by-construction)
* eqList, eqOption, eqEither, eqRecord, eqCodata

**Pitfall:** Type-level reductions don't compose with term-level reductions
in the standard β/ι sense; they're at the Conv layer.
**Mitigation:** Each OEq rule produces a Conv-equality `Conv.fromStep`. Use
`Term.castTargetType` to coerce typed terms across these conversions.

**Smoke:** Each OEq rule typechecks; sample reductions:
* `Eq Nat zero zero ↦ Ty.unit` (refl-equal closed nats)
* `Eq Nat zero (succ k) ↦ Ty.empty` (impossible closed nats)
* `Eq (Π A B) f g ↦ Π x, Eq B (f x) (g x)` (funext-by-construction)
* `Eq Type A B ↦ Equiv A B` (univalence-by-construction)

**Task 2.7 — Reduction/Step.lean: modal + refinement + records + codata + sessions + effects (2h)**

Add remaining ~20 Step rules:
* modIntroElim, modElimIntro
* refineExtractIntro
* recordProjIntro
* codataObserveUnfold (head + tail observations)
* sessionSendBeta, sessionRecvBeta, sessionBranchSelect, sessionEndComplete
* effectHandleReturn, effectHandleOp
* idStrictJ rules (only in strict mode)

**Smoke:** Each rule zero-axiom; mode-restricted rules respect Mode discipline.

### Evening (8h) — ParRed + RawPar + Compat propagation

**Task 2.8 — Reduction/ParRed.lean extension (3h)**

Each new Step ctor needs a parallel-reduction analog. ~80 ctors.

```lean
inductive Step.par : ... where
  | ... existing par ctors ...
  -- New: for each Step ctor, the parallel-reduction analog
  | pathBeta_par ...
  | transpRefl_par ...
  -- ... ~80 par ctors total
```

**Pitfall:** R-20 (mutual block coordination); ParRed needs same mutual
structure as Step.
**Mitigation:** Strict ordering: Step first (Task 2.5-2.7), ParRed second
(Task 2.8). Build green between.

**Smoke:** Build green; each par ctor produces a parallel reduction.

**Task 2.9 — Reduction/RawPar.lean extension (2h)**

Mirror Step.par at RawTerm level.

**Smoke:** Build green; each raw par ctor matches the typed par ctor.

**Task 2.10 — Reduction/Compat.lean extension (2h)**

Compatibility lemmas: `rename` and `subst` preserve `Step.par` for new ctors.
~80 lemmas, mostly mechanical.

**Pitfall:** P-1 (mutual-block propext leak).
**Mitigation:** Use term-mode Option.recOn pattern. Pre-write Match-compiler
propext probe.

**Smoke:** Build green; sample compatibility lemmas zero-axiom.

**Task 2.11 — Day 2 audit + commit (1h)**

```lean
import LeanFX2.Reduction.Step
import LeanFX2.Reduction.ParRed
import LeanFX2.Term.SubjectReduction

#print axioms Step.preserves_isClosedTy
#print axioms StepStar.preserves_isClosedTy
#print axioms Step.betaPathApp
-- ... ~80 Step ctor audits
#print axioms Step.par.pathBeta_par
-- ... ~80 par ctor audits
```

All zero-axiom.

Root-status audit:
* Mark each new reduction rule as `FX-rich`.
* Add an FX1 bridge obligation for each rule whose computation must eventually
  be visible to `FX1.check`.
* Do not call any Day 2 rule `Root-FX1` unless it is covered by FX1.check_sound.

Commit: `Phase 12.A.2: reduction core — ~80 Step rules + general SR`.

**Day 2 acceptance criteria:**
* `lake build LeanFX2` exits 0
* General SR via IsClosedTy shipped
* ~80 new Step rules + their par analogs shipped
* All zero-axiom verified
* M06, M07, M08, M09, M10 marked complete
* Every new rule has a root-status label, normally `FX-rich`
* FX1 bridge obligations are listed for rich primitives that must enter the
  minimal checker later

**Day 2 cut-line:** Some HOTT OEq rules deferred to Day 3 if Step explosion
takes more than 8h.

---

## Day 3 (24h) — Confluence + HoTT + HITs + Cubical math

**Mission:** Extend confluence machinery for new ctors. Ship HOTT mathematics
(Equiv, Univalence). DELETE `axiom Univalence`. Implement HITs. Classify all
results by trust status so rich-layer theorems are not mistaken for minimal
root theorems.

**Dependencies:** Day 2 reduction complete.

**Root status:** Day 3 output is `FX-rich` unless an explicit FX1 bridge theorem
promotes a fragment. `Univalence` and `funext` can be zero-axiom rich-layer
theorems before they are `Root-FX1`; the stronger root claim waits for FX1
encoding and checker soundness.

### AM (8h) — Confluence extension

**Task 3.1 — Confluence/Cd.lean extension (3h)**

Each new Step ctor needs a `Term.cd` case. ~30 cases.

```lean
def Term.cd {ctx : Ctx mode level scope} {ty : Ty level scope}
    {raw : RawTerm scope} (term : Term ctx ty raw) :
    Σ (rawOut : RawTerm scope), Σ' (tyOut : Ty level scope),
      Term ctx tyOut rawOut
  | ... existing cases ...
  | .pathLam body => 
      let bodyCd := body.cd
      ⟨RawTerm.pathLam bodyCd.1, ⟨..., Term.pathLam bodyCd.2.2⟩⟩
  | .pathApp path point => ...
  -- ... ~30 cases
```

**Pitfall:** P-1 (mutual-block propext).
**Mitigation:** Term-mode match patterns; verify per-case axioms.

**Smoke:** Build green; cd computes for each new ctor.

**Task 3.2 — Confluence/CdLemma.lean extension (3h)**

Each new Step ctor needs a CdLemma case proving cd respects step.

```lean
theorem Step.par.cd_lemma (someStep : Step.par sourceTerm targetTerm) :
    Step.par targetTerm sourceTerm.cd.2.2
  | ... existing cases ...
  | .pathBeta_par ... => ...
  -- ... ~30 cases
```

**Smoke:** Build green; sample cd_lemma cases zero-axiom.

**Task 3.3 — Confluence/Diamond.lean (1h)**

Diamond auto-extends from cd_lemma.

**Task 3.4 — Confluence/ChurchRosser.lean + CanonicalForm.lean (1h)**

Re-verify Tait-Martin-Löf chain holds with new ctors. Canonical form for
closed types extended.

### PM (8h) — HoTT machinery + Univalence

**Task 3.5 — HoTT/Equivalence.lean (2h)**

```lean
def IsContr (A : Ty level scope) (raw : RawTerm scope) : Prop :=
  ∃ (x : Term ctx A xRaw), ∀ (y : Term ctx A yRaw), Conv x y

def Fiber (f : Term ctx (A → B) fRaw) (y : Term ctx B yRaw) :
    Ty level scope :=
  Ty.sigmaTy A (Ty.id B (RawTerm.app fRaw (RawTerm.var 0)) yRaw)

def IsEquiv (f : Term ctx (A → B) fRaw) : Prop :=
  ∀ (y : Term ctx B yRaw), IsContr (Fiber f y) ...

def Equiv (A B : Ty level scope) : Type :=
  Σ (f : Term ctx (Ty.arrow A B) ...), IsEquiv f

def idEquiv (A : Ty level scope) : Equiv A A := ...
def Equiv.compose : Equiv A B → Equiv B C → Equiv A C := ...
def Equiv.inverse : Equiv A B → Equiv B A := ...

theorem Equiv.compose_id (e : Equiv A B) : e.compose idEquiv = e
theorem Equiv.id_compose (e : Equiv A B) : idEquiv.compose e = e
-- ... groupoid laws
```

**Smoke:** Each Equiv operation zero-axiom; groupoid laws verified.

**Task 3.6 — HoTT/Univalence.lean REWRITE (1h)**

```lean
-- Phase 6 placeholder:
-- axiom Univalence : Equiv A B → Path Type A B

-- Phase 12.A.3 (this commit):
def Univalence (A B : Ty (lvl+1) scope) :
    Conv (Ty.id (Ty.universe lvl) A B) (Ty.equiv A B) :=
  Conv.fromStep Step.eqType

def ua : Equiv A B → Term ctx (Ty.id (Ty.universe lvl) A_raw B_raw) raw :=
  fun e => Term.castTargetType (Conv.sym Univalence) e

theorem ua_β (e : Equiv A B) (x : Term ctx A xRaw) :
    Conv (Term.transp (ua e) Interval.i0 x) (e.fwd x) := ...
  -- 6 sub-lemmas; each ~30 LoC

#print axioms Univalence  -- expected: zero
#print axioms ua          -- expected: zero
#print axioms ua_β        -- expected: zero
```

**DELETE `axiom Univalence` from the file.** This is a destructive change but
intentional. The placeholder is replaced with the definitional theorem.

**Pitfall:** R-2 (ua_β intractable).
**Mitigation:** HOTT delivers Univalence definitionally; ua_β as Conv-equality
is much weaker than full Step rule. If even Conv proves intractable, ship
Univalence as the headline (sufficient for FX users).

**Smoke:** `axiom Univalence` no longer appears in source. `#print axioms ua`
zero. AuditAll passes.

**Task 3.7 — Cubical/PathLemmas.lean: funext (1h)**

```lean
theorem funext {A : Ty level scope} {B : Ty level scope} 
    (f g : Term ctx (Ty.arrow A B) ...) 
    (h : ∀ (x : Term ctx A xRaw), 
         Term ctx (Ty.id B (RawTerm.app fRaw xRaw) (RawTerm.app gRaw xRaw))
                  (... refl ...)) :
    Term ctx (Ty.id (Ty.arrow A B) fRaw gRaw) (... refl ...) :=
  -- Eq (A → B) f g ↦ Π x, Eq B (f x) (g x) (HOTT eqArrow rule)
  -- so funext h := Term.castTargetType (Conv.sym Step.eqArrow_conv) h
  Term.castTargetType (Conv.sym (Conv.fromStep Step.eqArrow)) h

#print axioms funext  -- expected: zero
```

**Smoke:** funext is a zero-axiom theorem.

**Task 3.8 — HoTT/HIT/Spec + Eliminator (2h)**

`HoTT/HIT/Spec.lean`:
```lean
structure PointCtorSpec where
  name : Ident
  paramTypes : List (Ty level scope)
  
structure PathCtorSpec where
  name : Ident
  paramTypes : List (Ty level scope)
  leftEndpoint : (params : RawTerm) → RawTerm
  rightEndpoint : (params : RawTerm) → RawTerm
  
structure HITSpec (level scope : Nat) where
  pointCtors : List PointCtorSpec
  pathCtors : List PathCtorSpec
```

`HoTT/HIT/Eliminator.lean`:
```lean
def HIT.rec (spec : HITSpec) (motive : ...) (pointCases : ...) (pathCases : ...) :
    ∀ h : HIT spec, motive h := ...
```

Generic dependent eliminator + computation rules.

**Smoke:** HIT spec typechecks; sample eliminator typechecks.

**Task 3.9 — HoTT/HIT/Examples — concrete HITs (2h)**

7 HITs:

```lean
def Quot (R : A → A → Prop) : Ty level scope := -- via OEq quotient
def propTrunc (A : Ty level scope) : Ty level scope := -- ‖A‖
def setTrunc (A : Ty level scope) : Ty level scope := -- ‖A‖₀
def S1 : Ty level scope := -- base + loop
def suspension (A : Ty level scope) : Ty level scope := -- north + south + meridian
def pushout (f : A → B) (g : A → C) : Ty level scope := -- inl + inr + glue
def coequalizer (f g : A → B) : Ty level scope := -- point + path
```

Each via HIT.rec specialization.

**Pitfall:** R-4 (HITs require general cofibrations).
**Mitigation:** Use HOTT's OEq for Quot; cubical paths for S¹ and suspension
(boundary cofibs sufficient).

**Smoke:** All 7 HITs typecheck zero-axiom.

### Evening (8h) — Path lemmas + bridges + commit

**Task 3.10 — HoTT/Path/{Composition, Inverse, Groupoid}.lean (3h)**

```lean
-- Path/Inverse.lean
def Path.inv {A : Ty level scope} (p : Term ctx (Ty.path A x y) pRaw) :
    Term ctx (Ty.path A y x) ... :=
  Term.pathLam (fun i => Term.pathApp p i.opp)

-- Path/Composition.lean (uses comp from cubical)
def Path.compose : Path A x y → Path A y z → Path A x z := ...

-- Path/Groupoid.lean — 8 groupoid laws
theorem Path.compose_id, ..., -- 8 theorems
```

**Smoke:** All 8 groupoid laws zero-axiom.

**Task 3.11 — Cubical/Bridge.lean: Path ↔ Id (2h)**

```lean
def Bridge.pathToId : Term ctx (Ty.path A x y) pRaw → Term ctx (Ty.id A x y) ... :=
  fun p => -- via OEq reduction at endpoints

def Bridge.idToPath : Term ctx (Ty.id A x y) iRaw → Term ctx (Ty.path A x y) ... :=
  fun i => -- inverse construction

theorem Bridge.pathToId_idToPath_inv : ...
theorem Bridge.idToPath_pathToId_inv : ...
theorem Bridge.pathIdEquiv : Equiv (Path A x y) (Ty.id A x y)
```

Set-level only.

**Smoke:** Bridge equivalences zero-axiom; sample uses commute.

**Task 3.12 — Day 3 audit + commit (3h)**

Comprehensive audit:
```
#print axioms LeanFX2.Univalence       -- zero
#print axioms LeanFX2.ua                -- zero
#print axioms LeanFX2.ua_β              -- zero
#print axioms LeanFX2.funext            -- zero
#print axioms LeanFX2.Quot              -- zero
#print axioms LeanFX2.propTrunc         -- zero
#print axioms LeanFX2.S1                -- zero
#print axioms LeanFX2.Bridge.pathIdEquiv -- zero
-- ... ~50 audits
```

Verify `axiom Univalence` does NOT appear in source:
```
grep -r "^axiom" /root/iprit/FX/lean-fx-2/LeanFX2/HoTT/ 
# Expected: empty (no axioms)
```

Root-status audit:
* `HoTT/Equivalence`, `HoTT/Univalence`, `Cubical/PathLemmas`, HIT modules,
  and bridge modules receive explicit `FX-rich`, `Bridge`, or `Deferred`
  classification.
* HITs implemented as setoid presentations are labeled `FX-rich` or
  `Scaffold`, not `Root-FX1`.
* A Path↔Id bridge is labeled `Bridge` only for the exact fragment proven.
  Refl-only bridges must say refl-only.
* Any theorem that depends on future `idJDep`, full hcomp, full transp, or
  full HIT eliminators is marked `Deferred`.

Commit: `Phase 12.A.3: HOTT machinery + ua-as-theorem + 7 HITs + bridges`.

**Day 3 acceptance criteria:**
* `lake build LeanFX2` exits 0
* `axiom Univalence` DELETED from source tree
* ua, ua_β, funext, Univalence all zero-axiom theorems
* 7 HITs implemented and zero-axiom verified
* Path↔Id bridge implemented and zero-axiom verified
* All AuditAll smoke passes
* Every HoTT/cubical/HIT/bridge claim has a root-status label
* No setoid or refl-fragment bridge is described as full root-trusted HIT or
  full Path↔Id equivalence unless the stronger theorem exists

**Day 3 cut-line:** HITs reduced to {Quot, propTrunc, S¹} → v1.1 if budget
tight. Path/Composition/Inverse/Groupoid can defer some lemmas.

---

## Day 4 (24h) — 2LTT + cohesive modalities

**Mission:** Implement 2LTT outer/inner stratification with `◇ ⊣ □` adjunction
+ cohesive `♭ ⊣ ◇ ⊣ □ ⊣ ♯` adjoint chain.

**Dependencies:** Day 3 HOTT + Univalence complete.

### AM (8h) — Mode + 2LTT basic

**Task 4.1 — Modal/TwoLevel.lean basic 2LTT (3h)**

```lean
structure Modality where
  fromMode : Mode
  toMode : Mode
  -- coherence laws (composability, identity)

def Modality.box : Modality := { fromMode := .observational, toMode := .strict, ... }
def Modality.diamond : Modality := { fromMode := .strict, toMode := .observational, ... }

-- Modality is composable
def Modality.compose : Modality → Modality → Option Modality := ...

theorem Modality.compose_assoc : ...
theorem Modality.identity_left : ...
theorem Modality.identity_right : ...
```

**Smoke:** Basic 2LTT structure zero-axiom.

**Task 4.2 — Modal/Adjunction.lean: ◇ ⊣ □ basic (3h)**

```lean
-- Unit and counit:
def adjUnit (A : Ty level scope) (mode : Mode = .strict) :
    Term ctx A raw → Term ctx (Ty.modal box (Ty.modal diamond A)) ... :=
  fun a => Term.modIntro (Term.modIntro a)

def adjCounit (A : Ty level scope) (mode : Mode = .observational) :
    Term ctx (Ty.modal diamond (Ty.modal box A)) raw → Term ctx A ... :=
  fun a => Term.modElim (Term.modElim a)

-- Triangle identities:
theorem adj_triangle_left : ...
theorem adj_triangle_right : ...

-- Naturality:
theorem adj_natural_unit : ...
theorem adj_natural_counit : ...
```

**Smoke:** All 4 adjunction theorems zero-axiom.

**Task 4.3 — Modal/BoxPath.lean (2h)**

```lean
theorem boxPath {A : Ty inner-mode-level scope} 
    (x y : Term inner-ctx A _) :
    Equiv (Ty.path (Ty.modal box A) (Term.modIntro x) (Term.modIntro y))
          (Ty.modal box (Ty.path A x y))
```

CLEANER via HOTT than via cubical: OEq's Π reduction handles this case
definitionally.

**Smoke:** boxPath equivalence zero-axiom.

### PM (8h) — Cohesive modalities

**Task 4.4 — Modal/Cohesive.lean: ♭ and ♯ (3h)**

```lean
def Modality.flat : Modality := 
  { fromMode := .observational, toMode := .cohesiveFlat, ... }

def Modality.sharp : Modality :=
  { fromMode := .cohesiveSharp, toMode := .observational, ... }

-- ♭-modal and ♯-modal types
def Ty.flatModal (A : Ty level scope) : Ty level scope := Ty.modal flat A
def Ty.sharpModal (A : Ty level scope) : Ty level scope := Ty.modal sharp A
```

**Pitfall:** R-3 (cohesive cuts).
**Mitigation:** If overrun, defer ♭/♯ to v1.1; ship ◇⊣□ for v1.0.

**Smoke:** Cohesive types typecheck.

**Task 4.5 — Modal/Adjunction.lean: full chain ♭ ⊣ ◇ ⊣ □ ⊣ ♯ (3h)**

12 adjunction theorems (3 pairs × 4 directions). Pentagon coherence.

**Pitfall:** Pentagon proof is intricate.
**Mitigation:** Use ACK 2LTT paper Lemma 4.2 directly. ~80 LoC adaptation.

**Smoke:** All 12 + pentagon zero-axiom.

**Task 4.6 — Modal/Bridge.lean: strict ↔ observational ↔ univalent (2h)**

Transfer reasoning across modes:
* Lift strict equality to path
* Project path to strict via □

**Smoke:** Bridge transfers preserve typing.

### Evening (8h) — Modal applications

**Task 4.7 — Modal/Ghost.lean + Cap.lean + Later.lean + Clock.lean (4h)**

Concrete modalities used by FX:
* Ghost: ◇ specialized for compile-time-only (◇.toMode = strict, marker = .ghost)
* Cap: capability modality (effects + permissions)
* Later: guarded recursion for codata productivity
* Clock: variable-clock modality

Each is a Modality + supporting Term ctors + reduction rules.

**Task 4.8 — Modal/2LTT.lean integration (3h)**

```lean
-- Demo: ua only typechecks in univalent mode
example : Conv (Ty.id Ty.universe A B) (Ty.equiv A B) := ... 
  -- only valid in univalent mode

-- Demo: decide only typechecks in strict mode
example : Decidable (Ty.idStrict A x y) := ... 
  -- only valid in strict mode

-- Demo: flat modality erases path information
example : Term flatCtx (Ty.flatModal A) raw → ... := ...
```

**Task 4.9 — Day 4 audit + commit (1h)**

Audit ~30 modal theorems. Commit:
`Phase 12.A.4: 2LTT modal stratification + cohesive ♭⊣◇⊣□⊣♯`.

**Day 4 acceptance criteria:**
* All 4 modes integrated
* ◇ ⊣ □ adjunction with 4 theorems shipped
* Cohesive ♭⊣◇⊣□⊣♯ adjunction (or deferred to v1.1)
* BoxPath equivalence shipped
* All zero-axiom verified

**Day 4 cut-line:** Cohesive ♭/♯ → v1.1.

---

## Day 5 (24h) — Layers 7-9 (Graded + Refine + Effects + Sessions + Codata)

**Mission:** Implement all 21 graded dimensions, refinement types,
effects, sessions, codata.

**Dependencies:** Day 4 modal complete.

### AM (8h) — Graded TT

**Task 5.1 — Graded/Semiring.lean: abstract semiring (1h)**

Abstract Semiring structure with verified laws.

**Task 5.2 — Graded/GradeVector.lean: 21-dim vector (2h)**

Grade vector across all 21 dimensions. Pointwise add and mul.

**Task 5.3 — Graded/Ctx.lean + Rules.lean: Wood/Atkey 2022 Lam (3h)**

Graded context + corrected Lam rule.

```lean
-- Wood/Atkey 2022 corrected Lam rule:
def Term.gradedLam (G : GradedCtx) (p r : GradeVector) (A : Ty) (B : Ty)
    (b : Term (G/p, A^r) B 1) :
    Term G (Pi A^r B)^p
```

**Smoke:** Lam rule zero-axiom; corrected version distinct from Atkey 2018.

**Task 5.4 — Graded/Instances/{Usage, Effect, Security, Lifetime, ...}.lean (2h)**

21 instance files, each ~10 LoC + verified semiring laws.

### PM (8h) — Atkey 2018 attack rejection + Refinement

**Task 5.5 — Atkey 2018 attack term verification (1h)**

```lean
-- The Atkey 2018 attack: λ f. λ x. f (f x) with linear f
-- This term does NOT typecheck under Wood/Atkey 2022 Lam rule.

example : ¬ (typeable (λ f : i64 → i64. λ x : i64. f (f x)) at-grade-1) := by
  -- f's grade is 1 (linear). The closure (λ x. f (f x)) requires
  -- f used at grade w (for the duplicate use). 
  -- 1/w = 0 in usage semiring, so f isn't available in the closure.
  -- Hence the term fails to typecheck.
  ...
```

**Smoke:** Attack rejection theorem zero-axiom.

**Task 5.6 — Refine/Ty.lean + Term.lean: extension (2h)**

Already exist; extend with subtyping + intro/elim:

```lean
-- T{P} <: T (forget refinement)
theorem Refine.unrefine_subtype (T_refined : Ty.refine T P) :
    Ty.refine T P → T

-- Term.refineIntro: introduce refinement with proof
def Term.refineIntro (witness : Term ctx T raw)
    (predicate : Term ctx P[witness/0] proofRaw) :
    Term ctx (Ty.refine T P) (RawTerm.refineIntro witness proofRaw)
```

**Task 5.7 — Refine/Decidable.lean (2h)**

```lean
-- For decidable predicates, refinement can be discharged automatically
instance : DecidableEq (Term ctx (Ty.refine T DecidableP) raw) := ...
```

**Task 5.8 — Refine/SMTCert.lean + SMTRecheck.lean (3h)**

Placeholder structure for SMT certificates. SMT recheck is v1.1.

```lean
structure SMTCert where
  goal : RawTerm scope
  -- Just a placeholder. v1.1 adds external SMT solver invocation.
```

### Evening (8h) — Effects + Sessions + Codata

**Task 5.9 — Effects/Foundation.lean (2h)**

```lean
inductive Op where
  | mkOp (name : Ident) (paramType : Ty level scope) (resultType : Ty level scope)

def EffectRow := List Op

def Effect.empty : EffectRow := []
def Effect.union : EffectRow → EffectRow → EffectRow := ...

-- Term ctors:
-- (in Layer 0, already added)

-- Effect handlers
def Term.effectHandle 
    (body : Term (ctx.withEffect effects) A raw) 
    (handlers : Map Op (Term ctx (paramType ⟶ contType ⟶ A) handlerRaw)) :
    Term ctx A (RawTerm.effectHandle body handlers)
```

**Task 5.10 — Effects/Step.lean: handler reductions (2h)**

```lean
-- Already in Layer 2 Step (effectHandleReturn, effectHandleOp)
-- This file collects derived theorems and ensures handler composition works
```

**Task 5.11 — Sessions/Foundation.lean (1h)**

```lean
inductive SessionProtocol where
  | send (T : Ty 0 scope) (rest : SessionProtocol)
  | recv (T : Ty 0 scope) (rest : SessionProtocol)
  | branch (options : List (Tag × SessionProtocol))
  | end
```

**Task 5.12 — Sessions/Duality.lean (1h)**

```lean
def SessionProtocol.dual : SessionProtocol → SessionProtocol := ...

theorem SessionProtocol.dual_involutive (p : SessionProtocol) :
    p.dual.dual = p := ...
```

**Task 5.13 — Codata/Foundation.lean + Productivity.lean (1h)**

Codata via Later modality for productivity. Codata stream:
```lean
codata Stream A where
  head : A
  tail : Later (Stream A)
```

**Task 5.14 — Day 5 audit + commit (1h)**

Audit ~50 graded/refine/effect/session/codata theorems. Commit:
`Phase 12.A.5: layers 7-9 — graded TT + refinement + effects + sessions + codata`.

**Day 5 acceptance criteria:**
* All 21 graded dimensions implemented
* Atkey 2018 attack rejected (verified in smoke)
* Refinement types with decidable predicates
* Effect handlers (single-shot)
* Sessions with linear typing + duality
* Codata with Later-modality productivity
* All zero-axiom

**Day 5 cut-line:** SMT external recheck → v1.1. Multi-shot effect
continuations → v1.1.

---

## Day 6 (24h) — Surface frontend

**Mission:** Complete surface frontend: AST extensions, parser, printer,
roundtrip, elaboration soundness + completeness. Close all 95 surface tasks.

**Dependencies:** Day 5 layers 7-9 complete.

### AM (8h) — AST + Token + Lex

**Task 6.1 — Surface/AST.lean extensions A05-A15 + H01-H05 (3h)**

15 + 5 = 20 new AST node types or extensions:
* A05: pre/post/decreases/where on `Decl.fnDecl`
* A06: `Expr.matchExpr` (intrinsic exhaustiveness)
* A07: `isType` predicate distinguishing type-expr from value-expr
* A08: `Expr.tryCatch`
* A09: `Expr.handleEffect`
* A10: `Expr.selectChannel`
* A11: `Expr.modal` markers (comptime, ghost, secret, await)
* A12: `Expr.verifyBlock`, `Expr.assertExpr`, `Expr.calcChain`
* A13: `Decl.machine`, `Decl.contract`, `Decl.codata`, `Decl.session`,
  `Decl.hardware`
* A14: `FnDecl.typeParams`
* A15: `FnDecl.effectRow`
* H01: Dependent FnParam (paramType references earlier binders)
* H02: Type-class context
* H03: forall/exists for higher-rank
* H04: Variance annotations
* H05: Class-level kind annotations

**Task 6.2 — Surface/Token + TokenSchema + GrammarToken refinements (2h)**

T01-T10:
* T01: BitLitValid refinement on bitLit
* T02-T03: Typed numeric suffixes
* T04: Ident name → LowerIdent / UpperIdent
* T05: StrEscape refinement
* T06-T10: WellFormedTokenStream + balance + chained-comparison rejection

**Task 6.3 — Surface/Lex.lean audits L01-L08 (3h)**

* L01: Lex consumes all input or produces error
* L02: classifyIdent round-trips
* L03: Lex output EOF-terminated
* L04: Lex positions monotonic
* L05: Refine output to Array WellFormedToken
* L06: Invalid characters always produce errors
* L07: LexError offset within source range
* L08: Lex.runFromString documented

### PM (8h) — Parser + Printer + Roundtrip

**Task 6.4 — Surface/Parse.lean: full parser (3h)**

LALR(1)-compatible recursive descent. Full FX grammar (1981 lines spec).
Precedence-climbing for operators. Position tracking. Disambiguation rules.

**Pitfall:** R-8 (parser size).
**Mitigation:** Canonical fragment first; full grammar incrementally.

**Task 6.5 — Surface/Print.lean: pretty printer (2h)**

Inverse of Parse: AST → String.

**Task 6.6 — Surface/Roundtrip.lean: M01 + M02 theorems (3h)**

```lean
theorem M01 : ∀ tok : List Token, 
    Lex.run (Print.runTokens tok) = ok tok

theorem M02 : ∀ ast : AST,
    Parse.run (Lex.run (Print.run ast)) = ok ast
```

### Evening (8h) — Elaboration + Bridge cleanup

**Task 6.7 — Surface/Elab.lean (3h)**

Elaboration: AST → typed Term. Mode-inference per declaration.

**Task 6.8 — Surface/ElabSoundness.lean (2h)**

Soundness: every elaborated Term is well-typed.

**Task 6.9 — Surface/ElabCompleteness.lean (1h)**

Completeness: every well-typed program elaborates.

**Pitfall:** R-19 (mode-inference).
**Mitigation:** Default mode per declaration context; explicit mode markers
override.

**Task 6.10 — Surface/KernelEnv.lean: B10 propext-clean refactor (1h)**

Replace mutual block tactic-mode with term-mode `Option.recOn`. Verify
zero-axiom.

**Task 6.11 — Surface/Bridge.lean: extension for new ctors (R-series complete) (1h)**

Bridge handles all new ctors (path, glue, refine, record, codata, session,
effect).

**Task 6.12 — Pipeline.lean: end-to-end (1h)**

```lean
def compile (source : String) : Either Error (Σ ctx ty raw, Term ctx ty raw) :=
  Parse.run (Lex.run source) |>.bind elaborate
```

**Task 6.13 — Day 6 audit + commit**

All 95 surface tasks closed. AuditAll passes. Commit:
`Phase 12.A.6: surface frontend complete`.

**Day 6 acceptance criteria:**
* `lake build LeanFX2` exits 0
* All 95 surface tasks resolved
* M01 + M02 roundtrip theorems shipped
* Elab Soundness + Completeness theorems shipped
* B10 propext-clean refactor complete
* Pipeline end-to-end works

**Day 6 cut-line:** Parser canonical fragment only; full grammar v1.1.
ElabCompleteness → v1.1 if budget tight.

---

## Day 7 (24h) — Audit + Final + v1.0 close

**Mission:** Comprehensive audit, documentation closure, v1.0 tag.

**Dependencies:** Day 6 surface complete.

### AM (8h) — Comprehensive audit

**Task 7.1 — Tools/AuditAll.lean (3h)**

~500 `#assert_no_axioms` calls covering every kernel declaration.

**Task 7.2 — Tools/AuditGen.lean (2h)**

Auto-generation tactic that walks all .lean files and emits AuditAll entries.

**Task 7.3 — Tools/Tactics/Cast.lean + HEq.lean + SimpStrip.lean (3h)**

Kernel tactics for HEq simplification, cast handling, simp lemma stripping.

### PM (8h) — Documentation closure

**Task 7.4 — AXIOMS.md REWRITE (2h)**

Strict zero-axiom across ALL layers. No documented exceptions. The Univalence
postulate REMOVED. Catastrophe analysis archived as historical note.

**Task 7.5 — ROADMAP.md closure (1h)**

Phases 0-15 marked COMPLETE. v1.0 milestone declared.

**Task 7.6 — MIGRATION.md final (1h)**

* lean-fx → lean-fx.deprecated
* lean-fx-2 → lean-fx
* Update parent project imports

**Task 7.7 — README.md final (2h)**

v1.0 release notes. Architecture overview (15 layers, all complete).
Quickstart for users.

**Task 7.8 — fx_design.md cross-reference (2h)**

Verify §27 metatheory aligns with shipped theorems. Update citations.

### Evening (8h) — Final integration + v1.0 tag

**Task 7.9 — Smoke/AuditAll.lean comprehensive (4h)**

~500 `#print axioms` calls, ALL must report "does not depend on any axioms".

**Task 7.10 — Final integration tests (2h)**

End-to-end programs combining all theories. Verify zero-axiom + correct
behavior.

**Task 7.11 — v1.0 tag (2h)**

```bash
git add -A
git commit -m "Phase 12.A.7: v1.0 audit + close"
git tag -a v1.0 -m "v1.0 — strict zero-axiom dependently-typed graded modal univalent observational kernel for FX"
```

**Day 7 acceptance criteria:**
* `lake build LeanFX2` exits 0
* AuditAll smoke passes (~500 `#print axioms` clean)
* `axiom` keyword does NOT appear in any kernel file
* `sorry` does NOT appear in any kernel file
* All 95 deferred tasks resolved
* MIGRATION.md cutover complete
* v1.0 git tag placed

**Day 7 cut-line:** Tools/Tactics/* → v1.1 if budget tight.

---

## Day 8 (24h+ gated) — FX1 + Lean Kernel Meta-Verification

**Mission:** Finish the minimal FX1 checker spine, then encode the Lean 4
kernel over FX1 and prove the LeanKernel checker sound. Reduce TCB without
mistaking the rich kernel for the minimal root.

**Dependencies:** Day M0 complete. Rich-layer Day 2/3 work may be complete, but
LeanKernel-FX1 is blocked on FX1 M1-M4:

* M1: FX1 syntax, declarations, environments, contexts, scope checking.
* M2: FX1 renaming and substitution, with identity/composition lemmas.
* M3: FX1 typing and beta/delta reduction, with preservation.
* M4: FX1 executable checker, WHNF, conversion soundness, `FX1.check_sound`.

If M4 is not complete, Day 8 does not start LeanKernel implementation. It stays
on FX1/Core.

### Gate 8.0 — FX1/Core minimal root

Implement or verify:

```text
LeanFX2/FX1/Core/Name.lean
LeanFX2/FX1/Core/Level.lean
LeanFX2/FX1/Core/Expr.lean
LeanFX2/FX1/Core/Declaration.lean
LeanFX2/FX1/Core/Environment.lean
LeanFX2/FX1/Core/Context.lean
LeanFX2/FX1/Core/Substitution.lean
LeanFX2/FX1/Core/Reduction.lean
LeanFX2/FX1/Core/HasType.lean
LeanFX2/FX1/Core/Check.lean
LeanFX2/FX1/Core/Soundness.lean
```

The required theorem is:

```lean
theorem LeanFX2.FX1.check_sound :
    FX1.check environment context expression = some typeExpression ->
    FX1.HasType environment context expression typeExpression
```

Only after this theorem is audit-clean can LeanKernel-FX1 make a TCB-reduction
claim.

### AM (8h) — LeanKernel-FX1 syntax encoding

**Task 8.1 — FX1/LeanKernel/Level.lean (2h)**

Lean's universe levels:
```lean
inductive Level
  | zero
  | succ : Level → Level
  | max : Level → Level → Level
  | imax : Level → Level → Level
  | param : Name → Level
  | mvar : Name → Level

def Level.normalize : Level → Level := ...
def Level.le : Level → Level → Prop := ...

instance : DecidableEq Level := ...
instance : ∀ l1 l2, Decidable (Level.le l1 l2) := ...
```

**Task 8.2 — FX1/LeanKernel/Name.lean (1h)**

```lean
inductive Name
  | anonymous
  | str : Name → String → Name
  | num : Name → Nat → Name
```

**Task 8.3 — FX1/LeanKernel/Expr.lean: 12-ctor encoding (3h)**

```lean
inductive Expr (level scope : Nat) : Type
  | bvar : Fin scope → Expr level scope
  | fvar : FVarId → Expr level scope
  | sort : Level → Expr level scope
  | const : Name → List Level → Expr level scope
  | app : Expr level scope → Expr level scope → Expr level scope
  | lam : Expr level scope → Expr level (scope+1) → Expr level scope
  | pi : Expr level scope → Expr level (scope+1) → Expr level scope
  | letE : Expr level scope → Expr level scope → Expr level (scope+1) → Expr level scope
  | lit : Literal → Expr level scope
  | mdata : MData → Expr level scope → Expr level scope
  | proj : Name → Nat → Expr level scope → Expr level scope
  -- 12 ctors total, matching Lean's expr_kind enum
```

**Pitfall:** Lean's BVar uses Nat (not Fin); we strengthen via Fin scope.
Lean's MVar is metavariable; we model as a separate inductive.

**Task 8.4 — FX1/LeanKernel/Substitution.lean (2h)**

`Expr.instantiate`, `Expr.abstract`, `Expr.lift`. Mirrors Lean's
`instantiate.cpp`.

### PM (8h) — Reduction + typing rules

**Task 8.5 — FX1/LeanKernel/Reduction.lean: 8 reduction rules (4h)**

```lean
inductive Step : Expr level scope → Expr level scope → Prop
  | beta  : Step ((Expr.lam ty body).app arg) (body.instantiate arg)
  | eta   : ∀ {body : Expr level (scope+1)}, 
            (¬ body.contains 0) → 
            Step (Expr.lam ty (body.app (Expr.bvar 0))) body
  | delta : env.find c = some def → 
            Step (Expr.const c lvls) 
                 (def.value.instLevels lvls)
  | zeta  : Step (Expr.letE ty val body) (body.instantiate val)
  | iota  : ... ι-reduction per inductive ...
  | proj  : ... projection on ctor ...
  | quot  : ... Quot.lift on Quot.mk ...
  | natLit : ... Nat literal reduction ...

def whnf : Environment → Expr level scope → Option (Expr level scope) := ...
```

**Pitfall:** P-23 (lazy delta heuristic).
**Mitigation:** We prove SOUND, not COMPLETE. Lean's heuristic may accept
things our pure relation rejects (acceptable).

**Task 8.6 — FX1/LeanKernel/Inductive.lean (2h)**

Inductive specifications + recursor synthesis + ι-reduction + strict
positivity.

**Pitfall:** P-19 (strict positivity).
**Mitigation:** `IsStrictlyPositive` decidable predicate, checked structurally.

**Task 8.7 — FX1/LeanKernel/HasType.lean: typing rules (2h)**

~25 typing rules (one per Expr ctor + universe rules + Pi rule with imax + ...).

### Evening (8h) — Type checker + soundness

**Task 8.8 — FX1/LeanKernel/Check.lean: executable type checker (4h)**

```lean
def check : Environment → LocalContext → Expr → Option Expr := ...

-- ~600 LoC mirroring Lean's type_checker.cpp ~1244 LoC of C++
```

**Task 8.9 — FX1/LeanKernel/Soundness.lean: THE THEOREM (3h)**

```lean
theorem check_sound :
    LeanFX2.FX1.LeanKernel.check env ctx e = some ty →
    LeanFX2.FX1.LeanKernel.HasType env ctx e ty := by
  -- Induction on e's structure + structural induction on check function
  -- Using lean-fx-2's general SR for closed-typed positions
  -- Using lean-fx-2's confluence for DefEq decisions
  ...
```

**Task 8.10 — FX1/LeanKernel/Audit.lean + commit (1h)**

```lean
#print axioms LeanFX2.FX1.LeanKernel.check_sound
-- Expected: zero (Outcome A)
-- OR: documented dependency on a specific lemma (Outcome B/C)
```

**Outcome A:** Clean proof. TCB reduced.

**Outcome B:** Encoding gap. We've discovered a Lean kernel issue. File with
Mario, get it fixed in Lean upstream, re-check.

**Outcome C:** Confluence/SR gap. Real research result.

**Outcome D:** Trust list. Document specific operationally-trusted components.

Commit: `Phase 12.A.8: FX1-root + LeanKernel-FX1 meta-verification (Outcome X)`.

**Day 8 acceptance criteria:**
* `lake build LeanFX2` exits 0
* `LeanFX2.FX1.check_sound` typechecks and is audit-clean
* `lake build LeanFX2.FX1.LeanKernel.Soundness` exits 0 if LeanKernel work has
  started
* `LeanFX2.FX1.LeanKernel.check_sound` typechecks
* `#print axioms LeanFX2.FX1.LeanKernel.check_sound` reports zero OR documented
  gap filed
* TCB reduced to FX1-root (Outcome A) OR research result (Outcome B/C)
* No direct LeanKernel TCB claim is made against the broad rich kernel

**Day 8 cut-line:** Completeness → v1.1. Universe normalization completeness
→ v1.1. LeanKernel-FX1 itself is delayed if FX1.check_sound is not complete.

---

## Day 9 (24h) — Cross-Theory Bridges

**Mission:** Implement bridge equivalences between cubical Path,
observational Id, modal-projected variants. Conservativity proofs. Translation
functors.

**Dependencies:** Day 7 v1.0 (HOTT + cubical + 2LTT all shipped).

### AM (8h) — Bridge equivalences

**Task 9.1 — Bridge/PathToId.lean (1.5h)**

```lean
def Bridge.pathToId : Term ctx (Ty.path A x y) pRaw → Term ctx (Ty.id A x y) ... := ...
```

**Task 9.2 — Bridge/IdToPath.lean (1.5h)**

```lean
def Bridge.idToPath : Term ctx (Ty.id A x y) iRaw → Term ctx (Ty.path A x y) ... := ...
```

**Task 9.3 — Bridge/PathIdInverse.lean (1.5h)**

```lean
theorem Bridge.pathToId_idToPath_inv : ...
theorem Bridge.idToPath_pathToId_inv : ...
theorem Bridge.pathIdEquiv : Equiv (Path A x y) (Ty.id A x y)
```

**Task 9.4 — Bridge/IdEqType.lean (0.5h)**

```lean
theorem Bridge.idEqType (A B : Ty (lvl+1) scope) :
    Conv (Ty.id (Ty.universe lvl) A B) (Ty.equiv A B) :=
  Conv.fromStep Step.eqType
```

(Pure HOTT.)

**Task 9.5 — Bridge/PathEqType.lean (1h)**

```lean
theorem Bridge.pathEqType (A B : Ty (lvl+1) scope) :
    Equiv (Path Ty.universe A B) (Equiv A B) := ...
```

**Task 9.6 — Bridge/BoxObservational.lean (1h)**

```lean
theorem Bridge.boxObservational :
    Equiv (Ty.id (Ty.modal box A) (boxIntro x) (boxIntro y))
          (Ty.modal box (Ty.id A x y)) := ...
```

**Task 9.7 — Bridge/BoxCubical.lean (1h)**

```lean
theorem Bridge.boxCubical :
    Equiv (Path (Ty.modal box A) (boxIntro x) (boxIntro y))
          (Ty.modal box (Path A x y)) := ...
```

### PM (8h) — Conservativity

**Task 9.8 — Conservativity/HOTTOverMLTT.lean (3h)**

```lean
def HOTT.toMLTT : Term ctx_HOTT A_HOTT raw → Term ctx_MLTT A_MLTT raw_MLTT := ...

theorem HOTTOverMLTT_typing_preservation :
    ∀ (e : Term ctx_HOTT A_HOTT raw),
      A_HOTT only mentions MLTT-types →
      HasType ctx_MLTT (HOTT.toMLTT e).rawForm A_HOTT.toMLTT
```

**Task 9.9 — Conservativity/CubicalOverHOTT.lean (3h)**

Cubical paths can be observationalized via Bridge.pathToId.

```lean
def Cubical.toHOTT : Term ctx_cubical (Ty.path A x y) raw → 
                     Term ctx_HOTT (Ty.id A x y) ... := Bridge.pathToId

theorem CubicalOverHOTT_preservation : ...
```

**Task 9.10 — Conservativity/ModalOverObservational.lean (2h)**

Modal layer is conservative over observational. Outer mode programs are
exactly the strict-MLTT subset.

### Evening (8h) — Translation functors + coherence

**Task 9.11 — Translation/CubicalToObservational.lean (2h)**

Explicit translation functor. Functoriality proof.

**Task 9.12 — Translation/ObservationalToCubical.lean (2h)**

Reverse functor.

**Task 9.13 — Translation/Inverse.lean (2h)**

The functors compose to identity (set-level).

**Task 9.14 — InternalLanguage/Coherence.lean (1h)**

Diamond commutation: triangle of translations Cubical/Observational/MLTT
commutes up to provable equality.

**Task 9.15 — Day 9 audit + commit (1h)**

Audit ~30 bridge/conservativity/translation theorems. Commit:
`Phase 12.A.9: cross-theory bridges + conservativity + coherence`.

**Day 9 acceptance criteria:**
* `lake build LeanFX2` exits 0
* All 6 bridge equivalences proven zero-axiom
* All 3 conservativity proofs shipped
* All 3 translation functors with inverse-pair proof
* Coherence diamond proven
* Programs in any theory inter-translatable

**Day 9 cut-line:** Higher-coherence bridges (h-groupoid level) → v1.1.

---

# Section 6 — Cut Order If Behind Schedule

In severity order (cut LAST things first):

0. **Day M0 trust-spine interlock** is not cuttable. Without it, the sprint can
   stay zero-axiom but become TCB-ambiguous.
1. **Cohesive modalities ♭/♯** → v1.1 (keep ◇⊣□)
2. **HITs beyond {Quot, propTrunc, S¹}** → v1.1
3. **Multi-shot effect continuations** → v1.1
4. **SMT external recheck (Decidable only)**
5. **Pipeline.lean full grammar** (canonical fragment OK)
6. **ElabCompleteness** (Soundness suffices for v1.0)
7. **Tools/Tactics/*** (manual proofs OK for v1.0)
8. **Some Surface refinements (A11-A13)** → v1.1
9. **Day 8 completeness theorem** (soundness suffices)
10. **Day 9 higher-coherence bridges** (set-level OK)

Days 1-3 + M0 + 7 are non-negotiable for the rich-layer sprint. FX1.check_sound
is non-negotiable before any TCB-reduction or Lean-in-FX claim. If FX1 M4
overruns, Day 8 LeanKernel work slides; it is not replaced by a direct rich
kernel encoding.

---

# Section 7 — Per-Day Acceptance Criteria

## Day 0
* Scaffold complete: ~40 new files with stub docstrings
* `lake build LeanFX2` exits 0
* Initial commit `Phase 12.A.0` exists

## Day 1
* Foundation rebuild: ~17 Ty ctors + ~27 RawTerm ctors
* All substitution machinery extended
* Term layer rebuilt
* Build green; per-ctor zero-axiom

## Day M0
* `kernel-sprint.md` wired to `kernel-metaplan.md`
* Day 2/3 default status recorded as `FX-rich`
* FX1/Core host-minimal audit gate planned or implemented
* Day 8 retargeted to `LeanFX2.FX1.LeanKernel`
* Build green after any code changes

## Day 2
* General SR via IsClosedTy shipped
* ~80 Step rules + their par analogs
* M06, M07, M08, M09, M10 marked complete
* Build green
* New rules classified by root status
* FX1 bridge obligations listed

## Day 3
* `axiom Univalence` DELETED
* ua, ua_β, funext zero-axiom theorems
* 7 HITs implemented
* Path↔Id bridge
* Every HoTT/cubical/HIT/bridge claim classified as `FX-rich`, `Bridge`,
  `Scaffold`, or `Deferred`

## Day 4
* 2LTT ◇⊣□ adjunction shipped
* Cohesive ♭⊣◇⊣□⊣♯ chain (or deferred)
* BoxPath equivalence
* Modal applications populated

## Day 5
* All 21 graded dimensions
* Atkey 2018 attack rejected
* Refinement types + decidable
* Effects (single-shot)
* Sessions + Codata

## Day 6
* All 95 surface tasks resolved
* Parser, printer, roundtrip M01+M02
* Elab Soundness + Completeness
* B10 propext-clean
* Pipeline end-to-end

## Day 7
* AuditAll passes (~500 `#print axioms` clean)
* `axiom` and `sorry` keywords absent from kernel
* MIGRATION.md cutover
* v1.0 tag placed

## Day 8
* `LeanFX2.FX1.check_sound` typechecks
* `LeanFX2.FX1.LeanKernel.check_sound` typechecks if LeanKernel work starts
* TCB reduced to FX1-root (Outcome A) OR documented gap (Outcome B/C)
* No direct rich-kernel LeanKernel TCB claim

## Day 9
* All 6 bridge equivalences zero-axiom
* All 3 conservativity proofs
* Translation functors with inverse-pair
* Coherence diamond

---

# Section 8 — v1.0 Manifest

What ships at end of Day 9:

## Trust status

The manifest is split by trust role:

* `FX-rich`: expressive lean-fx-2 features implemented directly in the current
  `Ty` / `RawTerm` / `Term` / `Step` / `Conv` architecture.
* `Bridge`: translations and soundness theorems connecting rich features into
  FX1.
* `Root-FX1`: the minimal lambda-Pi checker fragment covered by
  `FX1.check_sound`.
* `LeanKernel-FX1`: Lean-kernel model and checker soundness over FX1.
* `FX0-root`: first-order certificate checker work. This is the final skeptical
  root path and may remain post-v1.0 unless explicitly completed.

No rich-layer feature is counted as minimal-root trusted merely because it is
zero-axiom.

## Theory completeness

* Higher Observational Type Theory at set-level
* Cubical Path machinery (boundary cofibs)
* 2LTT outer/inner stratification with full ◇⊣□ adjunction
* Cohesive modalities ♭⊣◇⊣□⊣♯ (or deferred to v1.1)
* All 21 graded dimensions (Atkey-2022-corrected Lam)

These are `FX-rich` unless promoted by bridge theorems.

## HITs

* Quot, propTrunc, setTrunc, S¹, suspension, pushout, coequalizer

## Type extensions

* Refinement types with decidable predicates
* Records as kernel primitive
* First-class effect handlers (single-shot)
* Linear session types with duality
* Codata with Later-modality productivity

## Bridges

* Path ≃ Id (cubical ↔ observational, set-level)
* Id Type A B = Equiv A B (HOTT definitional)
* Path Type A B ≃ Equiv A B (cubical via Glue)
* □ commutes with Id (modal ↔ observational)
* □ commutes with Path (modal ↔ cubical)

## Conservativity

* HOTT ⊃ MLTT (conservative over MLTT-only types)
* Cubical ⊃ HOTT (cubical paths observationalize)
* Modal ⊃ Observational (outer = strict-MLTT subset)

## Translation functors

* Cubical → Observational (and inverse, set-level)
* Coherence diamond (triangle commutes)

## Surface

* Full AST extensions (A05-A15, H01-H05)
* Lex with audits (L01-L08)
* Token refinements (T01-T10)
* Schema audits (C01-C09)
* Parser (canonical fragment; full grammar v1.1)
* Printer
* Roundtrip M01+M02
* Elab Soundness + Completeness

## Pipeline

* String → Tokens → AST → Term → Reduced value end-to-end

## Tools

* AuditAll comprehensive (~500 zero-axiom assertions)
* AuditGen auto-generation
* Tactics for HEq, Cast, SimpStrip

## Lean kernel meta-verification

* `FX1.check_sound` zero-axiom for the minimal lambda-Pi checker
* Faithful LeanKernel-FX1 encoding of Lean's 12-ctor expression syntax
* Faithful LeanKernel-FX1 encoding of all 8 reduction rules
* LeanKernel-FX1 `HasType` typing relation
* LeanKernel-FX1 `check` function (executable)
* `LeanFX2.FX1.LeanKernel.check_sound` zero-axiom (Outcome A) OR documented
  gap (Outcome B/C)
* TCB reduced from "Lean's C++ kernel" to "lean-fx-2's verified FX1
  meta-theory" for the modeled Lean fragment
* Final minimal TCB claim deferred until FX0 certificates verify FX1 proof
  traces, unless FX0-root is completed in this sprint

## Axioms ELIMINATED

* `axiom Univalence` DELETED (now `def Univalence := rfl`)
* `funext` was implicit via stdlib; now `funext h := h` (definitional)
* No `propext`, `Quot.sound`, `Classical.choice` in any kernel theorem
* No `K`, no `sorry` durable

## Cutover

* `lean-fx-2` → `lean-fx`
* `lean-fx` → `lean-fx.deprecated`
* Parent project imports updated
* MIGRATION.md final
* ROADMAP.md Phases 0-15 COMPLETE

## Tag

* `git tag v1.0` at the final commit
* Released as: "strict zero-axiom dependently-typed graded modal univalent
  observational kernel for FX, with verified Lean kernel embedding"

---

# Section 9 — Post-v1.0 Roadmap

## v1.1 (1-2 months post v1.0)

* FX0 first-order certificate checker if not completed in v1.0
* FX1 proof-trace emitter and FX0 certificate generation for at least one
  non-trivial FX1 typing proof
* Rich-layer bridge expansion: encode all Day 2/3 cubical, HoTT, HIT, and
  bridge primitives into FX1 with `encode_*_sound` theorems
* H-groupoid coherence in HOTT (n-truncation at all levels, Sterling et al.
  2024 paper full mechanization)
* Full CCHM cofibration lattice
* Multi-shot effect continuations
* SMT external recheck for refinement types
* Full FX grammar in parser
* HITs beyond {Quot, propTrunc, S¹}: 2-truncation, fundamental groupoid,
  Eilenberg-MacLane spaces
* Cohesive `♭/♯` if deferred
* Higher-coherence bridges (h-groupoid level)
* `LeanFX2.FX1.LeanKernel.check_complete` (completeness theorem)
* Lean kernel inductive elaborator full faithfulness

## v2.x (longer-term)

* Cubical kernel native (instead of HOTT-as-primary): full CCHM with native
  interval, comp/hcomp, ua-as-step-rule
* Modal univalence (Cohen-Kleitman-Whittemore)
* Cohesive HoTT extensions
* Quantum modalities
* Linear ⊆ Affine ⊆ Cartesian universe stratification

## v3.x

* Full constructive cubical kernel (no fall-back to HOTT)
* `LeanFX2.FX1.LeanKernel.check_full_completeness` (full sound + complete)
* Cross-language bridges to Coq, Agda, Idris

---

# Closing Note

This is **9 days of focused agentic work** plus the FX1 trust-spine interlock.
~10,000 LoC kernel additions. ~500 zero-axiom theorems. Four equality types
(`idStrict`, `id`, `path`, `equiv`) bridged by provable equivalences. Lean's
kernel is embedded only through `LeanFX2.FX1.LeanKernel`, after FX1.check_sound.
Cross-theory bridges make the three rich theories interchangeable for set-level
reasoning, while root-trust claims are routed through FX1 and eventually FX0.

Each obstacle in Section 3 has a known mitigation. Each risk in Section 4 has
a probability and an impact and a mitigation. Each cut in Section 6 is
documented in advance.

When ready to launch: Day 0 starts with scaffolding directories and stub
files. Day 1 follows immediately. The Ralph loop drives the iteration.

The acceptance criterion is concrete: `git tag v1.0` exists, `axiom
Univalence` is absent from the source, AuditAll smoke passes with
~500 `#print axioms` reports of "does not depend on any axioms", every rich
primitive has a root-status label, `FX1.check_sound` typechecks zero-axiom
before any TCB-reduction claim, and `LeanFX2.FX1.LeanKernel.check_sound`
typechecks zero-axiom or a documented gap is filed.

Anything provable in zero-axiom Lean is engineering, not research.

This is engineering.
