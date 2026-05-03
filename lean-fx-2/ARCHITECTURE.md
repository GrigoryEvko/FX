# Architecture — lean-fx-2

13 layers, strict dependency order (each layer depends only on layers below).

## Layer 0 — Foundation: untyped substrate

The "untyped" layer.  No `Term` references.  Provides the index types that everything else uses.

| File | Contains |
|---|---|
| `Foundation/Mode.lean` | Mode 2-category: Mode, Modality (1-cell), TwoCell (2-cell), composability/collision lattice.  Foundational to MTT.  No Term references. |
| `Foundation/RawTerm.lean` | Untyped well-scoped terms (de Bruijn, Fin-indexed).  Substrate for `Term`'s raw index. |
| `Foundation/RawSubst.lean` | Untyped substitution / renaming algebra.  `RawTermSubst`, `RawRenaming`, lift, compose, identity. |
| `Foundation/Ty.lean` | Types: Π, Σ, Id (with raw endpoints), Universe (with cumulativity bound), bool/nat/list/option/either, modal-decorated, refinement-decorated.  Indexed by `(level, scope)`. |
| `Foundation/Subst.lean` | Joint type substitution: `Subst level src tgt = { forTy : Fin src → Ty level tgt, forRaw : RawTermSubst src tgt }`.  Lift, compose, **unified** singleton (one definition, no dropNewest variant). |
| `Foundation/Context.lean` | Typing contexts `Ctx mode level scope`, `Ctx.cons`, `Ctx.lookup`, `varType`.  Mode-aware. |

## Layer 1 — Term: raw-aware typed term

The kernel's **load-bearing inductive**.

```lean
Term : (ctx : Ctx mode level scope) → (ty : Ty level scope) →
       (raw : RawTerm scope) → Type
```

Each constructor pins its raw form structurally.  `Term.toRaw t = raw` is `rfl`.

| File | Contains |
|---|---|
| `Term.lean` | Term inductive: var, unit, lam/app (non-dep arrow), lamPi/appPi (dep Π), pair/fst/snd (Σ), boolTrue/False/Elim, natZero/Succ/Elim/Rec, listNil/Cons/Elim, optionNone/Some/Match, eitherInl/Inr/Match, refl/idJ (Identity types), modIntro/modElim/subsume (Modal).  TermRenaming structure. |
| `Term/Rename.lean` | `Term.rename : Term ctx ty raw → Term ctx' ty.rename ρ (raw.rename ρ)`. |
| `Term/Subst.lean` | `TermSubst` type, `Term.subst`, `Term.subst0` (single-binder; UNIFIED — no `_term` variant). |
| `Term/Pointwise.lean` | Substitution pointwise lemmas. |
| `Term/ToRaw.lean` | `def Term.toRaw : Term ctx ty raw → RawTerm scope := raw` (the projection).  Trivial collapsed-to-rfl lemmas. |

## Layer 2 — Reduction: computation rules

| File | Contains |
|---|---|
| `Reduction/Step.lean` | Single-step reduction `Step : Term ctx ty raw1 → Term ctx ty raw2 → Prop`.  Cong rules + β/ι rules.  η rules opt-in via separate `Reduction/Eta.lean` (when added). |
| `Reduction/StepStar.lean` | Multi-step: reflexive-transitive closure of Step.  `StepStar.mapStep` lifter for cong refactor. |
| `Reduction/Conv.lean` | **Conv as ∃-StepStar**: `Conv t1 t2 := ∃ t', StepStar t1 t' ∧ StepStar t2 t'`.  Uniform — no inductive Conv with 13 cong rules.  Decidability cleaner. |
| `Reduction/ParRed.lean` | Parallel reduction `Step.par` — Tait–Martin-Löf vehicle for confluence. |
| `Reduction/RawPar.lean` | Raw parallel reduction (unchanged from lean-fx).  Used by Bridge. |
| `Reduction/Compat.lean` | Step.rename_compatible, Step.subst_compatible (NO RawConsistent threading needed — every TermSubst is automatically raw-consistent because forRaw is constrained by Term values' raw indices), StepStar/Conv compat, Step.par compat. |

## Layer 3 — Confluence: Tait–Martin-Löf chain

| File | Contains |
|---|---|
| `Confluence/Cd.lean` | Complete development function `Term.cd : Term ctx ty raw → Term ctx ty (raw.cd)`.  Fires every redex in a single pass. |
| `Confluence/CdLemma.lean` | `Step.par.cd_lemma`: every parallel reduct lands in `Term.cd t`. |
| `Confluence/Diamond.lean` | Diamond property for Step.par. |
| `Confluence/ChurchRosser.lean` | Step.parStar.confluence. |
| `Confluence/CanonicalForm.lean` | Conv.canonical_form: convertible terms have a common reduct. |

## Layer 4 — Bridge: typed↔raw correspondence

| File | Contains |
|---|---|
| `Bridge.lean` | Forward bridge (`Step.par t t' → RawStep.par t.toRaw t'.toRaw`) — closes via `rfl + RawStep.par.<ctor>` per case (the lean-fx 4-sorry pain dissolves here).  Backward extraction (where decidable).  Source/target inversion lemmas. |

## Layer 5 — HoTT

| File | Contains |
|---|---|
| `HoTT/Identity.lean` | Id type intro (`refl`), elim (J), computation rules. |
| `HoTT/J.lean` | J eliminator with **full dependent motive**: `(C : (a b : A) → Id A a b → Type) → ((x : A) → C x x (refl x)) → (a b : A) → (p : Id A a b) → C a b p`.  This is the lean-fx v2.7 task that got deferred. |
| `HoTT/Path/Composition.lean` | `Id.trans`: composition of paths. |
| `HoTT/Path/Inverse.lean` | `Id.sym`: inverse of a path. |
| `HoTT/Path/Groupoid.lean` | Groupoid laws on paths (assoc, inv, identity laws). |
| `HoTT/Transport.lean` | `transport : (P : A → Type) → Id A a b → P a → P b`. |
| `HoTT/Equivalence.lean` | `Equiv A B`, bi-inverses with coherence, `id ≃ id` is the trivial equiv. |
| `HoTT/NTypes.lean` | `isProp`, `isSet`, `isGroupoid` predicates and stratification. |
| `HoTT/Univalence.lean` | Univalence as a REAL THEOREM with body `Conv.fromStep Step.eqType` (zero-axiom).  NEVER a postulate, NEVER an axiom, NEVER scoped via `@[univalence_postulate]` (that attribute is forbidden — see CLAUDE.md / AXIOMS.md). |
| `HoTT/HIT/Spec.lean` | HIT specification structure: data + path constructors. |
| `HoTT/HIT/Setoid.lean` | HIT setoid encoding (Quotient inductive with manual respect — propext-free). |
| `HoTT/HIT/Eliminator.lean` | HIT induction over data with respect proofs. |
| `HoTT/HIT/Examples.lean` | Concrete HITs: Circle (S¹), Suspension, Quotient, PropTrunc. |

## Layer 6 — Modal (MTT)

| File | Contains |
|---|---|
| `Modal/Foundation.lean` | Ty.modal constructor, Term.modIntro/modElim/subsume, modal computation rules. |
| `Modal/Later.lean` | Later (▶) modality: `next : A → ▶ A`, productive corecursion via setoid encoding. |
| `Modal/Clock.lean` | Clock quantification ∀κ.A. |
| `Modal/Bridge.lean` | Bridge modality (parametricity): bridge_intro, bridge_extract, free-theorem extraction.  Internal parametricity via type-indexed relations. |
| `Modal/Cap.lean` | Capability modality: capability-label data + lattice, intro/elim, subsumption preorder. |
| `Modal/Ghost.lean` | Ghost (erased) modality + `ghost ⊣ erase` adjunction. |
| `Modal/2LTT.lean` | Two-Level Type Theory: static layer (Ghost mode separation) + dynamic layer (Software/Hardware/Wire), classical-content separation theorem. |
| `Modal/Adjunction.lean` | Modal adjunction infrastructure (e.g., `ghost ⊣ erase`, `bridge ⊣ extract`). |

## Layer 7 — Graded

Per `fx_design.md` §6 (the 19-dimension graded type system).

| File | Contains |
|---|---|
| `Graded/Semiring.lean` | Generic semiring framework — typeclass + laws (associativity, commutativity, distributivity, annihilation). |
| `Graded/GradeVector.lean` | Dependent product over registered dimensions; pointwise operations. |
| `Graded/Ctx.lean` | Bindings carry GradeVector. |
| `Graded/Rules.lean` | Wood-Atkey lambda rule (context division), App graded scaling, modality interaction (modality scales grade vector). |
| `Graded/Instances/Usage.lean` | `{0, 1, ω}` semiring (linear/affine/unrestricted, Atkey 2018 with Wood/Atkey 2022 correction). |
| `Graded/Instances/Effect.lean` | Effect lattice (`Tot ⊆ IO ⊆ ...`, join). |
| `Graded/Instances/Security.lean` | `unclassified ≤ classified` lattice. |

## Layer 8 — Refine

| File | Contains |
|---|---|
| `Refine/Ty.lean` | `Ty.refine` constructor — refinement with predicate field. |
| `Refine/Term.lean` | Refinement intro/elim — proof-bundling at boundaries. |
| `Refine/Decidable.lean` | Lean-internal Decidable instance for the predicate fragment. |
| `Refine/SMTCert.lean` | SMT certificate format (proof-only, axiom-free). |
| `Refine/SMTRecheck.lean` | Lean-side rechecker — convert certificate to Decidable result. |

## Layer 9 — Algo: algorithmic content

| File | Contains |
|---|---|
| `Algo/WHNF.lean` | Weak head normal form classifier: `WHNF : Term → Bool` decides head-normal-ness. |
| `Algo/DecConv.lean` | Decidable Conv instance: given Conv = ∃-StepStar, run WHNF on both sides, compare, recurse. |
| `Algo/Infer.lean` | Type inference for synth forms (`var`, `app`, `appPi`, `fst`, `snd`, `idJ`, etc.). |
| `Algo/Check.lean` | Type checking: check fallthrough — synth forms + Conv check.  Bidirectional. |
| `Algo/Synth.lean` | Synthesis for atomic surface constructors. |
| `Algo/Eval.lean` | Fuel-bounded evaluator: `Term Γ T → reduct` with explicit fuel parameter. |
| `Algo/Soundness.lean` | Algorithmic content soundness: if infer succeeds, the typed Term is well-typed. |
| `Algo/Completeness.lean` | Completeness: every well-typed Term has a synthesizable type. |

## Layer 10 — Surface: frontend

| File | Contains |
|---|---|
| `Surface/Token.lean` | Token alphabet: keywords, punctuation, identifiers, literals. |
| `Surface/Lex.lean` | Lexer body: `String → List Token` with error recovery. |
| `Surface/AST.lean` | Surface AST: pre-elaboration syntax tree.  Includes patterns/refinements/modal annotations. |
| `Surface/Parse.lean` | Parser combinators + expression parser + declaration parser. |
| `Surface/Print.lean` | Pretty printer: AST → String. |
| `Surface/Roundtrip.lean` | lex/print roundtrip, parse/print roundtrip theorems. |
| `Surface/Elab.lean` | Elaboration to kernel: surface AST → kernel `Term`.  Fills implicit arguments, resolves names. |
| `Surface/ElabSoundness.lean` | If elab succeeds, kernel Term is well-typed. |
| `Surface/ElabCompleteness.lean` | Every kernel Term has a surface preimage. |

## Layer 11 — Pipeline

| File | Contains |
|---|---|
| `Pipeline.lean` | End-to-end: `String → Either Error CompiledModule`.  Composes lex + parse + elab + check + eval.  Smoke example demonstrating round-trip. |

## Layer 12 — Tools

| File | Contains |
|---|---|
| `Tools/AuditAll.lean` | Auto-generated `#assert_no_axioms` gates for every kernel declaration.  Generated by `Tools/AuditGen.lean`. |
| `Tools/AuditGen.lean` | Tactic that crawls declarations and emits `#assert_no_axioms` per decl. |
| `Tools/Tactics/Cast.lean` | Step.castBoth/Source/Target threading helpers (replaces lean-fx's manual cast scaffolding). |
| `Tools/Tactics/HEq.lean` | HEq → Eq via Term-typing. |
| `Tools/Tactics/SimpStrip.lean` | Bridge-rfl simp set (collapses `Term.toRaw`-related casts). |

## Smoke tests

| File | Contains |
|---|---|
| `Smoke/Foundation.lean` | RawTerm/Ty/Subst sanity examples. |
| `Smoke/Term.lean` | Concrete typed terms: `λx.x`, `(λx.x) ()`, etc. |
| `Smoke/Reduction.lean` | β-reduction examples reach normal form. |
| `Smoke/Confluence.lean` | Diamond on representative dependent terms. |
| `Smoke/Bridge.lean` | Typed↔raw roundtrip on identity-laden terms. |
| `Smoke/HoTT.lean` | J on refl, transport along refl, S¹ examples. |
| `Smoke/Modal.lean` | modIntro then modElim is identity, subsume composition. |
| `Smoke/Graded.lean` | Atkey-2018 witness rejection (the broken Lam rule rejects the linear-double-use term), canonical examples. |

## Cross-layer principles

* **Mode 2-category infrastructure is foundational.**  Modes/modalities are Layer 0, not bolted on.  This makes Modal (Layer 6) clean to build.
* **Conv as ∃-StepStar.**  Eliminates the inductive Conv's 13 cong rules.  Decidability cleaner, mapStep refactor unnecessary at the Conv level (mapStep still applies to StepStar).
* **Smoke tests live next to spec.**  Every theorem ships with a concrete `example` in the same file (or a sibling `Smoke/<Module>.lean`).  No silent regressions.
* **AuditAll is auto-generated.**  Manual `#assert_no_axioms` lists drift; the tactic crawls definitions and emits gates per build.

## Diff from lean-fx (file-level)

* lean-fx has `Inductive.lean` + per-eliminator congruence files; lean-fx-2 consolidates per-layer.
* lean-fx has `TermSubst/Commute/{SubstRename,RenameSubst,Subst0Rename,Subst0Subst,SingletonRename}.lean` — lean-fx-2 puts these in one `Term/Pointwise.lean` (smaller because raw-aware Term simplifies).
* lean-fx has `Reduction/{ParCompatible,ParCompatibleIsBi,ParStarWithBi,ParSubstWitnessed,ParSubstPointwise}.lean` — lean-fx-2 collapses these into `Reduction/Compat.lean` (the paired-predicate workaround was needed for lean-fx's typed inversion gap; lean-fx-2's raw-aware Term sidesteps it).
* lean-fx has `Reduction/CdLemmaStarWithBi.lean` + per-redex helpers; lean-fx-2 has `Confluence/CdLemma.lean` (single file, 17 cases inline).
* No `Stash/`, no quarantined files.  No deferred-to-Wave-N markers.

## File count target

* Skeleton: ~70 stub files
* Working kernel (Layers 0–4 implemented): ~70 files, ~3000 lines
* Full engine (all 13 layers): ~70 files, ~5000–7000 lines

vs lean-fx's 92 files, ~41 000 lines.
